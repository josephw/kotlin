/*
 * Copyright 2010-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license
 * that can be found in the LICENSE file.
 */

#ifndef RUNTIME_MM_OBJECT_FACTORY_H
#define RUNTIME_MM_OBJECT_FACTORY_H

#include <algorithm>
#include <memory>
#include <mutex>
#include <type_traits>

#include "Alignment.hpp"
#include "Alloc.h"
#include "FinalizerHooks.hpp"
#include "Memory.h"
#include "Mutex.hpp"
#include "Types.h"
#include "Utils.hpp"

namespace kotlin {
namespace mm {

namespace internal {

// A queue that is constructed by collecting subqueues from several `Producer`s.
// This is essentially a heterogeneous `MultiSourceQueue` on top of a singly linked list that
// uses `Allocator` to allocate and free memory.
// TODO: Consider merging with `MultiSourceQueue` somehow.
template <size_t DataAlignment, typename Allocator>
class ObjectFactoryStorage : private Pinned {
    static_assert(IsValidAlignment(DataAlignment), "DataAlignment is not a valid alignment");

    template <typename T>
    class Deleter {
    public:
        void operator()(T* instance) noexcept {
            instance->~T();
            Allocator::Free(instance);
        }
    };

    template <typename T>
    using unique_ptr = std::unique_ptr<T, Deleter<T>>;

public:
    // This class does not know its size at compile-time. Does not inherit from `KonanAllocatorAware` because
    // in `KonanAllocatorAware::operator new(size_t size, KonanAllocTag)` `size` would be incorrect.
    class Node : private Pinned {
        constexpr static size_t DataOffset() noexcept { return AlignUp(sizeof(Node), DataAlignment); }

    public:
        ~Node() = default;

        constexpr static std::pair<size_t, size_t> GetSizeAndAlignmentForDataSize(size_t dataSize) noexcept {
            size_t dataSizeAligned = AlignUp(dataSize, DataAlignment);
            size_t totalAlignment = std::max(alignof(Node), DataAlignment);
            size_t totalSize = AlignUp(sizeof(Node) + dataSizeAligned, totalAlignment);
            return std::make_pair(totalSize, totalAlignment);
        }

        static Node& FromData(void* data) noexcept {
            constexpr size_t kDataOffset = DataOffset();
            Node* node = reinterpret_cast<Node*>(reinterpret_cast<uintptr_t>(data) - kDataOffset);
            RuntimeAssert(node->Data() == data, "Node layout has broken");
            return *node;
        }

        // Note: This can only be trivially destructible data, as nobody can invoke its destructor.
        void* Data() noexcept {
            constexpr size_t kDataOffset = DataOffset();
            void* ptr = reinterpret_cast<uint8_t*>(this) + kDataOffset;
            RuntimeAssert(IsAligned(ptr, DataAlignment), "Data=%p is not aligned to %zu", ptr, DataAlignment);
            return ptr;
        }

        // It's a caller responsibility to know if the underlying data is `T`.
        template <typename T>
        T& Data() noexcept {
            return *static_cast<T*>(Data());
        }

    private:
        friend class ObjectFactoryStorage;

        Node() noexcept = default;

        static unique_ptr<Node> Create(Allocator& allocator, size_t dataSize) noexcept {
            auto [totalSize, totalAlignment] = GetSizeAndAlignmentForDataSize(dataSize);
            RuntimeAssert(
                    DataOffset() + dataSize <= totalSize, "totalSize %zu is not enough to fit data %zu at offset %zu", totalSize, dataSize,
                    DataOffset());
            void* ptr = allocator.Alloc(totalSize, totalAlignment);
            if (!ptr) {
                konan::consoleErrorf("Out of memory trying to allocate %zu bytes. Aborting.\n", totalSize);
                konan::abort();
            }
            RuntimeAssert(IsAligned(ptr, totalAlignment), "Allocator returned unaligned to %zu pointer %p", totalAlignment, ptr);
            return unique_ptr<Node>(new (ptr) Node());
        }

        unique_ptr<Node> next_;
        // There's some more data of an unknown (at compile-time) size here, but it cannot be represented
        // with C++ members.
    };

    class Producer : private MoveOnly {
    public:
        class Iterator {
        public:
            Node& operator*() noexcept { return *node_; }
            Node* operator->() noexcept { return node_; }

            Iterator& operator++() noexcept {
                node_ = node_->next_.get();
                return *this;
            }

            bool operator==(const Iterator& rhs) const noexcept { return node_ == rhs.node_; }
            bool operator!=(const Iterator& rhs) const noexcept { return node_ != rhs.node_; }

        private:
            friend class Producer;
            explicit Iterator(Node* node) noexcept : node_(node) {}

            Node* node_;
        };

        Producer(ObjectFactoryStorage& owner, Allocator allocator) noexcept : owner_(owner), allocator_(std::move(allocator)) {}

        ~Producer() { Publish(); }

        size_t size() const noexcept { return size_; }

        Node& Insert(size_t dataSize) noexcept {
            AssertCorrect();
            auto node = Node::Create(allocator_, dataSize);
            auto* nodePtr = node.get();
            if (!root_) {
                root_ = std::move(node);
            } else {
                last_->next_ = std::move(node);
            }

            last_ = nodePtr;
            ++size_;
            RuntimeAssert(root_ != nullptr, "Must not be empty");
            AssertCorrect();
            return *nodePtr;
        }

        template <typename T, typename... Args>
        Node& Insert(Args&&... args) noexcept {
            static_assert(alignof(T) <= DataAlignment, "Cannot insert type with alignment bigger than DataAlignment");
            static_assert(std::is_trivially_destructible_v<T>, "Type must be trivially destructible");
            auto& node = Insert(sizeof(T));
            new (node.Data()) T(std::forward<Args>(args)...);
            return node;
        }

        // Merge `this` queue with owning `ObjectFactoryStorage`.
        // `this` will have empty queue after the call.
        // This call is performed without heap allocations. TODO: Test that no allocations are happening.
        void Publish() noexcept {
            AssertCorrect();
            if (!root_) {
                return;
            }

            std::lock_guard guard(owner_.mutex_);

            owner_.AssertCorrectUnsafe();

            if (!owner_.root_) {
                owner_.root_ = std::move(root_);
            } else {
                owner_.last_->next_ = std::move(root_);
            }

            owner_.last_ = last_;
            last_ = nullptr;
            owner_.size_ += size_;
            size_ = 0;

            RuntimeAssert(root_ == nullptr, "Must be empty");
            AssertCorrect();
            RuntimeAssert(owner_.root_ != nullptr, "Must not be empty");
            owner_.AssertCorrectUnsafe();
        }

        Iterator begin() noexcept { return Iterator(root_.get()); }
        Iterator end() noexcept { return Iterator(nullptr); }

        void ClearForTests() noexcept {
            // Since it's only for tests, no need to worry about stack overflows.
            root_.reset();
            last_ = nullptr;
            size_ = 0;
        }

    private:
        friend class ObjectFactoryStorage;

        ALWAYS_INLINE void AssertCorrect() const noexcept {
            if (root_ == nullptr) {
                RuntimeAssert(last_ == nullptr, "last_ must be null");
            } else {
                RuntimeAssert(last_ != nullptr, "last_ must not be null");
                RuntimeAssert(last_->next_ == nullptr, "last_ must not have next");
            }
        }

        ObjectFactoryStorage& owner_; // weak
        Allocator allocator_;
        unique_ptr<Node> root_;
        Node* last_ = nullptr;
        size_t size_ = 0;
    };

    class Iterator {
    public:
        Node& operator*() noexcept { return *node_; }
        Node* operator->() noexcept { return node_; }

        Iterator& operator++() noexcept {
            previousNode_ = node_;
            node_ = node_->next_.get();
            return *this;
        }

        bool operator==(const Iterator& rhs) const noexcept { return node_ == rhs.node_; }

        bool operator!=(const Iterator& rhs) const noexcept { return node_ != rhs.node_; }

    private:
        friend class ObjectFactoryStorage;

        Iterator(Node* previousNode, Node* node) noexcept : previousNode_(previousNode), node_(node) {}

        Node* previousNode_; // Kept for `Iterable::EraseAndAdvance`.
        Node* node_;
    };

    class Consumer : private MoveOnly {
    public:
        class Iterator {
        public:
            Node& operator*() noexcept { return *node_; }
            Node* operator->() noexcept { return node_; }

            Iterator& operator++() noexcept {
                node_ = node_->next_.get();
                return *this;
            }

            bool operator==(const Iterator& rhs) const noexcept { return node_ == rhs.node_; }
            bool operator!=(const Iterator& rhs) const noexcept { return node_ != rhs.node_; }

        private:
            friend class Consumer;
            explicit Iterator(Node* node) noexcept : node_(node) {}

            Node* node_;
        };

        Consumer() noexcept = default;

        Consumer(Consumer&& other) noexcept {
            root_ = std::move(other.root_);
            size_ = other.size_;
            last_ = other.last_;
            other.size_ = 0;
            other.last_ = nullptr;
        }
        Consumer& operator=(Consumer&& other) noexcept {
            Consumer temp = std::move(other);
            std::swap(root_, temp.root_);
            std::swap(size_, temp.size_);
            std::swap(last_, temp.last_);
            return *this;
        }

        ~Consumer() {
            // Make sure not to blow up the stack by nested `~Node` calls.
            for (auto node = std::move(root_); node != nullptr; node = std::move(node->next_)) {
            }
        }

        size_t size() const noexcept { return size_; }

        Iterator begin() noexcept { return Iterator(root_.get()); }
        Iterator end() noexcept { return Iterator(nullptr); }

        void MergeWith(Consumer &&other) {
            AssertCorrect();
            if (other.root_) {
                if (!root_) {
                    root_ = std::move(other.root_);
                } else {
                    last_->next_ = std::move(other.root_);
                }
                last_ = other.last_;
                size_ += other.size_;
                other.last_ = nullptr;
                other.size_ = 0;
            }
            AssertCorrect();
        }

    private:
        friend class ObjectFactoryStorage;

        void Insert(unique_ptr<Node> node) noexcept {
            AssertCorrect();
            auto* nodePtr = node.get();
            if (!root_) {
                root_ = std::move(node);
            } else {
                last_->next_ = std::move(node);
            }

            last_ = nodePtr;
            ++size_;
            AssertCorrect();
        }

        ALWAYS_INLINE void AssertCorrect() const noexcept {
            if (root_ == nullptr) {
                RuntimeAssert(last_ == nullptr, "last_ must be null");
            } else {
                RuntimeAssert(last_ != nullptr, "last_ must not be null");
                RuntimeAssert(last_->next_ == nullptr, "last_ must not have next");
            }
        }

        unique_ptr<Node> root_;
        Node* last_ = nullptr;
        size_t size_ = 0;
    };

    class Iterable : private MoveOnly {
    public:
        explicit Iterable(ObjectFactoryStorage& owner) noexcept : owner_(owner), guard_(owner_.mutex_) {}

        size_t size() const noexcept { return owner_.size_; }

        Iterator begin() noexcept { return Iterator(nullptr, owner_.root_.get()); }
        Iterator end() noexcept { return Iterator(owner_.last_, nullptr); }

        void EraseAndAdvance(Iterator& iterator) noexcept {
            auto result = owner_.ExtractUnsafe(iterator.previousNode_);
            iterator.node_ = result.second;
        }

        void MoveAndAdvance(Consumer& consumer, Iterator& iterator) noexcept {
            auto result = owner_.ExtractUnsafe(iterator.previousNode_);
            iterator.node_ = result.second;
            consumer.Insert(std::move(result.first));
        }

    private:
        ObjectFactoryStorage& owner_; // weak
        std::unique_lock<SpinLock<MutexThreadStateHandling::kIgnore>> guard_;
    };

    ~ObjectFactoryStorage() {
        // Make sure not to blow up the stack by nested `~Node` calls.
        for (auto node = std::move(root_); node != nullptr; node = std::move(node->next_)) {}
    }

    // Lock `ObjectFactoryStorage` for safe iteration.
    Iterable LockForIter() noexcept { return Iterable(*this); }

    size_t GetSizeUnsafe() const noexcept { return size_; }

    void ClearForTests() {
        root_.reset();
        last_ = nullptr;
        size_ = 0;
    }

private:
    // Expects `mutex_` to be held by the current thread.
    std::pair<unique_ptr<Node>, Node*> ExtractUnsafe(Node* previousNode) noexcept {
        RuntimeAssert(root_ != nullptr, "Must not be empty");
        AssertCorrectUnsafe();

        if (previousNode == nullptr) {
            // Extracting the root.
            auto node = std::move(root_);
            root_ = std::move(node->next_);
            if (!root_) {
                last_ = nullptr;
            }
            --size_;
            AssertCorrectUnsafe();
            return {std::move(node), root_.get()};
        }

        auto node = std::move(previousNode->next_);
        previousNode->next_ = std::move(node->next_);
        if (!previousNode->next_) {
            last_ = previousNode;
        }
        --size_;

        AssertCorrectUnsafe();
        return {std::move(node), previousNode->next_.get()};
    }

    // Expects `mutex_` to be held by the current thread.
    ALWAYS_INLINE void AssertCorrectUnsafe() const noexcept {
        if (root_ == nullptr) {
            RuntimeAssert(last_ == nullptr, "last_ must be null");
        } else {
            RuntimeAssert(last_ != nullptr, "last_ must not be null");
            RuntimeAssert(last_->next_ == nullptr, "last_ must not have next");
        }
    }

    unique_ptr<Node> root_;
    Node* last_ = nullptr;
    size_t size_ = 0;
    SpinLock<MutexThreadStateHandling::kIgnore> mutex_;
};

} // namespace internal

template <typename GC>
class ObjectFactory : private Pinned {
    using GCObjectData = typename GC::ObjectData;
    using GCThreadData = typename GC::ThreadData;
    using Allocator = typename GC::Allocator;

    struct HeapObjHeader {
        GCObjectData gcData;
        alignas(kObjectAlignment) ObjHeader object;
    };

    // Needs to be kept compatible with `HeapObjHeader` just like `ArrayHeader` is compatible
    // with `ObjHeader`: the former can always be casted to the other.
    struct HeapArrayHeader {
        GCObjectData gcData;
        alignas(kObjectAlignment) ArrayHeader array;
    };

public:
    using Storage = internal::ObjectFactoryStorage<kObjectAlignment, Allocator>;

    class NodeRef {
    public:
        explicit NodeRef(typename Storage::Node& node) noexcept : node_(node) {}

        static NodeRef From(ObjHeader* object) noexcept {
            RuntimeAssert(object->heap(), "Must be a heap object");
            auto* heapObject = reinterpret_cast<HeapObjHeader*>(reinterpret_cast<uintptr_t>(object) - offsetof(HeapObjHeader, object));
            RuntimeAssert(&heapObject->object == object, "HeapObjHeader layout has broken");
            return NodeRef(Storage::Node::FromData(heapObject));
        }

        static NodeRef From(ArrayHeader* array) noexcept {
            // `ArrayHeader` and `ObjHeader` are kept compatible, so the former can
            // be always casted to the other.
            RuntimeAssert(reinterpret_cast<ObjHeader*>(array)->heap(), "Must be a heap object");
            auto* heapArray = reinterpret_cast<HeapArrayHeader*>(reinterpret_cast<uintptr_t>(array) - offsetof(HeapArrayHeader, array));
            RuntimeAssert(&heapArray->array == array, "HeapArrayHeader layout has broken");
            return NodeRef(Storage::Node::FromData(heapArray));
        }

        NodeRef* operator->() noexcept { return this; }

        GCObjectData& GCObjectData() noexcept {
            // `HeapArrayHeader` and `HeapObjHeader` are kept compatible, so the former can
            // be always casted to the other.
            return static_cast<HeapObjHeader*>(node_.Data())->gcData;
        }

        bool IsArray() const noexcept {
            // `HeapArrayHeader` and `HeapObjHeader` are kept compatible, so the former can
            // be always casted to the other.
            auto* object = &static_cast<HeapObjHeader*>(node_.Data())->object;
            return object->type_info()->IsArray();
        }

        ObjHeader* GetObjHeader() noexcept {
            auto* object = &static_cast<HeapObjHeader*>(node_.Data())->object;
            RuntimeAssert(!object->type_info()->IsArray(), "Must not be an array");
            return object;
        }

        ArrayHeader* GetArrayHeader() noexcept {
            auto* array = &static_cast<HeapArrayHeader*>(node_.Data())->array;
            RuntimeAssert(array->type_info()->IsArray(), "Must be an array");
            return array;
        }

        bool operator==(const NodeRef& rhs) const noexcept { return &node_ == &rhs.node_; }

        bool operator!=(const NodeRef& rhs) const noexcept { return !(*this == rhs); }

    private:
        typename Storage::Node& node_;
    };

    class ThreadQueue : private MoveOnly {
    public:
        class Iterator {
        public:
            NodeRef operator*() noexcept { return NodeRef(*iterator_); }
            NodeRef operator->() noexcept { return NodeRef(*iterator_); }

            Iterator& operator++() noexcept {
                ++iterator_;
                return *this;
            }

            bool operator==(const Iterator& rhs) const noexcept { return iterator_ == rhs.iterator_; }
            bool operator!=(const Iterator& rhs) const noexcept { return iterator_ != rhs.iterator_; }

        private:
            friend class ObjectFactory;

            explicit Iterator(typename Storage::Producer::Iterator iterator) noexcept : iterator_(std::move(iterator)) {}

            typename Storage::Producer::Iterator iterator_;
        };

        ThreadQueue(ObjectFactory& owner, GCThreadData& gc) noexcept : producer_(owner.storage_, gc.CreateAllocator()) {}

        static size_t ObjectAllocatedSize(const TypeInfo* typeInfo) noexcept {
            RuntimeAssert(!typeInfo->IsArray(), "Must not be an array");
            size_t allocSize = ObjectAllocatedDataSize(typeInfo);
            return Storage::Node::GetSizeAndAlignmentForDataSize(allocSize).first;
        }

        ObjHeader* CreateObject(const TypeInfo* typeInfo) noexcept {
            RuntimeAssert(!typeInfo->IsArray(), "Must not be an array");
            size_t allocSize = ObjectAllocatedDataSize(typeInfo);
            auto& node = producer_.Insert(allocSize);
            auto* heapObject = new (node.Data()) HeapObjHeader();
            auto* object = &heapObject->object;
            object->typeInfoOrMeta_ = const_cast<TypeInfo*>(typeInfo);
            // TODO: Consider supporting TF_IMMUTABLE: mark instance as frozen upon creation.
            return object;
        }

        static size_t ArrayAllocatedSize(const TypeInfo* typeInfo, uint32_t count) noexcept {
            RuntimeAssert(typeInfo->IsArray(), "Must be an array");
            size_t allocSize = ArrayAllocatedDataSize(typeInfo, count);
            return Storage::Node::GetSizeAndAlignmentForDataSize(allocSize).first;
        }

        ArrayHeader* CreateArray(const TypeInfo* typeInfo, uint32_t count) noexcept {
            RuntimeAssert(typeInfo->IsArray(), "Must be an array");
            size_t allocSize = ArrayAllocatedDataSize(typeInfo, count);
            auto& node = producer_.Insert(allocSize);
            auto* heapArray = new (node.Data()) HeapArrayHeader();
            auto* array = &heapArray->array;
            array->typeInfoOrMeta_ = const_cast<TypeInfo*>(typeInfo);
            array->count_ = count;
            // TODO: Consider supporting TF_IMMUTABLE: mark instance as frozen upon creation.
            return array;
        }

        void Publish() noexcept { producer_.Publish(); }

        Iterator begin() noexcept { return Iterator(producer_.begin()); }
        Iterator end() noexcept { return Iterator(producer_.end()); }

        void ClearForTests() noexcept { producer_.ClearForTests(); }

    private:
        static size_t ObjectAllocatedDataSize(const TypeInfo* typeInfo) noexcept {
            size_t membersSize = typeInfo->instanceSize_ - sizeof(ObjHeader);
            return AlignUp(sizeof(HeapObjHeader) + membersSize, kObjectAlignment);
        }

        static size_t ArrayAllocatedDataSize(const TypeInfo* typeInfo, uint32_t count) noexcept {
            uint32_t membersSize = static_cast<uint32_t>(-typeInfo->instanceSize_) * count;
            // Note: array body is aligned, but for size computation it is enough to align the sum.
            return AlignUp(sizeof(HeapArrayHeader) + membersSize, kObjectAlignment);
        }

        typename Storage::Producer producer_;
    };

    class Iterator {
    public:
        NodeRef operator*() noexcept { return NodeRef(*iterator_); }
        NodeRef operator->() noexcept { return NodeRef(*iterator_); }

        Iterator& operator++() noexcept {
            ++iterator_;
            return *this;
        }

        bool operator==(const Iterator& rhs) const noexcept { return iterator_ == rhs.iterator_; }

        bool operator!=(const Iterator& rhs) const noexcept { return iterator_ != rhs.iterator_; }

    private:
        friend class ObjectFactory;

        explicit Iterator(typename Storage::Iterator iterator) noexcept : iterator_(std::move(iterator)) {}

        typename Storage::Iterator iterator_;
    };

    class FinalizerQueue : private MoveOnly {
    public:
        class Iterator {
        public:
            NodeRef operator*() noexcept { return NodeRef(*iterator_); }
            NodeRef operator->() noexcept { return NodeRef(*iterator_); }

            Iterator& operator++() noexcept {
                ++iterator_;
                return *this;
            }

            bool operator==(const Iterator& rhs) const noexcept { return iterator_ == rhs.iterator_; }
            bool operator!=(const Iterator& rhs) const noexcept { return iterator_ != rhs.iterator_; }

        private:
            friend class ObjectFactory;

            explicit Iterator(typename Storage::Consumer::Iterator iterator) noexcept : iterator_(std::move(iterator)) {}

            typename Storage::Consumer::Iterator iterator_;
        };

        class Iterable {
        public:
            Iterator begin() noexcept { return Iterator(owner_.consumer_.begin()); }
            Iterator end() noexcept { return Iterator(owner_.consumer_.end()); }

        private:
            friend class FinalizerQueue;

            explicit Iterable(FinalizerQueue& owner) : owner_(owner) {}

            FinalizerQueue& owner_;
        };

        size_t size() const noexcept { return consumer_.size(); }

        // TODO: Consider running it in the destructor instead.
        void Finalize() noexcept {
            for (auto node : Iterable(*this)) {
                RunFinalizers(node->IsArray() ? node->GetArrayHeader()->obj() : node->GetObjHeader());
            }
        }

        void MergeWith(FinalizerQueue &&other) {
            consumer_.MergeWith(std::move(other.consumer_));
        }

        Iterable IterForTests() noexcept { return Iterable(*this); }

    private:
        friend class ObjectFactory;

        typename Storage::Consumer consumer_;
    };

    class Iterable {
    public:
        Iterable(ObjectFactory& owner) noexcept : iter_(owner.storage_.LockForIter()) {}

        Iterator begin() noexcept { return Iterator(iter_.begin()); }
        Iterator end() noexcept { return Iterator(iter_.end()); }

        void EraseAndAdvance(Iterator& iterator) noexcept { iter_.EraseAndAdvance(iterator.iterator_); }

        void MoveAndAdvance(FinalizerQueue& queue, Iterator& iterator) noexcept {
            iter_.MoveAndAdvance(queue.consumer_, iterator.iterator_);
        }

    private:
        typename Storage::Iterable iter_;
    };

    ObjectFactory() noexcept = default;
    ~ObjectFactory() = default;

    // Lock ObjectFactory for safe iteration.
    Iterable LockForIter() noexcept { return Iterable(*this); }

    size_t GetSizeUnsafe() const noexcept { return storage_.GetSizeUnsafe(); }

    void ClearForTests() { storage_.ClearForTests(); }

private:
    Storage storage_;
};

} // namespace mm
} // namespace kotlin

#endif // RUNTIME_MM_OBJECT_FACTORY_H
