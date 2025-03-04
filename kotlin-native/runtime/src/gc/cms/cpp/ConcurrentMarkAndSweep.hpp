/*
 * Copyright 2010-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license
 * that can be found in the LICENSE file.
 */

#pragma once

#include <cstddef>

#include "Allocator.hpp"
#include "GCScheduler.hpp"
#include "ObjectFactory.hpp"
#include "Types.h"
#include "Utils.hpp"
#include "GCState.hpp"

namespace kotlin {

namespace mm {
class ThreadData;
}

namespace gc {

class FinalizerProcessor;

// Stop-the-world mark + concurrent sweep. The GC runs in a separate thread, finalizers run in another thread of their own.
// TODO: Also make mark concurrent.
class ConcurrentMarkAndSweep : private Pinned {
public:

    class ObjectData {
    public:
        enum class Color {
            kWhite = 0, // Initial color at the start of collection cycles. Objects with this color at the end of GC cycle are collected.
                        // All new objects are allocated with this color.
            kBlack, // Objects encountered during mark phase.
        };

        Color color() const noexcept { return color_; }
        void setColor(Color color) noexcept { color_ = color; }

    private:
        Color color_ = Color::kWhite;
    };

    class ThreadData : private Pinned {
    public:
        using ObjectData = ConcurrentMarkAndSweep::ObjectData;
        using Allocator = AllocatorWithGC<AlignedAllocator, ThreadData>;

        explicit ThreadData(ConcurrentMarkAndSweep& gc, mm::ThreadData& threadData) noexcept : gc_(gc), threadData_(threadData) {}
        ~ThreadData() = default;

        void SafePointFunctionPrologue() noexcept;
        void SafePointLoopBody() noexcept;
        void SafePointExceptionUnwind() noexcept;
        void SafePointAllocation(size_t size) noexcept;

        void ScheduleAndWaitFullGC() noexcept;
        void ScheduleAndWaitFullGCWithFinalizers() noexcept;
        void StopFinalizerThreadForTests() noexcept;

        void OnOOM(size_t size) noexcept;

        Allocator CreateAllocator() noexcept { return Allocator(AlignedAllocator(), *this); }

    private:
        void SafePointRegular(size_t weight) noexcept;

        ConcurrentMarkAndSweep& gc_;
        mm::ThreadData& threadData_;
    };

    using Allocator = ThreadData::Allocator;

    ConcurrentMarkAndSweep() noexcept;
    ~ConcurrentMarkAndSweep();

private:
    // Returns `true` if GC has happened, and `false` if not (because someone else has suspended the threads).
    bool PerformFullGC(int64_t epoch) noexcept;

    uint64_t lastGCTimestampUs_ = 0;
    GCStateHolder state_;
    std::thread gcThread_;
    KStdUniquePtr<FinalizerProcessor> finalizerProcessor_;
};

} // namespace gc
} // namespace kotlin
