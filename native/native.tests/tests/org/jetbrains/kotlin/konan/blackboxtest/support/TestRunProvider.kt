/*
 * Copyright 2010-2021 JetBrains s.r.o. and Kotlin Programming Language contributors.
 * Use of this source code is governed by the Apache 2.0 license that can be found in the license/LICENSE.txt file.
 */

@file:Suppress("KDocUnresolvedReference")

package org.jetbrains.kotlin.konan.blackboxtest.support

import com.intellij.openapi.util.Disposer
import org.jetbrains.kotlin.konan.blackboxtest.support.TestCase.NoTestRunnerExtras
import org.jetbrains.kotlin.konan.blackboxtest.support.TestCompilationResult.Companion.assertSuccess
import org.jetbrains.kotlin.konan.blackboxtest.support.group.TestCaseGroupProvider
import org.jetbrains.kotlin.konan.blackboxtest.support.runner.AbstractRunner
import org.jetbrains.kotlin.konan.blackboxtest.support.runner.LocalTestFunctionExtractor
import org.jetbrains.kotlin.konan.blackboxtest.support.runner.LocalTestRunner
import org.jetbrains.kotlin.konan.blackboxtest.support.settings.GlobalSettings
import org.jetbrains.kotlin.konan.blackboxtest.support.settings.Settings
import org.jetbrains.kotlin.konan.blackboxtest.support.util.ThreadSafeCache
import org.jetbrains.kotlin.konan.blackboxtest.support.util.TreeNode
import org.jetbrains.kotlin.konan.blackboxtest.support.util.buildTree
import org.jetbrains.kotlin.konan.blackboxtest.support.util.isSameOrSubpackageOf
import org.jetbrains.kotlin.test.services.JUnit5Assertions.assertTrue
import org.jetbrains.kotlin.test.services.JUnit5Assertions.fail
import org.junit.jupiter.api.Assumptions.assumeTrue
import org.junit.jupiter.api.extension.ExtensionContext
import java.io.File

internal class TestRunProvider(
    private val settings: Settings,
    private val testCaseGroupProvider: TestCaseGroupProvider
) : ExtensionContext.Store.CloseableResource {
    private val compilationFactory = TestCompilationFactory(settings)
    private val cachedCompilations = ThreadSafeCache<TestCompilationCacheKey, TestCompilation>()
    private val cachedTestFunctions = ThreadSafeCache<TestCompilationCacheKey, Collection<TestFunction>>()

    fun setProcessors(testDataFile: File, sourceTransformers: List<(String) -> String>) {
        testCaseGroupProvider.setPreprocessors(testDataFile, sourceTransformers)
    }

    /**
     * Produces a single [TestRun] per [TestCase]. So-called "one test case/one test run" mode.
     *
     * If [TestCase] contains multiple functions annotated with [kotlin.test.Test], then all these functions will be executed
     * in one shot. If either function will fail, the whole JUnit test will be considered as failed.
     *
     * Example:
     *   //+++ testData file (foo.kt): +++//
     *   @kotlin.test.Test
     *   fun one() { /* ... */ }
     *
     *   @kotlin.test.Test
     *   fun two() { /* ... */ }
     *
     *   //+++ generated JUnit test suite: +++//
     *   public class MyTestSuiteGenerated {
     *       @org.junit.jupiter.api.Test
     *       @org.jetbrains.kotlin.test.TestMetadata("foo.kt")
     *       public void testFoo() {
     *           // Compiles foo.kt with test-runner, probably together with other testData files (bar.kt, qux.kt, ...).
     *           // Then executes FooKt.one() and FooKt.two() test functions one after another in one shot.
     *           // If either of test functions fails, the whole "testFoo()" JUnit test is marked as failed.
     *       }
     *   }
     */
    fun getSingleTestRun(testCaseId: TestCaseId): TestRun = withTestExecutable(testCaseId) { testCase, executable, _ ->
        val runParameters = getRunParameters(testCase, testFunction = null)
        TestRun(displayName = /* Unimportant. Used only in dynamic tests. */ "", executable, runParameters, testCase.id)
    }

    /**
     * Produces at least one [TestRun] per [TestCase]. So-called "one test function/one test run" mode.
     *
     * If [TestCase] contains multiple functions annotated with [kotlin.test.Test], then a separate [TestRun] will be produced
     * for each such function.
     *
     * This allows to have a better granularity in tests. So that every individual test method inside [TestCase] will be considered
     * as an individual JUnit test, and will be presented as a separate row in JUnit test report.
     *
     * Example:
     *   //+++ testData file (foo.kt): +++//
     *   @kotlin.test.Test
     *   fun one() { /* ... */ }
     *
     *   @kotlin.test.Test
     *   fun two() { /* ... */ }
     *
     *   //+++ generated JUnit test suite: +++//
     *   public class MyTestSuiteGenerated {
     *       @org.junit.jupiter.api.TestFactory
     *       @org.jetbrains.kotlin.test.TestMetadata("foo.kt")
     *       public Collection<org.junit.jupiter.api.DynamicNode> testFoo() {
     *           // Compiles foo.kt with test-runner, probably together with other testData files (bar.kt, qux.kt, ...).
     *           // Then produces two instances of DynamicTest for FooKt.one() and FooKt.two() functions.
     *           // Each DynamicTest is executed as a separate JUnit test.
     *           // So if FooKt.one() fails and FooKt.two() succeeds, then "testFoo.one" JUnit test will be presented as failed
     *           // in the test report, and "testFoo.two" will be presented as passed.
     *       }
     *   }
     */
    fun getTestRuns(
        testCaseId: TestCaseId
    ): Collection<TreeNode<TestRun>> = withTestExecutable(testCaseId) { testCase, executable, cacheKey ->
        fun createTestRun(testRunName: String, testFunction: TestFunction?): TestRun {
            val runParameters = getRunParameters(testCase, testFunction)
            return TestRun(testRunName, executable, runParameters, testCase.id)
        }

        when (testCase.kind) {
            TestKind.STANDALONE_NO_TR -> {
                val testRunName = testCase.extras<NoTestRunnerExtras>().entryPoint.substringAfterLast('.')
                val testRun = createTestRun(testRunName, testFunction = null)
                TreeNode.oneLevel(testRun)
            }
            TestKind.REGULAR, TestKind.STANDALONE -> {
                val testFunctions = cachedTestFunctions.computeIfAbsent(cacheKey) {
                    extractTestFunctions(executable)
                }.filterIrrelevant(testCase)

                testFunctions.buildTree(TestFunction::packageName) { testFunction ->
                    createTestRun(testFunction.functionName, testFunction)
                }
            }
        }
    }

    private fun <T> withTestExecutable(testCaseId: TestCaseId, action: (TestCase, TestExecutable, TestCompilationCacheKey) -> T): T {
        settings.assertNotDisposed()

        val testCaseGroup = testCaseGroupProvider.getTestCaseGroup(testCaseId.testCaseGroupId) ?: fail { "No test case for $testCaseId" }
        assumeTrue(testCaseGroup.isEnabled(testCaseId), "Test case is disabled")

        val testCase = testCaseGroup.getByName(testCaseId) ?: fail { "No test case for $testCaseId" }

        val (testCompilation, cacheKey) = when (testCase.kind) {
            TestKind.STANDALONE, TestKind.STANDALONE_NO_TR -> {
                // Create a separate compilation for each standalone test case.
                val cacheKey = TestCompilationCacheKey.Standalone(testCaseId)
                val testCompilation = cachedCompilations.computeIfAbsent(cacheKey) {
                    compilationFactory.testCasesToExecutable(listOf(testCase))
                }
                testCompilation to cacheKey
            }
            TestKind.REGULAR -> {
                // Group regular test cases by compiler arguments.
                val cacheKey = TestCompilationCacheKey.Grouped(testCaseId.testCaseGroupId, testCase.freeCompilerArgs)
                val testCompilation = cachedCompilations.computeIfAbsent(cacheKey) {
                    val testCases = testCaseGroup.getRegularOnlyByCompilerArgs(testCase.freeCompilerArgs)
                    assertTrue(testCases.isNotEmpty())
                    compilationFactory.testCasesToExecutable(testCases)
                }
                testCompilation to cacheKey
            }
        }

        val (executableFile, loggedCompilerCall) = testCompilation.result.assertSuccess() // <-- Compilation happens here.
        val executable = TestExecutable(executableFile, loggedCompilerCall)

        return action(testCase, executable, cacheKey)
    }

    private fun getRunParameters(testCase: TestCase, testFunction: TestFunction?): List<TestRunParameter> = with(testCase) {
        when (kind) {
            TestKind.STANDALONE_NO_TR -> {
                assertTrue(testFunction == null)
                listOfNotNull(
                    extras<NoTestRunnerExtras>().inputDataFile?.let(TestRunParameter::WithInputData),
                    expectedOutputDataFile?.let(TestRunParameter::WithExpectedOutputData)
                )
            }
            TestKind.STANDALONE -> listOfNotNull(
                TestRunParameter.WithTCTestLogger,
                testFunction?.let(TestRunParameter::WithFunctionFilter),
                expectedOutputDataFile?.let(TestRunParameter::WithExpectedOutputData)
            )
            TestKind.REGULAR -> listOfNotNull(
                TestRunParameter.WithTCTestLogger,
                testFunction?.let(TestRunParameter::WithFunctionFilter) ?: TestRunParameter.WithPackageFilter(nominalPackageName),
                expectedOutputDataFile?.let(TestRunParameter::WithExpectedOutputData)
            )
        }
    }

    // Currently, only local test runner is supported.
    fun createRunner(testRun: TestRun): AbstractRunner<*> = with(settings.get<GlobalSettings>()) {
        if (target == hostTarget)
            LocalTestRunner(testRun, executionTimeout)
        else
            runningAtNonHostTarget()
    }

    // Currently, only local test function extractor is supported.
    private fun extractTestFunctions(executable: TestExecutable): Collection<TestFunction> = with(settings.get<GlobalSettings>()) {
        if (target == hostTarget)
            LocalTestFunctionExtractor(executable, executionTimeout).run()
        else
            runningAtNonHostTarget()
    }

    private fun Collection<TestFunction>.filterIrrelevant(testCase: TestCase) =
        if (testCase.kind == TestKind.REGULAR)
            filter { testFunction -> testFunction.packageName.isSameOrSubpackageOf(testCase.nominalPackageName) }
        else
            this

    private fun GlobalSettings.runningAtNonHostTarget(): Nothing = fail {
        """
            Running at non-host target is not supported yet.
            Compilation target: $target
            Host target: $hostTarget
        """.trimIndent()
    }

    override fun close() {
        Disposer.dispose(settings)
    }

    private sealed class TestCompilationCacheKey {
        data class Standalone(val testCaseId: TestCaseId) : TestCompilationCacheKey()
        data class Grouped(val testCaseGroupId: TestCaseGroupId, val freeCompilerArgs: TestCompilerArgs) : TestCompilationCacheKey()
    }
}
