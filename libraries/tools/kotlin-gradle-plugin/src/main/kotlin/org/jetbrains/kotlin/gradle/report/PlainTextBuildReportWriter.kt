/*
 * Copyright 2010-2020 JetBrains s.r.o. and Kotlin Programming Language contributors.
 * Use of this source code is governed by the Apache 2.0 license that can be found in the license/LICENSE.txt file.
 */

package org.jetbrains.kotlin.gradle.report

import org.gradle.api.logging.Logger
import org.jetbrains.kotlin.build.report.metrics.*
import org.jetbrains.kotlin.gradle.report.data.BuildExecutionData
import org.jetbrains.kotlin.gradle.report.data.BuildExecutionDataProcessor
import org.jetbrains.kotlin.gradle.report.data.TaskExecutionData
import org.jetbrains.kotlin.gradle.utils.Printer
import java.io.File
import kotlin.math.max

internal class PlainTextBuildReportWriter(
    private val outputFile: File,
    private val printMetrics: Boolean,
    private val log: Logger
) : BuildExecutionDataProcessor {

    private lateinit var p: Printer

    override fun process(build: BuildExecutionData) {
        try {
            outputFile.parentFile.mkdirs()
            if (!(outputFile.parentFile.exists() && outputFile.parentFile.isDirectory)) {
                log.error("Kotlin build report cannot be created: '$outputFile.parentFile' is a file or do not have permissions to create")
                return
            }

            outputFile.bufferedWriter().use { writer ->
                p = Printer(writer)
                printBuildReport(build)
            }

            log.lifecycle("Kotlin build report is written to ${outputFile.canonicalPath}")
        } catch (e: Exception) {
            log.error("Could not write Kotlin build report to ${outputFile.canonicalPath}", e)
        }
    }

    private fun printBuildReport(build: BuildExecutionData) {
        printBuildInfo(build)
        printMetrics(build.aggregatedMetrics)
        printTaskOverview(build)
        printTasksLog(build)
    }

    private fun printBuildInfo(build: BuildExecutionData) {
        p.withIndent("Gradle start parameters:") {
            build.startParameters.forEach { p.println(it) }
        }

        p.println()
        if (build.failure != null) {
            p.println("Build failed: ${build.failure}")
        }
        p.println()
    }

    private fun printMetrics(buildMetrics: BuildMetrics) {
        if (!printMetrics) return

        printBuildTimes(buildMetrics.buildTimes)
        printBuildPerformanceMetrics(buildMetrics.buildPerformanceMetrics)
        printBuildAttributes(buildMetrics.buildAttributes)
    }

    private fun printBuildTimes(buildTimes: BuildTimes) {
        val collectedBuildTimes = buildTimes.asMap()

        if (collectedBuildTimes.isEmpty()) return

        p.println("Time metrics:")
        p.withIndent {
            val visitedBuildTimes = HashSet<BuildTime>()
            fun printBuildTime(buildTime: BuildTime) {
                if (!visitedBuildTimes.add(buildTime)) return

                val timeMs = collectedBuildTimes[buildTime] ?: return
                p.println("${buildTime.name}: ${formatTime(timeMs)}")
                p.withIndent {
                    BuildTime.children[buildTime]?.forEach { printBuildTime(it) }
                }
            }

            for (buildTime in BuildTime.values()) {
                if (buildTime.parent != null) continue

                printBuildTime(buildTime)
            }
        }
        p.println()
    }

    private fun printBuildPerformanceMetrics(buildMetrics: BuildPerformanceMetrics) {
        val allBuildMetrics = buildMetrics.asMap()
        if (allBuildMetrics.isEmpty()) return

        p.withIndent("Build performance metrics:") {
            for (metric in BuildPerformanceMetric.values()) {
                allBuildMetrics[metric]?.let { p.println("${metric.name}: $it") }
            }
        }
        p.println()
    }

    private fun printBuildAttributes(buildAttributes: BuildAttributes) {
        val allAttributes = buildAttributes.asMap()
        if (allAttributes.isEmpty()) return

        p.withIndent("Build attributes:") {
            val attributesByKind = allAttributes.entries.groupBy { it.key.kind }.toSortedMap()
            for ((kind, attributesCounts) in attributesByKind) {
                printMap(p, kind.name, attributesCounts.map { (k, v) -> k.name to v }.toMap())
            }
        }
        p.println()
    }

    private fun printTaskOverview(build: BuildExecutionData) {
        var allTasksTimeMs = 0L
        var kotlinTotalTimeMs = 0L
        val kotlinTasks = ArrayList<TaskExecutionData>()

        for (task in build.taskExecutionData) {
            val taskTimeMs = task.totalTimeMs
            allTasksTimeMs += taskTimeMs

            if (task.isKotlinTask) {
                kotlinTotalTimeMs += taskTimeMs
                kotlinTasks.add(task)
            }
        }

        if (kotlinTasks.isEmpty()) {
            p.println("No Kotlin task was run")
            return
        }

        val ktTaskPercent = (kotlinTotalTimeMs.toDouble() / allTasksTimeMs * 100).asString(1)
        p.println("Total time for Kotlin tasks: ${formatTime(kotlinTotalTimeMs)} ($ktTaskPercent % of all tasks time)")

        val table = TextTable("Time", "% of Kotlin time", "Task")
        for (task in kotlinTasks.sortedByDescending { it.totalTimeMs }) {
            val timeMs = task.totalTimeMs
            val percent = (timeMs.toDouble() / kotlinTotalTimeMs * 100).asString(1)
            table.addRow(formatTime(timeMs), "$percent %", task.task.path)
        }
        table.printTo(p)
        p.println()
    }

    private fun printTasksLog(build: BuildExecutionData) {
        for (task in build.taskExecutionData) {
            printTaskLog(task)
            p.println()
        }
    }

    private fun printTaskLog(task: TaskExecutionData) {
        val skipMessage = task.resultState.skipMessage
        if (skipMessage != null) {
            p.println("Task '${task.task.path}' was skipped: $skipMessage")
        } else {
            p.println("Task '${task.task.path}' finished in ${formatTime(task.totalTimeMs)}")
        }

        if (task.icLogLines.isNotEmpty()) {
            p.withIndent("Compilation log for task '${task.task.path}':") {
                task.icLogLines.forEach { p.println(it) }
            }
        }

        printMetrics(task.buildMetrics)
    }
}

private fun printMap(p: Printer, name: String, mapping: Map<String, Int>) {
    if (mapping.isEmpty()) return

    if (mapping.size == 1) {
        p.println("$name: ${mapping.keys.single()}")
        return
    }

    p.withIndent("$name:") {
        val sortedEnumMap = mapping.toSortedMap()
        for ((k, v) in sortedEnumMap) {
            p.println("$k($v)")
        }
    }
}

private class TextTable(vararg columnNames: String) {
    private val rows = ArrayList<List<String>>()
    private val columnsCount = columnNames.size
    private val maxLengths = IntArray(columnsCount) { columnNames[it].length }

    init {
        rows.add(columnNames.toList())
    }

    fun addRow(vararg row: String) {
        check(row.size == columnsCount) { "Row size ${row.size} differs from columns count $columnsCount" }
        rows.add(row.toList())

        for ((i, col) in row.withIndex()) {
            maxLengths[i] = max(maxLengths[i], col.length)
        }
    }

    fun printTo(p: Printer) {
        for (row in rows) {
            val rowStr = row.withIndex().joinToString("|") { (i, col) -> col.padEnd(maxLengths[i], ' ') }
            p.println(rowStr)
        }
    }
}
