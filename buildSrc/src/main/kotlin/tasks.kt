/*
 * Copyright 2010-2021 JetBrains s.r.o. and Kotlin Programming Language contributors.
 * Use of this source code is governed by the Apache 2.0 license that can be found in the license/LICENSE.txt file.
 */


// usages in build scripts are not tracked properly
@file:Suppress("unused")

import org.gradle.api.InvalidUserDataException
import org.gradle.api.Project
import org.gradle.api.Task
import org.gradle.api.artifacts.ProjectDependency
import org.gradle.api.file.FileSystemOperations
import org.gradle.api.internal.tasks.testing.filter.DefaultTestFilter
import org.gradle.api.publish.internal.PublishOperation
import org.gradle.api.publish.maven.internal.publication.MavenPublicationInternal
import org.gradle.api.publish.maven.internal.publisher.MavenNormalizedPublication
import org.gradle.api.publish.maven.internal.publisher.MavenPublisher
import org.gradle.api.publish.maven.internal.publisher.ValidatingMavenPublisher
import org.gradle.api.publish.maven.tasks.AbstractPublishToMaven
import org.gradle.api.tasks.TaskAction
import org.gradle.api.tasks.TaskProvider
import org.gradle.api.tasks.testing.Test
import org.gradle.internal.serialization.Cached
import org.gradle.kotlin.dsl.extra
import org.gradle.kotlin.dsl.project
import org.gradle.kotlin.dsl.support.serviceOf
import java.io.File
import java.lang.Character.isLowerCase
import java.lang.Character.isUpperCase
import java.nio.file.Files
import java.nio.file.Path

val kotlinGradlePluginAndItsRequired = arrayOf(
    ":kotlin-allopen",
    ":kotlin-noarg",
    ":kotlin-sam-with-receiver",
    ":kotlin-android-extensions",
    ":kotlin-android-extensions-runtime",
    ":kotlin-parcelize-compiler",
    ":kotlin-build-common",
    ":kotlin-compiler-embeddable",
    ":native:kotlin-native-utils",
    ":kotlin-util-klib",
    ":kotlin-util-io",
    ":kotlin-compiler-runner",
    ":kotlin-daemon-embeddable",
    ":kotlin-daemon-client",
    ":kotlin-project-model",
    ":kotlin-gradle-plugin-api",
    ":kotlin-gradle-plugin",
    ":kotlin-gradle-plugin-model",
    ":kotlin-tooling-metadata",
    ":kotlin-reflect",
    ":kotlin-annotation-processing-gradle",
    ":kotlin-test",
    ":kotlin-gradle-subplugin-example",
    ":kotlin-stdlib-common",
    ":kotlin-stdlib",
    ":kotlin-stdlib-jdk7",
    ":kotlin-stdlib-jdk8",
    ":kotlin-stdlib-js",
    ":examples:annotation-processor-example",
    ":kotlin-script-runtime",
    ":kotlin-scripting-common",
    ":kotlin-scripting-jvm",
    ":kotlin-scripting-compiler-embeddable",
    ":kotlin-scripting-compiler-impl-embeddable",
    ":kotlin-serialization",
    ":kotlin-test-js-runner",
    ":native:kotlin-klib-commonizer-embeddable",
    ":native:kotlin-klib-commonizer-api",
    ":native:kotlin-native-utils"
)

fun Task.dependsOnKotlinGradlePluginInstall() {
    kotlinGradlePluginAndItsRequired.forEach {
        dependsOn("${it}:install")
    }
}

fun Task.dependsOnKotlinGradlePluginPublish() {
    kotlinGradlePluginAndItsRequired.forEach {
        project.rootProject.tasks.findByPath("${it}:publish")?.let { task ->
            dependsOn(task)
        }
    }
}

// Mixing JUnit4 and Junit5 in one module proved to be problematic, consider using separate modules instead
enum class JUnitMode {
    JUnit4, JUnit5
}

/**
 * @param parallel is redundant if @param jUnit5Enabled is true, because
 *   JUnit5 supports parallel test execution by itself, without gradle help
 */
fun Project.projectTest(
    taskName: String = "test",
    parallel: Boolean = false,
    shortenTempRootName: Boolean = false,
    jUnitMode: JUnitMode = JUnitMode.JUnit4,
    body: Test.() -> Unit = {}
): TaskProvider<Test> {
    val shouldInstrument = project.providers.gradleProperty("kotlin.test.instrumentation.disable")
        .forUseAtConfigurationTime().orNull?.toBoolean() != true
    if (shouldInstrument) {
        evaluationDependsOn(":test-instrumenter")
    }
    return getOrCreateTask<Test>(taskName) {
        doFirst {
            if (jUnitMode == JUnitMode.JUnit5) return@doFirst

            val commandLineIncludePatterns = (filter as? DefaultTestFilter)?.commandLineIncludePatterns?.toMutableList() ?: mutableSetOf()
            val patterns = filter.includePatterns + commandLineIncludePatterns
            if (patterns.isEmpty() || patterns.any { '*' in it }) return@doFirst
            patterns.forEach { pattern ->
                var isClassPattern = false
                val maybeMethodName = pattern.substringAfterLast('.')
                val maybeClassFqName = if (maybeMethodName.isFirstChar(::isLowerCase)) {
                    pattern.substringBeforeLast('.')
                } else {
                    isClassPattern = true
                    pattern
                }

                if (!maybeClassFqName.substringAfterLast('.').isFirstChar(::isUpperCase)) {
                    return@forEach
                }

                val classFileNameWithoutExtension = maybeClassFqName.replace('.', '/')
                val classFileName = "$classFileNameWithoutExtension.class"

                if (isClassPattern) {
                    val innerClassPattern = "$pattern$*"
                    if (pattern in commandLineIncludePatterns) {
                        commandLineIncludePatterns.add(innerClassPattern)
                        (filter as? DefaultTestFilter)?.setCommandLineIncludePatterns(commandLineIncludePatterns)
                    } else {
                        filter.includePatterns.add(innerClassPattern)
                    }
                }

                include { treeElement ->
                    val path = treeElement.path
                    if (treeElement.isDirectory) {
                        classFileNameWithoutExtension.startsWith(path)
                    } else {
                        if (path == classFileName) return@include true
                        if (!path.endsWith(".class")) return@include false
                        path.startsWith("$classFileNameWithoutExtension$")
                    }
                }
            }
        }

        if (shouldInstrument) {
            val instrumentationArgsProperty = project.providers.gradleProperty("kotlin.test.instrumentation.args")
            val testInstrumenterOutputs = project.tasks.findByPath(":test-instrumenter:jar")!!.outputs.files
            doFirst {
                val agent = testInstrumenterOutputs.singleFile
                val args = instrumentationArgsProperty.orNull?.let { "=$it" }.orEmpty()
                jvmArgs("-javaagent:$agent$args")
            }
            dependsOn(":test-instrumenter:jar")
        }

        jvmArgs(
            "-ea",
            "-XX:+HeapDumpOnOutOfMemoryError",
            "-XX:+UseCodeCacheFlushing",
            "-XX:ReservedCodeCacheSize=256m",
            "-Djna.nosys=true"
        )

        maxHeapSize = "1600m"
        systemProperty("idea.is.unit.test", "true")
        systemProperty("idea.home.path", project.intellijRootDir().canonicalPath)
        systemProperty("java.awt.headless", "true")
        environment("NO_FS_ROOTS_ACCESS_CHECK", "true")
        environment("PROJECT_CLASSES_DIRS", project.testSourceSet.output.classesDirs.asPath)
        environment("PROJECT_BUILD_DIR", project.buildDir)
        systemProperty("jps.kotlin.home", project.rootProject.extra["distKotlinHomeDir"]!!)
        systemProperty("kotlin.ni", if (project.rootProject.hasProperty("newInferenceTests")) "true" else "false")
        systemProperty("org.jetbrains.kotlin.skip.muted.tests", if (project.rootProject.hasProperty("skipMutedTests")) "true" else "false")
        project.kotlinBuildProperties.junit5NumberOfThreadsForParallelExecution?.let { n ->
            systemProperty("junit.jupiter.execution.parallel.config.strategy", "fixed")
            systemProperty("junit.jupiter.execution.parallel.config.fixed.parallelism", n)
        }

        systemProperty("idea.ignore.disabled.plugins", "true")

        var subProjectTempRoot: Path? = null
        val projectName = project.name
        val teamcity = project.rootProject.findProperty("teamcity") as? Map<*, *>
        doFirst {
            val systemTempRoot =
                // TC by default doesn't switch `teamcity.build.tempDir` to 'java.io.tmpdir' so it could cause to wasted disk space
                // Should be fixed soon on Teamcity side
                (teamcity?.get("teamcity.build.tempDir") as? String)
                    ?: System.getProperty("java.io.tmpdir")
            systemTempRoot.let {
                val prefix = (projectName + "Project_" + taskName + "_").takeUnless { shortenTempRootName }
                subProjectTempRoot = Files.createTempDirectory(File(systemTempRoot).toPath(), prefix)
                systemProperty("java.io.tmpdir", subProjectTempRoot.toString())
            }
        }

        val fs = project.serviceOf<FileSystemOperations>()
        doLast {
            subProjectTempRoot?.let {
                try {
                    fs.delete {
                        delete(it)
                    }
                } catch (e: Exception) {
                    logger.warn("Can't delete test temp root folder $it", e.printStackTrace())
                }
            }
        }

        if (parallel && jUnitMode != JUnitMode.JUnit5) {
            maxParallelForks =
                project.providers.gradleProperty("kotlin.test.maxParallelForks").forUseAtConfigurationTime().orNull?.toInt()
                    ?: (Runtime.getRuntime().availableProcessors() / if (project.kotlinBuildProperties.isTeamcityBuild) 2 else 4).coerceAtLeast(1)
        }
    }.apply { configure(body) }
}

private inline fun String.isFirstChar(f: (Char) -> Boolean) = isNotEmpty() && f(first())

inline fun <reified T : Task> Project.getOrCreateTask(taskName: String, noinline body: T.() -> Unit): TaskProvider<T> =
    if (tasks.names.contains(taskName)) tasks.named(taskName, T::class.java).apply { configure(body) }
    else tasks.register(taskName, T::class.java, body)

object TaskUtils {
    fun useAndroidSdk(task: Task) {
        task.useAndroidConfiguration(systemPropertyName = "android.sdk", configName = "androidSdk")
    }

    fun useAndroidJar(task: Task) {
        task.useAndroidConfiguration(systemPropertyName = "android.jar", configName = "androidJar")
    }

    fun useAndroidEmulator(task: Task) {
        task.useAndroidConfiguration(systemPropertyName = "android.sdk", configName = "androidEmulator")
    }
}

private fun Task.useAndroidConfiguration(systemPropertyName: String, configName: String) {
    val configuration = with(project) {
        configurations.getOrCreate(configName)
            .also {
                if (it.allDependencies.matching { dep ->
                        dep is ProjectDependency &&
                                dep.targetConfiguration == configName &&
                                dep.dependencyProject.path == ":dependencies:android-sdk"
                    }.count() == 0) {
                    dependencies.add(
                        configName,
                        dependencies.project(":dependencies:android-sdk", configuration = configName)
                    )
                }
            }
    }

    dependsOn(configuration)

    if (this is Test) {
        val androidFilePath = configuration.singleFile.canonicalPath
        doFirst {
            systemProperty(systemPropertyName, androidFilePath)
        }
    }
}

fun Task.useAndroidSdk() {
    TaskUtils.useAndroidSdk(this)
}

fun Task.useAndroidJar() {
    TaskUtils.useAndroidJar(this)
}

// Workaround to make PublishToMavenLocal compatible with Gradle configuration cache
// TODO: remove it when https://github.com/gradle/gradle/pull/16945 merged into used in build Gradle version
abstract class PublishToMavenLocalSerializable : AbstractPublishToMaven() {
    private val normalizedPublication = Cached.of { this.computeNormalizedPublication() }

    private fun computeNormalizedPublication(): MavenNormalizedPublication {
        val publicationInternal: MavenPublicationInternal = publicationInternal
            ?: throw InvalidUserDataException("The 'publication' property is required")
        duplicatePublicationTracker.checkCanPublishToMavenLocal(publicationInternal)
        return publicationInternal.asNormalisedPublication()
    }

    @TaskAction
    open fun publish() {
        val normalizedPublication = normalizedPublication.get()
        object : PublishOperation(normalizedPublication.name, "mavenLocal") {
            override fun publish() {
                val localPublisher = mavenPublishers.getLocalPublisher(
                    temporaryDirFactory
                )
                val validatingPublisher: MavenPublisher = ValidatingMavenPublisher(localPublisher)
                validatingPublisher.publish(normalizedPublication, null)
            }
        }.run()
    }
}
