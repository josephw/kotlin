import org.jetbrains.kotlin.gradle.tasks.KotlinCompile
import java.util.Properties
import java.io.FileReader

extra["versions.native-platform"] = "0.14"



buildscript {
    java.util.Properties().also {
        it.load(java.io.FileReader(project.file("../../../gradle.properties")))
    }.forEach { k, v->
        val key = k as String
        val value = project.findProperty(key) ?: v
        project.logger.info("${project.name}<<<[$key] = $value>>>")
        extra[key] = value
    }
    val cacheRedirectorEnabled = findProperty("cacheRedirectorEnabled")?.toString()?.toBoolean() ?: false

    extra["defaultSnapshotVersion"] = kotlinBuildProperties.defaultSnapshotVersion
    kotlinBootstrapFrom(BootstrapOption.SpaceBootstrap(kotlinBuildProperties.kotlinBootstrapVersion!!, cacheRedirectorEnabled))

    repositories {
        maven("https://maven.pkg.jetbrains.space/kotlin/p/kotlin/kotlin-dependencies")
        jcenter()
        mavenCentral()
        project.bootstrapKotlinRepo?.let {
            maven(url = it)
        }
    }

    dependencies {
        classpath("org.jetbrains.kotlin:kotlin-build-gradle-plugin:0.0.32")
        classpath("org.jetbrains.kotlin:kotlin-gradle-plugin:${project.bootstrapKotlinVersion}")
    }
}

apply{
    plugin("kotlin")
    plugin("kotlin-sam-with-receiver")
}
plugins {
    `kotlin-dsl`
    //kotlin("multiplatform") version "${project.bootstrapKotlinVersion}"
}

val cacheRedirectorEnabled = findProperty("cacheRedirectorEnabled")?.toString()?.toBoolean() == true
repositories {
    maven("https://maven.pkg.jetbrains.space/kotlin/p/kotlin/kotlin-dependencies")
    jcenter()
    mavenCentral()
    gradlePluginPortal()
    extra["bootstrapKotlinRepo"]?.let {
        maven(url = it)
    }
}

tasks.validatePlugins.configure {
    enabled = false
}


sourceSets["main"].withConvention(org.jetbrains.kotlin.gradle.plugin.KotlinSourceSet::class) {
    kotlin.filter.exclude("**/FileCheckTest.kt")
    kotlin.filter.exclude("**/bitcode/**")
    kotlin.filter.exclude("**/testing/**")
    kotlin.filter.exclude("**/CompilationDatabase.kt")

    kotlin.srcDir("src/main/kotlin")
    kotlin.srcDir("../../build-tools/src/main/kotlin")
    kotlin.srcDir("../../shared/src/library/kotlin")
    kotlin.srcDir("../../shared/src/main/kotlin")
    kotlin.srcDir("../../tools/benchmarks/shared/src/main/kotlin/report")
    kotlin.srcDir("../../../native/utils/src")
}

tasks.withType<KotlinCompile>().configureEach {
    kotlinOptions.freeCompilerArgs +=
        listOf("-opt-in=kotlin.RequiresOptIn", "-opt-in=kotlin.ExperimentalStdlibApi")
}


dependencies {
    implementation("org.jetbrains.kotlin:kotlin-build-gradle-plugin:0.0.32")
    implementation("org.jetbrains.kotlin:kotlin-gradle-plugin:${project.bootstrapKotlinVersion}")
    api("org.jetbrains.kotlin:kotlin-native-utils:${project.bootstrapKotlinVersion}")
    api("org.jetbrains.kotlin:kotlin-util-klib:${project.bootstrapKotlinVersion}")
    compileOnly(gradleApi())
    val kotlinVersion = project.bootstrapKotlinVersion
    val ktorVersion  = "1.2.1"
    val slackApiVersion = "1.2.0"
    val shadowVersion = "5.1.0"
    val metadataVersion = "0.0.1-dev-10"

    implementation("org.jetbrains.kotlin:kotlin-gradle-plugin:$kotlinVersion")
    implementation("org.jetbrains.kotlin:kotlin-stdlib:$kotlinVersion")
    implementation("org.jetbrains.kotlin:kotlin-reflect:$kotlinVersion")
    implementation("com.ullink.slack:simpleslackapi:$slackApiVersion")

    implementation("io.ktor:ktor-client-auth:$ktorVersion")
    implementation("io.ktor:ktor-client-core:$ktorVersion")
    implementation("io.ktor:ktor-client-cio:$ktorVersion")

    api("org.jetbrains.kotlin:kotlin-native-utils:$kotlinVersion")

    // Located in <repo root>/shared and always provided by the composite build.
    //api("org.jetbrains.kotlin:kotlin-native-shared:$konanVersion")
    implementation("com.github.jengelman.gradle.plugins:shadow:$shadowVersion")

    implementation("org.jetbrains.kotlinx:kotlinx-metadata-klib:$metadataVersion")
}

gradlePlugin {
    plugins {
        create("benchmarkPlugin") {
            id = "benchmarking"
            implementationClass = "org.jetbrains.kotlin.benchmark.KotlinNativeBenchmarkingPlugin"
        }
        create("compileBenchmarking") {
            id = "compile-benchmarking"
            implementationClass = "org.jetbrains.kotlin.benchmark.CompileBenchmarkingPlugin"
        }
        create("swiftBenchmarking") {
            id = "swift-benchmarking"
            implementationClass = "org.jetbrains.kotlin.benchmark.SwiftBenchmarkingPlugin"
        }
        create("compileToBitcode") {
            id = "compile-to-bitcode"
            implementationClass = "org.jetbrains.kotlin.bitcode.CompileToBitcodePlugin"
        }
        create("runtimeTesting") {
            id = "runtime-testing"
            implementationClass = "org.jetbrains.kotlin.testing.native.RuntimeTestingPlugin"
        }
    }
}

afterEvaluate {
    tasks.withType<KotlinCompile>().configureEach {
        kotlinOptions {
            languageVersion = "1.4"
            apiVersion = "1.4"
        }
    }
}
