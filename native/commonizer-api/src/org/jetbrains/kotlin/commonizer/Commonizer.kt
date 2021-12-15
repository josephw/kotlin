/*
 * Copyright 2010-2021 JetBrains s.r.o. and Kotlin Programming Language contributors.
 * Use of this source code is governed by the Apache 2.0 license that can be found in the license/LICENSE.txt file.
 */

package org.jetbrains.kotlin.commonizer

import org.jetbrains.kotlin.commonizer.cli.CommonizerSettingOptionType
import java.io.File
import java.io.Serializable

public interface CInteropCommonizer : Serializable {
    @Throws(Throwable::class)
    public fun commonizeLibraries(
        konanHome: File,
        inputLibraries: Set<File>,
        dependencyLibraries: Set<CommonizerDependency>,
        outputTargets: Set<SharedCommonizerTarget>,
        outputDirectory: File,
        logLevel: CommonizerLogLevel = CommonizerLogLevel.Quiet,
        additionalSettings: List<CommonizerSetting<*>> = emptyList(),
    )
}

public interface NativeDistributionCommonizer : Serializable {
    @Throws(Throwable::class)
    public fun commonizeNativeDistribution(
        konanHome: File,
        outputDirectory: File,
        outputTargets: Set<SharedCommonizerTarget>,
        logLevel: CommonizerLogLevel = CommonizerLogLevel.Quiet,
        additionalSettings: List<CommonizerSetting<*>> = emptyList(),
    )
}

public data class CommonizerSetting<T : Any>(
    public val settingType: CommonizerSettingOptionType<T>,
    public val settingValue: T,
)

public infix fun <T : Any> CommonizerSettingOptionType<T>.setTo(settingValue: T): CommonizerSetting<T> =
    CommonizerSetting(this, settingValue)
