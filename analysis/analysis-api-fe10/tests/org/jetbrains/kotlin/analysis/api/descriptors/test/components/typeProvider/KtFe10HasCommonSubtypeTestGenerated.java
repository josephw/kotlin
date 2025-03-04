/*
 * Copyright 2010-2021 JetBrains s.r.o. and Kotlin Programming Language contributors.
 * Use of this source code is governed by the Apache 2.0 license that can be found in the license/LICENSE.txt file.
 */

package org.jetbrains.kotlin.analysis.api.descriptors.test.components.typeProvider;

import com.intellij.testFramework.TestDataPath;
import org.jetbrains.kotlin.test.util.KtTestUtil;
import org.jetbrains.kotlin.test.TestMetadata;
import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;

import java.io.File;
import java.util.regex.Pattern;

/** This class is generated by {@link GenerateNewCompilerTests.kt}. DO NOT MODIFY MANUALLY */
@SuppressWarnings("all")
@TestMetadata("analysis/analysis-api/testData/components/typeProvider/haveCommonSubtype")
@TestDataPath("$PROJECT_ROOT")
public class KtFe10HasCommonSubtypeTestGenerated extends AbstractKtFe10HasCommonSubtypeTest {
    @Test
    public void testAllFilesPresentInHaveCommonSubtype() throws Exception {
        KtTestUtil.assertAllTestsPresentByMetadataWithExcluded(this.getClass(), new File("analysis/analysis-api/testData/components/typeProvider/haveCommonSubtype"), Pattern.compile("^(.+)\\.kt$"), null, true);
    }

    @Test
    @TestMetadata("collections.kt")
    public void testCollections() throws Exception {
        runTest("analysis/analysis-api/testData/components/typeProvider/haveCommonSubtype/collections.kt");
    }

    @Test
    @TestMetadata("dataClasses.kt")
    public void testDataClasses() throws Exception {
        runTest("analysis/analysis-api/testData/components/typeProvider/haveCommonSubtype/dataClasses.kt");
    }

    @Test
    @TestMetadata("enums.kt")
    public void testEnums() throws Exception {
        runTest("analysis/analysis-api/testData/components/typeProvider/haveCommonSubtype/enums.kt");
    }

    @Test
    @TestMetadata("simple.kt")
    public void testSimple() throws Exception {
        runTest("analysis/analysis-api/testData/components/typeProvider/haveCommonSubtype/simple.kt");
    }
}
