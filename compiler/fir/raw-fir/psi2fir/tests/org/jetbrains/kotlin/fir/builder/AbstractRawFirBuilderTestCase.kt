/*
 * Copyright 2010-2018 JetBrains s.r.o. and Kotlin Programming Language contributors.
 * Use of this source code is governed by the Apache 2.0 license that can be found in the license/LICENSE.txt file.
 */

package org.jetbrains.kotlin.fir.builder

import com.intellij.openapi.fileTypes.FileTypeManager
import com.intellij.openapi.fileTypes.FileTypeRegistry
import com.intellij.openapi.util.Getter
import com.intellij.openapi.util.io.FileUtil
import com.intellij.openapi.util.io.FileUtilRt
import com.intellij.psi.PsiFile
import com.intellij.psi.tree.IElementType
import com.intellij.util.PathUtil
import org.jetbrains.kotlin.KtNodeTypes
import org.jetbrains.kotlin.fir.*
import org.jetbrains.kotlin.fir.contracts.impl.FirEmptyContractDescription
import org.jetbrains.kotlin.fir.declarations.FirFile
import org.jetbrains.kotlin.fir.declarations.FirTypeParameter
import org.jetbrains.kotlin.fir.declarations.FirValueParameter
import org.jetbrains.kotlin.fir.declarations.impl.FirResolvedDeclarationStatusImpl
import org.jetbrains.kotlin.fir.expressions.FirAnnotation
import org.jetbrains.kotlin.fir.expressions.FirAnnotationArgumentMapping
import org.jetbrains.kotlin.fir.expressions.FirEmptyArgumentList
import org.jetbrains.kotlin.fir.expressions.FirExpression
import org.jetbrains.kotlin.fir.expressions.impl.FirNoReceiverExpression
import org.jetbrains.kotlin.fir.expressions.impl.FirStubStatement
import org.jetbrains.kotlin.fir.references.impl.FirStubReference
import org.jetbrains.kotlin.fir.session.FirSessionFactory
import org.jetbrains.kotlin.fir.types.FirTypeProjection
import org.jetbrains.kotlin.fir.types.FirTypeRef
import org.jetbrains.kotlin.fir.types.isExtensionFunctionAnnotationCall
import org.jetbrains.kotlin.fir.visitors.FirTransformer
import org.jetbrains.kotlin.fir.visitors.FirVisitorVoid
import org.jetbrains.kotlin.parsing.KotlinParserDefinition
import org.jetbrains.kotlin.psi
import org.jetbrains.kotlin.psi.KtFile
import org.jetbrains.kotlin.psi.KtPropertyDelegate
import org.jetbrains.kotlin.psi.KtPsiFactory
import org.jetbrains.kotlin.test.KotlinTestUtils
import org.jetbrains.kotlin.test.testFramework.KtParsingTestCase
import org.jetbrains.kotlin.test.util.KtTestUtil
import java.io.File
import kotlin.reflect.full.memberProperties
import kotlin.reflect.jvm.isAccessible

abstract class AbstractRawFirBuilderTestCase : KtParsingTestCase(
    "",
    "kt",
    KotlinParserDefinition()
) {
    override fun getTestDataPath() = KtTestUtil.getHomeDirectory()

    private fun createFile(filePath: String, fileType: IElementType): PsiFile {
        val psiFactory = KtPsiFactory(myProject)
        return when (fileType) {
            KtNodeTypes.EXPRESSION_CODE_FRAGMENT ->
                psiFactory.createExpressionCodeFragment(loadFile(filePath), null)
            KtNodeTypes.BLOCK_CODE_FRAGMENT ->
                psiFactory.createBlockCodeFragment(loadFile(filePath), null)
            else ->
                createPsiFile(FileUtil.getNameWithoutExtension(PathUtil.getFileName(filePath)), loadFile(filePath))
        }
    }

    protected open fun doRawFirTest(filePath: String) {
        val file = createKtFile(filePath)
        val firFile = file.toFirFile(BodyBuildingMode.NORMAL)
        val firFileDump = StringBuilder().also { FirRenderer(it, mode = FirRenderer.RenderMode.WithDeclarationAttributes).visitFile(firFile) }.toString()
        val expectedPath = filePath.replace(".kt", ".txt")
        KotlinTestUtils.assertEqualsToFile(File(expectedPath), firFileDump)
    }

    protected fun createKtFile(filePath: String): KtFile {
        myFileExt = FileUtilRt.getExtension(PathUtil.getFileName(filePath))
        return (createFile(filePath, KtNodeTypes.KT_FILE) as KtFile).apply {
            myFile = this
        }
    }

    protected fun KtFile.toFirFile(bodyBuildingMode: BodyBuildingMode = BodyBuildingMode.NORMAL): FirFile {
        val session = FirSessionFactory.createEmptySession()
        return RawFirBuilder(
            session,
            StubFirScopeProvider,
            psiMode = PsiHandlingMode.COMPILER,
            bodyBuildingMode = bodyBuildingMode
        ).buildFirFile(this)
    }

    private fun FirElement.traverseChildren(result: MutableSet<FirElement> = hashSetOf()): MutableSet<FirElement> {
        if (!result.add(this)) {
            return result
        }
        for (property in this::class.memberProperties) {
            if (hasNoAcceptAndTransform(this::class.simpleName, property.name)) continue

            when (val childElement = property.getter.apply { isAccessible = true }.call(this)) {
                is FirNoReceiverExpression -> continue
                is FirElement -> childElement.traverseChildren(result)
                is List<*> -> childElement.filterIsInstance<FirElement>().forEach { it.traverseChildren(result) }
                else -> continue
            }

        }
        return result
    }

    private val firImplClassPropertiesWithNoAcceptAndTransform = mapOf(
        "FirResolvedImportImpl" to "delegate",
        "FirErrorTypeRefImpl" to "delegatedTypeRef",
        "FirResolvedTypeRefImpl" to "delegatedTypeRef"
    )

    private fun hasNoAcceptAndTransform(className: String?, propertyName: String): Boolean {
        if (className == null) return false
        return firImplClassPropertiesWithNoAcceptAndTransform[className] == propertyName
    }

    private fun FirFile.visitChildren(): Set<FirElement> =
        ConsistencyVisitor().let {
            this@visitChildren.accept(it)
            it.result
        }

    private fun FirFile.transformChildren(): Set<FirElement> =
        ConsistencyTransformer().let {
            this@transformChildren.transform<FirFile, Unit>(it, Unit)
            it.result
        }

    protected fun FirFile.checkChildren() {
        val children = traverseChildren()
        val visitedChildren = visitChildren()
        children.removeAll(visitedChildren)
        if (children.isNotEmpty()) {
            val element = children.firstOrNull { it !is FirAnnotationArgumentMapping } ?: return
            val elementDump = element.render()
            throw AssertionError("FirElement ${element.javaClass} is not visited: $elementDump")
        }
    }

    protected fun FirFile.checkTransformedChildren() {
        val children = traverseChildren()
        val transformedChildren = transformChildren()
        children.removeAll(transformedChildren)
        if (children.isNotEmpty()) {
            val element = children.firstOrNull { it !is FirAnnotationArgumentMapping } ?: return
            val elementDump = element.render()
            throw AssertionError("FirElement ${element.javaClass} is not transformed: $elementDump")
        }
    }

    private class ConsistencyVisitor : FirVisitorVoid() {
        var result = hashSetOf<FirElement>()

        override fun visitElement(element: FirElement) {
            // NB: types are reused sometimes (e.g. in accessors)
            if (!result.add(element)) {
                throwTwiceVisitingError(element)
            } else {
                element.acceptChildren(this)
            }
        }
    }

    private class ConsistencyTransformer : FirTransformer<Unit>() {
        var result = hashSetOf<FirElement>()

        override fun <E : FirElement> transformElement(element: E, data: Unit): E {
            if (!result.add(element)) {
                throwTwiceVisitingError(element)
            } else {
                element.transformChildren(this, Unit)
            }
            return element
        }
    }

    override fun tearDown() {
        super.tearDown()
        FileTypeRegistry.ourInstanceGetter = Getter<FileTypeRegistry> { FileTypeManager.getInstance() }
    }

}

private fun throwTwiceVisitingError(element: FirElement) {
    if (element is FirTypeRef || element is FirNoReceiverExpression || element is FirTypeParameter ||
        element is FirTypeProjection || element is FirValueParameter || element is FirAnnotation ||
        element is FirEmptyContractDescription ||
        element is FirStubReference || element.isExtensionFunctionAnnotation || element is FirEmptyArgumentList ||
        element is FirStubStatement || element === FirResolvedDeclarationStatusImpl.DEFAULT_STATUS_FOR_STATUSLESS_DECLARATIONS
    ) {
        return
    }
    if (element is FirExpression) {
        val psiParent = element.source?.psi?.parent
        if (psiParent is KtPropertyDelegate || psiParent?.parent is KtPropertyDelegate) return
    }

    val elementDump = StringBuilder().also { element.accept(FirRenderer(it)) }.toString()
    throw AssertionError("FirElement ${element.javaClass} is visited twice: $elementDump")
}


private val FirElement.isExtensionFunctionAnnotation: Boolean
    get() = (this as? FirAnnotation)?.isExtensionFunctionAnnotationCall == true
