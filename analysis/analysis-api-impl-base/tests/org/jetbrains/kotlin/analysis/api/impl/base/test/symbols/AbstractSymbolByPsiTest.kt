/*
 * Copyright 2010-2020 JetBrains s.r.o. and Kotlin Programming Language contributors.
 * Use of this source code is governed by the Apache 2.0 license that can be found in the license/LICENSE.txt file.
 */

package org.jetbrains.kotlin.analysis.api.impl.base.test.symbols

import org.jetbrains.kotlin.analysis.api.KtAnalysisSession
import org.jetbrains.kotlin.analysis.api.impl.barebone.test.FrontendApiTestConfiguratorService
import org.jetbrains.kotlin.analysis.api.symbols.KtSymbol
import org.jetbrains.kotlin.psi.KtDeclaration
import org.jetbrains.kotlin.psi.KtFile
import org.jetbrains.kotlin.psi.KtParameter
import org.jetbrains.kotlin.psi.psiUtil.collectDescendantsOfType
import org.jetbrains.kotlin.test.services.TestServices

abstract class AbstractSymbolByPsiTest(configurator: FrontendApiTestConfiguratorService) : AbstractSymbolTest(configurator) {
    override val prettyRenderMode: PrettyRenderingMode get() = PrettyRenderingMode.RENDER_SYMBOLS_NESTED

    override fun KtAnalysisSession.collectSymbols(ktFile: KtFile, testServices: TestServices): SymbolsData {
        val allDeclarationSymbols = ktFile.collectDescendantsOfType<KtDeclaration> { it.isValidForSymbolCreation }.map { declaration ->
            declaration.getSymbol()
        }
        return SymbolsData(
            allDeclarationSymbols,
            listOf(ktFile.getFileSymbol()),
        )
    }

    private val KtDeclaration.isValidForSymbolCreation
        get() =
            when (this) {
                is KtParameter -> !this.isFunctionTypeParameter
                else -> true
            }
}
