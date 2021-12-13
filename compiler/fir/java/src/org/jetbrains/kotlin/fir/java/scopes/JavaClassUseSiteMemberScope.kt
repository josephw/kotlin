/*
 * Copyright 2010-2020 JetBrains s.r.o. and Kotlin Programming Language contributors.
 * Use of this source code is governed by the Apache 2.0 license that can be found in the license/LICENSE.txt file.
 */

package org.jetbrains.kotlin.fir.java.scopes

import org.jetbrains.kotlin.descriptors.Modality
import org.jetbrains.kotlin.fir.*
import org.jetbrains.kotlin.fir.declarations.*
import org.jetbrains.kotlin.fir.declarations.synthetic.FirSyntheticProperty
import org.jetbrains.kotlin.fir.declarations.synthetic.buildSyntheticProperty
import org.jetbrains.kotlin.fir.declarations.utils.*
import org.jetbrains.kotlin.fir.java.declarations.FirJavaClass
import org.jetbrains.kotlin.fir.java.declarations.buildJavaMethodCopy
import org.jetbrains.kotlin.fir.java.declarations.buildJavaValueParameterCopy
import org.jetbrains.kotlin.fir.java.symbols.FirJavaOverriddenSyntheticPropertySymbol
import org.jetbrains.kotlin.fir.java.toConeKotlinTypeProbablyFlexible
import org.jetbrains.kotlin.fir.resolve.defaultType
import org.jetbrains.kotlin.fir.resolve.toSymbol
import org.jetbrains.kotlin.fir.scopes.*
import org.jetbrains.kotlin.fir.scopes.impl.AbstractFirUseSiteMemberScope
import org.jetbrains.kotlin.fir.scopes.impl.FirTypeIntersectionScopeContext.ResultOfIntersection
import org.jetbrains.kotlin.fir.scopes.impl.FirTypeIntersectionScopeContext.ResultOfIntersection.ChosenSymbol
import org.jetbrains.kotlin.fir.scopes.impl.isIntersectionOverride
import org.jetbrains.kotlin.fir.scopes.jvm.computeJvmDescriptor
import org.jetbrains.kotlin.fir.scopes.jvm.computeJvmSignature
import org.jetbrains.kotlin.fir.symbols.impl.*
import org.jetbrains.kotlin.fir.symbols.impl.isStatic
import org.jetbrains.kotlin.fir.types.*
import org.jetbrains.kotlin.load.java.BuiltinSpecialProperties
import org.jetbrains.kotlin.load.java.JvmAbi
import org.jetbrains.kotlin.load.java.SpecialGenericSignatures
import org.jetbrains.kotlin.load.java.SpecialGenericSignatures.Companion.ERASED_COLLECTION_PARAMETER_NAMES
import org.jetbrains.kotlin.load.java.SpecialGenericSignatures.Companion.sameAsBuiltinMethodWithErasedValueParameters
import org.jetbrains.kotlin.load.java.SpecialGenericSignatures.Companion.sameAsRenamedInJvmBuiltin
import org.jetbrains.kotlin.load.java.getPropertyNamesCandidatesByAccessorName
import org.jetbrains.kotlin.name.CallableId
import org.jetbrains.kotlin.name.Name
import org.jetbrains.kotlin.name.StandardClassIds
import org.jetbrains.kotlin.types.AbstractTypeChecker
import org.jetbrains.kotlin.utils.addIfNotNull

class JavaClassUseSiteMemberScope(
    klass: FirJavaClass,
    session: FirSession,
//    val superTypesScope: FirTypeScope,
    superTypeScopes: List<FirTypeScope>,
    declaredMemberScope: FirContainingNamesAwareScope
) : AbstractFirUseSiteMemberScope(
    klass.classId,
    session,
    JavaOverrideChecker(session, klass.javaTypeParameterStack, superTypeScopes, considerReturnTypeKinds = true),
    superTypeScopes,
    klass.defaultType(),
    declaredMemberScope
) {
    private val typeParameterStack = klass.javaTypeParameterStack
    private val specialFunctions = hashMapOf<Name, Collection<FirNamedFunctionSymbol>>()
    private val syntheticPropertyByNameMap = hashMapOf<Name, FirSyntheticPropertySymbol>()

    private val canUseSpecialGetters: Boolean by lazy { !klass.hasKotlinSuper(session) }

    private fun generateSyntheticPropertySymbol(
        getterSymbol: FirNamedFunctionSymbol,
        setterSymbol: FirNamedFunctionSymbol?,
        property: FirProperty,
        takeModalityFromGetter: Boolean,
    ): FirSyntheticPropertySymbol {
        return syntheticPropertyByNameMap.getOrPut(property.name) {
            buildSyntheticProperty {
                moduleData = session.moduleData
                name = property.name
                symbol = FirJavaOverriddenSyntheticPropertySymbol(
                    getterId = getterSymbol.callableId,
                    propertyId = CallableId(getterSymbol.callableId.packageName, getterSymbol.callableId.className, property.name)
                )
                delegateGetter = getterSymbol.fir
                delegateSetter = setterSymbol?.fir
                status = getterSymbol.fir.status.copy(
                    newModality = if (takeModalityFromGetter) {
                        delegateGetter.modality ?: property.modality
                    } else {
                        chooseModalityForAccessor(property, delegateGetter)
                    }
                )
                deprecation = getDeprecationsFromAccessors(delegateGetter, delegateSetter, session.languageVersionSettings.apiVersion)
            }.symbol
        }
    }

    private fun chooseModalityForAccessor(property: FirProperty, getter: FirSimpleFunction): Modality? {
        val a = property.modality
        val b = getter.modality

        if (a == null) return b
        if (b == null) return a

        return minOf(a, b)
    }

    override fun collectProperties(name: Name): Collection<FirVariableSymbol<*>> {
        val fields = mutableSetOf<FirCallableSymbol<*>>()
        val fieldNames = mutableSetOf<Name>()
        val result = mutableSetOf<FirVariableSymbol<*>>()

        // fields
        declaredMemberScope.processPropertiesByName(name) processor@{ variableSymbol ->
            if (variableSymbol.isStatic) return@processor
            fields += variableSymbol
            fieldNames += variableSymbol.fir.name
            result += variableSymbol
        }

        /*
         * From supertype we can get at most two results:
         * 1. Set of properties with same name
         * 2. Field from some java superclass (only one, if class have more than one superclass then we can choose
         *   just one field because this is incorrect code anyway)
         */
        val fromSupertypes = supertypeScopeContext.collectCallables(name, FirScope::processPropertiesByName)

        val (fieldsFromSupertype, propertiesFromSupertypes) = fromSupertypes.partition {
            it.chosenSymbol is ChosenSymbol.RegularSymbol && it.chosenSymbol.symbol is FirFieldSymbol
        }

        assert(fieldsFromSupertype.size in 0..1)
        assert(propertiesFromSupertypes.size in 0..1)

        fieldsFromSupertype.firstOrNull()?.chosenSymbol?.symbol?.let { fieldSymbol ->
            require(fieldSymbol is FirFieldSymbol)
            if (fieldSymbol.name !in fieldNames) {
                result.addIfNotNull(fieldSymbol)
            }
        }

        @Suppress("UNCHECKED_CAST")
        val overriddenProperty = propertiesFromSupertypes.firstOrNull() as ResultOfIntersection<FirPropertySymbol>? ?: return result
        val (chosenSymbolFromSupertype, overriddenMembers, _) = overriddenProperty

        val propertyFromSupertype = chosenSymbolFromSupertype.extractSomeSymbolFromSuperType()
        val overrideInClass =
            propertyFromSupertype.createOverridePropertyIfExists(declaredMemberScope, takeModalityFromGetter = true)
                ?: superTypeScopes.firstNotNullOfOrNull {
                    propertyFromSupertype.createOverridePropertyIfExists(it, takeModalityFromGetter = false)
                }

        val chosenSymbol = overrideInClass ?: chosenSymbolFromSupertype.symbol
        directOverriddenProperties[chosenSymbol] = listOf(overriddenProperty)
        overriddenMembers.forEach { overrideByBase[it.member] = overrideInClass }
        result += chosenSymbol
        return result
    }

    private fun FirPropertySymbol.createOverridePropertyIfExists(
        scope: FirScope,
        takeModalityFromGetter: Boolean
    ): FirPropertySymbol? {
        val getterSymbol = this.findGetterOverride(scope) ?: return null
        val setterSymbol =
            if (this.fir.isVar)
                this.findSetterOverride(scope) ?: return null
            else
                null
        if (setterSymbol != null && setterSymbol.fir.modality != getterSymbol.fir.modality) return null

        return generateSyntheticPropertySymbol(getterSymbol, setterSymbol, fir, takeModalityFromGetter)
    }

    private fun FirPropertySymbol.findGetterOverride(
        scope: FirScope,
    ): FirNamedFunctionSymbol? {
        val specialGetterName = if (canUseSpecialGetters) getBuiltinSpecialPropertyGetterName() else null
        val name = specialGetterName?.asString() ?: JvmAbi.getterName(fir.name.asString())
        return findGetterByName(name, scope)
    }

    private fun FirPropertySymbol.findGetterByName(
        getterName: String,
        scope: FirScope,
    ): FirNamedFunctionSymbol? {
        val propertyFromSupertype = fir
        val expectedReturnType = propertyFromSupertype.returnTypeRef.coneTypeSafe<ConeKotlinType>()
        return scope.getFunctions(Name.identifier(getterName)).firstNotNullOfOrNull factory@{ candidateSymbol ->
            val candidate = candidateSymbol.fir
            if (candidate.valueParameters.isNotEmpty()) return@factory null

            val candidateReturnType = candidate.returnTypeRef.toConeKotlinTypeProbablyFlexible(session, typeParameterStack)

            candidateSymbol.takeIf {
                // TODO: Decide something for the case when property type is not computed yet
                expectedReturnType == null || AbstractTypeChecker.isSubtypeOf(session.typeContext, candidateReturnType, expectedReturnType)
            }
        }
    }

    private fun FirPropertySymbol.findSetterOverride(
        scope: FirScope,
    ): FirNamedFunctionSymbol? {
        val propertyType = fir.returnTypeRef.coneTypeSafe<ConeKotlinType>() ?: return null
        return scope.getFunctions(Name.identifier(JvmAbi.setterName(fir.name.asString()))).firstNotNullOfOrNull factory@{ candidateSymbol ->
            val candidate = candidateSymbol.fir
            if (candidate.valueParameters.size != 1) return@factory null

            if (!candidate.returnTypeRef.toConeKotlinTypeProbablyFlexible(session, typeParameterStack).isUnit) return@factory null

            val parameterType =
                candidate.valueParameters.single().returnTypeRef.toConeKotlinTypeProbablyFlexible(session, typeParameterStack)

            candidateSymbol.takeIf {
                AbstractTypeChecker.equalTypes(session.typeContext, parameterType, propertyType)
            }
        }
    }

    private fun FirPropertySymbol.getBuiltinSpecialPropertyGetterName(): Name? {
        var result: Name? = null
        superTypeScopes.processOverriddenPropertiesAndSelf(this) { overridden ->
            val fqName = overridden.fir.containingClass()?.classId?.asSingleFqName()?.child(overridden.fir.name)

            BuiltinSpecialProperties.PROPERTY_FQ_NAME_TO_JVM_GETTER_NAME_MAP[fqName]?.let { name ->
                result = name
                return@processOverriddenPropertiesAndSelf ProcessorAction.STOP
            }

            ProcessorAction.NEXT
        }

        return result
    }

    override fun processFunctionsByName(name: Name, processor: (FirNamedFunctionSymbol) -> Unit) {
        val potentialPropertyNames = getPropertyNamesCandidatesByAccessorName(name)

        val renamedSpecialBuiltInName = SpecialGenericSignatures.getBuiltinFunctionNamesByJvmName(name)

        if (potentialPropertyNames.isEmpty() &&
            renamedSpecialBuiltInName == null &&
            !name.sameAsBuiltinMethodWithErasedValueParameters &&
            !name.sameAsRenamedInJvmBuiltin
        ) {
            return super.processFunctionsByName(name, processor)
        }

        val overriddenProperties = potentialPropertyNames.flatMap(this::getProperties).filterIsInstance<FirPropertySymbol>()

        specialFunctions.getOrPut(name) {
            collectSpecialFunctions(name, overriddenProperties, renamedSpecialBuiltInName)
        }.forEach {
            processor(it)
        }
    }

    /*
     * "special" here means functions which can have different name in kotlin because of mapping builtins
     */
    private fun collectSpecialFunctions(
        name: Name,
        overriddenProperties: List<FirPropertySymbol>,
        renamedSpecialBuiltInName: Name?
    ): List<FirNamedFunctionSymbol> {
        val result = mutableListOf<FirNamedFunctionSymbol>()

        declaredMemberScope.processFunctionsByName(name) { functionSymbol ->
            if (functionSymbol.isStatic) return@processFunctionsByName
            if (overriddenProperties.none { it.isOverriddenInClassBy(functionSymbol) } &&
                !functionSymbol.doesOverrideRenamedBuiltins(renamedSpecialBuiltInName) &&
                !functionSymbol.shouldBeVisibleAsOverrideOfBuiltInWithErasedValueParameters()
            ) {
                result += functionSymbol
            }
        }

        addOverriddenSpecialMethods(name, result)

        val overrideCandidates = result.toSet()

        for ((chosenSymbolFromSupertype, _, _) in getFunctionsFromSupertypesByName(name)) {
            val superSymbol = chosenSymbolFromSupertype.extractSomeSymbolFromSuperType()
            val overriddenBy = superSymbol.getOverridden(overrideCandidates)
            if (
                overriddenBy == null &&
                overriddenProperties.none { it.isOverriddenInClassBy(superSymbol) } &&
                !superSymbol.doesOverrideRenamedBuiltins(renamedSpecialBuiltInName) &&
                !superSymbol.shouldBeVisibleAsOverrideOfBuiltInWithErasedValueParameters()
            ) {
                result.add(chosenSymbolFromSupertype.symbol)
            }
        }

        return result
    }

    private fun FirPropertySymbol.isOverriddenInClassBy(functionSymbol: FirNamedFunctionSymbol): Boolean {
        val fir = fir as? FirSyntheticProperty ?: return false

        if (fir.getter.delegate.symbol == functionSymbol || fir.setter?.delegate?.symbol == functionSymbol) return true

        val currentJvmDescriptor = functionSymbol.fir.computeJvmDescriptor(includeReturnType = false)
        val getterJvmDescriptor = fir.getter.delegate.computeJvmDescriptor(includeReturnType = false)
        val setterJvmDescriptor = fir.setter?.delegate?.computeJvmDescriptor(includeReturnType = false)

        return currentJvmDescriptor == getterJvmDescriptor || currentJvmDescriptor == setterJvmDescriptor
    }

    private fun addOverriddenSpecialMethods(
        name: Name,
        result: MutableList<FirNamedFunctionSymbol>,
    ) {
        for (fromSupertype in getFunctionsFromSupertypesByName(name)) {
            obtainOverrideForBuiltinWithDifferentJvmName(fromSupertype, name)?.let {
                directOverriddenFunctions[it] = listOf(fromSupertype)
                for (overriddenMember in fromSupertype.overriddenMembers) {
                    overrideByBase[overriddenMember.member] = it
                }
                result += it
            }

            obtainOverrideForBuiltInWithErasedValueParametersInJava(fromSupertype)?.let {
                directOverriddenFunctions[it] = listOf(fromSupertype)
                for (overriddenMember in fromSupertype.overriddenMembers) {
                    overrideByBase[overriddenMember.member] = it
                }
                result += it
            }
        }
    }

    private fun obtainOverrideForBuiltinWithDifferentJvmName(
        symbolsFromSupertypes: ResultOfIntersection<FirNamedFunctionSymbol>,
        name: Name,
    ): FirNamedFunctionSymbol? {
        val overriddenBuiltin = symbolsFromSupertypes.getOverriddenBuiltinWithDifferentJvmName() ?: return null

        val someSymbolFromSuperTypes = symbolsFromSupertypes.chosenSymbol.extractSomeSymbolFromSuperType()
        //if (unrelated) method with special name is already defined, we don't add renamed method at all
        //otherwise  we get methods ambiguity
        val alreadyDefined = declaredMemberScope.getFunctions(name).any { declaredSymbol ->
            overrideChecker.isOverriddenFunction(declaredSymbol.fir, someSymbolFromSuperTypes.fir)
        }
        if (alreadyDefined) return null

        val nameInJava =
            SpecialGenericSignatures.SIGNATURE_TO_JVM_REPRESENTATION_NAME[overriddenBuiltin.fir.computeJvmSignature() ?: return null]
                ?: return null

        for (candidateSymbol in declaredMemberScope.getFunctions(nameInJava)) {
            val candidateFir = candidateSymbol.fir
            val renamedCopy = buildJavaMethodCopy(candidateFir) {
                this.name = name
                this.symbol = FirNamedFunctionSymbol(CallableId(candidateFir.symbol.callableId.classId!!, name))
                this.status = candidateFir.status.copy(isOperator = someSymbolFromSuperTypes.isOperator)
            }.apply {
                initialSignatureAttr = candidateFir
            }

            if (overrideChecker.isOverriddenFunction(renamedCopy, overriddenBuiltin.fir)) {
                return renamedCopy.symbol
            }
        }

        return null
    }

    private fun obtainOverrideForBuiltInWithErasedValueParametersInJava(symbolsFromSupertypes: ResultOfIntersection<FirNamedFunctionSymbol>): FirNamedFunctionSymbol? {
        val overriddenBuiltin =
            symbolsFromSupertypes.getOverriddenBuiltinFunctionWithErasedValueParametersInJava()
                ?: return null

        return createOverrideForBuiltinFunctionWithErasedParameterIfNeeded(symbolsFromSupertypes, overriddenBuiltin)
    }

    private fun createOverrideForBuiltinFunctionWithErasedParameterIfNeeded(
        symbolsFromSupertypes: ResultOfIntersection<FirNamedFunctionSymbol>,
        overriddenBuiltin: FirNamedFunctionSymbol
    ): FirNamedFunctionSymbol? {
        return declaredMemberScope.getFunctions(overriddenBuiltin.fir.name).firstOrNull { candidateOverride ->
            candidateOverride.fir.computeJvmDescriptor() == overriddenBuiltin.fir.computeJvmDescriptor() &&
                    candidateOverride.hasErasedParameters()
        }?.let { override ->
            buildJavaMethodCopy(override.fir) {
                this.valueParameters.clear()
                override.fir.valueParameters.zip(symbolsFromSupertypes.chosenSymbol.extractSomeSymbolFromSuperType().fir.valueParameters)
                    .mapTo(this.valueParameters) { (overrideParameter, parameterFromSupertype) ->
                        buildJavaValueParameterCopy(overrideParameter) {
                            this@buildJavaValueParameterCopy.returnTypeRef = parameterFromSupertype.returnTypeRef
                        }
                    }

                symbol = FirNamedFunctionSymbol(override.callableId)
            }.apply {
                initialSignatureAttr = override.fir
            }.symbol
        }
    }

    // It's either overrides Collection.contains(Object) or Collection.containsAll(Collection<?>) or similar methods
    private fun FirNamedFunctionSymbol.hasErasedParameters(): Boolean {
        val valueParameter = fir.valueParameters.first()
        val parameterType = valueParameter.returnTypeRef.toConeKotlinTypeProbablyFlexible(session, typeParameterStack)
        val upperBound = parameterType.upperBoundIfFlexible()
        if (upperBound !is ConeClassLikeType) return false

        if (fir.name.asString() in ERASED_COLLECTION_PARAMETER_NAMES) {
            require(upperBound.lookupTag.classId == StandardClassIds.Collection) {
                "Unexpected type: ${upperBound.lookupTag.classId}"
            }

            return upperBound.typeArguments.singleOrNull() is ConeStarProjection
        }

        return upperBound.classId == StandardClassIds.Any
    }

    private fun FirNamedFunctionSymbol.doesOverrideRenamedBuiltins(renamedSpecialBuiltInName: Name?): Boolean {
        if (renamedSpecialBuiltInName == null) return false
        // e.g. 'removeAt' or 'toInt'
        val builtinSpecialFromSuperTypes =
            getFunctionsFromSupertypes(renamedSpecialBuiltInName).filter { it.getOverriddenBuiltinWithDifferentJvmName() != null }
        if (builtinSpecialFromSuperTypes.isEmpty()) return false

        val currentJvmDescriptor = fir.computeJvmDescriptor(customName = renamedSpecialBuiltInName.asString())

        return builtinSpecialFromSuperTypes.any { builtinSpecial ->
            builtinSpecial.chosenSymbol.extractSomeSymbolFromSuperType().fir.computeJvmDescriptor() == currentJvmDescriptor
        }
    }

    private fun FirFunction.computeJvmSignature(): String? {
        return computeJvmSignature { it.toConeKotlinTypeProbablyFlexible(session, typeParameterStack) }
    }

    private fun FirFunction.computeJvmDescriptor(customName: String? = null, includeReturnType: Boolean = false): String {
        return computeJvmDescriptor(customName, includeReturnType) {
            it.toConeKotlinTypeProbablyFlexible(
                session,
                typeParameterStack
            )
        }
    }

    private fun getFunctionsFromSupertypes(name: Name): List<ResultOfIntersection<FirNamedFunctionSymbol>> {
        return supertypeScopeContext.collectFunctions(name)
    }

    private fun ResultOfIntersection<FirNamedFunctionSymbol>.getOverriddenBuiltinWithDifferentJvmName(): FirNamedFunctionSymbol? {
        var result: FirNamedFunctionSymbol? = null

        if (chosenSymbol is ChosenSymbol.RegularSymbol) {
            val symbol = chosenSymbol.symbol
            val signature = symbol.fir.computeJvmSignature()
            if (signature in SpecialGenericSignatures.SIGNATURE_TO_JVM_REPRESENTATION_NAME) {
                return symbol
            }
        }

        this.processOverrides processor@{
            if (!it.isFromBuiltInClass(session)) return@processor ProcessorAction.NEXT
            if (SpecialGenericSignatures.SIGNATURE_TO_JVM_REPRESENTATION_NAME.containsKey(it.fir.computeJvmSignature())) {
                result = it
                return@processor ProcessorAction.STOP
            }

            ProcessorAction.NEXT
        }

        return result
    }

    private fun FirNamedFunctionSymbol.shouldBeVisibleAsOverrideOfBuiltInWithErasedValueParameters(): Boolean {
        val name = fir.name
        if (!name.sameAsBuiltinMethodWithErasedValueParameters) return false
        val candidatesToOverride =
            getFunctionsFromSupertypes(name).mapNotNull {
                it.getOverriddenBuiltinFunctionWithErasedValueParametersInJava()
            }

        val jvmDescriptor = fir.computeJvmDescriptor()

        return candidatesToOverride.any { candidate ->
            candidate.fir.computeJvmDescriptor() == jvmDescriptor && this.hasErasedParameters()
        }
    }

    private fun ResultOfIntersection<FirNamedFunctionSymbol>.getOverriddenBuiltinFunctionWithErasedValueParametersInJava(): FirNamedFunctionSymbol? {
        var result: FirNamedFunctionSymbol? = null

        this.processOverrides processor@{
            if (it.fir.computeJvmSignature() in SpecialGenericSignatures.ERASED_VALUE_PARAMETERS_SIGNATURES) {
                result = it
                return@processor ProcessorAction.STOP
            }

            ProcessorAction.NEXT
        }

        return result
    }

    private fun ResultOfIntersection<FirNamedFunctionSymbol>.processOverrides(processor: (FirNamedFunctionSymbol) -> ProcessorAction) {
        if (chosenSymbol.isIntersectionOverride()) {
            for ((symbol, scope) in overriddenMembers) {
                val action = scope.processOverriddenFunctionsAndSelf(symbol, processor)
                if (action == ProcessorAction.STOP) break
            }
        } else {
            containingScope?.processOverriddenFunctionsAndSelf(chosenSymbol.symbol, processor)
        }
    }

    /**
     * Checks if class has any kotlin super-types apart from builtins and interfaces
     */
    private fun FirRegularClass.hasKotlinSuper(session: FirSession, visited: MutableSet<FirRegularClass> = mutableSetOf()): Boolean =
        when {
            !visited.add(this) -> false
            this is FirJavaClass -> superConeTypes.any { type ->
                type.toFir(session)?.hasKotlinSuper(session, visited) == true
            }
            isInterface || origin == FirDeclarationOrigin.BuiltIns -> false
            else -> true
        }

    private fun ConeClassLikeType.toFir(session: FirSession): FirRegularClass? {
        val symbol = this.toSymbol(session)
        return if (symbol is FirRegularClassSymbol) {
            symbol.fir
        } else {
            null
        }
    }

    override fun toString(): String {
        return "Java use site scope of $classId"
    }
}

private fun FirCallableSymbol<*>.isFromBuiltInClass(session: FirSession) =
    dispatchReceiverClassOrNull()?.toSymbol(session)?.fir?.origin == FirDeclarationOrigin.BuiltIns
