// WITH_RUNTIME
// DONT_TARGET_EXACT_BACKEND: WASM
// !LANGUAGE: +UseBuilderInferenceWithoutAnnotation

fun <K, V> buildMap(builderAction: MutableMap<K, V>.() -> Unit): Map<K, V> = mapOf()

fun box(): String {
    val x = buildMap {
        put("", "")
    }
    return "OK"
}