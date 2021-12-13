// SCOPE_DUMP: Some:toInt;intValue;toByte;byteValue;toLong;longValue

// FILE: MyNumber.java
public interface MyNumber {
    int intValue();
    byte byteValue();
}

// FILE: Some.java
public abstract class Some extends Number implements MyNumber {
    @Override
    public int intValue() {
        return 0;
    }
}

// FILE: main.kt
fun test(some: Some) {
//    some.toInt()
//    some.<!UNRESOLVED_REFERENCE!>intValue<!>() // should be error
    some.toByte()
//    some.<!UNRESOLVED_REFERENCE!>byteValue<!>() // should be error
//    some.toLong()
//    some.<!UNRESOLVED_REFERENCE!>longValue<!>() // should be error
}
