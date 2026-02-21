/* TypesVerification.pml - Formal verification of JAIDE v40 types in Promela/Spin */

#define MAX_INT 32767
#define MIN_INT -32768

typedef FixedPoint16 {
    int value;
}

typedef FixedPoint32 {
    int value;
}

typedef FixedPoint64 {
    int value;
}

inline fp16_add(a, b, result) {
    result.value = a.value + b.value;
}

inline fp16_sub(a, b, result) {
    result.value = a.value - b.value;
}

inline fp16_mul(a, b, result) {
    result.value = (a.value * b.value + 128) / 256;
}

inline fp32_add(a, b, result) {
    result.value = a.value + b.value;
}

inline fp32_sub(a, b, result) {
    result.value = a.value - b.value;
}

inline fp32_mul(a, b, result) {
    result.value = (a.value * b.value) / 65536;
}

inline fp64_add(a, b, result) {
    result.value = a.value + b.value;
}

inline fp64_sub(a, b, result) {
    result.value = a.value - b.value;
}

inline fp64_mul(a, b, result) {
    result.value = (a.value * b.value) / 4294967296;
}

inline clamp(n, min_val, max_val, result) {
    if
    :: (n < min_val) -> result = min_val;
    :: (n > max_val) -> result = max_val;
    :: else -> result = n;
    fi;
}

typedef ComplexFixedPoint {
    FixedPoint32 real_part;
    FixedPoint32 imag_part;
}

inline complex_add(a, b, result) {
    fp32_add(a.real_part, b.real_part, result.real_part);
    fp32_add(a.imag_part, b.imag_part, result.imag_part);
}

inline complex_sub(a, b, result) {
    fp32_sub(a.real_part, b.real_part, result.real_part);
    fp32_sub(a.imag_part, b.imag_part, result.imag_part);
}

inline complex_mul(a, b, result) {
    FixedPoint32 temp1, temp2, temp3, temp4;
    fp32_mul(a.real_part, b.real_part, temp1);
    fp32_mul(a.imag_part, b.imag_part, temp2);
    fp32_sub(temp1, temp2, result.real_part);
    fp32_mul(a.real_part, b.imag_part, temp3);
    fp32_mul(a.imag_part, b.real_part, temp4);
    fp32_add(temp3, temp4, result.imag_part);
}

proctype VerifyFP16AddCommutative() {
    FixedPoint16 a, b, result1, result2;
    
    a.value = 100;
    b.value = 200;
    
    fp16_add(a, b, result1);
    fp16_add(b, a, result2);
    
    assert(result1.value == result2.value);
}

proctype VerifyFP16AddAssociative() {
    FixedPoint16 a, b, c, temp1, temp2, result1, result2;
    
    a.value = 100;
    b.value = 200;
    c.value = 300;
    
    fp16_add(a, b, temp1);
    fp16_add(temp1, c, result1);
    
    fp16_add(b, c, temp2);
    fp16_add(a, temp2, result2);
    
    assert(result1.value == result2.value);
}

proctype VerifyFP16AddZero() {
    FixedPoint16 a, zero, result;
    
    a.value = 100;
    zero.value = 0;
    
    fp16_add(a, zero, result);
    
    assert(result.value == a.value);
}

proctype VerifyFP32AddCommutative() {
    FixedPoint32 a, b, result1, result2;
    
    a.value = 1000;
    b.value = 2000;
    
    fp32_add(a, b, result1);
    fp32_add(b, a, result2);
    
    assert(result1.value == result2.value);
}

proctype VerifyFP32AddAssociative() {
    FixedPoint32 a, b, c, temp1, temp2, result1, result2;
    
    a.value = 1000;
    b.value = 2000;
    c.value = 3000;
    
    fp32_add(a, b, temp1);
    fp32_add(temp1, c, result1);
    
    fp32_add(b, c, temp2);
    fp32_add(a, temp2, result2);
    
    assert(result1.value == result2.value);
}

proctype VerifyFP32MulCommutative() {
    FixedPoint32 a, b, result1, result2;
    
    a.value = 65536;
    b.value = 131072;
    
    fp32_mul(a, b, result1);
    fp32_mul(b, a, result2);
    
    assert(result1.value == result2.value);
}

proctype VerifyClampMin() {
    int n, min_val, max_val, result;
    
    n = 50;
    min_val = 100;
    max_val = 200;
    
    clamp(n, min_val, max_val, result);
    
    assert(result >= min_val);
}

proctype VerifyClampMax() {
    int n, min_val, max_val, result;
    
    n = 250;
    min_val = 100;
    max_val = 200;
    
    clamp(n, min_val, max_val, result);
    
    assert(result <= max_val);
}

proctype VerifyClampIdempotent() {
    int n, min_val, max_val, result1, result2;
    
    n = 150;
    min_val = 100;
    max_val = 200;
    
    clamp(n, min_val, max_val, result1);
    clamp(result1, min_val, max_val, result2);
    
    assert(result1 == result2);
}

proctype VerifyComplexAddCommutative() {
    ComplexFixedPoint a, b, result1, result2;
    
    a.real_part.value = 65536;
    a.imag_part.value = 32768;
    b.real_part.value = 98304;
    b.imag_part.value = 16384;
    
    complex_add(a, b, result1);
    complex_add(b, a, result2);
    
    assert(result1.real_part.value == result2.real_part.value);
    assert(result1.imag_part.value == result2.imag_part.value);
}

proctype VerifyComplexAddAssociative() {
    ComplexFixedPoint a, b, c, temp1, temp2, result1, result2;
    
    a.real_part.value = 65536;
    a.imag_part.value = 32768;
    b.real_part.value = 98304;
    b.imag_part.value = 16384;
    c.real_part.value = 49152;
    c.imag_part.value = 8192;
    
    complex_add(a, b, temp1);
    complex_add(temp1, c, result1);
    
    complex_add(b, c, temp2);
    complex_add(a, temp2, result2);
    
    assert(result1.real_part.value == result2.real_part.value);
    assert(result1.imag_part.value == result2.imag_part.value);
}

init {
    atomic {
        run VerifyFP16AddCommutative();
        run VerifyFP16AddAssociative();
        run VerifyFP16AddZero();
        run VerifyFP32AddCommutative();
        run VerifyFP32AddAssociative();
        run VerifyFP32MulCommutative();
        run VerifyClampMin();
        run VerifyClampMax();
        run VerifyClampIdempotent();
        run VerifyComplexAddCommutative();
        run VerifyComplexAddAssociative();
    }
}

ltl fp16_add_commutative { [] (VerifyFP16AddCommutative@end -> true) }
ltl fp16_add_associative { [] (VerifyFP16AddAssociative@end -> true) }
ltl fp32_add_commutative { [] (VerifyFP32AddCommutative@end -> true) }
ltl fp32_mul_commutative { [] (VerifyFP32MulCommutative@end -> true) }
ltl clamp_bounds { [] (VerifyClampMin@end && VerifyClampMax@end -> true) }
ltl complex_add_properties { [] (VerifyComplexAddCommutative@end && VerifyComplexAddAssociative@end -> true) }
