---- MODULE TypesVerification ----
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS MaxValue, MinValue

VARIABLES fixedPoint16, fixedPoint32, fixedPoint64

TypeInvariant ==
    /\ fixedPoint16 \in Int
    /\ fixedPoint32 \in Int
    /\ fixedPoint64 \in Int

FP16Add(a, b) == a + b

FP16Sub(a, b) == a - b

FP16Mul(a, b) == (a * b + 128) \div 256

FP32Add(a, b) == a + b

FP32Sub(a, b) == a - b

FP32Mul(a, b) == (a * b) \div 65536

FP64Add(a, b) == a + b

FP64Sub(a, b) == a - b

FP64Mul(a, b) == (a * b) \div 4294967296

Clamp(n, minVal, maxVal) ==
    IF n < minVal THEN minVal
    ELSE IF n > maxVal THEN maxVal
    ELSE n

THEOREM FP16AddCommutative ==
    ASSUME NEW a \in Int, NEW b \in Int
    PROVE FP16Add(a, b) = FP16Add(b, a)

THEOREM FP16AddAssociative ==
    ASSUME NEW a \in Int, NEW b \in Int, NEW c \in Int
    PROVE FP16Add(FP16Add(a, b), c) = FP16Add(a, FP16Add(b, c))

THEOREM FP16AddIdentity ==
    ASSUME NEW a \in Int
    PROVE FP16Add(a, 0) = a

THEOREM FP32AddCommutative ==
    ASSUME NEW a \in Int, NEW b \in Int
    PROVE FP32Add(a, b) = FP32Add(b, a)

THEOREM FP32AddAssociative ==
    ASSUME NEW a \in Int, NEW b \in Int, NEW c \in Int
    PROVE FP32Add(FP32Add(a, b), c) = FP32Add(a, FP32Add(b, c))

THEOREM FP32MulCommutative ==
    ASSUME NEW a \in Int, NEW b \in Int
    PROVE FP32Mul(a, b) = FP32Mul(b, a)

THEOREM FP32Distributive ==
    ASSUME NEW a \in Int, NEW b \in Int, NEW c \in Int
    PROVE FP32Mul(a, FP32Add(b, c)) = FP32Add(FP32Mul(a, b), FP32Mul(a, c))

THEOREM ClampMinBound ==
    ASSUME NEW n \in Int, NEW minVal \in Int, NEW maxVal \in Int,
           minVal <= maxVal
    PROVE Clamp(n, minVal, maxVal) >= minVal

THEOREM ClampMaxBound ==
    ASSUME NEW n \in Int, NEW minVal \in Int, NEW maxVal \in Int,
           minVal <= maxVal
    PROVE Clamp(n, minVal, maxVal) <= maxVal

THEOREM ClampIdempotent ==
    ASSUME NEW n \in Int, NEW minVal \in Int, NEW maxVal \in Int
    PROVE Clamp(Clamp(n, minVal, maxVal), minVal, maxVal) = Clamp(n, minVal, maxVal)

ComplexNumber == [real: Int, imag: Int]

ComplexAdd(a, b) == [real |-> FP32Add(a.real, b.real),
                     imag |-> FP32Add(a.imag, b.imag)]

ComplexSub(a, b) == [real |-> FP32Sub(a.real, b.real),
                     imag |-> FP32Sub(a.imag, b.imag)]

ComplexMul(a, b) == [real |-> FP32Sub(FP32Mul(a.real, b.real),
                                       FP32Mul(a.imag, b.imag)),
                     imag |-> FP32Add(FP32Mul(a.real, b.imag),
                                       FP32Mul(a.imag, b.real))]

THEOREM ComplexAddCommutative ==
    ASSUME NEW a \in ComplexNumber, NEW b \in ComplexNumber
    PROVE ComplexAdd(a, b) = ComplexAdd(b, a)

THEOREM ComplexAddAssociative ==
    ASSUME NEW a \in ComplexNumber, NEW b \in ComplexNumber, NEW c \in ComplexNumber
    PROVE ComplexAdd(ComplexAdd(a, b), c) = ComplexAdd(a, ComplexAdd(b, c))

RECURSIVE Factorial(_)
Factorial(n) == IF n = 0 THEN 1 ELSE n * Factorial(n - 1)

THEOREM FactorialPositive ==
    ASSUME NEW n \in Nat
    PROVE Factorial(n) >= 1

RECURSIVE PowerNat(_, _)
PowerNat(base, exp) == IF exp = 0 THEN 1 ELSE base * PowerNat(base, exp - 1)

THEOREM PowerZero ==
    ASSUME NEW base \in Nat
    PROVE PowerNat(base, 0) = 1

THEOREM PowerOne ==
    ASSUME NEW exp \in Nat
    PROVE PowerNat(1, exp) = 1

Init ==
    /\ fixedPoint16 = 0
    /\ fixedPoint32 = 0
    /\ fixedPoint64 = 0

Next ==
    \/ /\ fixedPoint16' = FP16Add(fixedPoint16, 1)
       /\ UNCHANGED <<fixedPoint32, fixedPoint64>>
    \/ /\ fixedPoint32' = FP32Add(fixedPoint32, 1)
       /\ UNCHANGED <<fixedPoint16, fixedPoint64>>
    \/ /\ fixedPoint64' = FP64Add(fixedPoint64, 1)
       /\ UNCHANGED <<fixedPoint16, fixedPoint32>>

Spec == Init /\ [][Next]_<<fixedPoint16, fixedPoint32, fixedPoint64>>

THEOREM Spec => []TypeInvariant

====
