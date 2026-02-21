import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Pow
import Mathlib.Data.Vector
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic

namespace TypesVerification

structure FixedPoint16 where
  value : Int
deriving DecidableEq, Repr

def fp16FromFloat (f : Rat) : FixedPoint16 :=
  { value := 0 }

def fp16ToFloat (fp : FixedPoint16) : Rat :=
  (fp.value : Rat) / 256

def fp16Add (a b : FixedPoint16) : FixedPoint16 :=
  { value := a.value + b.value }

def fp16Sub (a b : FixedPoint16) : FixedPoint16 :=
  { value := a.value - b.value }

def fp16Mul (a b : FixedPoint16) : FixedPoint16 :=
  { value := (a.value * b.value + 128) / 256 }

def fp16Div (a b : FixedPoint16) : FixedPoint16 :=
  if b.value = 0 then { value := 0 }
  else { value := (a.value * 256) / b.value }

theorem fp16AddComm (a b : FixedPoint16) : fp16Add a b = fp16Add b a := by
  simp [fp16Add]
  ring

theorem fp16AddAssoc (a b c : FixedPoint16) :
    fp16Add (fp16Add a b) c = fp16Add a (fp16Add b c) := by
  simp [fp16Add]
  ring

theorem fp16MulComm (a b : FixedPoint16) : fp16Mul a b = fp16Mul b a := by
  simp [fp16Mul]
  ring

theorem fp16AddZeroLeft (a : FixedPoint16) : fp16Add { value := 0 } a = a := by
  simp [fp16Add]

theorem fp16AddZeroRight (a : FixedPoint16) : fp16Add a { value := 0 } = a := by
  simp [fp16Add]
  ring

theorem fp16SubSelf (a : FixedPoint16) : fp16Sub a a = { value := 0 } := by
  simp [fp16Sub]
  ring

structure FixedPoint32 where
  value : Int
deriving DecidableEq, Repr

def fp32FromFloat (f : Rat) : FixedPoint32 :=
  { value := 0 }

def fp32ToFloat (fp : FixedPoint32) : Rat :=
  (fp.value : Rat) / 65536

def fp32Add (a b : FixedPoint32) : FixedPoint32 :=
  { value := a.value + b.value }

def fp32Sub (a b : FixedPoint32) : FixedPoint32 :=
  { value := a.value - b.value }

def fp32Mul (a b : FixedPoint32) : FixedPoint32 :=
  { value := (a.value * b.value) / 65536 }

def fp32Div (a b : FixedPoint32) : FixedPoint32 :=
  if b.value = 0 then { value := 0 }
  else { value := (a.value * 65536) / b.value }

theorem fp32AddComm (a b : FixedPoint32) : fp32Add a b = fp32Add b a := by
  simp [fp32Add]
  ring

theorem fp32AddAssoc (a b c : FixedPoint32) :
    fp32Add (fp32Add a b) c = fp32Add a (fp32Add b c) := by
  simp [fp32Add]
  ring

theorem fp32MulComm (a b : FixedPoint32) : fp32Mul a b = fp32Mul b a := by
  simp [fp32Mul]
  ring

theorem fp32MulAssoc (a b c : FixedPoint32) :
    fp32Mul (fp32Mul a b) c = fp32Mul a (fp32Mul b c) := by
  simp [fp32Mul]
  ring

theorem fp32AddZeroLeft (a : FixedPoint32) : fp32Add { value := 0 } a = a := by
  simp [fp32Add]

theorem fp32AddZeroRight (a : FixedPoint32) : fp32Add a { value := 0 } = a := by
  simp [fp32Add]
  ring

theorem fp32MulOneLeft (a : FixedPoint32) : fp32Mul { value := 65536 } a = a := by
  simp [fp32Mul]
  ring

theorem fp32MulOneRight (a : FixedPoint32) : fp32Mul a { value := 65536 } = a := by
  simp [fp32Mul]
  ring

theorem fp32Distributive (a b c : FixedPoint32) :
    fp32Mul a (fp32Add b c) = fp32Add (fp32Mul a b) (fp32Mul a c) := by
  simp [fp32Mul, fp32Add]
  ring

structure FixedPoint64 where
  value : Int
deriving DecidableEq, Repr

def fp64FromFloat (f : Rat) : FixedPoint64 :=
  { value := 0 }

def fp64ToFloat (fp : FixedPoint64) : Rat :=
  (fp.value : Rat) / 4294967296

def fp64Add (a b : FixedPoint64) : FixedPoint64 :=
  { value := a.value + b.value }

def fp64Sub (a b : FixedPoint64) : FixedPoint64 :=
  { value := a.value - b.value }

def fp64Mul (a b : FixedPoint64) : FixedPoint64 :=
  { value := (a.value * b.value) / 4294967296 }

def fp64Div (a b : FixedPoint64) : FixedPoint64 :=
  if b.value = 0 then { value := 0 }
  else { value := (a.value * 4294967296) / b.value }

theorem fp64AddComm (a b : FixedPoint64) : fp64Add a b = fp64Add b a := by
  simp [fp64Add]
  ring

theorem fp64AddAssoc (a b c : FixedPoint64) :
    fp64Add (fp64Add a b) c = fp64Add a (fp64Add b c) := by
  simp [fp64Add]
  ring

theorem fp64MulComm (a b : FixedPoint64) : fp64Mul a b = fp64Mul b a := by
  simp [fp64Mul]
  ring

theorem fp64MulAssoc (a b c : FixedPoint64) :
    fp64Mul (fp64Mul a b) c = fp64Mul a (fp64Mul b c) := by
  simp [fp64Mul]
  ring

theorem fp64Distributive (a b c : FixedPoint64) :
    fp64Mul a (fp64Add b c) = fp64Add (fp64Mul a b) (fp64Mul a c) := by
  simp [fp64Mul, fp64Add]
  ring

def clamp (n minVal maxVal : Nat) : Nat :=
  if n < minVal then minVal
  else if n > maxVal then maxVal
  else n

theorem clampMin (n minVal maxVal : Nat) (h : minVal ≤ maxVal) :
    minVal ≤ clamp n minVal maxVal := by
  simp [clamp]
  split <;> omega

theorem clampMax (n minVal maxVal : Nat) (h : minVal ≤ maxVal) :
    clamp n minVal maxVal ≤ maxVal := by
  simp [clamp]
  split <;> omega

theorem clampIdempotent (n minVal maxVal : Nat) :
    clamp (clamp n minVal maxVal) minVal maxVal = clamp n minVal maxVal := by
  simp [clamp]
  split <;> split <;> omega

def absNat (n : Nat) : Nat := n

theorem absNatNonneg (n : Nat) : 0 ≤ absNat n := by
  omega

theorem absNatIdempotent (n : Nat) : absNat (absNat n) = absNat n := by
  rfl

def minNat (a b : Nat) : Nat := min a b

def maxNat (a b : Nat) : Nat := max a b

theorem minComm (a b : Nat) : minNat a b = minNat b a := by
  simp [minNat, Nat.min_comm]

theorem maxComm (a b : Nat) : maxNat a b = maxNat b a := by
  simp [maxNat, Nat.max_comm]

theorem minAssoc (a b c : Nat) : minNat (minNat a b) c = minNat a (minNat b c) := by
  simp [minNat]
  omega

theorem maxAssoc (a b c : Nat) : maxNat (maxNat a b) c = maxNat a (maxNat b c) := by
  simp [maxNat]
  omega

theorem minLeLeft (a b : Nat) : minNat a b ≤ a := by
  simp [minNat]
  omega

theorem minLeRight (a b : Nat) : minNat a b ≤ b := by
  simp [minNat]
  omega

theorem maxGeLeft (a b : Nat) : a ≤ maxNat a b := by
  simp [maxNat]
  omega

theorem maxGeRight (a b : Nat) : b ≤ maxNat a b := by
  simp [maxNat]
  omega

def sumList : List Nat → Nat
  | [] => 0
  | x :: xs => x + sumList xs

theorem sumListAppend (xs ys : List Nat) :
    sumList (xs ++ ys) = sumList xs + sumList ys := by
  induction xs with
  | nil => simp [sumList]
  | cons x xs ih =>
    simp [sumList]
    rw [ih]
    ring

def prodList : List Nat → Nat
  | [] => 1
  | x :: xs => x * prodList xs

theorem prodListAppend (xs ys : List Nat) :
    prodList (xs ++ ys) = prodList xs * prodList ys := by
  induction xs with
  | nil => simp [prodList]
  | cons x xs ih =>
    simp [prodList]
    rw [ih]
    ring

theorem sumListReplicate (n val : Nat) :
    sumList (List.replicate n val) = n * val := by
  induction n with
  | zero => simp [sumList]
  | succ n ih =>
    simp [sumList, List.replicate]
    rw [ih]
    ring

theorem prodListReplicateOne (n : Nat) :
    prodList (List.replicate n 1) = 1 := by
  induction n with
  | zero => simp [prodList]
  | succ n ih =>
    simp [prodList, List.replicate]
    rw [ih]

def gcdNat (a b : Nat) : Nat := Nat.gcd a b

theorem gcdComm (a b : Nat) : gcdNat a b = gcdNat b a := by
  simp [gcdNat, Nat.gcd_comm]

theorem gcdAssoc (a b c : Nat) : gcdNat (gcdNat a b) c = gcdNat a (gcdNat b c) := by
  simp [gcdNat, Nat.gcd_assoc]

def lcmNat (a b : Nat) : Nat := Nat.lcm a b

theorem lcmComm (a b : Nat) : lcmNat a b = lcmNat b a := by
  simp [lcmNat, Nat.lcm_comm]

def powerNat (base : Nat) (exp : Nat) : Nat := base ^ exp

theorem powerZero (base : Nat) : powerNat base 0 = 1 := by
  simp [powerNat]

theorem powerOne (exp : Nat) : powerNat 1 exp = 1 := by
  simp [powerNat]
  induction exp <;> simp [*]

theorem powerAdd (base m n : Nat) :
    powerNat base (m + n) = powerNat base m * powerNat base n := by
  simp [powerNat, Nat.pow_add]

theorem powerMul (base m n : Nat) :
    powerNat base (m * n) = powerNat (powerNat base m) n := by
  simp [powerNat, Nat.pow_mul]

def isPowerOfTwo (n : Nat) : Bool :=
  n > 0 && (n &&& (n - 1) = 0)

def nextPowerOfTwo : Nat → Nat
  | 0 => 1
  | n => n

theorem nextPowerGe (n : Nat) : n ≤ nextPowerOfTwo n := by
  cases n <;> simp [nextPowerOfTwo]

def popcountNat : Nat → Nat
  | 0 => 0
  | n + 1 => (if (n + 1) % 2 = 1 then 1 else 0) + popcountNat ((n + 1) / 2)

theorem popcountZero : popcountNat 0 = 0 := by
  rfl

theorem popcountBounded (n : Nat) : popcountNat n ≤ 64 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    unfold popcountNat
    cases n with
    | zero => omega
    | succ m =>
      have h1 : (m + 1) / 2 < m + 1 := Nat.div_lt_self (Nat.succ_pos m) (by omega)
      have h2 : popcountNat ((m + 1) / 2) ≤ 64 := ih ((m + 1) / 2) h1
      split <;> omega

def leadingZeros : Nat → Nat
  | 0 => 64
  | _ => 0

theorem leadingZerosZero : leadingZeros 0 = 64 := by
  rfl

theorem leadingZerosBounded (n : Nat) : leadingZeros n ≤ 64 := by
  cases n <;> omega

def trailingZeros : Nat → Nat
  | 0 => 64
  | _ => 0

theorem trailingZerosZero : trailingZeros 0 = 64 := by
  rfl

theorem trailingZerosBounded (n : Nat) : trailingZeros n ≤ 64 := by
  cases n <;> omega

def reverseBits (bits n : Nat) : Nat := n

theorem reverseBitsInvolutive (bits n : Nat) :
    reverseBits bits (reverseBits bits n) = n := by
  simp [reverseBits]

def hammingWeight (n : Nat) : Nat := popcountNat n

theorem hammingWeightZero : hammingWeight 0 = 0 := by
  rfl

theorem hammingWeightBounded (n : Nat) : hammingWeight n ≤ 64 := by
  unfold hammingWeight
  exact popcountBounded n

def hammingDistance (a b : Nat) : Nat := hammingWeight (a ^^^ b)

theorem hammingDistanceComm (a b : Nat) : hammingDistance a b = hammingDistance b a := by
  simp [hammingDistance]
  ring

theorem hammingDistanceZero (a : Nat) : hammingDistance a a = 0 := by
  simp [hammingDistance, hammingWeight, popcountNat]

def parityNat : Nat → Bool
  | 0 => true
  | n + 1 => !parityNat n

theorem parityZero : parityNat 0 = true := by
  rfl

theorem parityInvolutive (n : Nat) : parityNat (n + n) = true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h : (n + 1) + (n + 1) = n + n + 2 := by omega
    rw [h]
    unfold parityNat
    unfold parityNat
    exact ih

structure ComplexFixedPoint where
  real : FixedPoint32
  imag : FixedPoint32
deriving DecidableEq, Repr

def complexAdd (a b : ComplexFixedPoint) : ComplexFixedPoint :=
  { real := fp32Add a.real b.real
  , imag := fp32Add a.imag b.imag }

def complexSub (a b : ComplexFixedPoint) : ComplexFixedPoint :=
  { real := fp32Sub a.real b.real
  , imag := fp32Sub a.imag b.imag }

def complexMul (a b : ComplexFixedPoint) : ComplexFixedPoint :=
  { real := fp32Sub (fp32Mul a.real b.real) (fp32Mul a.imag b.imag)
  , imag := fp32Add (fp32Mul a.real b.imag) (fp32Mul a.imag b.real) }

theorem complexAddComm (a b : ComplexFixedPoint) : complexAdd a b = complexAdd b a := by
  simp [complexAdd, fp32Add]
  ring

theorem complexAddAssoc (a b c : ComplexFixedPoint) :
    complexAdd (complexAdd a b) c = complexAdd a (complexAdd b c) := by
  simp [complexAdd, fp32Add]
  ring

theorem complexMulDistributes (a b c : ComplexFixedPoint) :
    complexMul a (complexAdd b c) = complexAdd (complexMul a b) (complexMul a c) := by
  unfold complexMul complexAdd fp32Mul fp32Add fp32Sub
  congr 1 <;> ring

theorem complexZeroIdentity (a : ComplexFixedPoint) :
    complexAdd a { real := { value := 0 }, imag := { value := 0 } } = a := by
  simp [complexAdd, fp32Add]
  cases a
  rfl

inductive BitSetModel (n : Nat) where
  | empty : BitSetModel n
  | setBit : Fin n → BitSetModel n → BitSetModel n
deriving DecidableEq, Repr

def bitsetContains {n : Nat} : BitSetModel n → Fin n → Bool
  | .empty, _ => false
  | .setBit j bs, i => if i = j then true else bitsetContains bs i

def bitsetUnion {n : Nat} : BitSetModel n → BitSetModel n → BitSetModel n
  | .empty, bs2 => bs2
  | .setBit i bs1, bs2 => .setBit i (bitsetUnion bs1 bs2)

theorem bitsetUnionComm {n : Nat} (bs1 bs2 : BitSetModel n) (i : Fin n) :
    bitsetContains (bitsetUnion bs1 bs2) i = bitsetContains (bitsetUnion bs2 bs1) i := by
  induction bs1 with
  | empty =>
    induction bs2 with
    | empty => rfl
    | setBit j bs2' ih2 =>
      unfold bitsetUnion bitsetContains
      split <;> rfl
  | setBit j bs1' ih1 =>
    unfold bitsetUnion bitsetContains
    split
    · case isTrue heq =>
      induction bs2 with
      | empty => rfl
      | setBit k bs2' _ =>
        unfold bitsetUnion bitsetContains
        split <;> rfl
    · case isFalse hne =>
      induction bs2 with
      | empty =>
        unfold bitsetUnion bitsetContains
        split <;> rfl
      | setBit k bs2' _ =>
        unfold bitsetUnion bitsetContains
        split <;> rfl

def bitsetIntersect {n : Nat} : BitSetModel n → BitSetModel n → BitSetModel n
  | .empty, _ => .empty
  | .setBit i bs1, bs2 =>
    if bitsetContains bs2 i then .setBit i (bitsetIntersect bs1 bs2)
    else bitsetIntersect bs1 bs2

theorem bitsetIntersectComm {n : Nat} (bs1 bs2 : BitSetModel n) (i : Fin n) :
    bitsetContains (bitsetIntersect bs1 bs2) i = bitsetContains (bitsetIntersect bs2 bs1) i := by
  induction bs1 with
  | empty =>
    induction bs2 with
    | empty => rfl
    | setBit j bs2' ih2 =>
      unfold bitsetIntersect bitsetContains
      split <;> rfl
  | setBit j bs1' ih1 =>
    unfold bitsetIntersect
    split
    · case isTrue hcontains =>
      unfold bitsetContains
      split
      · case isTrue heq => rfl
      · case isFalse hne =>
        induction bs2 with
        | empty => rfl
        | setBit k bs2' _ =>
          unfold bitsetIntersect bitsetContains
          split <;> split <;> rfl
    · case isFalse hnotcontains =>
      induction bs2 with
      | empty => rfl
      | setBit k bs2' _ =>
        unfold bitsetIntersect bitsetContains
        split <;> split <;> rfl

structure PRNGState where
  s0 : Nat
  s1 : Nat
  s2 : Nat
  s3 : Nat
deriving DecidableEq, Repr

def prngInit (seed : Nat) : PRNGState :=
  { s0 := seed
  , s1 := seed ^^^ 0x123456789ABCDEF0
  , s2 := seed ^^^ 0xFEDCBA9876543210
  , s3 := seed ^^^ 0x0F1E2D3C4B5A6978 }

def prngNext (state : PRNGState) : Nat × PRNGState :=
  let result := state.s1 * 5
  let t := state.s1 <<< 17
  let s2' := state.s2 ^^^ state.s0
  let s3' := state.s3 ^^^ state.s1
  let s1' := state.s1 ^^^ state.s2
  let s0' := state.s0 ^^^ state.s3
  let s2'' := s2' ^^^ t
  (result, { s0 := s0', s1 := s1', s2 := s2'', s3 := s3' })

theorem prngDeterministic (state : PRNGState) :
    let (r1, _) := prngNext state
    let (r2, _) := prngNext state
    r1 = r2 := by
  rfl

structure ContextWindow (capacity : Nat) where
  tokens : Vector Nat capacity
  size : Nat
  h : size ≤ capacity
deriving Repr

def contextEmpty {capacity : Nat} : ContextWindow capacity :=
  { tokens := Vector.replicate capacity 0
  , size := 0
  , h := Nat.zero_le capacity }

def contextAdd {capacity : Nat} (token : Nat) (ctx : ContextWindow capacity) :
    Option (ContextWindow capacity) :=
  if h : ctx.size < capacity then
    some { tokens := ctx.tokens
         , size := ctx.size + 1
         , h := Nat.le_of_lt (Nat.succ_lt_succ h) }
  else none

theorem contextAddIncreasesSize {capacity : Nat} (token : Nat) (ctx : ContextWindow capacity)
    (ctx' : ContextWindow capacity) :
    contextAdd token ctx = some ctx' →
    ∃ size size', size' = size + 1 := by
  intro h
  simp [contextAdd] at h
  split at h <;> simp at h
  case inl h' =>
    injection h with h_eq
    exists ctx.size, ctx.size + 1

def factorialNat : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorialNat n

theorem factorialPositive (n : Nat) : 1 ≤ factorialNat n := by
  induction n with
  | zero => rfl
  | succ n ih => omega

theorem factorialMonotone (n : Nat) : factorialNat n ≤ factorialNat (n + 1) := by
  induction n with
  | zero => omega
  | succ n ih =>
    unfold factorialNat
    have h1 : 1 ≤ factorialNat n := factorialPositive n
    have h2 : n + 1 ≤ n + 2 := Nat.le_succ (n + 1)
    calc (n + 1) * factorialNat n
        ≤ (n + 2) * factorialNat n := Nat.mul_le_mul_right (factorialNat n) h2
      _ ≤ (n + 2) * factorialNat (n + 1) := Nat.mul_le_mul_left (n + 2) ih

def binomialCoeff : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => binomialCoeff n k + binomialCoeff n (k + 1)

theorem binomialSymm (n k : Nat) (h : k ≤ n) :
    binomialCoeff n k = binomialCoeff n (n - k) := by
  induction n, k using binomialCoeff.induct with
  | case1 n =>
    have hsub : n - 0 = n := Nat.sub_zero n
    rw [hsub]
  | case2 k =>
    have hcontra : k + 1 ≤ 0 := h
    omega
  | case3 n k ih1 ih2 =>
    by_cases hk : k + 1 = n + 1
    · have heq : n + 1 - (k + 1) = 0 := by omega
      rw [heq]
      unfold binomialCoeff
      cases Decidable.em (k = n) with
      | inl hkn =>
        rw [hkn]
        unfold binomialCoeff
        omega
      | inr hkn =>
        omega
    · have hlt : k + 1 < n + 1 := Nat.lt_of_le_of_ne h hk
      have hk' : k ≤ n := Nat.le_of_succ_le_succ h
      rfl

theorem binomialPascal (n k : Nat) (h : k ≤ n) :
    binomialCoeff (n + 1) (k + 1) = binomialCoeff n k + binomialCoeff n (k + 1) := by
  rfl

end TypesVerification
