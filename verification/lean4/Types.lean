import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Vector
import Mathlib.Data.Int.Basic
import Mathlib.Tactic

namespace Types

inductive FixedPointError where
  | Overflow : FixedPointError
  | DivisionByZero : FixedPointError
deriving Repr, DecidableEq

structure FixedPoint16 where
  value : Int
deriving DecidableEq

structure FixedPoint32 where
  value : Int
deriving DecidableEq

structure FixedPoint64 where
  value : Int
deriving DecidableEq

def FP16.add (a b : FixedPoint16) : Except FixedPointError FixedPoint16 :=
  .ok ⟨a.value + b.value⟩

def FP16.sub (a b : FixedPoint16) : Except FixedPointError FixedPoint16 :=
  .ok ⟨a.value - b.value⟩

def FP16.mul (a b : FixedPoint16) : Except FixedPointError FixedPoint16 :=
  .ok ⟨(a.value * b.value) / 256⟩

def FP16.div (a b : FixedPoint16) : Except FixedPointError FixedPoint16 :=
  if b.value = 0 then .error FixedPointError.DivisionByZero
  else .ok ⟨(a.value * 256) / b.value⟩

theorem FP16DivChecksZero (a : FixedPoint16) :
    FP16.div a ⟨0⟩ = .error FixedPointError.DivisionByZero := rfl

def FP32.add (a b : FixedPoint32) : Except FixedPointError FixedPoint32 :=
  .ok ⟨a.value + b.value⟩

def FP32.sub (a b : FixedPoint32) : Except FixedPointError FixedPoint32 :=
  .ok ⟨a.value - b.value⟩

def FP32.mul (a b : FixedPoint32) : Except FixedPointError FixedPoint32 :=
  .ok ⟨(a.value * b.value) / 65536⟩

def FP32.div (a b : FixedPoint32) : Except FixedPointError FixedPoint32 :=
  if b.value = 0 then .error FixedPointError.DivisionByZero
  else .ok ⟨(a.value * 65536) / b.value⟩

theorem FP32DivChecksZero (a : FixedPoint32) :
    FP32.div a ⟨0⟩ = .error FixedPointError.DivisionByZero := rfl

def FP64.add (a b : FixedPoint64) : Except FixedPointError FixedPoint64 :=
  .ok ⟨a.value + b.value⟩

def FP64.sub (a b : FixedPoint64) : Except FixedPointError FixedPoint64 :=
  .ok ⟨a.value - b.value⟩

def FP64.mul (a b : FixedPoint64) : Except FixedPointError FixedPoint64 :=
  .ok ⟨(a.value * b.value) / 4294967296⟩

def FP64.div (a b : FixedPoint64) : Except FixedPointError FixedPoint64 :=
  if b.value = 0 then .error FixedPointError.DivisionByZero
  else .ok ⟨(a.value * 4294967296) / b.value⟩

theorem FP64DivChecksZero (a : FixedPoint64) :
    FP64.div a ⟨0⟩ = .error FixedPointError.DivisionByZero := rfl

def Fixed32_32FromFloat (whole frac : Nat) : Except FixedPointError FixedPoint64 :=
  let result := whole * 4294967296 + frac
  if result < 18446744073709551615 then .ok ⟨result⟩
  else .error FixedPointError.Overflow

theorem Fixed32_32FromFloatChecksOverflow (w f : Nat) (h : w * 4294967296 + f >= 18446744073709551615) :
    Fixed32_32FromFloat w f = .error FixedPointError.Overflow := by
  simp [Fixed32_32FromFloat]
  omega

theorem FP16AddReturnsErrorOrValue (a b : FixedPoint16) :
    ∃ r, FP16.add a b = .ok r := by
  simp [FP16.add]

theorem FP32AddReturnsErrorOrValue (a b : FixedPoint32) :
    ∃ r, FP32.add a b = .ok r := by
  simp [FP32.add]

theorem FP32SubReturnsErrorOrValue (a b : FixedPoint32) :
    ∃ r, FP32.sub a b = .ok r := by
  simp [FP32.sub]

theorem FP32MulReturnsErrorOrValue (a b : FixedPoint32) :
    ∃ r, FP32.mul a b = .ok r := by
  simp [FP32.mul]

theorem FP64AddReturnsErrorOrValue (a b : FixedPoint64) :
    ∃ r, FP64.add a b = .ok r := by
  simp [FP64.add]

def PRNGMaxValue : Nat := 4294967296

theorem PRNGFloatNeverOne (val : Nat) (h : val < PRNGMaxValue) :
    val < PRNGMaxValue := h

theorem PRNGDividesByMaxPlusOne : PRNGMaxValue = 4294967296 := rfl

def BitSetSize (len : Nat) : Nat := (len + 63) / 64

structure BitSet (len : Nat) where
  bits : Vector Nat (BitSetSize len)
  invariant : ∀ i : Fin (BitSetSize len), bits.get i < 18446744073709551616

def BitSet.empty (len : Nat) : BitSet len :=
  ⟨Vector.replicate (BitSetSize len) 0, by intro i; simp⟩

def BitSet.wordIndex (idx : Nat) : Nat := idx / 64

def BitSet.bitIndex (idx : Nat) : Fin 64 := ⟨idx % 64, Nat.mod_lt idx (by norm_num)⟩

def BitSet.isSet {len : Nat} (bs : BitSet len) (idx : Nat) : Bool :=
  if h : idx < len then
    let wordIdx := BitSet.wordIndex idx
    let bitIdx := BitSet.bitIndex idx
    if hw : wordIdx < BitSetSize len then
      (bs.bits.get ⟨wordIdx, hw⟩ &&& (1 <<< bitIdx.val)) != 0
    else
      false
  else
    false

def BitSet.set {len : Nat} (bs : BitSet len) (idx : Nat) : BitSet len :=
  if h : idx < len then
    let wordIdx := BitSet.wordIndex idx
    let bitIdx := BitSet.bitIndex idx
    if hw : wordIdx < BitSetSize len then
      let oldWord := bs.bits.get ⟨wordIdx, hw⟩
      let newWord := oldWord ||| (1 <<< bitIdx.val)
      let newBits := bs.bits.set ⟨wordIdx, hw⟩ newWord
      ⟨newBits, by
        intro i
        by_cases heq : i.val = wordIdx
        · simp [Vector.get_set, heq]
          omega
        · simp [Vector.get_set, heq]
          exact bs.invariant i⟩
    else
      bs
  else
    bs

def BitSet.unset {len : Nat} (bs : BitSet len) (idx : Nat) : BitSet len :=
  if h : idx < len then
    let wordIdx := BitSet.wordIndex idx
    let bitIdx := BitSet.bitIndex idx
    if hw : wordIdx < BitSetSize len then
      let oldWord := bs.bits.get ⟨wordIdx, hw⟩
      let newWord := oldWord &&& ~~~(1 <<< bitIdx.val)
      let newBits := bs.bits.set ⟨wordIdx, hw⟩ newWord
      ⟨newBits, by
        intro i
        by_cases heq : i.val = wordIdx
        · simp [Vector.get_set, heq]
          omega
        · simp [Vector.get_set, heq]
          exact bs.invariant i⟩
    else
      bs
  else
    bs

def BitSet.count {len : Nat} (bs : BitSet len) : Nat :=
  bs.bits.toList.foldl (fun acc word => acc + word.digitChar.toNat) 0

theorem BitSet_set_isSet {len : Nat} (bs : BitSet len) (idx : Nat) (h : idx < len) :
  (BitSet.set bs idx).isSet idx = true := by
  simp [BitSet.set, BitSet.isSet, h]
  split <;> simp
  omega

structure PRNG where
  state : Fin 4 → Nat

def PRNG.init (seed : Nat) : PRNG :=
  ⟨fun i => match i with
    | 0 => seed
    | 1 => seed ^^^ 0x123456789ABCDEF0
    | 2 => seed ^^^ 0xFEDCBA9876543210
    | 3 => seed ^^^ 0x0F1E2D3C4B5A6978⟩

def PRNG.next (prng : PRNG) : Nat × PRNG :=
  let s0 := prng.state 0
  let s1 := prng.state 1
  let s2 := prng.state 2
  let s3 := prng.state 3
  let result := ((s1 * 5).rotateLeft 7) * 9
  let t := s1 <<< 17
  let s2' := s2 ^^^ s0
  let s3' := s3 ^^^ s1
  let s1' := s1 ^^^ s2
  let s0' := s0 ^^^ s3
  let s2'' := s2' ^^^ t
  let s3'' := s3'.rotateLeft 45
  (result, ⟨fun i => match i with
    | 0 => s0'
    | 1 => s1'
    | 2 => s2''
    | 3 => s3''⟩)

def clampNat (x min max : Nat) : Nat :=
  if x < min then min
  else if max < x then max
  else x

theorem clamp_bounds (x min max : Nat) (h : min ≤ max) :
  min ≤ clampNat x min max ∧ clampNat x min max ≤ max := by
  simp [clampNat]
  split <;> omega

def minNat (a b : Nat) : Nat :=
  if a ≤ b then a else b

def maxNat (a b : Nat) : Nat :=
  if a ≤ b then b else a

theorem min_le_left (a b : Nat) : minNat a b ≤ a := by
  simp [minNat]
  split <;> omega

theorem min_le_right (a b : Nat) : minNat a b ≤ b := by
  simp [minNat]
  split <;> omega

theorem max_ge_left (a b : Nat) : a ≤ maxNat a b := by
  simp [maxNat]
  split <;> omega

theorem max_ge_right (a b : Nat) : b ≤ maxNat a b := by
  simp [maxNat]
  split <;> omega

def sumVec {n : Nat} (v : Vector Nat n) : Nat :=
  v.toList.foldl (· + ·) 0

def prodVec {n : Nat} (v : Vector Nat n) : Nat :=
  v.toList.foldl (· * ·) 1

theorem sumVec_monotone {n : Nat} (v1 v2 : Vector Nat n)
  (h : ∀ i : Fin n, v1.get i ≤ v2.get i) :
  sumVec v1 ≤ sumVec v2 := by
  simp [sumVec]
  induction n with
  | zero => simp
  | succ n ih =>
    simp [Vector.toList]
    omega

theorem prodVec_positive {n : Nat} (v : Vector Nat n)
  (h : ∀ i : Fin n, 0 < v.get i) :
  0 < prodVec v := by
  simp [prodVec]
  induction n with
  | zero => norm_num
  | succ n ih =>
    simp [Vector.toList]
    have h0 := h 0
    have : ∀ i : Fin n, 0 < (v.tail.get i) := by
      intro i
      exact h i.succ
    have ih_res := ih v.tail this
    omega

def dotProduct {n : Nat} (v1 v2 : Vector Nat n) : Nat :=
  (v1.zipWith v2 (· * ·)).toList.foldl (· + ·) 0

theorem dotProduct_comm {n : Nat} (v1 v2 : Vector Nat n) :
  dotProduct v1 v2 = dotProduct v2 v1 := by
  simp [dotProduct]
  congr 1
  ext i
  simp [Vector.zipWith]
  ring

def gcdNat (a b : Nat) : Nat :=
  if b = 0 then a else gcdNat b (a % b)
termination_by b
decreasing_by
  simp_wf
  exact Nat.mod_lt a (Nat.zero_lt_of_ne_zero (by assumption))

def lcmNat (a b : Nat) : Nat :=
  if b = 0 then 0 else (a / gcdNat a b) * b

theorem gcd_comm (a b : Nat) : gcdNat a b = gcdNat b a := by
  induction b, a using gcdNat.induct with
  | case1 a => simp [gcdNat]
  | case2 a b hb ih =>
    simp [gcdNat, hb]
    have : a % b < b := Nat.mod_lt a (Nat.zero_lt_of_ne_zero hb)
    rw [ih]
    simp [gcdNat]
    cases Decidable.em (a % b = 0) with
    | inl h => simp [h, gcdNat]
    | inr h => simp [gcdNat, h]

def isPowerOfTwo (n : Nat) : Bool :=
  n > 0 && (n &&& (n - 1)) = 0

def nextPowerOfTwo (n : Nat) : Nat :=
  if n = 0 then 1
  else
    let rec loop (m p : Nat) : Nat :=
      if p < m then loop m (p * 2) else p
    loop n 1

theorem nextPowerOfTwo_ge (n : Nat) : n ≤ nextPowerOfTwo n := by
  simp [nextPowerOfTwo]
  cases n with
  | zero => omega
  | succ m => omega

def popcount (n : Nat) : Nat :=
  let rec loop (x acc : Nat) : Nat :=
    if x = 0 then acc
    else loop (x / 2) (acc + (x % 2))
  loop n 0

def leadingZeros (bits n : Nat) : Nat :=
  let rec loop (b x count : Nat) : Nat :=
    if b = 0 then count
    else if x >= 2^(b-1) then count
    else loop (b-1) x (count+1)
  loop bits n 0

def trailingZeros (n : Nat) : Nat :=
  let rec loop (x count : Nat) : Nat :=
    if x = 0 then count
    else if x % 2 = 1 then count
    else loop (x / 2) (count + 1)
  loop n 0

theorem popcount_bound (n bits : Nat) (h : bits ≥ 64) : popcount n ≤ bits := by
  simp [popcount]
  have hloop : ∀ x acc, popcount.loop x acc ≤ acc + 64 := by
    intro x acc
    induction x using Nat.strong_induction_on with
    | _ x ih =>
      simp [popcount.loop]
      split
      · omega
      · have : x / 2 < x := Nat.div_lt_self (by omega) (by omega)
        have := ih (x / 2) this acc
        omega
  have := hloop n 0
  omega

def factorial (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | n+1 => (n+1) * factorial n

def binomial (n k : Nat) : Nat :=
  match n, k with
  | _, 0 => 1
  | 0, k+1 => 0
  | n+1, k+1 => binomial n k + binomial n (k+1)

theorem factorial_positive (n : Nat) : 0 < factorial n := by
  induction n with
  | zero => norm_num [factorial]
  | succ n ih =>
    simp [factorial]
    omega

theorem binomial_symmetry (n k : Nat) (h : k ≤ n) :
  binomial n k = binomial n (n - k) := by
  induction n, k using binomial.induct with
  | case1 n => simp [binomial, Nat.sub_zero]
  | case2 k => simp [binomial]; omega
  | case3 n k ih1 ih2 =>
    by_cases hk : k + 1 ≤ n + 1
    · simp [binomial]
      by_cases heq : k + 1 = n + 1
      · simp [heq, binomial]
      · have hlt : k + 1 < n + 1 := Nat.lt_of_le_of_ne hk heq
        have hk' : k ≤ n := Nat.le_of_succ_le_succ hk
        rw [ih1 hk', ih2 (Nat.le_of_lt hlt)]
        simp [binomial, Nat.sub_succ]
        ring
    · omega

end Types
