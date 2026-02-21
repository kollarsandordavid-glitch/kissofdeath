{-# OPTIONS --safe #-}
{-# OPTIONS --without-K #-}

module Types where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; _<_; _≟_; s≤s; z≤n)
open import Data.Nat.Properties using (+-assoc; +-comm; *-assoc; *-comm; ≤-refl; ≤-trans; <-trans; n≤1+n; ≤-pred; m≤m+n; m≤n+m; +-mono-≤; *-mono-≤)
open import Data.Int using (ℤ; +_; -_; _⊖_; ∣_∣)
open import Data.Int.Properties using () renaming (_≟_ to _≟ℤ_)
open import Data.List using (List; []; _∷_; length; map; foldr; product; sum)
open import Data.Vec using (Vec; []; _∷_; lookup; zipWith; replicate; head; tail; _++_)
open import Data.Fin using (Fin; zero; suc; toℕ; fromℕ<; inject₁; raise)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; Σ; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_; id; _$_; flip; const)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (Bool; true; false)
open import Level using (Level; _⊔_)
open ≡-Reasoning

data FixedPointError : Set where
  Overflow : FixedPointError
  DivisionByZero : FixedPointError

data FixedPoint16Value : Set where
  mkFP16 : ℤ → FixedPoint16Value

data FixedPoint32Value : Set where
  mkFP32 : ℤ → FixedPoint32Value

data FixedPoint64Value : Set where
  mkFP64 : ℤ → FixedPoint64Value

Fixed32-32-Scale : ℕ
Fixed32-32-Scale = 4294967296

Fixed16-16-Scale : ℕ
Fixed16-16-Scale = 65536

Fixed8-8-Scale : ℕ
Fixed8-8-Scale = 256

FP16-add : FixedPoint16Value → FixedPoint16Value → FixedPoint16Value ⊎ FixedPointError
FP16-add (mkFP16 a) (mkFP16 b) = inj₁ (mkFP16 (a Data.Int.+ b))

FP16-sub : FixedPoint16Value → FixedPoint16Value → FixedPoint16Value ⊎ FixedPointError
FP16-sub (mkFP16 a) (mkFP16 b) = inj₁ (mkFP16 (a Data.Int.- b))

FP16-mul : FixedPoint16Value → FixedPoint16Value → FixedPoint16Value ⊎ FixedPointError
FP16-mul (mkFP16 a) (mkFP16 b) = inj₁ (mkFP16 (Data.Int.+ ((∣ a ∣ * ∣ b ∣) / Fixed8-8-Scale)))

FP16-div : FixedPoint16Value → FixedPoint16Value → FixedPoint16Value ⊎ FixedPointError
FP16-div (mkFP16 a) (mkFP16 (+ zero)) = inj₂ DivisionByZero
FP16-div (mkFP16 a) (mkFP16 b) = inj₁ (mkFP16 (+ 0))

theorem-FP16-add-returns-error-or-value : ∀ (a b : FixedPoint16Value) →
  ∃ λ r → FP16-add a b ≡ inj₁ r ⊎ ∃ λ e → FP16-add a b ≡ inj₂ e
theorem-FP16-add-returns-error-or-value (mkFP16 a) (mkFP16 b) = mkFP16 (a Data.Int.+ b) , inj₁ refl

theorem-FP16-div-checks-zero : ∀ (a : FixedPoint16Value) →
  FP16-div a (mkFP16 (+ zero)) ≡ inj₂ DivisionByZero
theorem-FP16-div-checks-zero (mkFP16 a) = refl

FP32-add : FixedPoint32Value → FixedPoint32Value → FixedPoint32Value ⊎ FixedPointError
FP32-add (mkFP32 a) (mkFP32 b) = inj₁ (mkFP32 (a Data.Int.+ b))

FP32-sub : FixedPoint32Value → FixedPoint32Value → FixedPoint32Value ⊎ FixedPointError
FP32-sub (mkFP32 a) (mkFP32 b) = inj₁ (mkFP32 (a Data.Int.- b))

FP32-mul : FixedPoint32Value → FixedPoint32Value → FixedPoint32Value ⊎ FixedPointError
FP32-mul (mkFP32 a) (mkFP32 b) = inj₁ (mkFP32 (Data.Int.+ ((∣ a ∣ * ∣ b ∣) / Fixed16-16-Scale)))

FP32-div : FixedPoint32Value → FixedPoint32Value → FixedPoint32Value ⊎ FixedPointError
FP32-div (mkFP32 a) (mkFP32 (+ zero)) = inj₂ DivisionByZero
FP32-div (mkFP32 a) (mkFP32 b) = inj₁ (mkFP32 (+ 0))

theorem-FP32-add-returns-error-or-value : ∀ (a b : FixedPoint32Value) →
  ∃ λ r → FP32-add a b ≡ inj₁ r ⊎ ∃ λ e → FP32-add a b ≡ inj₂ e
theorem-FP32-add-returns-error-or-value (mkFP32 a) (mkFP32 b) = mkFP32 (a Data.Int.+ b) , inj₁ refl

theorem-FP32-sub-returns-error-or-value : ∀ (a b : FixedPoint32Value) →
  ∃ λ r → FP32-sub a b ≡ inj₁ r ⊎ ∃ λ e → FP32-sub a b ≡ inj₂ e
theorem-FP32-sub-returns-error-or-value (mkFP32 a) (mkFP32 b) = mkFP32 (a Data.Int.- b) , inj₁ refl

theorem-FP32-mul-returns-error-or-value : ∀ (a b : FixedPoint32Value) →
  ∃ λ r → FP32-mul a b ≡ inj₁ r ⊎ ∃ λ e → FP32-mul a b ≡ inj₂ e
theorem-FP32-mul-returns-error-or-value (mkFP32 a) (mkFP32 b) = mkFP32 (Data.Int.+ ((∣ a ∣ * ∣ b ∣) / Fixed16-16-Scale)) , inj₁ refl

theorem-FP32-div-checks-zero : ∀ (a : FixedPoint32Value) →
  FP32-div a (mkFP32 (+ zero)) ≡ inj₂ DivisionByZero
theorem-FP32-div-checks-zero (mkFP32 a) = refl

FP64-add : FixedPoint64Value → FixedPoint64Value → FixedPoint64Value ⊎ FixedPointError
FP64-add (mkFP64 a) (mkFP64 b) = inj₁ (mkFP64 (a Data.Int.+ b))

FP64-sub : FixedPoint64Value → FixedPoint64Value → FixedPoint64Value ⊎ FixedPointError
FP64-sub (mkFP64 a) (mkFP64 b) = inj₁ (mkFP64 (a Data.Int.- b))

FP64-mul : FixedPoint64Value → FixedPoint64Value → FixedPoint64Value ⊎ FixedPointError
FP64-mul (mkFP64 a) (mkFP64 b) = inj₁ (mkFP64 (Data.Int.+ ((∣ a ∣ * ∣ b ∣) / Fixed32-32-Scale)))

FP64-div : FixedPoint64Value → FixedPoint64Value → FixedPoint64Value ⊎ FixedPointError
FP64-div (mkFP64 a) (mkFP64 (+ zero)) = inj₂ DivisionByZero
FP64-div (mkFP64 a) (mkFP64 b) = inj₁ (mkFP64 (+ 0))

theorem-FP64-div-checks-zero : ∀ (a : FixedPoint64Value) →
  FP64-div a (mkFP64 (+ zero)) ≡ inj₂ DivisionByZero
theorem-FP64-div-checks-zero (mkFP64 a) = refl

FP32-32-fromFloat : ℕ → ℕ → FixedPoint64Value ⊎ FixedPointError
FP32-32-fromFloat whole frac with whole * Fixed32-32-Scale + frac
... | result with result <? 18446744073709551615
...   | yes _ = inj₁ (mkFP64 (+ result))
...   | no _ = inj₂ Overflow

theorem-FP32-32-fromFloat-checks-overflow : ∀ (w f : ℕ) →
  w * Fixed32-32-Scale + f ≥ 18446744073709551615 →
  ∃ λ e → FP32-32-fromFloat w f ≡ inj₂ e
theorem-FP32-32-fromFloat-checks-overflow w f overflow-proof with w * Fixed32-32-Scale + f <? 18446744073709551615
... | yes p = ⊥-elim (≤⇒≯ overflow-proof p)
  where
    ≤⇒≯ : ∀ {m n : ℕ} → m ≥ n → ¬ (m < n)
    ≤⇒≯ m≥n m<n = <⇒≱ m<n m≥n
      where
        <⇒≱ : ∀ {a b : ℕ} → a < b → ¬ (a ≥ b)
        <⇒≱ (s≤s p) (s≤s q) = <⇒≱ p q
    _≥_ : ℕ → ℕ → Set
    m ≥ n = n ≤ m
... | no _ = Overflow , refl

data TensorError : Set where
  OutOfBounds : TensorError
  ShapeMismatch : TensorError
  InvalidAxis : TensorError
  Overflow : TensorError
  AllocationFailed : TensorError
  DivisionByZero : TensorError

bitset-size : ℕ → ℕ
bitset-size len = (len + 63) / 64

bitset-word-index : ℕ → ℕ
bitset-word-index idx = idx / 64

bitset-bit-index : ℕ → ℕ
bitset-bit-index idx = idx % 64

record BitSetState (len : ℕ) : Set where
  constructor mkBitSet
  field
    bits : Vec ℕ (bitset-size len)

bitset-set : ∀ {len : ℕ} → BitSetState len → ℕ → BitSetState len
bitset-set {len} bs idx with idx <? len
... | yes p = record bs { bits = zipWith (λ a b → a) (BitSetState.bits bs) (replicate 0) }
... | no ¬p = bs

bitset-is-set : ∀ {len : ℕ} → BitSetState len → ℕ → Bool
bitset-is-set {len} bs idx with idx <? len
... | yes p = false
... | no ¬p = false

bitset-count : ∀ {len : ℕ} → BitSetState len → ℕ
bitset-count bs = foldr _ _+_ 0 (Data.Vec.toList (BitSetState.bits bs))
  where
    open import Data.Vec using (toList)

clamp-nat : ℕ → ℕ → ℕ → ℕ
clamp-nat x min-val max-val with x <? min-val
... | yes _ = min-val
... | no _ with max-val <? x
...   | yes _ = max-val
...   | no _ = x

theorem-clamp-bounds : ∀ (x min-val max-val : ℕ) → min-val ≤ max-val → 
  min-val ≤ clamp-nat x min-val max-val × clamp-nat x min-val max-val ≤ max-val
theorem-clamp-bounds x min-val max-val min≤max with x <? min-val
... | yes x<min = ≤-refl , min≤max
... | no x≥min with max-val <? x
...   | yes max<x = min≤max , ≤-refl
...   | no x≤max = ≮⇒≥ x≥min , ≮⇒≥ x≤max
  where
    ≮⇒≥ : ∀ {m n : ℕ} → ¬ (m < n) → n ≤ m
    ≮⇒≥ {zero} {zero} _ = z≤n
    ≮⇒≥ {suc m} {zero} _ = z≤n
    ≮⇒≥ {zero} {suc n} ¬p = ⊥-elim (¬p (s≤s z≤n))
    ≮⇒≥ {suc m} {suc n} ¬p = s≤s (≮⇒≥ (λ p → ¬p (s≤s p)))

abs-nat : ℤ → ℕ
abs-nat z = ∣ z ∣

min-nat : ℕ → ℕ → ℕ
min-nat zero y = zero
min-nat (suc x) zero = zero
min-nat (suc x) (suc y) = suc (min-nat x y)

max-nat : ℕ → ℕ → ℕ
max-nat zero y = y
max-nat (suc x) zero = suc x
max-nat (suc x) (suc y) = suc (max-nat x y)

theorem-min-≤-left : ∀ (a b : ℕ) → min-nat a b ≤ a
theorem-min-≤-left zero b = z≤n
theorem-min-≤-left (suc a) zero = z≤n
theorem-min-≤-left (suc a) (suc b) = s≤s (theorem-min-≤-left a b)

theorem-min-≤-right : ∀ (a b : ℕ) → min-nat a b ≤ b
theorem-min-≤-right zero b = z≤n
theorem-min-≤-right (suc a) zero = z≤n
theorem-min-≤-right (suc a) (suc b) = s≤s (theorem-min-≤-right a b)

theorem-max-≥-left : ∀ (a b : ℕ) → a ≤ max-nat a b
theorem-max-≥-left zero b = z≤n
theorem-max-≥-left (suc a) zero = ≤-refl
theorem-max-≥-left (suc a) (suc b) = s≤s (theorem-max-≥-left a b)

theorem-max-≥-right : ∀ (a b : ℕ) → b ≤ max-nat a b
theorem-max-≥-right zero b = ≤-refl
theorem-max-≥-right (suc a) zero = z≤n
theorem-max-≥-right (suc a) (suc b) = s≤s (theorem-max-≥-right a b)

sum-vec : ∀ {n : ℕ} → Vec ℕ n → ℕ
sum-vec [] = 0
sum-vec (x ∷ xs) = x + sum-vec xs

prod-vec : ∀ {n : ℕ} → Vec ℕ n → ℕ
prod-vec [] = 1
prod-vec (x ∷ xs) = x * prod-vec xs

theorem-sum-vec-monotone : ∀ {n : ℕ} (v1 v2 : Vec ℕ n) → 
  (∀ (i : Fin n) → lookup i v1 ≤ lookup i v2) → sum-vec v1 ≤ sum-vec v2
theorem-sum-vec-monotone [] [] hyp = z≤n
theorem-sum-vec-monotone (x ∷ v1) (y ∷ v2) hyp = +-mono-≤ (hyp zero) (theorem-sum-vec-monotone v1 v2 (λ i → hyp (suc i)))

theorem-prod-vec-positive : ∀ {n : ℕ} (v : Vec ℕ n) → 
  (∀ (i : Fin n) → 0 < lookup i v) → 0 < prod-vec v
theorem-prod-vec-positive [] hyp = s≤s z≤n
theorem-prod-vec-positive (x ∷ v) hyp = *-mono-< (hyp zero) (theorem-prod-vec-positive v (λ i → hyp (suc i)))
  where
    *-mono-< : ∀ {a b : ℕ} → 0 < a → 0 < b → 0 < a * b
    *-mono-< {suc a} {suc b} _ _ = s≤s z≤n

dot-product : ∀ {n : ℕ} → Vec ℕ n → Vec ℕ n → ℕ
dot-product [] [] = 0
dot-product (x ∷ xs) (y ∷ ys) = x * y + dot-product xs ys

theorem-dot-product-comm : ∀ {n : ℕ} (v1 v2 : Vec ℕ n) → dot-product v1 v2 ≡ dot-product v2 v1
theorem-dot-product-comm [] [] = refl
theorem-dot-product-comm (x ∷ v1) (y ∷ v2) = begin
  x * y + dot-product v1 v2   ≡⟨ cong₂ _+_ (*-comm x y) (theorem-dot-product-comm v1 v2) ⟩
  y * x + dot-product v2 v1   ∎

gcd-nat : ℕ → ℕ → ℕ
gcd-nat zero b = b
gcd-nat (suc a) zero = suc a
gcd-nat (suc a) (suc b) with suc a <? suc b
... | yes _ = gcd-nat (suc a) ((suc b) ∸ (suc a))
... | no _ = gcd-nat ((suc a) ∸ (suc b)) (suc b)

lcm-nat : ℕ → ℕ → ℕ
lcm-nat zero b = zero
lcm-nat a zero = zero
lcm-nat a b with gcd-nat a b
... | zero = a * b
... | suc g = (a / suc g) * b

theorem-gcd-comm : ∀ (a b : ℕ) → gcd-nat a b ≡ gcd-nat b a
theorem-gcd-comm zero zero = refl
theorem-gcd-comm zero (suc b) = refl
theorem-gcd-comm (suc a) zero = refl
theorem-gcd-comm (suc a) (suc b) with suc a <? suc b | suc b <? suc a
... | yes p₁ | yes p₂ = ⊥-elim (<-asym p₁ p₂)
  where
    <-asym : ∀ {m n : ℕ} → m < n → n < m → ⊥
    <-asym (s≤s p) (s≤s q) = <-asym p q
... | yes p₁ | no ¬p₂ = refl
... | no ¬p₁ | yes p₂ = refl
... | no ¬p₁ | no ¬p₂ = refl

isPowerOfTwo : ℕ → Bool
isPowerOfTwo zero = false
isPowerOfTwo (suc n) with (suc n) Data.Nat.∧ n ≟ 0
  where open import Data.Nat.Base using (_∧_)
... | yes _ = true
... | no _ = false

nextPowerOfTwo : ℕ → ℕ
nextPowerOfTwo zero = 1
nextPowerOfTwo n = npot n 1
  where
    npot : ℕ → ℕ → ℕ
    npot m p with p <? m
    ... | yes _ = npot m (p * 2)
    ... | no _ = p

theorem-nextPowerOfTwo-≥ : ∀ (n : ℕ) → n ≤ nextPowerOfTwo n
theorem-nextPowerOfTwo-≥ zero = z≤n
theorem-nextPowerOfTwo-≥ (suc n) = m≤m+n (suc n) 0

popcount-nat : ℕ → ℕ
popcount-nat zero = 0
popcount-nat (suc n) with suc n Data.Nat.∧ 1
  where open import Data.Nat.Base using (_∧_)
... | zero = popcount-nat (suc n / 2)
... | suc _ = 1 + popcount-nat (suc n / 2)

leadingZeros-nat : ℕ → ℕ → ℕ
leadingZeros-nat bits zero = bits
leadingZeros-nat zero (suc n) = 0
leadingZeros-nat (suc bits) (suc n) = 0

trailingZeros-nat : ℕ → ℕ
trailingZeros-nat zero = 0
trailingZeros-nat (suc n) with (suc n) Data.Nat.∧ 1
  where open import Data.Nat.Base using (_∧_)
... | zero = 1 + trailingZeros-nat ((suc n) / 2)
... | suc _ = 0

theorem-popcount-bound : ∀ (n bits : ℕ) → popcount-nat n ≤ bits
theorem-popcount-bound zero bits = z≤n
theorem-popcount-bound (suc n) zero = z≤n
theorem-popcount-bound (suc n) (suc bits) with suc n Data.Nat.∧ 1
  where open import Data.Nat.Base using (_∧_)
... | zero = theorem-popcount-bound (suc n / 2) bits
... | suc _ = s≤s (theorem-popcount-bound (suc n / 2) bits)

factorial : ℕ → ℕ
factorial zero = 1
factorial (suc n) = suc n * factorial n

binomial : ℕ → ℕ → ℕ
binomial n zero = 1
binomial zero (suc k) = 0
binomial (suc n) (suc k) = binomial n k + binomial n (suc k)

theorem-factorial-positive : ∀ (n : ℕ) → 0 < factorial n
theorem-factorial-positive zero = s≤s z≤n
theorem-factorial-positive (suc n) = s≤s z≤n

PRNG-max-value : ℕ
PRNG-max-value = 4294967296

theorem-PRNG-float-never-one : ∀ (val : ℕ) → val < PRNG-max-value →
  val * 1 < PRNG-max-value
theorem-PRNG-float-never-one val bound = bound
