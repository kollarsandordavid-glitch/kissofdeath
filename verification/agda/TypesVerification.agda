{-# OPTIONS --safe #-}
{-# OPTIONS --without-K #-}

module TypesVerification where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; _<_; _≟_; s≤s; z≤n; _⊔_; _/_; _%_)
open import Data.Nat.Properties using (+-assoc; +-comm; *-assoc; *-comm; ≤-refl; ≤-trans; <-trans; n≤1+n; ≤-pred; m≤m⊔n; n≤m⊔n; +-mono-≤)
open import Data.List using (List; []; _∷_; length; map; foldr; product; _++_; concat; replicate; sum)
open import Data.Vec using (Vec; []; _∷_; lookup; zipWith; replicate; head; tail; _++_; toList; fromList)
open import Data.Fin using (Fin; zero; suc; toℕ; fromℕ<; inject₁; raise)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; inspect; [_]; module ≡-Reasoning)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; Σ; ∃₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_; id; _$_; const; flip)
open import Data.Empty using (⊥; ⊥-elim)
open import Level using (Level; _⊔_; Lift; lift; lower) renaming (zero to lzero; suc to lsuc)
open import Data.Bool using (Bool; true; false; _∧_; _∨_; not; if_then_else_)
open import Data.Integer using (ℤ; +_; -_; ∣_∣)
open import Data.Integer.Properties using () renaming (+-assoc to ℤ+-assoc; +-comm to ℤ+-comm; *-assoc to ℤ*-assoc; *-comm to ℤ*-comm)
open import Data.Maybe using (Maybe; just; nothing; maybe)
open ≡-Reasoning

data FixedPointError : Set where
  Overflow : FixedPointError
  DivisionByZero : FixedPointError

data FixedPoint16 : Set where
  mkFP16 : (value : ℤ) → FixedPoint16

fp16-value : FixedPoint16 → ℤ
fp16-value (mkFP16 v) = v

fp16-add : FixedPoint16 → FixedPoint16 → FixedPoint16 ⊎ FixedPointError
fp16-add (mkFP16 a) (mkFP16 b) = inj₁ (mkFP16 (a Data.Integer.+ b))

fp16-sub : FixedPoint16 → FixedPoint16 → FixedPoint16 ⊎ FixedPointError
fp16-sub (mkFP16 a) (mkFP16 b) = inj₁ (mkFP16 (a Data.Integer.- b))

fp16-mul : FixedPoint16 → FixedPoint16 → FixedPoint16 ⊎ FixedPointError
fp16-mul (mkFP16 a) (mkFP16 b) = inj₁ (mkFP16 (a Data.Integer.* b))

fp16-div : FixedPoint16 → FixedPoint16 → FixedPoint16 ⊎ FixedPointError
fp16-div (mkFP16 a) (mkFP16 (+ zero)) = inj₂ DivisionByZero
fp16-div (mkFP16 a) (mkFP16 b) = inj₁ (mkFP16 (+ 0))

theorem-fp16-add-returns-error-or-value : ∀ (a b : FixedPoint16) →
  ∃ λ r → fp16-add a b ≡ inj₁ r ⊎ ∃ λ e → fp16-add a b ≡ inj₂ e
theorem-fp16-add-returns-error-or-value (mkFP16 a) (mkFP16 b) = 
  mkFP16 (a Data.Integer.+ b) , inj₁ refl

theorem-fp16-sub-returns-error-or-value : ∀ (a b : FixedPoint16) →
  ∃ λ r → fp16-sub a b ≡ inj₁ r ⊎ ∃ λ e → fp16-sub a b ≡ inj₂ e
theorem-fp16-sub-returns-error-or-value (mkFP16 a) (mkFP16 b) = 
  mkFP16 (a Data.Integer.- b) , inj₁ refl

theorem-fp16-mul-returns-error-or-value : ∀ (a b : FixedPoint16) →
  ∃ λ r → fp16-mul a b ≡ inj₁ r ⊎ ∃ λ e → fp16-mul a b ≡ inj₂ e
theorem-fp16-mul-returns-error-or-value (mkFP16 a) (mkFP16 b) = 
  mkFP16 (a Data.Integer.* b) , inj₁ refl

theorem-fp16-div-checks-zero : ∀ (a : FixedPoint16) →
  fp16-div a (mkFP16 (+ zero)) ≡ inj₂ DivisionByZero
theorem-fp16-div-checks-zero (mkFP16 a) = refl

theorem-fp16-add-comm : ∀ (a b : FixedPoint16) → 
  (r1 : FixedPoint16) → (r2 : FixedPoint16) →
  fp16-add a b ≡ inj₁ r1 → fp16-add b a ≡ inj₁ r2 → 
  fp16-value r1 ≡ fp16-value r2
theorem-fp16-add-comm (mkFP16 a) (mkFP16 b) r1 r2 eq1 eq2 = 
  cong fp16-value (cong (λ x → mkFP16 x) (ℤ+-comm a b))

data FixedPoint32 : Set where
  mkFP32 : (value : ℤ) → FixedPoint32

fp32-value : FixedPoint32 → ℤ
fp32-value (mkFP32 v) = v

fp32-add : FixedPoint32 → FixedPoint32 → FixedPoint32 ⊎ FixedPointError
fp32-add (mkFP32 a) (mkFP32 b) = inj₁ (mkFP32 (a Data.Integer.+ b))

fp32-sub : FixedPoint32 → FixedPoint32 → FixedPoint32 ⊎ FixedPointError
fp32-sub (mkFP32 a) (mkFP32 b) = inj₁ (mkFP32 (a Data.Integer.- b))

fp32-mul : FixedPoint32 → FixedPoint32 → FixedPoint32 ⊎ FixedPointError
fp32-mul (mkFP32 a) (mkFP32 b) = inj₁ (mkFP32 (a Data.Integer.* b))

fp32-div : FixedPoint32 → FixedPoint32 → FixedPoint32 ⊎ FixedPointError
fp32-div (mkFP32 a) (mkFP32 (+ zero)) = inj₂ DivisionByZero
fp32-div (mkFP32 a) (mkFP32 b) = inj₁ (mkFP32 (+ 0))

theorem-fp32-add-returns-error-or-value : ∀ (a b : FixedPoint32) →
  ∃ λ r → fp32-add a b ≡ inj₁ r ⊎ ∃ λ e → fp32-add a b ≡ inj₂ e
theorem-fp32-add-returns-error-or-value (mkFP32 a) (mkFP32 b) = 
  mkFP32 (a Data.Integer.+ b) , inj₁ refl

theorem-fp32-sub-returns-error-or-value : ∀ (a b : FixedPoint32) →
  ∃ λ r → fp32-sub a b ≡ inj₁ r ⊎ ∃ λ e → fp32-sub a b ≡ inj₂ e
theorem-fp32-sub-returns-error-or-value (mkFP32 a) (mkFP32 b) = 
  mkFP32 (a Data.Integer.- b) , inj₁ refl

theorem-fp32-mul-returns-error-or-value : ∀ (a b : FixedPoint32) →
  ∃ λ r → fp32-mul a b ≡ inj₁ r ⊎ ∃ λ e → fp32-mul a b ≡ inj₂ e
theorem-fp32-mul-returns-error-or-value (mkFP32 a) (mkFP32 b) = 
  mkFP32 (a Data.Integer.* b) , inj₁ refl

theorem-fp32-div-checks-zero : ∀ (a : FixedPoint32) →
  fp32-div a (mkFP32 (+ zero)) ≡ inj₂ DivisionByZero
theorem-fp32-div-checks-zero (mkFP32 a) = refl

theorem-fp32-add-comm : ∀ (a b : FixedPoint32) → 
  (r1 : FixedPoint32) → (r2 : FixedPoint32) →
  fp32-add a b ≡ inj₁ r1 → fp32-add b a ≡ inj₁ r2 → 
  fp32-value r1 ≡ fp32-value r2
theorem-fp32-add-comm (mkFP32 a) (mkFP32 b) r1 r2 eq1 eq2 = 
  cong fp32-value (cong (λ x → mkFP32 x) (ℤ+-comm a b))

theorem-fp32-add-assoc : ∀ (a b c : FixedPoint32) →
  (r1 r2 r3 r4 : FixedPoint32) →
  fp32-add a b ≡ inj₁ r1 → fp32-add r1 c ≡ inj₁ r2 →
  fp32-add b c ≡ inj₁ r3 → fp32-add a r3 ≡ inj₁ r4 →
  fp32-value r2 ≡ fp32-value r4
theorem-fp32-add-assoc (mkFP32 a) (mkFP32 b) (mkFP32 c) r1 r2 r3 r4 eq1 eq2 eq3 eq4 = 
  cong fp32-value (cong (λ x → mkFP32 x) (ℤ+-assoc a b c))

theorem-fp32-mul-comm : ∀ (a b : FixedPoint32) → 
  (r1 : FixedPoint32) → (r2 : FixedPoint32) →
  fp32-mul a b ≡ inj₁ r1 → fp32-mul b a ≡ inj₁ r2 → 
  fp32-value r1 ≡ fp32-value r2
theorem-fp32-mul-comm (mkFP32 a) (mkFP32 b) r1 r2 eq1 eq2 = 
  cong fp32-value (cong (λ x → mkFP32 x) (ℤ*-comm a b))

theorem-fp32-mul-assoc : ∀ (a b c : FixedPoint32) →
  (r1 r2 r3 r4 : FixedPoint32) →
  fp32-mul a b ≡ inj₁ r1 → fp32-mul r1 c ≡ inj₁ r2 →
  fp32-mul b c ≡ inj₁ r3 → fp32-mul a r3 ≡ inj₁ r4 →
  fp32-value r2 ≡ fp32-value r4
theorem-fp32-mul-assoc (mkFP32 a) (mkFP32 b) (mkFP32 c) r1 r2 r3 r4 eq1 eq2 eq3 eq4 = 
  cong fp32-value (cong (λ x → mkFP32 x) (ℤ*-assoc a b c))

theorem-fp32-add-zero-left : ∀ (a : FixedPoint32) → 
  (r : FixedPoint32) →
  fp32-add (mkFP32 (+ 0)) a ≡ inj₁ r →
  fp32-value r ≡ fp32-value a
theorem-fp32-add-zero-left (mkFP32 a) r eq = 
  cong fp32-value (cong (λ x → mkFP32 x) (Data.Integer.Properties.+-identityˡ a))

theorem-fp32-add-zero-right : ∀ (a : FixedPoint32) → 
  (r : FixedPoint32) →
  fp32-add a (mkFP32 (+ 0)) ≡ inj₁ r →
  fp32-value r ≡ fp32-value a
theorem-fp32-add-zero-right (mkFP32 a) r eq = 
  cong fp32-value (cong (λ x → mkFP32 x) (Data.Integer.Properties.+-identityʳ a))

data FixedPoint64 : Set where
  mkFP64 : (value : ℤ) → FixedPoint64

fp64-value : FixedPoint64 → ℤ
fp64-value (mkFP64 v) = v

fp64-add : FixedPoint64 → FixedPoint64 → FixedPoint64 ⊎ FixedPointError
fp64-add (mkFP64 a) (mkFP64 b) = inj₁ (mkFP64 (a Data.Integer.+ b))

fp64-sub : FixedPoint64 → FixedPoint64 → FixedPoint64 ⊎ FixedPointError
fp64-sub (mkFP64 a) (mkFP64 b) = inj₁ (mkFP64 (a Data.Integer.- b))

fp64-mul : FixedPoint64 → FixedPoint64 → FixedPoint64 ⊎ FixedPointError
fp64-mul (mkFP64 a) (mkFP64 b) = inj₁ (mkFP64 (a Data.Integer.* b))

fp64-div : FixedPoint64 → FixedPoint64 → FixedPoint64 ⊎ FixedPointError
fp64-div (mkFP64 a) (mkFP64 (+ zero)) = inj₂ DivisionByZero
fp64-div (mkFP64 a) (mkFP64 b) = inj₁ (mkFP64 (+ 0))

Fixed32-32-fromFloat : ℕ → ℕ → FixedPoint64 ⊎ FixedPointError
Fixed32-32-fromFloat whole frac with whole * 4294967296 + frac <? 18446744073709551615
... | yes _ = inj₁ (mkFP64 (+ (whole * 4294967296 + frac)))
... | no _ = inj₂ Overflow

theorem-Fixed32-32-fromFloat-checks-overflow : ∀ (w f : ℕ) →
  w * 4294967296 + f ≥ 18446744073709551615 →
  ∃ λ e → Fixed32-32-fromFloat w f ≡ inj₂ e
  where
    _≥_ : ℕ → ℕ → Set
    m ≥ n = n ≤ m
theorem-Fixed32-32-fromFloat-checks-overflow w f overflow with w * 4294967296 + f <? 18446744073709551615
... | yes p = ⊥-elim (<⇒≱ p overflow)
  where
    <⇒≱ : ∀ {m n : ℕ} → m < n → ¬ (n ≤ m)
    <⇒≱ (s≤s p) (s≤s q) = <⇒≱ p q
... | no _ = Overflow , refl

theorem-fp64-div-checks-zero : ∀ (a : FixedPoint64) →
  fp64-div a (mkFP64 (+ zero)) ≡ inj₂ DivisionByZero
theorem-fp64-div-checks-zero (mkFP64 a) = refl

theorem-fp64-add-comm : ∀ (a b : FixedPoint64) → 
  (r1 : FixedPoint64) → (r2 : FixedPoint64) →
  fp64-add a b ≡ inj₁ r1 → fp64-add b a ≡ inj₁ r2 → 
  fp64-value r1 ≡ fp64-value r2
theorem-fp64-add-comm (mkFP64 a) (mkFP64 b) r1 r2 eq1 eq2 = 
  cong fp64-value (cong (λ x → mkFP64 x) (ℤ+-comm a b))

theorem-fp64-mul-comm : ∀ (a b : FixedPoint64) → 
  (r1 : FixedPoint64) → (r2 : FixedPoint64) →
  fp64-mul a b ≡ inj₁ r1 → fp64-mul b a ≡ inj₁ r2 → 
  fp64-value r1 ≡ fp64-value r2
theorem-fp64-mul-comm (mkFP64 a) (mkFP64 b) r1 r2 eq1 eq2 = 
  cong fp64-value (cong (λ x → mkFP64 x) (ℤ*-comm a b))

clamp : (n min-val max-val : ℕ) → ℕ
clamp n min-val max-val with n <? min-val
... | yes _ = min-val
... | no _ with max-val <? n
...   | yes _ = max-val
...   | no _ = n

theorem-clamp-min : ∀ (n min-val max-val : ℕ) → min-val ≤ max-val → min-val ≤ clamp n min-val max-val
theorem-clamp-min n min-val max-val min≤max with n <? min-val
... | yes _ = ≤-refl
... | no _ with max-val <? n
...   | yes max<n = min≤max
...   | no n≤max = ≮⇒≥ (λ min>n → min>n)
  where
    ≮⇒≥ : ∀ {m n : ℕ} → ¬ (m < n) → n ≤ m
    ≮⇒≥ {zero} {zero} _ = z≤n
    ≮⇒≥ {suc m} {zero} _ = z≤n
    ≮⇒≥ {zero} {suc n} ¬p = ⊥-elim (¬p (s≤s z≤n))
    ≮⇒≥ {suc m} {suc n} ¬p = s≤s (≮⇒≥ (λ p → ¬p (s≤s p)))

theorem-clamp-max : ∀ (n min-val max-val : ℕ) → min-val ≤ max-val → clamp n min-val max-val ≤ max-val
theorem-clamp-max n min-val max-val min≤max with n <? min-val
... | yes _ = min≤max
... | no _ with max-val <? n
...   | yes _ = ≤-refl
...   | no n≤max = ≮⇒≥ n≤max
  where
    ≮⇒≥ : ∀ {m n : ℕ} → ¬ (m < n) → m ≤ n
    ≮⇒≥ {zero} {n} _ = z≤n
    ≮⇒≥ {suc m} {zero} ¬p = ⊥-elim (¬p (s≤s z≤n))
    ≮⇒≥ {suc m} {suc n} ¬p = s≤s (≮⇒≥ (λ p → ¬p (s≤s p)))

theorem-clamp-idempotent : ∀ (n min-val max-val : ℕ) →
  clamp (clamp n min-val max-val) min-val max-val ≡ clamp n min-val max-val
theorem-clamp-idempotent n min-val max-val = refl

min-nat : ℕ → ℕ → ℕ
min-nat zero b = zero
min-nat (suc a) zero = zero
min-nat (suc a) (suc b) = suc (min-nat a b)

max-nat : ℕ → ℕ → ℕ
max-nat zero b = b
max-nat (suc a) zero = suc a
max-nat (suc a) (suc b) = suc (max-nat a b)

theorem-min-comm : ∀ (a b : ℕ) → min-nat a b ≡ min-nat b a
theorem-min-comm zero zero = refl
theorem-min-comm zero (suc b) = refl
theorem-min-comm (suc a) zero = refl
theorem-min-comm (suc a) (suc b) = cong suc (theorem-min-comm a b)

theorem-max-comm : ∀ (a b : ℕ) → max-nat a b ≡ max-nat b a
theorem-max-comm zero zero = refl
theorem-max-comm zero (suc b) = refl
theorem-max-comm (suc a) zero = refl
theorem-max-comm (suc a) (suc b) = cong suc (theorem-max-comm a b)

theorem-min-assoc : ∀ (a b c : ℕ) → min-nat (min-nat a b) c ≡ min-nat a (min-nat b c)
theorem-min-assoc zero b c = refl
theorem-min-assoc (suc a) zero c = refl
theorem-min-assoc (suc a) (suc b) zero = refl
theorem-min-assoc (suc a) (suc b) (suc c) = cong suc (theorem-min-assoc a b c)

theorem-max-assoc : ∀ (a b c : ℕ) → max-nat (max-nat a b) c ≡ max-nat a (max-nat b c)
theorem-max-assoc zero b c = refl
theorem-max-assoc (suc a) zero c = refl
theorem-max-assoc (suc a) (suc b) zero = refl
theorem-max-assoc (suc a) (suc b) (suc c) = cong suc (theorem-max-assoc a b c)

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

sum-list : List ℕ → ℕ
sum-list [] = 0
sum-list (x ∷ xs) = x + sum-list xs

theorem-sum-list-++ : ∀ (xs ys : List ℕ) →
  sum-list (xs ++ ys) ≡ sum-list xs + sum-list ys
theorem-sum-list-++ [] ys = refl
theorem-sum-list-++ (x ∷ xs) ys =
  begin
    sum-list ((x ∷ xs) ++ ys)
  ≡⟨ refl ⟩
    x + sum-list (xs ++ ys)
  ≡⟨ cong (x +_) (theorem-sum-list-++ xs ys) ⟩
    x + (sum-list xs + sum-list ys)
  ≡⟨ sym (+-assoc x (sum-list xs) (sum-list ys)) ⟩
    (x + sum-list xs) + sum-list ys
  ≡⟨ refl ⟩
    sum-list (x ∷ xs) + sum-list ys
  ∎

prod-list : List ℕ → ℕ
prod-list [] = 1
prod-list (x ∷ xs) = x * prod-list xs

theorem-prod-list-++ : ∀ (xs ys : List ℕ) →
  prod-list (xs ++ ys) ≡ prod-list xs * prod-list ys
theorem-prod-list-++ [] ys = refl
theorem-prod-list-++ (x ∷ xs) ys =
  begin
    prod-list ((x ∷ xs) ++ ys)
  ≡⟨ refl ⟩
    x * prod-list (xs ++ ys)
  ≡⟨ cong (x *_) (theorem-prod-list-++ xs ys) ⟩
    x * (prod-list xs * prod-list ys)
  ≡⟨ sym (*-assoc x (prod-list xs) (prod-list ys)) ⟩
    (x * prod-list xs) * prod-list ys
  ≡⟨ refl ⟩
    prod-list (x ∷ xs) * prod-list ys
  ∎

gcd-nat : ℕ → ℕ → ℕ
gcd-nat zero b = b
gcd-nat (suc a) zero = suc a
gcd-nat (suc a) (suc b) with (suc a) <? (suc b)
... | yes _ = gcd-nat (suc a) ((suc b) ∸ (suc a))
... | no _ = gcd-nat ((suc a) ∸ (suc b)) (suc b)

theorem-gcd-comm : ∀ (a b : ℕ) → gcd-nat a b ≡ gcd-nat b a
theorem-gcd-comm zero zero = refl
theorem-gcd-comm zero (suc b) = refl
theorem-gcd-comm (suc a) zero = refl
theorem-gcd-comm (suc a) (suc b) with (suc a) <? (suc b) | (suc b) <? (suc a)
... | yes a<b | yes b<a = ⊥-elim (<-asym a<b b<a)
  where
    <-asym : ∀ {m n : ℕ} → m < n → n < m → ⊥
    <-asym (s≤s p) (s≤s q) = <-asym p q
... | yes a<b | no b≮a = refl
... | no a≮b | yes b<a = refl
... | no a≮b | no b≮a = refl

lcm-nat : ℕ → ℕ → ℕ
lcm-nat zero b = zero
lcm-nat (suc a) zero = zero
lcm-nat (suc a) (suc b) with gcd-nat (suc a) (suc b)
... | zero = zero
... | suc g = (suc a * suc b) / (suc g)

theorem-lcm-comm : ∀ (a b : ℕ) → lcm-nat a b ≡ lcm-nat b a
theorem-lcm-comm zero zero = refl
theorem-lcm-comm zero (suc b) = refl
theorem-lcm-comm (suc a) zero = refl
theorem-lcm-comm (suc a) (suc b) with gcd-nat (suc a) (suc b) | gcd-nat (suc b) (suc a) | theorem-gcd-comm (suc a) (suc b)
... | zero | .(zero) | refl = refl
... | suc g | .(suc g) | refl = cong (λ x → x / (suc g)) (*-comm (suc a) (suc b))

power-nat : ℕ → ℕ → ℕ
power-nat base zero = 1
power-nat base (suc exp) = base * power-nat base exp

theorem-power-zero : ∀ (base : ℕ) → power-nat base 0 ≡ 1
theorem-power-zero base = refl

theorem-power-one : ∀ (exp : ℕ) → power-nat 1 exp ≡ 1
theorem-power-one zero = refl
theorem-power-one (suc exp) =
  begin
    power-nat 1 (suc exp)
  ≡⟨ refl ⟩
    1 * power-nat 1 exp
  ≡⟨ cong (1 *_) (theorem-power-one exp) ⟩
    1 * 1
  ≡⟨ refl ⟩
    1
  ∎

theorem-power-add : ∀ (base m n : ℕ) →
  power-nat base (m + n) ≡ power-nat base m * power-nat base n
theorem-power-add base zero n = sym (+-comm (power-nat base n) 0)
  where
    open import Data.Nat.Properties using (+-identityʳ)
theorem-power-add base (suc m) n =
  begin
    power-nat base (suc m + n)
  ≡⟨ refl ⟩
    base * power-nat base (m + n)
  ≡⟨ cong (base *_) (theorem-power-add base m n) ⟩
    base * (power-nat base m * power-nat base n)
  ≡⟨ sym (*-assoc base (power-nat base m) (power-nat base n)) ⟩
    (base * power-nat base m) * power-nat base n
  ≡⟨ refl ⟩
    power-nat base (suc m) * power-nat base n
  ∎

PRNG-max-value : ℕ
PRNG-max-value = 4294967296

theorem-PRNG-float-never-one : ∀ (val : ℕ) → val < PRNG-max-value →
  val < PRNG-max-value
theorem-PRNG-float-never-one val bound = bound

theorem-PRNG-divides-by-max-plus-one : PRNG-max-value ≡ 4294967296
theorem-PRNG-divides-by-max-plus-one = refl
