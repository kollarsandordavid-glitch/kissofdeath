{-# OPTIONS --safe #-}
{-# OPTIONS --without-K #-}

module TensorArithmeticLemmas where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; _<_)
open import Data.Nat.Properties
open import Data.Rational as ℚ using (ℚ; mkℚ; _+_; _*_; _-_; 0ℚ; 1ℚ)
open import Data.Rational.Properties
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)
open ≡-Reasoning

lemma-+-zero-left : ∀ (x : ℚ) → 0ℚ ℚ.+ x ≡ x
lemma-+-zero-left x = ℚ.+-identityˡ x

lemma-+-zero-right : ∀ (x : ℚ) → x ℚ.+ 0ℚ ≡ x
lemma-+-zero-right x = ℚ.+-identityʳ x

lemma-*-one-left : ∀ (x : ℚ) → 1ℚ ℚ.* x ≡ x
lemma-*-one-left x = ℚ.*-identityˡ x

lemma-*-one-right : ∀ (x : ℚ) → x ℚ.* 1ℚ ≡ x
lemma-*-one-right x = ℚ.*-identityʳ x

lemma-*-zero-left : ∀ (x : ℚ) → 0ℚ ℚ.* x ≡ 0ℚ
lemma-*-zero-left x = ℚ.*-zeroˡ x

lemma-*-zero-right : ∀ (x : ℚ) → x ℚ.* 0ℚ ≡ 0ℚ
lemma-*-zero-right x = ℚ.*-zeroʳ x

lemma-+-comm : ∀ (x y : ℚ) → x ℚ.+ y ≡ y ℚ.+ x
lemma-+-comm x y = ℚ.+-comm x y

lemma-+-assoc : ∀ (x y z : ℚ) → (x ℚ.+ y) ℚ.+ z ≡ x ℚ.+ (y ℚ.+ z)
lemma-+-assoc x y z = ℚ.+-assoc x y z

lemma-*-comm : ∀ (x y : ℚ) → x ℚ.* y ≡ y ℚ.* x
lemma-*-comm x y = ℚ.*-comm x y

lemma-*-assoc : ∀ (x y z : ℚ) → (x ℚ.* y) ℚ.* z ≡ x ℚ.* (y ℚ.* z)
lemma-*-assoc x y z = ℚ.*-assoc x y z

lemma-distrib-left : ∀ (x y z : ℚ) → x ℚ.* (y ℚ.+ z) ≡ (x ℚ.* y) ℚ.+ (x ℚ.* z)
lemma-distrib-left x y z = ℚ.*-distribˡ-+ x y z

lemma-distrib-right : ∀ (x y z : ℚ) → (x ℚ.+ y) ℚ.* z ≡ (x ℚ.* z) ℚ.+ (y ℚ.* z)
lemma-distrib-right x y z = ℚ.*-distribʳ-+ z x y

lemma-+-cancel-left : ∀ (x y z : ℚ) → x ℚ.+ y ≡ x ℚ.+ z → y ≡ z
lemma-+-cancel-left x y z prf = ℚ.+-cancelˡ-≡ x prf

lemma-+-cancel-right : ∀ (x y z : ℚ) → x ℚ.+ z ≡ y ℚ.+ z → x ≡ y
lemma-+-cancel-right x y z prf = ℚ.+-cancelʳ-≡ z prf

lemma-+-rearrange : ∀ (a b c d : ℚ) → (a ℚ.+ b) ℚ.+ (c ℚ.+ d) ≡ (a ℚ.+ c) ℚ.+ (b ℚ.+ d)
lemma-+-rearrange a b c d = begin
  (a ℚ.+ b) ℚ.+ (c ℚ.+ d)
    ≡⟨ ℚ.+-assoc a b (c ℚ.+ d) ⟩
  a ℚ.+ (b ℚ.+ (c ℚ.+ d))
    ≡⟨ cong (a ℚ.+_) (sym (ℚ.+-assoc b c d)) ⟩
  a ℚ.+ ((b ℚ.+ c) ℚ.+ d)
    ≡⟨ cong (λ w → a ℚ.+ (w ℚ.+ d)) (ℚ.+-comm b c) ⟩
  a ℚ.+ ((c ℚ.+ b) ℚ.+ d)
    ≡⟨ cong (a ℚ.+_) (ℚ.+-assoc c b d) ⟩
  a ℚ.+ (c ℚ.+ (b ℚ.+ d))
    ≡⟨ sym (ℚ.+-assoc a c (b ℚ.+ d)) ⟩
  (a ℚ.+ c) ℚ.+ (b ℚ.+ d) ∎

lemma-*-rearrange : ∀ (a b c d : ℚ) → (a ℚ.* b) ℚ.* (c ℚ.* d) ≡ (a ℚ.* c) ℚ.* (b ℚ.* d)
lemma-*-rearrange a b c d = begin
  (a ℚ.* b) ℚ.* (c ℚ.* d)
    ≡⟨ ℚ.*-assoc a b (c ℚ.* d) ⟩
  a ℚ.* (b ℚ.* (c ℚ.* d))
    ≡⟨ cong (a ℚ.*_) (sym (ℚ.*-assoc b c d)) ⟩
  a ℚ.* ((b ℚ.* c) ℚ.* d)
    ≡⟨ cong (λ w → a ℚ.* (w ℚ.* d)) (ℚ.*-comm b c) ⟩
  a ℚ.* ((c ℚ.* b) ℚ.* d)
    ≡⟨ cong (a ℚ.*_) (ℚ.*-assoc c b d) ⟩
  a ℚ.* (c ℚ.* (b ℚ.* d))
    ≡⟨ sym (ℚ.*-assoc a c (b ℚ.* d)) ⟩
  (a ℚ.* c) ℚ.* (b ℚ.* d) ∎

lemma-double-negation : ∀ (x : ℚ) → ℚ.- (ℚ.- x) ≡ x
lemma-double-negation x = ℚ.neg-involutive x

lemma-neg-distributes-+ : ∀ (x y : ℚ) → ℚ.- (x ℚ.+ y) ≡ (ℚ.- x) ℚ.+ (ℚ.- y)
lemma-neg-distributes-+ x y = ℚ.neg-distrib-+ x y

lemma-neg-distributes-* : ∀ (x y : ℚ) → ℚ.- (x ℚ.* y) ≡ (ℚ.- x) ℚ.* y
lemma-neg-distributes-* x y = ℚ.neg-distribˡ-* x y

lemma-neg-distributes-*-right : ∀ (x y : ℚ) → ℚ.- (x ℚ.* y) ≡ x ℚ.* (ℚ.- y)
lemma-neg-distributes-*-right x y = ℚ.neg-distribʳ-* x y

lemma-+-inverse-left : ∀ (x : ℚ) → (ℚ.- x) ℚ.+ x ≡ 0ℚ
lemma-+-inverse-left x = ℚ.+-inverseˡ x

lemma-+-inverse-right : ∀ (x : ℚ) → x ℚ.+ (ℚ.- x) ≡ 0ℚ
lemma-+-inverse-right x = ℚ.+-inverseʳ x

lemma-subtraction-definition : ∀ (x y : ℚ) → x ℚ.- y ≡ x ℚ.+ (ℚ.- y)
lemma-subtraction-definition x y = refl

lemma-subtraction-self : ∀ (x : ℚ) → x ℚ.- x ≡ 0ℚ
lemma-subtraction-self x = ℚ.+-inverseʳ x

lemma-subtraction-zero : ∀ (x : ℚ) → x ℚ.- 0ℚ ≡ x
lemma-subtraction-zero x = ℚ.+-identityʳ x

lemma-zero-subtraction : ∀ (x : ℚ) → 0ℚ ℚ.- x ≡ ℚ.- x
lemma-zero-subtraction x = ℚ.+-identityˡ (ℚ.- x)

lemma-subtraction-addition : ∀ (x y z : ℚ) → (x ℚ.- y) ℚ.+ y ≡ x
lemma-subtraction-addition x y z = begin
  (x ℚ.- y) ℚ.+ y
    ≡⟨ cong (_ℚ.+ y) (lemma-subtraction-definition x y) ⟩
  (x ℚ.+ (ℚ.- y)) ℚ.+ y
    ≡⟨ ℚ.+-assoc x (ℚ.- y) y ⟩
  x ℚ.+ ((ℚ.- y) ℚ.+ y)
    ≡⟨ cong (x ℚ.+_) (ℚ.+-inverseˡ y) ⟩
  x ℚ.+ 0ℚ
    ≡⟨ ℚ.+-identityʳ x ⟩
  x ∎

lemma-addition-subtraction : ∀ (x y z : ℚ) → (x ℚ.+ y) ℚ.- y ≡ x
lemma-addition-subtraction x y z = begin
  (x ℚ.+ y) ℚ.- y
    ≡⟨ lemma-subtraction-definition (x ℚ.+ y) y ⟩
  (x ℚ.+ y) ℚ.+ (ℚ.- y)
    ≡⟨ ℚ.+-assoc x y (ℚ.- y) ⟩
  x ℚ.+ (y ℚ.+ (ℚ.- y))
    ≡⟨ cong (x ℚ.+_) (ℚ.+-inverseʳ y) ⟩
  x ℚ.+ 0ℚ
    ≡⟨ ℚ.+-identityʳ x ⟩
  x ∎

lemma-subtraction-comm : ∀ (x y z : ℚ) → (x ℚ.- y) ℚ.- z ≡ (x ℚ.- z) ℚ.- y
lemma-subtraction-comm x y z = begin
  (x ℚ.- y) ℚ.- z
    ≡⟨ cong (_ℚ.- z) (lemma-subtraction-definition x y) ⟩
  (x ℚ.+ (ℚ.- y)) ℚ.- z
    ≡⟨ lemma-subtraction-definition (x ℚ.+ (ℚ.- y)) z ⟩
  (x ℚ.+ (ℚ.- y)) ℚ.+ (ℚ.- z)
    ≡⟨ ℚ.+-assoc x (ℚ.- y) (ℚ.- z) ⟩
  x ℚ.+ ((ℚ.- y) ℚ.+ (ℚ.- z))
    ≡⟨ cong (x ℚ.+_) (ℚ.+-comm (ℚ.- y) (ℚ.- z)) ⟩
  x ℚ.+ ((ℚ.- z) ℚ.+ (ℚ.- y))
    ≡⟨ sym (ℚ.+-assoc x (ℚ.- z) (ℚ.- y)) ⟩
  (x ℚ.+ (ℚ.- z)) ℚ.+ (ℚ.- y)
    ≡⟨ sym (lemma-subtraction-definition (x ℚ.+ (ℚ.- z)) y) ⟩
  (x ℚ.+ (ℚ.- z)) ℚ.- y
    ≡⟨ cong (_ℚ.- y) (sym (lemma-subtraction-definition x z)) ⟩
  (x ℚ.- z) ℚ.- y ∎

lemma-*-left-absorbs-neg : ∀ (x y : ℚ) → (ℚ.- x) ℚ.* y ≡ ℚ.- (x ℚ.* y)
lemma-*-left-absorbs-neg x y = ℚ.neg-distribˡ-* x y

lemma-*-right-absorbs-neg : ∀ (x y : ℚ) → x ℚ.* (ℚ.- y) ≡ ℚ.- (x ℚ.* y)
lemma-*-right-absorbs-neg x y = ℚ.neg-distribʳ-* x y

lemma-neg-*-neg : ∀ (x y : ℚ) → (ℚ.- x) ℚ.* (ℚ.- y) ≡ x ℚ.* y
lemma-neg-*-neg x y = begin
  (ℚ.- x) ℚ.* (ℚ.- y)
    ≡⟨ ℚ.neg-distribˡ-* x (ℚ.- y) ⟩
  ℚ.- (x ℚ.* (ℚ.- y))
    ≡⟨ cong ℚ.-_ (ℚ.neg-distribʳ-* x y) ⟩
  ℚ.- (ℚ.- (x ℚ.* y))
    ≡⟨ ℚ.neg-involutive (x ℚ.* y) ⟩
  x ℚ.* y ∎

lemma-distributive-+ : ∀ (a b c d : ℚ) → (a ℚ.+ b) ℚ.* (c ℚ.+ d) ≡ (a ℚ.* c) ℚ.+ (a ℚ.* d) ℚ.+ (b ℚ.* c) ℚ.+ (b ℚ.* d)
lemma-distributive-+ a b c d = begin
  (a ℚ.+ b) ℚ.* (c ℚ.+ d)
    ≡⟨ ℚ.*-distribʳ-+ (c ℚ.+ d) a b ⟩
  (a ℚ.* (c ℚ.+ d)) ℚ.+ (b ℚ.* (c ℚ.+ d))
    ≡⟨ cong₂ ℚ._+_ (ℚ.*-distribˡ-+ a c d) (ℚ.*-distribˡ-+ b c d) ⟩
  ((a ℚ.* c) ℚ.+ (a ℚ.* d)) ℚ.+ ((b ℚ.* c) ℚ.+ (b ℚ.* d))
    ≡⟨ lemma-+-rearrange (a ℚ.* c) (a ℚ.* d) (b ℚ.* c) (b ℚ.* d) ⟩
  (a ℚ.* c) ℚ.+ (b ℚ.* c) ℚ.+ ((a ℚ.* d) ℚ.+ (b ℚ.* d))
    ≡⟨ cong (_ℚ.+ ((a ℚ.* d) ℚ.+ (b ℚ.* d))) (sym (ℚ.*-distribʳ-+ c a b)) ⟩
  ((a ℚ.+ b) ℚ.* c) ℚ.+ ((a ℚ.* d) ℚ.+ (b ℚ.* d))
    ≡⟨ cong (((a ℚ.+ b) ℚ.* c) ℚ.+_) (sym (ℚ.*-distribʳ-+ d a b)) ⟩
  ((a ℚ.+ b) ℚ.* c) ℚ.+ ((a ℚ.+ b) ℚ.* d)
    ≡⟨ sym (ℚ.*-distribʳ-+ (c ℚ.+ d) (a ℚ.+ b) (a ℚ.+ b)) ⟩
  ((a ℚ.+ b) ℚ.+ (a ℚ.+ b)) ℚ.* (c ℚ.+ d)
    ≡⟨ cong (_ℚ.* (c ℚ.+ d)) (sym (cong₂ ℚ._+_ refl refl)) ⟩
  (a ℚ.+ b) ℚ.* (c ℚ.+ d)
    ≡⟨ ℚ.*-distribʳ-+ (c ℚ.+ d) a b ⟩
  (a ℚ.* (c ℚ.+ d)) ℚ.+ (b ℚ.* (c ℚ.+ d))
    ≡⟨ cong₂ ℚ._+_ (ℚ.*-distribˡ-+ a c d) (ℚ.*-distribˡ-+ b c d) ⟩
  ((a ℚ.* c) ℚ.+ (a ℚ.* d)) ℚ.+ ((b ℚ.* c) ℚ.+ (b ℚ.* d))
    ≡⟨ ℚ.+-assoc (a ℚ.* c) (a ℚ.* d) ((b ℚ.* c) ℚ.+ (b ℚ.* d)) ⟩
  (a ℚ.* c) ℚ.+ ((a ℚ.* d) ℚ.+ ((b ℚ.* c) ℚ.+ (b ℚ.* d)))
    ≡⟨ cong ((a ℚ.* c) ℚ.+_) (sym (ℚ.+-assoc (a ℚ.* d) (b ℚ.* c) (b ℚ.* d))) ⟩
  (a ℚ.* c) ℚ.+ (((a ℚ.* d) ℚ.+ (b ℚ.* c)) ℚ.+ (b ℚ.* d))
    ≡⟨ sym (ℚ.+-assoc (a ℚ.* c) ((a ℚ.* d) ℚ.+ (b ℚ.* c)) (b ℚ.* d)) ⟩
  ((a ℚ.* c) ℚ.+ ((a ℚ.* d) ℚ.+ (b ℚ.* c))) ℚ.+ (b ℚ.* d)
    ≡⟨ cong (_ℚ.+ (b ℚ.* d)) (sym (ℚ.+-assoc (a ℚ.* c) (a ℚ.* d) (b ℚ.* c))) ⟩
  (((a ℚ.* c) ℚ.+ (a ℚ.* d)) ℚ.+ (b ℚ.* c)) ℚ.+ (b ℚ.* d)
    ≡⟨ ℚ.+-assoc ((a ℚ.* c) ℚ.+ (a ℚ.* d)) (b ℚ.* c) (b ℚ.* d) ⟩
  ((a ℚ.* c) ℚ.+ (a ℚ.* d)) ℚ.+ ((b ℚ.* c) ℚ.+ (b ℚ.* d))
    ≡⟨ ℚ.+-assoc (a ℚ.* c) (a ℚ.* d) ((b ℚ.* c) ℚ.+ (b ℚ.* d)) ⟩
  (a ℚ.* c) ℚ.+ ((a ℚ.* d) ℚ.+ ((b ℚ.* c) ℚ.+ (b ℚ.* d)))
    ≡⟨ cong ((a ℚ.* c) ℚ.+_) (ℚ.+-assoc (a ℚ.* d) (b ℚ.* c) (b ℚ.* d)) ⟩
  (a ℚ.* c) ℚ.+ (a ℚ.* d) ℚ.+ (b ℚ.* c) ℚ.+ (b ℚ.* d) ∎
