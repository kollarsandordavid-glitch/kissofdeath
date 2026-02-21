{-# OPTIONS --safe #-}
{-# OPTIONS --without-K #-}

module TensorVectorLemmas where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_)
open import Data.Nat.Properties
open import Data.Vec using (Vec; []; _∷_; lookup; zipWith; replicate; head; tail; map; foldr)
open import Data.Vec.Properties
open import Data.Fin using (Fin; zero; suc; toℕ; fromℕ<)
open import Data.Rational as ℚ using (ℚ; _+_; _*_; 0ℚ; 1ℚ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)
open ≡-Reasoning

lemma-vec-map-id : ∀ {n : ℕ} {A : Set} (v : Vec A n) → Data.Vec.map (λ x → x) v ≡ v
lemma-vec-map-id v = Data.Vec.Properties.map-id v

lemma-vec-map-compose : ∀ {n : ℕ} {A B C : Set} (f : B → C) (g : A → B) (v : Vec A n) →
  Data.Vec.map (f ∘ g) v ≡ Data.Vec.map f (Data.Vec.map g v)
  where
    _∘_ : {A B C : Set} → (B → C) → (A → B) → (A → C)
    (f ∘ g) x = f (g x)
lemma-vec-map-compose f g v = sym (Data.Vec.Properties.map-∘ f g v)

lemma-vec-lookup-replicate : ∀ {n : ℕ} {A : Set} (x : A) (i : Fin n) →
  Data.Vec.lookup i (Data.Vec.replicate x) ≡ x
lemma-vec-lookup-replicate x i = Data.Vec.Properties.lookup-replicate i x

lemma-vec-lookup-map : ∀ {n : ℕ} {A B : Set} (f : A → B) (v : Vec A n) (i : Fin n) →
  Data.Vec.lookup i (Data.Vec.map f v) ≡ f (Data.Vec.lookup i v)
lemma-vec-lookup-map f v i = Data.Vec.Properties.lookup-map i f v

lemma-vec-lookup-zipWith : ∀ {n : ℕ} {A B C : Set} (f : A → B → C) (v1 : Vec A n) (v2 : Vec B n) (i : Fin n) →
  Data.Vec.lookup i (Data.Vec.zipWith f v1 v2) ≡ f (Data.Vec.lookup i v1) (Data.Vec.lookup i v2)
lemma-vec-lookup-zipWith f v1 v2 i = Data.Vec.Properties.lookup-zipWith i f v1 v2

lemma-vec-zipWith-comm : ∀ {n : ℕ} (f : ℚ → ℚ → ℚ) (comm : ∀ x y → f x y ≡ f y x) (v1 v2 : Vec ℚ n) →
  Data.Vec.zipWith f v1 v2 ≡ Data.Vec.zipWith f v2 v1
lemma-vec-zipWith-comm f comm v1 v2 = Data.Vec.Properties.zipWith-comm f comm v1 v2

lemma-vec-zipWith-assoc : ∀ {n : ℕ} (f : ℚ → ℚ → ℚ)
  (assoc : ∀ x y z → f (f x y) z ≡ f x (f y z)) (v1 v2 v3 : Vec ℚ n) →
  Data.Vec.zipWith f (Data.Vec.zipWith f v1 v2) v3 ≡ Data.Vec.zipWith f v1 (Data.Vec.zipWith f v2 v3)
lemma-vec-zipWith-assoc f assoc v1 v2 v3 = Data.Vec.Properties.zipWith-assoc f assoc v1 v2 v3

lemma-vec-map-replicate : ∀ {n : ℕ} {A B : Set} (f : A → B) (x : A) →
  Data.Vec.map f (Data.Vec.replicate {n} x) ≡ Data.Vec.replicate (f x)
lemma-vec-map-replicate {n} f x = Data.Vec.Properties.map-replicate f x

lemma-vec-zipWith-replicate : ∀ {n : ℕ} (f : ℚ → ℚ → ℚ) (x y : ℚ) →
  Data.Vec.zipWith f (Data.Vec.replicate {n} x) (Data.Vec.replicate y) ≡ Data.Vec.replicate (f x y)
lemma-vec-zipWith-replicate {zero} f x y = refl
lemma-vec-zipWith-replicate {suc n} f x y = cong (f x y ∷_) (lemma-vec-zipWith-replicate f x y)

lemma-vec-map-zipWith-distrib : ∀ {n : ℕ} {A B C D : Set}
  (f : C → D) (g : A → B → C) (v1 : Vec A n) (v2 : Vec B n) →
  Data.Vec.map f (Data.Vec.zipWith g v1 v2) ≡ Data.Vec.zipWith (λ a b → f (g a b)) v1 v2
lemma-vec-map-zipWith-distrib f g [] [] = refl
lemma-vec-map-zipWith-distrib f g (x ∷ v1) (y ∷ v2) =
  cong (f (g x y) ∷_) (lemma-vec-map-zipWith-distrib f g v1 v2)

lemma-vec-foldr-replicate : ∀ {n : ℕ} (f : ℚ → ℚ → ℚ) (z x : ℚ)
  (left-id : ∀ y → f z y ≡ y) →
  Data.Vec.foldr _ f z (Data.Vec.replicate {n} x) ≡ foldr-helper n f z x
  where
    foldr-helper : ℕ → (ℚ → ℚ → ℚ) → ℚ → ℚ → ℚ
    foldr-helper zero f z x = z
    foldr-helper (suc n) f z x = f x (foldr-helper n f z x)
lemma-vec-foldr-replicate {zero} f z x left-id = refl
lemma-vec-foldr-replicate {suc n} f z x left-id = cong (f x) (lemma-vec-foldr-replicate f z x left-id)

lemma-vec-sum-replicate : ∀ {n : ℕ} (x : ℚ) →
  Data.Vec.foldr _ ℚ._+_ 0ℚ (Data.Vec.replicate {n} x) ≡ nat-to-rat n ℚ.* x
  where
    nat-to-rat : ℕ → ℚ
    nat-to-rat zero = 0ℚ
    nat-to-rat (suc n) = 1ℚ ℚ.+ nat-to-rat n
lemma-vec-sum-replicate {zero} x = refl
lemma-vec-sum-replicate {suc n} x = begin
  x ℚ.+ Data.Vec.foldr _ ℚ._+_ 0ℚ (Data.Vec.replicate x)
    ≡⟨ cong (x ℚ.+_) (lemma-vec-sum-replicate {n} x) ⟩
  x ℚ.+ (nat-to-rat n ℚ.* x)
    ≡⟨ sym (ℚ.*-distribʳ-+ x 1ℚ (nat-to-rat n)) ⟩
  (1ℚ ℚ.+ nat-to-rat n) ℚ.* x ∎
  where
    nat-to-rat : ℕ → ℚ
    nat-to-rat zero = 0ℚ
    nat-to-rat (suc n) = 1ℚ ℚ.+ nat-to-rat n

lemma-vec-sum-zipWith-add : ∀ {n : ℕ} (v1 v2 : Vec ℚ n) →
  Data.Vec.foldr _ ℚ._+_ 0ℚ (Data.Vec.zipWith ℚ._+_ v1 v2) ≡
  Data.Vec.foldr _ ℚ._+_ 0ℚ v1 ℚ.+ Data.Vec.foldr _ ℚ._+_ 0ℚ v2
lemma-vec-sum-zipWith-add [] [] = refl
lemma-vec-sum-zipWith-add (x ∷ v1) (y ∷ v2) = begin
  (x ℚ.+ y) ℚ.+ Data.Vec.foldr _ ℚ._+_ 0ℚ (Data.Vec.zipWith ℚ._+_ v1 v2)
    ≡⟨ cong ((x ℚ.+ y) ℚ.+_) (lemma-vec-sum-zipWith-add v1 v2) ⟩
  (x ℚ.+ y) ℚ.+ (Data.Vec.foldr _ ℚ._+_ 0ℚ v1 ℚ.+ Data.Vec.foldr _ ℚ._+_ 0ℚ v2)
    ≡⟨ ℚ.+-assoc (x ℚ.+ y) (Data.Vec.foldr _ ℚ._+_ 0ℚ v1) (Data.Vec.foldr _ ℚ._+_ 0ℚ v2) ⟩
  x ℚ.+ y ℚ.+ Data.Vec.foldr _ ℚ._+_ 0ℚ v1 ℚ.+ Data.Vec.foldr _ ℚ._+_ 0ℚ v2
    ≡⟨ cong (_ℚ.+ Data.Vec.foldr _ ℚ._+_ 0ℚ v2) (sym (ℚ.+-assoc x y (Data.Vec.foldr _ ℚ._+_ 0ℚ v1))) ⟩
  (x ℚ.+ (y ℚ.+ Data.Vec.foldr _ ℚ._+_ 0ℚ v1)) ℚ.+ Data.Vec.foldr _ ℚ._+_ 0ℚ v2
    ≡⟨ cong (λ w → (x ℚ.+ w) ℚ.+ Data.Vec.foldr _ ℚ._+_ 0ℚ v2) (ℚ.+-comm y (Data.Vec.foldr _ ℚ._+_ 0ℚ v1)) ⟩
  (x ℚ.+ (Data.Vec.foldr _ ℚ._+_ 0ℚ v1 ℚ.+ y)) ℚ.+ Data.Vec.foldr _ ℚ._+_ 0ℚ v2
    ≡⟨ cong (_ℚ.+ Data.Vec.foldr _ ℚ._+_ 0ℚ v2) (ℚ.+-assoc x (Data.Vec.foldr _ ℚ._+_ 0ℚ v1) y) ⟩
  (x ℚ.+ Data.Vec.foldr _ ℚ._+_ 0ℚ v1 ℚ.+ y) ℚ.+ Data.Vec.foldr _ ℚ._+_ 0ℚ v2
    ≡⟨ sym (ℚ.+-assoc (x ℚ.+ Data.Vec.foldr _ ℚ._+_ 0ℚ v1) y (Data.Vec.foldr _ ℚ._+_ 0ℚ v2)) ⟩
  x ℚ.+ Data.Vec.foldr _ ℚ._+_ 0ℚ v1 ℚ.+ (y ℚ.+ Data.Vec.foldr _ ℚ._+_ 0ℚ v2) ∎

lemma-vec-sum-map : ∀ {n : ℕ} (f : ℚ → ℚ) (v : Vec ℚ n)
  (distrib : ∀ x y → f (x ℚ.+ y) ≡ f x ℚ.+ f y) (zero-map : f 0ℚ ≡ 0ℚ) →
  Data.Vec.foldr _ ℚ._+_ 0ℚ (Data.Vec.map f v) ≡ f (Data.Vec.foldr _ ℚ._+_ 0ℚ v)
lemma-vec-sum-map f [] distrib zero-map = sym zero-map
lemma-vec-sum-map f (x ∷ v) distrib zero-map = begin
  f x ℚ.+ Data.Vec.foldr _ ℚ._+_ 0ℚ (Data.Vec.map f v)
    ≡⟨ cong (f x ℚ.+_) (lemma-vec-sum-map f v distrib zero-map) ⟩
  f x ℚ.+ f (Data.Vec.foldr _ ℚ._+_ 0ℚ v)
    ≡⟨ sym (distrib x (Data.Vec.foldr _ ℚ._+_ 0ℚ v)) ⟩
  f (x ℚ.+ Data.Vec.foldr _ ℚ._+_ 0ℚ v) ∎

lemma-vec-sum-scalar-mul : ∀ {n : ℕ} (k : ℚ) (v : Vec ℚ n) →
  Data.Vec.foldr _ ℚ._+_ 0ℚ (Data.Vec.map (k ℚ.*_) v) ≡ k ℚ.* Data.Vec.foldr _ ℚ._+_ 0ℚ v
lemma-vec-sum-scalar-mul k [] = sym (ℚ.*-zeroʳ k)
lemma-vec-sum-scalar-mul k (x ∷ v) = begin
  (k ℚ.* x) ℚ.+ Data.Vec.foldr _ ℚ._+_ 0ℚ (Data.Vec.map (k ℚ.*_) v)
    ≡⟨ cong ((k ℚ.* x) ℚ.+_) (lemma-vec-sum-scalar-mul k v) ⟩
  (k ℚ.* x) ℚ.+ (k ℚ.* Data.Vec.foldr _ ℚ._+_ 0ℚ v)
    ≡⟨ sym (ℚ.*-distribˡ-+ k x (Data.Vec.foldr _ ℚ._+_ 0ℚ v)) ⟩
  k ℚ.* (x ℚ.+ Data.Vec.foldr _ ℚ._+_ 0ℚ v) ∎

lemma-vec-prod-replicate : ∀ {n : ℕ} (x : ℚ) →
  Data.Vec.foldr _ ℚ._*_ 1ℚ (Data.Vec.replicate {n} x) ≡ power x n
  where
    power : ℚ → ℕ → ℚ
    power x zero = 1ℚ
    power x (suc n) = x ℚ.* power x n
lemma-vec-prod-replicate {zero} x = refl
lemma-vec-prod-replicate {suc n} x = cong (x ℚ.*_) (lemma-vec-prod-replicate {n} x)

lemma-vec-prod-zipWith-mul : ∀ {n : ℕ} (v1 v2 : Vec ℚ n) →
  Data.Vec.foldr _ ℚ._*_ 1ℚ (Data.Vec.zipWith ℚ._*_ v1 v2) ≡
  Data.Vec.foldr _ ℚ._*_ 1ℚ v1 ℚ.* Data.Vec.foldr _ ℚ._*_ 1ℚ v2
lemma-vec-prod-zipWith-mul [] [] = refl
lemma-vec-prod-zipWith-mul (x ∷ v1) (y ∷ v2) = begin
  (x ℚ.* y) ℚ.* Data.Vec.foldr _ ℚ._*_ 1ℚ (Data.Vec.zipWith ℚ._*_ v1 v2)
    ≡⟨ cong ((x ℚ.* y) ℚ.*_) (lemma-vec-prod-zipWith-mul v1 v2) ⟩
  (x ℚ.* y) ℚ.* (Data.Vec.foldr _ ℚ._*_ 1ℚ v1 ℚ.* Data.Vec.foldr _ ℚ._*_ 1ℚ v2)
    ≡⟨ ℚ.*-assoc (x ℚ.* y) (Data.Vec.foldr _ ℚ._*_ 1ℚ v1) (Data.Vec.foldr _ ℚ._*_ 1ℚ v2) ⟩
  x ℚ.* y ℚ.* Data.Vec.foldr _ ℚ._*_ 1ℚ v1 ℚ.* Data.Vec.foldr _ ℚ._*_ 1ℚ v2
    ≡⟨ cong (_ℚ.* Data.Vec.foldr _ ℚ._*_ 1ℚ v2) (sym (ℚ.*-assoc x y (Data.Vec.foldr _ ℚ._*_ 1ℚ v1))) ⟩
  (x ℚ.* (y ℚ.* Data.Vec.foldr _ ℚ._*_ 1ℚ v1)) ℚ.* Data.Vec.foldr _ ℚ._*_ 1ℚ v2
    ≡⟨ cong (λ w → (x ℚ.* w) ℚ.* Data.Vec.foldr _ ℚ._*_ 1ℚ v2) (ℚ.*-comm y (Data.Vec.foldr _ ℚ._*_ 1ℚ v1)) ⟩
  (x ℚ.* (Data.Vec.foldr _ ℚ._*_ 1ℚ v1 ℚ.* y)) ℚ.* Data.Vec.foldr _ ℚ._*_ 1ℚ v2
    ≡⟨ cong (_ℚ.* Data.Vec.foldr _ ℚ._*_ 1ℚ v2) (ℚ.*-assoc x (Data.Vec.foldr _ ℚ._*_ 1ℚ v1) y) ⟩
  (x ℚ.* Data.Vec.foldr _ ℚ._*_ 1ℚ v1 ℚ.* y) ℚ.* Data.Vec.foldr _ ℚ._*_ 1ℚ v2
    ≡⟨ sym (ℚ.*-assoc (x ℚ.* Data.Vec.foldr _ ℚ._*_ 1ℚ v1) y (Data.Vec.foldr _ ℚ._*_ 1ℚ v2)) ⟩
  x ℚ.* Data.Vec.foldr _ ℚ._*_ 1ℚ v1 ℚ.* (y ℚ.* Data.Vec.foldr _ ℚ._*_ 1ℚ v2) ∎

lemma-vec-all-elements-equal : ∀ {n : ℕ} (v : Vec ℚ n) (x : ℚ)
  (all-eq : ∀ (i : Fin n) → Data.Vec.lookup i v ≡ x) →
  v ≡ Data.Vec.replicate x
lemma-vec-all-elements-equal {zero} [] x all-eq = refl
lemma-vec-all-elements-equal {suc n} (y ∷ v) x all-eq =
  cong₂ _∷_ (all-eq zero) (lemma-vec-all-elements-equal v x (λ i → all-eq (suc i)))

lemma-vec-extensionality : ∀ {n : ℕ} (v1 v2 : Vec ℚ n)
  (lookup-eq : ∀ (i : Fin n) → Data.Vec.lookup i v1 ≡ Data.Vec.lookup i v2) →
  v1 ≡ v2
lemma-vec-extensionality {zero} [] [] lookup-eq = refl
lemma-vec-extensionality {suc n} (x ∷ v1) (y ∷ v2) lookup-eq =
  cong₂ _∷_ (lookup-eq zero) (lemma-vec-extensionality v1 v2 (λ i → lookup-eq (suc i)))

lemma-vec-zipWith-extensionality : ∀ {n : ℕ} {A B C : Set}
  (f g : A → B → C) (v1 : Vec A n) (v2 : Vec B n)
  (f-eq-g : ∀ a b → f a b ≡ g a b) →
  Data.Vec.zipWith f v1 v2 ≡ Data.Vec.zipWith g v1 v2
lemma-vec-zipWith-extensionality f g [] [] f-eq-g = refl
lemma-vec-zipWith-extensionality f g (x ∷ v1) (y ∷ v2) f-eq-g =
  cong₂ _∷_ (f-eq-g x y) (lemma-vec-zipWith-extensionality f g v1 v2 f-eq-g)

lemma-vec-head-map : ∀ {n : ℕ} {A B : Set} (f : A → B) (x : A) (v : Vec A n) →
  Data.Vec.head (Data.Vec.map f (x ∷ v)) ≡ f x
lemma-vec-head-map f x v = refl

lemma-vec-tail-map : ∀ {n : ℕ} {A B : Set} (f : A → B) (x : A) (v : Vec A n) →
  Data.Vec.tail (Data.Vec.map f (x ∷ v)) ≡ Data.Vec.map f v
lemma-vec-tail-map f x v = refl

lemma-vec-head-zipWith : ∀ {n : ℕ} {A B C : Set} (f : A → B → C) (x : A) (y : B) (v1 : Vec A n) (v2 : Vec B n) →
  Data.Vec.head (Data.Vec.zipWith f (x ∷ v1) (y ∷ v2)) ≡ f x y
lemma-vec-head-zipWith f x y v1 v2 = refl

lemma-vec-tail-zipWith : ∀ {n : ℕ} {A B C : Set} (f : A → B → C) (x : A) (y : B) (v1 : Vec A n) (v2 : Vec B n) →
  Data.Vec.tail (Data.Vec.zipWith f (x ∷ v1) (y ∷ v2)) ≡ Data.Vec.zipWith f v1 v2
lemma-vec-tail-zipWith f x y v1 v2 = refl

lemma-vec-map-++-distrib : ∀ {m n : ℕ} {A B : Set} (f : A → B) (v1 : Vec A m) (v2 : Vec A n) →
  Data.Vec.map f (v1 Data.Vec.++ v2) ≡ Data.Vec.map f v1 Data.Vec.++ Data.Vec.map f v2
lemma-vec-map-++-distrib f [] v2 = refl
lemma-vec-map-++-distrib f (x ∷ v1) v2 = cong (f x ∷_) (lemma-vec-map-++-distrib f v1 v2)

lemma-vec-lookup-++ : ∀ {m n : ℕ} {A : Set} (v1 : Vec A m) (v2 : Vec A n) (i : Fin m) →
  Data.Vec.lookup (inject₁ i) (v1 Data.Vec.++ v2) ≡ Data.Vec.lookup i v1
  where
    inject₁ : ∀ {n} → Fin n → Fin (suc n)
    inject₁ zero = zero
    inject₁ (suc i) = suc (inject₁ i)
lemma-vec-lookup-++ (x ∷ v1) v2 zero = refl
lemma-vec-lookup-++ (x ∷ v1) v2 (suc i) = lemma-vec-lookup-++ v1 v2 i

lemma-vec-sum-++ : ∀ {m n : ℕ} (v1 : Vec ℚ m) (v2 : Vec ℚ n) →
  Data.Vec.foldr _ ℚ._+_ 0ℚ (v1 Data.Vec.++ v2) ≡
  Data.Vec.foldr _ ℚ._+_ 0ℚ v1 ℚ.+ Data.Vec.foldr _ ℚ._+_ 0ℚ v2
lemma-vec-sum-++ [] v2 = refl
lemma-vec-sum-++ (x ∷ v1) v2 = begin
  x ℚ.+ Data.Vec.foldr _ ℚ._+_ 0ℚ (v1 Data.Vec.++ v2)
    ≡⟨ cong (x ℚ.+_) (lemma-vec-sum-++ v1 v2) ⟩
  x ℚ.+ (Data.Vec.foldr _ ℚ._+_ 0ℚ v1 ℚ.+ Data.Vec.foldr _ ℚ._+_ 0ℚ v2)
    ≡⟨ sym (ℚ.+-assoc x (Data.Vec.foldr _ ℚ._+_ 0ℚ v1) (Data.Vec.foldr _ ℚ._+_ 0ℚ v2)) ⟩
  (x ℚ.+ Data.Vec.foldr _ ℚ._+_ 0ℚ v1) ℚ.+ Data.Vec.foldr _ ℚ._+_ 0ℚ v2 ∎

lemma-vec-dot-product : ∀ {n : ℕ} (v1 v2 : Vec ℚ n) →
  Data.Vec.foldr _ ℚ._+_ 0ℚ (Data.Vec.zipWith ℚ._*_ v1 v2) ≡
  Data.Vec.foldr _ ℚ._+_ 0ℚ (Data.Vec.zipWith ℚ._*_ v2 v1)
lemma-vec-dot-product v1 v2 = begin
  Data.Vec.foldr _ ℚ._+_ 0ℚ (Data.Vec.zipWith ℚ._*_ v1 v2)
    ≡⟨ cong (Data.Vec.foldr _ ℚ._+_ 0ℚ) (lemma-vec-zipWith-extensionality ℚ._*_ (flip ℚ._*_) v1 v2 ℚ.*-comm) ⟩
  Data.Vec.foldr _ ℚ._+_ 0ℚ (Data.Vec.zipWith (flip ℚ._*_) v1 v2)
    ≡⟨ cong (Data.Vec.foldr _ ℚ._+_ 0ℚ) (sym (Data.Vec.Properties.zipWith-comm ℚ._*_ ℚ.*-comm v2 v1)) ⟩
  Data.Vec.foldr _ ℚ._+_ 0ℚ (Data.Vec.zipWith ℚ._*_ v2 v1) ∎
  where
    flip : {A B C : Set} → (A → B → C) → B → A → C
    flip f x y = f y x

lemma-vec-dot-product-replicate-left : ∀ {n : ℕ} (x : ℚ) (v : Vec ℚ n) →
  Data.Vec.foldr _ ℚ._+_ 0ℚ (Data.Vec.zipWith ℚ._*_ (Data.Vec.replicate x) v) ≡
  x ℚ.* Data.Vec.foldr _ ℚ._+_ 0ℚ v
lemma-vec-dot-product-replicate-left {zero} x [] = sym (ℚ.*-zeroʳ x)
lemma-vec-dot-product-replicate-left {suc n} x (y ∷ v) = begin
  (x ℚ.* y) ℚ.+ Data.Vec.foldr _ ℚ._+_ 0ℚ (Data.Vec.zipWith ℚ._*_ (Data.Vec.replicate x) v)
    ≡⟨ cong ((x ℚ.* y) ℚ.+_) (lemma-vec-dot-product-replicate-left x v) ⟩
  (x ℚ.* y) ℚ.+ (x ℚ.* Data.Vec.foldr _ ℚ._+_ 0ℚ v)
    ≡⟨ sym (ℚ.*-distribˡ-+ x y (Data.Vec.foldr _ ℚ._+_ 0ℚ v)) ⟩
  x ℚ.* (y ℚ.+ Data.Vec.foldr _ ℚ._+_ 0ℚ v) ∎

lemma-vec-dot-product-replicate-right : ∀ {n : ℕ} (v : Vec ℚ n) (x : ℚ) →
  Data.Vec.foldr _ ℚ._+_ 0ℚ (Data.Vec.zipWith ℚ._*_ v (Data.Vec.replicate x)) ≡
  Data.Vec.foldr _ ℚ._+_ 0ℚ v ℚ.* x
lemma-vec-dot-product-replicate-right v x = begin
  Data.Vec.foldr _ ℚ._+_ 0ℚ (Data.Vec.zipWith ℚ._*_ v (Data.Vec.replicate x))
    ≡⟨ lemma-vec-dot-product v (Data.Vec.replicate x) ⟩
  Data.Vec.foldr _ ℚ._+_ 0ℚ (Data.Vec.zipWith ℚ._*_ (Data.Vec.replicate x) v)
    ≡⟨ lemma-vec-dot-product-replicate-left x v ⟩
  x ℚ.* Data.Vec.foldr _ ℚ._+_ 0ℚ v
    ≡⟨ ℚ.*-comm x (Data.Vec.foldr _ ℚ._+_ 0ℚ v) ⟩
  Data.Vec.foldr _ ℚ._+_ 0ℚ v ℚ.* x ∎

lemma-vec-dot-product-zero-left : ∀ {n : ℕ} (v : Vec ℚ n) →
  Data.Vec.foldr _ ℚ._+_ 0ℚ (Data.Vec.zipWith ℚ._*_ (Data.Vec.replicate 0ℚ) v) ≡ 0ℚ
lemma-vec-dot-product-zero-left v = begin
  Data.Vec.foldr _ ℚ._+_ 0ℚ (Data.Vec.zipWith ℚ._*_ (Data.Vec.replicate 0ℚ) v)
    ≡⟨ lemma-vec-dot-product-replicate-left 0ℚ v ⟩
  0ℚ ℚ.* Data.Vec.foldr _ ℚ._+_ 0ℚ v
    ≡⟨ ℚ.*-zeroˡ (Data.Vec.foldr _ ℚ._+_ 0ℚ v) ⟩
  0ℚ ∎

lemma-vec-dot-product-zero-right : ∀ {n : ℕ} (v : Vec ℚ n) →
  Data.Vec.foldr _ ℚ._+_ 0ℚ (Data.Vec.zipWith ℚ._*_ v (Data.Vec.replicate 0ℚ)) ≡ 0ℚ
lemma-vec-dot-product-zero-right v = begin
  Data.Vec.foldr _ ℚ._+_ 0ℚ (Data.Vec.zipWith ℚ._*_ v (Data.Vec.replicate 0ℚ))
    ≡⟨ lemma-vec-dot-product v (Data.Vec.replicate 0ℚ) ⟩
  Data.Vec.foldr _ ℚ._+_ 0ℚ (Data.Vec.zipWith ℚ._*_ (Data.Vec.replicate 0ℚ) v)
    ≡⟨ lemma-vec-dot-product-zero-left v ⟩
  0ℚ ∎
