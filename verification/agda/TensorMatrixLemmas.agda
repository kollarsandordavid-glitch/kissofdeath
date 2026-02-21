{-# OPTIONS --safe #-}
{-# OPTIONS --without-K #-}

module TensorMatrixLemmas where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_)
open import Data.Nat.Properties
open import Data.Vec using (Vec; lookup; zipWith; replicate; map; foldr)
open import Data.Fin using (Fin; toℕ)
open import Data.Rational as ℚ using (ℚ; _+_; _*_; 0ℚ; 1ℚ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)
open ≡-Reasoning

Matrix : ℕ → ℕ → Set
Matrix m n = Vec (Vec ℚ n) m

Vector : ℕ → Set
Vector n = Vec ℚ n

mat-get : ∀ {m n} → Matrix m n → Fin m → Fin n → ℚ
mat-get mat i j = lookup j (lookup i mat)

vec-dot : ∀ {n} → Vector n → Vector n → ℚ
vec-dot v1 v2 = foldr _ ℚ._+_ 0ℚ (zipWith ℚ._*_ v1 v2)

lemma-dot-comm : ∀ {n} (v1 v2 : Vector n) →
  vec-dot v1 v2 ≡ vec-dot v2 v1
lemma-dot-comm {zero} [] [] = refl
lemma-dot-comm {suc n} (x ∷ v1) (y ∷ v2) = begin
  (x ℚ.* y) ℚ.+ vec-dot v1 v2
    ≡⟨ cong₂ ℚ._+_ (ℚ.*-comm x y) (lemma-dot-comm v1 v2) ⟩
  (y ℚ.* x) ℚ.+ vec-dot v2 v1 ∎

lemma-dot-zero-left : ∀ {n} (v : Vector n) →
  vec-dot (replicate 0ℚ) v ≡ 0ℚ
lemma-dot-zero-left {zero} [] = refl
lemma-dot-zero-left {suc n} (x ∷ v) = begin
  (0ℚ ℚ.* x) ℚ.+ vec-dot (replicate 0ℚ) v
    ≡⟨ cong₂ ℚ._+_ (ℚ.*-zeroˡ x) (lemma-dot-zero-left v) ⟩
  0ℚ ℚ.+ 0ℚ
    ≡⟨ ℚ.+-identityˡ 0ℚ ⟩
  0ℚ ∎

lemma-dot-zero-right : ∀ {n} (v : Vector n) →
  vec-dot v (replicate 0ℚ) ≡ 0ℚ
lemma-dot-zero-right v = trans (lemma-dot-comm v (replicate 0ℚ)) (lemma-dot-zero-left v)

lemma-dot-scalar-left : ∀ {n} (k : ℚ) (v1 v2 : Vector n) →
  vec-dot (map (k ℚ.*_) v1) v2 ≡ k ℚ.* vec-dot v1 v2
lemma-dot-scalar-left {zero} k [] [] = sym (ℚ.*-zeroʳ k)
lemma-dot-scalar-left {suc n} k (x ∷ v1) (y ∷ v2) = begin
  ((k ℚ.* x) ℚ.* y) ℚ.+ vec-dot (map (k ℚ.*_) v1) v2
    ≡⟨ cong₂ ℚ._+_ (ℚ.*-assoc k x y) (lemma-dot-scalar-left k v1 v2) ⟩
  (k ℚ.* (x ℚ.* y)) ℚ.+ (k ℚ.* vec-dot v1 v2)
    ≡⟨ sym (ℚ.*-distribˡ-+ k (x ℚ.* y) (vec-dot v1 v2)) ⟩
  k ℚ.* ((x ℚ.* y) ℚ.+ vec-dot v1 v2) ∎

lemma-dot-scalar-right : ∀ {n} (k : ℚ) (v1 v2 : Vector n) →
  vec-dot v1 (map (k ℚ.*_) v2) ≡ k ℚ.* vec-dot v1 v2
lemma-dot-scalar-right k v1 v2 = begin
  vec-dot v1 (map (k ℚ.*_) v2)
    ≡⟨ lemma-dot-comm v1 (map (k ℚ.*_) v2) ⟩
  vec-dot (map (k ℚ.*_) v2) v1
    ≡⟨ lemma-dot-scalar-left k v2 v1 ⟩
  k ℚ.* vec-dot v2 v1
    ≡⟨ cong (k ℚ.*_) (lemma-dot-comm v2 v1) ⟩
  k ℚ.* vec-dot v1 v2 ∎

lemma-dot-add-left : ∀ {n} (v1 v2 v3 : Vector n) →
  vec-dot (zipWith ℚ._+_ v1 v2) v3 ≡ vec-dot v1 v3 ℚ.+ vec-dot v2 v3
lemma-dot-add-left {zero} [] [] [] = refl
lemma-dot-add-left {suc n} (x ∷ v1) (y ∷ v2) (z ∷ v3) = begin
  ((x ℚ.+ y) ℚ.* z) ℚ.+ vec-dot (zipWith ℚ._+_ v1 v2) v3
    ≡⟨ cong₂ ℚ._+_ (ℚ.*-distribʳ-+ z x y) (lemma-dot-add-left v1 v2 v3) ⟩
  ((x ℚ.* z) ℚ.+ (y ℚ.* z)) ℚ.+ (vec-dot v1 v3 ℚ.+ vec-dot v2 v3)
    ≡⟨ ℚ.+-assoc (x ℚ.* z) (y ℚ.* z) (vec-dot v1 v3 ℚ.+ vec-dot v2 v3) ⟩
  (x ℚ.* z) ℚ.+ ((y ℚ.* z) ℚ.+ (vec-dot v1 v3 ℚ.+ vec-dot v2 v3))
    ≡⟨ cong ((x ℚ.* z) ℚ.+_) (sym (ℚ.+-assoc (y ℚ.* z) (vec-dot v1 v3) (vec-dot v2 v3))) ⟩
  (x ℚ.* z) ℚ.+ (((y ℚ.* z) ℚ.+ vec-dot v1 v3) ℚ.+ vec-dot v2 v3)
    ≡⟨ cong (λ w → (x ℚ.* z) ℚ.+ (w ℚ.+ vec-dot v2 v3)) (ℚ.+-comm (y ℚ.* z) (vec-dot v1 v3)) ⟩
  (x ℚ.* z) ℚ.+ ((vec-dot v1 v3 ℚ.+ (y ℚ.* z)) ℚ.+ vec-dot v2 v3)
    ≡⟨ cong ((x ℚ.* z) ℚ.+_) (ℚ.+-assoc (vec-dot v1 v3) (y ℚ.* z) (vec-dot v2 v3)) ⟩
  (x ℚ.* z) ℚ.+ (vec-dot v1 v3 ℚ.+ ((y ℚ.* z) ℚ.+ vec-dot v2 v3))
    ≡⟨ sym (ℚ.+-assoc (x ℚ.* z) (vec-dot v1 v3) ((y ℚ.* z) ℚ.+ vec-dot v2 v3)) ⟩
  ((x ℚ.* z) ℚ.+ vec-dot v1 v3) ℚ.+ ((y ℚ.* z) ℚ.+ vec-dot v2 v3) ∎

lemma-dot-add-right : ∀ {n} (v1 v2 v3 : Vector n) →
  vec-dot v1 (zipWith ℚ._+_ v2 v3) ≡ vec-dot v1 v2 ℚ.+ vec-dot v1 v3
lemma-dot-add-right v1 v2 v3 = begin
  vec-dot v1 (zipWith ℚ._+_ v2 v3)
    ≡⟨ lemma-dot-comm v1 (zipWith ℚ._+_ v2 v3) ⟩
  vec-dot (zipWith ℚ._+_ v2 v3) v1
    ≡⟨ lemma-dot-add-left v2 v3 v1 ⟩
  vec-dot v2 v1 ℚ.+ vec-dot v3 v1
    ≡⟨ cong₂ ℚ._+_ (lemma-dot-comm v2 v1) (lemma-dot-comm v3 v1) ⟩
  vec-dot v1 v2 ℚ.+ vec-dot v1 v3 ∎

mat-zero : ∀ {m n} → Matrix m n
mat-zero {m} {n} = replicate (replicate 0ℚ)

mat-identity : ∀ {n} → Matrix n n
mat-identity {zero} = []
mat-identity {suc n} = (1ℚ ∷ replicate 0ℚ) ∷ map (0ℚ ∷_) mat-identity

mat-add : ∀ {m n} → Matrix m n → Matrix m n → Matrix m n
mat-add = zipWith (zipWith ℚ._+_)

mat-scalar-mul : ∀ {m n} → ℚ → Matrix m n → Matrix m n
mat-scalar-mul k = map (map (k ℚ.*_))

lemma-mat-add-comm : ∀ {m n} (A B : Matrix m n) →
  mat-add A B ≡ mat-add B A
lemma-mat-add-comm {zero} [] [] = refl
lemma-mat-add-comm {suc m} (row1 ∷ A) (row2 ∷ B) =
  cong₂ _∷_ (zipWith-comm-helper row1 row2) (lemma-mat-add-comm A B)
  where
    zipWith-comm-helper : ∀ {n} (v1 v2 : Vec ℚ n) →
      zipWith ℚ._+_ v1 v2 ≡ zipWith ℚ._+_ v2 v1
    zipWith-comm-helper {zero} [] [] = refl
    zipWith-comm-helper {suc n} (x ∷ v1) (y ∷ v2) =
      cong₂ _∷_ (ℚ.+-comm x y) (zipWith-comm-helper v1 v2)

lemma-mat-add-assoc : ∀ {m n} (A B C : Matrix m n) →
  mat-add (mat-add A B) C ≡ mat-add A (mat-add B C)
lemma-mat-add-assoc {zero} [] [] [] = refl
lemma-mat-add-assoc {suc m} (row1 ∷ A) (row2 ∷ B) (row3 ∷ C) =
  cong₂ _∷_ (zipWith-assoc-helper row1 row2 row3) (lemma-mat-add-assoc A B C)
  where
    zipWith-assoc-helper : ∀ {n} (v1 v2 v3 : Vec ℚ n) →
      zipWith ℚ._+_ (zipWith ℚ._+_ v1 v2) v3 ≡ zipWith ℚ._+_ v1 (zipWith ℚ._+_ v2 v3)
    zipWith-assoc-helper {zero} [] [] [] = refl
    zipWith-assoc-helper {suc n} (x ∷ v1) (y ∷ v2) (z ∷ v3) =
      cong₂ _∷_ (ℚ.+-assoc x y z) (zipWith-assoc-helper v1 v2 v3)

lemma-mat-add-zero-left : ∀ {m n} (A : Matrix m n) →
  mat-add mat-zero A ≡ A
lemma-mat-add-zero-left {zero} [] = refl
lemma-mat-add-zero-left {suc m} (row ∷ A) =
  cong₂ _∷_ (zipWith-zero-left row) (lemma-mat-add-zero-left A)
  where
    zipWith-zero-left : ∀ {n} (v : Vec ℚ n) →
      zipWith ℚ._+_ (replicate 0ℚ) v ≡ v
    zipWith-zero-left {zero} [] = refl
    zipWith-zero-left {suc n} (x ∷ v) =
      cong₂ _∷_ (ℚ.+-identityˡ x) (zipWith-zero-left v)

lemma-mat-add-zero-right : ∀ {m n} (A : Matrix m n) →
  mat-add A mat-zero ≡ A
lemma-mat-add-zero-right A =
  trans (lemma-mat-add-comm A mat-zero) (lemma-mat-add-zero-left A)

lemma-mat-scalar-mul-zero : ∀ {m n} (A : Matrix m n) →
  mat-scalar-mul 0ℚ A ≡ mat-zero
lemma-mat-scalar-mul-zero {zero} [] = refl
lemma-mat-scalar-mul-zero {suc m} (row ∷ A) =
  cong₂ _∷_ (map-zero row) (lemma-mat-scalar-mul-zero A)
  where
    map-zero : ∀ {n} (v : Vec ℚ n) → map (0ℚ ℚ.*_) v ≡ replicate 0ℚ
    map-zero {zero} [] = refl
    map-zero {suc n} (x ∷ v) = cong₂ _∷_ (ℚ.*-zeroˡ x) (map-zero v)

lemma-mat-scalar-mul-one : ∀ {m n} (A : Matrix m n) →
  mat-scalar-mul 1ℚ A ≡ A
lemma-mat-scalar-mul-one {zero} [] = refl
lemma-mat-scalar-mul-one {suc m} (row ∷ A) =
  cong₂ _∷_ (map-one row) (lemma-mat-scalar-mul-one A)
  where
    map-one : ∀ {n} (v : Vec ℚ n) → map (1ℚ ℚ.*_) v ≡ v
    map-one {zero} [] = refl
    map-one {suc n} (x ∷ v) = cong₂ _∷_ (ℚ.*-identityˡ x) (map-one v)

lemma-mat-scalar-mul-assoc : ∀ {m n} (k1 k2 : ℚ) (A : Matrix m n) →
  mat-scalar-mul k1 (mat-scalar-mul k2 A) ≡ mat-scalar-mul (k1 ℚ.* k2) A
lemma-mat-scalar-mul-assoc {zero} k1 k2 [] = refl
lemma-mat-scalar-mul-assoc {suc m} k1 k2 (row ∷ A) =
  cong₂ _∷_ (map-assoc k1 k2 row) (lemma-mat-scalar-mul-assoc k1 k2 A)
  where
    map-assoc : ∀ {n} (k1 k2 : ℚ) (v : Vec ℚ n) →
      map (k1 ℚ.*_) (map (k2 ℚ.*_) v) ≡ map ((k1 ℚ.* k2) ℚ.*_) v
    map-assoc {zero} k1 k2 [] = refl
    map-assoc {suc n} k1 k2 (x ∷ v) =
      cong₂ _∷_ (ℚ.*-assoc k1 k2 x) (map-assoc k1 k2 v)

lemma-mat-scalar-mul-distrib-add : ∀ {m n} (k : ℚ) (A B : Matrix m n) →
  mat-scalar-mul k (mat-add A B) ≡ mat-add (mat-scalar-mul k A) (mat-scalar-mul k B)
lemma-mat-scalar-mul-distrib-add {zero} k [] [] = refl
lemma-mat-scalar-mul-distrib-add {suc m} k (row1 ∷ A) (row2 ∷ B) =
  cong₂ _∷_ (map-distrib k row1 row2) (lemma-mat-scalar-mul-distrib-add k A B)
  where
    map-distrib : ∀ {n} (k : ℚ) (v1 v2 : Vec ℚ n) →
      map (k ℚ.*_) (zipWith ℚ._+_ v1 v2) ≡ zipWith ℚ._+_ (map (k ℚ.*_) v1) (map (k ℚ.*_) v2)
    map-distrib {zero} k [] [] = refl
    map-distrib {suc n} k (x ∷ v1) (y ∷ v2) =
      cong₂ _∷_ (ℚ.*-distribˡ-+ k x y) (map-distrib k v1 v2)

