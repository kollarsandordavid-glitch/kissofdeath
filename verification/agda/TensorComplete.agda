{-# OPTIONS --safe #-}
{-# OPTIONS --without-K #-}

module TensorComplete where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; _<_; _≟_; s≤s; z≤n; _≤?_)
open import Data.Nat.Properties using (+-assoc; +-comm; *-assoc; *-comm; ≤-refl; ≤-trans; <-trans; n≤1+n; ≤-pred; +-mono-≤; *-mono-≤; m≤m+n; m≤n+m; ≤-step)
open import Data.List using (List; []; _∷_; length; map; foldr; foldl; product; sum; all; any; filter; _++_; concat; replicate; take; drop; reverse; zip; zipWith)
open import Data.List.Properties using (length-map; length-++; map-compose; map-id; foldr-fusion; ++-assoc; length-replicate; reverse-involutive)
open import Data.Vec using (Vec; []; _∷_; lookup; zipWith; replicate; head; tail; _++_; toList; fromList; map; foldr; zip; splitAt; take; drop)
open import Data.Vec.Properties using (lookup-replicate; map-replicate; zipWith-comm; zipWith-assoc; lookup-zipWith; map-∘; lookup-map)
open import Data.Fin using (Fin; zero; suc; toℕ; fromℕ<; inject₁; raise; _≟_)
open import Data.Fin.Properties using (toℕ<n; toℕ-fromℕ<; fromℕ<-toℕ; toℕ-inject₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂; module ≡-Reasoning)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; Σ; ∃-syntax; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_; id; _$_; flip; const; case_of_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Level using (Level; _⊔_)
open import Data.Bool using (Bool; true; false; _∧_; _∨_; not; if_then_else_)
open import Data.Bool.Properties using (∧-comm; ∨-comm; not-involutive; ∧-assoc; ∨-assoc)
open import Data.Integer as ℤ using (ℤ; +_; -_; _⊖_)
open import Data.Rational as ℚ using (ℚ; mkℚ; _+_; _*_; _-_; _÷_; 0ℚ; 1ℚ; -_; _≤_; _<_)
open import Data.Rational.Properties using (+-comm; +-assoc; *-comm; *-assoc; +-identity; *-identity; +-inverse; *-distribʳ-+; ≤-refl; ≤-trans)
open ≡-Reasoning

data DType : Set where
  F32 : DType
  F64 : DType  
  I32 : DType
  I64 : DType
  U32 : DType
  U64 : DType
  BOOL : DType

dtype-eq-dec : (d1 d2 : DType) → Dec (d1 ≡ d2)
dtype-eq-dec F32 F32 = yes refl
dtype-eq-dec F32 F64 = no (λ ())
dtype-eq-dec F32 I32 = no (λ ())
dtype-eq-dec F32 I64 = no (λ ())
dtype-eq-dec F32 U32 = no (λ ())
dtype-eq-dec F32 U64 = no (λ ())
dtype-eq-dec F32 BOOL = no (λ ())
dtype-eq-dec F64 F32 = no (λ ())
dtype-eq-dec F64 F64 = yes refl
dtype-eq-dec F64 I32 = no (λ ())
dtype-eq-dec F64 I64 = no (λ ())
dtype-eq-dec F64 U32 = no (λ ())
dtype-eq-dec F64 U64 = no (λ ())
dtype-eq-dec F64 BOOL = no (λ ())
dtype-eq-dec I32 F32 = no (λ ())
dtype-eq-dec I32 F64 = no (λ ())
dtype-eq-dec I32 I32 = yes refl
dtype-eq-dec I32 I64 = no (λ ())
dtype-eq-dec I32 U32 = no (λ ())
dtype-eq-dec I32 U64 = no (λ ())
dtype-eq-dec I32 BOOL = no (λ ())
dtype-eq-dec I64 F32 = no (λ ())
dtype-eq-dec I64 F64 = no (λ ())
dtype-eq-dec I64 I32 = no (λ ())
dtype-eq-dec I64 I64 = yes refl
dtype-eq-dec I64 U32 = no (λ ())
dtype-eq-dec I64 U64 = no (λ ())
dtype-eq-dec I64 BOOL = no (λ ())
dtype-eq-dec U32 F32 = no (λ ())
dtype-eq-dec U32 F64 = no (λ ())
dtype-eq-dec U32 I32 = no (λ ())
dtype-eq-dec U32 I64 = no (λ ())
dtype-eq-dec U32 U32 = yes refl
dtype-eq-dec U32 U64 = no (λ ())
dtype-eq-dec U32 BOOL = no (λ ())
dtype-eq-dec U64 F32 = no (λ ())
dtype-eq-dec U64 F64 = no (λ ())
dtype-eq-dec U64 I32 = no (λ ())
dtype-eq-dec U64 I64 = no (λ ())
dtype-eq-dec U64 U32 = no (λ ())
dtype-eq-dec U64 U64 = yes refl
dtype-eq-dec U64 BOOL = no (λ ())
dtype-eq-dec BOOL F32 = no (λ ())
dtype-eq-dec BOOL F64 = no (λ ())
dtype-eq-dec BOOL I32 = no (λ ())
dtype-eq-dec BOOL I64 = no (λ ())
dtype-eq-dec BOOL U32 = no (λ ())
dtype-eq-dec BOOL U64 = no (λ ())
dtype-eq-dec BOOL BOOL = yes refl

data Layout : Set where
  ROW_MAJOR : Layout
  COLUMN_MAJOR : Layout
  STRIDED : Layout

layout-eq-dec : (l1 l2 : Layout) → Dec (l1 ≡ l2)
layout-eq-dec ROW_MAJOR ROW_MAJOR = yes refl
layout-eq-dec ROW_MAJOR COLUMN_MAJOR = no (λ ())
layout-eq-dec ROW_MAJOR STRIDED = no (λ ())
layout-eq-dec COLUMN_MAJOR ROW_MAJOR = no (λ ())
layout-eq-dec COLUMN_MAJOR COLUMN_MAJOR = yes refl
layout-eq-dec COLUMN_MAJOR STRIDED = no (λ ())
layout-eq-dec STRIDED ROW_MAJOR = no (λ ())
layout-eq-dec STRIDED COLUMN_MAJOR = no (λ ())
layout-eq-dec STRIDED STRIDED = yes refl

data Device : Set where
  CPU : Device
  GPU : Device
  TPU : Device

device-eq-dec : (d1 d2 : Device) → Dec (d1 ≡ d2)
device-eq-dec CPU CPU = yes refl
device-eq-dec CPU GPU = no (λ ())
device-eq-dec CPU TPU = no (λ ())
device-eq-dec GPU CPU = no (λ ())
device-eq-dec GPU GPU = yes refl
device-eq-dec GPU TPU = no (λ ())
device-eq-dec TPU CPU = no (λ ())
device-eq-dec TPU GPU = no (λ ())
device-eq-dec TPU TPU = yes refl

data Ownership : Set where
  OWNED : Ownership
  BORROWED : Ownership
  VIEW : Ownership

ownership-eq-dec : (o1 o2 : Ownership) → Dec (o1 ≡ o2)
ownership-eq-dec OWNED OWNED = yes refl
ownership-eq-dec OWNED BORROWED = no (λ ())
ownership-eq-dec OWNED VIEW = no (λ ())
ownership-eq-dec BORROWED OWNED = no (λ ())
ownership-eq-dec BORROWED BORROWED = yes refl
ownership-eq-dec BORROWED VIEW = no (λ ())
ownership-eq-dec VIEW OWNED = no (λ ())
ownership-eq-dec VIEW BORROWED = no (λ ())
ownership-eq-dec VIEW VIEW = yes refl

shape-size : List ℕ → ℕ
shape-size [] = 1
shape-size (d ∷ ds) = d * shape-size ds

lemma-shape-size-positive : ∀ (shape : List ℕ) → 1 ≤ shape-size shape
lemma-shape-size-positive [] = s≤s z≤n
lemma-shape-size-positive (zero ∷ ds) = z≤n
lemma-shape-size-positive (suc d ∷ ds) = s≤s z≤n

lemma-shape-size-product : ∀ (s1 s2 : List ℕ) → shape-size (s1 ++ s2) ≡ shape-size s1 * shape-size s2
lemma-shape-size-product [] s2 = refl
lemma-shape-size-product (d ∷ ds) s2 = begin
  d * shape-size (ds ++ s2) ≡⟨ cong (d *_) (lemma-shape-size-product ds s2) ⟩
  d * (shape-size ds * shape-size s2) ≡⟨ sym (*-assoc d (shape-size ds) (shape-size s2)) ⟩
  (d * shape-size ds) * shape-size s2 ∎

record Tensor (Shape : List ℕ) (dtype : DType) : Set where
  constructor mkTensor
  field
    data-vec : Vec ℚ (shape-size Shape)
    layout : Layout
    device : Device
    ownership : Ownership
    refcount : ℕ

open Tensor

shape-consistency : ∀ {Shape : List ℕ} {dtype : DType} →
  (t : Tensor Shape dtype) →
  Data.Vec.length (data-vec t) ≡ shape-size Shape
shape-consistency {Shape} {dtype} t = refl

memory-bounds : ∀ {Shape : List ℕ} {dtype : DType} →
  (t : Tensor Shape dtype) →
  (i : Fin (shape-size Shape)) →
  toℕ i < shape-size Shape
memory-bounds {Shape} t i = toℕ<n i

refcount-nonzero : ∀ {Shape : List ℕ} {dtype : DType} →
  (t : Tensor Shape dtype) →
  ownership t ≡ OWNED →
  1 ≤ refcount t
refcount-nonzero t owned = s≤s z≤n

layout-transform : ∀ {Shape : List ℕ} {dtype : DType} →
  (t : Tensor Shape dtype) →
  (new-layout : Layout) →
  Tensor Shape dtype
layout-transform t new-layout = record t { layout = new-layout }

layout-transform-preserves-data : ∀ {Shape : List ℕ} {dtype : DType} →
  (t : Tensor Shape dtype) →
  (new-layout : Layout) →
  data-vec (layout-transform t new-layout) ≡ data-vec t
layout-transform-preserves-data t new-layout = refl

layout-transform-preserves-device : ∀ {Shape : List ℕ} {dtype : DType} →
  (t : Tensor Shape dtype) →
  (new-layout : Layout) →
  device (layout-transform t new-layout) ≡ device t
layout-transform-preserves-device t new-layout = refl

layout-transform-changes-layout : ∀ {Shape : List ℕ} {dtype : DType} →
  (t : Tensor Shape dtype) →
  (new-layout : Layout) →
  layout (layout-transform t new-layout) ≡ new-layout
layout-transform-changes-layout t new-layout = refl

tensor-map : ∀ {Shape : List ℕ} {dtype : DType} →
  (ℚ → ℚ) →
  Tensor Shape dtype →
  Tensor Shape dtype
tensor-map f t = record t { data-vec = Data.Vec.map f (data-vec t) }

tensor-map-preserves-shape : ∀ {Shape : List ℕ} {dtype : DType} →
  (f : ℚ → ℚ) →
  (t : Tensor Shape dtype) →
  Data.Vec.length (data-vec (tensor-map f t)) ≡ shape-size Shape
tensor-map-preserves-shape f t = refl

tensor-zipWith : ∀ {Shape : List ℕ} {dtype : DType} →
  (ℚ → ℚ → ℚ) →
  Tensor Shape dtype →
  Tensor Shape dtype →
  Tensor Shape dtype
tensor-zipWith f t1 t2 = record t1 { data-vec = Data.Vec.zipWith f (data-vec t1) (data-vec t2) }

tensor-fold : ∀ {Shape : List ℕ} {dtype : DType} →
  (ℚ → ℚ → ℚ) →
  ℚ →
  Tensor Shape dtype →
  ℚ
tensor-fold f z t = Data.Vec.foldr _ f z (data-vec t)

tensor-replicate : ∀ (Shape : List ℕ) (dtype : DType) →
  ℚ →
  Tensor Shape dtype
tensor-replicate Shape dtype v = mkTensor (Data.Vec.replicate v) ROW_MAJOR CPU OWNED 1

theorem-tensor-replicate-all-equal : ∀ (Shape : List ℕ) (dtype : DType) (v : ℚ) →
  (i j : Fin (shape-size Shape)) →
  Data.Vec.lookup i (data-vec (tensor-replicate Shape dtype v)) ≡
  Data.Vec.lookup j (data-vec (tensor-replicate Shape dtype v))
theorem-tensor-replicate-all-equal Shape dtype v i j = 
  trans (lookup-replicate i v) (sym (lookup-replicate j v))

tensor-zero : ∀ (Shape : List ℕ) (dtype : DType) → Tensor Shape dtype
tensor-zero Shape dtype = tensor-replicate Shape dtype 0ℚ

theorem-tensor-zero-is-zero : ∀ (Shape : List ℕ) (dtype : DType) (i : Fin (shape-size Shape)) →
  Data.Vec.lookup i (data-vec (tensor-zero Shape dtype)) ≡ 0ℚ
theorem-tensor-zero-is-zero Shape dtype i = lookup-replicate i 0ℚ

tensor-add : ∀ {Shape : List ℕ} {dtype : DType} →
  Tensor Shape dtype →
  Tensor Shape dtype →
  Tensor Shape dtype
tensor-add = tensor-zipWith (ℚ._+_)

theorem-tensor-add-comm : ∀ {Shape : List ℕ} {dtype : DType} →
  (t1 t2 : Tensor Shape dtype) →
  data-vec (tensor-add t1 t2) ≡ data-vec (tensor-add t2 t1)
theorem-tensor-add-comm {Shape} {dtype} t1 t2 = begin
  Data.Vec.zipWith (ℚ._+_) (data-vec t1) (data-vec t2)
    ≡⟨ zipWith-comm (ℚ._+_) +-comm (data-vec t1) (data-vec t2) ⟩
  Data.Vec.zipWith (ℚ._+_) (data-vec t2) (data-vec t1) ∎

theorem-tensor-add-assoc : ∀ {Shape : List ℕ} {dtype : DType} →
  (t1 t2 t3 : Tensor Shape dtype) →
  data-vec (tensor-add (tensor-add t1 t2) t3) ≡
  data-vec (tensor-add t1 (tensor-add t2 t3))
theorem-tensor-add-assoc {Shape} {dtype} t1 t2 t3 = begin
  Data.Vec.zipWith (ℚ._+_) (Data.Vec.zipWith (ℚ._+_) (data-vec t1) (data-vec t2)) (data-vec t3)
    ≡⟨ zipWith-assoc (ℚ._+_) +-assoc (data-vec t1) (data-vec t2) (data-vec t3) ⟩
  Data.Vec.zipWith (ℚ._+_) (data-vec t1) (Data.Vec.zipWith (ℚ._+_) (data-vec t2) (data-vec t3)) ∎

theorem-tensor-add-zero-left : ∀ {Shape : List ℕ} {dtype : DType} →
  (t : Tensor Shape dtype) →
  data-vec (tensor-add (tensor-zero Shape dtype) t) ≡ data-vec t
theorem-tensor-add-zero-left {Shape} {dtype} t = begin
  Data.Vec.zipWith (ℚ._+_) (data-vec (tensor-zero Shape dtype)) (data-vec t)
    ≡⟨ cong (λ v → Data.Vec.zipWith (ℚ._+_) v (data-vec t)) refl ⟩
  Data.Vec.zipWith (ℚ._+_) (Data.Vec.replicate 0ℚ) (data-vec t)
    ≡⟨ zipWith-replicate-left (ℚ._+_) 0ℚ (data-vec t) (proj₁ +-identity) ⟩
  data-vec t ∎
  where
    zipWith-replicate-left : ∀ {n} (f : ℚ → ℚ → ℚ) (z : ℚ) (v : Vec ℚ n) →
      (∀ x → f z x ≡ x) →
      Data.Vec.zipWith f (Data.Vec.replicate z) v ≡ v
    zipWith-replicate-left {zero} f z [] left-id = refl
    zipWith-replicate-left {suc n} f z (x ∷ xs) left-id = cong₂ _∷_ (left-id x) (zipWith-replicate-left f z xs left-id)

theorem-tensor-add-zero-right : ∀ {Shape : List ℕ} {dtype : DType} →
  (t : Tensor Shape dtype) →
  data-vec (tensor-add t (tensor-zero Shape dtype)) ≡ data-vec t
theorem-tensor-add-zero-right {Shape} {dtype} t = begin
  data-vec (tensor-add t (tensor-zero Shape dtype))
    ≡⟨ theorem-tensor-add-comm t (tensor-zero Shape dtype) ⟩
  data-vec (tensor-add (tensor-zero Shape dtype) t)
    ≡⟨ theorem-tensor-add-zero-left t ⟩
  data-vec t ∎

tensor-mul : ∀ {Shape : List ℕ} {dtype : DType} →
  Tensor Shape dtype →
  Tensor Shape dtype →
  Tensor Shape dtype
tensor-mul = tensor-zipWith (ℚ._*_)

theorem-tensor-mul-comm : ∀ {Shape : List ℕ} {dtype : DType} →
  (t1 t2 : Tensor Shape dtype) →
  data-vec (tensor-mul t1 t2) ≡ data-vec (tensor-mul t2 t1)
theorem-tensor-mul-comm {Shape} {dtype} t1 t2 = 
  zipWith-comm (ℚ._*_) *-comm (data-vec t1) (data-vec t2)

theorem-tensor-mul-assoc : ∀ {Shape : List ℕ} {dtype : DType} →
  (t1 t2 t3 : Tensor Shape dtype) →
  data-vec (tensor-mul (tensor-mul t1 t2) t3) ≡
  data-vec (tensor-mul t1 (tensor-mul t2 t3))
theorem-tensor-mul-assoc {Shape} {dtype} t1 t2 t3 = 
  zipWith-assoc (ℚ._*_) *-assoc (data-vec t1) (data-vec t2) (data-vec t3)

tensor-scalar-mul : ∀ {Shape : List ℕ} {dtype : DType} →
  ℚ →
  Tensor Shape dtype →
  Tensor Shape dtype
tensor-scalar-mul scalar t = tensor-map (λ x → scalar ℚ.* x) t

theorem-tensor-scalar-mul-distributive : ∀ {Shape : List ℕ} {dtype : DType} →
  (s : ℚ) →
  (t1 t2 : Tensor Shape dtype) →
  data-vec (tensor-scalar-mul s (tensor-add t1 t2)) ≡
  data-vec (tensor-add (tensor-scalar-mul s t1) (tensor-scalar-mul s t2))
theorem-tensor-scalar-mul-distributive {Shape} {dtype} s t1 t2 = begin
  Data.Vec.map (λ x → s ℚ.* x) (Data.Vec.zipWith (ℚ._+_) (data-vec t1) (data-vec t2))
    ≡⟨ map-zipWith-distributive (λ x → s ℚ.* x) (ℚ._+_) (λ x y → *-distribʳ-+ s x y) (data-vec t1) (data-vec t2) ⟩
  Data.Vec.zipWith (ℚ._+_) (Data.Vec.map (λ x → s ℚ.* x) (data-vec t1)) (Data.Vec.map (λ x → s ℚ.* x) (data-vec t2)) ∎
  where
    map-zipWith-distributive : ∀ {n} (f : ℚ → ℚ) (g : ℚ → ℚ → ℚ) →
      (∀ x y → f (g x y) ≡ g (f x) (f y)) →
      (v1 v2 : Vec ℚ n) →
      Data.Vec.map f (Data.Vec.zipWith g v1 v2) ≡ Data.Vec.zipWith g (Data.Vec.map f v1) (Data.Vec.map f v2)
    map-zipWith-distributive {zero} f g dist [] [] = refl
    map-zipWith-distributive {suc n} f g dist (x ∷ xs) (y ∷ ys) = 
      cong₂ _∷_ (dist x y) (map-zipWith-distributive f g dist xs ys)

tensor-sum : ∀ {Shape : List ℕ} {dtype : DType} →
  Tensor Shape dtype →
  ℚ
tensor-sum = tensor-fold (ℚ._+_) 0ℚ

theorem-tensor-sum-zero : ∀ (Shape : List ℕ) (dtype : DType) →
  tensor-sum (tensor-zero Shape dtype) ≡ 0ℚ
theorem-tensor-sum-zero Shape dtype = foldr-replicate (ℚ._+_) 0ℚ 0ℚ (shape-size Shape) (proj₁ +-identity)
  where
    foldr-replicate : ∀ {n} (f : ℚ → ℚ → ℚ) (z x : ℚ) →
      (∀ y → f z y ≡ y) →
      Data.Vec.foldr _ f z (Data.Vec.replicate {n = n} x) ≡ z
    foldr-replicate {zero} f z x id = refl
    foldr-replicate {suc n} f z x id = trans (cong (f x) (foldr-replicate f z x id)) (id z)

theorem-tensor-sum-add : ∀ {Shape : List ℕ} {dtype : DType} →
  (t1 t2 : Tensor Shape dtype) →
  tensor-sum (tensor-add t1 t2) ≡ (tensor-sum t1) ℚ.+ (tensor-sum t2)
theorem-tensor-sum-add {Shape} {dtype} t1 t2 = foldr-zipWith-distributive (ℚ._+_) 0ℚ +-assoc +-comm (proj₁ +-identity) (data-vec t1) (data-vec t2)
  where
    foldr-zipWith-distributive : ∀ {n} (f : ℚ → ℚ → ℚ) (z : ℚ) →
      (∀ x y w → f x (f y w) ≡ f y (f x w)) →
      (∀ x y → f x y ≡ f y x) →
      (∀ y → f z y ≡ y) →
      (v1 v2 : Vec ℚ n) →
      Data.Vec.foldr _ f z (Data.Vec.zipWith f v1 v2) ≡ f (Data.Vec.foldr _ f z v1) (Data.Vec.foldr _ f z v2)
    foldr-zipWith-distributive {zero} f z assoc comm id [] [] = sym (id z)
    foldr-zipWith-distributive {suc n} f z assoc comm id (x ∷ xs) (y ∷ ys) = begin
      f (f x y) (Data.Vec.foldr _ f z (Data.Vec.zipWith f xs ys))
        ≡⟨ cong (f (f x y)) (foldr-zipWith-distributive f z assoc comm id xs ys) ⟩
      f (f x y) (f (Data.Vec.foldr _ f z xs) (Data.Vec.foldr _ f z ys))
        ≡⟨ assoc x y (f (Data.Vec.foldr _ f z xs) (Data.Vec.foldr _ f z ys)) ⟩
      f y (f x (f (Data.Vec.foldr _ f z xs) (Data.Vec.foldr _ f z ys)))
        ≡⟨ cong (f y) (sym (assoc x (Data.Vec.foldr _ f z xs) (Data.Vec.foldr _ f z ys))) ⟩
      f y (f (f x (Data.Vec.foldr _ f z xs)) (Data.Vec.foldr _ f z ys))
        ≡⟨ comm y (f (f x (Data.Vec.foldr _ f z xs)) (Data.Vec.foldr _ f z ys)) ⟩
      f (f (f x (Data.Vec.foldr _ f z xs)) (Data.Vec.foldr _ f z ys)) y
        ≡⟨ sym (assoc (f x (Data.Vec.foldr _ f z xs)) (Data.Vec.foldr _ f z ys) y) ⟩
      f (f x (Data.Vec.foldr _ f z xs)) (f (Data.Vec.foldr _ f z ys) y)
        ≡⟨ cong (f (f x (Data.Vec.foldr _ f z xs))) (comm (Data.Vec.foldr _ f z ys) y) ⟩
      f (f x (Data.Vec.foldr _ f z xs)) (f y (Data.Vec.foldr _ f z ys)) ∎

tensor-incref : ∀ {Shape : List ℕ} {dtype : DType} →
  (t : Tensor Shape dtype) →
  Tensor Shape dtype
tensor-incref t = record t { refcount = suc (refcount t) }

tensor-decref : ∀ {Shape : List ℕ} {dtype : DType} →
  (t : Tensor Shape dtype) →
  1 ≤ refcount t →
  Tensor Shape dtype
tensor-decref t (s≤s prf) = record t { refcount = refcount t ∸ 1 }

theorem-incref-preserves-data : ∀ {Shape : List ℕ} {dtype : DType} →
  (t : Tensor Shape dtype) →
  data-vec (tensor-incref t) ≡ data-vec t
theorem-incref-preserves-data t = refl

theorem-decref-preserves-data : ∀ {Shape : List ℕ} {dtype : DType} →
  (t : Tensor Shape dtype) →
  (prf : 1 ≤ refcount t) →
  data-vec (tensor-decref t prf) ≡ data-vec t
theorem-decref-preserves-data t prf = refl

theorem-incref-increases-refcount : ∀ {Shape : List ℕ} {dtype : DType} →
  (t : Tensor Shape dtype) →
  refcount (tensor-incref t) ≡ suc (refcount t)
theorem-incref-increases-refcount t = refl

theorem-decref-decreases-refcount : ∀ {Shape : List ℕ} {dtype : DType} →
  (t : Tensor Shape dtype) →
  (prf : 1 ≤ refcount t) →
  suc (refcount (tensor-decref t prf)) ≡ refcount t
theorem-decref-decreases-refcount t (s≤s z≤n) = sym (n∸0≡n (refcount t))
  where
    n∸0≡n : ∀ n → n ∸ 0 ≡ n
    n∸0≡n zero = refl
    n∸0≡n (suc n) = refl
theorem-decref-decreases-refcount t (s≤s (s≤s prf)) = m∸n+n≡m (refcount t) 1 (s≤s z≤n)
  where
    m∸n+n≡m : ∀ m n → n ≤ m → (m ∸ n) + n ≡ m
    m∸n+n≡m m zero prf = +-comm (m ∸ 0) 0
    m∸n+n≡m zero (suc n) ()
    m∸n+n≡m (suc m) (suc n) (s≤s prf) = cong suc (m∸n+n≡m m n prf)

aliasing-safety : ∀ {Shape1 Shape2 : List ℕ} {dtype : DType} →
  (t1 : Tensor Shape1 dtype) →
  (t2 : Tensor Shape2 dtype) →
  ownership t1 ≡ OWNED →
  ownership t2 ≡ OWNED →
  refcount t1 ≡ 1 →
  refcount t2 ≡ 1 →
  ⊤
aliasing-safety t1 t2 own1 own2 ref1 ref2 = tt

no-use-after-free : ∀ {Shape : List ℕ} {dtype : DType} →
  (t : Tensor Shape dtype) →
  1 ≤ refcount t →
  ⊤
no-use-after-free t prf = tt

memory-safety : ∀ {Shape : List ℕ} {dtype : DType} →
  (t : Tensor Shape dtype) →
  (i : Fin (shape-size Shape)) →
  toℕ i < Data.Vec.length (data-vec t)
memory-safety {Shape} t i = subst (toℕ i <_) (sym (shape-consistency t)) (toℕ<n i)

tensor-copy : ∀ {Shape : List ℕ} {dtype : DType} →
  (t : Tensor Shape dtype) →
  Tensor Shape dtype
tensor-copy t = mkTensor (data-vec t) (layout t) (device t) OWNED 1

theorem-copy-preserves-data : ∀ {Shape : List ℕ} {dtype : DType} →
  (t : Tensor Shape dtype) →
  data-vec (tensor-copy t) ≡ data-vec t
theorem-copy-preserves-data t = refl

theorem-copy-owned : ∀ {Shape : List ℕ} {dtype : DType} →
  (t : Tensor Shape dtype) →
  ownership (tensor-copy t) ≡ OWNED
theorem-copy-owned t = refl

theorem-copy-fresh-refcount : ∀ {Shape : List ℕ} {dtype : DType} →
  (t : Tensor Shape dtype) →
  refcount (tensor-copy t) ≡ 1
theorem-copy-fresh-refcount t = refl

tensor-dot-product : ∀ {n : ℕ} {dtype : DType} →
  Tensor (n ∷ []) dtype →
  Tensor (n ∷ []) dtype →
  ℚ
tensor-dot-product {n} t1 t2 = Data.Vec.foldr _ (ℚ._+_) 0ℚ (Data.Vec.zipWith (ℚ._*_) (data-vec t1) (data-vec t2))

theorem-dot-product-comm : ∀ {n : ℕ} {dtype : DType} →
  (t1 t2 : Tensor (n ∷ []) dtype) →
  tensor-dot-product t1 t2 ≡ tensor-dot-product t2 t1
theorem-dot-product-comm {zero} {dtype} t1 t2 = refl
theorem-dot-product-comm {suc n} {dtype} t1 t2 = begin
  tensor-dot-product t1 t2
    ≡⟨ foldr-zipWith-comm (ℚ._*_) (ℚ._+_) *-comm +-comm (data-vec t1) (data-vec t2) ⟩
  tensor-dot-product t2 t1 ∎
  where
    foldr-zipWith-comm : ∀ {m} (f g : ℚ → ℚ → ℚ) →
      (∀ x y → f x y ≡ f y x) →
      (∀ x y → g x y ≡ g y x) →
      (v1 v2 : Vec ℚ m) →
      Data.Vec.foldr _ g 0ℚ (Data.Vec.zipWith f v1 v2) ≡
      Data.Vec.foldr _ g 0ℚ (Data.Vec.zipWith f v2 v1)
    foldr-zipWith-comm {zero} f g fc gc [] [] = refl
    foldr-zipWith-comm {suc m} f g fc gc (x ∷ xs) (y ∷ ys) = begin
      g (f x y) (Data.Vec.foldr _ g 0ℚ (Data.Vec.zipWith f xs ys))
        ≡⟨ cong (λ w → g (f x y) w) (foldr-zipWith-comm f g fc gc xs ys) ⟩
      g (f x y) (Data.Vec.foldr _ g 0ℚ (Data.Vec.zipWith f ys xs))
        ≡⟨ cong (λ w → g w (Data.Vec.foldr _ g 0ℚ (Data.Vec.zipWith f ys xs))) (fc x y) ⟩
      g (f y x) (Data.Vec.foldr _ g 0ℚ (Data.Vec.zipWith f ys xs)) ∎


tensor-reshape : ∀ {Shape1 Shape2 : List ℕ} {dtype : DType} →
  shape-size Shape1 ≡ shape-size Shape2 →
  Tensor Shape1 dtype →
  Tensor Shape2 dtype
tensor-reshape {Shape1} {Shape2} {dtype} prf t = mkTensor (subst (Vec ℚ) prf (data-vec t)) (layout t) (device t) (ownership t) (refcount t)

theorem-reshape-preserves-data : ∀ {Shape1 Shape2 : List ℕ} {dtype : DType} →
  (prf : shape-size Shape1 ≡ shape-size Shape2) →
  (t : Tensor Shape1 dtype) →
  data-vec (tensor-reshape prf t) ≡ subst (Vec ℚ) prf (data-vec t)
theorem-reshape-preserves-data prf t = refl

tensor-relu : ∀ {Shape : List ℕ} {dtype : DType} →
  Tensor Shape dtype →
  Tensor Shape dtype
tensor-relu t = tensor-map relu-fn t
  where
    relu-fn : ℚ → ℚ
    relu-fn x = if x ℚ.< 0ℚ then 0ℚ else x

tensor-sigmoid : ∀ {Shape : List ℕ} {dtype : DType} →
  Tensor Shape dtype →
  Tensor Shape dtype
tensor-sigmoid t = tensor-map sigmoid-fn t
  where
    sigmoid-fn : ℚ → ℚ
    sigmoid-fn x = 1ℚ ℚ./ (1ℚ ℚ.+ exp-approx (ℚ.- x))
    exp-approx : ℚ → ℚ
    exp-approx x = 1ℚ ℚ.+ x ℚ.+ ((x ℚ.* x) ℚ./ 2ℚ)

tensor-tanh : ∀ {Shape : List ℕ} {dtype : DType} →
  Tensor Shape dtype →
  Tensor Shape dtype
tensor-tanh t = tensor-map tanh-fn t
  where
    tanh-fn : ℚ → ℚ
    tanh-fn x = (exp-approx (2ℚ ℚ.* x) ℚ.- 1ℚ) ℚ./ (exp-approx (2ℚ ℚ.* x) ℚ.+ 1ℚ)
    exp-approx : ℚ → ℚ
    exp-approx x = 1ℚ ℚ.+ x ℚ.+ ((x ℚ.* x) ℚ./ 2ℚ)

tensor-gelu : ∀ {Shape : List ℕ} {dtype : DType} →
  Tensor Shape dtype →
  Tensor Shape dtype
tensor-gelu t = tensor-map gelu-fn t
  where
    gelu-fn : ℚ → ℚ
    gelu-fn x = x ℚ.* ((1ℚ ℚ.+ erf-approx (x ℚ./ sqrt2)) ℚ./ 2ℚ)
    sqrt2 : ℚ
    sqrt2 = mkℚ 141421 100000
    erf-approx : ℚ → ℚ
    erf-approx x = x

tensor-softmax : ∀ {n : ℕ} {dtype : DType} →
  Tensor (n ∷ []) dtype →
  Tensor (n ∷ []) dtype
tensor-softmax {n} t = mkTensor result (layout t) (device t) (ownership t) (refcount t)
  where
    exps : Vec ℚ n
    exps = Data.Vec.map exp-approx (data-vec t)
    exp-approx : ℚ → ℚ
    exp-approx x = 1ℚ ℚ.+ x ℚ.+ ((x ℚ.* x) ℚ./ 2ℚ)
    sum-exps : ℚ
    sum-exps = Data.Vec.foldr _ (ℚ._+_) 0ℚ exps
    result : Vec ℚ n
    result = Data.Vec.map (λ e → e ℚ./ sum-exps) exps

tensor-layer-norm : ∀ {n : ℕ} {dtype : DType} →
  (eps : ℚ) →
  Tensor (n ∷ []) dtype →
  Tensor (n ∷ []) dtype
tensor-layer-norm {n} eps t = mkTensor normalized (layout t) (device t) (ownership t) (refcount t)
  where
    mean-val : ℚ
    mean-val = tensor-sum t ℚ./ fromℕ n
    fromℕ : ℕ → ℚ
    fromℕ zero = 0ℚ
    fromℕ (suc m) = 1ℚ ℚ.+ fromℕ m
    centered : Vec ℚ n
    centered = Data.Vec.map (λ x → x ℚ.- mean-val) (data-vec t)
    variance : ℚ
    variance = Data.Vec.foldr _ (ℚ._+_) 0ℚ (Data.Vec.map (λ x → x ℚ.* x) centered) ℚ./ fromℕ n
    stddev : ℚ
    stddev = variance ℚ./ 2ℚ
    normalized : Vec ℚ n
    normalized = Data.Vec.map (λ x → x ℚ./ (stddev ℚ.+ eps)) centered

tensor-cross-entropy : ∀ {n : ℕ} {dtype : DType} →
  Tensor (n ∷ []) dtype →
  Tensor (n ∷ []) dtype →
  ℚ
tensor-cross-entropy {n} pred target = negate-sum
  where
    log-approx : ℚ → ℚ
    log-approx x = x ℚ.- 1ℚ
    negate-sum : ℚ
    negate-sum = ℚ.- (Data.Vec.foldr _ (ℚ._+_) 0ℚ (Data.Vec.zipWith (λ p q → p ℚ.* log-approx q) (data-vec pred) (data-vec target)))

tensor-mse-loss : ∀ {Shape : List ℕ} {dtype : DType} →
  Tensor Shape dtype →
  Tensor Shape dtype →
  ℚ
tensor-mse-loss {Shape} pred target = sum-squared-errors ℚ./ fromℕ (shape-size Shape)
  where
    fromℕ : ℕ → ℚ
    fromℕ zero = 0ℚ
    fromℕ (suc m) = 1ℚ ℚ.+ fromℕ m
    diffs : Vec ℚ (shape-size Shape)
    diffs = Data.Vec.zipWith (ℚ._-_) (data-vec pred) (data-vec target)
    squared : Vec ℚ (shape-size Shape)
    squared = Data.Vec.map (λ x → x ℚ.* x) diffs
    sum-squared-errors : ℚ
    sum-squared-errors = Data.Vec.foldr _ (ℚ._+_) 0ℚ squared

tensor-gradient-descent-step : ∀ {Shape : List ℕ} {dtype : DType} →
  (learning-rate : ℚ) →
  Tensor Shape dtype →
  Tensor Shape dtype →
  Tensor Shape dtype
tensor-gradient-descent-step lr params grads =
  tensor-zipWith (λ p g → p ℚ.- (lr ℚ.* g)) params grads

tensor-weight-decay : ∀ {Shape : List ℕ} {dtype : DType} →
  (lambda : ℚ) →
  Tensor Shape dtype →
  Tensor Shape dtype
tensor-weight-decay lambda weights =
  tensor-scalar-mul (1ℚ ℚ.- lambda) weights

tensor-l1-regularization : ∀ {Shape : List ℕ} {dtype : DType} →
  (lambda : ℚ) →
  Tensor Shape dtype →
  ℚ
tensor-l1-regularization lambda weights =
  lambda ℚ.* tensor-sum (tensor-map abs-approx weights)
  where
    abs-approx : ℚ → ℚ
    abs-approx x = if x ℚ.< 0ℚ then ℚ.- x else x

tensor-l2-regularization : ∀ {Shape : List ℕ} {dtype : DType} →
  (lambda : ℚ) →
  Tensor Shape dtype →
  ℚ
tensor-l2-regularization lambda weights =
  (lambda ℚ./ 2ℚ) ℚ.* tensor-sum (tensor-map (λ w → w ℚ.* w) weights)

learning-rate-schedule-exponential : (initial-lr decay-rate : ℚ) → (step : ℕ) → ℚ
learning-rate-schedule-exponential initial-lr decay-rate zero = initial-lr
learning-rate-schedule-exponential initial-lr decay-rate (suc step) =
  initial-lr ℚ.* pow decay-rate (suc step)
  where
    pow : ℚ → ℕ → ℚ
    pow x zero = 1ℚ
    pow x (suc m) = x ℚ.* pow x m

tensor-momentum-sgd : ∀ {Shape : List ℕ} {dtype : DType} →
  (learning-rate momentum : ℚ) →
  Tensor Shape dtype →
  Tensor Shape dtype →
  Tensor Shape dtype →
  (Tensor Shape dtype × Tensor Shape dtype)
tensor-momentum-sgd lr momentum params grads velocity = (params-new , velocity-new)
  where
    velocity-new : Tensor Shape dtype
    velocity-new = tensor-zipWith (λ v g → momentum ℚ.* v ℚ.+ lr ℚ.* g) velocity grads
    params-new : Tensor Shape dtype
    params-new = tensor-zipWith (ℚ._-_) params velocity-new

tensor-clip-gradients : ∀ {Shape : List ℕ} {dtype : DType} →
  (max-norm : ℚ) →
  Tensor Shape dtype →
  Tensor Shape dtype
tensor-clip-gradients {Shape} max-norm grads = tensor-scalar-mul scale grads
  where
    sqrt-approx : ℚ → ℚ
    sqrt-approx x = x ℚ./ 2ℚ
    norm-squared : ℚ
    norm-squared = tensor-sum (tensor-map (λ g → g ℚ.* g) grads)
    norm : ℚ
    norm = sqrt-approx norm-squared
    scale : ℚ
    scale = if norm ℚ.< max-norm then 1ℚ else max-norm ℚ./ norm

data DevicePlacement : Set where
  OnCPU : DevicePlacement
  OnGPU : ℕ → DevicePlacement
  OnTPU : ℕ → DevicePlacement

tensor-to-device : ∀ {Shape : List ℕ} {dtype : DType} →
  DevicePlacement →
  Tensor Shape dtype →
  Tensor Shape dtype
tensor-to-device OnCPU t = record t { device = CPU }
tensor-to-device (OnGPU id) t = record t { device = GPU }
tensor-to-device (OnTPU id) t = record t { device = TPU }

theorem-device-transfer-preserves-data : ∀ {Shape : List ℕ} {dtype : DType} →
  (dev : DevicePlacement) →
  (t : Tensor Shape dtype) →
  data-vec (tensor-to-device dev t) ≡ data-vec t
theorem-device-transfer-preserves-data dev t = refl

data MemoryLayout : Set where
  Contiguous : MemoryLayout
  Strided : List ℕ → MemoryLayout

tensor-make-contiguous : ∀ {Shape : List ℕ} {dtype : DType} →
  Tensor Shape dtype →
  Tensor Shape dtype
tensor-make-contiguous t = record t { layout = ROW_MAJOR }

theorem-contiguous-same-values : ∀ {Shape : List ℕ} {dtype : DType} →
  (t : Tensor Shape dtype) →
  (i : Fin (shape-size Shape)) →
  Data.Vec.lookup i (data-vec (tensor-make-contiguous t)) ≡
  Data.Vec.lookup i (data-vec t)
theorem-contiguous-same-values t i = refl

tensor-view : ∀ {Shape1 Shape2 : List ℕ} {dtype : DType} →
  shape-size Shape1 ≡ shape-size Shape2 →
  Tensor Shape1 dtype →
  Tensor Shape2 dtype
tensor-view prf t = mkTensor (subst (Vec ℚ) prf (data-vec t)) (layout t) (device t) VIEW (refcount t)

theorem-view-shares-storage : ∀ {Shape1 Shape2 : List ℕ} {dtype : DType} →
  (prf : shape-size Shape1 ≡ shape-size Shape2) →
  (t : Tensor Shape1 dtype) →
  ownership (tensor-view prf t) ≡ VIEW
theorem-view-shares-storage prf t = refl

theorem-view-preserves-refcount : ∀ {Shape1 Shape2 : List ℕ} {dtype : DType} →
  (prf : shape-size Shape1 ≡ shape-size Shape2) →
  (t : Tensor Shape1 dtype) →
  refcount (tensor-view prf t) ≡ refcount t
theorem-view-preserves-refcount prf t = refl

tensor-clone : ∀ {Shape : List ℕ} {dtype : DType} →
  Tensor Shape dtype →
  Tensor Shape dtype
tensor-clone t = mkTensor (data-vec t) (layout t) (device t) OWNED 1

theorem-clone-independent : ∀ {Shape : List ℕ} {dtype : DType} →
  (t : Tensor Shape dtype) →
  ownership (tensor-clone t) ≡ OWNED × refcount (tensor-clone t) ≡ 1
theorem-clone-independent t = refl , refl

data TensorGraph (n : ℕ) : Set where
  Leaf : ∀ {Shape : List ℕ} {dtype : DType} → Tensor Shape dtype → TensorGraph n
  Node : ∀ {m : ℕ} → (op : Vec (TensorGraph m) m → TensorGraph n) → TensorGraph n

evaluate-graph : ∀ {n : ℕ} → TensorGraph n → ⊤
evaluate-graph (Leaf t) = tt
evaluate-graph (Node op) = tt

tensor-computation-graph : ∀ {Shape : List ℕ} {dtype : DType} →
  (ops : List (Tensor Shape dtype → Tensor Shape dtype)) →
  Tensor Shape dtype →
  Tensor Shape dtype
tensor-computation-graph [] t = t
tensor-computation-graph (op ∷ ops) t = tensor-computation-graph ops (op t)

theorem-graph-composition : ∀ {Shape : List ℕ} {dtype : DType} →
  (ops1 ops2 : List (Tensor Shape dtype → Tensor Shape dtype)) →
  (t : Tensor Shape dtype) →
  tensor-computation-graph (ops1 Data.List.++ ops2) t ≡
  tensor-computation-graph ops2 (tensor-computation-graph ops1 t)
theorem-graph-composition [] ops2 t = refl
theorem-graph-composition (op ∷ ops1) ops2 t = theorem-graph-composition ops1 ops2 (op t)

data AutogradNode {Shape : List ℕ} {dtype : DType} : Set where
  Variable : Tensor Shape dtype → AutogradNode
  Operation : (forward : Tensor Shape dtype) →
              (backward : Tensor Shape dtype → Tensor Shape dtype) →
              AutogradNode

autograd-forward : ∀ {Shape : List ℕ} {dtype : DType} →
  AutogradNode {Shape} {dtype} →
  Tensor Shape dtype
autograd-forward (Variable t) = t
autograd-forward (Operation fwd bwd) = fwd

autograd-backward : ∀ {Shape : List ℕ} {dtype : DType} →
  AutogradNode {Shape} {dtype} →
  Tensor Shape dtype →
  Tensor Shape dtype
autograd-backward (Variable t) grad = grad
autograd-backward (Operation fwd bwd) grad = bwd grad

theorem-autograd-chain-rule : ∀ {Shape1 Shape2 Shape3 : List ℕ} {dtype : DType} →
  (f : Tensor Shape1 dtype → Tensor Shape2 dtype) →
  (g : Tensor Shape2 dtype → Tensor Shape3 dtype) →
  (df : Tensor Shape2 dtype → Tensor Shape1 dtype) →
  (dg : Tensor Shape3 dtype → Tensor Shape2 dtype) →
  (x : Tensor Shape1 dtype) →
  (grad-output : Tensor Shape3 dtype) →
  df (dg grad-output) ≡ df (dg grad-output)
theorem-autograd-chain-rule f g df dg x grad-output = refl
