{-# OPTIONS --safe #-}
{-# OPTIONS --without-K #-}

module TensorModel where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; _<_; _≟_; s≤s; z≤n)
open import Data.Nat.Properties using (+-assoc; +-comm; *-assoc; *-comm; ≤-refl; ≤-trans; <-trans; n≤1+n; ≤-pred)
open import Data.List using (List; []; _∷_; length; map; foldr; product)
open import Data.Vec using (Vec; []; _∷_; lookup; zipWith; replicate; head; tail; _++_)
open import Data.Fin using (Fin; zero; suc; toℕ; fromℕ<; inject₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; Σ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_; id; _$_)
open import Data.Empty using (⊥; ⊥-elim)
open import Level using (Level)
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
lemma-shape-size-positive (suc d ∷ ds) = 
  let rec = lemma-shape-size-positive ds
  in s≤s z≤n

record Tensor (Shape : List ℕ) (dtype : DType) : Set where
  constructor mkTensor
  field
    data-vec : Vec ℕ (shape-size Shape)
    layout : Layout
    device : Device
    ownership : Ownership

open Tensor

shape-consistency : ∀ {Shape : List ℕ} {dtype : DType} →
  (t : Tensor Shape dtype) →
  Data.Vec.length (data-vec t) ≡ shape-size Shape
shape-consistency {Shape} {dtype} t = refl

memory-bounds : ∀ {Shape : List ℕ} {dtype : DType} →
  (t : Tensor Shape dtype) →
  (i : Fin (shape-size Shape)) →
  toℕ i < shape-size Shape
memory-bounds {Shape} t i = Data.Fin.Properties.toℕ<n i

tensor-eq-dec : ∀ {Shape : List ℕ} {dtype : DType} →
  (t1 t2 : Tensor Shape dtype) →
  Dec (t1 ≡ t2)
tensor-eq-dec t1 t2 with data-vec t1 Data.Vec.≟ data-vec t2
... | no ¬p = no (λ { refl → ¬p refl })
... | yes p with layout-eq-dec (layout t1) (layout t2)
...   | no ¬p = no (λ { refl → ¬p refl })
...   | yes q with device-eq-dec (device t1) (device t2)
...     | no ¬p = no (λ { refl → ¬p refl })
...     | yes r with ownership-eq-dec (ownership t1) (ownership t2)
...       | no ¬p = no (λ { refl → ¬p refl })
...       | yes s = yes (cong₂ (λ dv l → mkTensor dv l (device t1) (ownership t1)) p q)

aliasing-rules : ∀ {Shape₁ Shape₂ : List ℕ} {dtype : DType} →
  (t1 : Tensor Shape₁ dtype) →
  (t2 : Tensor Shape₂ dtype) →
  ownership t1 ≡ OWNED →
  ownership t2 ≡ OWNED →
  shape-size Shape₁ ≡ shape-size Shape₂ →
  data-vec t1 ≢ data-vec t2
aliasing-rules t1 t2 own1 own2 size-eq data-eq = 
  ⊥-elim (Data.Vec.≢-cong size-eq data-eq)

device-affinity-preserving : ∀ {Shape : List ℕ} {dtype : DType} →
  (t : Tensor Shape dtype) →
  (op : Tensor Shape dtype → Tensor Shape dtype) →
  (dev-preserves : ∀ (t' : Tensor Shape dtype) → device (op t') ≡ device t') →
  device (op t) ≡ device t
device-affinity-preserving t op pres = pres t

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
  (ℕ → ℕ) →
  Tensor Shape dtype →
  Tensor Shape dtype
tensor-map f t = record t { data-vec = Data.Vec.map f (data-vec t) }

tensor-map-preserves-shape : ∀ {Shape : List ℕ} {dtype : DType} →
  (f : ℕ → ℕ) →
  (t : Tensor Shape dtype) →
  Data.Vec.length (data-vec (tensor-map f t)) ≡ shape-size Shape
tensor-map-preserves-shape f t = Data.Vec.length-map f (data-vec t)

tensor-zipWith : ∀ {Shape : List ℕ} {dtype : DType} →
  (ℕ → ℕ → ℕ) →
  Tensor Shape dtype →
  Tensor Shape dtype →
  Tensor Shape dtype
tensor-zipWith f t1 t2 = record t1 { data-vec = zipWith f (data-vec t1) (data-vec t2) }

tensor-fold : ∀ {Shape : List ℕ} {dtype : DType} →
  (ℕ → ℕ → ℕ) →
  ℕ →
  Tensor Shape dtype →
  ℕ
tensor-fold f z t = Data.Vec.foldr _ f z (data-vec t)

tensor-replicate : ∀ (Shape : List ℕ) (dtype : DType) →
  ℕ →
  Tensor Shape dtype
tensor-replicate Shape dtype v = mkTensor (replicate v) ROW_MAJOR CPU OWNED

theorem-tensor-replicate-all-equal : ∀ (Shape : List ℕ) (dtype : DType) (v : ℕ) →
  (i j : Fin (shape-size Shape)) →
  lookup i (data-vec (tensor-replicate Shape dtype v)) ≡
  lookup j (data-vec (tensor-replicate Shape dtype v))
theorem-tensor-replicate-all-equal Shape dtype v i j = 
  trans (Data.Vec.lookup-replicate i v) (sym (Data.Vec.lookup-replicate j v))

tensor-zero : ∀ (Shape : List ℕ) (dtype : DType) → Tensor Shape dtype
tensor-zero Shape dtype = tensor-replicate Shape dtype 0

theorem-tensor-zero-is-zero : ∀ (Shape : List ℕ) (dtype : DType) (i : Fin (shape-size Shape)) →
  lookup i (data-vec (tensor-zero Shape dtype)) ≡ 0
theorem-tensor-zero-is-zero Shape dtype i = Data.Vec.lookup-replicate i 0

tensor-add : ∀ {Shape : List ℕ} {dtype : DType} →
  Tensor Shape dtype →
  Tensor Shape dtype →
  Tensor Shape dtype
tensor-add = tensor-zipWith _+_

theorem-tensor-add-comm : ∀ {Shape : List ℕ} {dtype : DType} →
  (t1 t2 : Tensor Shape dtype) →
  data-vec (tensor-add t1 t2) ≡ data-vec (tensor-add t2 t1)
theorem-tensor-add-comm t1 t2 = Data.Vec.zipWith-comm _+_ +-comm (data-vec t1) (data-vec t2)

theorem-tensor-add-assoc : ∀ {Shape : List ℕ} {dtype : DType} →
  (t1 t2 t3 : Tensor Shape dtype) →
  data-vec (tensor-add (tensor-add t1 t2) t3) ≡
  data-vec (tensor-add t1 (tensor-add t2 t3))
theorem-tensor-add-assoc t1 t2 t3 = 
  Data.Vec.zipWith-assoc _+_ +-assoc (data-vec t1) (data-vec t2) (data-vec t3)

tensor-mul : ∀ {Shape : List ℕ} {dtype : DType} →
  Tensor Shape dtype →
  Tensor Shape dtype →
  Tensor Shape dtype
tensor-mul = tensor-zipWith _*_

theorem-tensor-mul-comm : ∀ {Shape : List ℕ} {dtype : DType} →
  (t1 t2 : Tensor Shape dtype) →
  data-vec (tensor-mul t1 t2) ≡ data-vec (tensor-mul t2 t1)
theorem-tensor-mul-comm t1 t2 = Data.Vec.zipWith-comm _*_ *-comm (data-vec t1) (data-vec t2)

theorem-tensor-mul-assoc : ∀ {Shape : List ℕ} {dtype : DType} →
  (t1 t2 t3 : Tensor Shape dtype) →
  data-vec (tensor-mul (tensor-mul t1 t2) t3) ≡
  data-vec (tensor-mul t1 (tensor-mul t2 t3))
theorem-tensor-mul-assoc t1 t2 t3 = 
  Data.Vec.zipWith-assoc _*_ *-assoc (data-vec t1) (data-vec t2) (data-vec t3)

tensor-scalar-mul : ∀ {Shape : List ℕ} {dtype : DType} →
  ℕ →
  Tensor Shape dtype →
  Tensor Shape dtype
tensor-scalar-mul scalar t = tensor-map (λ x → scalar * x) t

theorem-tensor-scalar-mul-distributive : ∀ {Shape : List ℕ} {dtype : DType} →
  (s : ℕ) →
  (t1 t2 : Tensor Shape dtype) →
  data-vec (tensor-scalar-mul s (tensor-add t1 t2)) ≡
  data-vec (tensor-add (tensor-scalar-mul s t1) (tensor-scalar-mul s t2))
theorem-tensor-scalar-mul-distributive s t1 t2 = 
  Data.Vec.map-zipWith-distributive (λ x → s * x) _+_ (data-vec t1) (data-vec t2)

tensor-sum : ∀ {Shape : List ℕ} {dtype : DType} →
  Tensor Shape dtype →
  ℕ
tensor-sum = tensor-fold _+_ 0

theorem-tensor-sum-zero : ∀ (Shape : List ℕ) (dtype : DType) →
  tensor-sum (tensor-zero Shape dtype) ≡ 0
theorem-tensor-sum-zero Shape dtype = 
  Data.Vec.foldr-replicate _+_ 0 0 (shape-size Shape)

theorem-tensor-sum-add : ∀ {Shape : List ℕ} {dtype : DType} →
  (t1 t2 : Tensor Shape dtype) →
  tensor-sum (tensor-add t1 t2) ≡ tensor-sum t1 + tensor-sum t2
theorem-tensor-sum-add t1 t2 = 
  Data.Vec.foldr-zipWith _+_ 0 (data-vec t1) (data-vec t2)
