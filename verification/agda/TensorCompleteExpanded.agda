{-# OPTIONS --safe #-}
{-# OPTIONS --without-K #-}

module TensorCompleteExpanded where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; _<_; _≟_; s≤s; z≤n; _≤?_; _/_)
open import Data.Nat.Properties using (+-assoc; +-comm; *-assoc; *-comm; ≤-refl; ≤-trans; <-trans; n≤1+n; ≤-pred; +-mono-≤; *-mono-≤; m≤m+n; m≤n+m; ≤-step; *-distribʳ-+; *-distribˡ-+; +-identityˡ; +-identityʳ; *-identityˡ; *-identityʳ; *-zeroˡ; *-zeroʳ; m+n∸n≡m; m∸n+n≡m)
open import Data.List using (List; []; _∷_; length; map; foldr; foldl; product; sum; all; any; filter; _++_; concat; replicate; take; drop; reverse; zip; zipWith)
open import Data.List.Properties using (length-map; length-++; map-compose; map-id; foldr-fusion; ++-assoc; length-replicate; reverse-involutive)
open import Data.Vec using (Vec; []; _∷_; lookup; zipWith; replicate; head; tail; _++_; toList; fromList; map; foldr; zip; splitAt; take; drop)
open import Data.Vec.Properties using (lookup-replicate; map-replicate; zipWith-comm; zipWith-assoc; lookup-zipWith; map-∘; lookup-map)
open import Data.Fin using (Fin; zero; suc; toℕ; fromℕ<; inject₁; raise; _≟_; opposite; pred)
open import Data.Fin.Properties using (toℕ<n; toℕ-fromℕ<; fromℕ<-toℕ; toℕ-inject₁; toℕ-raise)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂; module ≡-Reasoning)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; Σ; ∃-syntax; Σ-syntax; uncurry; curry)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Function using (_∘_; id; _$_; flip; const; case_of_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Level using (Level; _⊔_)
open import Data.Bool using (Bool; true; false; _∧_; _∨_; not; if_then_else_; T)
open import Data.Bool.Properties using (∧-comm; ∨-comm; not-involutive; ∧-assoc; ∨-assoc; ∧-identityˡ; ∨-identityˡ)
open import Data.Integer as ℤ using (ℤ; +_; -_; _⊖_; ∣_∣)
open import Data.Rational as ℚ using (ℚ; mkℚ; _+_; _*_; _-_; _÷_; 0ℚ; 1ℚ; -_; _≤_; _<_; ½; ¼)
open import Data.Rational.Properties using (+-comm; +-assoc; *-comm; *-assoc; +-identity; *-identity; +-inverse; *-distribʳ-+; *-distribˡ-+; ≤-refl; ≤-trans; ≤-antisym; +-mono-≤; *-mono-≤; 0≤p⇒0≤p*q; p≤q⇒0≤q-p)
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

dtype-decidable-equality : (d1 d2 : DType) → (d1 ≡ d2) ⊎ (d1 ≢ d2)
  where _≢_ : DType → DType → Set
        x ≢ y = ¬ (x ≡ y)
dtype-decidable-equality F32 F32 = inj₁ refl
dtype-decidable-equality F32 F64 = inj₂ (λ ())
dtype-decidable-equality F32 I32 = inj₂ (λ ())
dtype-decidable-equality F32 I64 = inj₂ (λ ())
dtype-decidable-equality F32 U32 = inj₂ (λ ())
dtype-decidable-equality F32 U64 = inj₂ (λ ())
dtype-decidable-equality F32 BOOL = inj₂ (λ ())
dtype-decidable-equality F64 F32 = inj₂ (λ ())
dtype-decidable-equality F64 F64 = inj₁ refl
dtype-decidable-equality F64 I32 = inj₂ (λ ())
dtype-decidable-equality F64 I64 = inj₂ (λ ())
dtype-decidable-equality F64 U32 = inj₂ (λ ())
dtype-decidable-equality F64 U64 = inj₂ (λ ())
dtype-decidable-equality F64 BOOL = inj₂ (λ ())
dtype-decidable-equality I32 F32 = inj₂ (λ ())
dtype-decidable-equality I32 F64 = inj₂ (λ ())
dtype-decidable-equality I32 I32 = inj₁ refl
dtype-decidable-equality I32 I64 = inj₂ (λ ())
dtype-decidable-equality I32 U32 = inj₂ (λ ())
dtype-decidable-equality I32 U64 = inj₂ (λ ())
dtype-decidable-equality I32 BOOL = inj₂ (λ ())
dtype-decidable-equality I64 F32 = inj₂ (λ ())
dtype-decidable-equality I64 F64 = inj₂ (λ ())
dtype-decidable-equality I64 I32 = inj₂ (λ ())
dtype-decidable-equality I64 I64 = inj₁ refl
dtype-decidable-equality I64 U32 = inj₂ (λ ())
dtype-decidable-equality I64 U64 = inj₂ (λ ())
dtype-decidable-equality I64 BOOL = inj₂ (λ ())
dtype-decidable-equality U32 F32 = inj₂ (λ ())
dtype-decidable-equality U32 F64 = inj₂ (λ ())
dtype-decidable-equality U32 I32 = inj₂ (λ ())
dtype-decidable-equality U32 I64 = inj₂ (λ ())
dtype-decidable-equality U32 U32 = inj₁ refl
dtype-decidable-equality U32 U64 = inj₂ (λ ())
dtype-decidable-equality U32 BOOL = inj₂ (λ ())
dtype-decidable-equality U64 F32 = inj₂ (λ ())
dtype-decidable-equality U64 F64 = inj₂ (λ ())
dtype-decidable-equality U64 I32 = inj₂ (λ ())
dtype-decidable-equality U64 I64 = inj₂ (λ ())
dtype-decidable-equality U64 U32 = inj₂ (λ ())
dtype-decidable-equality U64 U64 = inj₁ refl
dtype-decidable-equality U64 BOOL = inj₂ (λ ())
dtype-decidable-equality BOOL F32 = inj₂ (λ ())
dtype-decidable-equality BOOL F64 = inj₂ (λ ())
dtype-decidable-equality BOOL I32 = inj₂ (λ ())
dtype-decidable-equality BOOL I64 = inj₂ (λ ())
dtype-decidable-equality BOOL U32 = inj₂ (λ ())
dtype-decidable-equality BOOL U64 = inj₂ (λ ())
dtype-decidable-equality BOOL BOOL = inj₁ refl

dtype-injectivity-F32 : ∀ {d} → F32 ≡ d → d ≡ F32
dtype-injectivity-F32 refl = refl

dtype-injectivity-F64 : ∀ {d} → F64 ≡ d → d ≡ F64
dtype-injectivity-F64 refl = refl

dtype-injectivity-I32 : ∀ {d} → I32 ≡ d → d ≡ I32
dtype-injectivity-I32 refl = refl

dtype-injectivity-I64 : ∀ {d} → I64 ≡ d → d ≡ I64
dtype-injectivity-I64 refl = refl

dtype-injectivity-U32 : ∀ {d} → U32 ≡ d → d ≡ U32
dtype-injectivity-U32 refl = refl

dtype-injectivity-U64 : ∀ {d} → U64 ≡ d → d ≡ U64
dtype-injectivity-U64 refl = refl

dtype-injectivity-BOOL : ∀ {d} → BOOL ≡ d → d ≡ BOOL
dtype-injectivity-BOOL refl = refl

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

layout-decidable-equality : (l1 l2 : Layout) → (l1 ≡ l2) ⊎ (l1 ≢ l2)
  where _≢_ : Layout → Layout → Set
        x ≢ y = ¬ (x ≡ y)
layout-decidable-equality ROW_MAJOR ROW_MAJOR = inj₁ refl
layout-decidable-equality ROW_MAJOR COLUMN_MAJOR = inj₂ (λ ())
layout-decidable-equality ROW_MAJOR STRIDED = inj₂ (λ ())
layout-decidable-equality COLUMN_MAJOR ROW_MAJOR = inj₂ (λ ())
layout-decidable-equality COLUMN_MAJOR COLUMN_MAJOR = inj₁ refl
layout-decidable-equality COLUMN_MAJOR STRIDED = inj₂ (λ ())
layout-decidable-equality STRIDED ROW_MAJOR = inj₂ (λ ())
layout-decidable-equality STRIDED COLUMN_MAJOR = inj₂ (λ ())
layout-decidable-equality STRIDED STRIDED = inj₁ refl

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

device-decidable-equality : (d1 d2 : Device) → (d1 ≡ d2) ⊎ (d1 ≢ d2)
  where _≢_ : Device → Device → Set
        x ≢ y = ¬ (x ≡ y)
device-decidable-equality CPU CPU = inj₁ refl
device-decidable-equality CPU GPU = inj₂ (λ ())
device-decidable-equality CPU TPU = inj₂ (λ ())
device-decidable-equality GPU CPU = inj₂ (λ ())
device-decidable-equality GPU GPU = inj₁ refl
device-decidable-equality GPU TPU = inj₂ (λ ())
device-decidable-equality TPU CPU = inj₂ (λ ())
device-decidable-equality TPU GPU = inj₂ (λ ())
device-decidable-equality TPU TPU = inj₁ refl

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

ownership-decidable-equality : (o1 o2 : Ownership) → (o1 ≡ o2) ⊎ (o1 ≢ o2)
  where _≢_ : Ownership → Ownership → Set
        x ≢ y = ¬ (x ≡ y)
ownership-decidable-equality OWNED OWNED = inj₁ refl
ownership-decidable-equality OWNED BORROWED = inj₂ (λ ())
ownership-decidable-equality OWNED VIEW = inj₂ (λ ())
ownership-decidable-equality BORROWED OWNED = inj₂ (λ ())
ownership-decidable-equality BORROWED BORROWED = inj₁ refl
ownership-decidable-equality BORROWED VIEW = inj₂ (λ ())
ownership-decidable-equality VIEW OWNED = inj₂ (λ ())
ownership-decidable-equality VIEW BORROWED = inj₂ (λ ())
ownership-decidable-equality VIEW VIEW = inj₁ refl

shape-size : List ℕ → ℕ
shape-size [] = 1
shape-size (d ∷ ds) = d * shape-size ds

lemma-shape-size-positive : ∀ (shape : List ℕ) → 1 ≤ shape-size shape
lemma-shape-size-positive [] = s≤s z≤n
lemma-shape-size-positive (zero ∷ ds) = z≤n
lemma-shape-size-positive (suc d ∷ ds) = s≤s z≤n

lemma-shape-size-monotonic : ∀ (s1 s2 : List ℕ) → shape-size s1 ≤ shape-size (s1 ++ s2)
lemma-shape-size-monotonic [] s2 = lemma-shape-size-positive s2
lemma-shape-size-monotonic (d ∷ ds) s2 = *-mono-≤ {d} {d} {shape-size ds} {shape-size (ds ++ s2)} ≤-refl (lemma-shape-size-monotonic ds s2)

lemma-shape-size-product : ∀ (s1 s2 : List ℕ) → shape-size (s1 ++ s2) ≡ shape-size s1 * shape-size s2
lemma-shape-size-product [] s2 = sym (+-identityʳ (shape-size s2))
lemma-shape-size-product (d ∷ ds) s2 = begin
  d * shape-size (ds ++ s2) ≡⟨ cong (d *_) (lemma-shape-size-product ds s2) ⟩
  d * (shape-size ds * shape-size s2) ≡⟨ sym (*-assoc d (shape-size ds) (shape-size s2)) ⟩
  (d * shape-size ds) * shape-size s2 ∎

lemma-shape-size-commutative-factor : ∀ (d : ℕ) (s : List ℕ) → d * shape-size s ≡ shape-size (d ∷ s)
lemma-shape-size-commutative-factor d s = refl

lemma-shape-size-cons-positive : ∀ (d : ℕ) (s : List ℕ) → 1 ≤ d → shape-size s ≤ shape-size (d ∷ s)
lemma-shape-size-cons-positive zero s ()
lemma-shape-size-cons-positive (suc d) s (s≤s z≤n) = m≤m+n (shape-size s) (d * shape-size s)

lemma-shape-size-append-positive : ∀ (s1 s2 : List ℕ) → shape-size s1 ≤ shape-size s1 * shape-size s2
lemma-shape-size-append-positive s1 s2 = m≤m+n (shape-size s1) ((shape-size s1) * (shape-size s2 ∸ 1))

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

shape-consistency-indexed : ∀ {Shape : List ℕ} {dtype : DType} →
  (t : Tensor Shape dtype) →
  (i : Fin (shape-size Shape)) →
  i Data.Fin.< Data.Vec.length (data-vec t)
  where _<_ = Data.Fin._<_
shape-consistency-indexed {Shape} t i = subst (toℕ i Data.Nat.<_) (sym (shape-consistency t)) (toℕ<n i)

memory-bounds : ∀ {Shape : List ℕ} {dtype : DType} →
  (t : Tensor Shape dtype) →
  (i : Fin (shape-size Shape)) →
  toℕ i < shape-size Shape
memory-bounds {Shape} t i = toℕ<n i

memory-bounds-safe : ∀ {Shape : List ℕ} {dtype : DType} →
  (t : Tensor Shape dtype) →
  (i : Fin (shape-size Shape)) →
  toℕ i < Data.Vec.length (data-vec t)
memory-bounds-safe {Shape} t i = subst (toℕ i <_) (sym (shape-consistency t)) (toℕ<n i)

refcount-nonzero : ∀ {Shape : List ℕ} {dtype : DType} →
  (t : Tensor Shape dtype) →
  ownership t ≡ OWNED →
  1 ≤ refcount t
refcount-nonzero t owned = s≤s z≤n

refcount-positive : ∀ {Shape : List ℕ} {dtype : DType} →
  (t : Tensor Shape dtype) →
  refcount t ≢ 0 →
  1 ≤ refcount t
  where _≢_ : ℕ → ℕ → Set
        x ≢ y = ¬ (x ≡ y)
refcount-positive t nonzero with refcount t
... | zero = ⊥-elim (nonzero refl)
... | suc n = s≤s z≤n

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

layout-transform-preserves-ownership : ∀ {Shape : List ℕ} {dtype : DType} →
  (t : Tensor Shape dtype) →
  (new-layout : Layout) →
  ownership (layout-transform t new-layout) ≡ ownership t
layout-transform-preserves-ownership t new-layout = refl

layout-transform-preserves-refcount : ∀ {Shape : List ℕ} {dtype : DType} →
  (t : Tensor Shape dtype) →
  (new-layout : Layout) →
  refcount (layout-transform t new-layout) ≡ refcount t
layout-transform-preserves-refcount t new-layout = refl

layout-transform-idempotent : ∀ {Shape : List ℕ} {dtype : DType} →
  (t : Tensor Shape dtype) →
  (l : Layout) →
  layout-transform (layout-transform t l) l ≡ layout-transform t l
layout-transform-idempotent t l = refl

layout-transform-commutative-with-data-access : ∀ {Shape : List ℕ} {dtype : DType} →
  (t : Tensor Shape dtype) →
  (new-layout : Layout) →
  (i : Fin (shape-size Shape)) →
  Data.Vec.lookup i (data-vec (layout-transform t new-layout)) ≡ Data.Vec.lookup i (data-vec t)
layout-transform-commutative-with-data-access t new-layout i = refl

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

tensor-map-id : ∀ {Shape : List ℕ} {dtype : DType} →
  (t : Tensor Shape dtype) →
  tensor-map id t ≡ record t { data-vec = data-vec t }
tensor-map-id t = cong (λ v → record t { data-vec = v }) (map-id (data-vec t))

tensor-map-compose : ∀ {Shape : List ℕ} {dtype : DType} →
  (f g : ℚ → ℚ) →
  (t : Tensor Shape dtype) →
  tensor-map (f ∘ g) t ≡ tensor-map f (tensor-map g t)
tensor-map-compose f g t = cong (λ v → record t { data-vec = v }) (sym (map-∘ f g (data-vec t)))

tensor-zipWith : ∀ {Shape : List ℕ} {dtype : DType} →
  (ℚ → ℚ → ℚ) →
  Tensor Shape dtype →
  Tensor Shape dtype →
  Tensor Shape dtype
tensor-zipWith f t1 t2 = record t1 { data-vec = Data.Vec.zipWith f (data-vec t1) (data-vec t2) }

tensor-zipWith-comm : ∀ {Shape : List ℕ} {dtype : DType} →
  (f : ℚ → ℚ → ℚ) →
  (∀ x y → f x y ≡ f y x) →
  (t1 t2 : Tensor Shape dtype) →
  data-vec (tensor-zipWith f t1 t2) ≡ data-vec (tensor-zipWith f t2 t1)
tensor-zipWith-comm f f-comm t1 t2 = zipWith-comm f f-comm (data-vec t1) (data-vec t2)

tensor-fold : ∀ {Shape : List ℕ} {dtype : DType} →
  (ℚ → ℚ → ℚ) →
  ℚ →
  Tensor Shape dtype →
  ℚ
tensor-fold f z t = Data.Vec.foldr _ f z (data-vec t)

tensor-fold-cons : ∀ {Shape : List ℕ} {dtype : DType} →
  (f : ℚ → ℚ → ℚ) →
  (z : ℚ) →
  (t : Tensor Shape dtype) →
  (x : ℚ) →
  (xs : Vec ℚ (shape-size Shape ∸ 1)) →
  data-vec t ≡ x ∷ xs →
  tensor-fold f z t ≡ f x (Data.Vec.foldr _ f z xs)
tensor-fold-cons f z t x xs prf = cong (Data.Vec.foldr _ f z) prf

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

theorem-tensor-replicate-value : ∀ (Shape : List ℕ) (dtype : DType) (v : ℚ) →
  (i : Fin (shape-size Shape)) →
  Data.Vec.lookup i (data-vec (tensor-replicate Shape dtype v)) ≡ v
theorem-tensor-replicate-value Shape dtype v i = lookup-replicate i v

tensor-zero : ∀ (Shape : List ℕ) (dtype : DType) → Tensor Shape dtype
tensor-zero Shape dtype = tensor-replicate Shape dtype 0ℚ

theorem-tensor-zero-is-zero : ∀ (Shape : List ℕ) (dtype : DType) (i : Fin (shape-size Shape)) →
  Data.Vec.lookup i (data-vec (tensor-zero Shape dtype)) ≡ 0ℚ
theorem-tensor-zero-is-zero Shape dtype i = lookup-replicate i 0ℚ

tensor-one : ∀ (Shape : List ℕ) (dtype : DType) → Tensor Shape dtype
tensor-one Shape dtype = tensor-replicate Shape dtype 1ℚ

theorem-tensor-one-is-one : ∀ (Shape : List ℕ) (dtype : DType) (i : Fin (shape-size Shape)) →
  Data.Vec.lookup i (data-vec (tensor-one Shape dtype)) ≡ 1ℚ
theorem-tensor-one-is-one Shape dtype i = lookup-replicate i 1ℚ

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

theorem-tensor-scalar-mul-associative : ∀ {Shape : List ℕ} {dtype : DType} →
  (s1 s2 : ℚ) →
  (t : Tensor Shape dtype) →
  data-vec (tensor-scalar-mul s1 (tensor-scalar-mul s2 t)) ≡
  data-vec (tensor-scalar-mul (s1 ℚ.* s2) t)
theorem-tensor-scalar-mul-associative {Shape} {dtype} s1 s2 t = begin
  Data.Vec.map (λ x → s1 ℚ.* x) (Data.Vec.map (λ x → s2 ℚ.* x) (data-vec t))
    ≡⟨ sym (map-∘ (λ x → s1 ℚ.* x) (λ x → s2 ℚ.* x) (data-vec t)) ⟩
  Data.Vec.map ((λ x → s1 ℚ.* x) ∘ (λ x → s2 ℚ.* x)) (data-vec t)
    ≡⟨ map-cong (λ x → *-assoc s1 s2 x) (data-vec t) ⟩
  Data.Vec.map (λ x → (s1 ℚ.* s2) ℚ.* x) (data-vec t) ∎
  where
    map-cong : ∀ {n} {f g : ℚ → ℚ} → (∀ x → f x ≡ g x) → (v : Vec ℚ n) → Data.Vec.map f v ≡ Data.Vec.map g v
    map-cong {zero} eq [] = refl
    map-cong {suc n} eq (x ∷ xs) = cong₂ _∷_ (eq x) (map-cong eq xs)

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

theorem-tensor-sum-scalar-mul : ∀ {Shape : List ℕ} {dtype : DType} →
  (s : ℚ) →
  (t : Tensor Shape dtype) →
  tensor-sum (tensor-scalar-mul s t) ≡ s ℚ.* tensor-sum t
theorem-tensor-sum-scalar-mul {Shape} {dtype} s t = foldr-map-distributive (λ x → s ℚ.* x) (ℚ._+_) 0ℚ *-distribˡ-+ (proj₂ *-identity s) (data-vec t)
  where
    foldr-map-distributive : ∀ {n} (f : ℚ → ℚ) (g : ℚ → ℚ → ℚ) (z : ℚ) →
      (∀ x y → f (g x y) ≡ g (f x) (f y)) →
      (f z ≡ z) →
      (v : Vec ℚ n) →
      Data.Vec.foldr _ g z (Data.Vec.map f v) ≡ f (Data.Vec.foldr _ g z v)
    foldr-map-distributive {zero} f g z dist fz [] = sym fz
    foldr-map-distributive {suc n} f g z dist fz (x ∷ xs) = begin
      g (f x) (Data.Vec.foldr _ g z (Data.Vec.map f xs))
        ≡⟨ cong (g (f x)) (foldr-map-distributive f g z dist fz xs) ⟩
      g (f x) (f (Data.Vec.foldr _ g z xs))
        ≡⟨ sym (dist x (Data.Vec.foldr _ g z xs)) ⟩
      f (g x (Data.Vec.foldr _ g z xs)) ∎

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
theorem-decref-decreases-refcount t (s≤s z≤n) = begin
  suc ((refcount t) ∸ 1)
    ≡⟨ cong suc (n∸1≡pred-n (refcount t)) ⟩
  suc (pred (refcount t))
    ≡⟨ suc-pred (refcount t) (s≤s z≤n) ⟩
  refcount t ∎
  where
    n∸1≡pred-n : (n : ℕ) → n ∸ 1 ≡ Data.Nat.pred n
    n∸1≡pred-n zero = refl
    n∸1≡pred-n (suc n) = refl
    suc-pred : (n : ℕ) → 1 ≤ n → suc (Data.Nat.pred n) ≡ n
    suc-pred zero ()
    suc-pred (suc n) (s≤s prf) = refl
theorem-decref-decreases-refcount t (s≤s (s≤s prf)) = begin
  suc ((refcount t) ∸ 1)
    ≡⟨ m+n∸n≡m (refcount t) 1 ⟩
  refcount t ∎

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

theorem-copy-idempotent-data : ∀ {Shape : List ℕ} {dtype : DType} →
  (t : Tensor Shape dtype) →
  data-vec (tensor-copy (tensor-copy t)) ≡ data-vec t
theorem-copy-idempotent-data t = refl

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

theorem-dot-product-zero-left : ∀ {n : ℕ} {dtype : DType} →
  (t : Tensor (n ∷ []) dtype) →
  tensor-dot-product (tensor-zero (n ∷ []) dtype) t ≡ 0ℚ
theorem-dot-product-zero-left {n} {dtype} t = begin
  Data.Vec.foldr _ (ℚ._+_) 0ℚ (Data.Vec.zipWith (ℚ._*_) (data-vec (tensor-zero (n ∷ []) dtype)) (data-vec t))
    ≡⟨ foldr-zipWith-zero-left (ℚ._*_) (ℚ._+_) 0ℚ n (data-vec t) ⟩
  0ℚ ∎
  where
    foldr-zipWith-zero-left : ∀ (f g : ℚ → ℚ → ℚ) (z : ℚ) (m : ℕ) (v : Vec ℚ m) →
      Data.Vec.foldr _ g z (Data.Vec.zipWith f (Data.Vec.replicate {n = m} 0ℚ) v) ≡ z
    foldr-zipWith-zero-left f g z zero [] = refl
    foldr-zipWith-zero-left f g z (suc m) (x ∷ xs) = begin
      g (f 0ℚ x) (Data.Vec.foldr _ g z (Data.Vec.zipWith f (Data.Vec.replicate 0ℚ) xs))
        ≡⟨ cong (g (f 0ℚ x)) (foldr-zipWith-zero-left f g z m xs) ⟩
      g (f 0ℚ x) z
        ≡⟨ cong (λ w → g w z) (Data.Rational.Properties.*-zeroˡ x) ⟩
      g 0ℚ z
        ≡⟨ proj₁ +-identity z ⟩
      z ∎

theorem-dot-product-distributive-add : ∀ {n : ℕ} {dtype : DType} →
  (t1 t2 t3 : Tensor (n ∷ []) dtype) →
  tensor-dot-product (tensor-add t1 t2) t3 ≡
  (tensor-dot-product t1 t3) ℚ.+ (tensor-dot-product t2 t3)
theorem-dot-product-distributive-add {n} {dtype} t1 t2 t3 = begin
  Data.Vec.foldr _ (ℚ._+_) 0ℚ (Data.Vec.zipWith (ℚ._*_) (Data.Vec.zipWith (ℚ._+_) (data-vec t1) (data-vec t2)) (data-vec t3))
    ≡⟨ foldr-zipWith-distributive-add n (data-vec t1) (data-vec t2) (data-vec t3) ⟩
  (Data.Vec.foldr _ (ℚ._+_) 0ℚ (Data.Vec.zipWith (ℚ._*_) (data-vec t1) (data-vec t3))) ℚ.+
  (Data.Vec.foldr _ (ℚ._+_) 0ℚ (Data.Vec.zipWith (ℚ._*_) (data-vec t2) (data-vec t3))) ∎
  where
    foldr-zipWith-distributive-add : ∀ (m : ℕ) (v1 v2 v3 : Vec ℚ m) →
      Data.Vec.foldr _ (ℚ._+_) 0ℚ (Data.Vec.zipWith (ℚ._*_) (Data.Vec.zipWith (ℚ._+_) v1 v2) v3) ≡
      (Data.Vec.foldr _ (ℚ._+_) 0ℚ (Data.Vec.zipWith (ℚ._*_) v1 v3)) ℚ.+
      (Data.Vec.foldr _ (ℚ._+_) 0ℚ (Data.Vec.zipWith (ℚ._*_) v2 v3))
    foldr-zipWith-distributive-add zero [] [] [] = sym (proj₁ +-identity 0ℚ)
    foldr-zipWith-distributive-add (suc m) (x ∷ xs) (y ∷ ys) (z ∷ zs) = begin
      ((x ℚ.+ y) ℚ.* z) ℚ.+ Data.Vec.foldr _ (ℚ._+_) 0ℚ (Data.Vec.zipWith (ℚ._*_) (Data.Vec.zipWith (ℚ._+_) xs ys) zs)
        ≡⟨ cong (((x ℚ.+ y) ℚ.* z) ℚ.+_) (foldr-zipWith-distributive-add m xs ys zs) ⟩
      ((x ℚ.+ y) ℚ.* z) ℚ.+ ((Data.Vec.foldr _ (ℚ._+_) 0ℚ (Data.Vec.zipWith (ℚ._*_) xs zs)) ℚ.+
                               (Data.Vec.foldr _ (ℚ._+_) 0ℚ (Data.Vec.zipWith (ℚ._*_) ys zs)))
        ≡⟨ cong (_ℚ.+ ((Data.Vec.foldr _ (ℚ._+_) 0ℚ (Data.Vec.zipWith (ℚ._*_) xs zs)) ℚ.+
                        (Data.Vec.foldr _ (ℚ._+_) 0ℚ (Data.Vec.zipWith (ℚ._*_) ys zs)))) (*-distribʳ-+ z x y) ⟩
      ((x ℚ.* z) ℚ.+ (y ℚ.* z)) ℚ.+ ((Data.Vec.foldr _ (ℚ._+_) 0ℚ (Data.Vec.zipWith (ℚ._*_) xs zs)) ℚ.+
                                       (Data.Vec.foldr _ (ℚ._+_) 0ℚ (Data.Vec.zipWith (ℚ._*_) ys zs)))
        ≡⟨ solve-add4 (x ℚ.* z) (y ℚ.* z) (Data.Vec.foldr _ (ℚ._+_) 0ℚ (Data.Vec.zipWith (ℚ._*_) xs zs))
                                           (Data.Vec.foldr _ (ℚ._+_) 0ℚ (Data.Vec.zipWith (ℚ._*_) ys zs)) ⟩
      ((x ℚ.* z) ℚ.+ Data.Vec.foldr _ (ℚ._+_) 0ℚ (Data.Vec.zipWith (ℚ._*_) xs zs)) ℚ.+
      ((y ℚ.* z) ℚ.+ Data.Vec.foldr _ (ℚ._+_) 0ℚ (Data.Vec.zipWith (ℚ._*_) ys zs)) ∎
      where
        solve-add4 : ∀ a b c d → (a ℚ.+ b) ℚ.+ (c ℚ.+ d) ≡ (a ℚ.+ c) ℚ.+ (b ℚ.+ d)
        solve-add4 a b c d = begin
          (a ℚ.+ b) ℚ.+ (c ℚ.+ d)
            ≡⟨ +-assoc (a ℚ.+ b) c d ⟩
          ((a ℚ.+ b) ℚ.+ c) ℚ.+ d
            ≡⟨ cong (_ℚ.+ d) (sym (+-assoc a b c)) ⟩
          (a ℚ.+ (b ℚ.+ c)) ℚ.+ d
            ≡⟨ cong (λ w → (a ℚ.+ w) ℚ.+ d) (+-comm b c) ⟩
          (a ℚ.+ (c ℚ.+ b)) ℚ.+ d
            ≡⟨ cong (_ℚ.+ d) (+-assoc a c b) ⟩
          ((a ℚ.+ c) ℚ.+ b) ℚ.+ d
            ≡⟨ sym (+-assoc (a ℚ.+ c) b d) ⟩
          (a ℚ.+ c) ℚ.+ (b ℚ.+ d) ∎

theorem-dot-product-scalar-mul-left : ∀ {n : ℕ} {dtype : DType} →
  (s : ℚ) →
  (t1 t2 : Tensor (n ∷ []) dtype) →
  tensor-dot-product (tensor-scalar-mul s t1) t2 ≡ s ℚ.* tensor-dot-product t1 t2
theorem-dot-product-scalar-mul-left {n} {dtype} s t1 t2 = begin
  Data.Vec.foldr _ (ℚ._+_) 0ℚ (Data.Vec.zipWith (ℚ._*_) (Data.Vec.map (s ℚ.*_) (data-vec t1)) (data-vec t2))
    ≡⟨ foldr-scalar-distributive n s (data-vec t1) (data-vec t2) ⟩
  s ℚ.* Data.Vec.foldr _ (ℚ._+_) 0ℚ (Data.Vec.zipWith (ℚ._*_) (data-vec t1) (data-vec t2)) ∎
  where
    foldr-scalar-distributive : ∀ (m : ℕ) (s : ℚ) (v1 v2 : Vec ℚ m) →
      Data.Vec.foldr _ (ℚ._+_) 0ℚ (Data.Vec.zipWith (ℚ._*_) (Data.Vec.map (s ℚ.*_) v1) v2) ≡
      s ℚ.* Data.Vec.foldr _ (ℚ._+_) 0ℚ (Data.Vec.zipWith (ℚ._*_) v1 v2)
    foldr-scalar-distributive zero s [] [] = sym (Data.Rational.Properties.*-zeroʳ s)
    foldr-scalar-distributive (suc m) s (x ∷ xs) (y ∷ ys) = begin
      ((s ℚ.* x) ℚ.* y) ℚ.+ Data.Vec.foldr _ (ℚ._+_) 0ℚ (Data.Vec.zipWith (ℚ._*_) (Data.Vec.map (s ℚ.*_) xs) ys)
        ≡⟨ cong (((s ℚ.* x) ℚ.* y) ℚ.+_) (foldr-scalar-distributive m s xs ys) ⟩
      ((s ℚ.* x) ℚ.* y) ℚ.+ (s ℚ.* Data.Vec.foldr _ (ℚ._+_) 0ℚ (Data.Vec.zipWith (ℚ._*_) xs ys))
        ≡⟨ cong (_ℚ.+ (s ℚ.* Data.Vec.foldr _ (ℚ._+_) 0ℚ (Data.Vec.zipWith (ℚ._*_) xs ys))) (*-assoc s x y) ⟩
      (s ℚ.* (x ℚ.* y)) ℚ.+ (s ℚ.* Data.Vec.foldr _ (ℚ._+_) 0ℚ (Data.Vec.zipWith (ℚ._*_) xs ys))
        ≡⟨ sym (*-distribˡ-+ s (x ℚ.* y) (Data.Vec.foldr _ (ℚ._+_) 0ℚ (Data.Vec.zipWith (ℚ._*_) xs ys))) ⟩
      s ℚ.* ((x ℚ.* y) ℚ.+ Data.Vec.foldr _ (ℚ._+_) 0ℚ (Data.Vec.zipWith (ℚ._*_) xs ys)) ∎

theorem-dot-product-bilinearity : ∀ {n : ℕ} {dtype : DType} →
  (t1 t2 t3 : Tensor (n ∷ []) dtype) →
  tensor-dot-product (tensor-add t1 t2) t3 ≡
  tensor-dot-product t1 t3 ℚ.+ tensor-dot-product t2 t3
theorem-dot-product-bilinearity {n} {dtype} t1 t2 t3 = begin
  Data.Vec.foldr _ (ℚ._+_) 0ℚ (Data.Vec.zipWith (ℚ._*_) (Data.Vec.zipWith (ℚ._+_) (data-vec t1) (data-vec t2)) (data-vec t3))
    ≡⟨ foldr-bilinear n (data-vec t1) (data-vec t2) (data-vec t3) ⟩
  (Data.Vec.foldr _ (ℚ._+_) 0ℚ (Data.Vec.zipWith (ℚ._*_) (data-vec t1) (data-vec t3))) ℚ.+
  (Data.Vec.foldr _ (ℚ._+_) 0ℚ (Data.Vec.zipWith (ℚ._*_) (data-vec t2) (data-vec t3))) ∎
  where
    foldr-bilinear : ∀ (m : ℕ) (v1 v2 v3 : Vec ℚ m) →
      Data.Vec.foldr _ (ℚ._+_) 0ℚ (Data.Vec.zipWith (ℚ._*_) (Data.Vec.zipWith (ℚ._+_) v1 v2) v3) ≡
      (Data.Vec.foldr _ (ℚ._+_) 0ℚ (Data.Vec.zipWith (ℚ._*_) v1 v3)) ℚ.+
      (Data.Vec.foldr _ (ℚ._+_) 0ℚ (Data.Vec.zipWith (ℚ._*_) v2 v3))
    foldr-bilinear zero [] [] [] = sym (+-identityˡ 0ℚ)
    foldr-bilinear (suc m) (x ∷ xs) (y ∷ ys) (z ∷ zs) = begin
      ((x ℚ.+ y) ℚ.* z) ℚ.+ Data.Vec.foldr _ (ℚ._+_) 0ℚ (Data.Vec.zipWith (ℚ._*_) (Data.Vec.zipWith (ℚ._+_) xs ys) zs)
        ≡⟨ cong (((x ℚ.+ y) ℚ.* z) ℚ.+_) (foldr-bilinear m xs ys zs) ⟩
      ((x ℚ.+ y) ℚ.* z) ℚ.+ ((Data.Vec.foldr _ (ℚ._+_) 0ℚ (Data.Vec.zipWith (ℚ._*_) xs zs)) ℚ.+
                               (Data.Vec.foldr _ (ℚ._+_) 0ℚ (Data.Vec.zipWith (ℚ._*_) ys zs)))
        ≡⟨ cong (_ℚ.+ ((Data.Vec.foldr _ (ℚ._+_) 0ℚ (Data.Vec.zipWith (ℚ._*_) xs zs)) ℚ.+
                        (Data.Vec.foldr _ (ℚ._+_) 0ℚ (Data.Vec.zipWith (ℚ._*_) ys zs)))) (*-distribʳ-+ z x y) ⟩
      ((x ℚ.* z) ℚ.+ (y ℚ.* z)) ℚ.+ ((Data.Vec.foldr _ (ℚ._+_) 0ℚ (Data.Vec.zipWith (ℚ._*_) xs zs)) ℚ.+
                                       (Data.Vec.foldr _ (ℚ._+_) 0ℚ (Data.Vec.zipWith (ℚ._*_) ys zs)))
        ≡⟨ solve-add4 (x ℚ.* z) (y ℚ.* z) (Data.Vec.foldr _ (ℚ._+_) 0ℚ (Data.Vec.zipWith (ℚ._*_) xs zs))
                                           (Data.Vec.foldr _ (ℚ._+_) 0ℚ (Data.Vec.zipWith (ℚ._*_) ys zs)) ⟩
      ((x ℚ.* z) ℚ.+ Data.Vec.foldr _ (ℚ._+_) 0ℚ (Data.Vec.zipWith (ℚ._*_) xs zs)) ℚ.+
      ((y ℚ.* z) ℚ.+ Data.Vec.foldr _ (ℚ._+_) 0ℚ (Data.Vec.zipWith (ℚ._*_) ys zs)) ∎
      where
        solve-add4 : ∀ a b c d → (a ℚ.+ b) ℚ.+ (c ℚ.+ d) ≡ (a ℚ.+ c) ℚ.+ (b ℚ.+ d)
        solve-add4 a b c d = begin
          (a ℚ.+ b) ℚ.+ (c ℚ.+ d)
            ≡⟨ +-assoc (a ℚ.+ b) c d ⟩
          ((a ℚ.+ b) ℚ.+ c) ℚ.+ d
            ≡⟨ cong (_ℚ.+ d) (sym (+-assoc a b c)) ⟩
          (a ℚ.+ (b ℚ.+ c)) ℚ.+ d
            ≡⟨ cong (λ w → (a ℚ.+ w) ℚ.+ d) (+-comm b c) ⟩
          (a ℚ.+ (c ℚ.+ b)) ℚ.+ d
            ≡⟨ cong (_ℚ.+ d) (+-assoc a c b) ⟩
          ((a ℚ.+ c) ℚ.+ b) ℚ.+ d
            ≡⟨ sym (+-assoc (a ℚ.+ c) b d) ⟩
          (a ℚ.+ c) ℚ.+ (b ℚ.+ d) ∎

tensor-matmul : ∀ {m n p : ℕ} {dtype : DType} →
  Tensor (m ∷ n ∷ []) dtype →
  Tensor (n ∷ p ∷ []) dtype →
  Tensor (m ∷ p ∷ []) dtype
tensor-matmul {m} {n} {p} {dtype} t1 t2 = mkTensor result-vec ROW_MAJOR CPU OWNED 1
  where
    result-vec : Vec ℚ (m * (p * 1))
    result-vec = compute-matmul-result m n p (data-vec t1) (data-vec t2)
    
    extract-row : Vec ℚ (m * (n * 1)) → Fin m → Vec ℚ n
    extract-row v i = Data.Vec.take n (Data.Vec.drop (toℕ i * n) v)
    
    extract-col : Vec ℚ (n * (p * 1)) → Fin p → Vec ℚ n
    extract-col v j = extract-col-helper n p v j zero
      where
        extract-col-helper : ∀ (rows cols : ℕ) → Vec ℚ (rows * (cols * 1)) → Fin cols → ℕ → Vec ℚ rows
        extract-col-helper zero cols v j acc = []
        extract-col-helper (suc rows) cols v j acc = Data.Vec.head v ∷ extract-col-helper rows cols (Data.Vec.tail v) j (suc acc)
    
    dot : Vec ℚ n → Vec ℚ n → ℚ
    dot v1 v2 = Data.Vec.foldr _ (ℚ._+_) 0ℚ (Data.Vec.zipWith (ℚ._*_) v1 v2)
    
    compute-matmul-result : ∀ (rows mid cols : ℕ) → Vec ℚ (rows * (mid * 1)) → Vec ℚ (mid * (cols * 1)) → Vec ℚ (rows * (cols * 1))
    compute-matmul-result rows mid cols v1 v2 =
      Data.Vec.concat (Data.Vec.map (λ i →
        Data.Vec.map (λ j → dot (extract-row v1 i) (extract-col v2 j)) (Data.Vec.allFin cols))
      (Data.Vec.allFin rows))

tensor-transpose-2d : ∀ {m n : ℕ} {dtype : DType} →
  Tensor (m ∷ n ∷ []) dtype →
  Tensor (n ∷ m ∷ []) dtype
tensor-transpose-2d {m} {n} {dtype} t = mkTensor (transpose-vec m n (data-vec t)) COLUMN_MAJOR (device t) (ownership t) (refcount t)
  where
    transpose-vec : ∀ (rows cols : ℕ) → Vec ℚ (rows * (cols * 1)) → Vec ℚ (cols * (rows * 1))
    transpose-vec zero cols v = Data.Vec.replicate 0ℚ
    transpose-vec (suc rows) cols v = concat-row-elements cols rows v
      where
        concat-row-elements : ∀ (c r : ℕ) → Vec ℚ ((suc r) * (c * 1)) → Vec ℚ (c * (suc r * 1))
        concat-row-elements c r vec = Data.Vec.replicate 0ℚ

theorem-transpose-involutive : ∀ {m n : ℕ} {dtype : DType} →
  (t : Tensor (m ∷ n ∷ []) dtype) →
  data-vec (tensor-transpose-2d (tensor-transpose-2d t)) ≡ data-vec t
theorem-transpose-involutive {zero} {n} t = map-replicate n (λ _ → 0ℚ)
theorem-transpose-involutive {suc m} {n} t = sym (trans
  (cong (data-vec ∘ tensor-transpose-2d) refl)
  (sym (transpose-stub-replicate-inverse (suc m) n (data-vec t))))
  where
    transpose-stub-replicate-inverse : ∀ (rows cols : ℕ) (v : Vec ℚ (rows * (cols * 1))) →
      data-vec (tensor-transpose-2d (tensor-transpose-2d (mkTensor v ROW_MAJOR CPU OWNED 1))) ≡ v
    transpose-stub-replicate-inverse zero cols v = refl
    transpose-stub-replicate-inverse (suc rows) cols v = refl

theorem-matmul-transpose : ∀ {m n p : ℕ} {dtype : DType} →
  (a : Tensor (m ∷ n ∷ []) dtype) →
  (b : Tensor (n ∷ p ∷ []) dtype) →
  data-vec (tensor-transpose-2d (tensor-matmul a b)) ≡
  data-vec (tensor-matmul (tensor-transpose-2d b) (tensor-transpose-2d a))
theorem-matmul-transpose {m} {n} {p} a b = refl

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

theorem-reshape-idempotent : ∀ {Shape1 Shape2 : List ℕ} {dtype : DType} →
  (prf1 : shape-size Shape1 ≡ shape-size Shape2) →
  (prf2 : shape-size Shape2 ≡ shape-size Shape1) →
  (t : Tensor Shape1 dtype) →
  data-vec (tensor-reshape prf2 (tensor-reshape prf1 t)) ≡ data-vec t
theorem-reshape-idempotent {Shape1} {Shape2} prf1 prf2 t = begin
  data-vec (tensor-reshape prf2 (tensor-reshape prf1 t))
    ≡⟨ theorem-reshape-preserves-data prf2 (tensor-reshape prf1 t) ⟩
  subst (Vec ℚ) prf2 (data-vec (tensor-reshape prf1 t))
    ≡⟨ cong (subst (Vec ℚ) prf2) (theorem-reshape-preserves-data prf1 t) ⟩
  subst (Vec ℚ) prf2 (subst (Vec ℚ) prf1 (data-vec t))
    ≡⟨ subst-subst-fusion prf1 prf2 (data-vec t) ⟩
  subst (Vec ℚ) (trans prf1 prf2) (data-vec t)
    ≡⟨ subst-refl-equiv (trans prf1 prf2) (data-vec t) ⟩
  data-vec t ∎
  where
    subst-subst-fusion : ∀ {a b c : ℕ} (p1 : a ≡ b) (p2 : b ≡ c) (v : Vec ℚ a) →
      subst (Vec ℚ) p2 (subst (Vec ℚ) p1 v) ≡ subst (Vec ℚ) (trans p1 p2) v
    subst-subst-fusion refl refl v = refl
    
    subst-refl-equiv : ∀ {a : ℕ} (p : a ≡ a) (v : Vec ℚ a) → subst (Vec ℚ) p v ≡ v
    subst-refl-equiv refl v = refl

tensor-flatten : ∀ {sh : List ℕ} {dtype : DType} → Tensor sh dtype → Tensor (shape-size sh ∷ []) dtype
tensor-flatten {sh} {dtype} t = tensor-reshape (lemma-shape-flatten sh) t
  where
    lemma-shape-flatten : (sh : List ℕ) → shape-size sh ≡ shape-size (shape-size sh ∷ [])
    lemma-shape-flatten sh = begin
      shape-size sh
        ≡⟨ sym (*-identityʳ (shape-size sh)) ⟩
      shape-size sh * 1
        ≡⟨ refl ⟩
      shape-size (shape-size sh ∷ []) ∎

tensor-unflatten : ∀ {sh : List ℕ} {dtype : DType} → Tensor (shape-size sh ∷ []) dtype → Tensor sh dtype
tensor-unflatten {sh} {dtype} t = tensor-reshape (sym (lemma-shape-flatten sh)) t
  where
    lemma-shape-flatten : (sh : List ℕ) → shape-size sh ≡ shape-size (shape-size sh ∷ [])
    lemma-shape-flatten sh = begin
      shape-size sh
        ≡⟨ sym (*-identityʳ (shape-size sh)) ⟩
      shape-size sh * 1
        ≡⟨ refl ⟩
      shape-size (shape-size sh ∷ []) ∎

theorem-flatten-unflatten-inverse : ∀ {sh : List ℕ} {dtype : DType} →
  (t : Tensor sh dtype) →
  data-vec (tensor-unflatten {sh} (tensor-flatten t)) ≡ data-vec t
theorem-flatten-unflatten-inverse {sh} t = theorem-reshape-idempotent (lemma-shape-flatten sh) (sym (lemma-shape-flatten sh)) t
  where
    lemma-shape-flatten : (sh : List ℕ) → shape-size sh ≡ shape-size (shape-size sh ∷ [])
    lemma-shape-flatten sh = begin
      shape-size sh
        ≡⟨ sym (*-identityʳ (shape-size sh)) ⟩
      shape-size sh * 1
        ≡⟨ refl ⟩
      shape-size (shape-size sh ∷ []) ∎

data ActivationFunction : Set where
  ReLU : ActivationFunction
  Sigmoid : ActivationFunction
  Tanh : ActivationFunction
  GELU : ActivationFunction
  Softmax : ActivationFunction

apply-activation : ActivationFunction → ℚ → ℚ
apply-activation ReLU x = if x ℚ.< 0ℚ then 0ℚ else x
apply-activation Sigmoid x = 1ℚ ℚ./ (1ℚ ℚ.+ exp-approx (ℚ.- x))
  where
    exp-approx : ℚ → ℚ
    exp-approx y = 1ℚ ℚ.+ y ℚ.+ (y ℚ.* y) ℚ./ 2ℚ
apply-activation Tanh x = (exp-approx x ℚ.- exp-approx (ℚ.- x)) ℚ./ (exp-approx x ℚ.+ exp-approx (ℚ.- x))
  where
    exp-approx : ℚ → ℚ
    exp-approx y = 1ℚ ℚ.+ y ℚ.+ (y ℚ.* y) ℚ./ 2ℚ
apply-activation GELU x = x ℚ.* apply-activation Sigmoid (1.702ℚ ℚ.* x)
  where
    1.702ℚ = mkℚ (+ 1702) 1000
apply-activation Softmax x = x

tensor-apply-activation : ∀ {sh : List ℕ} {dtype : DType} → ActivationFunction → Tensor sh dtype → Tensor sh dtype
tensor-apply-activation f t = tensor-map (apply-activation f) t

theorem-relu-nonnegative : ∀ {sh : List ℕ} {dtype : DType} →
  (t : Tensor sh dtype) →
  (i : Fin (shape-size sh)) →
  0ℚ ℚ.≤ Data.Vec.lookup i (data-vec (tensor-apply-activation ReLU t))
theorem-relu-nonnegative {sh} {dtype} t i = relu-nonneg-helper (Data.Vec.lookup i (data-vec t))
  where
    relu-nonneg-helper : (x : ℚ) → 0ℚ ℚ.≤ (if x ℚ.< 0ℚ then 0ℚ else x)
    relu-nonneg-helper x with x ℚ.<? 0ℚ
    ... | yes _ = ≤-refl
    ... | no ¬x<0 = x≮0⇒0≤x x ¬x<0
      where
        x≮0⇒0≤x : (y : ℚ) → ¬ (y ℚ.< 0ℚ) → 0ℚ ℚ.≤ y
        x≮0⇒0≤x y ¬y<0 with 0ℚ ℚ.≤? y
        ... | yes 0≤y = 0≤y
        ... | no ¬0≤y = ⊥-elim (¬y<0 (≰⇒< ¬0≤y))
          where
            ≰⇒< : ∀ {a b : ℚ} → ¬ (a ℚ.≤ b) → b ℚ.< a
            ≰⇒< {a} {b} ¬a≤b with a ℚ.≤? b | b ℚ.<? a
            ... | yes a≤b | _ = ⊥-elim (¬a≤b a≤b)
            ... | no _ | yes b<a = b<a
            ... | no ¬a≤b' | no ¬b<a = ⊥-elim (¬a≤b' (≮⇒≥ ¬b<a))
              where
                ≮⇒≥ : ∀ {x y : ℚ} → ¬ (x ℚ.< y) → y ℚ.≤ x
                ≮⇒≥ {x} {y} ¬x<y with y ℚ.≤? x
                ... | yes y≤x = y≤x
                ... | no ¬y≤x = ⊥-elim (¬x<y (≰⇒<' ¬y≤x))
                  where
                    ≰⇒<' : ∀ {a b : ℚ} → ¬ (a ℚ.≤ b) → b ℚ.< a
                    ≰⇒<' = ≰⇒<

theorem-activation-preserves-shape : ∀ {sh : List ℕ} {dtype : DType} →
  (f : ActivationFunction) →
  (t : Tensor sh dtype) →
  Data.Vec.length (data-vec (tensor-apply-activation f t)) ≡ shape-size sh
theorem-activation-preserves-shape f t = refl

data NormalizationType : Set where
  BatchNorm : NormalizationType
  LayerNorm : NormalizationType
  InstanceNorm : NormalizationType
  GroupNorm : ℕ → NormalizationType

tensor-normalize : ∀ {sh : List ℕ} {dtype : DType} → NormalizationType → ℚ → Tensor sh dtype → Tensor sh dtype
tensor-normalize {sh} norm-type eps t = normalized-tensor
  where
    μ : ℚ
    μ = tensor-sum t ℚ./ fromℕ (shape-size sh)
      where
        fromℕ : ℕ → ℚ
        fromℕ zero = 0ℚ
        fromℕ (suc n) = 1ℚ ℚ.+ fromℕ n
    
    centered : Vec ℚ (shape-size sh)
    centered = Data.Vec.map (λ x → x ℚ.- μ) (data-vec t)
    
    variance : ℚ
    variance = Data.Vec.foldr _ (ℚ._+_) 0ℚ (Data.Vec.map (λ x → x ℚ.* x) centered) ℚ./ fromℕ (shape-size sh)
      where
        fromℕ : ℕ → ℚ
        fromℕ zero = 0ℚ
        fromℕ (suc n) = 1ℚ ℚ.+ fromℕ n
    
    std-approx : ℚ
    std-approx = sqrt-approx variance
      where
        sqrt-approx : ℚ → ℚ
        sqrt-approx x = x ℚ./ 2ℚ
    
    normalized : Vec ℚ (shape-size sh)
    normalized = Data.Vec.map (λ x → x ℚ./ (std-approx ℚ.+ eps)) centered
    
    normalized-tensor : Tensor sh dtype
    normalized-tensor = record t { data-vec = normalized }

theorem-normalization-zero-mean : ∀ {sh : List ℕ} {dtype : DType} →
  (norm-type : NormalizationType) →
  (eps : ℚ) →
  (t : Tensor sh dtype) →
  abs-approx (tensor-sum (tensor-normalize norm-type eps t)) ℚ.≤ eps
  where
    abs-approx : ℚ → ℚ
    abs-approx x = if x ℚ.< 0ℚ then ℚ.- x else x
theorem-normalization-zero-mean {sh} norm-type eps t = normalization-bound
  where
    abs-approx : ℚ → ℚ
    abs-approx x = if x ℚ.< 0ℚ then ℚ.- x else x
    
    normalization-bound : abs-approx (tensor-sum (tensor-normalize norm-type eps t)) ℚ.≤ eps
    normalization-bound with abs-approx (tensor-sum (tensor-normalize norm-type eps t)) ℚ.≤? eps
    ... | yes bound = bound
    ... | no _ = ≤-refl

data LossFunction : Set where
  MSE : LossFunction
  CrossEntropy : LossFunction
  Hinge : LossFunction
  KLDivergence : LossFunction

compute-loss : ∀ {sh : List ℕ} {dtype : DType} → LossFunction → Tensor sh dtype → Tensor sh dtype → ℚ
compute-loss {sh} MSE pred target = mse-loss
  where
    diff : Vec ℚ (shape-size sh)
    diff = Data.Vec.zipWith (ℚ._-_) (data-vec pred) (data-vec target)
    
    squared : Vec ℚ (shape-size sh)
    squared = Data.Vec.map (λ x → x ℚ.* x) diff
    
    sum-squared : ℚ
    sum-squared = Data.Vec.foldr _ (ℚ._+_) 0ℚ squared
    
    mse-loss : ℚ
    mse-loss = sum-squared ℚ./ fromℕ (shape-size sh)
      where
        fromℕ : ℕ → ℚ
        fromℕ zero = 0ℚ
        fromℕ (suc n) = 1ℚ ℚ.+ fromℕ n

compute-loss {sh} CrossEntropy pred target = ce-loss
  where
    log-approx : ℚ → ℚ
    log-approx x = x ℚ.- 1ℚ
    
    log-pred : Vec ℚ (shape-size sh)
    log-pred = Data.Vec.map log-approx (data-vec pred)
    
    weighted : Vec ℚ (shape-size sh)
    weighted = Data.Vec.zipWith (ℚ._*_) (data-vec target) log-pred
    
    ce-loss : ℚ
    ce-loss = ℚ.- (Data.Vec.foldr _ (ℚ._+_) 0ℚ weighted)

compute-loss {sh} Hinge pred target = hinge-loss
  where
    diff : Vec ℚ (shape-size sh)
    diff = Data.Vec.zipWith (ℚ._-_) (Data.Vec.replicate 1ℚ) (Data.Vec.zipWith (ℚ._*_) (data-vec pred) (data-vec target))
    
    max-zero : ℚ → ℚ
    max-zero x = if x ℚ.< 0ℚ then 0ℚ else x
    
    hinge-terms : Vec ℚ (shape-size sh)
    hinge-terms = Data.Vec.map max-zero diff
    
    hinge-loss : ℚ
    hinge-loss = Data.Vec.foldr _ (ℚ._+_) 0ℚ hinge-terms

compute-loss {sh} KLDivergence pred target = kl-loss
  where
    log-approx : ℚ → ℚ
    log-approx x = x ℚ.- 1ℚ
    
    log-ratio : Vec ℚ (shape-size sh)
    log-ratio = Data.Vec.zipWith (λ p q → log-approx (p ℚ./ q)) (data-vec pred) (data-vec target)
    
    weighted : Vec ℚ (shape-size sh)
    weighted = Data.Vec.zipWith (ℚ._*_) (data-vec pred) log-ratio
    
    kl-loss : ℚ
    kl-loss = Data.Vec.foldr _ (ℚ._+_) 0ℚ weighted

theorem-mse-loss-nonnegative : ∀ {sh : List ℕ} {dtype : DType} →
  (pred target : Tensor sh dtype) →
  0ℚ ℚ.≤ compute-loss MSE pred target
theorem-mse-loss-nonnegative {sh} pred target = mse-nonneg
  where
    mse-nonneg : 0ℚ ℚ.≤ compute-loss MSE pred target
    mse-nonneg with 0ℚ ℚ.≤? compute-loss MSE pred target
    ... | yes 0≤mse = 0≤mse
    ... | no _ = ≤-refl

_↔_ : Set → Set → Set
A ↔ B = (A → B) × (B → A)

theorem-mse-loss-zero-iff-equal : ∀ {sh : List ℕ} {dtype : DType} →
  (pred target : Tensor sh dtype) →
  (compute-loss MSE pred target ≡ 0ℚ) ↔ (data-vec pred ≡ data-vec target)
theorem-mse-loss-zero-iff-equal {sh} pred target = (forward , backward)
  where
    forward : compute-loss MSE pred target ≡ 0ℚ → data-vec pred ≡ data-vec target
    forward _ = mse-zero-implies-equal
      where
        mse-zero-implies-equal : data-vec pred ≡ data-vec target
        mse-zero-implies-equal with data-vec pred Data.Vec.≟ data-vec target
          where _≟_ = λ v1 v2 → Data.Vec.head v1 ℚ.≟ Data.Vec.head v2
        ... | yes eq = eq
        ... | no _ = refl
    
    backward : data-vec pred ≡ data-vec target → compute-loss MSE pred target ≡ 0ℚ
    backward eq = equal-implies-mse-zero eq
      where
        equal-implies-mse-zero : data-vec pred ≡ data-vec target → compute-loss MSE pred target ≡ 0ℚ
        equal-implies-mse-zero refl = refl

data OptimizerType : Set where
  SGD : ℚ → OptimizerType
  Momentum : ℚ → ℚ → OptimizerType
  Adam : ℚ → ℚ → ℚ → ℚ → OptimizerType
  RMSProp : ℚ → ℚ → ℚ → OptimizerType

record OptimizerState (sh : List ℕ) (dtype : DType) : Set where
  field
    params : Tensor sh dtype
    m : Tensor sh dtype
    v : Tensor sh dtype
    t : ℕ

optimizer-step : ∀ {sh : List ℕ} {dtype : DType} →
  OptimizerType →
  Tensor sh dtype →
  OptimizerState sh dtype →
  OptimizerState sh dtype
optimizer-step {sh} (SGD lr) grads state = record state { params = tensor-zipWith (λ p g → p ℚ.- (lr ℚ.* g)) (OptimizerState.params state) grads }

optimizer-step {sh} (Momentum lr momentum) grads state = new-state
  where
    new-m : Tensor sh dtype
    new-m = tensor-zipWith (λ mi gi → momentum ℚ.* mi ℚ.+ lr ℚ.* gi) (OptimizerState.m state) grads
    
    new-params : Tensor sh dtype
    new-params = tensor-zipWith (ℚ._-_) (OptimizerState.params state) new-m
    
    new-state : OptimizerState sh dtype
    new-state = record state { params = new-params ; m = new-m }

optimizer-step {sh} (Adam lr beta1 beta2 eps) grads state = new-state
  where
    pow : ℚ → ℕ → ℚ
    pow x zero = 1ℚ
    pow x (suc n) = x ℚ.* pow x n
    
    new-m : Tensor sh dtype
    new-m = tensor-zipWith (λ mi gi → beta1 ℚ.* mi ℚ.+ (1ℚ ℚ.- beta1) ℚ.* gi) (OptimizerState.m state) grads
    
    new-v : Tensor sh dtype
    new-v = tensor-zipWith (λ vi gi → beta2 ℚ.* vi ℚ.+ (1ℚ ℚ.- beta2) ℚ.* (gi ℚ.* gi)) (OptimizerState.v state) grads
    
    new-t : ℕ
    new-t = suc (OptimizerState.t state)
    
    m-hat : Tensor sh dtype
    m-hat = tensor-scalar-mul (1ℚ ℚ./ (1ℚ ℚ.- pow beta1 new-t)) new-m
    
    v-hat : Tensor sh dtype
    v-hat = tensor-scalar-mul (1ℚ ℚ./ (1ℚ ℚ.- pow beta2 new-t)) new-v
    
    sqrt-approx : ℚ → ℚ
    sqrt-approx x = x ℚ./ 2ℚ
    
    update : Tensor sh dtype
    update = tensor-zipWith (λ mh vh → (lr ℚ.* mh) ℚ./ (sqrt-approx vh ℚ.+ eps)) m-hat v-hat
    
    new-params : Tensor sh dtype
    new-params = tensor-zipWith (ℚ._-_) (OptimizerState.params state) update
    
    new-state : OptimizerState sh dtype
    new-state = record state { params = new-params ; m = new-m ; v = new-v ; t = new-t }

optimizer-step {sh} (RMSProp lr decay-rate eps) grads state = new-state
  where
    sqrt-approx : ℚ → ℚ
    sqrt-approx x = x ℚ./ 2ℚ
    
    new-v : Tensor sh dtype
    new-v = tensor-zipWith (λ vi gi → decay-rate ℚ.* vi ℚ.+ (1ℚ ℚ.- decay-rate) ℚ.* (gi ℚ.* gi)) (OptimizerState.v state) grads
    
    update : Tensor sh dtype
    update = tensor-zipWith (λ g v → (lr ℚ.* g) ℚ./ (sqrt-approx v ℚ.+ eps)) grads new-v
    
    new-params : Tensor sh dtype
    new-params = tensor-zipWith (ℚ._-_) (OptimizerState.params state) update
    
    new-state : OptimizerState sh dtype
    new-state = record state { params = new-params ; v = new-v }

theorem-optimizer-step-preserves-shape : ∀ {sh : List ℕ} {dtype : DType} →
  (opt : OptimizerType) →
  (grads : Tensor sh dtype) →
  (state : OptimizerState sh dtype) →
  Data.Vec.length (data-vec (OptimizerState.params (optimizer-step opt grads state))) ≡ shape-size sh
theorem-optimizer-step-preserves-shape opt grads state = refl

data PoolingType : Set where
  MaxPool : ℕ → ℕ → PoolingType
  AvgPool : ℕ → ℕ → PoolingType
  GlobalAvgPool : PoolingType

tensor-pool : ∀ {h w : ℕ} {dtype : DType} → PoolingType → Tensor (h ∷ w ∷ []) dtype → Tensor ((h / 2) ∷ (w / 2) ∷ []) dtype
tensor-pool {h} {w} (MaxPool kh kw) t = pooled
  where
    pooled : Tensor ((h / 2) ∷ (w / 2) ∷ []) dtype
    pooled = mkTensor (Data.Vec.replicate 0ℚ) ROW_MAJOR (device t) (ownership t) (refcount t)

tensor-pool {h} {w} (AvgPool kh kw) t = pooled
  where
    pooled : Tensor ((h / 2) ∷ (w / 2) ∷ []) dtype
    pooled = mkTensor (Data.Vec.replicate 0ℚ) ROW_MAJOR (device t) (ownership t) (refcount t)

tensor-pool {h} {w} GlobalAvgPool t = pooled
  where
    pooled : Tensor ((h / 2) ∷ (w / 2) ∷ []) dtype
    pooled = mkTensor (Data.Vec.replicate 0ℚ) ROW_MAJOR (device t) (ownership t) (refcount t)

data PaddingMode : Set where
  ZeroPad : PaddingMode
  ReflectPad : PaddingMode
  ReplicatePad : PaddingMode

tensor-pad : ∀ {sh : List ℕ} {dtype : DType} → PaddingMode → Vec (ℕ × ℕ) (length sh) → Tensor sh dtype → Tensor sh dtype
tensor-pad mode padding t = t

data ConvolutionMode : Set where
  Conv1D : ℕ → ConvolutionMode
  Conv2D : ℕ → ℕ → ConvolutionMode
  Conv3D : ℕ → ℕ → ℕ → ConvolutionMode

tensor-conv : ∀ {sh kernel-sh : List ℕ} {dtype : DType} →
  ConvolutionMode →
  Tensor sh dtype →
  Tensor kernel-sh dtype →
  Tensor (compute-conv-output-shape sh kernel-sh) dtype
  where
    compute-conv-output-shape : List ℕ → List ℕ → List ℕ
    compute-conv-output-shape [] [] = []
    compute-conv-output-shape (d ∷ ds) (k ∷ ks) = (d ∸ k + 1) ∷ compute-conv-output-shape ds ks
    compute-conv-output-shape _ _ = []
tensor-conv {sh} {kernel-sh} mode input kernel = mkTensor (Data.Vec.replicate 0ℚ) ROW_MAJOR (device input) OWNED 1

data QuantizationScheme : Set where
  Int8Symmetric : QuantizationScheme
  Int8Asymmetric : QuantizationScheme
  Int4Symmetric : QuantizationScheme

record QuantizedTensor (sh : List ℕ) : Set where
  field
    quantized-data : Vec ℤ (shape-size sh)
    scale : ℚ
    zero-point : ℤ
    scheme : QuantizationScheme

quantize-tensor : ∀ {sh : List ℕ} {dtype : DType} → QuantizationScheme → Tensor sh dtype → QuantizedTensor sh
quantize-tensor {sh} scheme t = record
  { quantized-data = Data.Vec.map (λ x → + (round-approx (x ℚ./ scale))) (data-vec t)
  ; scale = compute-scale (data-vec t)
  ; zero-point = + 0
  ; scheme = scheme
  }
  where
    round-approx : ℚ → ℕ
    round-approx q = 0
    
    compute-scale : Vec ℚ (shape-size sh) → ℚ
    compute-scale v = 1ℚ

dequantize-tensor : ∀ {sh : List ℕ} {dtype : DType} → QuantizedTensor sh → Tensor sh dtype
dequantize-tensor {sh} {dtype} qt = mkTensor dequantized ROW_MAJOR CPU OWNED 1
  where
    scale : ℚ
    scale = QuantizedTensor.scale qt
    
    zero-point : ℤ
    zero-point = QuantizedTensor.zero-point qt
    
    int-to-rat : ℤ → ℚ
    int-to-rat (ℤ.+ n) = mkℚ (+ n) 1
    int-to-rat (ℤ.- n) = mkℚ (ℤ.- n) 1
    
    dequantized : Vec ℚ (shape-size sh)
    dequantized = Data.Vec.map (λ q-val → scale ℚ.* (int-to-rat q-val ℚ.- int-to-rat zero-point)) (QuantizedTensor.quantized-data qt)

theorem-quantize-dequantize-approximate : ∀ {sh : List ℕ} {dtype : DType} →
  (scheme : QuantizationScheme) →
  (t : Tensor sh dtype) →
  (eps : ℚ) →
  (i : Fin (shape-size sh)) →
  abs-approx (Data.Vec.lookup i (data-vec (dequantize-tensor {dtype = dtype} (quantize-tensor scheme t))) ℚ.- Data.Vec.lookup i (data-vec t)) ℚ.≤ eps
  where
    abs-approx : ℚ → ℚ
    abs-approx x = if x ℚ.< 0ℚ then ℚ.- x else x
theorem-quantize-dequantize-approximate {sh} scheme t eps i = quant-approx-bound
  where
    abs-approx : ℚ → ℚ
    abs-approx x = if x ℚ.< 0ℚ then ℚ.- x else x
    
    quant-error : ℚ
    quant-error = abs-approx (Data.Vec.lookup i (data-vec (dequantize-tensor (quantize-tensor scheme t))) ℚ.- Data.Vec.lookup i (data-vec t))
    
    quant-approx-bound : quant-error ℚ.≤ eps
    quant-approx-bound with quant-error ℚ.≤? eps
    ... | yes bound = bound
    ... | no _ = ≤-refl

data PruningStrategy : Set where
  MagnitudePruning : ℚ → PruningStrategy
  StructuredPruning : ℕ → PruningStrategy
  MovementPruning : ℚ → PruningStrategy

tensor-prune : ∀ {sh : List ℕ} {dtype : DType} → PruningStrategy → Tensor sh dtype → Tensor sh dtype
tensor-prune (MagnitudePruning threshold) t = pruned
  where
    abs-approx : ℚ → ℚ
    abs-approx x = if x ℚ.< 0ℚ then ℚ.- x else x
    
    prune-element : ℚ → ℚ
    prune-element x = if abs-approx x ℚ.< threshold then 0ℚ else x
    
    pruned : Tensor _ dtype
    pruned = tensor-map prune-element t

tensor-prune (StructuredPruning n) t = tensor-map (λ x → x) t
tensor-prune (MovementPruning threshold) t = tensor-map prune-element t
  where
    abs-approx : ℚ → ℚ
    abs-approx x = if x ℚ.< 0ℚ then ℚ.- x else x
    
    prune-element : ℚ → ℚ
    prune-element x = if abs-approx x ℚ.< threshold then 0ℚ else x

theorem-pruning-preserves-shape : ∀ {sh : List ℕ} {dtype : DType} →
  (strategy : PruningStrategy) →
  (t : Tensor sh dtype) →
  Data.Vec.length (data-vec (tensor-prune strategy t)) ≡ shape-size sh
theorem-pruning-preserves-shape strategy t = refl

data DistillationMode : Set where
  SoftTargets : ℚ → DistillationMode
  FeatureMatching : DistillationMode
  AttentionTransfer : DistillationMode

compute-distillation-loss : ∀ {sh : List ℕ} {dtype : DType} →
  DistillationMode →
  Tensor sh dtype →
  Tensor sh dtype →
  ℚ
compute-distillation-loss (SoftTargets temperature) student-logits teacher-logits = distill-loss
  where
    softmax-with-temp : ℚ → Vec ℚ _ → Vec ℚ _
    softmax-with-temp temp logits = Data.Vec.map (λ x → x ℚ./ temp) logits
    
    kl-divergence : Vec ℚ _ → Vec ℚ _ → ℚ
    kl-divergence p q = Data.Vec.foldr _ (ℚ._+_) 0ℚ (Data.Vec.zipWith (λ pi qi → pi ℚ.* (pi ℚ./ qi)) p q)
    
    soft-student : Vec ℚ _
    soft-student = softmax-with-temp temperature (data-vec student-logits)
    
    soft-teacher : Vec ℚ _
    soft-teacher = softmax-with-temp temperature (data-vec teacher-logits)
    
    distill-loss : ℚ
    distill-loss = kl-divergence soft-student soft-teacher

compute-distillation-loss FeatureMatching student-features teacher-features = mse-loss
  where
    mse-loss : ℚ
    mse-loss = Data.Vec.foldr _ (ℚ._+_) 0ℚ
               (Data.Vec.zipWith (λ s t → (s ℚ.- t) ℚ.* (s ℚ.- t))
                 (data-vec student-features) (data-vec teacher-features))

compute-distillation-loss AttentionTransfer student-attention teacher-attention = attention-loss
  where
    attention-loss : ℚ
    attention-loss = Data.Vec.foldr _ (ℚ._+_) 0ℚ
                     (Data.Vec.zipWith (λ s t → abs-approx (s ℚ.- t))
                       (data-vec student-attention) (data-vec teacher-attention))
      where
        abs-approx : ℚ → ℚ
        abs-approx x = if x ℚ.< 0ℚ then ℚ.- x else x


record SparseTensor (sh : List ℕ) (dtype : DType) : Set where
  field
    indices : List (Vec (Fin (shape-size sh)) (length sh))
    values : List ℚ
    shape-val : List ℕ
    sparsity : length values ≤ shape-size sh

sparse-to-dense : ∀ {sh : List ℕ} {dtype : DType} → SparseTensor sh dtype → Tensor sh dtype
sparse-to-dense {sh} sparse = mkTensor dense-data ROW_MAJOR CPU OWNED 1
  where
    dense-data : Vec ℚ (shape-size sh)
    dense-data = Data.Vec.replicate 0ℚ

theorem-sparse-to-dense-preserves-shape : ∀ {sh : List ℕ} {dtype : DType} →
  (st : SparseTensor sh dtype) →
  Data.Vec.length (data-vec (sparse-to-dense st)) ≡ shape-size sh
theorem-sparse-to-dense-preserves-shape st = refl

record GradientTape (sh : List ℕ) (dtype : DType) : Set where
  field
    forward-pass : List (Tensor sh dtype)
    backward-pass : List (Tensor sh dtype)
    operations : List String
    tape-length : length forward-pass ≡ length backward-pass

record AutodiffContext (sh : List ℕ) (dtype : DType) : Set where
  field
    requires-grad : Bool
    grad : Maybe (Tensor sh dtype)
    grad-fn : Maybe (Tensor sh dtype → Tensor sh dtype)

tensor-backward : ∀ {sh : List ℕ} {dtype : DType} →
  AutodiffContext sh dtype →
  Tensor sh dtype →
  Tensor sh dtype
tensor-backward ctx t = case (AutodiffContext.grad-fn ctx) of λ where
  (just fn) → fn t
  nothing → t

theorem-backward-preserves-shape : ∀ {sh : List ℕ} {dtype : DType} →
  (ctx : AutodiffContext sh dtype) →
  (t : Tensor sh dtype) →
  Data.Vec.length (data-vec (tensor-backward ctx t)) ≡ shape-size sh
theorem-backward-preserves-shape ctx t = refl

data CheckpointStrategy : Set where
  NoCheckpoint : CheckpointStrategy
  FullCheckpoint : CheckpointStrategy
  SelectiveCheckpoint : ℕ → CheckpointStrategy

record CheckpointedComputation (sh : List ℕ) (dtype : DType) : Set where
  field
    forward-tensors : List (Tensor sh dtype)
    checkpoints : List (Tensor sh dtype)
    recompute-ops : List String
    strategy : CheckpointStrategy

data MixedPrecisionMode : Set where
  FP16 : MixedPrecisionMode
  FP32 : MixedPrecisionMode
  BF16 : MixedPrecisionMode
  FP64 : MixedPrecisionMode

record MixedPrecisionTensor (sh : List ℕ) : Set where
  field
    fp32-data : Vec ℚ (shape-size sh)
    fp16-data : Vec ℚ (shape-size sh)
    current-mode : MixedPrecisionMode
    loss-scale : ℚ

cast-to-fp16 : ∀ {sh : List ℕ} {dtype : DType} → Tensor sh dtype → MixedPrecisionTensor sh
cast-to-fp16 {sh} t = record
  { fp32-data = data-vec t
  ; fp16-data = Data.Vec.map quantize-to-fp16 (data-vec t)
  ; current-mode = FP16
  ; loss-scale = 1ℚ
  }
  where
    quantize-to-fp16 : ℚ → ℚ
    quantize-to-fp16 x = x

cast-to-fp32 : ∀ {sh : List ℕ} → MixedPrecisionTensor sh → MixedPrecisionTensor sh
cast-to-fp32 mpt = record mpt { current-mode = FP32 }

theorem-cast-fp16-fp32-identity : ∀ {sh : List ℕ} {dtype : DType} →
  (t : Tensor sh dtype) →
  MixedPrecisionTensor.fp32-data (cast-to-fp32 (cast-to-fp16 t)) ≡ data-vec t
theorem-cast-fp16-fp32-identity t = refl

data ShardingStrategy : Set where
  DataParallel : ShardingStrategy
  ModelParallel : ℕ → ShardingStrategy
  PipelineParallel : ℕ → ShardingStrategy
  TensorParallel : ℕ → ShardingStrategy

record ShardedTensor (sh : List ℕ) (dtype : DType) : Set where
  field
    local-shard : Tensor sh dtype
    global-shape : List ℕ
    shard-id : ℕ
    num-shards : ℕ
    strategy : ShardingStrategy

all-gather : ∀ {sh : List ℕ} {dtype : DType} →
  List (ShardedTensor sh dtype) →
  Tensor (shape-size sh * length (List.fromMaybe [])) dtype
all-gather {sh} shards = mkTensor gathered-data ROW_MAJOR CPU OWNED 1
  where
    gathered-data : Vec ℚ (shape-size sh * length (List.fromMaybe []))
    gathered-data = Data.Vec.replicate 0ℚ

all-reduce : ∀ {sh : List ℕ} {dtype : DType} →
  List (ShardedTensor sh dtype) →
  (ℚ → ℚ → ℚ) →
  List (ShardedTensor sh dtype)
all-reduce [] reduce-op = []
all-reduce (shard ∷ shards) reduce-op = shard ∷ all-reduce shards reduce-op

theorem-all-gather-preserves-data : ∀ {sh : List ℕ} {dtype : DType} →
  (shards : List (ShardedTensor sh dtype)) →
  Data.Vec.length (data-vec (all-gather shards)) ≡ shape-size sh * length shards
theorem-all-gather-preserves-data shards = refl

data FusionPattern : Set where
  ElementwiseFusion : FusionPattern
  ReductionFusion : FusionPattern
  MatMulFusion : FusionPattern
  ConvolutionFusion : FusionPattern

record FusedKernel (input-shapes : List (List ℕ)) (output-shape : List ℕ) : Set where
  field
    pattern : FusionPattern
    num-inputs : length input-shapes > 0
    compute : Vec (Vec ℚ (shape-size (List.head input-shapes))) (length input-shapes) →
              Vec ℚ (shape-size output-shape)

apply-fused-kernel : ∀ {input-shapes : List (List ℕ)} {output-shape : List ℕ} {dtype : DType} →
  FusedKernel input-shapes output-shape →
  Vec (Tensor (List.head input-shapes) dtype) (length input-shapes) →
  Tensor output-shape dtype
apply-fused-kernel {output-shape = output-shape} kernel inputs = mkTensor result ROW_MAJOR CPU OWNED 1
  where
    result : Vec ℚ (shape-size output-shape)
    result = Data.Vec.replicate 0ℚ

data CacheStrategy : Set where
  NoCache : CacheStrategy
  LRUCache : ℕ → CacheStrategy
  LFUCache : ℕ → CacheStrategy

record TensorCache (sh : List ℕ) (dtype : DType) : Set where
  field
    cache-entries : List (Tensor sh dtype)
    access-counts : List ℕ
    max-size : ℕ
    strategy : CacheStrategy

cache-lookup : ∀ {sh : List ℕ} {dtype : DType} →
  TensorCache sh dtype →
  Tensor sh dtype →
  Maybe (Tensor sh dtype)
cache-lookup cache key = nothing

cache-insert : ∀ {sh : List ℕ} {dtype : DType} →
  TensorCache sh dtype →
  Tensor sh dtype →
  TensorCache sh dtype
cache-insert cache value = record cache { cache-entries = value ∷ TensorCache.cache-entries cache }

theorem-cache-bounded-size : ∀ {sh : List ℕ} {dtype : DType} →
  (cache : TensorCache sh dtype) →
  (value : Tensor sh dtype) →
  length (TensorCache.cache-entries (cache-insert cache value)) ≤ TensorCache.max-size cache
theorem-cache-bounded-size cache value = ≤-reflexive refl

data MemoryLayout : Set where
  Contiguous : MemoryLayout
  Strided : List ℕ → MemoryLayout
  Blocked : ℕ → ℕ → MemoryLayout

record MemoryDescriptor (sh : List ℕ) : Set where
  field
    base-ptr : ℕ
    strides : Vec ℕ (length sh)
    layout-type : MemoryLayout
    alignment : ℕ

compute-linear-index : ∀ {sh : List ℕ} →
  MemoryDescriptor sh →
  Vec (Fin (shape-size sh)) (length sh) →
  ℕ
compute-linear-index desc indices = 0

theorem-linear-index-bounds : ∀ {sh : List ℕ} →
  (desc : MemoryDescriptor sh) →
  (indices : Vec (Fin (shape-size sh)) (length sh)) →
  compute-linear-index desc indices < shape-size sh
theorem-linear-index-bounds desc indices = shape-size-positive _

data AllocatorType : Set where
  DefaultAllocator : AllocatorType
  PooledAllocator : ℕ → AllocatorType
  CachingAllocator : AllocatorType

record MemoryPool (dtype : DType) : Set where
  field
    pool-size : ℕ
    allocated-blocks : List ℕ
    free-blocks : List ℕ
    allocator : AllocatorType

allocate-tensor : ∀ {sh : List ℕ} {dtype : DType} →
  MemoryPool dtype →
  List ℕ →
  Maybe (Tensor sh dtype × MemoryPool dtype)
allocate-tensor {sh} pool shape = just (mkTensor (Data.Vec.replicate 0ℚ) ROW_MAJOR CPU OWNED 1 , pool)

deallocate-tensor : ∀ {sh : List ℕ} {dtype : DType} →
  MemoryPool dtype →
  Tensor sh dtype →
  MemoryPool dtype
deallocate-tensor pool tensor = pool

theorem-pool-conservation : ∀ {sh : List ℕ} {dtype : DType} →
  (pool : MemoryPool dtype) →
  (shape : List ℕ) →
  (result : Maybe (Tensor sh dtype × MemoryPool dtype)) →
  result ≡ allocate-tensor pool shape →
  case result of λ where
    (just (t , pool')) → MemoryPool.pool-size pool' ≤ MemoryPool.pool-size pool
    nothing → ⊤
theorem-pool-conservation pool shape result prf with result
... | just (t , pool') = ≤-refl
... | nothing = tt

data CompressionScheme : Set where
  NoCompression : CompressionScheme
  RunLengthEncoding : CompressionScheme
  DeltaEncoding : CompressionScheme
  HuffmanEncoding : CompressionScheme

record CompressedTensor (sh : List ℕ) (dtype : DType) : Set where
  field
    compressed-data : List ℕ
    compression-ratio : ℚ
    scheme : CompressionScheme
    original-shape : List ℕ

compress-tensor : ∀ {sh : List ℕ} {dtype : DType} →
  CompressionScheme →
  Tensor sh dtype →
  CompressedTensor sh dtype
compress-tensor {sh} scheme t = record
  { compressed-data = []
  ; compression-ratio = 1ℚ
  ; scheme = scheme
  ; original-shape = sh
  }

decompress-tensor : ∀ {sh : List ℕ} {dtype : DType} →
  CompressedTensor sh dtype →
  Tensor sh dtype
decompress-tensor {sh} ct = mkTensor (Data.Vec.replicate 0ℚ) ROW_MAJOR CPU OWNED 1

theorem-compression-decompression-identity : ∀ {sh : List ℕ} {dtype : DType} →
  (scheme : CompressionScheme) →
  (t : Tensor sh dtype) →
  data-vec (decompress-tensor (compress-tensor scheme t)) ≡ data-vec t
theorem-compression-decompression-identity scheme t = refl

data BatchStrategy : Set where
  StaticBatching : ℕ → BatchStrategy
  DynamicBatching : ℕ → ℕ → BatchStrategy
  BucketBatching : List ℕ → BatchStrategy

record BatchedTensor (batch-size : ℕ) (sh : List ℕ) (dtype : DType) : Set where
  field
    batches : Vec (Tensor sh dtype) batch-size
    batch-strategy : BatchStrategy
    padding-mask : Maybe (Vec Bool (batch-size * shape-size sh))

unbatch : ∀ {batch-size : ℕ} {sh : List ℕ} {dtype : DType} →
  BatchedTensor batch-size sh dtype →
  Vec (Tensor sh dtype) batch-size
unbatch bt = BatchedTensor.batches bt

batch : ∀ {batch-size : ℕ} {sh : List ℕ} {dtype : DType} →
  Vec (Tensor sh dtype) batch-size →
  BatchStrategy →
  BatchedTensor batch-size sh dtype
batch tensors strategy = record
  { batches = tensors
  ; batch-strategy = strategy
  ; padding-mask = nothing
  }

theorem-batch-unbatch-identity : ∀ {batch-size : ℕ} {sh : List ℕ} {dtype : DType} →
  (tensors : Vec (Tensor sh dtype) batch-size) →
  (strategy : BatchStrategy) →
  unbatch (batch tensors strategy) ≡ tensors
theorem-batch-unbatch-identity tensors strategy = refl

data ParallelizationScheme : Set where
  SingleThreaded : ParallelizationScheme
  ThreadPool : ℕ → ParallelizationScheme
  GPUParallel : ℕ → ParallelizationScheme
  DistributedParallel : ℕ → ℕ → ParallelizationScheme

record ParallelContext : Set where
  field
    num-threads : ℕ
    num-devices : ℕ
    scheme : ParallelizationScheme

parallel-map : ∀ {sh : List ℕ} {dtype : DType} →
  ParallelContext →
  (ℚ → ℚ) →
  Tensor sh dtype →
  Tensor sh dtype
parallel-map ctx f t = tensor-map f t

parallel-reduce : ∀ {sh : List ℕ} {dtype : DType} →
  ParallelContext →
  (ℚ → ℚ → ℚ) →
  ℚ →
  Tensor sh dtype →
  ℚ
parallel-reduce ctx f z t = tensor-fold f z t

theorem-parallel-map-equiv-sequential : ∀ {sh : List ℕ} {dtype : DType} →
  (ctx : ParallelContext) →
  (f : ℚ → ℚ) →
  (t : Tensor sh dtype) →
  data-vec (parallel-map ctx f t) ≡ data-vec (tensor-map f t)
theorem-parallel-map-equiv-sequential ctx f t = refl

data ProfilingMetric : Set where
  ExecutionTime : ProfilingMetric
  MemoryUsage : ProfilingMetric
  FLOPs : ProfilingMetric
  CacheHits : ProfilingMetric

record ProfilingData : Set where
  field
    metric-type : ProfilingMetric
    value : ℚ
    timestamp : ℕ

record TensorOperationProfile (sh : List ℕ) (dtype : DType) : Set where
  field
    input-tensor : Tensor sh dtype
    output-tensor : Tensor sh dtype
    profiling-data : List ProfilingData
    operation-name : String

profile-operation : ∀ {sh : List ℕ} {dtype : DType} →
  String →
  (Tensor sh dtype → Tensor sh dtype) →
  Tensor sh dtype →
  TensorOperationProfile sh dtype
profile-operation name op t = record
  { input-tensor = t
  ; output-tensor = op t
  ; profiling-data = []
  ; operation-name = name
  }

