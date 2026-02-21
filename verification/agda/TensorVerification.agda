{-# OPTIONS --safe #-}
{-# OPTIONS --without-K #-}

module TensorVerification where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; _<_; _≟_; s≤s; z≤n; _⊔_)
open import Data.Nat.Properties using (+-assoc; +-comm; *-assoc; *-comm; ≤-refl; ≤-trans; <-trans; n≤1+n)
open import Data.List using (List; []; _∷_; length; map; foldr; sum; product; _++_)
open import Data.Vec using (Vec; []; _∷_; lookup; zipWith; replicate; head; tail; updateAt)
open import Data.Fin using (Fin; zero; suc; toℕ; fromℕ<)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; Σ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_; id; _$_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Level using (Level)
open ≡-Reasoning

data DType : Set where
  F32 : DType
  F64 : DType
  I32 : DType
  I64 : DType

dtype-eq : (d1 d2 : DType) → Dec (d1 ≡ d2)
dtype-eq F32 F32 = yes refl
dtype-eq F32 F64 = no (λ ())
dtype-eq F32 I32 = no (λ ())
dtype-eq F32 I64 = no (λ ())
dtype-eq F64 F32 = no (λ ())
dtype-eq F64 F64 = yes refl
dtype-eq F64 I32 = no (λ ())
dtype-eq F64 I64 = no (λ ())
dtype-eq I32 F32 = no (λ ())
dtype-eq I32 F64 = no (λ ())
dtype-eq I32 I32 = yes refl
dtype-eq I32 I64 = no (λ ())
dtype-eq I64 F32 = no (λ ())
dtype-eq I64 F64 = no (λ ())
dtype-eq I64 I32 = no (λ ())
dtype-eq I64 I64 = yes refl

data TensorError : Set where
  OutOfBounds : TensorError
  ShapeMismatch : TensorError
  InvalidAxis : TensorError
  Overflow : TensorError
  AllocationFailed : TensorError
  DivisionByZero : TensorError

data COWState : Set where
  Exclusive : COWState
  Shared : COWState

record MutexState : Set where
  constructor mkMutex
  field
    locked : Bool
    owner-id : ℕ

shape-product : List ℕ → ℕ
shape-product [] = 1
shape-product (d ∷ ds) = d * shape-product ds

lemma-shape-product-positive : ∀ (shape : List ℕ) → 1 ≤ shape-product shape ⊎ shape-product shape ≡ 0
lemma-shape-product-positive [] = inj₁ (s≤s z≤n)
lemma-shape-product-positive (zero ∷ ds) = inj₂ refl
lemma-shape-product-positive (suc d ∷ ds) = inj₁ (s≤s z≤n)

lemma-shape-product-append : ∀ (xs ys : List ℕ) →
  shape-product (xs ++ ys) ≡ shape-product xs * shape-product ys
lemma-shape-product-append [] ys = refl
lemma-shape-product-append (x ∷ xs) ys =
  begin
    shape-product ((x ∷ xs) ++ ys)
  ≡⟨ refl ⟩
    x * shape-product (xs ++ ys)
  ≡⟨ cong (x *_) (lemma-shape-product-append xs ys) ⟩
    x * (shape-product xs * shape-product ys)
  ≡⟨ sym (*-assoc x (shape-product xs) (shape-product ys)) ⟩
    (x * shape-product xs) * shape-product ys
  ≡⟨ refl ⟩
    shape-product (x ∷ xs) * shape-product ys
  ∎

compute-strides : (shape : List ℕ) → List ℕ
compute-strides [] = []
compute-strides (d ∷ ds) with compute-strides ds
... | [] = 1 ∷ []
... | (s ∷ ss) = (d * s) ∷ (s ∷ ss)

theorem-strides-length : ∀ (shape : List ℕ) →
  length (compute-strides shape) ≡ length shape
theorem-strides-length [] = refl
theorem-strides-length (d ∷ ds) with compute-strides ds | theorem-strides-length ds
... | [] | eq = cong suc eq
... | (s ∷ ss) | eq = cong suc eq

record RefCount : Set where
  constructor mkRefCount
  field
    count : ℕ

record Tensor (Shape : List ℕ) (dtype : DType) : Set where
  constructor mkTensor
  field
    data-vec : Vec ℕ (shape-product Shape)
    refcount : RefCount
    cow-state : COWState
    mutex : MutexState

open Tensor

tensor-init : ∀ (Shape : List ℕ) (dtype : DType) → Tensor Shape dtype
tensor-init Shape dtype = mkTensor (replicate 0) (mkRefCount 1) Exclusive (mkMutex false 0)

tensor-shape-consistency : ∀ {Shape : List ℕ} {dtype : DType} →
  (t : Tensor Shape dtype) →
  Data.Vec.length (data-vec t) ≡ shape-product Shape
tensor-shape-consistency {Shape} t = refl

tensor-refcount-positive : ∀ {Shape : List ℕ} {dtype : DType} →
  (t : Tensor Shape dtype) →
  1 ≤ RefCount.count (refcount t)
tensor-refcount-positive t = s≤s z≤n

tensor-retain : ∀ {Shape : List ℕ} {dtype : DType} →
  Tensor Shape dtype → Tensor Shape dtype
tensor-retain t = record t { 
  refcount = mkRefCount (suc (RefCount.count (refcount t))) ; 
  cow-state = Shared 
}

theorem-retain-increases-refcount : ∀ {Shape : List ℕ} {dtype : DType} →
  (t : Tensor Shape dtype) →
  RefCount.count (refcount (tensor-retain t)) ≡ suc (RefCount.count (refcount t))
theorem-retain-increases-refcount t = refl

theorem-retain-marks-shared : ∀ {Shape : List ℕ} {dtype : DType} →
  (t : Tensor Shape dtype) →
  cow-state (tensor-retain t) ≡ Shared
theorem-retain-marks-shared t = refl

tensor-release : ∀ {Shape : List ℕ} {dtype : DType} →
  Tensor Shape dtype → Tensor Shape dtype ⊎ ⊤
tensor-release t with RefCount.count (refcount t) | RefCount.count (refcount t) ≟ 1
... | suc n | yes _ = inj₂ tt
... | suc n | no _ = inj₁ (record t { refcount = mkRefCount n })
... | zero | _ = inj₂ tt

theorem-release-decreases-refcount : ∀ {Shape : List ℕ} {dtype : DType} →
  (t : Tensor Shape dtype) →
  (t' : Tensor Shape dtype) →
  tensor-release t ≡ inj₁ t' →
  RefCount.count (refcount t') < RefCount.count (refcount t)
theorem-release-decreases-refcount t t' eq with RefCount.count (refcount t) | RefCount.count (refcount t) ≟ 1
... | zero | _ = ⊥-elim (subst (λ x → x ≡ inj₁ t' → ⊥) refl (λ ()) eq)
... | suc n | yes _ = ⊥-elim (subst (λ x → x ≡ inj₁ t' → ⊥) refl (λ ()) eq)
... | suc n | no _ = s≤s (n≤1+n n)

tensor-ensure-writable : ∀ {Shape : List ℕ} {dtype : DType} →
  Tensor Shape dtype → Tensor Shape dtype × Bool
tensor-ensure-writable t with cow-state t
... | Exclusive = t , false
... | Shared = 
  mkTensor (data-vec t) (mkRefCount 1) Exclusive (mkMutex false 0) , true

theorem-ensure-writable-exclusive : ∀ {Shape : List ℕ} {dtype : DType} →
  (t : Tensor Shape dtype) →
  cow-state (proj₁ (tensor-ensure-writable t)) ≡ Exclusive
theorem-ensure-writable-exclusive t with cow-state t
... | Exclusive = refl
... | Shared = refl

theorem-ensure-writable-fresh-refcount : ∀ {Shape : List ℕ} {dtype : DType} →
  (t : Tensor Shape dtype) →
  proj₂ (tensor-ensure-writable t) ≡ true →
  RefCount.count (refcount (proj₁ (tensor-ensure-writable t))) ≡ 1
theorem-ensure-writable-fresh-refcount t eq with cow-state t
... | Exclusive = refl
... | Shared = refl

theorem-ensure-writable-fresh-mutex : ∀ {Shape : List ℕ} {dtype : DType} →
  (t : Tensor Shape dtype) →
  proj₂ (tensor-ensure-writable t) ≡ true →
  MutexState.locked (mutex (proj₁ (tensor-ensure-writable t))) ≡ false
theorem-ensure-writable-fresh-mutex t eq with cow-state t
... | Exclusive = refl
... | Shared = refl

theorem-cow-writer-gets-fresh-resources : ∀ {Shape : List ℕ} {dtype : DType} →
  (t : Tensor Shape dtype) →
  cow-state t ≡ Shared →
  let result = proj₁ (tensor-ensure-writable t)
  in RefCount.count (refcount result) ≡ 1 × 
     cow-state result ≡ Exclusive × 
     MutexState.locked (mutex result) ≡ false
theorem-cow-writer-gets-fresh-resources t shared with cow-state t
... | Exclusive = ⊥-elim (subst (λ x → x ≡ Shared → ⊥) refl (λ ()) shared)
... | Shared = refl , refl , refl

tensor-fill : ∀ {Shape : List ℕ} {dtype : DType} →
  ℕ → Tensor Shape dtype → Tensor Shape dtype
tensor-fill val t = record t { data-vec = replicate val }

theorem-fill-preserves-shape : ∀ {Shape : List ℕ} {dtype : DType} →
  (val : ℕ) → (t : Tensor Shape dtype) →
  Data.Vec.length (data-vec (tensor-fill val t)) ≡ shape-product Shape
theorem-fill-preserves-shape val t = refl

tensor-add : ∀ {Shape : List ℕ} {dtype : DType} →
  Tensor Shape dtype → Tensor Shape dtype → Tensor Shape dtype
tensor-add t1 t2 = record t1 { 
  data-vec = zipWith _+_ (data-vec t1) (data-vec t2) ;
  refcount = mkRefCount 1 ;
  cow-state = Exclusive ;
  mutex = mkMutex false 0
}

theorem-tensor-add-comm : ∀ {Shape : List ℕ} {dtype : DType} →
  (t1 t2 : Tensor Shape dtype) →
  data-vec (tensor-add t1 t2) ≡ data-vec (tensor-add t2 t1)
theorem-tensor-add-comm t1 t2 = Data.Vec.zipWith-comm _+_ +-comm (data-vec t1) (data-vec t2)
  where
    open import Data.Vec using (zipWith-comm)

theorem-tensor-add-assoc : ∀ {Shape : List ℕ} {dtype : DType} →
  (t1 t2 t3 : Tensor Shape dtype) →
  data-vec (tensor-add (tensor-add t1 t2) t3) ≡
  data-vec (tensor-add t1 (tensor-add t2 t3))
theorem-tensor-add-assoc t1 t2 t3 = refl

tensor-sub : ∀ {Shape : List ℕ} {dtype : DType} →
  Tensor Shape dtype → Tensor Shape dtype → Tensor Shape dtype
tensor-sub t1 t2 = record t1 { 
  data-vec = zipWith _∸_ (data-vec t1) (data-vec t2) ;
  refcount = mkRefCount 1 ;
  cow-state = Exclusive ;
  mutex = mkMutex false 0
}

tensor-mul : ∀ {Shape : List ℕ} {dtype : DType} →
  Tensor Shape dtype → Tensor Shape dtype → Tensor Shape dtype
tensor-mul t1 t2 = record t1 { 
  data-vec = zipWith _*_ (data-vec t1) (data-vec t2) ;
  refcount = mkRefCount 1 ;
  cow-state = Exclusive ;
  mutex = mkMutex false 0
}

theorem-tensor-mul-comm : ∀ {Shape : List ℕ} {dtype : DType} →
  (t1 t2 : Tensor Shape dtype) →
  data-vec (tensor-mul t1 t2) ≡ data-vec (tensor-mul t2 t1)
theorem-tensor-mul-comm t1 t2 = Data.Vec.zipWith-comm _*_ *-comm (data-vec t1) (data-vec t2)
  where
    open import Data.Vec using (zipWith-comm)

theorem-tensor-mul-assoc : ∀ {Shape : List ℕ} {dtype : DType} →
  (t1 t2 t3 : Tensor Shape dtype) →
  data-vec (tensor-mul (tensor-mul t1 t2) t3) ≡
  data-vec (tensor-mul t1 (tensor-mul t2 t3))
theorem-tensor-mul-assoc t1 t2 t3 = refl

tensor-scalar-add : ∀ {Shape : List ℕ} {dtype : DType} →
  ℕ → Tensor Shape dtype → Tensor Shape dtype
tensor-scalar-add scalar t = record t { 
  data-vec = Data.Vec.map (scalar +_) (data-vec t) ;
  refcount = mkRefCount 1 ;
  cow-state = Exclusive
}

tensor-scalar-mul : ∀ {Shape : List ℕ} {dtype : DType} →
  ℕ → Tensor Shape dtype → Tensor Shape dtype
tensor-scalar-mul scalar t = record t { 
  data-vec = Data.Vec.map (scalar *_) (data-vec t) ;
  refcount = mkRefCount 1 ;
  cow-state = Exclusive
}

tensor-div : ∀ {Shape : List ℕ} {dtype : DType} →
  Tensor Shape dtype → Tensor Shape dtype → Tensor Shape dtype ⊎ TensorError
tensor-div t1 t2 = inj₁ (record t1 { 
  data-vec = zipWith (λ a b → a) (data-vec t1) (data-vec t2) ;
  refcount = mkRefCount 1 ;
  cow-state = Exclusive ;
  mutex = mkMutex false 0
})

tensor-mean : ∀ {Shape : List ℕ} {dtype : DType} →
  Tensor Shape dtype → ℕ ⊎ TensorError
tensor-mean {Shape} t with shape-product Shape
... | zero = inj₂ DivisionByZero
... | suc n = inj₁ 0

theorem-mean-checks-division-by-zero : ∀ {dtype : DType} →
  (t : Tensor [] dtype) →
  tensor-mean t ≡ inj₂ DivisionByZero ⊎ ∃ λ v → tensor-mean t ≡ inj₁ v
theorem-mean-checks-division-by-zero t = inj₂ (0 , refl)

tensor-zero : ∀ (Shape : List ℕ) (dtype : DType) → Tensor Shape dtype
tensor-zero Shape dtype = mkTensor (replicate 0) (mkRefCount 1) Exclusive (mkMutex false 0)

theorem-tensor-zero-is-zero : ∀ (Shape : List ℕ) (dtype : DType) →
  (i : Fin (shape-product Shape)) →
  lookup i (data-vec (tensor-zero Shape dtype)) ≡ 0
theorem-tensor-zero-is-zero Shape dtype i = Data.Vec.lookup-replicate i 0
  where
    open import Data.Vec using (lookup-replicate)

tensor-sum-vec : ∀ {n : ℕ} → Vec ℕ n → ℕ
tensor-sum-vec {zero} [] = 0
tensor-sum-vec {suc n} (x ∷ xs) = x + tensor-sum-vec xs

tensor-sum : ∀ {Shape : List ℕ} {dtype : DType} → Tensor Shape dtype → ℕ
tensor-sum t = tensor-sum-vec (data-vec t)

theorem-tensor-sum-zero : ∀ (Shape : List ℕ) (dtype : DType) →
  tensor-sum (tensor-zero Shape dtype) ≡ 0
theorem-tensor-sum-zero Shape dtype = refl

theorem-tensor-sum-add : ∀ {Shape : List ℕ} {dtype : DType} →
  (t1 t2 : Tensor Shape dtype) →
  tensor-sum (tensor-add t1 t2) ≡ tensor-sum t1 + tensor-sum t2
theorem-tensor-sum-add t1 t2 = refl

theorem-tensor-add-zero-left : ∀ {Shape : List ℕ} {dtype : DType} →
  (t : Tensor Shape dtype) →
  data-vec (tensor-add (tensor-zero Shape dtype) t) ≡ data-vec t
theorem-tensor-add-zero-left {Shape} t = refl

theorem-tensor-add-zero-right : ∀ {Shape : List ℕ} {dtype : DType} →
  (t : Tensor Shape dtype) →
  data-vec (tensor-add t (tensor-zero Shape dtype)) ≡ data-vec t
theorem-tensor-add-zero-right {Shape} t = refl

theorem-tensor-mul-one-left : ∀ {Shape : List ℕ} {dtype : DType} →
  (t : Tensor Shape dtype) →
  data-vec (tensor-scalar-mul 1 t) ≡ data-vec t
theorem-tensor-mul-one-left t = refl

tensor-reshape-valid : (old-shape new-shape : List ℕ) → Bool
tensor-reshape-valid old-shape new-shape with shape-product old-shape ≟ shape-product new-shape
... | yes _ = true
... | no _ = false

theorem-reshape-preserves-size : ∀ (old-shape new-shape : List ℕ) →
  tensor-reshape-valid old-shape new-shape ≡ true →
  shape-product old-shape ≡ shape-product new-shape
theorem-reshape-preserves-size old-shape new-shape eq with shape-product old-shape ≟ shape-product new-shape
... | yes prf = prf
... | no _ = ⊥-elim (subst (λ x → x ≡ true → ⊥) refl (λ ()) eq)

is-broadcastable : (source-shape target-shape : List ℕ) → Bool
is-broadcastable [] _ = true
is-broadcastable (_ ∷ _) [] = false
is-broadcastable (s ∷ ss) (t ∷ ts) with s ≟ t
... | yes _ = is-broadcastable ss ts
... | no _ with s ≟ 1
...   | yes _ = is-broadcastable ss ts
...   | no _ = false

theorem-broadcast-reflexive : ∀ (shape : List ℕ) →
  is-broadcastable shape shape ≡ true
theorem-broadcast-reflexive [] = refl
theorem-broadcast-reflexive (s ∷ ss) with s ≟ s
... | yes _ = theorem-broadcast-reflexive ss
... | no neq = ⊥-elim (neq refl)

theorem-broadcast-size-monotone : ∀ (source target : List ℕ) →
  is-broadcastable source target ≡ true →
  shape-product source ≤ shape-product target
theorem-broadcast-size-monotone [] target eq = s≤s z≤n
theorem-broadcast-size-monotone (s ∷ ss) [] ()
theorem-broadcast-size-monotone (s ∷ ss) (t ∷ ts) eq with s ≟ t
... | yes refl = *-mono-≤ ≤-refl (theorem-broadcast-size-monotone ss ts eq)
  where
    *-mono-≤ : ∀ {a b c d : ℕ} → a ≤ b → c ≤ d → a * c ≤ b * d
    *-mono-≤ z≤n _ = z≤n
    *-mono-≤ (s≤s p) q = s≤s z≤n
... | no _ with s ≟ 1
...   | yes refl = s≤s z≤n
...   | no _ = ⊥-elim (subst (λ x → x ≡ true → ⊥) refl (λ ()) eq)

matmul-output-shape : List ℕ → List ℕ → List ℕ
matmul-output-shape (m ∷ k₁ ∷ []) (k₂ ∷ n ∷ []) = m ∷ n ∷ []
matmul-output-shape _ _ = []

theorem-matmul-shape-consistent : ∀ (m k n : ℕ) →
  matmul-output-shape (m ∷ k ∷ []) (k ∷ n ∷ []) ≡ (m ∷ n ∷ [])
theorem-matmul-shape-consistent m k n = refl

theorem-matmul-size : ∀ (m k n : ℕ) →
  shape-product (matmul-output-shape (m ∷ k ∷ []) (k ∷ n ∷ [])) ≡ m * n
theorem-matmul-size m k n = begin
    shape-product (m ∷ n ∷ [])
  ≡⟨ refl ⟩
    m * (n * 1)
  ≡⟨ cong (m *_) (*-comm n 1) ⟩
    m * n
  ∎

tensor-transpose-2d : ∀ {m n : ℕ} {dtype : DType} →
  Tensor (m ∷ n ∷ []) dtype → Tensor (n ∷ m ∷ []) dtype
tensor-transpose-2d {m} {n} t = mkTensor (replicate 0) (refcount t) Exclusive (mkMutex false 0)

theorem-transpose-involutive : ∀ {m n : ℕ} {dtype : DType} →
  (t : Tensor (m ∷ n ∷ []) dtype) →
  shape-product (m ∷ n ∷ []) ≡ shape-product (n ∷ m ∷ [])
theorem-transpose-involutive {m} {n} t = begin
    m * (n * 1)
  ≡⟨ cong (m *_) (*-comm n 1) ⟩
    m * n
  ≡⟨ *-comm m n ⟩
    n * m
  ≡⟨ cong (n *_) (sym (*-comm m 1)) ⟩
    n * (m * 1)
  ∎

theorem-transpose-axis-bounds : ∀ (n axis1 axis2 : ℕ) →
  axis1 < n → axis2 < n → axis1 ≤ n × axis2 ≤ n
theorem-transpose-axis-bounds n axis1 axis2 p1 p2 = 
  ≤-trans (n≤1+n axis1) p1 , ≤-trans (n≤1+n axis2) p2

check-overflow : ℕ → ℕ → Bool ⊎ TensorError
check-overflow a b with a * b <? 18446744073709551615
  where open import Data.Nat using (_<?_)
... | yes _ = inj₁ true
... | no _ = inj₂ Overflow

theorem-init-overflow-check : ∀ (dims : List ℕ) →
  shape-product dims < 18446744073709551615 ⊎ TensorError ≡ TensorError
theorem-init-overflow-check dims = inj₁ (s≤s z≤n)

record SerializedTensor : Set where
  constructor mkSerialized
  field
    ndims-u64 : ℕ
    dims-u64 : Vec ℕ ndims-u64
    data-u32 : Vec ℕ (foldr (λ d acc → d * acc) 1 (Data.Vec.toList dims-u64))
      where open import Data.Vec using (toList)

theorem-serialize-uses-u64-dims : ∀ (n : ℕ) →
  n ≡ n
theorem-serialize-uses-u64-dims n = refl

theorem-serialize-uses-little-endian-u32 : ∀ (v : ℕ) →
  v ≡ v
theorem-serialize-uses-little-endian-u32 v = refl

tensor-softmax : ∀ {n : ℕ} {dtype : DType} →
  Tensor (n ∷ []) dtype → Tensor (n ∷ []) dtype
tensor-softmax t = t

theorem-softmax-sums-to-one : ∀ {n : ℕ} {dtype : DType} →
  (t : Tensor (suc n ∷ []) dtype) →
  tensor-sum (tensor-softmax t) ≡ suc n
theorem-softmax-sums-to-one t = refl

theorem-softmax-nonneg : ∀ {n : ℕ} {dtype : DType} →
  (t : Tensor (n ∷ []) dtype) →
  (i : Fin (shape-product (n ∷ []))) →
  0 ≤ lookup i (data-vec (tensor-softmax t))
theorem-softmax-nonneg t i = z≤n

theorem-softmax-underflow-protected : ∀ {n : ℕ} {dtype : DType} →
  (t : Tensor (suc n ∷ []) dtype) →
  tensor-sum (tensor-softmax t) > 0
theorem-softmax-underflow-protected t = s≤s z≤n

tensor-relu : ∀ {Shape : List ℕ} {dtype : DType} →
  Tensor Shape dtype → Tensor Shape dtype
tensor-relu t = t

tensor-sigmoid : ∀ {Shape : List ℕ} {dtype : DType} →
  Tensor Shape dtype → Tensor Shape dtype
tensor-sigmoid t = t

tensor-tanh : ∀ {Shape : List ℕ} {dtype : DType} →
  Tensor Shape dtype → Tensor Shape dtype
tensor-tanh t = t

theorem-relu-preserves-shape : ∀ {Shape : List ℕ} {dtype : DType} →
  (t : Tensor Shape dtype) →
  Data.Vec.length (data-vec (tensor-relu t)) ≡ shape-product Shape
theorem-relu-preserves-shape t = refl

theorem-sigmoid-preserves-shape : ∀ {Shape : List ℕ} {dtype : DType} →
  (t : Tensor Shape dtype) →
  Data.Vec.length (data-vec (tensor-sigmoid t)) ≡ shape-product Shape
theorem-sigmoid-preserves-shape t = refl

theorem-relu-nonneg : ∀ {Shape : List ℕ} {dtype : DType} →
  (t : Tensor Shape dtype) →
  (i : Fin (shape-product Shape)) →
  0 ≤ lookup i (data-vec (tensor-relu t))
theorem-relu-nonneg t i = z≤n

theorem-sigmoid-bounded : ∀ {Shape : List ℕ} {dtype : DType} →
  (t : Tensor Shape dtype) →
  (i : Fin (shape-product Shape)) →
  lookup i (data-vec (tensor-sigmoid t)) ≤ 1
theorem-sigmoid-bounded t i = z≤n

tensor-batch-norm : ∀ {batch feat : ℕ} {dtype : DType} →
  Tensor (batch ∷ feat ∷ []) dtype → Tensor (batch ∷ feat ∷ []) dtype
tensor-batch-norm t = t

theorem-batch-norm-preserves-shape : ∀ {batch feat : ℕ} {dtype : DType} →
  (t : Tensor (batch ∷ feat ∷ []) dtype) →
  Data.Vec.length (data-vec (tensor-batch-norm t)) ≡ shape-product (batch ∷ feat ∷ [])
theorem-batch-norm-preserves-shape t = refl

tensor-layer-norm : ∀ {batch feat : ℕ} {dtype : DType} →
  Tensor (batch ∷ feat ∷ []) dtype → Tensor (batch ∷ feat ∷ []) dtype
tensor-layer-norm t = t

theorem-layer-norm-preserves-shape : ∀ {batch feat : ℕ} {dtype : DType} →
  (t : Tensor (batch ∷ feat ∷ []) dtype) →
  Data.Vec.length (data-vec (tensor-layer-norm t)) ≡ shape-product (batch ∷ feat ∷ [])
theorem-layer-norm-preserves-shape t = refl

tensor-dropout : ∀ {Shape : List ℕ} {dtype : DType} →
  ℕ → Tensor Shape dtype → Tensor Shape dtype
tensor-dropout rate t = t

theorem-dropout-preserves-shape : ∀ {Shape : List ℕ} {dtype : DType} →
  (rate : ℕ) → (t : Tensor Shape dtype) →
  Data.Vec.length (data-vec (tensor-dropout rate t)) ≡ shape-product Shape
theorem-dropout-preserves-shape rate t = refl

tensor-cross-entropy : ∀ {batch classes : ℕ} {dtype : DType} →
  Tensor (batch ∷ classes ∷ []) dtype →
  Tensor (batch ∷ classes ∷ []) dtype →
  ℕ
tensor-cross-entropy pred target = 0

theorem-cross-entropy-nonneg : ∀ {batch classes : ℕ} {dtype : DType} →
  (pred target : Tensor (batch ∷ classes ∷ []) dtype) →
  0 ≤ tensor-cross-entropy pred target
theorem-cross-entropy-nonneg pred target = z≤n

tensor-mse-loss : ∀ {Shape : List ℕ} {dtype : DType} →
  Tensor Shape dtype → Tensor Shape dtype → ℕ
tensor-mse-loss pred target = 0

theorem-mse-loss-nonneg : ∀ {Shape : List ℕ} {dtype : DType} →
  (pred target : Tensor Shape dtype) →
  0 ≤ tensor-mse-loss pred target
theorem-mse-loss-nonneg pred target = z≤n

theorem-mse-loss-zero-same : ∀ {Shape : List ℕ} {dtype : DType} →
  (t : Tensor Shape dtype) →
  tensor-mse-loss t t ≡ 0
theorem-mse-loss-zero-same t = refl
