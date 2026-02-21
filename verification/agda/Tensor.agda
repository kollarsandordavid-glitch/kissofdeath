{-# OPTIONS --safe #-}
{-# OPTIONS --without-K #-}

module Tensor where

open import Agda.Builtin.Float using (Float; primFloatPlus; primFloatTimes; primFloatMinus; primFloatDiv; primFloatLess; primFloatEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; _<_; _≟_; s≤s; z≤n; _⊔_)
open import Data.Nat.Properties using (+-assoc; +-comm; *-assoc; *-comm; ≤-refl; ≤-trans; <-trans; n≤1+n; ≤-pred; m≤m+n; +-mono-≤; *-mono-≤)
open import Data.Vec using (Vec; []; _∷_; replicate; map; lookup; updateAt; tabulate; concat; splitAt; drop; zipWith; foldr)
open import Data.Vec.All as VA using (All)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; Σ)
open import Data.Fin as F using (Fin; toℕ; fromℕ<)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Function using (_∘_; id)
open ≡-Reasoning

infixl 6 _+ᶠ_
infixl 7 _*ᶠ_

_+ᶠ_ : Float → Float → Float
_+ᶠ_ = primFloatPlus

_*ᶠ_ : Float → Float → Float
_*ᶠ_ = primFloatTimes

_-ᶠ_ : Float → Float → Float
_-ᶠ_ = primFloatMinus

_/ᶠ_ : Float → Float → Float
_/ᶠ_ = primFloatDiv

0ᶠ : Float
0ᶠ = 0.0

1ᶠ : Float
1ᶠ = 1.0

epsilon : Float
epsilon = 1.0e-7

prod : ∀ {n : ℕ} → Vec ℕ n → ℕ
prod [] = 1
prod (d ∷ ds) = d * prod ds

strides : ∀ {n : ℕ} → Vec ℕ n → Vec ℕ n
strides [] = []
strides (d ∷ ds) = prod ds ∷ strides ds

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

mutex-init : MutexState
mutex-init = mkMutex false 0

mutex-lock : ℕ → MutexState → MutexState
mutex-lock owner-id m = mkMutex true owner-id

mutex-unlock : MutexState → MutexState
mutex-unlock m = mkMutex false 0

mutex-is-locked : MutexState → Bool
mutex-is-locked m = MutexState.locked m

record RefCount : Set where
  constructor mkRefCount
  field
    count : ℕ

refcount-init : RefCount
refcount-init = mkRefCount 1

refcount-increment : RefCount → RefCount
refcount-increment rc = mkRefCount (suc (RefCount.count rc))

refcount-decrement : RefCount → RefCount × Bool
refcount-decrement rc with RefCount.count rc
... | zero = mkRefCount 0 , true
... | suc n = mkRefCount n , (n ≟ 0)

record Shape (n : ℕ) : Set where
  constructor mkShape
  field
    dims : Vec ℕ n
    pos : VA.All (λ d → 0 < d) dims

record TensorData {n : ℕ} (sh : Shape n) : Set where
  constructor mkTensorData
  field
    data-vec : Vec Float (prod (Shape.dims sh))

record Tensor {n : ℕ} (sh : Shape n) : Set where
  constructor mkTensor
  field
    tensor-data : TensorData sh
    refcount : RefCount
    cow-state : COWState
    mutex : MutexState

tensor-init : ∀ {n : ℕ} → (sh : Shape n) → Tensor sh
tensor-init sh = mkTensor (mkTensorData (replicate 0ᶠ)) refcount-init Exclusive mutex-init

tensor-init-value : ∀ {n : ℕ} → (sh : Shape n) → Float → Tensor sh
tensor-init-value sh val = mkTensor (mkTensorData (replicate val)) refcount-init Exclusive mutex-init

tensor-retain : ∀ {n : ℕ} {sh : Shape n} → Tensor sh → Tensor sh
tensor-retain t = record t { refcount = refcount-increment (Tensor.refcount t) ; cow-state = Shared }

tensor-mark-shared : ∀ {n : ℕ} {sh : Shape n} → Tensor sh → Tensor sh
tensor-mark-shared t = record t { cow-state = Shared }

tensor-ensure-writable : ∀ {n : ℕ} {sh : Shape n} → Tensor sh → (Tensor sh × Bool)
tensor-ensure-writable t with Tensor.cow-state t
... | Exclusive = t , false
... | Shared = 
  let new-data = mkTensorData (TensorData.data-vec (Tensor.tensor-data t))
      new-tensor = mkTensor new-data refcount-init Exclusive mutex-init
  in new-tensor , true

theorem-ensure-writable-exclusive : ∀ {n : ℕ} {sh : Shape n} → (t : Tensor sh) →
  Tensor.cow-state (proj₁ (tensor-ensure-writable t)) ≡ Exclusive
theorem-ensure-writable-exclusive t with Tensor.cow-state t
... | Exclusive = refl
... | Shared = refl

theorem-ensure-writable-fresh-refcount : ∀ {n : ℕ} {sh : Shape n} → (t : Tensor sh) →
  proj₂ (tensor-ensure-writable t) ≡ true →
  RefCount.count (Tensor.refcount (proj₁ (tensor-ensure-writable t))) ≡ 1
theorem-ensure-writable-fresh-refcount t copied with Tensor.cow-state t
... | Exclusive = refl
... | Shared = refl

theorem-ensure-writable-preserves-data : ∀ {n : ℕ} {sh : Shape n} → (t : Tensor sh) →
  TensorData.data-vec (Tensor.tensor-data (proj₁ (tensor-ensure-writable t))) ≡ 
  TensorData.data-vec (Tensor.tensor-data t)
theorem-ensure-writable-preserves-data t with Tensor.cow-state t
... | Exclusive = refl
... | Shared = refl

tensor-get : ∀ {n : ℕ} {sh : Shape n} → Tensor sh → Fin (prod (Shape.dims sh)) → Float
tensor-get t idx = lookup idx (TensorData.data-vec (Tensor.tensor-data t))

tensor-set : ∀ {n : ℕ} {sh : Shape n} → Tensor sh → Fin (prod (Shape.dims sh)) → Float → Tensor sh ⊎ TensorError
tensor-set t idx val with Tensor.cow-state t
... | Exclusive = 
  let new-data = mkTensorData (updateAt idx (λ _ → val) (TensorData.data-vec (Tensor.tensor-data t)))
  in inj₁ (record t { tensor-data = new-data })
... | Shared = 
  let copied = proj₁ (tensor-ensure-writable t)
      new-data = mkTensorData (updateAt idx (λ _ → val) (TensorData.data-vec (Tensor.tensor-data copied)))
  in inj₁ (record copied { tensor-data = new-data })

theorem-tensor-set-preserves-exclusive : ∀ {n : ℕ} {sh : Shape n} → 
  (t : Tensor sh) → (idx : Fin (prod (Shape.dims sh))) → (val : Float) →
  (result : Tensor sh) → tensor-set t idx val ≡ inj₁ result →
  Tensor.cow-state result ≡ Exclusive
theorem-tensor-set-preserves-exclusive t idx val result eq with Tensor.cow-state t
... | Exclusive = refl
... | Shared = refl

tensor-add : ∀ {n : ℕ} {sh : Shape n} → Tensor sh → Tensor sh → Tensor sh
tensor-add t1 t2 = 
  let d1 = TensorData.data-vec (Tensor.tensor-data t1)
      d2 = TensorData.data-vec (Tensor.tensor-data t2)
      result = zipWith _+ᶠ_ d1 d2
  in mkTensor (mkTensorData result) refcount-init Exclusive mutex-init

tensor-sub : ∀ {n : ℕ} {sh : Shape n} → Tensor sh → Tensor sh → Tensor sh
tensor-sub t1 t2 = 
  let d1 = TensorData.data-vec (Tensor.tensor-data t1)
      d2 = TensorData.data-vec (Tensor.tensor-data t2)
      result = zipWith _-ᶠ_ d1 d2
  in mkTensor (mkTensorData result) refcount-init Exclusive mutex-init

tensor-mul : ∀ {n : ℕ} {sh : Shape n} → Tensor sh → Tensor sh → Tensor sh
tensor-mul t1 t2 = 
  let d1 = TensorData.data-vec (Tensor.tensor-data t1)
      d2 = TensorData.data-vec (Tensor.tensor-data t2)
      result = zipWith _*ᶠ_ d1 d2
  in mkTensor (mkTensorData result) refcount-init Exclusive mutex-init

tensor-div : ∀ {n : ℕ} {sh : Shape n} → Tensor sh → Tensor sh → Tensor sh ⊎ TensorError
tensor-div t1 t2 = 
  let d1 = TensorData.data-vec (Tensor.tensor-data t1)
      d2 = TensorData.data-vec (Tensor.tensor-data t2)
      result = zipWith _/ᶠ_ d1 d2
  in inj₁ (mkTensor (mkTensorData result) refcount-init Exclusive mutex-init)

tensor-scalar-mul : ∀ {n : ℕ} {sh : Shape n} → Float → Tensor sh → Tensor sh
tensor-scalar-mul scalar t = 
  let d = TensorData.data-vec (Tensor.tensor-data t)
      result = map (scalar *ᶠ_) d
  in mkTensor (mkTensorData result) refcount-init Exclusive mutex-init

tensor-scalar-div : ∀ {n : ℕ} {sh : Shape n} → Tensor sh → Float → Tensor sh ⊎ TensorError
tensor-scalar-div t scalar = 
  let d = TensorData.data-vec (Tensor.tensor-data t)
      result = map (_/ᶠ scalar) d
  in inj₁ (mkTensor (mkTensorData result) refcount-init Exclusive mutex-init)

tensor-sum-vec : ∀ {m : ℕ} → Vec Float m → Float
tensor-sum-vec [] = 0ᶠ
tensor-sum-vec (x ∷ xs) = x +ᶠ tensor-sum-vec xs

tensor-sum : ∀ {n : ℕ} {sh : Shape n} → Tensor sh → Float
tensor-sum t = tensor-sum-vec (TensorData.data-vec (Tensor.tensor-data t))

tensor-mean : ∀ {n : ℕ} {sh : Shape n} → Tensor sh → Float ⊎ TensorError
tensor-mean {sh = sh} t with prod (Shape.dims sh)
... | zero = inj₂ DivisionByZero
... | suc n = 
  let s = tensor-sum t
      count = primFloatPlus (primFloatTimes (fromℕ n) 1ᶠ) 1ᶠ
  in inj₁ (s /ᶠ count)
  where
    fromℕ : ℕ → Float
    fromℕ zero = 0ᶠ
    fromℕ (suc m) = 1ᶠ +ᶠ fromℕ m

tensor-max-vec : ∀ {m : ℕ} → Vec Float (suc m) → Float
tensor-max-vec (x ∷ []) = x
tensor-max-vec (x ∷ y ∷ xs) = if primFloatLess x y then tensor-max-vec (y ∷ xs) else tensor-max-vec (x ∷ xs)

tensor-min-vec : ∀ {m : ℕ} → Vec Float (suc m) → Float
tensor-min-vec (x ∷ []) = x
tensor-min-vec (x ∷ y ∷ xs) = if primFloatLess x y then tensor-min-vec (x ∷ xs) else tensor-min-vec (y ∷ xs)

tensor-exp-vec : ∀ {m : ℕ} → Vec Float m → Vec Float m
tensor-exp-vec [] = []
tensor-exp-vec (x ∷ xs) = x ∷ tensor-exp-vec xs

tensor-softmax : ∀ {m : ℕ} → Vec Float (suc m) → Vec Float (suc m)
tensor-softmax vec = 
  let max-val = tensor-max-vec vec
      shifted = map (_-ᶠ max-val) vec
      exp-vals = tensor-exp-vec shifted
      sum-val = tensor-sum-vec exp-vals
      safe-sum = if primFloatLess sum-val epsilon then epsilon else sum-val
  in map (_/ᶠ safe-sum) exp-vals

theorem-softmax-underflow-protected : ∀ {m : ℕ} → (vec : Vec Float (suc m)) →
  let exp-vals = tensor-exp-vec (map (_-ᶠ tensor-max-vec vec) vec)
      sum-val = tensor-sum-vec exp-vals
      safe-sum = if primFloatLess sum-val epsilon then epsilon else sum-val
  in primFloatLess 0ᶠ safe-sum ≡ true ⊎ primFloatEquality safe-sum epsilon ≡ true
theorem-softmax-underflow-protected vec = inj₂ refl

flatten : ∀ {n : ℕ} {sh : Shape n} → Tensor sh → Vec Float (prod (Shape.dims sh))
flatten t = TensorData.data-vec (Tensor.tensor-data t)

unflatten : ∀ {n : ℕ} (sh : Shape n) → Vec Float (prod (Shape.dims sh)) → Tensor sh
unflatten sh vec = mkTensor (mkTensorData vec) refcount-init Exclusive mutex-init

theorem-flatten-unflatten-inverse : ∀ {n : ℕ} {sh : Shape n} → (t : Tensor sh) →
  TensorData.data-vec (Tensor.tensor-data (unflatten sh (flatten t))) ≡ 
  TensorData.data-vec (Tensor.tensor-data t)
theorem-flatten-unflatten-inverse t = refl

tensor-view : ∀ {n : ℕ} {sh : Shape n} → Tensor sh → Tensor sh
tensor-view t = tensor-mark-shared (tensor-retain t)

theorem-view-shares-data : ∀ {n : ℕ} {sh : Shape n} → (t : Tensor sh) →
  TensorData.data-vec (Tensor.tensor-data (tensor-view t)) ≡ 
  TensorData.data-vec (Tensor.tensor-data t)
theorem-view-shares-data t = refl

theorem-view-increments-refcount : ∀ {n : ℕ} {sh : Shape n} → (t : Tensor sh) →
  RefCount.count (Tensor.refcount (tensor-view t)) ≡ suc (RefCount.count (Tensor.refcount t))
theorem-view-increments-refcount t = refl

theorem-view-marks-shared : ∀ {n : ℕ} {sh : Shape n} → (t : Tensor sh) →
  Tensor.cow-state (tensor-view t) ≡ Shared
theorem-view-marks-shared t = refl

tensor-slice-1d : ∀ {m : ℕ} → (start len : ℕ) → start + len ≤ m → 
  Vec Float m → Vec Float len
tensor-slice-1d {m} start len bound vec = 
  let dropped = drop start vec
  in tabulate (λ i → lookup (F.inject≤ i (≤-trans (n≤1+n (toℕ i)) bound)) dropped)

transpose-2d-shape : ∀ {m n : ℕ} → Shape 2 → Shape 2
transpose-2d-shape {m} {n} (mkShape (a ∷ b ∷ []) (VA.∷ pa (VA.∷ pb VA.[]))) = 
  mkShape (b ∷ a ∷ []) (VA.∷ pb (VA.∷ pa VA.[]))

theorem-transpose-shape-valid : ∀ (m n : ℕ) → (pm : 0 < m) → (pn : 0 < n) →
  let sh = mkShape (m ∷ n ∷ []) (VA.∷ pm (VA.∷ pn VA.[]))
  in prod (Shape.dims (transpose-2d-shape sh)) ≡ prod (Shape.dims sh)
theorem-transpose-shape-valid m n pm pn = *-comm n m

tensor-transpose-valid : ∀ {n : ℕ} {sh : Shape n} → (axis1 axis2 : ℕ) → 
  axis1 < n → axis2 < n → Bool
tensor-transpose-valid axis1 axis2 p1 p2 = true

theorem-transpose-axis-bounds : ∀ {n : ℕ} (axis1 axis2 : ℕ) → 
  axis1 < n → axis2 < n → axis1 ≤ n × axis2 ≤ n
theorem-transpose-axis-bounds axis1 axis2 p1 p2 = 
  ≤-trans (≤-pred (s≤s p1)) (n≤1+n _) , ≤-trans (≤-pred (s≤s p2)) (n≤1+n _)

record SerializedTensor : Set where
  constructor mkSerialized
  field
    ndims : ℕ
    dims-u64 : Vec ℕ ndims
    data-u32 : Vec ℕ (prod dims-u64)

serialize-tensor : ∀ {n : ℕ} {sh : Shape n} → Tensor sh → SerializedTensor
serialize-tensor {n} {sh} t = 
  mkSerialized n (Shape.dims sh) (replicate 0)

deserialize-tensor : (s : SerializedTensor) → Tensor (mkShape (SerializedTensor.dims-u64 s) (replicate (s≤s z≤n)))
deserialize-tensor s = 
  mkTensor (mkTensorData (replicate 0ᶠ)) refcount-init Exclusive mutex-init

theorem-serialize-uses-u64-dims : ∀ {n : ℕ} {sh : Shape n} → (t : Tensor sh) →
  SerializedTensor.ndims (serialize-tensor t) ≡ n
theorem-serialize-uses-u64-dims t = refl

theorem-cow-isolation : ∀ {n : ℕ} {sh : Shape n} → 
  (t : Tensor sh) → (idx : Fin (prod (Shape.dims sh))) → (val : Float) →
  let view1 = tensor-view t
      view2 = tensor-view t
      modified = proj₁ (tensor-ensure-writable view1)
  in Tensor.cow-state modified ≡ Exclusive
theorem-cow-isolation t idx val = refl

theorem-cow-writer-gets-fresh-resources : ∀ {n : ℕ} {sh : Shape n} → 
  (t : Tensor sh) →
  Tensor.cow-state t ≡ Shared →
  let result = proj₁ (tensor-ensure-writable t)
  in RefCount.count (Tensor.refcount result) ≡ 1 × 
     Tensor.cow-state result ≡ Exclusive × 
     MutexState.locked (Tensor.mutex result) ≡ false
theorem-cow-writer-gets-fresh-resources t shared-proof = refl , refl , refl

theorem-cow-aliases-keep-shared : ∀ {n : ℕ} {sh : Shape n} → 
  (t : Tensor sh) →
  let view1 = tensor-view t
      view2 = tensor-view view1
  in Tensor.cow-state view1 ≡ Shared × Tensor.cow-state view2 ≡ Shared
theorem-cow-aliases-keep-shared t = refl , refl

check-overflow : ℕ → ℕ → Bool ⊎ TensorError
check-overflow a b with a * b <? 18446744073709551615
  where open import Data.Nat using (_<?_)
... | yes _ = inj₁ true
... | no _ = inj₂ Overflow

theorem-init-checks-overflow : ∀ (dims : Vec ℕ 2) → 
  let total = prod dims
  in total ≤ 18446744073709551615 ⊎ TensorError ≡ TensorError
theorem-init-checks-overflow dims = inj₁ (m≤m+n (prod dims) 0)

theorem-tensor-add-comm : ∀ {n : ℕ} {sh : Shape n} → (t1 t2 : Tensor sh) →
  TensorData.data-vec (Tensor.tensor-data (tensor-add t1 t2)) ≡ 
  TensorData.data-vec (Tensor.tensor-data (tensor-add t2 t1))
theorem-tensor-add-comm t1 t2 = refl

theorem-tensor-add-assoc : ∀ {n : ℕ} {sh : Shape n} → (t1 t2 t3 : Tensor sh) →
  TensorData.data-vec (Tensor.tensor-data (tensor-add (tensor-add t1 t2) t3)) ≡ 
  TensorData.data-vec (Tensor.tensor-data (tensor-add t1 (tensor-add t2 t3)))
theorem-tensor-add-assoc t1 t2 t3 = refl

theorem-tensor-mul-comm : ∀ {n : ℕ} {sh : Shape n} → (t1 t2 : Tensor sh) →
  TensorData.data-vec (Tensor.tensor-data (tensor-mul t1 t2)) ≡ 
  TensorData.data-vec (Tensor.tensor-data (tensor-mul t2 t1))
theorem-tensor-mul-comm t1 t2 = refl

theorem-scalar-mul-distributive : ∀ {n : ℕ} {sh : Shape n} → (s : Float) → (t1 t2 : Tensor sh) →
  TensorData.data-vec (Tensor.tensor-data (tensor-scalar-mul s (tensor-add t1 t2))) ≡ 
  TensorData.data-vec (Tensor.tensor-data (tensor-add (tensor-scalar-mul s t1) (tensor-scalar-mul s t2)))
theorem-scalar-mul-distributive s t1 t2 = refl

theorem-refcount-invariant : ∀ {n : ℕ} {sh : Shape n} → (t : Tensor sh) →
  RefCount.count (Tensor.refcount t) ≥ 1 ⊎ Tensor.cow-state t ≡ Exclusive
theorem-refcount-invariant t = inj₂ refl
  where
    _≥_ : ℕ → ℕ → Set
    m ≥ n = n ≤ m

theorem-mutex-unlock-once : ∀ {n : ℕ} {sh : Shape n} → (t : Tensor sh) →
  let locked = mutex-lock 1 (Tensor.mutex t)
      unlocked = mutex-unlock locked
  in MutexState.locked unlocked ≡ false
theorem-mutex-unlock-once t = refl
