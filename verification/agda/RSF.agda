{-# OPTIONS --safe #-}
{-# OPTIONS --without-K #-}

module RSF where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; _<_; _≟_; s≤s; z≤n; _/_)
open import Data.Nat.Properties using (+-assoc; +-comm; *-assoc; *-comm; ≤-refl; ≤-trans; <-trans; n≤1+n)
open import Data.List using (List; []; _∷_; length; map; foldr)
open import Data.Vec using (Vec; []; _∷_; lookup; zipWith; replicate; head; tail)
open import Data.Fin using (Fin; zero; suc; toℕ; fromℕ<)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; Σ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_; id)
open import Data.Empty using (⊥; ⊥-elim)
open import Tensor
open ≡-Reasoning

record RSFLayerWeights (dim : ℕ) : Set where
  constructor mkRSFLayerWeights
  field
    s-weight : Vec ℕ (dim * dim)
    t-weight : Vec ℕ (dim * dim)
    s-bias : Vec ℕ dim
    t-bias : Vec ℕ dim

RSFLayer-init : (dim : ℕ) → RSFLayerWeights dim
RSFLayer-init dim = mkRSFLayerWeights 
  (Data.Vec.replicate 0)
  (Data.Vec.replicate 0)
  (Data.Vec.replicate 0)
  (Data.Vec.replicate 0)

record RSFLayerGradients (dim : ℕ) : Set where
  constructor mkRSFLayerGradients
  field
    s-weight-grad : Vec ℕ (dim * dim)
    t-weight-grad : Vec ℕ (dim * dim)
    s-bias-grad : Vec ℕ dim
    t-bias-grad : Vec ℕ dim

RSFGradients-init : (dim : ℕ) → RSFLayerGradients dim
RSFGradients-init dim = mkRSFLayerGradients
  (Data.Vec.replicate 0)
  (Data.Vec.replicate 0)
  (Data.Vec.replicate 0)
  (Data.Vec.replicate 0)

record RSFLayerState (dim : ℕ) : Set where
  constructor mkRSFLayerState
  field
    weights : RSFLayerWeights dim
    gradients : RSFLayerGradients dim

RSFLayerState-init : (dim : ℕ) → RSFLayerState dim
RSFLayerState-init dim = mkRSFLayerState (RSFLayer-init dim) (RSFGradients-init dim)

matrix-vector-mul : ∀ {rows cols : ℕ} → Vec ℕ (rows * cols) → Vec ℕ cols → Vec ℕ rows
matrix-vector-mul {zero} {cols} mat vec = []
matrix-vector-mul {suc rows} {cols} mat vec = 
  let row = Data.Vec.take cols mat
      rest = Data.Vec.drop cols mat
      dot = Data.Vec.foldr _ _+_ 0 (zipWith _*_ row vec)
  in dot ∷ matrix-vector-mul rest vec

vector-add : ∀ {n : ℕ} → Vec ℕ n → Vec ℕ n → Vec ℕ n
vector-add = zipWith _+_

vector-mul : ∀ {n : ℕ} → Vec ℕ n → Vec ℕ n → Vec ℕ n
vector-mul = zipWith _*_

clamp : ℕ → ℕ → ℕ → ℕ
clamp x min-val max-val with x <? min-val
... | yes _ = min-val
... | no _ with max-val <? x
...   | yes _ = max-val
...   | no _ = x

vector-exp : ∀ {n : ℕ} → Vec ℕ n → Vec ℕ n
vector-exp vec = Data.Vec.map (λ x → 2) vec

rsf-forward-scatter : ∀ {dim : ℕ} → RSFLayerWeights dim → Vec ℕ dim → Vec ℕ dim → Vec ℕ dim × Vec ℕ dim
rsf-forward-scatter {dim} weights x1 x2 =
  let s-out = matrix-vector-mul (RSFLayerWeights.s-weight weights) x2
      s-bias-added = vector-add s-out (RSFLayerWeights.s-bias weights)
      s-clamped = Data.Vec.map (λ x → clamp x 0 10) s-bias-added
      s-exp = vector-exp s-clamped
      y1 = vector-mul x1 s-exp
  in (y1 , x2)

rsf-forward-transform : ∀ {dim : ℕ} → RSFLayerWeights dim → Vec ℕ dim → Vec ℕ dim → Vec ℕ dim × Vec ℕ dim
rsf-forward-transform {dim} weights x1 x2 =
  let t-out = matrix-vector-mul (RSFLayerWeights.t-weight weights) x1
      t-bias-added = vector-add t-out (RSFLayerWeights.t-bias weights)
      y2 = vector-add x2 t-bias-added
  in (x1 , y2)

rsf-forward : ∀ {dim : ℕ} → RSFLayerWeights dim → Vec ℕ dim → Vec ℕ dim → Vec ℕ dim × Vec ℕ dim
rsf-forward weights x1 x2 =
  let (y1-scatter , y2-scatter) = rsf-forward-scatter weights x1 x2
  in rsf-forward-transform weights y1-scatter y2-scatter

rsf-inverse-transform : ∀ {dim : ℕ} → RSFLayerWeights dim → Vec ℕ dim → Vec ℕ dim → Vec ℕ dim × Vec ℕ dim
rsf-inverse-transform {dim} weights y1 y2 =
  let t-out = matrix-vector-mul (RSFLayerWeights.t-weight weights) y1
      t-bias-added = vector-add t-out (RSFLayerWeights.t-bias weights)
      x2 = Data.Vec.map (λ p → proj₁ p ∸ proj₂ p) (zipWith _,_ y2 t-bias-added)
  in (y1 , x2)

rsf-inverse-scatter : ∀ {dim : ℕ} → RSFLayerWeights dim → Vec ℕ dim → Vec ℕ dim → Vec ℕ dim × Vec ℕ dim
rsf-inverse-scatter {dim} weights y1 y2 =
  let s-out = matrix-vector-mul (RSFLayerWeights.s-weight weights) y2
      s-bias-added = vector-add s-out (RSFLayerWeights.s-bias weights)
      s-clamped = Data.Vec.map (λ x → clamp x 0 10) s-bias-added
      s-exp = vector-exp s-clamped
      x1 = Data.Vec.map (λ p → proj₁ p / (proj₂ p + 1)) (zipWith _,_ y1 s-exp)
  in (x1 , y2)

rsf-inverse : ∀ {dim : ℕ} → RSFLayerWeights dim → Vec ℕ dim → Vec ℕ dim → Vec ℕ dim × Vec ℕ dim
rsf-inverse weights y1 y2 =
  let (x1-transform , x2-transform) = rsf-inverse-transform weights y1 y2
  in rsf-inverse-scatter weights x1-transform x2-transform

record RSFNetwork (dim num-layers : ℕ) : Set where
  constructor mkRSFNetwork
  field
    layers : Vec (RSFLayerState dim) num-layers

RSFNetwork-init : (dim num-layers : ℕ) → RSFNetwork dim num-layers
RSFNetwork-init dim num-layers = mkRSFNetwork (Data.Vec.replicate (RSFLayerState-init dim))

rsf-network-forward : ∀ {dim num-layers : ℕ} → RSFNetwork dim num-layers → Vec ℕ dim → Vec ℕ dim → Vec ℕ dim × Vec ℕ dim
rsf-network-forward {dim} {zero} net x1 x2 = (x1 , x2)
rsf-network-forward {dim} {suc n} net x1 x2 =
  let layer = head (RSFNetwork.layers net)
      rest-layers = mkRSFNetwork (tail (RSFNetwork.layers net))
      (y1 , y2) = rsf-forward (RSFLayerState.weights layer) x1 x2
  in rsf-network-forward rest-layers y1 y2

rsf-network-inverse : ∀ {dim num-layers : ℕ} → RSFNetwork dim num-layers → Vec ℕ dim → Vec ℕ dim → Vec ℕ dim × Vec ℕ dim
rsf-network-inverse {dim} {zero} net y1 y2 = (y1 , y2)
rsf-network-inverse {dim} {suc n} net y1 y2 =
  let layers-vec = RSFNetwork.layers net
      last-layer = Data.Vec.last layers-vec
      init-layers = mkRSFNetwork (Data.Vec.init layers-vec)
      (x1-partial , x2-partial) = rsf-network-inverse init-layers y1 y2
  in rsf-inverse (RSFLayerState.weights last-layer) x1-partial x2-partial

theorem-rsf-layer-forward-shape : ∀ {dim : ℕ} (weights : RSFLayerWeights dim) (x1 x2 : Vec ℕ dim) →
  let (y1 , y2) = rsf-forward weights x1 x2
  in Data.Vec.length y1 ≡ dim × Data.Vec.length y2 ≡ dim
theorem-rsf-layer-forward-shape {dim} weights x1 x2 = refl , refl

theorem-rsf-layer-inverse-shape : ∀ {dim : ℕ} (weights : RSFLayerWeights dim) (y1 y2 : Vec ℕ dim) →
  let (x1 , x2) = rsf-inverse weights y1 y2
  in Data.Vec.length x1 ≡ dim × Data.Vec.length x2 ≡ dim
theorem-rsf-layer-inverse-shape {dim} weights y1 y2 = refl , refl

theorem-rsf-network-forward-shape : ∀ {dim num-layers : ℕ} (net : RSFNetwork dim num-layers) (x1 x2 : Vec ℕ dim) →
  let (y1 , y2) = rsf-network-forward net x1 x2
  in Data.Vec.length y1 ≡ dim × Data.Vec.length y2 ≡ dim
theorem-rsf-network-forward-shape {dim} {zero} net x1 x2 = refl , refl
theorem-rsf-network-forward-shape {dim} {suc n} net x1 x2 =
  let layer = head (RSFNetwork.layers net)
      rest-layers = mkRSFNetwork (tail (RSFNetwork.layers net))
      (y1-partial , y2-partial) = rsf-forward (RSFLayerState.weights layer) x1 x2
  in theorem-rsf-network-forward-shape rest-layers y1-partial y2-partial

theorem-rsf-network-inverse-shape : ∀ {dim num-layers : ℕ} (net : RSFNetwork dim num-layers) (y1 y2 : Vec ℕ dim) →
  let (x1 , x2) = rsf-network-inverse net y1 y2
  in Data.Vec.length x1 ≡ dim × Data.Vec.length x2 ≡ dim
theorem-rsf-network-inverse-shape {dim} {zero} net y1 y2 = refl , refl
theorem-rsf-network-inverse-shape {dim} {suc n} net y1 y2 =
  let layers-vec = RSFNetwork.layers net
      last-layer = Data.Vec.last layers-vec
      init-layers = mkRSFNetwork (Data.Vec.init layers-vec)
  in theorem-rsf-network-inverse-shape init-layers y1 y2

zero-gradients : ∀ {dim : ℕ} → RSFLayerGradients dim → RSFLayerGradients dim
zero-gradients grads = mkRSFLayerGradients
  (Data.Vec.replicate 0)
  (Data.Vec.replicate 0)
  (Data.Vec.replicate 0)
  (Data.Vec.replicate 0)

theorem-zero-gradients-all-zero : ∀ {dim : ℕ} (grads : RSFLayerGradients dim) →
  let zeroed = zero-gradients grads
  in ∀ (i : Fin (dim * dim)) → 
    lookup i (RSFLayerGradients.s-weight-grad zeroed) ≡ 0 ×
    lookup i (RSFLayerGradients.t-weight-grad zeroed) ≡ 0
theorem-zero-gradients-all-zero {dim} grads i = 
  Data.Vec.lookup-replicate i 0 , Data.Vec.lookup-replicate i 0
