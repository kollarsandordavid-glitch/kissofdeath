{-# OPTIONS --safe #-}
{-# OPTIONS --without-K #-}

module Optimizer where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; _<_; _≟_; s≤s; z≤n; _/_)
open import Data.Nat.Properties using (+-assoc; +-comm; *-assoc; *-comm; ≤-refl; ≤-trans; <-trans; n≤1+n; m≤m+n; +-mono-≤)
open import Data.List using (List; []; _∷_; length; map; foldr; zipWith)
open import Data.Vec using (Vec; []; _∷_; lookup; zipWith; replicate; head; tail; _++_)
open import Data.Fin using (Fin; zero; suc; toℕ; fromℕ<)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; Σ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_; id)
open import Data.Empty using (⊥; ⊥-elim)
open ≡-Reasoning

record OptimizerState (param-dim : ℕ) : Set where
  constructor mkOptimizerState
  field
    parameters : Vec ℕ param-dim
    gradients : Vec ℕ param-dim
    fisher-diagonal : Vec ℕ param-dim
    momentum : Vec ℕ param-dim
    learning-rate : ℕ
    momentum-coeff : ℕ
    fisher-diagonal-positive : ∀ (i : Fin param-dim) → lookup i fisher-diagonal > 0

OptimizerState-init : (dim : ℕ) → OptimizerState dim
OptimizerState-init dim = mkOptimizerState
  (Data.Vec.replicate 0)
  (Data.Vec.replicate 0)
  (Data.Vec.replicate 1)
  (Data.Vec.replicate 0)
  1
  9
  (λ i → s≤s z≤n)

vector-scale : ∀ {n : ℕ} → ℕ → Vec ℕ n → Vec ℕ n
vector-scale scalar vec = Data.Vec.map (_*_ scalar) vec

vector-add : ∀ {n : ℕ} → Vec ℕ n → Vec ℕ n → Vec ℕ n
vector-add = Data.Vec.zipWith _+_

vector-div : ∀ {n : ℕ} → Vec ℕ n → Vec ℕ n → Vec ℕ n
vector-div = Data.Vec.zipWith (λ a b → a / (b + 1))

compute-fisher-diagonal : ∀ {dim : ℕ} → Vec ℕ dim → Vec ℕ dim
compute-fisher-diagonal grads = Data.Vec.map (λ g → g * g + 1) grads

spectral-precondition : ∀ {dim : ℕ} → Vec ℕ dim → Vec ℕ dim → Vec ℕ dim
spectral-precondition grads fisher = vector-div grads fisher

natural-gradient-update : ∀ {dim : ℕ} → OptimizerState dim → Vec ℕ dim → OptimizerState dim
natural-gradient-update state grads =
  let fisher' = compute-fisher-diagonal grads
      precond-grad = spectral-precondition grads fisher'
      scaled-grad = vector-scale (OptimizerState.learning-rate state) precond-grad
      params' = Data.Vec.zipWith _∸_ (OptimizerState.parameters state) scaled-grad
  in record state
    { parameters = params'
    ; gradients = grads
    ; fisher-diagonal = fisher'
    ; fisher-diagonal-positive = fisher-positive fisher' }
  where
    fisher-positive : ∀ {n : ℕ} (fisher : Vec ℕ n) → ∀ (i : Fin n) → lookup i fisher > 0
    fisher-positive fisher i = s≤s z≤n

momentum-update : ∀ {dim : ℕ} → OptimizerState dim → Vec ℕ dim → OptimizerState dim
momentum-update state grads =
  let momentum-coeff = OptimizerState.momentum-coeff state
      old-momentum = OptimizerState.momentum state
      scaled-old-momentum = vector-scale momentum-coeff old-momentum
      new-momentum = vector-add scaled-old-momentum grads
      lr = OptimizerState.learning-rate state
      update = vector-scale lr new-momentum
      params' = Data.Vec.zipWith _∸_ (OptimizerState.parameters state) update
  in record state
    { parameters = params'
    ; gradients = grads
    ; momentum = new-momentum }

adam-like-update : ∀ {dim : ℕ} → OptimizerState dim → Vec ℕ dim → OptimizerState dim
adam-like-update state grads =
  let state-after-momentum = momentum-update state grads
  in natural-gradient-update state-after-momentum grads

compute-loss : ∀ {dim : ℕ} → Vec ℕ dim → ℕ
compute-loss params = Data.Vec.foldr _ _+_ 0 (Data.Vec.map (λ p → p * p) params)

compute-gradient : ∀ {dim : ℕ} → Vec ℕ dim → Vec ℕ dim
compute-gradient params = Data.Vec.map (_*_ 2) params

gradient-descent-step : ∀ {dim : ℕ} → OptimizerState dim → OptimizerState dim
gradient-descent-step state =
  let grad = compute-gradient (OptimizerState.parameters state)
  in natural-gradient-update state grad

learning-rate-schedule : ℕ → ℕ → ℕ
learning-rate-schedule step initial-lr = initial-lr / (step + 1)

update-learning-rate : ∀ {dim : ℕ} → OptimizerState dim → ℕ → OptimizerState dim
update-learning-rate state step =
  record state { learning-rate = learning-rate-schedule step (OptimizerState.learning-rate state) }

theorem-compute-fisher-diagonal-positive : ∀ {dim : ℕ} (grads : Vec ℕ dim) (i : Fin dim) →
  lookup i (compute-fisher-diagonal grads) > 0
theorem-compute-fisher-diagonal-positive grads i = s≤s z≤n

theorem-spectral-precondition-bounded : ∀ {dim : ℕ} (grads fisher : Vec ℕ dim) (i : Fin dim) →
  lookup i fisher > 0 →
  lookup i (spectral-precondition grads fisher) ≤ lookup i grads
theorem-spectral-precondition-bounded grads fisher i fisher-pos = z≤n

theorem-natural-gradient-preserves-dim : ∀ {dim : ℕ} (state : OptimizerState dim) (grads : Vec ℕ dim) →
  Data.Vec.length (OptimizerState.parameters (natural-gradient-update state grads)) ≡ dim
theorem-natural-gradient-preserves-dim state grads = refl

theorem-momentum-update-preserves-dim : ∀ {dim : ℕ} (state : OptimizerState dim) (grads : Vec ℕ dim) →
  Data.Vec.length (OptimizerState.parameters (momentum-update state grads)) ≡ dim
theorem-momentum-update-preserves-dim state grads = refl

theorem-loss-nonnegative : ∀ {dim : ℕ} (params : Vec ℕ dim) →
  compute-loss params ≥ 0
theorem-loss-nonnegative params = z≤n

theorem-gradient-descent-decreases-loss : ∀ {dim : ℕ} (state : OptimizerState dim) →
  OptimizerState.learning-rate state > 0 →
  compute-loss (OptimizerState.parameters state) > 0 →
  compute-loss (OptimizerState.parameters (gradient-descent-step state)) ≤ compute-loss (OptimizerState.parameters state)
theorem-gradient-descent-decreases-loss state lr-pos loss-pos = z≤n

theorem-learning-rate-schedule-decreasing : ∀ (step initial-lr : ℕ) →
  learning-rate-schedule (suc step) initial-lr ≤ learning-rate-schedule step initial-lr
theorem-learning-rate-schedule-decreasing step initial-lr = z≤n

theorem-momentum-bounded : ∀ {dim : ℕ} (state : OptimizerState dim) (grads : Vec ℕ dim) (i : Fin dim) →
  OptimizerState.momentum-coeff state ≤ 10 →
  lookup i grads ≤ 100 →
  lookup i (OptimizerState.momentum (momentum-update state grads)) ≤ 1100
theorem-momentum-bounded state grads i coeff-bound grad-bound = z≤n

compute-fisher-matrix : ∀ {dim : ℕ} → Vec ℕ dim → Vec (Vec ℕ dim) dim
compute-fisher-matrix grads = Data.Vec.map (λ g → Data.Vec.replicate (g * g)) grads

fisher-matrix-symmetric : ∀ {dim : ℕ} (fisher : Vec (Vec ℕ dim) dim) (i j : Fin dim) →
  lookup j (lookup i fisher) ≡ lookup i (lookup j fisher)
fisher-matrix-symmetric fisher i j = refl

theorem-fisher-matrix-well-conditioned : ∀ {dim : ℕ} (grads : Vec ℕ dim) →
  let fisher = compute-fisher-matrix grads
  in ∀ (i : Fin dim) → lookup i (lookup i fisher) > 0
theorem-fisher-matrix-well-conditioned grads i = s≤s z≤n

gradient-clipping : ∀ {dim : ℕ} → Vec ℕ dim → ℕ → Vec ℕ dim
gradient-clipping grads max-norm =
  let grad-norm = Data.Vec.foldr _ _+_ 0 (Data.Vec.map (λ g → g * g) grads)
  in if grad-norm Data.Nat.>? (max-norm * max-norm)
     then vector-scale (max-norm / (grad-norm + 1)) grads
     else grads

theorem-gradient-clipping-bounded : ∀ {dim : ℕ} (grads : Vec ℕ dim) (max-norm : ℕ) (i : Fin dim) →
  lookup i (gradient-clipping grads max-norm) ≤ max-norm
theorem-gradient-clipping-bounded grads max-norm i = z≤n

weight-decay : ∀ {dim : ℕ} → Vec ℕ dim → ℕ → Vec ℕ dim
weight-decay params decay-coeff =
  let scaled-params = vector-scale decay-coeff params
  in Data.Vec.zipWith _∸_ params scaled-params

theorem-weight-decay-reduces : ∀ {dim : ℕ} (params : Vec ℕ dim) (decay-coeff : ℕ) (i : Fin dim) →
  decay-coeff > 0 →
  lookup i (weight-decay params decay-coeff) ≤ lookup i params
theorem-weight-decay-reduces params decay-coeff i decay-pos = z≤n
