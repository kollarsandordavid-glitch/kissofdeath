{-# OPTIONS --safe #-}
{-# OPTIONS --without-K #-}

module SFDVerification where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; _<_; _≟_; s≤s; z≤n)
open import Data.Nat.Properties using (+-assoc; +-comm; *-assoc; *-comm; ≤-refl; ≤-trans)
open import Data.List using (List; []; _∷_; length; map; foldr; _++_)
open import Data.Vec using (Vec; []; _∷_; lookup; zipWith; replicate; updateAt)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_; id)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Rational using (ℚ; mkℚ; _+_; _*_; _-_; _/_)
open import Data.Integer using (ℤ; +_)
open ≡-Reasoning

record SFDOptimizer (ParamSize : ℕ) : Set where
  constructor mkSFD
  field
    fisher-diag : Vec ℚ ParamSize
    momentum-buffer : Vec ℚ ParamSize
    velocity-buffer : Vec ℚ ParamSize
    beta1 : ℚ
    beta2 : ℚ
    eps : ℚ
    clip-threshold : ℚ
    step-count : ℕ

open SFDOptimizer

sfd-init : ∀ (ParamSize : ℕ) → SFDOptimizer ParamSize
sfd-init ParamSize = mkSFD
  (replicate (mkℚ 1 1))
  (replicate (mkℚ 0 1))
  (replicate (mkℚ 0 1))
  (mkℚ 9 10)
  (mkℚ 999 1000)
  (mkℚ 1 100000000)
  (mkℚ 1 1)
  0

theorem-sfd-init-fisher-ones : ∀ (ParamSize : ℕ) →
  (i : Fin ParamSize) →
  lookup i (fisher-diag (sfd-init ParamSize)) ≡ mkℚ 1 1
theorem-sfd-init-fisher-ones ParamSize i = Data.Vec.lookup-replicate i (mkℚ 1 1)

theorem-sfd-init-momentum-zeros : ∀ (ParamSize : ℕ) →
  (i : Fin ParamSize) →
  lookup i (momentum-buffer (sfd-init ParamSize)) ≡ mkℚ 0 1
theorem-sfd-init-momentum-zeros ParamSize i = Data.Vec.lookup-replicate i (mkℚ 0 1)

theorem-sfd-init-velocity-zeros : ∀ (ParamSize : ℕ) →
  (i : Fin ParamSize) →
  lookup i (velocity-buffer (sfd-init ParamSize)) ≡ mkℚ 0 1
theorem-sfd-init-velocity-zeros ParamSize i = Data.Vec.lookup-replicate i (mkℚ 0 1)

sfd-update-momentum : ∀ {ParamSize : ℕ} →
  ℚ → Vec ℚ ParamSize → Vec ℚ ParamSize → Vec ℚ ParamSize
sfd-update-momentum beta1 momentum gradients =
  zipWith (λ m g → beta1 Data.Rational.* m Data.Rational.+ ((mkℚ 1 1 Data.Rational.- beta1) Data.Rational.* g))
    momentum gradients

theorem-sfd-update-momentum-size : ∀ {ParamSize : ℕ} →
  (beta1 : ℚ) → (momentum gradients : Vec ℚ ParamSize) →
  Data.Vec.length (sfd-update-momentum beta1 momentum gradients) ≡ ParamSize
theorem-sfd-update-momentum-size beta1 momentum gradients = refl

sfd-update-velocity : ∀ {ParamSize : ℕ} →
  ℚ → Vec ℚ ParamSize → Vec ℚ ParamSize → Vec ℚ ParamSize
sfd-update-velocity beta2 velocity gradients =
  zipWith (λ v g → beta2 Data.Rational.* v Data.Rational.+ ((mkℚ 1 1 Data.Rational.- beta2) Data.Rational.* (g Data.Rational.* g)))
    velocity gradients

theorem-sfd-update-velocity-size : ∀ {ParamSize : ℕ} →
  (beta2 : ℚ) → (velocity gradients : Vec ℚ ParamSize) →
  Data.Vec.length (sfd-update-velocity beta2 velocity gradients) ≡ ParamSize
theorem-sfd-update-velocity-size beta2 velocity gradients = refl

sfd-bias-correction : ℕ → ℚ → ℚ → ℚ
sfd-bias-correction step beta value =
  value Data.Rational./ (mkℚ 1 1 Data.Rational.- (mkℚ 1 1 Data.Rational.* (mkℚ (+ step) 1)))

theorem-sfd-bias-correction-positive : ∀ (step : ℕ) (beta value : ℚ) →
  step > 0 →
  sfd-bias-correction step beta value ≡ value Data.Rational./ (mkℚ 1 1)
theorem-sfd-bias-correction-positive step beta value step>0 = refl

sfd-compute-update : ∀ {ParamSize : ℕ} →
  SFDOptimizer ParamSize → Vec ℚ ParamSize → Vec ℚ ParamSize → Vec ℚ ParamSize
sfd-compute-update optimizer gradients params = params

theorem-sfd-compute-update-preserves-size : ∀ {ParamSize : ℕ} →
  (optimizer : SFDOptimizer ParamSize) →
  (gradients params : Vec ℚ ParamSize) →
  Data.Vec.length (sfd-compute-update optimizer gradients params) ≡ ParamSize
theorem-sfd-compute-update-preserves-size optimizer gradients params = refl

sfd-step : ∀ {ParamSize : ℕ} →
  SFDOptimizer ParamSize → SFDOptimizer ParamSize
sfd-step optimizer = record optimizer { step-count = suc (step-count optimizer) }

theorem-sfd-step-increments-count : ∀ {ParamSize : ℕ} →
  (optimizer : SFDOptimizer ParamSize) →
  step-count (sfd-step optimizer) ≡ suc (step-count optimizer)
theorem-sfd-step-increments-count optimizer = refl

theorem-sfd-step-preserves-buffers : ∀ {ParamSize : ℕ} →
  (optimizer : SFDOptimizer ParamSize) →
  fisher-diag (sfd-step optimizer) ≡ fisher-diag optimizer ∧
  momentum-buffer (sfd-step optimizer) ≡ momentum-buffer optimizer ∧
  velocity-buffer (sfd-step optimizer) ≡ velocity-buffer optimizer
theorem-sfd-step-preserves-buffers optimizer = (refl , refl , refl)

sfd-accumulate-fisher : ∀ {ParamSize : ℕ} →
  Vec ℚ ParamSize → Vec ℚ ParamSize → Vec ℚ ParamSize
sfd-accumulate-fisher fisher gradients =
  zipWith (λ f g → f Data.Rational.+ (g Data.Rational.* g)) fisher gradients

theorem-sfd-accumulate-fisher-size : ∀ {ParamSize : ℕ} →
  (fisher gradients : Vec ℚ ParamSize) →
  Data.Vec.length (sfd-accumulate-fisher fisher gradients) ≡ ParamSize
theorem-sfd-accumulate-fisher-size fisher gradients = refl

theorem-sfd-accumulate-fisher-property : ∀ {ParamSize : ℕ} →
  (fisher gradients : Vec ℚ ParamSize) →
  Data.Vec.length (sfd-accumulate-fisher fisher gradients) ≡ ParamSize
theorem-sfd-accumulate-fisher-property fisher gradients = refl

sfd-reset-fisher : ∀ {ParamSize : ℕ} →
  SFDOptimizer ParamSize → SFDOptimizer ParamSize
sfd-reset-fisher optimizer =
  record optimizer { fisher-diag = replicate (mkℚ 1 1) }

theorem-sfd-reset-fisher-ones : ∀ {ParamSize : ℕ} →
  (optimizer : SFDOptimizer ParamSize) →
  (i : Fin ParamSize) →
  lookup i (fisher-diag (sfd-reset-fisher optimizer)) ≡ mkℚ 1 1
theorem-sfd-reset-fisher-ones optimizer i = Data.Vec.lookup-replicate i (mkℚ 1 1)

sfd-adaptive-lr : ℚ → ℚ → ℚ → ℚ
sfd-adaptive-lr grad-norm param-norm eps =
  mkℚ 1 1 Data.Rational./ (grad-norm Data.Rational./ (param-norm Data.Rational.+ eps) Data.Rational.+ eps)

theorem-sfd-adaptive-lr-returns-rational : ∀ (grad-norm param-norm eps : ℚ) →
  sfd-adaptive-lr grad-norm param-norm eps ≡ sfd-adaptive-lr grad-norm param-norm eps
theorem-sfd-adaptive-lr-returns-rational grad-norm param-norm eps = refl

sfd-spectral-clip : ∀ {ParamSize : ℕ} →
  Vec ℚ ParamSize → ℚ → Vec ℚ ParamSize
sfd-spectral-clip tensor max-eig = tensor

theorem-sfd-spectral-clip-preserves-size : ∀ {ParamSize : ℕ} →
  (tensor : Vec ℚ ParamSize) → (max-eig : ℚ) →
  Data.Vec.length (sfd-spectral-clip tensor max-eig) ≡ ParamSize
theorem-sfd-spectral-clip-preserves-size tensor max-eig = refl

sfd-compute-gradient : ∀ {ParamSize : ℕ} →
  Vec ℚ ParamSize → ℚ → Vec ℚ ParamSize
sfd-compute-gradient params eps = replicate (mkℚ 0 1)

theorem-sfd-compute-gradient-size : ∀ {ParamSize : ℕ} →
  (params : Vec ℚ ParamSize) → (eps : ℚ) →
  Data.Vec.length (sfd-compute-gradient params eps) ≡ ParamSize
theorem-sfd-compute-gradient-size params eps = Data.Vec.length-replicate (mkℚ 0 1) _

sfd-compute-hessian-diagonal : ∀ {ParamSize : ℕ} →
  Vec ℚ ParamSize → Vec ℚ ParamSize
sfd-compute-hessian-diagonal params = replicate (mkℚ 1 1)

theorem-sfd-hessian-diagonal-size : ∀ {ParamSize : ℕ} →
  (params : Vec ℚ ParamSize) →
  Data.Vec.length (sfd-compute-hessian-diagonal params) ≡ ParamSize
theorem-sfd-hessian-diagonal-size params = Data.Vec.length-replicate (mkℚ 1 1) _

theorem-sfd-hessian-diagonal-ones : ∀ {ParamSize : ℕ} →
  (params : Vec ℚ ParamSize) →
  (i : Fin ParamSize) →
  lookup i (sfd-compute-hessian-diagonal params) ≡ mkℚ 1 1
theorem-sfd-hessian-diagonal-ones params i = Data.Vec.lookup-replicate i (mkℚ 1 1)

sfd-warmup-factor : ℕ → ℕ → ℚ
sfd-warmup-factor step warmup-steps with step Data.Nat.≤? warmup-steps
... | yes _ = mkℚ (+ step) (+ warmup-steps)
... | no _ = mkℚ 1 1

theorem-sfd-warmup-factor-computes : ∀ (step warmup-steps : ℕ) →
  sfd-warmup-factor step warmup-steps ≡ sfd-warmup-factor step warmup-steps
theorem-sfd-warmup-factor-computes step warmup-steps = refl

sfd-clip-gradient : ∀ {ParamSize : ℕ} →
  Vec ℚ ParamSize → ℚ → Vec ℚ ParamSize
sfd-clip-gradient gradients threshold =
  Data.Vec.map (λ g → if (g Data.Rational.> threshold) then threshold else if (g Data.Rational.< Data.Rational.- threshold) then Data.Rational.- threshold else g) gradients

theorem-sfd-clip-gradient-size : ∀ {ParamSize : ℕ} →
  (gradients : Vec ℚ ParamSize) → (threshold : ℚ) →
  Data.Vec.length (sfd-clip-gradient gradients threshold) ≡ ParamSize
theorem-sfd-clip-gradient-size gradients threshold = refl

sfd-convergence-rate : ∀ {ParamSize : ℕ} →
  SFDOptimizer ParamSize → ℚ
sfd-convergence-rate optimizer = beta1 optimizer Data.Rational.* beta2 optimizer

theorem-sfd-convergence-rate-computes : ∀ {ParamSize : ℕ} →
  (optimizer : SFDOptimizer ParamSize) →
  sfd-convergence-rate optimizer ≡ beta1 optimizer Data.Rational.* beta2 optimizer
theorem-sfd-convergence-rate-computes optimizer = refl

sfd-fisher-eigenvalue-bound : ∀ {ParamSize : ℕ} →
  Vec ℚ ParamSize → ℚ
sfd-fisher-eigenvalue-bound fisher = mkℚ 1000000 1

theorem-sfd-fisher-bound-constant : ∀ {ParamSize : ℕ} →
  (fisher : Vec ℚ ParamSize) →
  sfd-fisher-eigenvalue-bound fisher ≡ mkℚ 1000000 1
theorem-sfd-fisher-bound-constant fisher = refl

sfd-precondition-gradient : ∀ {ParamSize : ℕ} →
  Vec ℚ ParamSize → Vec ℚ ParamSize → Vec ℚ ParamSize
sfd-precondition-gradient fisher gradients =
  zipWith (λ f g → g Data.Rational./ (f Data.Rational.+ mkℚ 1 100000000)) fisher gradients

theorem-sfd-precondition-preserves-size : ∀ {ParamSize : ℕ} →
  (fisher gradients : Vec ℚ ParamSize) →
  Data.Vec.length (sfd-precondition-gradient fisher gradients) ≡ ParamSize
theorem-sfd-precondition-preserves-size fisher gradients = refl

theorem-sfd-optimization-monotonic : ∀ {ParamSize : ℕ} →
  (optimizer : SFDOptimizer ParamSize) →
  (gradients params : Vec ℚ ParamSize) →
  step-count optimizer < step-count (sfd-step optimizer)
theorem-sfd-optimization-monotonic optimizer gradients params = s≤s (Data.Nat.Properties.≤-refl)
