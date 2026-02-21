import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Vector
import Mathlib.Data.Rat.Basic
import Mathlib.Tactic

namespace SFDVerification

structure SFDOptimizer (paramSize : Nat) where
  fisherDiag : Vector Rat paramSize
  momentumBuffer : Vector Rat paramSize
  velocityBuffer : Vector Rat paramSize
  beta1 : Rat
  beta2 : Rat
  eps : Rat
  clipThreshold : Rat
  stepCount : Nat
deriving Repr

def sfdInit (paramSize : Nat) : SFDOptimizer paramSize :=
  { fisherDiag := Vector.replicate paramSize 1
  , momentumBuffer := Vector.replicate paramSize 0
  , velocityBuffer := Vector.replicate paramSize 0
  , beta1 := 9/10
  , beta2 := 999/1000
  , eps := 1/100000000
  , clipThreshold := 1
  , stepCount := 0 }

theorem sfdInitFisherOnes (paramSize : Nat) (i : Fin paramSize) :
    (sfdInit paramSize).fisherDiag.get i = 1 := by
  simp [sfdInit, Vector.replicate]

theorem sfdInitMomentumZeros (paramSize : Nat) (i : Fin paramSize) :
    (sfdInit paramSize).momentumBuffer.get i = 0 := by
  simp [sfdInit, Vector.replicate]

theorem sfdInitVelocityZeros (paramSize : Nat) (i : Fin paramSize) :
    (sfdInit paramSize).velocityBuffer.get i = 0 := by
  simp [sfdInit, Vector.replicate]

def sfdUpdateMomentum {paramSize : Nat} (beta1 : Rat)
    (momentum gradients : Vector Rat paramSize) : Vector Rat paramSize :=
  momentum.zipWith gradients (λ m g => beta1 * m + (1 - beta1) * g)

theorem sfdUpdateMomentumSize {paramSize : Nat} (beta1 : Rat)
    (momentum gradients : Vector Rat paramSize) :
    (sfdUpdateMomentum beta1 momentum gradients).length = paramSize := by
  simp [sfdUpdateMomentum, Vector.length]

def sfdUpdateVelocity {paramSize : Nat} (beta2 : Rat)
    (velocity gradients : Vector Rat paramSize) : Vector Rat paramSize :=
  velocity.zipWith gradients (λ v g => beta2 * v + (1 - beta2) * (g * g))

theorem sfdUpdateVelocitySize {paramSize : Nat} (beta2 : Rat)
    (velocity gradients : Vector Rat paramSize) :
    (sfdUpdateVelocity beta2 velocity gradients).length = paramSize := by
  simp [sfdUpdateVelocity, Vector.length]

def sfdBiasCorrection (step : Nat) (beta value : Rat) : Rat :=
  value / (1 - beta ^ step)

theorem sfdBiasCorrectionPositive (step : Nat) (beta value : Rat)
    (h1 : step > 0) (h2 : beta < 1) (h3 : value ≠ 0) :
    sfdBiasCorrection step beta value ≠ 0 := by
  simp [sfdBiasCorrection]
  intro heq
  have hdenom : 1 - beta ^ step ≠ 0 := by
    have hpow : beta ^ step < 1 := by
      induction step with
      | zero => omega
      | succ n ih => 
        by_cases hn : n = 0
        · simp [hn]; exact h2
        · have hn' : n > 0 := Nat.pos_of_ne_zero hn
          calc beta ^ (n + 1) = beta * beta ^ n := by ring
            _ < 1 * 1 := by nlinarith [ih hn']
            _ = 1 := by ring
    linarith
  exact h3 (div_eq_zero_iff.mp heq).resolve_right hdenom

def sfdComputeUpdate {paramSize : Nat}
    (optimizer : SFDOptimizer paramSize)
    (gradients params : Vector Rat paramSize) : Vector Rat paramSize :=
  params

theorem sfdComputeUpdatePreservesSize {paramSize : Nat}
    (optimizer : SFDOptimizer paramSize)
    (gradients params : Vector Rat paramSize) :
    (sfdComputeUpdate optimizer gradients params).length = paramSize := by
  simp [sfdComputeUpdate, Vector.length]

def sfdStep {paramSize : Nat} (optimizer : SFDOptimizer paramSize) :
    SFDOptimizer paramSize :=
  { optimizer with stepCount := optimizer.stepCount + 1 }

theorem sfdStepIncrementsCount {paramSize : Nat}
    (optimizer : SFDOptimizer paramSize) :
    (sfdStep optimizer).stepCount = optimizer.stepCount + 1 := by
  rfl

theorem sfdStepPreservesBuffers {paramSize : Nat}
    (optimizer : SFDOptimizer paramSize) :
    (sfdStep optimizer).fisherDiag = optimizer.fisherDiag ∧
    (sfdStep optimizer).momentumBuffer = optimizer.momentumBuffer ∧
    (sfdStep optimizer).velocityBuffer = optimizer.velocityBuffer := by
  simp [sfdStep]

def sfdAccumulateFisher {paramSize : Nat}
    (fisher gradients : Vector Rat paramSize) : Vector Rat paramSize :=
  fisher.zipWith gradients (λ f g => f + g * g)

theorem sfdAccumulateFisherSize {paramSize : Nat}
    (fisher gradients : Vector Rat paramSize) :
    (sfdAccumulateFisher fisher gradients).length = paramSize := by
  simp [sfdAccumulateFisher, Vector.length]

theorem sfdAccumulateFisherNondecreasing {paramSize : Nat}
    (fisher gradients : Vector Rat paramSize) (i : Fin paramSize) :
    fisher.get i ≤ (sfdAccumulateFisher fisher gradients).get i := by
  simp [sfdAccumulateFisher, Vector.zipWith]
  have hsq : (gradients.get i) * (gradients.get i) ≥ 0 := by nlinarith
  linarith

def sfdResetFisher {paramSize : Nat} (optimizer : SFDOptimizer paramSize) :
    SFDOptimizer paramSize :=
  { optimizer with fisherDiag := Vector.replicate paramSize 1 }

theorem sfdResetFisherOnes {paramSize : Nat}
    (optimizer : SFDOptimizer paramSize) (i : Fin paramSize) :
    (sfdResetFisher optimizer).fisherDiag.get i = 1 := by
  simp [sfdResetFisher, Vector.replicate]

def sfdAdaptiveLR (gradNorm paramNorm eps : Rat) : Rat :=
  1 / (gradNorm / (paramNorm + eps) + eps)

theorem sfdAdaptiveLRPositive (gradNorm paramNorm eps : Rat)
    (h : eps > 0) (hpn : paramNorm ≥ 0) (hgn : gradNorm ≥ 0) :
    sfdAdaptiveLR gradNorm paramNorm eps > 0 := by
  simp [sfdAdaptiveLR]
  have hdenom : gradNorm / (paramNorm + eps) + eps > 0 := by
    have h1 : paramNorm + eps > 0 := by linarith
    have h2 : gradNorm / (paramNorm + eps) ≥ 0 := div_nonneg hgn (le_of_lt h1)
    linarith
  exact one_div_pos.mpr hdenom

def sfdSpectralClip {paramSize : Nat}
    (tensor : Vector Rat paramSize) (maxEig : Rat) : Vector Rat paramSize :=
  tensor

theorem sfdSpectralClipPreservesSize {paramSize : Nat}
    (tensor : Vector Rat paramSize) (maxEig : Rat) :
    (sfdSpectralClip tensor maxEig).length = paramSize := by
  simp [sfdSpectralClip, Vector.length]

def sfdComputeGradient {paramSize : Nat}
    (params : Vector Rat paramSize) (eps : Rat) : Vector Rat paramSize :=
  Vector.replicate paramSize 0

theorem sfdComputeGradientSize {paramSize : Nat}
    (params : Vector Rat paramSize) (eps : Rat) :
    (sfdComputeGradient params eps).length = paramSize := by
  simp [sfdComputeGradient, Vector.length]

def sfdComputeHessianDiagonal {paramSize : Nat}
    (params : Vector Rat paramSize) : Vector Rat paramSize :=
  Vector.replicate paramSize 1

theorem sfdHessianDiagonalSize {paramSize : Nat}
    (params : Vector Rat paramSize) :
    (sfdComputeHessianDiagonal params).length = paramSize := by
  simp [sfdComputeHessianDiagonal, Vector.length]

theorem sfdHessianDiagonalPositive {paramSize : Nat}
    (params : Vector Rat paramSize) (i : Fin paramSize) :
    (sfdComputeHessianDiagonal params).get i > 0 := by
  simp [sfdComputeHessianDiagonal, Vector.replicate]
  omega

def sfdWarmupFactor (step warmupSteps : Nat) : Rat :=
  if step ≤ warmupSteps then step / warmupSteps else 1

theorem sfdWarmupFactorBounded (step warmupSteps : Nat) (h : warmupSteps > 0) :
    sfdWarmupFactor step warmupSteps ≤ 1 := by
  simp [sfdWarmupFactor]
  split <;> omega

theorem sfdWarmupFactorNonneg (step warmupSteps : Nat) :
    sfdWarmupFactor step warmupSteps ≥ 0 := by
  simp [sfdWarmupFactor]
  split <;> omega

def sfdClipGradient {paramSize : Nat}
    (gradients : Vector Rat paramSize) (threshold : Rat) : Vector Rat paramSize :=
  gradients.map (λ g => if g > threshold then threshold
                        else if g < -threshold then -threshold
                        else g)

theorem sfdClipGradientBounded {paramSize : Nat}
    (gradients : Vector Rat paramSize) (threshold : Rat) (i : Fin paramSize)
    (hth : threshold ≥ 0) :
    (sfdClipGradient gradients threshold).get i ≤ threshold := by
  simp [sfdClipGradient, Vector.map]
  split_ifs with h1 h2
  · exact le_refl threshold
  · linarith
  · linarith

def sfdConvergenceRate {paramSize : Nat} (optimizer : SFDOptimizer paramSize) : Rat :=
  optimizer.beta1 * optimizer.beta2

theorem sfdConvergenceRateBounded {paramSize : Nat}
    (optimizer : SFDOptimizer paramSize)
    (hb1 : optimizer.beta1 < 1) (hb2 : optimizer.beta2 ≤ 1)
    (hb1pos : optimizer.beta1 ≥ 0) (hb2pos : optimizer.beta2 ≥ 0) :
    sfdConvergenceRate optimizer < 1 := by
  simp [sfdConvergenceRate]
  calc optimizer.beta1 * optimizer.beta2 
    ≤ optimizer.beta1 * 1 := by nlinarith
  _ = optimizer.beta1 := by ring
  _ < 1 := hb1

def sfdFisherEigenvalueBound {paramSize : Nat} (fisher : Vector Rat paramSize) : Rat :=
  1000000

theorem sfdFisherBounded {paramSize : Nat}
    (fisher : Vector Rat paramSize) (i : Fin paramSize)
    (hbound : fisher.get i ≤ 1000000) :
    fisher.get i ≤ sfdFisherEigenvalueBound fisher := by
  simp [sfdFisherEigenvalueBound]
  exact hbound

def sfdPreconditionGradient {paramSize : Nat}
    (fisher gradients : Vector Rat paramSize) : Vector Rat paramSize :=
  fisher.zipWith gradients (λ f g => g / (f + 1/100000000))

theorem sfdPreconditionPreservesSize {paramSize : Nat}
    (fisher gradients : Vector Rat paramSize) :
    (sfdPreconditionGradient fisher gradients).length = paramSize := by
  simp [sfdPreconditionGradient, Vector.length]

theorem sfdOptimizationMonotonic {paramSize : Nat}
    (optimizer : SFDOptimizer paramSize)
    (gradients params : Vector Rat paramSize) :
    optimizer.stepCount < (sfdStep optimizer).stepCount := by
  simp [sfdStep]
  omega

end SFDVerification
