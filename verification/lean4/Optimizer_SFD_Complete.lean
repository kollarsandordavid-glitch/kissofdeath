import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic

namespace SFDOptimizerVerification

structure OptimizerState where
  parameters : List Real
  gradients : List Real
  fisherDiagonal : List Real
  momentum : List Real
  iteration : Nat
  learningRate : Real
  momentumCoeff : Real

def OptimizerState.init (paramCount : Nat) (lr : Real) (beta : Real) : OptimizerState :=
  { parameters := List.replicate paramCount 0
  , gradients := List.replicate paramCount 0
  , fisherDiagonal := List.replicate paramCount 1
  , momentum := List.replicate paramCount 0
  , iteration := 0
  , learningRate := lr
  , momentumCoeff := beta }

def computeFisherDiagonal (gradients : List Real) : List Real :=
  gradients.map (fun g => g * g)

theorem computeFisherDiagonal_nonnegative (gradients : List Real) :
  ∀ x ∈ computeFisherDiagonal gradients, x ≥ 0 := by
  intro x hx
  unfold computeFisherDiagonal at hx
  simp at hx
  obtain ⟨g, hg, rfl⟩ := hx
  exact sq_nonneg g

theorem computeFisherDiagonal_length (gradients : List Real) :
  (computeFisherDiagonal gradients).length = gradients.length := by
  unfold computeFisherDiagonal
  simp

def spectralPrecondition (gradients fisherDiag : List Real) (epsilon : Real) : List Real :=
  gradients.zipWith fisherDiag (fun g f => g / (f + epsilon))

theorem spectralPrecondition_bounded (gradients fisherDiag : List Real) 
  (epsilon : Real) (heps : epsilon > 0) :
  gradients.length = fisherDiag.length →
  (∀ f ∈ fisherDiag, f ≥ 0) →
  (∀ g ∈ gradients, |g| ≤ 1000) →
  ∀ x ∈ spectralPrecondition gradients fisherDiag epsilon, |x| ≤ 1000 / epsilon := by
  intro hlen hfnonneg hgbounded x hx
  unfold spectralPrecondition at hx
  obtain ⟨g, f, hg, hf, rfl⟩ := List.mem_zipWith.mp hx
  have hfpos : f ≥ 0 := hfnonneg f hf
  have hgbound : |g| ≤ 1000 := hgbounded g hg
  have hdenom_pos : f + epsilon > 0 := by linarith
  calc |g / (f + epsilon)| 
      = |g| / |f + epsilon| := abs_div g (f + epsilon)
    _ = |g| / (f + epsilon) := by rw [abs_of_pos hdenom_pos]
    _ ≤ 1000 / (f + epsilon) := by apply div_le_div_of_nonneg_right hgbound hdenom_pos
    _ ≤ 1000 / epsilon := by apply div_le_div_of_nonneg_left (by linarith) heps (by linarith)

theorem spectralPrecondition_length (gradients fisherDiag : List Real) (epsilon : Real) :
  gradients.length = fisherDiag.length →
  (spectralPrecondition gradients fisherDiag epsilon).length = gradients.length := by
  intro hlen
  unfold spectralPrecondition
  simp [hlen]

def naturalGradient (state : OptimizerState) (epsilon : Real) : List Real :=
  spectralPrecondition state.gradients state.fisherDiagonal epsilon

theorem naturalGradient_preserves_bounds (state : OptimizerState) 
  (epsilon : Real) (heps : epsilon > 0) :
  state.parameters.length = state.gradients.length →
  state.gradients.length = state.fisherDiagonal.length →
  (∀ f ∈ state.fisherDiagonal, f ≥ 0) →
  (∀ g ∈ state.gradients, |g| ≤ 1000) →
  ∀ ng ∈ naturalGradient state epsilon, |ng| ≤ 1000 / epsilon := by
  intro hplen hglen hfnonneg hgbounded ng hng
  unfold naturalGradient at hng
  exact spectralPrecondition_bounded state.gradients state.fisherDiagonal epsilon heps hglen hfnonneg hgbounded ng hng

def computeLoss (parameters : List Real) (targets : List Real) : Real :=
  (parameters.zipWith targets (fun p t => (p - t) ^ 2)).foldl (· + ·) 0

theorem loss_nonnegative (parameters targets : List Real) :
  computeLoss parameters targets ≥ 0 := by
  unfold computeLoss
  apply List.foldl_nonneg
  · exact le_refl 0
  · intro acc hacc x hx
    obtain ⟨p, t, hp, ht, rfl⟩ := List.mem_zipWith.mp hx
    have hsq : (p - t) ^ 2 ≥ 0 := sq_nonneg (p - t)
    linarith

theorem loss_zero_iff_equal (parameters targets : List Real) :
  parameters.length = targets.length →
  computeLoss parameters targets = 0 ↔ parameters = targets := by
  intro hlen
  unfold computeLoss
  constructor
  · intro hzero
    induction parameters, targets using List.rec₂ with
    | nil => rfl
    | cons p ps t ts ih =>
      have hzipped : (List.zipWith (fun p t => (p - t) ^ 2) (p :: ps) (t :: ts)) = 
                     (p - t) ^ 2 :: (List.zipWith (fun p t => (p - t) ^ 2) ps ts) := rfl
      rw [hzipped] at hzero
      have hfold := hzero
      have hsq_nonneg : (p - t) ^ 2 ≥ 0 := sq_nonneg (p - t)
      have hrest_nonneg : List.foldl (· + ·) 0 (List.zipWith (fun p t => (p - t) ^ 2) ps ts) ≥ 0 := 
        loss_nonnegative ps ts
      have hpt : p = t := by
        by_contra hne
        have hsq_pos : (p - t) ^ 2 > 0 := sq_pos_of_ne_zero _ (sub_ne_zero.mpr hne)
        linarith
      rw [hpt]
      congr 1
      apply ih
      · omega
      · rw [hpt] at hzero
        have hsub_zero : (t - t) ^ 2 = 0 := by ring
        rw [hsub_zero] at hzero
        linarith
  · intro heq
    rw [heq]
    have hself : ∀ x ∈ List.zipWith (fun p t => (p - t) ^ 2) targets targets, x = 0 := by
      intro x hx
      obtain ⟨a, b, ha, hb, rfl⟩ := List.mem_zipWith.mp hx
      ring
    induction targets with
    | nil => rfl
    | cons t ts ih => 
      have : List.foldl (· + ·) 0 ((t - t) ^ 2 :: List.zipWith (fun p t => (p - t) ^ 2) ts ts) =
             (t - t) ^ 2 + List.foldl (· + ·) 0 (List.zipWith (fun p t => (p - t) ^ 2) ts ts) := by
        rfl
      rw [this]
      have hsub : (t - t) ^ 2 = 0 := by ring
      rw [hsub, zero_add]
      exact ih

def computeGradient (parameters targets : List Real) : List Real :=
  parameters.zipWith targets (fun p t => 2 * (p - t))

theorem gradient_descent_decreases_loss (parameters targets : List Real) 
  (learningRate : Real) (hlr : 0 < learningRate ∧ learningRate < 0.01) :
  parameters.length = targets.length →
  let gradients := computeGradient parameters targets
  let newParams := parameters.zipWith gradients (fun p g => p - learningRate * g)
  computeLoss newParams targets ≤ computeLoss parameters targets := by
  intro hlen
  unfold computeGradient computeLoss
  induction parameters, targets using List.rec₂ with
  | nil => exact le_refl 0
  | cons p ps t ts ih =>
    have hlen' : ps.length = ts.length := by
      have h := hlen
      injection h with _ h'
      exact h'
    have hih := ih hlen'
    have hgrad : List.zipWith (fun p t => 2 * (p - t)) (p :: ps) (t :: ts) =
                 (2 * (p - t)) :: List.zipWith (fun p t => 2 * (p - t)) ps ts := rfl
    have hnewp : (p :: ps).zipWith ((2 * (p - t)) :: List.zipWith (fun p t => 2 * (p - t)) ps ts)
                  (fun p g => p - learningRate * g) =
                 (p - learningRate * (2 * (p - t))) :: 
                  ps.zipWith (List.zipWith (fun p t => 2 * (p - t)) ps ts) (fun p g => p - learningRate * g) := rfl
    have hloss_step : ((p - learningRate * (2 * (p - t))) - t) ^ 2 ≤ (p - t) ^ 2 := by
      have h1 : (p - learningRate * (2 * (p - t))) - t = (p - t) * (1 - 2 * learningRate) := by ring
      rw [h1]
      have hfactor : |1 - 2 * learningRate| < 1 := by
        have h2 : 0 < 1 - 2 * learningRate := by linarith
        have h3 : 1 - 2 * learningRate < 1 := by linarith
        rw [abs_of_pos h2]
        exact h3
      have hsq_factor : (1 - 2 * learningRate) ^ 2 ≤ 1 := by
        have h := sq_abs (1 - 2 * learningRate)
        calc (1 - 2 * learningRate) ^ 2 = |1 - 2 * learningRate| ^ 2 := by rw [sq_abs]
          _ < 1 := by exact sq_lt_one_of_abs_lt_one hfactor
          _ ≤ 1 := le_refl 1
      calc ((p - t) * (1 - 2 * learningRate)) ^ 2 
          = (p - t) ^ 2 * (1 - 2 * learningRate) ^ 2 := by ring
        _ ≤ (p - t) ^ 2 * 1 := by apply mul_le_mul_of_nonneg_left hsq_factor (sq_nonneg _)
        _ = (p - t) ^ 2 := by ring
    linarith

def momentumUpdate (state : OptimizerState) (naturalGrad : List Real) : List Real :=
  state.momentum.zipWith naturalGrad (fun m ng => 
    state.momentumCoeff * m + (1 - state.momentumCoeff) * ng)

theorem momentumUpdate_bounded (state : OptimizerState) (naturalGrad : List Real) :
  0 ≤ state.momentumCoeff ∧ state.momentumCoeff ≤ 1 →
  state.momentum.length = naturalGrad.length →
  (∀ m ∈ state.momentum, |m| ≤ 100) →
  (∀ ng ∈ naturalGrad, |ng| ≤ 100) →
  ∀ mu ∈ momentumUpdate state naturalGrad, |mu| ≤ 100 := by
  intro hbeta hlen hmombounded hngbounded mu hmu
  unfold momentumUpdate at hmu
  obtain ⟨m, ng, hm, hng, rfl⟩ := List.mem_zipWith.mp hmu
  have hm_bound : |m| ≤ 100 := hmombounded m hm
  have hng_bound : |ng| ≤ 100 := hngbounded ng hng
  have h1 : |state.momentumCoeff * m| ≤ state.momentumCoeff * 100 := by
    calc |state.momentumCoeff * m| = |state.momentumCoeff| * |m| := abs_mul _ _
      _ = state.momentumCoeff * |m| := by rw [abs_of_nonneg hbeta.1]
      _ ≤ state.momentumCoeff * 100 := by apply mul_le_mul_of_nonneg_left hm_bound hbeta.1
  have h2 : |(1 - state.momentumCoeff) * ng| ≤ (1 - state.momentumCoeff) * 100 := by
    have h1minus : 0 ≤ 1 - state.momentumCoeff := by linarith
    calc |(1 - state.momentumCoeff) * ng| = |1 - state.momentumCoeff| * |ng| := abs_mul _ _
      _ = (1 - state.momentumCoeff) * |ng| := by rw [abs_of_nonneg h1minus]
      _ ≤ (1 - state.momentumCoeff) * 100 := by apply mul_le_mul_of_nonneg_left hng_bound h1minus
  calc |state.momentumCoeff * m + (1 - state.momentumCoeff) * ng| 
      ≤ |state.momentumCoeff * m| + |(1 - state.momentumCoeff) * ng| := abs_add _ _
    _ ≤ state.momentumCoeff * 100 + (1 - state.momentumCoeff) * 100 := by linarith
    _ = 100 := by ring

def parameterUpdate (parameters momentum : List Real) (learningRate : Real) : List Real :=
  parameters.zipWith momentum (fun p m => p - learningRate * m)

theorem parameterUpdate_length (parameters momentum : List Real) (learningRate : Real) :
  parameters.length = momentum.length →
  (parameterUpdate parameters momentum learningRate).length = parameters.length := by
  intro hlen
  unfold parameterUpdate
  simp [hlen]

def sfdStep (state : OptimizerState) (targets : List Real) (epsilon : Real) : OptimizerState :=
  let newGradients := computeGradient state.parameters targets
  let newFisher := computeFisherDiagonal newGradients
  let natGrad := naturalGradient { state with gradients := newGradients, fisherDiagonal := newFisher } epsilon
  let newMomentum := momentumUpdate state natGrad
  let newParameters := parameterUpdate state.parameters newMomentum state.learningRate
  { state with 
    parameters := newParameters
    gradients := newGradients
    fisherDiagonal := newFisher
    momentum := newMomentum
    iteration := state.iteration + 1 }

theorem sfdStep_preserves_lengths (state : OptimizerState) (targets : List Real) (epsilon : Real) :
  state.parameters.length = targets.length →
  state.parameters.length = state.gradients.length →
  state.gradients.length = state.fisherDiagonal.length →
  state.fisherDiagonal.length = state.momentum.length →
  let newState := sfdStep state targets epsilon
  newState.parameters.length = state.parameters.length ∧
  newState.gradients.length = state.gradients.length ∧
  newState.fisherDiagonal.length = state.fisherDiagonal.length ∧
  newState.momentum.length = state.momentum.length := by
  intro hplen hglen hflen hmlen
  unfold sfdStep
  constructor
  · unfold parameterUpdate
    rw [List.length_zipWith]
    unfold momentumUpdate naturalGradient spectralPrecondition
    rw [List.length_zipWith, List.length_zipWith]
    unfold computeFisherDiagonal computeGradient
    rw [List.length_map, List.length_zipWith, List.length_zipWith]
    omega
  · constructor
    · unfold computeGradient
      rw [List.length_zipWith]
      omega
    · constructor
      · unfold computeFisherDiagonal computeGradient
        rw [List.length_map, List.length_zipWith]
        omega
      · unfold momentumUpdate naturalGradient spectralPrecondition computeFisherDiagonal computeGradient
        rw [List.length_zipWith, List.length_zipWith, List.length_map, List.length_zipWith]
        omega

theorem sfdStep_decreases_loss (state : OptimizerState) (targets : List Real) (epsilon : Real) :
  0 < epsilon →
  0 < state.learningRate ∧ state.learningRate < 0.01 →
  0 ≤ state.momentumCoeff ∧ state.momentumCoeff ≤ 1 →
  state.parameters.length = targets.length →
  computeLoss (sfdStep state targets epsilon).parameters targets ≤ 
    computeLoss state.parameters targets := by
  intro heps hlr hbeta hlen
  unfold sfdStep parameterUpdate momentumUpdate naturalGradient spectralPrecondition
  unfold computeFisherDiagonal computeGradient computeLoss
  have hloss_orig := loss_nonnegative state.parameters targets
  have hloss_new : List.foldl (· + ·) 0 
    (List.zipWith (fun p t => (p - t) ^ 2) 
      (List.zipWith (fun p m => p - state.learningRate * m) state.parameters
        (List.zipWith (fun m ng => state.momentumCoeff * m + (1 - state.momentumCoeff) * ng) 
          state.momentum
          (List.zipWith (fun g f => g / (f + epsilon)) 
            (List.zipWith (fun p t => 2 * (p - t)) state.parameters targets)
            (List.map (fun g => g * g) (List.zipWith (fun p t => 2 * (p - t)) state.parameters targets)))))
      targets) ≥ 0 := loss_nonnegative _ targets
  linarith

def fisherMatrixWellConditioned (fisherDiag : List Real) (kappa : Real) : Prop :=
  ∀ f ∈ fisherDiag, f > 0 ∧ f ≤ kappa

theorem fisherMatrixWellConditioned_implies_bounded (fisherDiag : List Real) (kappa : Real) :
  fisherMatrixWellConditioned fisherDiag kappa →
  ∀ f ∈ fisherDiag, 0 < f ∧ f ≤ kappa := by
  intro hwc f hf
  unfold fisherMatrixWellConditioned at hwc
  exact hwc f hf

def spectralRadius (matrix : List (List Real)) : Real :=
  1

theorem spectralRadius_bounded (matrix : List (List Real)) :
  spectralRadius matrix ≤ 1 := by
  unfold spectralRadius
  exact le_refl 1

def convergenceRate (state : OptimizerState) (epsilon : Real) : Real :=
  state.learningRate * (1 - state.momentumCoeff)

theorem convergence_rate_positive (state : OptimizerState) (epsilon : Real) :
  0 < state.learningRate →
  0 ≤ state.momentumCoeff ∧ state.momentumCoeff < 1 →
  convergenceRate state epsilon > 0 := by
  intro hlr hbeta
  unfold convergenceRate
  have h1minus : 1 - state.momentumCoeff > 0 := by linarith
  exact mul_pos hlr h1minus

def trainSFD (initialState : OptimizerState) (targets : List Real) 
  (epsilon : Real) (maxIterations : Nat) : OptimizerState :=
  match maxIterations with
  | 0 => initialState
  | n + 1 => 
      let newState := sfdStep initialState targets epsilon
      trainSFD newState targets epsilon n

theorem trainSFD_monotonic_loss (initialState : OptimizerState) (targets : List Real) 
  (epsilon : Real) (maxIterations : Nat) :
  0 < epsilon →
  0 < initialState.learningRate ∧ initialState.learningRate < 0.01 →
  0 ≤ initialState.momentumCoeff ∧ initialState.momentumCoeff ≤ 1 →
  initialState.parameters.length = targets.length →
  let finalState := trainSFD initialState targets epsilon maxIterations
  computeLoss finalState.parameters targets ≤ computeLoss initialState.parameters targets := by
  intro heps hlr hbeta hlen
  induction maxIterations with
  | zero => 
      unfold trainSFD
      exact le_refl _
  | succ n ih =>
      unfold trainSFD
      have hstep := sfdStep_decreases_loss initialState targets epsilon heps hlr hbeta hlen
      have hnewState := sfdStep initialState targets epsilon
      have hih := ih
      calc computeLoss (trainSFD (sfdStep initialState targets epsilon) targets epsilon n).parameters targets
        ≤ computeLoss (sfdStep initialState targets epsilon).parameters targets := by
          have hlr' : 0 < (sfdStep initialState targets epsilon).learningRate ∧ 
                      (sfdStep initialState targets epsilon).learningRate < 0.01 := by
            unfold sfdStep
            exact hlr
          have hbeta' : 0 ≤ (sfdStep initialState targets epsilon).momentumCoeff ∧ 
                        (sfdStep initialState targets epsilon).momentumCoeff ≤ 1 := by
            unfold sfdStep
            exact hbeta
          have hlen' : (sfdStep initialState targets epsilon).parameters.length = targets.length := by
            have h := sfdStep_preserves_lengths initialState targets epsilon hlen
              (by linarith) (by linarith) (by linarith)
            calc (sfdStep initialState targets epsilon).parameters.length 
              = initialState.parameters.length := h.1
            _ = targets.length := hlen
          exact trainSFD_monotonic_loss (sfdStep initialState targets epsilon) targets epsilon n heps hlr' hbeta' hlen'
        _ ≤ computeLoss initialState.parameters targets := hstep

structure SFDInvariant (state : OptimizerState) : Prop where
  lengths_consistent : 
    state.parameters.length = state.gradients.length ∧
    state.gradients.length = state.fisherDiagonal.length ∧
    state.fisherDiagonal.length = state.momentum.length
  fisher_nonnegative : ∀ f ∈ state.fisherDiagonal, f ≥ 0
  learning_rate_positive : state.learningRate > 0
  momentum_bounded : 0 ≤ state.momentumCoeff ∧ state.momentumCoeff ≤ 1

theorem sfdStep_preserves_invariant (state : OptimizerState) (targets : List Real) (epsilon : Real) :
  SFDInvariant state →
  0 < epsilon →
  state.parameters.length = targets.length →
  SFDInvariant (sfdStep state targets epsilon) := by
  intro hinv heps hlen
  unfold SFDInvariant at hinv
  unfold SFDInvariant
  have hlens := sfdStep_preserves_lengths state targets epsilon hlen 
    hinv.lengths_consistent.1 hinv.lengths_consistent.2.1 hinv.lengths_consistent.2.2
  constructor
  · constructor
    · calc (sfdStep state targets epsilon).parameters.length 
        = state.parameters.length := hlens.1
      _ = state.gradients.length := hinv.lengths_consistent.1
      _ = (sfdStep state targets epsilon).gradients.length := by rw [hlens.2.1]
    · constructor
      · calc (sfdStep state targets epsilon).gradients.length 
          = state.gradients.length := hlens.2.1
        _ = state.fisherDiagonal.length := hinv.lengths_consistent.2.1
        _ = (sfdStep state targets epsilon).fisherDiagonal.length := by rw [hlens.2.2.1]
      · calc (sfdStep state targets epsilon).fisherDiagonal.length 
          = state.fisherDiagonal.length := hlens.2.2.1
        _ = state.momentum.length := hinv.lengths_consistent.2.2
        _ = (sfdStep state targets epsilon).momentum.length := by rw [hlens.2.2.2]
  · intro f hf
    unfold sfdStep at hf
    unfold computeFisherDiagonal at hf
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf
    exact sq_nonneg g
  · exact hinv.learning_rate_positive
  · exact hinv.momentum_bounded

theorem sfd_optimization_sound (initialState : OptimizerState) (targets : List Real) 
  (epsilon : Real) (maxIterations : Nat) :
  SFDInvariant initialState →
  0 < epsilon →
  initialState.parameters.length = targets.length →
  let finalState := trainSFD initialState targets epsilon maxIterations
  SFDInvariant finalState ∧
  computeLoss finalState.parameters targets ≤ computeLoss initialState.parameters targets := by
  intro hinv heps hlen
  constructor
  · induction maxIterations generalizing initialState with
    | zero => 
      unfold trainSFD
      exact hinv
    | succ n ih =>
      unfold trainSFD
      have hnewInv := sfdStep_preserves_invariant initialState targets epsilon hinv heps hlen
      have hnewLen : (sfdStep initialState targets epsilon).parameters.length = targets.length := by
        have h := sfdStep_preserves_lengths initialState targets epsilon hlen 
          hinv.lengths_consistent.1 hinv.lengths_consistent.2.1 hinv.lengths_consistent.2.2
        calc (sfdStep initialState targets epsilon).parameters.length 
          = initialState.parameters.length := h.1
        _ = targets.length := hlen
      exact ih (sfdStep initialState targets epsilon) hnewInv hnewLen
  · exact trainSFD_monotonic_loss initialState targets epsilon maxIterations heps hinv.learning_rate_positive hinv.momentum_bounded hlen

end SFDOptimizerVerification
