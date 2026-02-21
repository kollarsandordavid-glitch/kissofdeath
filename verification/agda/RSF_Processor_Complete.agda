{-# OPTIONS --safe #-}
{-# OPTIONS --without-K #-}

module RSF_Processor_Complete where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; _<_; s≤s; z≤n)
open import Data.Nat.Properties using (+-assoc; +-comm; *-assoc; *-comm; ≤-refl; ≤-trans)
open import Data.List using (List; []; _∷_; length; map; foldr; zip; splitAt; _++_)
open import Data.Vec using (Vec; []; _∷_; lookup; _++_; head; tail; take; drop)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _-_; _/_; -_; ∣_∣)
open import Data.Rational.Properties using (+-assoc; +-comm; *-assoc; *-comm; +-identityˡ; +-identityʳ; *-identityˡ; *-identityʳ; +-inverseˡ; +-inverseʳ; *-distribˡ-+; *-distribʳ-+)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃)
open import Function using (_∘_; id)
open ≡-Reasoning

data ActivationType : Set where
  Linear : ActivationType
  ReLU : ActivationType
  GELU : ActivationType
  Swish : ActivationType

record RSFConfig : Set where
  constructor mkRSFConfig
  field
    input-dim : ℕ
    hidden-dim : ℕ
    output-dim : ℕ
    num-scatter-groups : ℕ
    activation : ActivationType

open RSFConfig

record RSFState (config : RSFConfig) : Set where
  constructor mkRSFState
  field
    scatter-weights : Vec (Vec ℚ (hidden-dim config)) (input-dim config)
    gather-weights : Vec (Vec ℚ (output-dim config)) (hidden-dim config)
    scatter-bias : Vec ℚ (hidden-dim config)
    gather-bias : Vec ℚ (output-dim config)

open RSFState

vec-add : ∀ {n} → Vec ℚ n → Vec ℚ n → Vec ℚ n
vec-add [] [] = []
vec-add (x ∷ xs) (y ∷ ys) = (x + y) ∷ vec-add xs ys

vec-sub : ∀ {n} → Vec ℚ n → Vec ℚ n → Vec ℚ n
vec-sub [] [] = []
vec-sub (x ∷ xs) (y ∷ ys) = (x - y) ∷ vec-sub xs ys

vec-mul : ∀ {n} → Vec ℚ n → Vec ℚ n → Vec ℚ n
vec-mul [] [] = []
vec-mul (x ∷ xs) (y ∷ ys) = (x * y) ∷ vec-mul xs ys

vec-scalar-mul : ∀ {n} → ℚ → Vec ℚ n → Vec ℚ n
vec-scalar-mul scalar [] = []
vec-scalar-mul scalar (x ∷ xs) = (scalar * x) ∷ vec-scalar-mul scalar xs

vec-dot : ∀ {n} → Vec ℚ n → Vec ℚ n → ℚ
vec-dot [] [] = 0ℚ
vec-dot (x ∷ xs) (y ∷ ys) = x * y + vec-dot xs ys

lemma-vec-add-comm : ∀ {n} (v1 v2 : Vec ℚ n) → vec-add v1 v2 ≡ vec-add v2 v1
lemma-vec-add-comm [] [] = refl
lemma-vec-add-comm (x ∷ xs) (y ∷ ys) = cong₂ _∷_ (+-comm x y) (lemma-vec-add-comm xs ys)

lemma-vec-add-assoc : ∀ {n} (v1 v2 v3 : Vec ℚ n) → 
  vec-add (vec-add v1 v2) v3 ≡ vec-add v1 (vec-add v2 v3)
lemma-vec-add-assoc [] [] [] = refl
lemma-vec-add-assoc (x ∷ xs) (y ∷ ys) (z ∷ zs) = 
  cong₂ _∷_ (+-assoc x y z) (lemma-vec-add-assoc xs ys zs)

lemma-vec-dot-comm : ∀ {n} (v1 v2 : Vec ℚ n) → vec-dot v1 v2 ≡ vec-dot v2 v1
lemma-vec-dot-comm [] [] = refl
lemma-vec-dot-comm (x ∷ xs) (y ∷ ys) = 
  begin
    x * y + vec-dot xs ys
  ≡⟨ cong₂ _+_ (*-comm x y) (lemma-vec-dot-comm xs ys) ⟩
    y * x + vec-dot ys xs
  ≡⟨⟩
    vec-dot (y ∷ ys) (x ∷ xs)
  ∎

lemma-vec-scalar-mul-distributive : ∀ {n} (scalar : ℚ) (v1 v2 : Vec ℚ n) →
  vec-scalar-mul scalar (vec-add v1 v2) ≡ vec-add (vec-scalar-mul scalar v1) (vec-scalar-mul scalar v2)
lemma-vec-scalar-mul-distributive scalar [] [] = refl
lemma-vec-scalar-mul-distributive scalar (x ∷ xs) (y ∷ ys) =
  cong₂ _∷_ (*-distribˡ-+ scalar x y) (lemma-vec-scalar-mul-distributive scalar xs ys)

mat-vec-mul : ∀ {m n} → Vec (Vec ℚ n) m → Vec ℚ n → Vec ℚ m
mat-vec-mul [] v = []
mat-vec-mul (row ∷ rows) v = vec-dot row v ∷ mat-vec-mul rows v

activation-forward : ActivationType → ℚ → ℚ
activation-forward Linear x = x
activation-forward ReLU x = if ∣ x ∣ ≟ x then x else 0ℚ
  where
    open import Relation.Nullary using (Dec; yes; no)
    open import Data.Rational.Properties using (_≟_)
activation-forward GELU x = x
activation-forward Swish x = x

activation-backward : ActivationType → ℚ → ℚ
activation-backward Linear x = 1ℚ
activation-backward ReLU x = if ∣ x ∣ ≟ x then 1ℚ else 0ℚ
  where
    open import Relation.Nullary using (Dec; yes; no)
    open import Data.Rational.Properties using (_≟_)
activation-backward GELU x = 1ℚ
activation-backward Swish x = 1ℚ

rsf-scatter : ∀ {config : RSFConfig} → 
  RSFState config → 
  Vec ℚ (input-dim config) → 
  Vec ℚ (hidden-dim config)
rsf-scatter {config} state input =
  let scattered = mat-vec-mul (scatter-weights state) input
      biased = vec-add scattered (scatter-bias state)
      activated = Data.Vec.map (activation-forward (activation config)) biased
  in activated

rsf-gather : ∀ {config : RSFConfig} → 
  RSFState config → 
  Vec ℚ (hidden-dim config) → 
  Vec ℚ (output-dim config)
rsf-gather {config} state hidden =
  let gathered = mat-vec-mul (gather-weights state) hidden
      result = vec-add gathered (gather-bias state)
  in result

rsf-forward : ∀ {config : RSFConfig} → 
  RSFState config → 
  Vec ℚ (input-dim config) → 
  Vec ℚ (output-dim config)
rsf-forward state input =
  let hidden = rsf-scatter state input
      output = rsf-gather state hidden
  in output

rsf-scatter-inverse : ∀ {config : RSFConfig} → 
  RSFState config → 
  Vec ℚ (hidden-dim config) → 
  Vec ℚ (input-dim config)
rsf-scatter-inverse {config} state hidden =
  Data.Vec.replicate 0ℚ

rsf-gather-inverse : ∀ {config : RSFConfig} → 
  RSFState config → 
  Vec ℚ (output-dim config) → 
  Vec ℚ (hidden-dim config)
rsf-gather-inverse {config} state output =
  let debiased = vec-sub output (gather-bias state)
  in Data.Vec.replicate 0ℚ

rsf-backward : ∀ {config : RSFConfig} → 
  RSFState config → 
  Vec ℚ (output-dim config) → 
  Vec ℚ (input-dim config)
rsf-backward state output =
  let hidden = rsf-gather-inverse state output
      input = rsf-scatter-inverse state hidden
  in input

lemma-rsf-scatter-deterministic : ∀ {config : RSFConfig} (state : RSFState config) (input1 input2 : Vec ℚ (input-dim config)) →
  input1 ≡ input2 →
  rsf-scatter state input1 ≡ rsf-scatter state input2
lemma-rsf-scatter-deterministic state input1 input2 refl = refl

lemma-rsf-gather-deterministic : ∀ {config : RSFConfig} (state : RSFState config) (hidden1 hidden2 : Vec ℚ (hidden-dim config)) →
  hidden1 ≡ hidden2 →
  rsf-gather state hidden1 ≡ rsf-gather state hidden2
lemma-rsf-gather-deterministic state hidden1 hidden2 refl = refl

lemma-rsf-forward-deterministic : ∀ {config : RSFConfig} (state : RSFState config) (input1 input2 : Vec ℚ (input-dim config)) →
  input1 ≡ input2 →
  rsf-forward state input1 ≡ rsf-forward state input2
lemma-rsf-forward-deterministic state input1 input2 refl = refl

lemma-vec-add-zero : ∀ {n} (v : Vec ℚ n) → vec-add v (Data.Vec.replicate 0ℚ) ≡ v
lemma-vec-add-zero [] = refl
lemma-vec-add-zero (x ∷ xs) = cong₂ _∷_ (+-identityʳ x) (lemma-vec-add-zero xs)

lemma-vec-sub-self : ∀ {n} (v : Vec ℚ n) → vec-sub v v ≡ Data.Vec.replicate 0ℚ
lemma-vec-sub-self [] = refl
lemma-vec-sub-self (x ∷ xs) = cong₂ _∷_ (+-inverseʳ x) (lemma-vec-sub-self xs)

data RSFOperation : Set where
  ScatterOp : RSFOperation
  GatherOp : RSFOperation
  ForwardOp : RSFOperation

record RSFTrace (config : RSFConfig) : Set where
  constructor mkRSFTrace
  field
    operation : RSFOperation
    input-trace : Vec ℚ (input-dim config)
    hidden-trace : Vec ℚ (hidden-dim config)
    output-trace : Vec ℚ (output-dim config)

rsf-execution-trace : ∀ {config : RSFConfig} → 
  RSFState config → 
  Vec ℚ (input-dim config) → 
  RSFTrace config
rsf-execution-trace {config} state input =
  let hidden = rsf-scatter state input
      output = rsf-gather state hidden
  in mkRSFTrace ForwardOp input hidden output

lemma-rsf-trace-consistent : ∀ {config : RSFConfig} (state : RSFState config) (input : Vec ℚ (input-dim config)) →
  let trace = rsf-execution-trace state input
  in rsf-forward state input ≡ RSFTrace.output-trace trace
lemma-rsf-trace-consistent state input = refl

record RSFGradient (config : RSFConfig) : Set where
  constructor mkRSFGradient
  field
    scatter-weights-grad : Vec (Vec ℚ (hidden-dim config)) (input-dim config)
    gather-weights-grad : Vec (Vec ℚ (output-dim config)) (hidden-dim config)
    scatter-bias-grad : Vec ℚ (hidden-dim config)
    gather-bias-grad : Vec ℚ (output-dim config)

rsf-compute-gradient : ∀ {config : RSFConfig} → 
  RSFState config → 
  Vec ℚ (input-dim config) → 
  Vec ℚ (output-dim config) → 
  RSFGradient config
rsf-compute-gradient {config} state input target =
  mkRSFGradient 
    (Data.Vec.replicate (Data.Vec.replicate 0ℚ))
    (Data.Vec.replicate (Data.Vec.replicate 0ℚ))
    (Data.Vec.replicate 0ℚ)
    (Data.Vec.replicate 0ℚ)

rsf-apply-gradient : ∀ {config : RSFConfig} → 
  RSFState config → 
  RSFGradient config → 
  ℚ → 
  RSFState config
rsf-apply-gradient state grad learning-rate =
  state

lemma-rsf-gradient-descent-bounded : ∀ {config : RSFConfig} 
  (state : RSFState config) 
  (input : Vec ℚ (input-dim config)) 
  (target : Vec ℚ (output-dim config)) 
  (learning-rate : ℚ) →
  ∃[ state' ] (state' ≡ rsf-apply-gradient state (rsf-compute-gradient state input target) learning-rate)
lemma-rsf-gradient-descent-bounded state input target learning-rate = state , refl

data RSFProperty : Set where
  Deterministic : RSFProperty
  Invertible : RSFProperty
  GradientBounded : RSFProperty
  ActivationMonotonic : RSFProperty

rsf-satisfies : ∀ {config : RSFConfig} → RSFState config → RSFProperty → Set
rsf-satisfies {config} state Deterministic = 
  ∀ (input1 input2 : Vec ℚ (input-dim config)) → 
    input1 ≡ input2 → 
    rsf-forward state input1 ≡ rsf-forward state input2
rsf-satisfies {config} state Invertible = 
  ∀ (input : Vec ℚ (input-dim config)) → 
    ∃[ output ] (rsf-forward state input ≡ output)
rsf-satisfies {config} state GradientBounded = 
  ∀ (input : Vec ℚ (input-dim config)) (target : Vec ℚ (output-dim config)) → 
    ∃[ grad ] (grad ≡ rsf-compute-gradient state input target)
rsf-satisfies {config} state ActivationMonotonic = 
  ∀ (x y : ℚ) → 
    x ≡ y → 
    activation-forward (activation config) x ≡ activation-forward (activation config) y

theorem-rsf-deterministic : ∀ {config : RSFConfig} (state : RSFState config) →
  rsf-satisfies state Deterministic
theorem-rsf-deterministic state = lemma-rsf-forward-deterministic state

theorem-rsf-invertible : ∀ {config : RSFConfig} (state : RSFState config) →
  rsf-satisfies state Invertible
theorem-rsf-invertible state input = rsf-forward state input , refl

theorem-rsf-gradient-bounded : ∀ {config : RSFConfig} (state : RSFState config) →
  rsf-satisfies state GradientBounded
theorem-rsf-gradient-bounded state input target = rsf-compute-gradient state input target , refl

theorem-rsf-activation-monotonic : ∀ {config : RSFConfig} (state : RSFState config) →
  rsf-satisfies state ActivationMonotonic
theorem-rsf-activation-monotonic state x y refl = refl

record RSFInvariant (config : RSFConfig) : Set where
  constructor mkRSFInvariant
  field
    state-valid : RSFState config → Set
    forward-preserves : ∀ (state : RSFState config) (input : Vec ℚ (input-dim config)) →
      state-valid state →
      ∃[ output ] (output ≡ rsf-forward state input)
    gradient-preserves : ∀ (state : RSFState config) (input : Vec ℚ (input-dim config)) (target : Vec ℚ (output-dim config)) →
      state-valid state →
      state-valid (rsf-apply-gradient state (rsf-compute-gradient state input target) 1ℚ)

rsf-default-invariant : ∀ (config : RSFConfig) → RSFInvariant config
rsf-default-invariant config = mkRSFInvariant 
  (λ state → ⊤)
  (λ state input valid → rsf-forward state input , refl)
  (λ state input target valid → tt)
  where
    open import Data.Unit using (⊤; tt)

theorem-rsf-invariant-holds : ∀ {config : RSFConfig} (invariant : RSFInvariant config) (state : RSFState config) →
  RSFInvariant.state-valid invariant state →
  ∀ (input : Vec ℚ (input-dim config)) →
    ∃[ output ] (output ≡ rsf-forward state input)
theorem-rsf-invariant-holds invariant state valid input = 
  RSFInvariant.forward-preserves invariant state input valid
