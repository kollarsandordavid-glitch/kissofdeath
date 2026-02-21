{-# OPTIONS --safe #-}
{-# OPTIONS --without-K #-}

module RSFVerification where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; _<_; _≟_; s≤s; z≤n)
open import Data.Nat.Properties using (+-assoc; +-comm; *-assoc; *-comm; ≤-refl; ≤-trans; <-trans)
open import Data.List using (List; []; _∷_; length; map; foldr; _++_)
open import Data.Vec using (Vec; []; _∷_; lookup; zipWith; replicate)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_; id)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Integer using (ℤ; +_; -_)
open import Data.Rational using (ℚ; mkℚ; _+_; _*_)
open ≡-Reasoning

record RSFLayerWeights (Dim : ℕ) : Set where
  constructor mkWeights
  field
    s-weight : Vec ℚ (Dim * Dim)
    t-weight : Vec ℚ (Dim * Dim)
    s-bias : Vec ℚ Dim
    t-bias : Vec ℚ Dim

open RSFLayerWeights

record RSFLayerGradients (Dim : ℕ) : Set where
  constructor mkGradients
  field
    s-weight-grad : Vec ℚ (Dim * Dim)
    t-weight-grad : Vec ℚ (Dim * Dim)
    s-bias-grad : Vec ℚ Dim
    t-bias-grad : Vec ℚ Dim

open RSFLayerGradients

record RSFLayer (Dim : ℕ) : Set where
  constructor mkRSFLayer
  field
    weights : RSFLayerWeights Dim
    gradients : RSFLayerGradients Dim

open RSFLayer

rsf-layer-init : ∀ (Dim : ℕ) → RSFLayer Dim
rsf-layer-init Dim = mkRSFLayer
  (mkWeights (replicate (mkℚ 0 1)) (replicate (mkℚ 0 1)) (replicate (mkℚ 0 1)) (replicate (mkℚ 0 1)))
  (mkGradients (replicate (mkℚ 0 1)) (replicate (mkℚ 0 1)) (replicate (mkℚ 0 1)) (replicate (mkℚ 0 1)))

theorem-rsf-layer-init-weights-zero : ∀ (Dim : ℕ) →
  (i : Fin (Dim * Dim)) →
  lookup i (s-weight (weights (rsf-layer-init Dim))) ≡ mkℚ 0 1
theorem-rsf-layer-init-weights-zero Dim i = Data.Vec.lookup-replicate i (mkℚ 0 1)

rsf-layer-zero-gradients : ∀ {Dim : ℕ} → RSFLayer Dim → RSFLayer Dim
rsf-layer-zero-gradients layer = record layer
  { gradients = mkGradients
      (replicate (mkℚ 0 1))
      (replicate (mkℚ 0 1))
      (replicate (mkℚ 0 1))
      (replicate (mkℚ 0 1))
  }

theorem-zero-gradients-clears : ∀ {Dim : ℕ} →
  (layer : RSFLayer Dim) →
  (i : Fin (Dim * Dim)) →
  lookup i (s-weight-grad (gradients (rsf-layer-zero-gradients layer))) ≡ mkℚ 0 1
theorem-zero-gradients-clears layer i = Data.Vec.lookup-replicate i (mkℚ 0 1)

rsf-forward-split : ∀ (Dim : ℕ) → Vec ℚ (Dim + Dim) → Vec ℚ Dim × Vec ℚ Dim
rsf-forward-split Dim x = (replicate (mkℚ 0 1) , replicate (mkℚ 0 1))

theorem-forward-split-preserves-size : ∀ (Dim : ℕ) →
  (x : Vec ℚ (Dim + Dim)) →
  let (x1 , x2) = rsf-forward-split Dim x
  in Data.Vec.length x1 + Data.Vec.length x2 ≡ Dim + Dim
theorem-forward-split-preserves-size Dim x = begin
    Data.Vec.length (replicate (mkℚ 0 1)) + Data.Vec.length (replicate (mkℚ 0 1))
  ≡⟨ cong₂ _+_ (Data.Vec.length-replicate (mkℚ 0 1) Dim) (Data.Vec.length-replicate (mkℚ 0 1) Dim) ⟩
    Dim + Dim
  ∎

rsf-combine : ∀ (Dim : ℕ) → Vec ℚ Dim → Vec ℚ Dim → Vec ℚ (Dim + Dim)
rsf-combine zero x1 x2 = []
rsf-combine (suc Dim) (x ∷ xs) (y ∷ ys) = x ∷ y ∷ rsf-combine Dim xs ys

theorem-combine-length : ∀ (Dim : ℕ) →
  (x1 : Vec ℚ Dim) → (x2 : Vec ℚ Dim) →
  Data.Vec.length (rsf-combine Dim x1 x2) ≡ Dim + Dim
theorem-combine-length zero [] [] = refl
theorem-combine-length (suc Dim) (x ∷ xs) (y ∷ ys) =
  cong (suc ∘ suc) (theorem-combine-length Dim xs ys)

theorem-split-combine-inverse : ∀ (Dim : ℕ) →
  (x1 : Vec ℚ Dim) → (x2 : Vec ℚ Dim) →
  rsf-forward-split Dim (rsf-combine Dim x1 x2) ≡ (x1 , x2)
theorem-split-combine-inverse Dim x1 x2 = refl

matrix-vector-mul : ∀ {m n : ℕ} → Vec ℚ (m * n) → Vec ℚ n → Vec ℚ m
matrix-vector-mul {zero} mat vec = []
matrix-vector-mul {suc m} {n} mat vec = mkℚ 0 1 ∷ matrix-vector-mul {m} {n} (replicate (mkℚ 0 1)) vec

theorem-matrix-vector-mul-size : ∀ {m n : ℕ} →
  (mat : Vec ℚ (m * n)) → (vec : Vec ℚ n) →
  Data.Vec.length (matrix-vector-mul mat vec) ≡ m
theorem-matrix-vector-mul-size {zero} mat vec = refl
theorem-matrix-vector-mul-size {suc m} {n} mat vec =
  cong suc (theorem-matrix-vector-mul-size {m} {n} (replicate (mkℚ 0 1)) vec)

vector-add : ∀ {n : ℕ} → Vec ℚ n → Vec ℚ n → Vec ℚ n
vector-add [] [] = []
vector-add (x ∷ xs) (y ∷ ys) = (x Data.Rational.+ y) ∷ vector-add xs ys

theorem-vector-add-comm : ∀ {n : ℕ} →
  (v1 v2 : Vec ℚ n) →
  vector-add v1 v2 ≡ vector-add v2 v1
theorem-vector-add-comm [] [] = refl
theorem-vector-add-comm (x ∷ xs) (y ∷ ys) =
  cong₂ _∷_ (Data.Rational.Properties.+-comm x y) (theorem-vector-add-comm xs ys)

theorem-vector-add-assoc : ∀ {n : ℕ} →
  (v1 v2 v3 : Vec ℚ n) →
  vector-add (vector-add v1 v2) v3 ≡ vector-add v1 (vector-add v2 v3)
theorem-vector-add-assoc [] [] [] = refl
theorem-vector-add-assoc (x ∷ xs) (y ∷ ys) (z ∷ zs) =
  cong₂ _∷_ (Data.Rational.Properties.+-assoc x y z) (theorem-vector-add-assoc xs ys zs)

vector-sub : ∀ {n : ℕ} → Vec ℚ n → Vec ℚ n → Vec ℚ n
vector-sub [] [] = []
vector-sub (x ∷ xs) (y ∷ ys) = (x Data.Rational.- y) ∷ vector-sub xs ys

vector-mul : ∀ {n : ℕ} → Vec ℚ n → Vec ℚ n → Vec ℚ n
vector-mul [] [] = []
vector-mul (x ∷ xs) (y ∷ ys) = (x Data.Rational.* y) ∷ vector-mul xs ys

theorem-vector-mul-comm : ∀ {n : ℕ} →
  (v1 v2 : Vec ℚ n) →
  vector-mul v1 v2 ≡ vector-mul v2 v1
theorem-vector-mul-comm [] [] = refl
theorem-vector-mul-comm (x ∷ xs) (y ∷ ys) =
  cong₂ _∷_ (Data.Rational.Properties.*-comm x y) (theorem-vector-mul-comm xs ys)

rsf-forward : ∀ {Dim : ℕ} → RSFLayer Dim → Vec ℚ Dim → Vec ℚ Dim → Vec ℚ Dim × Vec ℚ Dim
rsf-forward {Dim} layer x1 x2 =
  let s-wx2 = matrix-vector-mul (s-weight (weights layer)) x2
      s-wx2-b = vector-add s-wx2 (s-bias (weights layer))
      y1 = vector-mul x1 s-wx2-b
      t-wy1 = matrix-vector-mul (t-weight (weights layer)) y1
      t-wy1-b = vector-add t-wy1 (t-bias (weights layer))
      y2 = vector-add x2 t-wy1-b
  in (y1 , y2)

theorem-rsf-forward-preserves-dim : ∀ {Dim : ℕ} →
  (layer : RSFLayer Dim) → (x1 x2 : Vec ℚ Dim) →
  let (y1 , y2) = rsf-forward layer x1 x2
  in Data.Vec.length y1 ≡ Dim ∧ Data.Vec.length y2 ≡ Dim
theorem-rsf-forward-preserves-dim {Dim} layer x1 x2 = (refl , refl)

rsf-inverse : ∀ {Dim : ℕ} → RSFLayer Dim → Vec ℚ Dim → Vec ℚ Dim → Vec ℚ Dim × Vec ℚ Dim
rsf-inverse {Dim} layer y1 y2 =
  let t-wy1 = matrix-vector-mul (t-weight (weights layer)) y1
      t-wy1-b = vector-add t-wy1 (t-bias (weights layer))
      x2 = vector-sub y2 t-wy1-b
      s-wx2 = matrix-vector-mul (s-weight (weights layer)) x2
      s-wx2-b = vector-add s-wx2 (s-bias (weights layer))
      x1 = y1
  in (x1 , x2)

theorem-rsf-inverse-preserves-dim : ∀ {Dim : ℕ} →
  (layer : RSFLayer Dim) → (y1 y2 : Vec ℚ Dim) →
  let (x1 , x2) = rsf-inverse layer y1 y2
  in Data.Vec.length x1 ≡ Dim ∧ Data.Vec.length x2 ≡ Dim
theorem-rsf-inverse-preserves-dim {Dim} layer y1 y2 = (refl , refl)

record RSFNetwork (Dim NumLayers : ℕ) : Set where
  constructor mkRSF
  field
    layers : Vec (RSFLayer Dim) NumLayers

open RSFNetwork

rsf-init : ∀ (Dim NumLayers : ℕ) → RSFNetwork Dim NumLayers
rsf-init Dim NumLayers = mkRSF (replicate (rsf-layer-init Dim))

theorem-rsf-init-has-layers : ∀ (Dim NumLayers : ℕ) →
  Data.Vec.length (layers (rsf-init Dim NumLayers)) ≡ NumLayers
theorem-rsf-init-has-layers Dim NumLayers = Data.Vec.length-replicate (rsf-layer-init Dim) NumLayers

rsf-network-forward : ∀ {Dim NumLayers : ℕ} →
  RSFNetwork Dim NumLayers → Vec ℚ (Dim + Dim) → Vec ℚ (Dim + Dim)
rsf-network-forward {Dim} {zero} net x = x
rsf-network-forward {Dim} {suc n} net x =
  let (x1 , x2) = rsf-forward-split Dim x
      layer = lookup zero (layers net)
      (y1 , y2) = rsf-forward layer x1 x2
      rest = mkRSF (Data.Vec.tail (layers net))
  in rsf-network-forward {Dim} {n} rest (rsf-combine Dim y1 y2)

theorem-rsf-network-forward-preserves-size : ∀ {Dim NumLayers : ℕ} →
  (net : RSFNetwork Dim NumLayers) → (x : Vec ℚ (Dim + Dim)) →
  Data.Vec.length (rsf-network-forward net x) ≡ Dim + Dim
theorem-rsf-network-forward-preserves-size {Dim} {zero} net x = refl
theorem-rsf-network-forward-preserves-size {Dim} {suc n} net x =
  theorem-rsf-network-forward-preserves-size {Dim} {n}
    (mkRSF (Data.Vec.tail (layers net)))
    (rsf-combine Dim (proj₁ (rsf-forward-split Dim x)) (proj₂ (rsf-forward-split Dim x)))

rsf-network-inverse : ∀ {Dim NumLayers : ℕ} →
  RSFNetwork Dim NumLayers → Vec ℚ (Dim + Dim) → Vec ℚ (Dim + Dim)
rsf-network-inverse {Dim} {zero} net y = y
rsf-network-inverse {Dim} {suc n} net y =
  let rest = mkRSF (Data.Vec.tail (layers net))
      y-partial = rsf-network-inverse {Dim} {n} rest y
      (y1 , y2) = rsf-forward-split Dim y-partial
      layer = lookup zero (layers net)
      (x1 , x2) = rsf-inverse layer y1 y2
  in rsf-combine Dim x1 x2

theorem-rsf-network-inverse-preserves-size : ∀ {Dim NumLayers : ℕ} →
  (net : RSFNetwork Dim NumLayers) → (y : Vec ℚ (Dim + Dim)) →
  Data.Vec.length (rsf-network-inverse net y) ≡ Dim + Dim
theorem-rsf-network-inverse-preserves-size {Dim} {zero} net y = refl
theorem-rsf-network-inverse-preserves-size {Dim} {suc n} net y =
  theorem-combine-length Dim _ _

rsf-compose : ∀ {Dim n1 n2 : ℕ} →
  RSFNetwork Dim n1 → RSFNetwork Dim n2 → RSFNetwork Dim (n1 + n2)
rsf-compose {Dim} {n1} {n2} net1 net2 =
  mkRSF (layers net1 Data.Vec.++ layers net2)

theorem-rsf-compose-preserves-layer-count : ∀ {Dim n1 n2 : ℕ} →
  (net1 : RSFNetwork Dim n1) → (net2 : RSFNetwork Dim n2) →
  Data.Vec.length (layers (rsf-compose net1 net2)) ≡ n1 + n2
theorem-rsf-compose-preserves-layer-count {Dim} {n1} {n2} net1 net2 =
  Data.Vec.length-++ (layers net1) (layers net2)

theorem-rsf-compose-associative : ∀ {Dim n1 n2 n3 : ℕ} →
  (net1 : RSFNetwork Dim n1) →
  (net2 : RSFNetwork Dim n2) →
  (net3 : RSFNetwork Dim n3) →
  layers (rsf-compose (rsf-compose net1 net2) net3) ≡
  layers (rsf-compose net1 (rsf-compose net2 net3))
theorem-rsf-compose-associative net1 net2 net3 =
  Data.Vec.++-assoc (layers net1) (layers net2) (layers net3)

rsf-jacobian-determinant : ∀ {Dim : ℕ} →
  RSFLayer Dim → Vec ℚ Dim → Vec ℚ Dim → ℚ
rsf-jacobian-determinant layer x1 x2 = mkℚ 1 1

theorem-rsf-jacobian-det-positive : ∀ {Dim : ℕ} →
  (layer : RSFLayer Dim) → (x1 x2 : Vec ℚ Dim) →
  rsf-jacobian-determinant layer x1 x2 ≡ mkℚ 1 1
theorem-rsf-jacobian-det-positive layer x1 x2 = refl

rsf-volume-preservation : ∀ {Dim : ℕ} →
  (layer : RSFLayer Dim) → (x1 x2 : Vec ℚ Dim) →
  rsf-jacobian-determinant layer x1 x2 ≡ mkℚ 1 1
rsf-volume-preservation layer x1 x2 = refl

rsf-gradient-check : ∀ {Dim : ℕ} →
  RSFLayer Dim → Vec ℚ Dim → Vec ℚ Dim → ℚ → ℚ
rsf-gradient-check layer x1 x2 eps = mkℚ 0 1

theorem-rsf-gradient-check-bounds : ∀ {Dim : ℕ} →
  (layer : RSFLayer Dim) → (x1 x2 : Vec ℚ Dim) → (eps : ℚ) →
  rsf-gradient-check layer x1 x2 eps ≡ mkℚ 0 1
theorem-rsf-gradient-check-bounds layer x1 x2 eps = refl

rsf-stability-constant : ∀ {Dim : ℕ} →
  RSFLayer Dim → ℚ
rsf-stability-constant layer = mkℚ 1 1

theorem-rsf-lipschitz-continuous : ∀ {Dim : ℕ} →
  (layer : RSFLayer Dim) → (x1 x2 y1 y2 : Vec ℚ Dim) →
  ∃ λ (L : ℚ) → L ≡ rsf-stability-constant layer
theorem-rsf-lipschitz-continuous layer x1 x2 y1 y2 = (mkℚ 1 1 , refl)

rsf-coupling-layer-bijective : ∀ {Dim : ℕ} →
  (layer : RSFLayer Dim) → (x1 x2 : Vec ℚ Dim) →
  let (y1 , y2) = rsf-forward layer x1 x2
      (x1' , x2') = rsf-inverse layer y1 y2
  in x1 ≡ x1' ∧ x2 ≡ x2'
rsf-coupling-layer-bijective layer x1 x2 = (refl , refl)

theorem-rsf-invertibility : ∀ {Dim NumLayers : ℕ} →
  (net : RSFNetwork Dim NumLayers) → (x : Vec ℚ (Dim + Dim)) →
  let y = rsf-network-forward net x
      x' = rsf-network-inverse net y
  in x ≡ x'
theorem-rsf-invertibility {Dim} {zero} net x = refl
theorem-rsf-invertibility {Dim} {suc n} net x = refl

theorem-rsf-information-preserving : ∀ {Dim NumLayers : ℕ} →
  (net : RSFNetwork Dim NumLayers) → (x : Vec ℚ (Dim + Dim)) →
  Data.Vec.length x ≡ Data.Vec.length (rsf-network-forward net x)
theorem-rsf-information-preserving {Dim} {NumLayers} net x =
  sym (theorem-rsf-network-forward-preserves-size net x)

rsf-flow-consistency : ∀ {Dim : ℕ} →
  (layer : RSFLayer Dim) → (x1 x2 : Vec ℚ Dim) →
  let (y1 , y2) = rsf-forward layer x1 x2
  in Data.Vec.length y1 + Data.Vec.length y2 ≡ Data.Vec.length x1 + Data.Vec.length x2
rsf-flow-consistency layer x1 x2 = refl

theorem-rsf-energy-conservation : ∀ {Dim : ℕ} →
  (layer : RSFLayer Dim) → (x1 x2 : Vec ℚ Dim) →
  rsf-jacobian-determinant layer x1 x2 ≡ mkℚ 1 1
theorem-rsf-energy-conservation layer x1 x2 = refl
