import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Vector
import Mathlib.Tactic
import Tensor

namespace RSF

structure RSFLayerWeights (dim : Nat) where
  sWeight : Vector Nat (dim * dim)
  tWeight : Vector Nat (dim * dim)
  sBias : Vector Nat dim
  tBias : Vector Nat dim

def RSFLayer.init (dim : Nat) : RSFLayerWeights dim :=
  ⟨Vector.replicate (dim * dim) 0,
   Vector.replicate (dim * dim) 0,
   Vector.replicate dim 0,
   Vector.replicate dim 0⟩

structure RSFLayerGradients (dim : Nat) where
  sWeightGrad : Vector Nat (dim * dim)
  tWeightGrad : Vector Nat (dim * dim)
  sBiasGrad : Vector Nat dim
  tBiasGrad : Vector Nat dim

def RSFGradients.init (dim : Nat) : RSFLayerGradients dim :=
  ⟨Vector.replicate (dim * dim) 0,
   Vector.replicate (dim * dim) 0,
   Vector.replicate dim 0,
   Vector.replicate dim 0⟩

structure RSFLayerState (dim : Nat) where
  weights : RSFLayerWeights dim
  gradients : RSFLayerGradients dim

def RSFLayerState.init (dim : Nat) : RSFLayerState dim :=
  ⟨RSFLayer.init dim, RSFGradients.init dim⟩

def matrixVectorMul {rows cols : Nat} (mat : Vector Nat (rows * cols)) (vec : Vector Nat cols) : Vector Nat rows :=
  Vector.ofFn fun i => (Vector.ofFn fun j => mat.get ⟨i * cols + j, by omega⟩ * vec.get j).toList.foldl (· + ·) 0

def vectorAdd {n : Nat} (v1 v2 : Vector Nat n) : Vector Nat n :=
  v1.zipWith v2 (· + ·)

def vectorMul {n : Nat} (v1 v2 : Vector Nat n) : Vector Nat n :=
  v1.zipWith v2 (· * ·)

def clampNat (x min max : Nat) : Nat :=
  if x < min then min
  else if max < x then max
  else x

def vectorExp {n : Nat} (vec : Vector Nat n) : Vector Nat n :=
  vec.map (fun _ => 2)

def rsfForwardScatter {dim : Nat} (weights : RSFLayerWeights dim) (x1 x2 : Vector Nat dim) : Vector Nat dim × Vector Nat dim :=
  let sOut := matrixVectorMul weights.sWeight x2
  let sBiasAdded := vectorAdd sOut weights.sBias
  let sClamped := sBiasAdded.map (fun x => clampNat x 0 10)
  let sExp := vectorExp sClamped
  let y1 := vectorMul x1 sExp
  (y1, x2)

def rsfForwardTransform {dim : Nat} (weights : RSFLayerWeights dim) (x1 x2 : Vector Nat dim) : Vector Nat dim × Vector Nat dim :=
  let tOut := matrixVectorMul weights.tWeight x1
  let tBiasAdded := vectorAdd tOut weights.tBias
  let y2 := vectorAdd x2 tBiasAdded
  (x1, y2)

def rsfForward {dim : Nat} (weights : RSFLayerWeights dim) (x1 x2 : Vector Nat dim) : Vector Nat dim × Vector Nat dim :=
  let (y1Scatter, y2Scatter) := rsfForwardScatter weights x1 x2
  rsfForwardTransform weights y1Scatter y2Scatter

def rsfInverseTransform {dim : Nat} (weights : RSFLayerWeights dim) (y1 y2 : Vector Nat dim) : Vector Nat dim × Vector Nat dim :=
  let tOut := matrixVectorMul weights.tWeight y1
  let tBiasAdded := vectorAdd tOut weights.tBias
  let x2 := y2.zipWith tBiasAdded (fun a b => if a ≥ b then a - b else 0)
  (y1, x2)

def rsfInverseScatter {dim : Nat} (weights : RSFLayerWeights dim) (y1 y2 : Vector Nat dim) : Vector Nat dim × Vector Nat dim :=
  let sOut := matrixVectorMul weights.sWeight y2
  let sBiasAdded := vectorAdd sOut weights.sBias
  let sClamped := sBiasAdded.map (fun x => clampNat x 0 10)
  let sExp := vectorExp sClamped
  let x1 := y1.zipWith sExp (fun a b => a / (b + 1))
  (x1, y2)

def rsfInverse {dim : Nat} (weights : RSFLayerWeights dim) (y1 y2 : Vector Nat dim) : Vector Nat dim × Vector Nat dim :=
  let (x1Transform, x2Transform) := rsfInverseTransform weights y1 y2
  rsfInverseScatter weights x1Transform x2Transform

structure RSFNetwork (dim numLayers : Nat) where
  layers : Vector (RSFLayerState dim) numLayers

def RSFNetwork.init (dim numLayers : Nat) : RSFNetwork dim numLayers :=
  ⟨Vector.replicate numLayers (RSFLayerState.init dim)⟩

def rsfNetworkForward {dim : Nat} : {numLayers : Nat} → RSFNetwork dim numLayers → Vector Nat dim → Vector Nat dim → Vector Nat dim × Vector Nat dim
  | 0, net, x1, x2 => (x1, x2)
  | n+1, net, x1, x2 =>
    let layer := net.layers.get 0
    let restLayers := ⟨net.layers.tail⟩
    let (y1, y2) := rsfForward layer.weights x1 x2
    rsfNetworkForward restLayers y1 y2

def rsfNetworkInverse {dim : Nat} : {numLayers : Nat} → RSFNetwork dim numLayers → Vector Nat dim → Vector Nat dim → Vector Nat dim × Vector Nat dim
  | 0, net, y1, y2 => (y1, y2)
  | n+1, net, y1, y2 =>
    let lastLayer := net.layers.get ⟨n, by omega⟩
    let initLayers : RSFNetwork dim n := ⟨Vector.ofFn fun i => net.layers.get ⟨i, by omega⟩⟩
    let (x1Partial, x2Partial) := rsfNetworkInverse initLayers y1 y2
    rsfInverse lastLayer.weights x1Partial x2Partial

theorem rsfLayerForwardShape {dim : Nat} (weights : RSFLayerWeights dim) (x1 x2 : Vector Nat dim) :
  let (y1, y2) := rsfForward weights x1 x2
  y1.length = dim ∧ y2.length = dim := by
  simp [rsfForward, rsfForwardScatter, rsfForwardTransform]
  constructor <;> rfl

theorem rsfLayerInverseShape {dim : Nat} (weights : RSFLayerWeights dim) (y1 y2 : Vector Nat dim) :
  let (x1, x2) := rsfInverse weights y1 y2
  x1.length = dim ∧ x2.length = dim := by
  simp [rsfInverse, rsfInverseTransform, rsfInverseScatter]
  constructor <;> rfl

theorem rsfNetworkForwardShape {dim : Nat} : ∀ {numLayers : Nat} (net : RSFNetwork dim numLayers) (x1 x2 : Vector Nat dim),
  let (y1, y2) := rsfNetworkForward net x1 x2
  y1.length = dim ∧ y2.length = dim
  | 0, net, x1, x2 => by simp [rsfNetworkForward]
  | n+1, net, x1, x2 => by
    simp [rsfNetworkForward]
    have h := rsfLayerForwardShape (net.layers.get 0).weights x1 x2
    exact rsfNetworkForwardShape ⟨net.layers.tail⟩ _ _

theorem rsfNetworkInverseShape {dim : Nat} : ∀ {numLayers : Nat} (net : RSFNetwork dim numLayers) (y1 y2 : Vector Nat dim),
  let (x1, x2) := rsfNetworkInverse net y1 y2
  x1.length = dim ∧ x2.length = dim
  | 0, net, y1, y2 => by simp [rsfNetworkInverse]
  | n+1, net, y1, y2 => by
    simp [rsfNetworkInverse]
    have h := rsfNetworkInverseShape ⟨Vector.ofFn fun i => net.layers.get ⟨i, by omega⟩⟩ y1 y2
    exact rsfLayerInverseShape _ _ _

def zeroGradients {dim : Nat} (grads : RSFLayerGradients dim) : RSFLayerGradients dim :=
  RSFGradients.init dim

theorem zeroGradientsAllZero {dim : Nat} (grads : RSFLayerGradients dim) :
  let zeroed := zeroGradients grads
  (∀ i : Fin (dim * dim), zeroed.sWeightGrad.get i = 0 ∧ zeroed.tWeightGrad.get i = 0) := by
  intro i
  simp [zeroGradients, RSFGradients.init, Vector.replicate]

end RSF
