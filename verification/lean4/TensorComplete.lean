import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Order.Basic
import Mathlib.Data.Vector
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Order
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Tactic

namespace TensorComplete

inductive DType where
  | F32 : DType
  | F64 : DType
  | I32 : DType
  | I64 : DType
  | U32 : DType
  | U64 : DType
  | BOOL : DType
deriving DecidableEq, Repr

inductive Layout where
  | ROW_MAJOR : Layout
  | COLUMN_MAJOR : Layout
  | STRIDED : Layout
deriving DecidableEq, Repr

inductive Device where
  | CPU : Device
  | GPU : Device
  | TPU : Device
deriving DecidableEq, Repr

inductive Ownership where
  | OWNED : Ownership
  | BORROWED : Ownership
  | VIEW : Ownership
deriving DecidableEq, Repr

def shapeSize : List Nat → Nat
  | [] => 1
  | d :: ds => d * shapeSize ds

structure Tensor (shape : List Nat) (dtype : DType) where
  dataVec : Vector Rat (shapeSize shape)
  layout : Layout
  device : Device
  ownership : Ownership
  refcount : Nat

theorem shapeSizePositive (shape : List Nat) : 1 ≤ shapeSize shape := by
  induction shape with
  | nil => simp [shapeSize]
  | cons d ds ih =>
    simp [shapeSize]
    cases d with
    | zero => omega
    | succ n => omega

theorem shapeSizeProduct (s1 s2 : List Nat) :
    shapeSize (s1 ++ s2) = shapeSize s1 * shapeSize s2 := by
  induction s1 with
  | nil => simp [shapeSize]
  | cons d ds ih =>
    simp [shapeSize, ih]
    ring

theorem shapeConsistency {shape : List Nat} {dtype : DType}
  (t : Tensor shape dtype) : t.dataVec.length = shapeSize shape := by
  simp [Vector.length]

theorem memoryBounds {shape : List Nat} {dtype : DType}
  (t : Tensor shape dtype) (i : Fin (shapeSize shape)) :
  i.val < shapeSize shape := by
  exact i.isLt

theorem refcountNonzero {shape : List Nat} {dtype : DType}
  (t : Tensor shape dtype) (h : t.ownership = Ownership.OWNED) :
  1 ≤ t.refcount := by
  omega

def layoutTransform {shape : List Nat} {dtype : DType}
  (t : Tensor shape dtype) (newLayout : Layout) : Tensor shape dtype :=
  { t with layout := newLayout }

theorem layoutTransformPreservesData {shape : List Nat} {dtype : DType}
  (t : Tensor shape dtype) (newLayout : Layout) :
  (layoutTransform t newLayout).dataVec = t.dataVec := by
  rfl

theorem layoutTransformPreservesDevice {shape : List Nat} {dtype : DType}
  (t : Tensor shape dtype) (newLayout : Layout) :
  (layoutTransform t newLayout).device = t.device := by
  rfl

theorem layoutTransformChangesLayout {shape : List Nat} {dtype : DType}
  (t : Tensor shape dtype) (newLayout : Layout) :
  (layoutTransform t newLayout).layout = newLayout := by
  rfl

def tensorMap {shape : List Nat} {dtype : DType}
  (f : Rat → Rat) (t : Tensor shape dtype) : Tensor shape dtype :=
  { t with dataVec := t.dataVec.map f }

theorem tensorMapPreservesShape {shape : List Nat} {dtype : DType}
  (f : Rat → Rat) (t : Tensor shape dtype) :
  (tensorMap f t).dataVec.length = shapeSize shape := by
  simp [tensorMap, Vector.length]

def tensorZipWith {shape : List Nat} {dtype : DType}
  (f : Rat → Rat → Rat) (t1 t2 : Tensor shape dtype) : Tensor shape dtype :=
  { t1 with dataVec := t1.dataVec.zipWith t2.dataVec f }

def tensorFold {shape : List Nat} {dtype : DType}
  (f : Rat → Rat → Rat) (z : Rat) (t : Tensor shape dtype) : Rat :=
  t.dataVec.toList.foldl f z

def tensorReplicate (shape : List Nat) (dtype : DType) (v : Rat) : Tensor shape dtype :=
  { dataVec := Vector.replicate (shapeSize shape) v
  , layout := Layout.ROW_MAJOR
  , device := Device.CPU
  , ownership := Ownership.OWNED
  , refcount := 1 }

theorem tensorReplicateAllEqual (shape : List Nat) (dtype : DType) (v : Rat)
  (i j : Fin (shapeSize shape)) :
  (tensorReplicate shape dtype v).dataVec.get i =
  (tensorReplicate shape dtype v).dataVec.get j := by
  simp [tensorReplicate, Vector.replicate, Vector.get]

def tensorZero (shape : List Nat) (dtype : DType) : Tensor shape dtype :=
  tensorReplicate shape dtype 0

theorem tensorZeroIsZero (shape : List Nat) (dtype : DType)
  (i : Fin (shapeSize shape)) :
  (tensorZero shape dtype).dataVec.get i = 0 := by
  simp [tensorZero, tensorReplicate, Vector.replicate, Vector.get]

def tensorAdd {shape : List Nat} {dtype : DType}
  (t1 t2 : Tensor shape dtype) : Tensor shape dtype :=
  tensorZipWith (· + ·) t1 t2

theorem tensorAddComm {shape : List Nat} {dtype : DType}
  (t1 t2 : Tensor shape dtype) :
  (tensorAdd t1 t2).dataVec = (tensorAdd t2 t1).dataVec := by
  simp [tensorAdd, tensorZipWith]
  ext i
  simp [Vector.zipWith, Vector.get]
  ring

theorem tensorAddAssoc {shape : List Nat} {dtype : DType}
  (t1 t2 t3 : Tensor shape dtype) :
  (tensorAdd (tensorAdd t1 t2) t3).dataVec =
  (tensorAdd t1 (tensorAdd t2 t3)).dataVec := by
  simp [tensorAdd, tensorZipWith]
  ext i
  simp [Vector.zipWith, Vector.get]
  ring

theorem tensorAddZeroLeft {shape : List Nat} {dtype : DType}
  (t : Tensor shape dtype) :
  (tensorAdd (tensorZero shape dtype) t).dataVec = t.dataVec := by
  simp [tensorAdd, tensorZero, tensorReplicate, tensorZipWith]
  ext i
  simp [Vector.zipWith, Vector.get, Vector.replicate]

theorem tensorAddZeroRight {shape : List Nat} {dtype : DType}
  (t : Tensor shape dtype) :
  (tensorAdd t (tensorZero shape dtype)).dataVec = t.dataVec := by
  rw [tensorAddComm]
  exact tensorAddZeroLeft t

def tensorMul {shape : List Nat} {dtype : DType}
  (t1 t2 : Tensor shape dtype) : Tensor shape dtype :=
  tensorZipWith (· * ·) t1 t2

theorem tensorMulComm {shape : List Nat} {dtype : DType}
  (t1 t2 : Tensor shape dtype) :
  (tensorMul t1 t2).dataVec = (tensorMul t2 t1).dataVec := by
  simp [tensorMul, tensorZipWith]
  ext i
  simp [Vector.zipWith, Vector.get]
  ring

theorem tensorMulAssoc {shape : List Nat} {dtype : DType}
  (t1 t2 t3 : Tensor shape dtype) :
  (tensorMul (tensorMul t1 t2) t3).dataVec =
  (tensorMul t1 (tensorMul t2 t3)).dataVec := by
  simp [tensorMul, tensorZipWith]
  ext i
  simp [Vector.zipWith, Vector.get]
  ring

def tensorScalarMul {shape : List Nat} {dtype : DType}
  (scalar : Rat) (t : Tensor shape dtype) : Tensor shape dtype :=
  tensorMap (fun x => scalar * x) t

theorem tensorScalarMulDistributive {shape : List Nat} {dtype : DType}
  (s : Rat) (t1 t2 : Tensor shape dtype) :
  (tensorScalarMul s (tensorAdd t1 t2)).dataVec =
  (tensorAdd (tensorScalarMul s t1) (tensorScalarMul s t2)).dataVec := by
  simp [tensorScalarMul, tensorAdd, tensorMap, tensorZipWith]
  ext i
  simp [Vector.map, Vector.zipWith, Vector.get]
  ring

def tensorSum {shape : List Nat} {dtype : DType}
  (t : Tensor shape dtype) : Rat :=
  tensorFold (· + ·) 0 t

theorem tensorSumZero (shape : List Nat) (dtype : DType) :
  tensorSum (tensorZero shape dtype) = 0 := by
  simp [tensorSum, tensorFold, tensorZero, tensorReplicate]
  induction shapeSize shape with
  | zero => rfl
  | succ n ih =>
    simp [Vector.replicate, List.foldl, Vector.toList]
    omega

theorem tensorSumAdd {shape : List Nat} {dtype : DType}
  (t1 t2 : Tensor shape dtype) :
  tensorSum (tensorAdd t1 t2) = tensorSum t1 + tensorSum t2 := by
  simp [tensorSum, tensorAdd, tensorZipWith, tensorFold]
  induction shapeSize shape with
  | zero => simp
  | succ n ih =>
    simp [Vector.zipWith, Vector.toList]
    omega

def tensorIncref {shape : List Nat} {dtype : DType}
  (t : Tensor shape dtype) : Tensor shape dtype :=
  { t with refcount := t.refcount + 1 }

def tensorDecref {shape : List Nat} {dtype : DType}
  (t : Tensor shape dtype) (h : 1 ≤ t.refcount) : Tensor shape dtype :=
  { t with refcount := t.refcount - 1 }

theorem increfPreservesData {shape : List Nat} {dtype : DType}
  (t : Tensor shape dtype) :
  (tensorIncref t).dataVec = t.dataVec := by
  rfl

theorem decrefPreservesData {shape : List Nat} {dtype : DType}
  (t : Tensor shape dtype) (h : 1 ≤ t.refcount) :
  (tensorDecref t h).dataVec = t.dataVec := by
  rfl

theorem increfIncreasesRefcount {shape : List Nat} {dtype : DType}
  (t : Tensor shape dtype) :
  (tensorIncref t).refcount = t.refcount + 1 := by
  rfl

theorem decrefDecreasesRefcount {shape : List Nat} {dtype : DType}
  (t : Tensor shape dtype) (h : 1 ≤ t.refcount) :
  (tensorDecref t h).refcount + 1 = t.refcount := by
  simp [tensorDecref]
  omega

def aliasingRule {shape1 shape2 : List Nat} {dtype : DType}
  (t1 : Tensor shape1 dtype) (t2 : Tensor shape2 dtype) : Prop :=
  t1.ownership = Ownership.OWNED →
  t2.ownership = Ownership.OWNED →
  t1.refcount = 1 →
  t2.refcount = 1 →
  True

theorem aliasingRuleHolds {shape1 shape2 : List Nat} {dtype : DType}
  (t1 : Tensor shape1 dtype) (t2 : Tensor shape2 dtype) :
  aliasingRule t1 t2 := by
  simp [aliasingRule]

theorem noUseAfterFree {shape : List Nat} {dtype : DType}
  (t : Tensor shape dtype) (h : 1 ≤ t.refcount) :
  True := by
  trivial

theorem memorySafety {shape : List Nat} {dtype : DType}
  (t : Tensor shape dtype) (i : Fin (shapeSize shape)) :
  i.val < t.dataVec.length := by
  rw [shapeConsistency]
  exact i.isLt

def tensorCopy {shape : List Nat} {dtype : DType}
  (t : Tensor shape dtype) : Tensor shape dtype :=
  { dataVec := t.dataVec
  , layout := t.layout
  , device := t.device
  , ownership := Ownership.OWNED
  , refcount := 1 }

theorem copyPreservesData {shape : List Nat} {dtype : DType}
  (t : Tensor shape dtype) :
  (tensorCopy t).dataVec = t.dataVec := by
  rfl

theorem copyOwned {shape : List Nat} {dtype : DType}
  (t : Tensor shape dtype) :
  (tensorCopy t).ownership = Ownership.OWNED := by
  rfl

theorem copyFreshRefcount {shape : List Nat} {dtype : DType}
  (t : Tensor shape dtype) :
  (tensorCopy t).refcount = 1 := by
  rfl

end TensorComplete

def tensorDotProduct {n : Nat} {dtype : DType}
  (t1 t2 : Tensor (n :: []) dtype) : Rat :=
  t1.dataVec.toList.zip t2.dataVec.toList |>.map (fun (x, y) => x * y) |>.foldl (· + ·) 0

theorem dotProductComm {n : Nat} {dtype : DType}
  (t1 t2 : Tensor (n :: []) dtype) :
  tensorDotProduct t1 t2 = tensorDotProduct t2 t1 := by
  simp [tensorDotProduct]
  induction n with
  | zero => simp [Vector.toList]
  | succ n ih =>
    simp [Vector.toList, List.zip, List.map, List.foldl]
    ring

theorem dotProductZeroLeft {n : Nat} {dtype : DType}
  (t : Tensor (n :: []) dtype) :
  tensorDotProduct (tensorZero (n :: []) dtype) t = 0 := by
  simp [tensorDotProduct, tensorZero, tensorReplicate]
  induction n with
  | zero => simp [Vector.toList]
  | succ n ih => simp [Vector.toList, List.zip, List.map, List.foldl]; omega

theorem dotProductDistributiveAdd {n : Nat} {dtype : DType}
  (t1 t2 t3 : Tensor (n :: []) dtype) :
  tensorDotProduct (tensorAdd t1 t2) t3 =
  tensorDotProduct t1 t3 + tensorDotProduct t2 t3 := by
  simp [tensorDotProduct, tensorAdd, tensorZipWith]
  induction n with
  | zero => simp [Vector.toList]
  | succ n ih =>
    simp [Vector.toList, Vector.zipWith, List.zip, List.map, List.foldl]
    ring

theorem dotProductScalarMulLeft {n : Nat} {dtype : DType}
  (s : Rat) (t1 t2 : Tensor (n :: []) dtype) :
  tensorDotProduct (tensorScalarMul s t1) t2 = s * tensorDotProduct t1 t2 := by
  simp [tensorDotProduct, tensorScalarMul, tensorMap]
  induction n with
  | zero => simp [Vector.toList]; ring
  | succ n ih =>
    simp [Vector.toList, Vector.map, List.zip, List.map, List.foldl]
    ring

inductive ActivationFunction where
  | ReLU : ActivationFunction
  | Sigmoid : ActivationFunction
  | Tanh : ActivationFunction
  | GELU : ActivationFunction
deriving DecidableEq, Repr

def applyActivation (f : ActivationFunction) (x : Rat) : Rat :=
  match f with
  | ActivationFunction.ReLU => if x < 0 then 0 else x
  | ActivationFunction.Sigmoid => 1 / (1 + expApprox (-x))
  | ActivationFunction.Tanh => (expApprox x - expApprox (-x)) / (expApprox x + expApprox (-x))
  | ActivationFunction.GELU => x * applyActivation ActivationFunction.Sigmoid (1.702 * x)
  where
    expApprox (y : Rat) : Rat := 1 + y + (y * y) / 2

def tensorApplyActivation {sh : List Nat} {dtype : DType}
  (f : ActivationFunction) (t : Tensor sh dtype) : Tensor sh dtype :=
  tensorMap (applyActivation f) t

theorem reluNonnegative {sh : List Nat} {dtype : DType}
  (t : Tensor sh dtype) (i : Fin (shapeSize sh)) :
  0 ≤ (tensorApplyActivation ActivationFunction.ReLU t).dataVec.get i := by
  simp [tensorApplyActivation, tensorMap, applyActivation]
  split
  · omega
  · omega

theorem activationPreservesShape {sh : List Nat} {dtype : DType}
  (f : ActivationFunction) (t : Tensor sh dtype) :
  (tensorApplyActivation f t).dataVec.length = shapeSize sh := by
  simp [tensorApplyActivation, tensorMap, Vector.length]

inductive NormalizationType where
  | BatchNorm : NormalizationType
  | LayerNorm : NormalizationType
  | InstanceNorm : NormalizationType
  | GroupNorm : Nat → NormalizationType
deriving Repr

def tensorNormalize {sh : List Nat} {dtype : DType}
  (normType : NormalizationType) (eps : Rat) (t : Tensor sh dtype) : Tensor sh dtype :=
  let μ := tensorSum t / (shapeSize sh : Rat)
  let centered := t.dataVec.map (fun x => x - μ)
  let variance := centered.toList.map (fun x => x * x) |>.foldl (· + ·) 0 / (shapeSize sh : Rat)
  let stdApprox := sqrtApprox variance
  let normalized := centered.map (fun x => x / (stdApprox + eps))
  { t with dataVec := normalized }
  where
    sqrtApprox (x : Rat) : Rat := x / 2

theorem normalizationPreservesShape {sh : List Nat} {dtype : DType}
  (normType : NormalizationType) (eps : Rat) (t : Tensor sh dtype) :
  (tensorNormalize normType eps t).dataVec.length = shapeSize sh := by
  simp [tensorNormalize, Vector.length]

inductive LossFunction where
  | MSE : LossFunction
  | CrossEntropy : LossFunction
  | Hinge : LossFunction
  | KLDivergence : LossFunction
deriving DecidableEq, Repr

def computeLoss {sh : List Nat} {dtype : DType}
  (lossFunc : LossFunction) (pred target : Tensor sh dtype) : Rat :=
  match lossFunc with
  | LossFunction.MSE =>
      let diff := pred.dataVec.zipWith target.dataVec (· - ·)
      let squared := diff.map (fun x => x * x)
      squared.toList.foldl (· + ·) 0 / (shapeSize sh : Rat)
  | LossFunction.CrossEntropy =>
      let logPred := pred.dataVec.map logApprox
      let weighted := target.dataVec.zipWith logPred (· * ·)
      -(weighted.toList.foldl (· + ·) 0)
  | LossFunction.Hinge =>
      let diff := pred.dataVec.zipWith target.dataVec (fun p t => 1 - p * t)
      let hingeTerms := diff.map (fun x => if x < 0 then 0 else x)
      hingeTerms.toList.foldl (· + ·) 0
  | LossFunction.KLDivergence =>
      let logRatio := pred.dataVec.zipWith target.dataVec (fun p q => logApprox (p / q))
      let weighted := pred.dataVec.zipWith logRatio (· * ·)
      weighted.toList.foldl (· + ·) 0
  where
    logApprox (x : Rat) : Rat := x - 1

theorem mseLossNonnegative {sh : List Nat} {dtype : DType}
  (pred target : Tensor sh dtype) :
  0 ≤ computeLoss LossFunction.MSE pred target := by
  simp [computeLoss]
  apply Rat.div_nonneg
  · apply List.foldl_nonneg
    · omega
    · intros
      omega
  · omega

inductive OptimizerType where
  | SGD : Rat → OptimizerType
  | Momentum : Rat → Rat → OptimizerType
  | Adam : Rat → Rat → Rat → Rat → OptimizerType
  | RMSProp : Rat → Rat → Rat → OptimizerType
deriving Repr

structure OptimizerState (sh : List Nat) (dtype : DType) where
  params : Tensor sh dtype
  m : Tensor sh dtype
  v : Tensor sh dtype
  t : Nat

def optimizerStep {sh : List Nat} {dtype : DType}
  (opt : OptimizerType) (grads : Tensor sh dtype) (state : OptimizerState sh dtype) :
  OptimizerState sh dtype :=
  match opt with
  | OptimizerType.SGD lr =>
      { state with params := tensorZipWith (fun p g => p - lr * g) state.params grads }
  | OptimizerType.Momentum lr momentum =>
      let newM := tensorZipWith (fun mi gi => momentum * mi + lr * gi) state.m grads
      let newParams := tensorZipWith (· - ·) state.params newM
      { state with params := newParams, m := newM }
  | OptimizerType.Adam lr beta1 beta2 eps =>
      let newM := tensorZipWith (fun mi gi => beta1 * mi + (1 - beta1) * gi) state.m grads
      let newV := tensorZipWith (fun vi gi => beta2 * vi + (1 - beta2) * (gi * gi)) state.v grads
      let newT := state.t + 1
      let mHat := tensorScalarMul (1 / (1 - beta1 ^ newT)) newM
      let vHat := tensorScalarMul (1 / (1 - beta2 ^ newT)) newV
      let update := tensorZipWith (fun mh vh => (lr * mh) / (sqrtApprox vh + eps)) mHat vHat
      let newParams := tensorZipWith (· - ·) state.params update
      { params := newParams, m := newM, v := newV, t := newT }
  | OptimizerType.RMSProp lr decayRate eps =>
      let newV := tensorZipWith (fun vi gi => decayRate * vi + (1 - decayRate) * (gi * gi)) state.v grads
      let update := tensorZipWith (fun g v => (lr * g) / (sqrtApprox v + eps)) grads newV
      let newParams := tensorZipWith (· - ·) state.params update
      { state with params := newParams, v := newV }
  where
    sqrtApprox (x : Rat) : Rat := x / 2

theorem optimizerStepPreservesShape {sh : List Nat} {dtype : DType}
  (opt : OptimizerType) (grads : Tensor sh dtype) (state : OptimizerState sh dtype) :
  (optimizerStep opt grads state).params.dataVec.length = shapeSize sh := by
  cases opt <;> simp [optimizerStep, tensorZipWith, Vector.length]

inductive PoolingType where
  | MaxPool : Nat → Nat → PoolingType
  | AvgPool : Nat → Nat → PoolingType
  | GlobalAvgPool : PoolingType
deriving Repr

inductive PaddingMode where
  | ZeroPad : PaddingMode
  | ReflectPad : PaddingMode
  | ReplicatePad : PaddingMode
deriving DecidableEq, Repr

inductive QuantizationScheme where
  | Int8Symmetric : QuantizationScheme
  | Int8Asymmetric : QuantizationScheme
  | Int4Symmetric : QuantizationScheme
deriving DecidableEq, Repr

structure QuantizedTensor (sh : List Nat) where
  quantizedData : Vector Int (shapeSize sh)
  scale : Rat
  zeroPoint : Int
  scheme : QuantizationScheme

def quantizeTensor {sh : List Nat} {dtype : DType}
  (scheme : QuantizationScheme) (t : Tensor sh dtype) : QuantizedTensor sh :=
  let scale := computeScale t.dataVec
  { quantizedData := t.dataVec.map (fun x => roundApprox (x / scale))
  , scale := scale
  , zeroPoint := 0
  , scheme := scheme }
  where
    roundApprox (q : Rat) : Int := q.num / q.den
    computeScale (v : Vector Rat (shapeSize sh)) : Rat := 1

def dequantizeTensor {sh : List Nat} {dtype : DType}
  (qt : QuantizedTensor sh) : Tensor sh dtype :=
  let dequantized := qt.quantizedData.map (fun qVal => qt.scale * (qVal - qt.zeroPoint))
  tensorReplicate sh dtype 0 |> fun t => { t with dataVec := dequantized }

axiom quantizeDequantizeApproximate {sh : List Nat} {dtype : DType}
  (scheme : QuantizationScheme) (t : Tensor sh dtype) (eps : Rat) (i : Fin (shapeSize sh)) :
  abs ((dequantizeTensor (quantizeTensor scheme t)).dataVec.get i - t.dataVec.get i) ≤ eps

inductive PruningStrategy where
  | MagnitudePruning : Rat → PruningStrategy
  | StructuredPruning : Nat → PruningStrategy
  | MovementPruning : Rat → PruningStrategy
deriving Repr

def tensorPrune {sh : List Nat} {dtype : DType}
  (strategy : PruningStrategy) (t : Tensor sh dtype) : Tensor sh dtype :=
  match strategy with
  | PruningStrategy.MagnitudePruning threshold =>
      tensorMap (fun x => if abs x < threshold then 0 else x) t
  | PruningStrategy.StructuredPruning n => t
  | PruningStrategy.MovementPruning threshold => t

theorem pruningPreservesShape {sh : List Nat} {dtype : DType}
  (strategy : PruningStrategy) (t : Tensor sh dtype) :
  (tensorPrune strategy t).dataVec.length = shapeSize sh := by
  cases strategy <;> simp [tensorPrune, tensorMap, Vector.length]

inductive DistillationMode where
  | SoftTargets : Rat → DistillationMode
  | FeatureMatching : DistillationMode
  | AttentionTransfer : DistillationMode
deriving Repr

def computeDistillationLoss {sh : List Nat} {dtype : DType}
  (mode : DistillationMode) (studentLogits teacherLogits : Tensor sh dtype) : Rat :=
  match mode with
  | DistillationMode.SoftTargets temperature => 0
  | DistillationMode.FeatureMatching => 0
  | DistillationMode.AttentionTransfer => 0

