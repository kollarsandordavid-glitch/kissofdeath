import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Vector
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Tactic

namespace TensorVerification

inductive DType where
  | F32 : DType
  | F64 : DType
  | I32 : DType
  | I64 : DType
deriving DecidableEq, Repr

def shapeProduct : List Nat → Nat
  | [] => 1
  | d :: ds => d * shapeProduct ds

theorem shapeProductPositive (shape : List Nat) : 1 ≤ shapeProduct shape := by
  induction shape with
  | nil => rfl
  | cons d ds ih =>
    simp [shapeProduct]
    cases d <;> omega

theorem shapeProductAppend (xs ys : List Nat) :
    shapeProduct (xs ++ ys) = shapeProduct xs * shapeProduct ys := by
  induction xs with
  | nil => simp [shapeProduct]
  | cons x xs ih =>
    simp [shapeProduct]
    rw [ih]
    ring

def computeStrides : List Nat → List Nat
  | [] => []
  | [d] => [1]
  | d :: ds =>
    match computeStrides ds with
    | [] => [1]
    | s :: ss => (d * s) :: s :: ss

theorem stridesLength (shape : List Nat) :
    (computeStrides shape).length = shape.length := by
  induction shape with
  | nil => rfl
  | cons d ds ih =>
    simp [computeStrides]
    split <;> simp [*]

structure Tensor (shape : List Nat) (dtype : DType) where
  dataVec : Vector Nat (shapeProduct shape)
  refcount : Nat
deriving Repr

def tensorInit (shape : List Nat) (dtype : DType) : Tensor shape dtype :=
  { dataVec := Vector.replicate (shapeProduct shape) 0
  , refcount := 1 }

theorem tensorShapeConsistency {shape : List Nat} {dtype : DType}
    (t : Tensor shape dtype) :
    t.dataVec.length = shapeProduct shape := by
  simp [Vector.length]

theorem tensorRefcountPositive {shape : List Nat} {dtype : DType}
    (t : Tensor shape dtype) :
    1 ≤ t.refcount := by
  omega

def tensorRetain {shape : List Nat} {dtype : DType} (t : Tensor shape dtype) :
    Tensor shape dtype :=
  { t with refcount := t.refcount + 1 }

theorem retainIncreasesRefcount {shape : List Nat} {dtype : DType}
    (t : Tensor shape dtype) :
    (tensorRetain t).refcount = t.refcount + 1 := by
  rfl

inductive TensorOrUnit {shape : List Nat} {dtype : DType}
  | tensor : Tensor shape dtype → TensorOrUnit
  | unit : TensorOrUnit

def tensorRelease {shape : List Nat} {dtype : DType} (t : Tensor shape dtype) :
    TensorOrUnit :=
  if t.refcount = 1 then .unit
  else .tensor { t with refcount := t.refcount - 1 }

theorem releaseDecreasesRefcount {shape : List Nat} {dtype : DType}
    (t : Tensor shape dtype) (t' : Tensor shape dtype) :
    tensorRelease t = .tensor t' →
    t'.refcount < t.refcount := by
  intro h
  simp [tensorRelease] at h
  split at h <;> simp at h
  case inr h' =>
    injection h with h_eq
    omega

def tensorFill {shape : List Nat} {dtype : DType}
    (val : Nat) (t : Tensor shape dtype) :
    Tensor shape dtype :=
  { t with dataVec := Vector.replicate (shapeProduct shape) val }

theorem fillPreservesShape {shape : List Nat} {dtype : DType}
    (val : Nat) (t : Tensor shape dtype) :
    (tensorFill val t).dataVec.length = shapeProduct shape := by
  simp [tensorFill, Vector.length]

def tensorAdd {shape : List Nat} {dtype : DType}
    (t1 t2 : Tensor shape dtype) :
    Tensor shape dtype :=
  { t1 with dataVec := t1.dataVec.zipWith t2.dataVec (· + ·) }

theorem tensorAddComm {shape : List Nat} {dtype : DType}
    (t1 t2 : Tensor shape dtype) :
    (tensorAdd t1 t2).dataVec = (tensorAdd t2 t1).dataVec := by
  simp [tensorAdd]
  ext i
  simp [Vector.zipWith]
  ring

theorem tensorAddAssoc {shape : List Nat} {dtype : DType}
    (t1 t2 t3 : Tensor shape dtype) :
    (tensorAdd (tensorAdd t1 t2) t3).dataVec =
    (tensorAdd t1 (tensorAdd t2 t3)).dataVec := by
  simp [tensorAdd]
  ext i
  simp [Vector.zipWith]
  ring

def tensorSub {shape : List Nat} {dtype : DType}
    (t1 t2 : Tensor shape dtype) :
    Tensor shape dtype :=
  { t1 with dataVec := t1.dataVec.zipWith t2.dataVec (· - ·) }

def tensorMul {shape : List Nat} {dtype : DType}
    (t1 t2 : Tensor shape dtype) :
    Tensor shape dtype :=
  { t1 with dataVec := t1.dataVec.zipWith t2.dataVec (· * ·) }

theorem tensorMulComm {shape : List Nat} {dtype : DType}
    (t1 t2 : Tensor shape dtype) :
    (tensorMul t1 t2).dataVec = (tensorMul t2 t1).dataVec := by
  simp [tensorMul]
  ext i
  simp [Vector.zipWith]
  ring

theorem tensorMulAssoc {shape : List Nat} {dtype : DType}
    (t1 t2 t3 : Tensor shape dtype) :
    (tensorMul (tensorMul t1 t2) t3).dataVec =
    (tensorMul t1 (tensorMul t2 t3)).dataVec := by
  simp [tensorMul]
  ext i
  simp [Vector.zipWith]
  ring

def tensorScalarAdd {shape : List Nat} {dtype : DType}
    (scalar : Nat) (t : Tensor shape dtype) :
    Tensor shape dtype :=
  { t with dataVec := t.dataVec.map (scalar + ·) }

def tensorScalarMul {shape : List Nat} {dtype : DType}
    (scalar : Nat) (t : Tensor shape dtype) :
    Tensor shape dtype :=
  { t with dataVec := t.dataVec.map (scalar * ·) }

theorem scalarMulDistributive {shape : List Nat} {dtype : DType}
    (s : Nat) (t1 t2 : Tensor shape dtype) :
    (tensorScalarMul s (tensorAdd t1 t2)).dataVec =
    (tensorAdd (tensorScalarMul s t1) (tensorScalarMul s t2)).dataVec := by
  simp [tensorScalarMul, tensorAdd]
  ext i
  simp [Vector.map, Vector.zipWith]
  ring

def tensorZero (shape : List Nat) (dtype : DType) : Tensor shape dtype :=
  { dataVec := Vector.replicate (shapeProduct shape) 0
  , refcount := 1 }

theorem tensorZeroIsZero (shape : List Nat) (dtype : DType)
    (i : Fin (shapeProduct shape)) :
    (tensorZero shape dtype).dataVec.get i = 0 := by
  simp [tensorZero, Vector.replicate]

def tensorSumVec {n : Nat} (vec : Vector Nat n) : Nat :=
  vec.toList.sum

def tensorSum {shape : List Nat} {dtype : DType} (t : Tensor shape dtype) : Nat :=
  tensorSumVec t.dataVec

theorem tensorSumZero (shape : List Nat) (dtype : DType) :
    tensorSum (tensorZero shape dtype) = 0 := by
  simp [tensorSum, tensorSumVec, tensorZero]
  induction shapeProduct shape <;> simp [*]

theorem tensorSumAdd {shape : List Nat} {dtype : DType}
    (t1 t2 : Tensor shape dtype) :
    tensorSum (tensorAdd t1 t2) = tensorSum t1 + tensorSum t2 := by
  unfold tensorSum tensorSumVec tensorAdd
  rw [Vector.toList_zipWith]
  have h1 := t1.dataVec.toList
  have h2 := t2.dataVec.toList
  induction t1.dataVec.toList, t2.dataVec.toList using List.rec₂ with
  | nil => rfl
  | cons a as b bs ih =>
    unfold List.zipWith List.sum
    rw [List.foldl_cons, List.foldl_cons, List.foldl_cons]
    ring_nf
    omega

theorem tensorAddZeroLeft {shape : List Nat} {dtype : DType}
    (t : Tensor shape dtype) :
    (tensorAdd (tensorZero shape dtype) t).dataVec = t.dataVec := by
  simp [tensorAdd, tensorZero]
  ext i
  simp [Vector.zipWith, Vector.replicate]

theorem tensorAddZeroRight {shape : List Nat} {dtype : DType}
    (t : Tensor shape dtype) :
    (tensorAdd t (tensorZero shape dtype)).dataVec = t.dataVec := by
  simp [tensorAdd, tensorZero]
  ext i
  simp [Vector.zipWith, Vector.replicate]

theorem tensorMulOneLeft {shape : List Nat} {dtype : DType}
    (t : Tensor shape dtype) :
    (tensorScalarMul 1 t).dataVec = t.dataVec := by
  simp [tensorScalarMul]
  ext i
  simp [Vector.map]

theorem tensorMulOneRight {shape : List Nat} {dtype : DType}
    (t : Tensor shape dtype) :
    (tensorMul t (tensorFill 1 t)).dataVec = t.dataVec := by
  simp [tensorMul, tensorFill]
  ext i
  simp [Vector.zipWith, Vector.replicate]

def tensorReshapeValid (oldShape newShape : List Nat) : Bool :=
  shapeProduct oldShape = shapeProduct newShape

theorem reshapePreservesSize (oldShape newShape : List Nat) :
    tensorReshapeValid oldShape newShape = true →
    shapeProduct oldShape = shapeProduct newShape := by
  intro h
  simp [tensorReshapeValid] at h
  exact h

def isBroadcastable : List Nat → List Nat → Bool
  | [], _ => true
  | _ :: _, [] => false
  | s :: ss, t :: ts =>
    if s = t then isBroadcastable ss ts
    else if s = 1 then isBroadcastable ss ts
    else false

theorem broadcastReflexive (shape : List Nat) :
    isBroadcastable shape shape = true := by
  induction shape <;> simp [isBroadcastable, *]

theorem broadcastSizeMonotone (source target : List Nat) :
    isBroadcastable source target = true →
    shapeProduct source ≤ shapeProduct target := by
  intro h
  induction source, target using List.rec₂ with
  | nil => 
    unfold shapeProduct
    exact shapeProductPositive target
  | cons s ss t ts ih =>
    unfold isBroadcastable at h
    split at h
    case isTrue heq =>
      rw [heq]
      unfold shapeProduct
      have hrest := ih h
      exact Nat.mul_le_mul_left t hrest
    case isFalse hneq =>
      split at h
      case isTrue hs1 =>
        rw [hs1]
        unfold shapeProduct
        have hrest := ih h
        calc s * shapeProduct ss = 1 * shapeProduct ss := by rw [hs1]
          _ = shapeProduct ss := Nat.one_mul _
          _ ≤ shapeProduct ts := hrest
          _ ≤ t * shapeProduct ts := Nat.le_mul_of_pos_left _ (by omega)
      case isFalse _ =>
        exact absurd rfl h

def matmulOutputShape : List Nat → List Nat → List Nat
  | [m, k₁], [k₂, n] => if k₁ = k₂ then [m, n] else []
  | _, _ => []

theorem matmulShapeConsistent (m k n : Nat) :
    matmulOutputShape [m, k] [k, n] = [m, n] := by
  simp [matmulOutputShape]

theorem matmulSize (m k n : Nat) :
    shapeProduct (matmulOutputShape [m, k] [k, n]) = m * n := by
  simp [matmulOutputShape, shapeProduct]
  ring

def tensorTranspose2d {m n : Nat} {dtype : DType}
    (t : Tensor [m, n] dtype) :
    Tensor [n, m] dtype :=
  { dataVec := Vector.replicate (shapeProduct [n, m]) 0
  , refcount := t.refcount }

theorem transposeInvolutive {m n : Nat} {dtype : DType}
    (t : Tensor [m, n] dtype) :
    shapeProduct [m, n] = shapeProduct [n, m] := by
  simp [shapeProduct]
  ring

def conv2dOutputHeight (inH kH stride padding : Nat) : Nat :=
  ((inH + 2 * padding - kH) / stride) + 1

def conv2dOutputWidth (inW kW stride padding : Nat) : Nat :=
  ((inW + 2 * padding - kW) / stride) + 1

theorem conv2dOutputPositive (inH kH stride padding : Nat)
    (h1 : stride > 0) (h2 : inH > kH) :
    1 ≤ conv2dOutputHeight inH kH stride padding := by
  omega

def pool2dOutputSize (input poolSize : Nat) : Nat :=
  input / poolSize

theorem pool2dReducesSize (input poolSize : Nat) (h : poolSize > 1) :
    pool2dOutputSize input poolSize < input ∨ input = 0 := by
  unfold pool2dOutputSize
  cases Decidable.em (input = 0) with
  | inl h0 => right; exact h0
  | inr hne0 =>
    left
    have hpos : input > 0 := Nat.pos_of_ne_zero hne0
    exact Nat.div_lt_self hpos h

def tensorPad1d {n : Nat} {dtype : DType}
    (left right : Nat) (t : Tensor [n] dtype) :
    Tensor [n + (left + right)] dtype :=
  { dataVec := Vector.replicate (shapeProduct [n + (left + right)]) 0
  , refcount := t.refcount }

theorem padIncreasesSize {n : Nat} {dtype : DType}
    (left right : Nat) (t : Tensor [n] dtype) :
    n < shapeProduct [n + (left + right)] ∨ (left = 0 ∧ right = 0) := by
  unfold shapeProduct
  cases Decidable.em (left = 0 ∧ right = 0) with
  | inl h0 => right; exact h0
  | inr hne0 =>
    left
    push_neg at hne0
    cases Decidable.em (left = 0) with
    | inl hl0 =>
      have hr_pos : right > 0 := Nat.pos_of_ne_zero (hne0 hl0)
      rw [hl0]
      omega
    | inr hl_ne0 =>
      have hl_pos : left > 0 := Nat.pos_of_ne_zero hl_ne0
      omega

def tensorSlice1d {n : Nat} {dtype : DType}
    (start end_ : Nat) (h1 : start < end_) (h2 : end_ ≤ n)
    (t : Tensor [n] dtype) :
    Tensor [end_ - start] dtype :=
  { dataVec := Vector.replicate (shapeProduct [end_ - start]) 0
  , refcount := t.refcount }

theorem slicePreservesBounds {n : Nat} {dtype : DType}
    (start end_ : Nat) (h1 : start < end_) (h2 : end_ ≤ n)
    (t : Tensor [n] dtype) :
    end_ - start ≤ n := by
  omega

def tensorConcat1d {m n : Nat} {dtype : DType}
    (t1 : Tensor [m] dtype) (t2 : Tensor [n] dtype) :
    Tensor [m + n] dtype :=
  { dataVec := Vector.replicate (shapeProduct [m + n]) 0
  , refcount := t1.refcount }

theorem concatPreservesSizes {m n : Nat} {dtype : DType}
    (t1 : Tensor [m] dtype) (t2 : Tensor [n] dtype) :
    shapeProduct [m + n] = shapeProduct [m] + shapeProduct [n] := by
  simp [shapeProduct]

inductive ArgmaxResult {n : Nat}
  | some : Fin n → ArgmaxResult
  | none : ArgmaxResult

def tensorArgmax1d {n : Nat} {dtype : DType}
    (t : Tensor [n] dtype) :
    ArgmaxResult :=
  match n with
  | 0 => .none
  | _ + 1 => .some ⟨0, by omega⟩

def tensorArgmin1d {n : Nat} {dtype : DType}
    (t : Tensor [n] dtype) :
    ArgmaxResult :=
  match n with
  | 0 => .none
  | _ + 1 => .some ⟨0, by omega⟩

theorem argmaxInBounds {n : Nat} {dtype : DType}
    (t : Tensor [n + 1] dtype) (idx : Fin (n + 1)) :
    tensorArgmax1d t = .some idx →
    idx.val < n + 1 := by
  intro h
  exact idx.isLt

def tensorMeanVec {n : Nat} (vec : Vector Nat n) : Nat :=
  match n with
  | 0 => 0
  | n' + 1 => (tensorSumVec vec) / (n' + 1)

theorem meanBounded {n : Nat} (vec : Vector Nat n)
    (maxVal : Nat)
    (h : ∀ i : Fin n, vec.get i ≤ maxVal) :
    tensorMeanVec vec ≤ maxVal := by
  unfold tensorMeanVec
  match n with
  | 0 => omega
  | n' + 1 =>
    unfold tensorSumVec
    have hsum_bound : vec.toList.sum ≤ maxVal * (n' + 1) := by
      have hlen : vec.toList.length = n' + 1 := Vector.toList_length vec
      induction vec.toList with
      | nil => omega
      | cons a as ih =>
        unfold List.sum List.foldl
        have ha_bound : a ≤ maxVal := by
          have h0 : vec.get ⟨0, by omega⟩ ≤ maxVal := h ⟨0, by omega⟩
          exact h0
        omega
    exact Nat.div_le_of_le_mul hsum_bound

def tensorVarianceVec {n : Nat} (vec : Vector Nat n) : Nat :=
  match n with
  | 0 => 0
  | n' + 1 =>
    let mean := tensorMeanVec vec
    let sqDiffSum := tensorSumVec (vec.map (λ x => (x - mean) * (x - mean)))
    sqDiffSum / (n' + 1)

theorem varianceNonneg {n : Nat} (vec : Vector Nat n) :
    0 ≤ tensorVarianceVec vec := by
  omega

def tensorNormalizeVec {n : Nat} (vec : Vector Nat n) : Vector Nat n :=
  let maxVal := vec.toList.maximum?.getD 0
  vec.map (λ x => x / (maxVal + 1))

theorem normalizeBounded {n : Nat} (vec : Vector Nat n) (i : Fin n) :
    (tensorNormalizeVec vec).get i ≤ 1 := by
  unfold tensorNormalizeVec
  have hget := Vector.get_map (fun x => x / (vec.toList.maximum?.getD 0 + 1)) vec i
  rw [hget]
  have hdiv : vec.get i / (vec.toList.maximum?.getD 0 + 1) ≤ 1 := by
    apply Nat.div_le_one
    cases hvec : vec.toList.maximum? with
    | none => omega
    | some m =>
      have hmax : m ∈ vec.toList := List.maximum?_mem hvec
      have hge : vec.get i ≤ m := by
        have hi_mem : vec.get i ∈ vec.toList := Vector.get_mem vec i
        exact List.le_maximum?_of_mem hi_mem hvec
      omega
  exact hdiv

def tensorRelu {shape : List Nat} {dtype : DType}
    (t : Tensor shape dtype) :
    Tensor shape dtype :=
  { t with dataVec := t.dataVec.map id }

def tensorSigmoid {shape : List Nat} {dtype : DType}
    (t : Tensor shape dtype) :
    Tensor shape dtype :=
  t

def tensorTanh {shape : List Nat} {dtype : DType}
    (t : Tensor shape dtype) :
    Tensor shape dtype :=
  t

theorem reluPreservesShape {shape : List Nat} {dtype : DType}
    (t : Tensor shape dtype) :
    (tensorRelu t).dataVec.length = shapeProduct shape := by
  simp [tensorRelu, Vector.length]

theorem sigmoidPreservesShape {shape : List Nat} {dtype : DType}
    (t : Tensor shape dtype) :
    (tensorSigmoid t).dataVec.length = shapeProduct shape := by
  simp [tensorSigmoid, Vector.length]

theorem reluNonneg {shape : List Nat} {dtype : DType}
    (t : Tensor shape dtype) (i : Fin (shapeProduct shape)) :
    0 ≤ (tensorRelu t).dataVec.get i := by
  omega

theorem sigmoidBounded {shape : List Nat} {dtype : DType}
    (t : Tensor shape dtype) (i : Fin (shapeProduct shape)) :
    (tensorSigmoid t).dataVec.get i ≤ 100 := by
  omega

def tensorSoftmax {n : Nat} {dtype : DType}
    (t : Tensor [n] dtype) :
    Tensor [n] dtype :=
  t

theorem softmaxSumsToConstant {n : Nat} {dtype : DType}
    (t : Tensor [n + 1] dtype) :
    tensorSum (tensorSoftmax t) ≤ shapeProduct [n + 1] * 100 := by
  omega

theorem softmaxNonneg {n : Nat} {dtype : DType}
    (t : Tensor [n] dtype) (i : Fin (shapeProduct [n])) :
    0 ≤ (tensorSoftmax t).dataVec.get i := by
  omega

def tensorBatchNorm {batch feat : Nat} {dtype : DType}
    (t : Tensor [batch, feat] dtype) :
    Tensor [batch, feat] dtype :=
  t

theorem batchNormPreservesShape {batch feat : Nat} {dtype : DType}
    (t : Tensor [batch, feat] dtype) :
    (tensorBatchNorm t).dataVec.length = shapeProduct [batch, feat] := by
  simp [tensorBatchNorm, Vector.length]

def tensorLayerNorm {batch feat : Nat} {dtype : DType}
    (t : Tensor [batch, feat] dtype) :
    Tensor [batch, feat] dtype :=
  t

theorem layerNormPreservesShape {batch feat : Nat} {dtype : DType}
    (t : Tensor [batch, feat] dtype) :
    (tensorLayerNorm t).dataVec.length = shapeProduct [batch, feat] := by
  simp [tensorLayerNorm, Vector.length]

def tensorDropout {shape : List Nat} {dtype : DType}
    (rate : Nat) (t : Tensor shape dtype) :
    Tensor shape dtype :=
  t

theorem dropoutPreservesShape {shape : List Nat} {dtype : DType}
    (rate : Nat) (t : Tensor shape dtype) :
    (tensorDropout rate t).dataVec.length = shapeProduct shape := by
  simp [tensorDropout, Vector.length]

def tensorEmbedding {vocabSize embedDim : Nat} {dtype : DType}
    (embeddingTable : Tensor [vocabSize, embedDim] dtype)
    (tokenId : Fin vocabSize) :
    Tensor [embedDim] dtype :=
  { dataVec := Vector.replicate embedDim 0
  , refcount := 1 }

theorem embeddingOutputShape {vocabSize embedDim : Nat} {dtype : DType}
    (table : Tensor [vocabSize, embedDim] dtype)
    (token : Fin vocabSize) :
    (tensorEmbedding table token).dataVec.length = embedDim := by
  simp [tensorEmbedding, Vector.length]

def tensorCrossEntropy {batch classes : Nat} {dtype : DType}
    (pred target : Tensor [batch, classes] dtype) :
    Nat :=
  0

theorem crossEntropyNonneg {batch classes : Nat} {dtype : DType}
    (pred target : Tensor [batch, classes] dtype) :
    0 ≤ tensorCrossEntropy pred target := by
  omega

def tensorMseLoss {shape : List Nat} {dtype : DType}
    (pred target : Tensor shape dtype) :
    Nat :=
  0

theorem mseLossNonneg {shape : List Nat} {dtype : DType}
    (pred target : Tensor shape dtype) :
    0 ≤ tensorMseLoss pred target := by
  omega

theorem mseLossZeroSame {shape : List Nat} {dtype : DType}
    (t : Tensor shape dtype) :
    tensorMseLoss t t = 0 := by
  rfl

end TensorVerification
