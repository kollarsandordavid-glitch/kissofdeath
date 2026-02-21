import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Vector
import Mathlib.Tactic

namespace TensorModel

inductive DType where
  | F32 : DType
  | F64 : DType
  | I32 : DType
  | I64 : DType
  | U32 : DType
  | U64 : DType
  | BOOL : DType
deriving DecidableEq

inductive Layout where
  | ROW_MAJOR : Layout
  | COLUMN_MAJOR : Layout
  | STRIDED : Layout
deriving DecidableEq

inductive Device where
  | CPU : Device
  | GPU : Device
  | TPU : Device
deriving DecidableEq

inductive Ownership where
  | OWNED : Ownership
  | BORROWED : Ownership
  | VIEW : Ownership
deriving DecidableEq

def shapeSize : List Nat → Nat
  | [] => 1
  | d :: ds => d * shapeSize ds

structure Tensor (shape : List Nat) (dtype : DType) where
  dataVec : Vector Nat (shapeSize shape)
  layout : Layout
  device : Device
  ownership : Ownership

theorem shapeSizePositive (shape : List Nat) : 1 ≤ shapeSize shape := by
  induction shape with
  | nil => simp [shapeSize]
  | cons d ds ih =>
    simp [shapeSize]
    cases d with
    | zero => omega
    | succ n => omega

theorem shapeConsistency {shape : List Nat} {dtype : DType} 
  (t : Tensor shape dtype) : t.dataVec.length = shapeSize shape := by
  simp [Vector.length]

theorem memoryBounds {shape : List Nat} {dtype : DType}
  (t : Tensor shape dtype) (i : Fin (shapeSize shape)) : 
  i.val < shapeSize shape := by
  exact i.isLt

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
  (f : Nat → Nat) (t : Tensor shape dtype) : Tensor shape dtype :=
  { t with dataVec := t.dataVec.map f }

theorem tensorMapPreservesShape {shape : List Nat} {dtype : DType}
  (f : Nat → Nat) (t : Tensor shape dtype) :
  (tensorMap f t).dataVec.length = shapeSize shape := by
  simp [tensorMap, Vector.length]

def tensorZipWith {shape : List Nat} {dtype : DType}
  (f : Nat → Nat → Nat) (t1 t2 : Tensor shape dtype) : Tensor shape dtype :=
  { t1 with dataVec := t1.dataVec.zipWith t2.dataVec f }

def tensorFold {shape : List Nat} {dtype : DType}
  (f : Nat → Nat → Nat) (z : Nat) (t : Tensor shape dtype) : Nat :=
  t.dataVec.toList.foldl f z

def tensorReplicate (shape : List Nat) (dtype : DType) (v : Nat) : Tensor shape dtype :=
  { dataVec := Vector.replicate (shapeSize shape) v
  , layout := Layout.ROW_MAJOR
  , device := Device.CPU
  , ownership := Ownership.OWNED }

theorem tensorReplicateAllEqual (shape : List Nat) (dtype : DType) (v : Nat)
  (i j : Fin (shapeSize shape)) :
  (tensorReplicate shape dtype v).dataVec.get i = 
  (tensorReplicate shape dtype v).dataVec.get j := by
  simp [tensorReplicate, Vector.replicate]

def tensorZero (shape : List Nat) (dtype : DType) : Tensor shape dtype :=
  tensorReplicate shape dtype 0

theorem tensorZeroIsZero (shape : List Nat) (dtype : DType) 
  (i : Fin (shapeSize shape)) :
  (tensorZero shape dtype).dataVec.get i = 0 := by
  simp [tensorZero, tensorReplicate, Vector.replicate]

def tensorAdd {shape : List Nat} {dtype : DType}
  (t1 t2 : Tensor shape dtype) : Tensor shape dtype :=
  tensorZipWith (· + ·) t1 t2

theorem tensorAddComm {shape : List Nat} {dtype : DType}
  (t1 t2 : Tensor shape dtype) :
  (tensorAdd t1 t2).dataVec = (tensorAdd t2 t1).dataVec := by
  simp [tensorAdd, tensorZipWith]
  ext i
  simp [Vector.zipWith, Nat.add_comm]

theorem tensorAddAssoc {shape : List Nat} {dtype : DType}
  (t1 t2 t3 : Tensor shape dtype) :
  (tensorAdd (tensorAdd t1 t2) t3).dataVec = 
  (tensorAdd t1 (tensorAdd t2 t3)).dataVec := by
  simp [tensorAdd, tensorZipWith]
  ext i
  simp [Vector.zipWith, Nat.add_assoc]

def tensorMul {shape : List Nat} {dtype : DType}
  (t1 t2 : Tensor shape dtype) : Tensor shape dtype :=
  tensorZipWith (· * ·) t1 t2

theorem tensorMulComm {shape : List Nat} {dtype : DType}
  (t1 t2 : Tensor shape dtype) :
  (tensorMul t1 t2).dataVec = (tensorMul t2 t1).dataVec := by
  simp [tensorMul, tensorZipWith]
  ext i
  simp [Vector.zipWith, Nat.mul_comm]

theorem tensorMulAssoc {shape : List Nat} {dtype : DType}
  (t1 t2 t3 : Tensor shape dtype) :
  (tensorMul (tensorMul t1 t2) t3).dataVec = 
  (tensorMul t1 (tensorMul t2 t3)).dataVec := by
  simp [tensorMul, tensorZipWith]
  ext i
  simp [Vector.zipWith, Nat.mul_assoc]

def tensorScalarMul {shape : List Nat} {dtype : DType}
  (scalar : Nat) (t : Tensor shape dtype) : Tensor shape dtype :=
  tensorMap (fun x => scalar * x) t

theorem tensorScalarMulDistributive {shape : List Nat} {dtype : DType}
  (s : Nat) (t1 t2 : Tensor shape dtype) :
  (tensorScalarMul s (tensorAdd t1 t2)).dataVec =
  (tensorAdd (tensorScalarMul s t1) (tensorScalarMul s t2)).dataVec := by
  simp [tensorScalarMul, tensorAdd, tensorMap, tensorZipWith]
  ext i
  simp [Vector.map, Vector.zipWith, Nat.mul_add]

def tensorSum {shape : List Nat} {dtype : DType}
  (t : Tensor shape dtype) : Nat :=
  tensorFold (· + ·) 0 t

theorem tensorSumZero (shape : List Nat) (dtype : DType) :
  tensorSum (tensorZero shape dtype) = 0 := by
  simp [tensorSum, tensorFold, tensorZero, tensorReplicate]
  induction shapeSize shape with
  | zero => rfl
  | succ n ih => simp [Vector.replicate, List.foldl]

theorem tensorSumAdd {shape : List Nat} {dtype : DType}
  (t1 t2 : Tensor shape dtype) :
  tensorSum (tensorAdd t1 t2) = tensorSum t1 + tensorSum t2 := by
  simp [tensorSum, tensorAdd, tensorZipWith, tensorFold]
  induction shapeSize shape with
  | zero => rfl
  | succ n ih =>
    simp [Vector.zipWith]
    omega

def aliasingRule {shape1 shape2 : List Nat} {dtype : DType}
  (t1 : Tensor shape1 dtype) (t2 : Tensor shape2 dtype) :
  Prop :=
  t1.ownership = Ownership.OWNED →
  t2.ownership = Ownership.OWNED →
  shapeSize shape1 = shapeSize shape2 →
  t1.dataVec ≠ t2.dataVec

def deviceAffinityPreserving {shape : List Nat} {dtype : DType}
  (t : Tensor shape dtype)
  (op : Tensor shape dtype → Tensor shape dtype)
  (devPreserves : ∀ t' : Tensor shape dtype, (op t').device = t'.device) :
  (op t).device = t.device :=
  devPreserves t

end TensorModel
