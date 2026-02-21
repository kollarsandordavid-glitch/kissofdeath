-------------------------- MODULE TensorComplete --------------------------

EXTENDS Naturals, Sequences, Integers, FiniteSets, TLC

CONSTANTS
  MAX_TENSOR_SIZE,
  MAX_REFCOUNT,
  MAX_VALUE

VARIABLES
  tensors,
  nextTensorId,
  allocatedTensors,
  tensorHistory

TensorDTypes == {"F32", "F64", "I32", "I64", "U32", "U64", "BOOL"}
TensorLayouts == {"ROW_MAJOR", "COLUMN_MAJOR", "STRIDED"}
TensorDevices == {"CPU", "GPU", "TPU"}
TensorOwnerships == {"OWNED", "BORROWED", "VIEW"}

TypeInvariant ==
  /\ nextTensorId \in Nat
  /\ allocatedTensors \subseteq Nat
  /\ tensors \in [Nat -> [
       shape: Seq(Nat),
       data: Seq(Int),
       dtype: TensorDTypes,
       layout: TensorLayouts,
       device: TensorDevices,
       ownership: TensorOwnerships,
       refcount: Nat
     ]]

ShapeSize(shape) ==
  IF Len(shape) = 0 THEN 1
  ELSE shape[1] * ShapeSize(SubSeq(shape, 2, Len(shape)))

TensorInvariant(tid) ==
  /\ tid \in allocatedTensors
  /\ Len(tensors[tid].data) = ShapeSize(tensors[tid].shape)
  /\ tensors[tid].refcount > 0
  /\ tensors[tid].refcount <= MAX_REFCOUNT
  /\ \A i \in 1..Len(tensors[tid].data) : 
       tensors[tid].data[i] >= -MAX_VALUE /\ tensors[tid].data[i] <= MAX_VALUE

MemorySafety ==
  \A tid \in allocatedTensors : TensorInvariant(tid)

Init ==
  /\ tensors = [i \in {} |-> []]
  /\ nextTensorId = 0
  /\ allocatedTensors = {}
  /\ tensorHistory = << >>

CreateTensor(shape_val, dtype_val, layout_val, device_val) ==
  /\ nextTensorId < MAX_TENSOR_SIZE
  /\ ShapeSize(shape_val) <= MAX_TENSOR_SIZE
  /\ tensors' = tensors @@ (nextTensorId :> [
       shape |-> shape_val,
       data |-> [i \in 1..ShapeSize(shape_val) |-> 0],
       dtype |-> dtype_val,
       layout |-> layout_val,
       device |-> device_val,
       ownership |-> "OWNED",
       refcount |-> 1
     ])
  /\ allocatedTensors' = allocatedTensors \cup {nextTensorId}
  /\ nextTensorId' = nextTensorId + 1
  /\ tensorHistory' = Append(tensorHistory, [op |-> "create", tid |-> nextTensorId, shape |-> shape_val])
  /\ TensorInvariant(nextTensorId)

Incref(tid) ==
  /\ tid \in allocatedTensors
  /\ tensors[tid].refcount < MAX_REFCOUNT
  /\ tensors' = [tensors EXCEPT ![tid].refcount = @ + 1]
  /\ UNCHANGED <<nextTensorId, allocatedTensors, tensorHistory>>
  /\ TensorInvariant(tid)

Decref(tid) ==
  /\ tid \in allocatedTensors
  /\ tensors[tid].refcount > 0
  /\ IF tensors[tid].refcount = 1
     THEN /\ allocatedTensors' = allocatedTensors \ {tid}
          /\ tensors' = [t \in DOMAIN tensors \ {tid} |-> tensors[t]]
          /\ tensorHistory' = Append(tensorHistory, [op |-> "free", tid |-> tid])
     ELSE /\ tensors' = [tensors EXCEPT ![tid].refcount = @ - 1]
          /\ UNCHANGED <<allocatedTensors, tensorHistory>>
  /\ UNCHANGED nextTensorId

TensorAdd(tid1, tid2) ==
  /\ tid1 \in allocatedTensors
  /\ tid2 \in allocatedTensors
  /\ tensors[tid1].shape = tensors[tid2].shape
  /\ nextTensorId < MAX_TENSOR_SIZE
  /\ LET newData == [i \in 1..Len(tensors[tid1].data) |-> 
                      tensors[tid1].data[i] + tensors[tid2].data[i]]
     IN /\ tensors' = tensors @@ (nextTensorId :> [
            shape |-> tensors[tid1].shape,
            data |-> newData,
            dtype |-> tensors[tid1].dtype,
            layout |-> tensors[tid1].layout,
            device |-> tensors[tid1].device,
            ownership |-> "OWNED",
            refcount |-> 1
          ])
  /\ allocatedTensors' = allocatedTensors \cup {nextTensorId}
  /\ nextTensorId' = nextTensorId + 1
  /\ tensorHistory' = Append(tensorHistory, [op |-> "add", tid1 |-> tid1, tid2 |-> tid2, result |-> nextTensorId])
  /\ TensorInvariant(nextTensorId)

TensorSub(tid1, tid2) ==
  /\ tid1 \in allocatedTensors
  /\ tid2 \in allocatedTensors
  /\ tensors[tid1].shape = tensors[tid2].shape
  /\ nextTensorId < MAX_TENSOR_SIZE
  /\ LET newData == [i \in 1..Len(tensors[tid1].data) |-> 
                      tensors[tid1].data[i] - tensors[tid2].data[i]]
     IN /\ tensors' = tensors @@ (nextTensorId :> [
            shape |-> tensors[tid1].shape,
            data |-> newData,
            dtype |-> tensors[tid1].dtype,
            layout |-> tensors[tid1].layout,
            device |-> tensors[tid1].device,
            ownership |-> "OWNED",
            refcount |-> 1
          ])
  /\ allocatedTensors' = allocatedTensors \cup {nextTensorId}
  /\ nextTensorId' = nextTensorId + 1
  /\ tensorHistory' = Append(tensorHistory, [op |-> "sub", tid1 |-> tid1, tid2 |-> tid2, result |-> nextTensorId])
  /\ TensorInvariant(nextTensorId)

TensorMul(tid1, tid2) ==
  /\ tid1 \in allocatedTensors
  /\ tid2 \in allocatedTensors
  /\ tensors[tid1].shape = tensors[tid2].shape
  /\ nextTensorId < MAX_TENSOR_SIZE
  /\ LET newData == [i \in 1..Len(tensors[tid1].data) |-> 
                      tensors[tid1].data[i] * tensors[tid2].data[i]]
     IN /\ tensors' = tensors @@ (nextTensorId :> [
            shape |-> tensors[tid1].shape,
            data |-> newData,
            dtype |-> tensors[tid1].dtype,
            layout |-> tensors[tid1].layout,
            device |-> tensors[tid1].device,
            ownership |-> "OWNED",
            refcount |-> 1
          ])
  /\ allocatedTensors' = allocatedTensors \cup {nextTensorId}
  /\ nextTensorId' = nextTensorId + 1
  /\ tensorHistory' = Append(tensorHistory, [op |-> "mul", tid1 |-> tid1, tid2 |-> tid2, result |-> nextTensorId])
  /\ TensorInvariant(nextTensorId)

TensorScalarMul(tid, scalar) ==
  /\ tid \in allocatedTensors
  /\ scalar \in Int
  /\ scalar >= -MAX_VALUE /\ scalar <= MAX_VALUE
  /\ nextTensorId < MAX_TENSOR_SIZE
  /\ LET newData == [i \in 1..Len(tensors[tid].data) |-> 
                      tensors[tid].data[i] * scalar]
     IN /\ tensors' = tensors @@ (nextTensorId :> [
            shape |-> tensors[tid].shape,
            data |-> newData,
            dtype |-> tensors[tid].dtype,
            layout |-> tensors[tid].layout,
            device |-> tensors[tid].device,
            ownership |-> "OWNED",
            refcount |-> 1
          ])
  /\ allocatedTensors' = allocatedTensors \cup {nextTensorId}
  /\ nextTensorId' = nextTensorId + 1
  /\ tensorHistory' = Append(tensorHistory, [op |-> "scalar_mul", tid |-> tid, scalar |-> scalar, result |-> nextTensorId])
  /\ TensorInvariant(nextTensorId)

TensorFill(tid, value) ==
  /\ tid \in allocatedTensors
  /\ value \in Int
  /\ value >= -MAX_VALUE /\ value <= MAX_VALUE
  /\ tensors[tid].ownership = "OWNED"
  /\ tensors' = [tensors EXCEPT ![tid].data = [i \in 1..Len(@) |-> value]]
  /\ UNCHANGED <<nextTensorId, allocatedTensors, tensorHistory>>
  /\ TensorInvariant(tid)

TensorCopy(tid) ==
  /\ tid \in allocatedTensors
  /\ nextTensorId < MAX_TENSOR_SIZE
  /\ tensors' = tensors @@ (nextTensorId :> [
       shape |-> tensors[tid].shape,
       data |-> tensors[tid].data,
       dtype |-> tensors[tid].dtype,
       layout |-> tensors[tid].layout,
       device |-> tensors[tid].device,
       ownership |-> "OWNED",
       refcount |-> 1
     ])
  /\ allocatedTensors' = allocatedTensors \cup {nextTensorId}
  /\ nextTensorId' = nextTensorId + 1
  /\ tensorHistory' = Append(tensorHistory, [op |-> "copy", tid |-> tid, result |-> nextTensorId])
  /\ TensorInvariant(nextTensorId)

LayoutTransform(tid, newLayout) ==
  /\ tid \in allocatedTensors
  /\ newLayout \in TensorLayouts
  /\ tensors' = [tensors EXCEPT ![tid].layout = newLayout]
  /\ UNCHANGED <<nextTensorId, allocatedTensors, tensorHistory>>
  /\ TensorInvariant(tid)
  /\ tensors'[tid].data = tensors[tid].data

DeviceTransfer(tid, newDevice) ==
  /\ tid \in allocatedTensors
  /\ newDevice \in TensorDevices
  /\ tensors' = [tensors EXCEPT ![tid].device = newDevice]
  /\ UNCHANGED <<nextTensorId, allocatedTensors, tensorHistory>>
  /\ TensorInvariant(tid)
  /\ tensors'[tid].data = tensors[tid].data

TensorSum(tid) ==
  /\ tid \in allocatedTensors
  /\ LET sum == SumSeq(tensors[tid].data, 1, Len(tensors[tid].data))
     IN /\ sum \in Int
        /\ UNCHANGED <<tensors, nextTensorId, allocatedTensors, tensorHistory>>

SumSeq(seq, start, end) ==
  IF start > end THEN 0
  ELSE seq[start] + SumSeq(seq, start + 1, end)

TensorMax(tid) ==
  /\ tid \in allocatedTensors
  /\ Len(tensors[tid].data) > 0
  /\ LET maxVal == MaxSeq(tensors[tid].data, 1, Len(tensors[tid].data))
     IN /\ maxVal \in Int
        /\ UNCHANGED <<tensors, nextTensorId, allocatedTensors, tensorHistory>>

MaxSeq(seq, start, end) ==
  IF start >= end THEN seq[start]
  ELSE LET midMax == MaxSeq(seq, start + 1, end)
       IN IF seq[start] > midMax THEN seq[start] ELSE midMax

TensorMin(tid) ==
  /\ tid \in allocatedTensors
  /\ Len(tensors[tid].data) > 0
  /\ LET minVal == MinSeq(tensors[tid].data, 1, Len(tensors[tid].data))
     IN /\ minVal \in Int
        /\ UNCHANGED <<tensors, nextTensorId, allocatedTensors, tensorHistory>>

MinSeq(seq, start, end) ==
  IF start >= end THEN seq[start]
  ELSE LET midMin == MinSeq(seq, start + 1, end)
       IN IF seq[start] < midMin THEN seq[start] ELSE midMin

TensorReLU(tid) ==
  /\ tid \in allocatedTensors
  /\ nextTensorId < MAX_TENSOR_SIZE
  /\ LET newData == [i \in 1..Len(tensors[tid].data) |-> 
                      IF tensors[tid].data[i] < 0 THEN 0 ELSE tensors[tid].data[i]]
     IN /\ tensors' = tensors @@ (nextTensorId :> [
            shape |-> tensors[tid].shape,
            data |-> newData,
            dtype |-> tensors[tid].dtype,
            layout |-> tensors[tid].layout,
            device |-> tensors[tid].device,
            ownership |-> "OWNED",
            refcount |-> 1
          ])
  /\ allocatedTensors' = allocatedTensors \cup {nextTensorId}
  /\ nextTensorId' = nextTensorId + 1
  /\ tensorHistory' = Append(tensorHistory, [op |-> "relu", tid |-> tid, result |-> nextTensorId])
  /\ TensorInvariant(nextTensorId)
  /\ \A i \in 1..Len(tensors'[nextTensorId].data) : tensors'[nextTensorId].data[i] >= 0

TensorClip(tid, minVal, maxVal) ==
  /\ tid \in allocatedTensors
  /\ minVal \in Int /\ maxVal \in Int
  /\ minVal <= maxVal
  /\ nextTensorId < MAX_TENSOR_SIZE
  /\ LET ClipValue(v) == IF v < minVal THEN minVal 
                         ELSE IF v > maxVal THEN maxVal 
                         ELSE v
         newData == [i \in 1..Len(tensors[tid].data) |-> ClipValue(tensors[tid].data[i])]
     IN /\ tensors' = tensors @@ (nextTensorId :> [
            shape |-> tensors[tid].shape,
            data |-> newData,
            dtype |-> tensors[tid].dtype,
            layout |-> tensors[tid].layout,
            device |-> tensors[tid].device,
            ownership |-> "OWNED",
            refcount |-> 1
          ])
  /\ allocatedTensors' = allocatedTensors \cup {nextTensorId}
  /\ nextTensorId' = nextTensorId + 1
  /\ tensorHistory' = Append(tensorHistory, [op |-> "clip", tid |-> tid, min |-> minVal, max |-> maxVal, result |-> nextTensorId])
  /\ TensorInvariant(nextTensorId)
  /\ \A i \in 1..Len(tensors'[nextTensorId].data) : 
       tensors'[nextTensorId].data[i] >= minVal /\ tensors'[nextTensorId].data[i] <= maxVal

NoMemoryLeaks ==
  \A tid \in allocatedTensors : tensors[tid].refcount > 0

NoUseAfterFree ==
  \A tid \in DOMAIN tensors : tid \in allocatedTensors => TensorInvariant(tid)

RefcountConsistency ==
  \A tid \in allocatedTensors :
    /\ tensors[tid].refcount >= 1
    /\ tensors[tid].ownership = "OWNED" => tensors[tid].refcount >= 1

DataIntegrity ==
  \A tid \in allocatedTensors :
    Len(tensors[tid].data) = ShapeSize(tensors[tid].shape)

BoundsInvariant ==
  \A tid \in allocatedTensors :
    \A i \in 1..Len(tensors[tid].data) :
      tensors[tid].data[i] >= -MAX_VALUE /\ tensors[tid].data[i] <= MAX_VALUE

AddCommutative ==
  \A tid1, tid2 \in allocatedTensors :
    tensors[tid1].shape = tensors[tid2].shape =>
      LET result1Data == [i \in 1..Len(tensors[tid1].data) |-> 
                           tensors[tid1].data[i] + tensors[tid2].data[i]]
          result2Data == [i \in 1..Len(tensors[tid2].data) |-> 
                           tensors[tid2].data[i] + tensors[tid1].data[i]]
      IN result1Data = result2Data

MulCommutative ==
  \A tid1, tid2 \in allocatedTensors :
    tensors[tid1].shape = tensors[tid2].shape =>
      LET result1Data == [i \in 1..Len(tensors[tid1].data) |-> 
                           tensors[tid1].data[i] * tensors[tid2].data[i]]
          result2Data == [i \in 1..Len(tensors[tid2].data) |-> 
                           tensors[tid2].data[i] * tensors[tid1].data[i]]
      IN result1Data = result2Data

LayoutTransformPreservesData ==
  \A tid \in allocatedTensors :
    \A newLayout \in TensorLayouts :
      LET t' == [tensors[tid] EXCEPT !.layout = newLayout]
      IN t'.data = tensors[tid].data

DeviceTransferPreservesData ==
  \A tid \in allocatedTensors :
    \A newDevice \in TensorDevices :
      LET t' == [tensors[tid] EXCEPT !.device = newDevice]
      IN t'.data = tensors[tid].data

Next ==
  \/ \E shape \in Seq(Nat), dtype \in TensorDTypes, layout \in TensorLayouts, device \in TensorDevices :
       CreateTensor(shape, dtype, layout, device)
  \/ \E tid \in allocatedTensors : Incref(tid)
  \/ \E tid \in allocatedTensors : Decref(tid)
  \/ \E tid1, tid2 \in allocatedTensors : TensorAdd(tid1, tid2)
  \/ \E tid1, tid2 \in allocatedTensors : TensorSub(tid1, tid2)
  \/ \E tid1, tid2 \in allocatedTensors : TensorMul(tid1, tid2)
  \/ \E tid \in allocatedTensors, scalar \in Int : TensorScalarMul(tid, scalar)
  \/ \E tid \in allocatedTensors, value \in Int : TensorFill(tid, value)
  \/ \E tid \in allocatedTensors : TensorCopy(tid)
  \/ \E tid \in allocatedTensors, newLayout \in TensorLayouts : LayoutTransform(tid, newLayout)
  \/ \E tid \in allocatedTensors, newDevice \in TensorDevices : DeviceTransfer(tid, newDevice)
  \/ \E tid \in allocatedTensors : TensorReLU(tid)
  \/ \E tid \in allocatedTensors, minVal, maxVal \in Int : TensorClip(tid, minVal, maxVal)

Spec == Init /\ [][Next]_<<tensors, nextTensorId, allocatedTensors, tensorHistory>>

THEOREM TypeCorrectness == Spec => []TypeInvariant
THEOREM MemoryCorrectness == Spec => []MemorySafety
THEOREM NoLeaks == Spec => []NoMemoryLeaks
THEOREM NoUAF == Spec => []NoUseAfterFree
THEOREM RefcountCorrectness == Spec => []RefcountConsistency
THEOREM DataCorrectness == Spec => []DataIntegrity
THEOREM BoundsSafety == Spec => []BoundsInvariant

=============================================================================
