---------------------------- MODULE TensorSpec ----------------------------

EXTENDS Naturals, Sequences, Integers, TLC

CONSTANTS MaxDim, MaxSize

VARIABLES tensorState, refcounts

TypeInvariant ==
    /\ tensorState \in [DOMAIN tensorState -> 
        [data: Seq(Nat), shape: Seq(Nat), refcount: Nat]]
    /\ \A tid \in DOMAIN tensorState:
        /\ tensorState[tid].refcount > 0
        /\ Len(tensorState[tid].data) = 
            CHOOSE n \in Nat: n = ShapeSize(tensorState[tid].shape)

ShapeSize(shape) ==
    IF Len(shape) = 0 THEN 1
    ELSE Head(shape) * ShapeSize(Tail(shape))

Init ==
    /\ tensorState = <<>>
    /\ refcounts = <<>>

TensorInit(tid, shape) ==
    /\ tid \notin DOMAIN tensorState
    /\ \A d \in DOMAIN shape: shape[d] > 0
    /\ LET size == ShapeSize(shape)
           data == [i \in 1..size |-> 0]
       IN tensorState' = tensorState @@ (tid :> 
           [data |-> data, shape |-> shape, refcount |-> 1])
    /\ UNCHANGED refcounts

TensorRetain(tid) ==
    /\ tid \in DOMAIN tensorState
    /\ tensorState' = [tensorState EXCEPT ![tid].refcount = @ + 1]
    /\ UNCHANGED refcounts

TensorRelease(tid) ==
    /\ tid \in DOMAIN tensorState
    /\ tensorState[tid].refcount > 0
    /\ IF tensorState[tid].refcount = 1
       THEN /\ tensorState' = [t \in (DOMAIN tensorState \ {tid}) |-> tensorState[t]]
            /\ UNCHANGED refcounts
       ELSE /\ tensorState' = [tensorState EXCEPT ![tid].refcount = @ - 1]
            /\ UNCHANGED refcounts

TensorFill(tid, value) ==
    /\ tid \in DOMAIN tensorState
    /\ value \in Nat
    /\ LET size == Len(tensorState[tid].data)
           newData == [i \in 1..size |-> value]
       IN tensorState' = [tensorState EXCEPT ![tid].data = newData]
    /\ UNCHANGED refcounts

TensorAddPointwise(tid1, tid2, tidResult) ==
    /\ tid1 \in DOMAIN tensorState
    /\ tid2 \in DOMAIN tensorState
    /\ tidResult \notin DOMAIN tensorState
    /\ tensorState[tid1].shape = tensorState[tid2].shape
    /\ LET size == Len(tensorState[tid1].data)
           newData == [i \in 1..size |-> 
                        tensorState[tid1].data[i] + tensorState[tid2].data[i]]
       IN tensorState' = tensorState @@ (tidResult :>
           [data |-> newData, 
            shape |-> tensorState[tid1].shape, 
            refcount |-> 1])
    /\ UNCHANGED refcounts

TensorSubPointwise(tid1, tid2, tidResult) ==
    /\ tid1 \in DOMAIN tensorState
    /\ tid2 \in DOMAIN tensorState
    /\ tidResult \notin DOMAIN tensorState
    /\ tensorState[tid1].shape = tensorState[tid2].shape
    /\ LET size == Len(tensorState[tid1].data)
           newData == [i \in 1..size |-> 
                        IF tensorState[tid1].data[i] >= tensorState[tid2].data[i]
                        THEN tensorState[tid1].data[i] - tensorState[tid2].data[i]
                        ELSE 0]
       IN tensorState' = tensorState @@ (tidResult :>
           [data |-> newData, 
            shape |-> tensorState[tid1].shape, 
            refcount |-> 1])
    /\ UNCHANGED refcounts

TensorMulPointwise(tid1, tid2, tidResult) ==
    /\ tid1 \in DOMAIN tensorState
    /\ tid2 \in DOMAIN tensorState
    /\ tidResult \notin DOMAIN tensorState
    /\ tensorState[tid1].shape = tensorState[tid2].shape
    /\ LET size == Len(tensorState[tid1].data)
           newData == [i \in 1..size |-> 
                        tensorState[tid1].data[i] * tensorState[tid2].data[i]]
       IN tensorState' = tensorState @@ (tidResult :>
           [data |-> newData, 
            shape |-> tensorState[tid1].shape, 
            refcount |-> 1])
    /\ UNCHANGED refcounts

TensorScalarAdd(tid, scalar, tidResult) ==
    /\ tid \in DOMAIN tensorState
    /\ tidResult \notin DOMAIN tensorState
    /\ scalar \in Nat
    /\ LET size == Len(tensorState[tid].data)
           newData == [i \in 1..size |-> 
                        tensorState[tid].data[i] + scalar]
       IN tensorState' = tensorState @@ (tidResult :>
           [data |-> newData, 
            shape |-> tensorState[tid].shape, 
            refcount |-> 1])
    /\ UNCHANGED refcounts

TensorScalarMul(tid, scalar, tidResult) ==
    /\ tid \in DOMAIN tensorState
    /\ tidResult \notin DOMAIN tensorState
    /\ scalar \in Nat
    /\ LET size == Len(tensorState[tid].data)
           newData == [i \in 1..size |-> 
                        tensorState[tid].data[i] * scalar]
       IN tensorState' = tensorState @@ (tidResult :>
           [data |-> newData, 
            shape |-> tensorState[tid].shape, 
            refcount |-> 1])
    /\ UNCHANGED refcounts

RefcountInvariant ==
    \A tid \in DOMAIN tensorState:
        tensorState[tid].refcount > 0

ShapeSizeInvariant ==
    \A tid \in DOMAIN tensorState:
        /\ Len(tensorState[tid].data) = ShapeSize(tensorState[tid].shape)
        /\ ShapeSize(tensorState[tid].shape) > 0

DataNonNegativeInvariant ==
    \A tid \in DOMAIN tensorState:
        \A i \in DOMAIN tensorState[tid].data:
            tensorState[tid].data[i] >= 0

Next ==
    \/ \E tid, shape: TensorInit(tid, shape)
    \/ \E tid: TensorRetain(tid)
    \/ \E tid: TensorRelease(tid)
    \/ \E tid, value: TensorFill(tid, value)
    \/ \E tid1, tid2, tidResult: TensorAddPointwise(tid1, tid2, tidResult)
    \/ \E tid1, tid2, tidResult: TensorSubPointwise(tid1, tid2, tidResult)
    \/ \E tid1, tid2, tidResult: TensorMulPointwise(tid1, tid2, tidResult)
    \/ \E tid, scalar, tidResult: TensorScalarAdd(tid, scalar, tidResult)
    \/ \E tid, scalar, tidResult: TensorScalarMul(tid, scalar, tidResult)

Spec == Init /\ [][Next]_<<tensorState, refcounts>>

THEOREM TypeCorrectness == Spec => []TypeInvariant
THEOREM RefcountCorrectness == Spec => []RefcountInvariant
THEOREM ShapeSizeCorrectness == Spec => []ShapeSizeInvariant
THEOREM DataNonNegative == Spec => []DataNonNegativeInvariant

AddCommutative ==
    \A tid1, tid2, tidResult1, tidResult2 \in DOMAIN tensorState:
        /\ tensorState[tid1].shape = tensorState[tid2].shape
        /\ TensorAddPointwise(tid1, tid2, tidResult1)
        /\ TensorAddPointwise(tid2, tid1, tidResult2)
        => tensorState'[tidResult1].data = tensorState'[tidResult2].data

MulCommutative ==
    \A tid1, tid2, tidResult1, tidResult2 \in DOMAIN tensorState:
        /\ tensorState[tid1].shape = tensorState[tid2].shape
        /\ TensorMulPointwise(tid1, tid2, tidResult1)
        /\ TensorMulPointwise(tid2, tid1, tidResult2)
        => tensorState'[tidResult1].data = tensorState'[tidResult2].data

THEOREM AddCommutativity == Spec => []AddCommutative
THEOREM MulCommutativity == Spec => []MulCommutative

=============================================================================
