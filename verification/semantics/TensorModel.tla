---- MODULE TensorModel ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS 
    DTypes,
    Layouts,
    Devices,
    Ownerships

DType == {"F32", "F64", "I32", "I64", "U32", "U64", "BOOL"}
Layout == {"ROW_MAJOR", "COLUMN_MAJOR", "STRIDED"}
Device == {"CPU", "GPU", "TPU"}
Ownership == {"OWNED", "BORROWED", "VIEW"}

ShapeSize(shape) ==
    IF shape = <<>> 
    THEN 1
    ELSE Head(shape) * ShapeSize(Tail(shape))

Tensor(shape, dtype) == 
    [dataVec: Seq(Nat),
     layout: Layout,
     device: Device,
     ownership: Ownership]

TensorValid(t, shape) ==
    /\ Len(t.dataVec) = ShapeSize(shape)
    /\ t.layout \in Layout
    /\ t.device \in Device
    /\ t.ownership \in Ownership

ShapeConsistency(t, shape) ==
    TensorValid(t, shape) => Len(t.dataVec) = ShapeSize(shape)

MemoryBounds(t, shape, i) ==
    /\ TensorValid(t, shape)
    /\ i \in 1..Len(t.dataVec)

LayoutTransform(t, newLayout) ==
    [t EXCEPT !.layout = newLayout]

LayoutTransformPreservesData(t, newLayout) ==
    LayoutTransform(t, newLayout).dataVec = t.dataVec

LayoutTransformPreservesDevice(t, newLayout) ==
    LayoutTransform(t, newLayout).device = t.device

LayoutTransformChangesLayout(t, newLayout) ==
    LayoutTransform(t, newLayout).layout = newLayout

TensorMap(f(_), t) ==
    [t EXCEPT !.dataVec = [i \in DOMAIN t.dataVec |-> f(t.dataVec[i])]]

TensorMapPreservesShape(f(_), t, shape) ==
    Len(TensorMap(f, t).dataVec) = ShapeSize(shape)

TensorZipWith(f(_, _), t1, t2) ==
    LET
        newDataVec == [i \in DOMAIN t1.dataVec |-> f(t1.dataVec[i], t2.dataVec[i])]
    IN
        [t1 EXCEPT !.dataVec = newDataVec]

TensorFold(f(_, _), z, t) ==
    LET
        Fold[seq \in Seq(Nat)] ==
            IF seq = <<>>
            THEN z
            ELSE f(Head(seq), Fold[Tail(seq)])
    IN
        Fold[t.dataVec]

TensorReplicate(shape, v) ==
    LET
        size == ShapeSize(shape)
        dataVec == [i \in 1..size |-> v]
    IN
        [dataVec |-> dataVec,
         layout |-> "ROW_MAJOR",
         device |-> "CPU",
         ownership |-> "OWNED"]

TensorReplicateAllEqual(shape, v) ==
    LET t == TensorReplicate(shape, v)
    IN \A i, j \in DOMAIN t.dataVec : t.dataVec[i] = t.dataVec[j]

TensorZero(shape) ==
    TensorReplicate(shape, 0)

TensorZeroIsZero(shape) ==
    LET t == TensorZero(shape)
    IN \A i \in DOMAIN t.dataVec : t.dataVec[i] = 0

TensorAdd(t1, t2) ==
    TensorZipWith(LAMBDA x, y: x + y, t1, t2)

TensorAddComm(t1, t2) ==
    TensorAdd(t1, t2).dataVec = TensorAdd(t2, t1).dataVec

TensorAddAssoc(t1, t2, t3) ==
    TensorAdd(TensorAdd(t1, t2), t3).dataVec = 
    TensorAdd(t1, TensorAdd(t2, t3)).dataVec

TensorMul(t1, t2) ==
    TensorZipWith(LAMBDA x, y: x * y, t1, t2)

TensorMulComm(t1, t2) ==
    TensorMul(t1, t2).dataVec = TensorMul(t2, t1).dataVec

TensorMulAssoc(t1, t2, t3) ==
    TensorMul(TensorMul(t1, t2), t3).dataVec = 
    TensorMul(t1, TensorMul(t2, t3)).dataVec

TensorScalarMul(scalar, t) ==
    TensorMap(LAMBDA x: scalar * x, t)

TensorScalarMulDistributive(s, t1, t2) ==
    TensorScalarMul(s, TensorAdd(t1, t2)).dataVec =
    TensorAdd(TensorScalarMul(s, t1), TensorScalarMul(s, t2)).dataVec

TensorSum(t) ==
    TensorFold(LAMBDA x, y: x + y, 0, t)

TensorSumZero(shape) ==
    TensorSum(TensorZero(shape)) = 0

TensorSumAdd(t1, t2) ==
    TensorSum(TensorAdd(t1, t2)) = TensorSum(t1) + TensorSum(t2)

AliasingRule(t1, t2) ==
    /\ t1.ownership = "OWNED"
    /\ t2.ownership = "OWNED"
    => t1.dataVec # t2.dataVec

DeviceAffinityPreserving(t, OpT) ==
    OpT.device = t.device

TypeInvariant ==
    /\ DType \subseteq STRING
    /\ Layout \subseteq STRING
    /\ Device \subseteq STRING
    /\ Ownership \subseteq STRING

THEOREM ShapeConsistencyTheorem ==
    \A t, shape: TensorValid(t, shape) => ShapeConsistency(t, shape)

THEOREM LayoutTransformTheorems ==
    /\ \A t, newLayout: LayoutTransformPreservesData(t, newLayout)
    /\ \A t, newLayout: LayoutTransformPreservesDevice(t, newLayout)
    /\ \A t, newLayout: LayoutTransformChangesLayout(t, newLayout)

THEOREM TensorArithmeticTheorems ==
    /\ \A t1, t2: TensorAddComm(t1, t2)
    /\ \A t1, t2, t3: TensorAddAssoc(t1, t2, t3)
    /\ \A t1, t2: TensorMulComm(t1, t2)
    /\ \A t1, t2, t3: TensorMulAssoc(t1, t2, t3)
    /\ \A s, t1, t2: TensorScalarMulDistributive(s, t1, t2)

THEOREM TensorZeroTheorems ==
    /\ \A shape: TensorZeroIsZero(shape)
    /\ \A shape: TensorSumZero(shape)

====
