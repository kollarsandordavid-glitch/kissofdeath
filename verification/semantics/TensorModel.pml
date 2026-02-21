mtype = { F32, F64, I32, I64, U32, U64, BOOL };
mtype = { ROW_MAJOR, COLUMN_MAJOR, STRIDED };
mtype = { CPU, GPU, TPU };
mtype = { OWNED, BORROWED, VIEW };

#define MAX_SHAPE_SIZE 1024
#define MAX_DIMS 8

typedef Tensor {
    int dataVec[MAX_SHAPE_SIZE];
    int dataSize;
    mtype layout;
    mtype device;
    mtype ownership;
}

typedef Shape {
    int dims[MAX_DIMS];
    int ndims;
}

inline shapeSize(shape, result) {
    int i;
    result = 1;
    i = 0;
    do
    :: i < shape.ndims ->
        result = result * shape.dims[i];
        i++;
    :: else -> break;
    od;
}

inline tensorCreate(shape, dtype, t) {
    int size;
    shapeSize(shape, size);
    t.dataSize = size;
    t.layout = ROW_MAJOR;
    t.device = CPU;
    t.ownership = OWNED;
    int i = 0;
    do
    :: i < size ->
        t.dataVec[i] = 0;
        i++;
    :: else -> break;
    od;
}

inline tensorValid(t, shape) {
    int size;
    shapeSize(shape, size);
    assert(t.dataSize == size);
    assert(t.layout == ROW_MAJOR || t.layout == COLUMN_MAJOR || t.layout == STRIDED);
    assert(t.device == CPU || t.device == GPU || t.device == TPU);
    assert(t.ownership == OWNED || t.ownership == BORROWED || t.ownership == VIEW);
}

inline shapeConsistency(t, shape) {
    int size;
    shapeSize(shape, size);
    assert(t.dataSize == size);
}

inline memoryBounds(t, shape, i) {
    assert(i >= 0 && i < t.dataSize);
}

inline layoutTransform(t, newLayout, tPrime) {
    tPrime.dataSize = t.dataSize;
    int i = 0;
    do
    :: i < t.dataSize ->
        tPrime.dataVec[i] = t.dataVec[i];
        i++;
    :: else -> break;
    od;
    tPrime.layout = newLayout;
    tPrime.device = t.device;
    tPrime.ownership = t.ownership;
}

inline tensorMap(t, scalar, tPrime) {
    tPrime.dataSize = t.dataSize;
    int i = 0;
    do
    :: i < t.dataSize ->
        tPrime.dataVec[i] = t.dataVec[i] * scalar;
        i++;
    :: else -> break;
    od;
    tPrime.layout = t.layout;
    tPrime.device = t.device;
    tPrime.ownership = t.ownership;
}

inline tensorZipWith(t1, t2, tPrime) {
    assert(t1.dataSize == t2.dataSize);
    tPrime.dataSize = t1.dataSize;
    int i = 0;
    do
    :: i < t1.dataSize ->
        tPrime.dataVec[i] = t1.dataVec[i] + t2.dataVec[i];
        i++;
    :: else -> break;
    od;
    tPrime.layout = t1.layout;
    tPrime.device = t1.device;
    tPrime.ownership = t1.ownership;
}

inline tensorAdd(t1, t2, tPrime) {
    tensorZipWith(t1, t2, tPrime);
}

inline tensorZero(shape, t) {
    int size;
    shapeSize(shape, size);
    t.dataSize = size;
    t.layout = ROW_MAJOR;
    t.device = CPU;
    t.ownership = OWNED;
    int i = 0;
    do
    :: i < size ->
        t.dataVec[i] = 0;
        i++;
    :: else -> break;
    od;
}

inline tensorSum(t, result) {
    result = 0;
    int i = 0;
    do
    :: i < t.dataSize ->
        result = result + t.dataVec[i];
        i++;
    :: else -> break;
    od;
}

inline tensorScalarMul(t, scalar, tPrime) {
    tensorMap(t, scalar, tPrime);
}

inline tensorMul(t1, t2, tPrime) {
    assert(t1.dataSize == t2.dataSize);
    tPrime.dataSize = t1.dataSize;
    int i = 0;
    do
    :: i < t1.dataSize ->
        tPrime.dataVec[i] = t1.dataVec[i] * t2.dataVec[i];
        i++;
    :: else -> break;
    od;
    tPrime.layout = t1.layout;
    tPrime.device = t1.device;
    tPrime.ownership = t1.ownership;
}

proctype VerifyTensorOperations() {
    Tensor t1, t2, t3;
    Shape shape;
    
    shape.ndims = 2;
    shape.dims[0] = 4;
    shape.dims[1] = 4;
    
    tensorCreate(shape, F32, t1);
    tensorCreate(shape, F32, t2);
    
    tensorValid(t1, shape);
    tensorValid(t2, shape);
    
    shapeConsistency(t1, shape);
    shapeConsistency(t2, shape);
    
    tensorAdd(t1, t2, t3);
    tensorValid(t3, shape);
    
    int sum;
    tensorSum(t3, sum);
    assert(sum >= 0);
    
    Tensor t4;
    layoutTransform(t1, COLUMN_MAJOR, t4);
    assert(t4.layout == COLUMN_MAJOR);
    assert(t4.device == t1.device);
    
    Tensor t5;
    tensorScalarMul(t1, 2, t5);
    tensorValid(t5, shape);
    
    printf("All tensor operations verified successfully\n");
}

init {
    run VerifyTensorOperations();
}
