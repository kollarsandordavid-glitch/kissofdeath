typedef TensorData {
    byte data[64];
    byte len;
}

typedef Shape {
    byte dims[8];
    byte ndim;
}

typedef Tensor {
    TensorData tdata;
    Shape shape;
    byte refcount;
    bit valid;
}

Tensor tensors[16];
byte num_tensors = 0;
byte next_tid = 0;

inline shape_size(s, result) {
    byte i;
    result = 1;
    i = 0;
    do
    :: (i < s.ndim) ->
        result = result * s.dims[i];
        i++;
    :: (i >= s.ndim) -> break;
    od;
}

inline tensor_init(tid, s) {
    atomic {
        assert(tid < 16);
        assert(num_tensors < 16);
        
        tensors[tid].shape = s;
        tensors[tid].refcount = 1;
        tensors[tid].valid = 1;
        
        byte size;
        shape_size(s, size);
        
        tensors[tid].tdata.len = size;
        
        byte i = 0;
        do
        :: (i < size) ->
            tensors[tid].tdata.data[i] = 0;
            i++;
        :: (i >= size) -> break;
        od;
        
        num_tensors++;
    }
}

inline tensor_retain(tid) {
    atomic {
        assert(tid < 16);
        assert(tensors[tid].valid == 1);
        assert(tensors[tid].refcount > 0);
        
        tensors[tid].refcount++;
        
        assert(tensors[tid].refcount > 0);
    }
}

inline tensor_release(tid) {
    atomic {
        assert(tid < 16);
        assert(tensors[tid].valid == 1);
        assert(tensors[tid].refcount > 0);
        
        if
        :: (tensors[tid].refcount == 1) ->
            tensors[tid].valid = 0;
            tensors[tid].refcount = 0;
            num_tensors--;
        :: (tensors[tid].refcount > 1) ->
            tensors[tid].refcount--;
        fi;
    }
}

inline tensor_fill(tid, value) {
    atomic {
        assert(tid < 16);
        assert(tensors[tid].valid == 1);
        
        byte i = 0;
        do
        :: (i < tensors[tid].tdata.len) ->
            tensors[tid].tdata.data[i] = value;
            i++;
        :: (i >= tensors[tid].tdata.len) -> break;
        od;
    }
}

inline tensor_add_pointwise(tid1, tid2, tidResult) {
    atomic {
        assert(tid1 < 16);
        assert(tid2 < 16);
        assert(tidResult < 16);
        assert(tensors[tid1].valid == 1);
        assert(tensors[tid2].valid == 1);
        assert(tensors[tidResult].valid == 0);
        
        assert(tensors[tid1].shape.ndim == tensors[tid2].shape.ndim);
        
        byte i;
        i = 0;
        do
        :: (i < tensors[tid1].shape.ndim) ->
            assert(tensors[tid1].shape.dims[i] == tensors[tid2].shape.dims[i]);
            i++;
        :: (i >= tensors[tid1].shape.ndim) -> break;
        od;
        
        tensors[tidResult].shape = tensors[tid1].shape;
        tensors[tidResult].tdata.len = tensors[tid1].tdata.len;
        tensors[tidResult].refcount = 1;
        tensors[tidResult].valid = 1;
        
        i = 0;
        do
        :: (i < tensors[tid1].tdata.len) ->
            tensors[tidResult].tdata.data[i] = 
                tensors[tid1].tdata.data[i] + tensors[tid2].tdata.data[i];
            i++;
        :: (i >= tensors[tid1].tdata.len) -> break;
        od;
        
        num_tensors++;
    }
}

inline tensor_sub_pointwise(tid1, tid2, tidResult) {
    atomic {
        assert(tid1 < 16);
        assert(tid2 < 16);
        assert(tidResult < 16);
        assert(tensors[tid1].valid == 1);
        assert(tensors[tid2].valid == 1);
        assert(tensors[tidResult].valid == 0);
        
        assert(tensors[tid1].shape.ndim == tensors[tid2].shape.ndim);
        
        tensors[tidResult].shape = tensors[tid1].shape;
        tensors[tidResult].tdata.len = tensors[tid1].tdata.len;
        tensors[tidResult].refcount = 1;
        tensors[tidResult].valid = 1;
        
        byte i = 0;
        do
        :: (i < tensors[tid1].tdata.len) ->
            if
            :: (tensors[tid1].tdata.data[i] >= tensors[tid2].tdata.data[i]) ->
                tensors[tidResult].tdata.data[i] = 
                    tensors[tid1].tdata.data[i] - tensors[tid2].tdata.data[i];
            :: (tensors[tid1].tdata.data[i] < tensors[tid2].tdata.data[i]) ->
                tensors[tidResult].tdata.data[i] = 0;
            fi;
            i++;
        :: (i >= tensors[tid1].tdata.len) -> break;
        od;
        
        num_tensors++;
    }
}

inline tensor_mul_pointwise(tid1, tid2, tidResult) {
    atomic {
        assert(tid1 < 16);
        assert(tid2 < 16);
        assert(tidResult < 16);
        assert(tensors[tid1].valid == 1);
        assert(tensors[tid2].valid == 1);
        assert(tensors[tidResult].valid == 0);
        
        assert(tensors[tid1].shape.ndim == tensors[tid2].shape.ndim);
        
        tensors[tidResult].shape = tensors[tid1].shape;
        tensors[tidResult].tdata.len = tensors[tid1].tdata.len;
        tensors[tidResult].refcount = 1;
        tensors[tidResult].valid = 1;
        
        byte i = 0;
        do
        :: (i < tensors[tid1].tdata.len) ->
            tensors[tidResult].tdata.data[i] = 
                tensors[tid1].tdata.data[i] * tensors[tid2].tdata.data[i];
            i++;
        :: (i >= tensors[tid1].tdata.len) -> break;
        od;
        
        num_tensors++;
    }
}

inline tensor_scalar_add(tid, scalar, tidResult) {
    atomic {
        assert(tid < 16);
        assert(tidResult < 16);
        assert(tensors[tid].valid == 1);
        assert(tensors[tidResult].valid == 0);
        
        tensors[tidResult].shape = tensors[tid].shape;
        tensors[tidResult].tdata.len = tensors[tid].tdata.len;
        tensors[tidResult].refcount = 1;
        tensors[tidResult].valid = 1;
        
        byte i = 0;
        do
        :: (i < tensors[tid].tdata.len) ->
            tensors[tidResult].tdata.data[i] = 
                tensors[tid].tdata.data[i] + scalar;
            i++;
        :: (i >= tensors[tid].tdata.len) -> break;
        od;
        
        num_tensors++;
    }
}

inline tensor_scalar_mul(tid, scalar, tidResult) {
    atomic {
        assert(tid < 16);
        assert(tidResult < 16);
        assert(tensors[tid].valid == 1);
        assert(tensors[tidResult].valid == 0);
        
        tensors[tidResult].shape = tensors[tid].shape;
        tensors[tidResult].tdata.len = tensors[tid].tdata.len;
        tensors[tidResult].refcount = 1;
        tensors[tidResult].valid = 1;
        
        byte i = 0;
        do
        :: (i < tensors[tid].tdata.len) ->
            tensors[tidResult].tdata.data[i] = 
                tensors[tid].tdata.data[i] * scalar;
            i++;
        :: (i >= tensors[tid].tdata.len) -> break;
        od;
        
        num_tensors++;
    }
}

ltl refcount_positive {
    [] (
        (num_tensors > 0) ->
        (forall [i : 0 .. 15] (
            (tensors[i].valid == 1) -> (tensors[i].refcount > 0)
        ))
    )
}

ltl shape_size_consistent {
    [] (
        (num_tensors > 0) ->
        (forall [i : 0 .. 15] (
            (tensors[i].valid == 1) -> (tensors[i].tdata.len > 0)
        ))
    )
}

ltl valid_tensor_count {
    [] (num_tensors <= 16 && num_tensors >= 0)
}

proctype TensorOperations() {
    Shape s1, s2;
    byte tid1, tid2, tidResult;
    
    s1.ndim = 2;
    s1.dims[0] = 3;
    s1.dims[1] = 4;
    
    s2.ndim = 2;
    s2.dims[0] = 3;
    s2.dims[1] = 4;
    
    tid1 = 0;
    tid2 = 1;
    tidResult = 2;
    
    tensor_init(tid1, s1);
    tensor_init(tid2, s2);
    
    assert(tensors[tid1].valid == 1);
    assert(tensors[tid2].valid == 1);
    assert(tensors[tid1].refcount == 1);
    assert(tensors[tid2].refcount == 1);
    
    tensor_retain(tid1);
    assert(tensors[tid1].refcount == 2);
    
    tensor_fill(tid1, 5);
    tensor_fill(tid2, 3);
    
    tensor_add_pointwise(tid1, tid2, tidResult);
    
    assert(tensors[tidResult].valid == 1);
    assert(tensors[tidResult].refcount == 1);
    assert(tensors[tidResult].tdata.len == tensors[tid1].tdata.len);
    
    byte i = 0;
    do
    :: (i < tensors[tidResult].tdata.len) ->
        assert(tensors[tidResult].tdata.data[i] == 8);
        i++;
    :: (i >= tensors[tidResult].tdata.len) -> break;
    od;
    
    tensor_release(tid1);
    assert(tensors[tid1].refcount == 1);
    
    tensor_release(tid1);
    assert(tensors[tid1].valid == 0);
    
    tensor_release(tid2);
    tensor_release(tidResult);
}

init {
    run TensorOperations();
}
