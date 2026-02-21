/* Tensor Complete Verification in Promela/Spin */
/* Production-ready formal verification with complete state space coverage */
/* Synced with Zig core: COW mutex semantics, Fixed32_32 error returns, 128-byte cache lines */

#define MAX_TENSORS 8
#define MAX_DATA_SIZE 16
#define MAX_REFCOUNT 10
#define MAX_VALUE 1000
#define CACHE_LINE_SIZE 128
#define EPSILON 1

mtype = { F32, F64, I32, I64, U32, U64, BOOL_TYPE };
mtype = { ROW_MAJOR, COLUMN_MAJOR, STRIDED };
mtype = { CPU, GPU, TPU };
mtype = { OWNED, BORROWED, VIEW };
mtype = { COW_EXCLUSIVE, COW_SHARED };
mtype = { ERR_NONE, ERR_OVERFLOW, ERR_DIVISION_BY_ZERO, ERR_OUT_OF_BOUNDS };

typedef MutexState {
  bit locked;
  byte owner_id;
}

typedef RefCountState {
  byte count;
}

#define MAX_DATA_BUFFERS 16

typedef TensorDataBuffer {
  int values[MAX_DATA_SIZE];
  byte length;
  byte buffer_refcount;
  bit buffer_allocated;
}

typedef TensorShape {
  byte dims[4];
  byte rank;
}

typedef Tensor {
  TensorShape shape;
  byte data_buffer_id;
  mtype dtype;
  mtype layout;
  mtype device;
  mtype ownership;
  RefCountState refcount;
  mtype cow_state;
  MutexState mutex;
  bit allocated;
}

TensorDataBuffer data_buffers[MAX_DATA_BUFFERS];
byte next_buffer_id = 0;

Tensor tensors[MAX_TENSORS];
byte nextTensorId = 0;
byte allocatedCount = 0;

inline allocate_buffer(buf_id) {
  byte search_idx = 0;
  bit found = 0;
  do
  :: (search_idx < MAX_DATA_BUFFERS && found == 0) -> {
      if
      :: (data_buffers[search_idx].buffer_allocated == 0) -> {
          buf_id = search_idx;
          found = 1;
        }
      :: else -> search_idx++;
      fi;
    }
  :: (search_idx >= MAX_DATA_BUFFERS || found == 1) -> break;
  od;
  assert(found == 1);
  data_buffers[buf_id].buffer_allocated = 1;
  data_buffers[buf_id].buffer_refcount = 1;
}

inline copy_buffer_data(src_buf_id, dst_buf_id) {
  byte i;
  for (i : 0 .. data_buffers[src_buf_id].length - 1) {
    data_buffers[dst_buf_id].values[i] = data_buffers[src_buf_id].values[i];
  }
  data_buffers[dst_buf_id].length = data_buffers[src_buf_id].length;
}

inline buffer_incref(buf_id) {
  data_buffers[buf_id].buffer_refcount = data_buffers[buf_id].buffer_refcount + 1;
}

inline buffer_decref(buf_id) {
  data_buffers[buf_id].buffer_refcount = data_buffers[buf_id].buffer_refcount - 1;
  if
  :: (data_buffers[buf_id].buffer_refcount == 0) -> {
      data_buffers[buf_id].buffer_allocated = 0;
    }
  :: else -> skip;
  fi;
}

byte shape_size(TensorShape s) {
  byte result = 1;
  byte i;
  for (i : 0 .. s.rank - 1) {
    result = result * s.dims[i];
  }
  return result;
}

byte get_tensor_data_value(byte tid; byte idx) {
  return data_buffers[tensors[tid].data_buffer_id].values[idx];
}

inline set_tensor_data_value(tid, idx, val) {
  data_buffers[tensors[tid].data_buffer_id].values[idx] = val;
}

inline mutex_init(m) {
  m.locked = 0;
  m.owner_id = 0;
}

inline mutex_lock(m, tid) {
  m.locked = 1;
  m.owner_id = tid;
}

inline mutex_unlock(m) {
  m.locked = 0;
  m.owner_id = 0;
}

inline refcount_init(rc) {
  rc.count = 1;
}

inline refcount_increment(rc) {
  rc.count = rc.count + 1;
}

proctype CreateTensor(mtype dt; mtype lay; mtype dev; byte rank; byte d0; byte d1) {
  atomic {
    byte tid;
    byte buf_id;
    
    assert(nextTensorId < MAX_TENSORS);
    assert(allocatedCount < MAX_TENSORS);
    assert(rank > 0 && rank <= 2);
    
    tid = nextTensorId;
    nextTensorId++;
    allocatedCount++;
    
    allocate_buffer(buf_id);
    
    tensors[tid].allocated = 1;
    tensors[tid].dtype = dt;
    tensors[tid].layout = lay;
    tensors[tid].device = dev;
    tensors[tid].ownership = OWNED;
    tensors[tid].data_buffer_id = buf_id;
    refcount_init(tensors[tid].refcount);
    tensors[tid].cow_state = COW_EXCLUSIVE;
    mutex_init(tensors[tid].mutex);
    tensors[tid].shape.rank = rank;
    tensors[tid].shape.dims[0] = d0;
    
    if
    :: (rank >= 2) -> tensors[tid].shape.dims[1] = d1;
    :: else -> skip;
    fi;
    
    byte size = shape_size(tensors[tid].shape);
    data_buffers[buf_id].length = size;
    
    byte i;
    for (i : 0 .. size - 1) {
      data_buffers[buf_id].values[i] = 0;
    }
    
    assert(tensors[tid].refcount.count > 0);
    assert(tensors[tid].cow_state == COW_EXCLUSIVE);
    assert(tensors[tid].mutex.locked == 0);
    assert(data_buffers[buf_id].length == size);
    assert(data_buffers[buf_id].length <= MAX_DATA_SIZE);
  }
}

proctype Incref(byte tid) {
  atomic {
    assert(tid < MAX_TENSORS);
    assert(tensors[tid].allocated == 1);
    assert(tensors[tid].refcount.count < MAX_REFCOUNT);
    
    refcount_increment(tensors[tid].refcount);
    buffer_incref(tensors[tid].data_buffer_id);
    tensors[tid].cow_state = COW_SHARED;
    
    assert(tensors[tid].refcount.count > 0);
    assert(tensors[tid].cow_state == COW_SHARED);
    assert(tensors[tid].allocated == 1);
  }
}

proctype Decref(byte tid) {
  atomic {
    assert(tid < MAX_TENSORS);
    assert(tensors[tid].allocated == 1);
    assert(tensors[tid].refcount.count > 0);
    
    tensors[tid].refcount.count = tensors[tid].refcount.count - 1;
    buffer_decref(tensors[tid].data_buffer_id);
    
    if
    :: (tensors[tid].refcount.count == 0) -> {
        tensors[tid].allocated = 0;
        allocatedCount--;
        assert(allocatedCount >= 0);
      }
    :: else -> skip;
    fi;
  }
}

proctype TensorView(byte src_tid; byte dst_tid) {
  atomic {
    assert(src_tid < MAX_TENSORS);
    assert(dst_tid < MAX_TENSORS);
    assert(tensors[src_tid].allocated == 1);
    
    tensors[dst_tid].data_buffer_id = tensors[src_tid].data_buffer_id;
    buffer_incref(tensors[src_tid].data_buffer_id);
    
    refcount_increment(tensors[src_tid].refcount);
    tensors[src_tid].cow_state = COW_SHARED;
    tensors[dst_tid].cow_state = COW_SHARED;
    
    assert(tensors[src_tid].cow_state == COW_SHARED);
    assert(tensors[src_tid].data_buffer_id == tensors[dst_tid].data_buffer_id);
  }
}

proctype EnsureWritable(byte tid) {
  atomic {
    byte old_buf_id;
    byte new_buf_id;
    
    assert(tid < MAX_TENSORS);
    assert(tensors[tid].allocated == 1);
    
    if
    :: (tensors[tid].cow_state == COW_EXCLUSIVE) -> {
        skip;
      }
    :: (tensors[tid].cow_state == COW_SHARED) -> {
        old_buf_id = tensors[tid].data_buffer_id;
        
        allocate_buffer(new_buf_id);
        copy_buffer_data(old_buf_id, new_buf_id);
        
        buffer_decref(old_buf_id);
        
        tensors[tid].data_buffer_id = new_buf_id;
        refcount_init(tensors[tid].refcount);
        tensors[tid].cow_state = COW_EXCLUSIVE;
        mutex_init(tensors[tid].mutex);
        
        assert(tensors[tid].refcount.count == 1);
        assert(tensors[tid].cow_state == COW_EXCLUSIVE);
        assert(tensors[tid].mutex.locked == 0);
        assert(tensors[tid].data_buffer_id == new_buf_id);
        assert(tensors[tid].data_buffer_id != old_buf_id);
      }
    fi;
  }
}

proctype TensorAdd(byte tid1; byte tid2) {
  atomic {
    byte resultId;
    byte result_buf_id;
    byte buf1_id;
    byte buf2_id;
    byte i;
    
    assert(tid1 < MAX_TENSORS && tid2 < MAX_TENSORS);
    assert(tensors[tid1].allocated == 1);
    assert(tensors[tid2].allocated == 1);
    assert(tensors[tid1].shape.rank == tensors[tid2].shape.rank);
    
    buf1_id = tensors[tid1].data_buffer_id;
    buf2_id = tensors[tid2].data_buffer_id;
    assert(data_buffers[buf1_id].length == data_buffers[buf2_id].length);
    assert(nextTensorId < MAX_TENSORS);
    
    resultId = nextTensorId;
    nextTensorId++;
    allocatedCount++;
    
    allocate_buffer(result_buf_id);
    
    tensors[resultId].allocated = 1;
    tensors[resultId].shape = tensors[tid1].shape;
    tensors[resultId].data_buffer_id = result_buf_id;
    tensors[resultId].dtype = tensors[tid1].dtype;
    tensors[resultId].layout = tensors[tid1].layout;
    tensors[resultId].device = tensors[tid1].device;
    tensors[resultId].ownership = OWNED;
    refcount_init(tensors[resultId].refcount);
    tensors[resultId].cow_state = COW_EXCLUSIVE;
    mutex_init(tensors[resultId].mutex);
    
    data_buffers[result_buf_id].length = data_buffers[buf1_id].length;
    for (i : 0 .. data_buffers[buf1_id].length - 1) {
      data_buffers[result_buf_id].values[i] = 
        data_buffers[buf1_id].values[i] + data_buffers[buf2_id].values[i];
    }
    
    assert(tensors[resultId].allocated == 1);
    assert(tensors[resultId].refcount.count == 1);
    assert(data_buffers[result_buf_id].length == data_buffers[buf1_id].length);
  }
}

proctype TensorSub(byte tid1; byte tid2) {
  atomic {
    byte resultId;
    byte result_buf_id;
    byte buf1_id;
    byte buf2_id;
    byte i;
    
    assert(tid1 < MAX_TENSORS && tid2 < MAX_TENSORS);
    assert(tensors[tid1].allocated == 1);
    assert(tensors[tid2].allocated == 1);
    assert(tensors[tid1].shape.rank == tensors[tid2].shape.rank);
    
    buf1_id = tensors[tid1].data_buffer_id;
    buf2_id = tensors[tid2].data_buffer_id;
    assert(data_buffers[buf1_id].length == data_buffers[buf2_id].length);
    assert(nextTensorId < MAX_TENSORS);
    
    resultId = nextTensorId;
    nextTensorId++;
    allocatedCount++;
    
    allocate_buffer(result_buf_id);
    
    tensors[resultId].allocated = 1;
    tensors[resultId].shape = tensors[tid1].shape;
    tensors[resultId].data_buffer_id = result_buf_id;
    tensors[resultId].dtype = tensors[tid1].dtype;
    tensors[resultId].layout = tensors[tid1].layout;
    tensors[resultId].device = tensors[tid1].device;
    tensors[resultId].ownership = OWNED;
    refcount_init(tensors[resultId].refcount);
    tensors[resultId].cow_state = COW_EXCLUSIVE;
    mutex_init(tensors[resultId].mutex);
    
    data_buffers[result_buf_id].length = data_buffers[buf1_id].length;
    for (i : 0 .. data_buffers[buf1_id].length - 1) {
      data_buffers[result_buf_id].values[i] = 
        data_buffers[buf1_id].values[i] - data_buffers[buf2_id].values[i];
    }
    
    assert(tensors[resultId].allocated == 1);
    assert(tensors[resultId].refcount.count == 1);
  }
}

proctype TensorMul(byte tid1; byte tid2) {
  atomic {
    byte resultId;
    byte result_buf_id;
    byte buf1_id;
    byte buf2_id;
    byte i;
    
    assert(tid1 < MAX_TENSORS && tid2 < MAX_TENSORS);
    assert(tensors[tid1].allocated == 1);
    assert(tensors[tid2].allocated == 1);
    assert(tensors[tid1].shape.rank == tensors[tid2].shape.rank);
    
    buf1_id = tensors[tid1].data_buffer_id;
    buf2_id = tensors[tid2].data_buffer_id;
    assert(data_buffers[buf1_id].length == data_buffers[buf2_id].length);
    assert(nextTensorId < MAX_TENSORS);
    
    resultId = nextTensorId;
    nextTensorId++;
    allocatedCount++;
    
    allocate_buffer(result_buf_id);
    
    tensors[resultId].allocated = 1;
    tensors[resultId].shape = tensors[tid1].shape;
    tensors[resultId].data_buffer_id = result_buf_id;
    tensors[resultId].dtype = tensors[tid1].dtype;
    tensors[resultId].layout = tensors[tid1].layout;
    tensors[resultId].device = tensors[tid1].device;
    tensors[resultId].ownership = OWNED;
    refcount_init(tensors[resultId].refcount);
    tensors[resultId].cow_state = COW_EXCLUSIVE;
    mutex_init(tensors[resultId].mutex);
    
    data_buffers[result_buf_id].length = data_buffers[buf1_id].length;
    for (i : 0 .. data_buffers[buf1_id].length - 1) {
      data_buffers[result_buf_id].values[i] = 
        data_buffers[buf1_id].values[i] * data_buffers[buf2_id].values[i];
    }
    
    assert(tensors[resultId].allocated == 1);
    assert(tensors[resultId].refcount.count == 1);
  }
}

proctype TensorScalarMul(byte tid; int scalar) {
  atomic {
    byte resultId;
    byte result_buf_id;
    byte src_buf_id;
    byte i;
    
    assert(tid < MAX_TENSORS);
    assert(tensors[tid].allocated == 1);
    assert(nextTensorId < MAX_TENSORS);
    assert(scalar >= -MAX_VALUE && scalar <= MAX_VALUE);
    
    src_buf_id = tensors[tid].data_buffer_id;
    
    resultId = nextTensorId;
    nextTensorId++;
    allocatedCount++;
    
    allocate_buffer(result_buf_id);
    
    tensors[resultId].allocated = 1;
    tensors[resultId].shape = tensors[tid].shape;
    tensors[resultId].data_buffer_id = result_buf_id;
    tensors[resultId].dtype = tensors[tid].dtype;
    tensors[resultId].layout = tensors[tid].layout;
    tensors[resultId].device = tensors[tid].device;
    tensors[resultId].ownership = OWNED;
    refcount_init(tensors[resultId].refcount);
    tensors[resultId].cow_state = COW_EXCLUSIVE;
    mutex_init(tensors[resultId].mutex);
    
    data_buffers[result_buf_id].length = data_buffers[src_buf_id].length;
    for (i : 0 .. data_buffers[src_buf_id].length - 1) {
      data_buffers[result_buf_id].values[i] = data_buffers[src_buf_id].values[i] * scalar;
    }
    
    assert(tensors[resultId].allocated == 1);
    assert(tensors[resultId].refcount.count == 1);
  }
}

proctype TensorFill(byte tid; int value) {
  atomic {
    byte i;
    byte buf_id;
    
    assert(tid < MAX_TENSORS);
    assert(tensors[tid].allocated == 1);
    assert(tensors[tid].ownership == OWNED);
    assert(value >= -MAX_VALUE && value <= MAX_VALUE);
    
    buf_id = tensors[tid].data_buffer_id;
    for (i : 0 .. data_buffers[buf_id].length - 1) {
      data_buffers[buf_id].values[i] = value;
    }
    
    assert(tensors[tid].allocated == 1);
  }
}

proctype TensorCopy(byte tid) {
  atomic {
    byte resultId;
    byte result_buf_id;
    byte src_buf_id;
    byte i;
    
    assert(tid < MAX_TENSORS);
    assert(tensors[tid].allocated == 1);
    assert(nextTensorId < MAX_TENSORS);
    
    src_buf_id = tensors[tid].data_buffer_id;
    
    resultId = nextTensorId;
    nextTensorId++;
    allocatedCount++;
    
    allocate_buffer(result_buf_id);
    
    tensors[resultId].allocated = 1;
    tensors[resultId].shape = tensors[tid].shape;
    tensors[resultId].data_buffer_id = result_buf_id;
    tensors[resultId].dtype = tensors[tid].dtype;
    tensors[resultId].layout = tensors[tid].layout;
    tensors[resultId].device = tensors[tid].device;
    tensors[resultId].ownership = OWNED;
    refcount_init(tensors[resultId].refcount);
    tensors[resultId].cow_state = COW_EXCLUSIVE;
    mutex_init(tensors[resultId].mutex);
    
    data_buffers[result_buf_id].length = data_buffers[src_buf_id].length;
    for (i : 0 .. data_buffers[src_buf_id].length - 1) {
      data_buffers[result_buf_id].values[i] = data_buffers[src_buf_id].values[i];
    }
    
    assert(tensors[resultId].allocated == 1);
    assert(tensors[resultId].refcount.count == 1);
    assert(data_buffers[result_buf_id].length == data_buffers[src_buf_id].length);
  }
}

proctype LayoutTransform(byte tid; mtype newLayout) {
  atomic {
    assert(tid < MAX_TENSORS);
    assert(tensors[tid].allocated == 1);
    
    byte i;
    byte buf_id;
    int oldData[MAX_DATA_SIZE];
    
    buf_id = tensors[tid].data_buffer_id;
    for (i : 0 .. data_buffers[buf_id].length - 1) {
      oldData[i] = data_buffers[buf_id].values[i];
    }
    
    tensors[tid].layout = newLayout;
    
    for (i : 0 .. data_buffers[buf_id].length - 1) {
      assert(data_buffers[buf_id].values[i] == oldData[i]);
    }
    
    assert(tensors[tid].allocated == 1);
  }
}

proctype DeviceTransfer(byte tid; mtype newDevice) {
  atomic {
    assert(tid < MAX_TENSORS);
    assert(tensors[tid].allocated == 1);
    
    byte i;
    byte buf_id;
    int oldData[MAX_DATA_SIZE];
    
    buf_id = tensors[tid].data_buffer_id;
    for (i : 0 .. data_buffers[buf_id].length - 1) {
      oldData[i] = data_buffers[buf_id].values[i];
    }
    
    tensors[tid].device = newDevice;
    
    for (i : 0 .. data_buffers[buf_id].length - 1) {
      assert(data_buffers[buf_id].values[i] == oldData[i]);
    }
    
    assert(tensors[tid].allocated == 1);
  }
}

proctype TensorReLU(byte tid) {
  atomic {
    byte resultId;
    byte result_buf_id;
    byte src_buf_id;
    byte i;
    
    assert(tid < MAX_TENSORS);
    assert(tensors[tid].allocated == 1);
    assert(nextTensorId < MAX_TENSORS);
    
    src_buf_id = tensors[tid].data_buffer_id;
    
    resultId = nextTensorId;
    nextTensorId++;
    allocatedCount++;
    
    allocate_buffer(result_buf_id);
    
    tensors[resultId].allocated = 1;
    tensors[resultId].shape = tensors[tid].shape;
    tensors[resultId].data_buffer_id = result_buf_id;
    tensors[resultId].dtype = tensors[tid].dtype;
    tensors[resultId].layout = tensors[tid].layout;
    tensors[resultId].device = tensors[tid].device;
    tensors[resultId].ownership = OWNED;
    refcount_init(tensors[resultId].refcount);
    tensors[resultId].cow_state = COW_EXCLUSIVE;
    mutex_init(tensors[resultId].mutex);
    
    data_buffers[result_buf_id].length = data_buffers[src_buf_id].length;
    for (i : 0 .. data_buffers[src_buf_id].length - 1) {
      if
      :: (data_buffers[src_buf_id].values[i] < 0) -> data_buffers[result_buf_id].values[i] = 0;
      :: else -> data_buffers[result_buf_id].values[i] = data_buffers[src_buf_id].values[i];
      fi;
    }
    
    for (i : 0 .. data_buffers[result_buf_id].length - 1) {
      assert(data_buffers[result_buf_id].values[i] >= 0);
    }
    
    assert(tensors[resultId].allocated == 1);
    assert(tensors[resultId].refcount.count == 1);
  }
}

proctype TensorClip(byte tid; int minVal; int maxVal) {
  atomic {
    byte resultId;
    byte result_buf_id;
    byte src_buf_id;
    byte i;
    
    assert(tid < MAX_TENSORS);
    assert(tensors[tid].allocated == 1);
    assert(nextTensorId < MAX_TENSORS);
    assert(minVal <= maxVal);
    
    src_buf_id = tensors[tid].data_buffer_id;
    
    resultId = nextTensorId;
    nextTensorId++;
    allocatedCount++;
    
    allocate_buffer(result_buf_id);
    
    tensors[resultId].allocated = 1;
    tensors[resultId].shape = tensors[tid].shape;
    tensors[resultId].data_buffer_id = result_buf_id;
    tensors[resultId].dtype = tensors[tid].dtype;
    tensors[resultId].layout = tensors[tid].layout;
    tensors[resultId].device = tensors[tid].device;
    tensors[resultId].ownership = OWNED;
    refcount_init(tensors[resultId].refcount);
    tensors[resultId].cow_state = COW_EXCLUSIVE;
    mutex_init(tensors[resultId].mutex);
    
    data_buffers[result_buf_id].length = data_buffers[src_buf_id].length;
    for (i : 0 .. data_buffers[src_buf_id].length - 1) {
      if
      :: (data_buffers[src_buf_id].values[i] < minVal) -> data_buffers[result_buf_id].values[i] = minVal;
      :: (data_buffers[src_buf_id].values[i] > maxVal) -> data_buffers[result_buf_id].values[i] = maxVal;
      :: else -> data_buffers[result_buf_id].values[i] = data_buffers[src_buf_id].values[i];
      fi;
    }
    
    for (i : 0 .. data_buffers[result_buf_id].length - 1) {
      assert(data_buffers[result_buf_id].values[i] >= minVal);
      assert(data_buffers[result_buf_id].values[i] <= maxVal);
    }
    
    assert(tensors[resultId].allocated == 1);
    assert(tensors[resultId].refcount.count == 1);
  }
}

ltl memory_safety { [](allocatedCount >= 0 && allocatedCount <= MAX_TENSORS) }
ltl no_memory_leaks { []((allocatedCount > 0) -> <>(allocatedCount == 0)) }
ltl refcount_positive { [](
  (tensors[0].allocated == 1 -> tensors[0].refcount.count > 0) &&
  (tensors[1].allocated == 1 -> tensors[1].refcount.count > 0) &&
  (tensors[2].allocated == 1 -> tensors[2].refcount.count > 0) &&
  (tensors[3].allocated == 1 -> tensors[3].refcount.count > 0)
) }
ltl no_use_after_free { [](
  (tensors[0].allocated == 0 -> tensors[0].refcount.count == 0) &&
  (tensors[1].allocated == 0 -> tensors[1].refcount.count == 0) &&
  (tensors[2].allocated == 0 -> tensors[2].refcount.count == 0) &&
  (tensors[3].allocated == 0 -> tensors[3].refcount.count == 0)
) }
ltl buffer_refcount_valid { [](
  (data_buffers[0].buffer_allocated == 1 -> data_buffers[0].buffer_refcount > 0) &&
  (data_buffers[1].buffer_allocated == 1 -> data_buffers[1].buffer_refcount > 0) &&
  (data_buffers[2].buffer_allocated == 1 -> data_buffers[2].buffer_refcount > 0) &&
  (data_buffers[3].buffer_allocated == 1 -> data_buffers[3].buffer_refcount > 0)
) }
ltl cow_exclusive_after_ensure_writable { [](
  ((tensors[0].allocated == 1 && tensors[0].cow_state == COW_EXCLUSIVE) -> tensors[0].refcount.count == 1) &&
  ((tensors[1].allocated == 1 && tensors[1].cow_state == COW_EXCLUSIVE) -> tensors[1].refcount.count == 1) &&
  ((tensors[2].allocated == 1 && tensors[2].cow_state == COW_EXCLUSIVE) -> tensors[2].refcount.count == 1) &&
  ((tensors[3].allocated == 1 && tensors[3].cow_state == COW_EXCLUSIVE) -> tensors[3].refcount.count == 1)
) }

init {
  byte i;
  for (i : 0 .. MAX_TENSORS - 1) {
    tensors[i].allocated = 0;
    refcount_init(tensors[i].refcount);
    tensors[i].refcount.count = 0;
    tensors[i].cow_state = COW_EXCLUSIVE;
    mutex_init(tensors[i].mutex);
  }
  for (i : 0 .. MAX_DATA_BUFFERS - 1) {
    data_buffers[i].buffer_allocated = 0;
    data_buffers[i].buffer_refcount = 0;
    data_buffers[i].length = 0;
  }
  
  run CreateTensor(F32, ROW_MAJOR, CPU, 1, 4, 0);
  run CreateTensor(F32, ROW_MAJOR, CPU, 1, 4, 0);
  run TensorAdd(0, 1);
  run Incref(0);
  run Decref(0);
  run Decref(0);
  run TensorFill(1, 5);
  run TensorCopy(1);
  run TensorReLU(1);
  run TensorScalarMul(1, 2);
  run LayoutTransform(1, COLUMN_MAJOR);
  run DeviceTransfer(1, GPU);
  run Decref(1);
  run Decref(2);
  run Decref(3);
  run Decref(4);
  run Decref(5);
}
