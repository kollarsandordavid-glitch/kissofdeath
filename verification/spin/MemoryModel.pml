typedef Arena {
    short bufferSize;
    short offset;
    bit valid;
}

typedef Slab {
    byte blockSize;
    byte numBlocks;
    byte usedBlocks;
    bit valid;
}

typedef Pool {
    byte blockSize;
    byte numBlocks;
    byte freeCount;
    bit valid;
}

typedef Refcount {
    byte count;
    bit valid;
}

Arena arenas[8];
Slab slabs[8];
Pool pools[8];
Refcount refcounts[16];

byte num_arenas = 0;
byte num_slabs = 0;
byte num_pools = 0;
byte num_refcounts = 0;

#define PageSize 16

inline align_forward(n, align, result) {
    result = ((n + align - 1) / align) * align;
}

inline arena_init(aid, size) {
    atomic {
        assert(aid < 8);
        assert(num_arenas < 8);
        assert(size > 0);
        
        short aligned_size;
        align_forward(size, PageSize, aligned_size);
        
        arenas[aid].bufferSize = aligned_size;
        arenas[aid].offset = 0;
        arenas[aid].valid = 1;
        
        num_arenas++;
        
        assert(arenas[aid].offset <= arenas[aid].bufferSize);
    }
}

inline arena_alloc(aid, size, alignment, success) {
    atomic {
        assert(aid < 8);
        assert(arenas[aid].valid == 1);
        assert(size > 0);
        assert(alignment > 0);
        
        short current_offset = arenas[aid].offset;
        short aligned_offset;
        align_forward(current_offset, alignment, aligned_offset);
        
        short end_offset = aligned_offset + size;
        
        if
        :: (end_offset <= arenas[aid].bufferSize) ->
            arenas[aid].offset = end_offset;
            success = 1;
            assert(arenas[aid].offset <= arenas[aid].bufferSize);
        :: (end_offset > arenas[aid].bufferSize) ->
            success = 0;
        fi;
    }
}

inline arena_reset(aid) {
    atomic {
        assert(aid < 8);
        assert(arenas[aid].valid == 1);
        
        arenas[aid].offset = 0;
        
        assert(arenas[aid].offset == 0);
        assert(arenas[aid].offset <= arenas[aid].bufferSize);
    }
}

inline slab_init(sid, blockSize, slabSize) {
    atomic {
        assert(sid < 8);
        assert(num_slabs < 8);
        assert(blockSize > 0);
        assert(slabSize > 0);
        
        slabs[sid].blockSize = blockSize;
        slabs[sid].numBlocks = slabSize / blockSize;
        slabs[sid].usedBlocks = 0;
        slabs[sid].valid = 1;
        
        num_slabs++;
        
        assert(slabs[sid].usedBlocks <= slabs[sid].numBlocks);
    }
}

inline slab_alloc_block(sid, success) {
    atomic {
        assert(sid < 8);
        assert(slabs[sid].valid == 1);
        
        if
        :: (slabs[sid].usedBlocks < slabs[sid].numBlocks) ->
            slabs[sid].usedBlocks++;
            success = 1;
            assert(slabs[sid].usedBlocks <= slabs[sid].numBlocks);
        :: (slabs[sid].usedBlocks >= slabs[sid].numBlocks) ->
            success = 0;
        fi;
    }
}

inline slab_free_block(sid) {
    atomic {
        assert(sid < 8);
        assert(slabs[sid].valid == 1);
        
        if
        :: (slabs[sid].usedBlocks > 0) ->
            slabs[sid].usedBlocks--;
            assert(slabs[sid].usedBlocks >= 0);
        :: (slabs[sid].usedBlocks == 0) ->
            skip;
        fi;
        
        assert(slabs[sid].usedBlocks <= slabs[sid].numBlocks);
    }
}

inline pool_init(pid, blockSize, numBlocks) {
    atomic {
        assert(pid < 8);
        assert(num_pools < 8);
        assert(blockSize > 0);
        assert(numBlocks > 0);
        
        pools[pid].blockSize = blockSize;
        pools[pid].numBlocks = numBlocks;
        pools[pid].freeCount = numBlocks;
        pools[pid].valid = 1;
        
        num_pools++;
        
        assert(pools[pid].freeCount <= pools[pid].numBlocks);
    }
}

inline pool_alloc(pid, success) {
    atomic {
        assert(pid < 8);
        assert(pools[pid].valid == 1);
        
        if
        :: (pools[pid].freeCount > 0) ->
            pools[pid].freeCount--;
            success = 1;
            assert(pools[pid].freeCount >= 0);
        :: (pools[pid].freeCount == 0) ->
            success = 0;
        fi;
        
        assert(pools[pid].freeCount <= pools[pid].numBlocks);
    }
}

inline pool_free(pid, success) {
    atomic {
        assert(pid < 8);
        assert(pools[pid].valid == 1);
        
        if
        :: (pools[pid].freeCount < pools[pid].numBlocks) ->
            pools[pid].freeCount++;
            success = 1;
            assert(pools[pid].freeCount <= pools[pid].numBlocks);
        :: (pools[pid].freeCount >= pools[pid].numBlocks) ->
            success = 0;
        fi;
    }
}

inline refcount_init(rid) {
    atomic {
        assert(rid < 16);
        assert(num_refcounts < 16);
        
        refcounts[rid].count = 1;
        refcounts[rid].valid = 1;
        
        num_refcounts++;
        
        assert(refcounts[rid].count > 0);
    }
}

inline refcount_increment(rid) {
    atomic {
        assert(rid < 16);
        assert(refcounts[rid].valid == 1);
        assert(refcounts[rid].count > 0);
        
        refcounts[rid].count++;
        
        assert(refcounts[rid].count > 0);
    }
}

inline refcount_decrement(rid) {
    atomic {
        assert(rid < 16);
        assert(refcounts[rid].valid == 1);
        assert(refcounts[rid].count > 0);
        
        if
        :: (refcounts[rid].count == 1) ->
            refcounts[rid].valid = 0;
            refcounts[rid].count = 0;
            num_refcounts--;
        :: (refcounts[rid].count > 1) ->
            refcounts[rid].count--;
            assert(refcounts[rid].count > 0);
        fi;
    }
}

ltl arena_offset_valid {
    [] (
        (num_arenas > 0) ->
        (forall [i : 0 .. 7] (
            (arenas[i].valid == 1) -> 
            (arenas[i].offset >= 0 && arenas[i].offset <= arenas[i].bufferSize)
        ))
    )
}

ltl slab_used_valid {
    [] (
        (num_slabs > 0) ->
        (forall [i : 0 .. 7] (
            (slabs[i].valid == 1) -> 
            (slabs[i].usedBlocks >= 0 && slabs[i].usedBlocks <= slabs[i].numBlocks)
        ))
    )
}

ltl pool_free_valid {
    [] (
        (num_pools > 0) ->
        (forall [i : 0 .. 7] (
            (pools[i].valid == 1) -> 
            (pools[i].freeCount >= 0 && pools[i].freeCount <= pools[i].numBlocks)
        ))
    )
}

ltl refcount_positive {
    [] (
        (num_refcounts > 0) ->
        (forall [i : 0 .. 15] (
            (refcounts[i].valid == 1) -> (refcounts[i].count > 0)
        ))
    )
}

ltl arena_count_valid {
    [] (num_arenas <= 8 && num_arenas >= 0)
}

ltl slab_count_valid {
    [] (num_slabs <= 8 && num_slabs >= 0)
}

ltl pool_count_valid {
    [] (num_pools <= 8 && num_pools >= 0)
}

ltl refcount_count_valid {
    [] (num_refcounts <= 16 && num_refcounts >= 0)
}

proctype ArenaOperations() {
    byte aid = 0;
    byte success;
    
    arena_init(aid, 100);
    assert(arenas[aid].valid == 1);
    assert(arenas[aid].offset == 0);
    
    arena_alloc(aid, 20, 4, success);
    assert(success == 1);
    assert(arenas[aid].offset >= 20);
    
    byte old_offset = arenas[aid].offset;
    
    arena_alloc(aid, 10, 1, success);
    assert(success == 1);
    assert(arenas[aid].offset >= old_offset);
    
    arena_reset(aid);
    assert(arenas[aid].offset == 0);
}

proctype SlabOperations() {
    byte sid = 0;
    byte success;
    
    slab_init(sid, 8, 64);
    assert(slabs[sid].valid == 1);
    assert(slabs[sid].usedBlocks == 0);
    assert(slabs[sid].numBlocks == 8);
    
    slab_alloc_block(sid, success);
    assert(success == 1);
    assert(slabs[sid].usedBlocks == 1);
    
    slab_alloc_block(sid, success);
    assert(success == 1);
    assert(slabs[sid].usedBlocks == 2);
    
    slab_free_block(sid);
    assert(slabs[sid].usedBlocks == 1);
    
    slab_free_block(sid);
    assert(slabs[sid].usedBlocks == 0);
}

proctype PoolOperations() {
    byte pid = 0;
    byte success;
    
    pool_init(pid, 16, 10);
    assert(pools[pid].valid == 1);
    assert(pools[pid].freeCount == 10);
    
    pool_alloc(pid, success);
    assert(success == 1);
    assert(pools[pid].freeCount == 9);
    
    pool_alloc(pid, success);
    assert(success == 1);
    assert(pools[pid].freeCount == 8);
    
    pool_free(pid, success);
    assert(success == 1);
    assert(pools[pid].freeCount == 9);
    
    pool_free(pid, success);
    assert(success == 1);
    assert(pools[pid].freeCount == 10);
}

proctype RefcountOperations() {
    byte rid = 0;
    
    refcount_init(rid);
    assert(refcounts[rid].valid == 1);
    assert(refcounts[rid].count == 1);
    
    refcount_increment(rid);
    assert(refcounts[rid].count == 2);
    
    refcount_increment(rid);
    assert(refcounts[rid].count == 3);
    
    refcount_decrement(rid);
    assert(refcounts[rid].count == 2);
    assert(refcounts[rid].valid == 1);
    
    refcount_decrement(rid);
    assert(refcounts[rid].count == 1);
    assert(refcounts[rid].valid == 1);
    
    refcount_decrement(rid);
    assert(refcounts[rid].valid == 0);
}

init {
    atomic {
        run ArenaOperations();
        run SlabOperations();
        run PoolOperations();
        run RefcountOperations();
    }
}
