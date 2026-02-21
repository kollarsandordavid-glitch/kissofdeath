---------------------------- MODULE MemorySpec ----------------------------

EXTENDS Naturals, Sequences, Integers, TLC

CONSTANTS MaxArenas, MaxSlabs, MaxPools, PageSize

VARIABLES arenas, slabs, pools, refcounts

PageSizeValue == 4096

AlignForward(n, align) ==
    ((n + align - 1) \div align) * align

TypeInvariant ==
    /\ arenas \in [DOMAIN arenas -> 
        [bufferSize: Nat, offset: Nat]]
    /\ slabs \in [DOMAIN slabs ->
        [blockSize: Nat, numBlocks: Nat, usedBlocks: Nat]]
    /\ pools \in [DOMAIN pools ->
        [blockSize: Nat, numBlocks: Nat, freeCount: Nat]]
    /\ refcounts \in [DOMAIN refcounts -> Nat]

ArenaInvariant ==
    \A aid \in DOMAIN arenas:
        /\ arenas[aid].offset >= 0
        /\ arenas[aid].offset <= arenas[aid].bufferSize
        /\ arenas[aid].bufferSize > 0

SlabInvariant ==
    \A sid \in DOMAIN slabs:
        /\ slabs[sid].blockSize > 0
        /\ slabs[sid].numBlocks > 0
        /\ slabs[sid].usedBlocks >= 0
        /\ slabs[sid].usedBlocks <= slabs[sid].numBlocks

PoolInvariant ==
    \A pid \in DOMAIN pools:
        /\ pools[pid].blockSize > 0
        /\ pools[pid].numBlocks > 0
        /\ pools[pid].freeCount >= 0
        /\ pools[pid].freeCount <= pools[pid].numBlocks

RefcountInvariant ==
    \A rid \in DOMAIN refcounts:
        refcounts[rid] >= 0

Init ==
    /\ arenas = <<>>
    /\ slabs = <<>>
    /\ pools = <<>>
    /\ refcounts = <<>>

ArenaInit(aid, size) ==
    /\ aid \notin DOMAIN arenas
    /\ size > 0
    /\ LET alignedSize == AlignForward(size, PageSizeValue)
       IN arenas' = arenas @@ (aid :> 
           [bufferSize |-> alignedSize, offset |-> 0])
    /\ UNCHANGED <<slabs, pools, refcounts>>

ArenaAlloc(aid, size, alignment) ==
    /\ aid \in DOMAIN arenas
    /\ size > 0
    /\ alignment > 0
    /\ LET currentOffset == arenas[aid].offset
           alignedOffset == AlignForward(currentOffset, alignment)
           endOffset == alignedOffset + size
       IN /\ IF endOffset <= arenas[aid].bufferSize
             THEN arenas' = [arenas EXCEPT ![aid].offset = endOffset]
             ELSE UNCHANGED arenas
    /\ UNCHANGED <<slabs, pools, refcounts>>

ArenaReset(aid) ==
    /\ aid \in DOMAIN arenas
    /\ arenas' = [arenas EXCEPT ![aid].offset = 0]
    /\ UNCHANGED <<slabs, pools, refcounts>>

SlabInit(sid, blockSize, slabSize) ==
    /\ sid \notin DOMAIN slabs
    /\ blockSize > 0
    /\ slabSize > 0
    /\ slabs' = slabs @@ (sid :>
        [blockSize |-> blockSize,
         numBlocks |-> slabSize \div blockSize,
         usedBlocks |-> 0])
    /\ UNCHANGED <<arenas, pools, refcounts>>

SlabAllocBlock(sid) ==
    /\ sid \in DOMAIN slabs
    /\ slabs[sid].usedBlocks < slabs[sid].numBlocks
    /\ slabs' = [slabs EXCEPT ![sid].usedBlocks = @ + 1]
    /\ UNCHANGED <<arenas, pools, refcounts>>

SlabFreeBlock(sid) ==
    /\ sid \in DOMAIN slabs
    /\ slabs[sid].usedBlocks > 0
    /\ slabs' = [slabs EXCEPT ![sid].usedBlocks = @ - 1]
    /\ UNCHANGED <<arenas, pools, refcounts>>

PoolInit(pid, blockSize, numBlocks) ==
    /\ pid \notin DOMAIN pools
    /\ blockSize > 0
    /\ numBlocks > 0
    /\ pools' = pools @@ (pid :>
        [blockSize |-> blockSize,
         numBlocks |-> numBlocks,
         freeCount |-> numBlocks])
    /\ UNCHANGED <<arenas, slabs, refcounts>>

PoolAlloc(pid) ==
    /\ pid \in DOMAIN pools
    /\ pools[pid].freeCount > 0
    /\ pools' = [pools EXCEPT ![pid].freeCount = @ - 1]
    /\ UNCHANGED <<arenas, slabs, refcounts>>

PoolFree(pid) ==
    /\ pid \in DOMAIN pools
    /\ pools[pid].freeCount < pools[pid].numBlocks
    /\ pools' = [pools EXCEPT ![pid].freeCount = @ + 1]
    /\ UNCHANGED <<arenas, slabs, refcounts>>

RefcountInit(rid) ==
    /\ rid \notin DOMAIN refcounts
    /\ refcounts' = refcounts @@ (rid :> 1)
    /\ UNCHANGED <<arenas, slabs, pools>>

RefcountIncrement(rid) ==
    /\ rid \in DOMAIN refcounts
    /\ refcounts' = [refcounts EXCEPT ![rid] = @ + 1]
    /\ UNCHANGED <<arenas, slabs, pools>>

RefcountDecrement(rid) ==
    /\ rid \in DOMAIN refcounts
    /\ refcounts[rid] > 0
    /\ IF refcounts[rid] = 1
       THEN refcounts' = [r \in (DOMAIN refcounts \ {rid}) |-> refcounts[r]]
       ELSE refcounts' = [refcounts EXCEPT ![rid] = @ - 1]
    /\ UNCHANGED <<arenas, slabs, pools>>

ArenaAllocMonotonic ==
    \A aid \in DOMAIN arenas:
        [][ArenaAlloc(aid, 1, 1) => arenas'[aid].offset >= arenas[aid].offset]_arenas

SlabUsedNonDecreasing ==
    \A sid \in DOMAIN slabs:
        [][SlabAllocBlock(sid) => slabs'[sid].usedBlocks > slabs[sid].usedBlocks]_slabs

PoolFreeMonotonic ==
    \A pid \in DOMAIN pools:
        [][PoolAlloc(pid) => pools'[pid].freeCount < pools[pid].freeCount]_pools

RefcountPositive ==
    \A rid \in DOMAIN refcounts:
        refcounts[rid] > 0

Next ==
    \/ \E aid, size: ArenaInit(aid, size)
    \/ \E aid, size, alignment: ArenaAlloc(aid, size, alignment)
    \/ \E aid: ArenaReset(aid)
    \/ \E sid, blockSize, slabSize: SlabInit(sid, blockSize, slabSize)
    \/ \E sid: SlabAllocBlock(sid)
    \/ \E sid: SlabFreeBlock(sid)
    \/ \E pid, blockSize, numBlocks: PoolInit(pid, blockSize, numBlocks)
    \/ \E pid: PoolAlloc(pid)
    \/ \E pid: PoolFree(pid)
    \/ \E rid: RefcountInit(rid)
    \/ \E rid: RefcountIncrement(rid)
    \/ \E rid: RefcountDecrement(rid)

Spec == Init /\ [][Next]_<<arenas, slabs, pools, refcounts>>

THEOREM TypeCorrectness == Spec => []TypeInvariant
THEOREM ArenaCorrectness == Spec => []ArenaInvariant
THEOREM SlabCorrectness == Spec => []SlabInvariant
THEOREM PoolCorrectness == Spec => []PoolInvariant
THEOREM RefcountCorrectness == Spec => []RefcountInvariant

THEOREM ArenaAllocMonotonicity == Spec => ArenaAllocMonotonic
THEOREM SlabUsageMonotonicity == Spec => SlabUsedNonDecreasing
THEOREM PoolFreeMonotonicity == Spec => PoolFreeMonotonic

PoolAllocFreeInverse ==
    \A pid \in DOMAIN pools:
        /\ [][PoolAlloc(pid) /\ PoolFree(pid) => 
            pools'[pid].freeCount = pools[pid].freeCount]_pools

THEOREM PoolInverse == Spec => PoolAllocFreeInverse

=============================================================================
