import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Vector
import Mathlib.Tactic

namespace Memory

def CacheLineSize : Nat := 128

theorem cacheLineSizeModern : CacheLineSize = 128 := rfl

def PageSizeRuntime (runtimeValue : Nat) : Nat := runtimeValue

def PageSizeDefault : Nat := 4096

structure MutexState where
  locked : Bool
  ownerThread : Nat
deriving Repr, DecidableEq

def MutexState.init : MutexState := ⟨false, 0⟩

def MutexState.lock (tid : Nat) (m : MutexState) : MutexState := ⟨true, tid⟩

def MutexState.unlock (m : MutexState) : MutexState := ⟨false, 0⟩

def MutexState.tryLock (tid : Nat) (m : MutexState) : MutexState × Bool :=
  if m.locked then (m, false) else (⟨true, tid⟩, true)

theorem mutexLockUnlock (tid : Nat) (m : MutexState) :
    (MutexState.unlock (MutexState.lock tid m)).locked = false := rfl

theorem mutexNoDoubleUnlock (m : MutexState) (h : m.locked = false) :
    MutexState.unlock m = ⟨false, 0⟩ := rfl

variable (PageSizeRT : Nat) in
def PageSize : Nat := PageSizeRT

def alignForwardRT (n align pageSize : Nat) : Nat :=
  ((n + align - 1) / align) * align

theorem pageSizeIsRuntimeValue (ps : Nat) (h : ps > 0) : PageSizeRuntime ps = ps := rfl

def alignForward (n align : Nat) (pageSize : Nat := PageSizeDefault) : Nat :=
  ((n + align - 1) / align) * align

theorem alignForward_ge (n align : Nat) (h : align > 0) : n ≤ alignForward n align := by
  simp [alignForward]
  omega

theorem alignForward_aligned (n align : Nat) (h : align > 0) :
  ∃ k, alignForward n align = k * align := by
  exists (n + align - 1) / align
  rfl

structure Arena where
  bufferSize : Nat
  offset : Nat
  offsetLeSize : offset ≤ bufferSize

def Arena.init (size : Nat) (pageSize : Nat := PageSizeDefault) : Arena :=
  ⟨alignForward size pageSize, 0, Nat.zero_le _⟩

def Arena.alloc (arena : Arena) (size alignment : Nat) : Option Arena :=
  let currentOffset := arena.offset
  let alignedOffset := alignForward currentOffset alignment
  let endOffset := alignedOffset + size
  if h : endOffset ≤ arena.bufferSize then
    some ⟨arena.bufferSize, endOffset, h⟩
  else
    none

def Arena.reset (arena : Arena) : Arena :=
  ⟨arena.bufferSize, 0, Nat.zero_le _⟩

def Arena.allocated (arena : Arena) : Nat :=
  arena.offset

def Arena.remaining (arena : Arena) : Nat :=
  arena.bufferSize - arena.offset

theorem Arena_alloc_increases_offset (arena : Arena) (size alignment : Nat) (result : Arena)
  (h : Arena.alloc arena size alignment = some result) :
  arena.offset ≤ result.offset := by
  simp [Arena.alloc] at h
  split at h <;> simp at h
  omega

theorem Arena_reset_clears (arena : Arena) :
  (Arena.reset arena).offset = 0 := by
  rfl

theorem Arena_remaining_correct (arena : Arena) :
  Arena.remaining arena + arena.offset = arena.bufferSize := by
  simp [Arena.remaining]
  omega

structure SlabMetadata where
  blockSize : Nat
  numBlocks : Nat
  usedBlocks : Nat
  usedLeTotal : usedBlocks ≤ numBlocks

def Slab.init (blockSize slabSize : Nat) : SlabMetadata :=
  ⟨blockSize, slabSize / blockSize, 0, Nat.zero_le _⟩

def Slab.allocBlock (slab : SlabMetadata) : Option SlabMetadata :=
  if h : slab.usedBlocks < slab.numBlocks then
    some ⟨slab.blockSize, slab.numBlocks, slab.usedBlocks + 1, Nat.succ_le_of_lt h⟩
  else
    none

def Slab.freeBlock (slab : SlabMetadata) : SlabMetadata :=
  match slab.usedBlocks with
  | 0 => slab
  | n+1 => ⟨slab.blockSize, slab.numBlocks, n, Nat.le_of_succ_le slab.usedLeTotal⟩

def Slab.isFull (slab : SlabMetadata) : Bool :=
  slab.usedBlocks = slab.numBlocks

def Slab.isEmpty (slab : SlabMetadata) : Bool :=
  slab.usedBlocks = 0

def Slab.utilization (slab : SlabMetadata) : Nat :=
  (slab.usedBlocks * 100) / slab.numBlocks

theorem Slab_alloc_increases_used (slab result : SlabMetadata)
  (h : Slab.allocBlock slab = some result) :
  slab.usedBlocks < result.usedBlocks := by
  simp [Slab.allocBlock] at h
  split at h <;> simp at h
  omega

theorem Slab_free_decreases_used (slab : SlabMetadata)
  (h : slab.usedBlocks > 0) :
  (Slab.freeBlock slab).usedBlocks < slab.usedBlocks := by
  simp [Slab.freeBlock]
  cases slab.usedBlocks with
  | zero => omega
  | succ n => omega

theorem Slab_invariant_preserved (slab : SlabMetadata) :
  (Slab.freeBlock slab).usedLeTotal := by
  simp [Slab.freeBlock]
  cases slab.usedBlocks with
  | zero => exact Nat.zero_le _
  | succ n => exact Nat.le_of_succ_le slab.usedLeTotal

structure PoolMetadata where
  blockSize : Nat
  numBlocks : Nat
  freeCount : Nat
  freeLeTotal : freeCount ≤ numBlocks

def Pool.init (blockSize numBlocks : Nat) : PoolMetadata :=
  ⟨blockSize, numBlocks, numBlocks, Nat.le_refl _⟩

def Pool.alloc (pool : PoolMetadata) : Option PoolMetadata :=
  match pool.freeCount with
  | 0 => none
  | n+1 => some ⟨pool.blockSize, pool.numBlocks, n, Nat.le_of_succ_le pool.freeLeTotal⟩

def Pool.free (pool : PoolMetadata) : Option PoolMetadata :=
  if h : pool.freeCount < pool.numBlocks then
    some ⟨pool.blockSize, pool.numBlocks, pool.freeCount + 1, Nat.succ_le_of_lt h⟩
  else
    none

def Pool.isFull (pool : PoolMetadata) : Bool :=
  pool.freeCount = 0

def Pool.isEmpty (pool : PoolMetadata) : Bool :=
  pool.freeCount = pool.numBlocks

theorem Pool_alloc_decreases_free (pool result : PoolMetadata)
  (h : Pool.alloc pool = some result) :
  result.freeCount < pool.freeCount := by
  simp [Pool.alloc] at h
  cases pool.freeCount with
  | zero => simp at h
  | succ n =>
    simp at h
    omega

theorem Pool_free_increases_free (pool result : PoolMetadata)
  (h : Pool.free pool = some result) :
  pool.freeCount < result.freeCount := by
  simp [Pool.free] at h
  split at h <;> simp at h
  omega

theorem Pool_alloc_free_inverse (pool pool' pool'' : PoolMetadata)
  (h1 : Pool.alloc pool = some pool')
  (h2 : Pool.free pool' = some pool'') :
  pool.freeCount = pool''.freeCount := by
  simp [Pool.alloc, Pool.free] at *
  cases pool.freeCount with
  | zero => simp at h1
  | succ n =>
    simp at h1 h2
    split at h2 <;> simp at h2
    omega

structure BuddyMetadata where
  totalSize : Nat
  minBlockSize : Nat
  maxOrder : Nat
  freeLists : Vector Nat (maxOrder + 1)
  totalSizePow2 : ∃ k, totalSize = minBlockSize * (2 ^ k)

def Buddy.init (totalSize minBlock maxOrder : Nat) : BuddyMetadata :=
  ⟨totalSize, minBlock, maxOrder, Vector.cons 1 (Vector.replicate maxOrder 0), ⟨maxOrder, rfl⟩⟩

def Buddy.orderForSize (size minBlock : Nat) : Nat :=
  let rec loop (s order : Nat) : Nat :=
    if s ≤ minBlock then order
    else loop (s / 2) (order + 1)
  loop size 0

def Buddy.allocOrder (buddy : BuddyMetadata) (order : Nat) : Option BuddyMetadata :=
  if h : order < buddy.maxOrder + 1 then
    let count := buddy.freeLists.get ⟨order, h⟩
    if count > 0 then
      let newFreeLists := buddy.freeLists.set ⟨order, h⟩ (count - 1)
      some ⟨buddy.totalSize, buddy.minBlockSize, buddy.maxOrder, newFreeLists, buddy.totalSizePow2⟩
    else
      none
  else
    none

def Buddy.freeOrder (buddy : BuddyMetadata) (order : Nat) : BuddyMetadata :=
  if h : order < buddy.maxOrder + 1 then
    let count := buddy.freeLists.get ⟨order, h⟩
    let newFreeLists := buddy.freeLists.set ⟨order, h⟩ (count + 1)
    ⟨buddy.totalSize, buddy.minBlockSize, buddy.maxOrder, newFreeLists, buddy.totalSizePow2⟩
  else
    buddy

theorem Buddy_size_invariant (buddy : BuddyMetadata) :
  ∃ k, buddy.totalSize = buddy.minBlockSize * (2 ^ k) :=
  buddy.totalSizePow2

def AtomicRefcount : Type := Nat

def Refcount.init : AtomicRefcount := 1

def Refcount.increment (rc : AtomicRefcount) : AtomicRefcount := rc + 1

def Refcount.decrement (rc : AtomicRefcount) : AtomicRefcount :=
  if rc = 0 then 0 else rc - 1

def Refcount.isZero (rc : AtomicRefcount) : Bool := rc = 0

theorem Refcount_increment_positive (rc : AtomicRefcount) :
  Refcount.increment rc > 0 := by
  simp [Refcount.increment]
  omega

theorem Refcount_inc_dec_inverse (rc : AtomicRefcount) (h : rc > 0) :
  Refcount.decrement (Refcount.increment rc) = rc := by
  simp [Refcount.increment, Refcount.decrement]
  omega

theorem Refcount_monotone_dec (rc : AtomicRefcount) :
  Refcount.decrement rc ≤ rc := by
  simp [Refcount.decrement]
  split <;> omega

structure MemoryRegion where
  startAddr : Nat
  size : Nat
  allocated : Bool

def MemRegion.init (start size : Nat) : MemoryRegion :=
  ⟨start, size, false⟩

def MemRegion.inBounds (region : MemoryRegion) (addr : Nat) : Bool :=
  region.startAddr ≤ addr && addr < region.startAddr + region.size

theorem MemRegion_bounds_correct (region : MemoryRegion) (addr : Nat)
  (h : MemRegion.inBounds region addr = true) :
  region.startAddr ≤ addr ∧ addr < region.startAddr + region.size := by
  simp [MemRegion.inBounds] at h
  omega

structure CacheLineState where
  valid : Bool
  dirty : Bool
  tag : Nat

def CacheLine.init : CacheLineState :=
  ⟨false, false, 0⟩

def CacheLine.load (line : CacheLineState) (tag : Nat) : CacheLineState :=
  ⟨true, line.dirty, tag⟩

def CacheLine.store (line : CacheLineState) (tag : Nat) : CacheLineState :=
  ⟨true, true, tag⟩

def CacheLine.invalidate (line : CacheLineState) : CacheLineState :=
  ⟨false, line.dirty, line.tag⟩

def CacheLine.flush (line : CacheLineState) : CacheLineState :=
  ⟨line.valid, false, line.tag⟩

theorem CacheLine_load_valid (line : CacheLineState) (tag : Nat) :
  (CacheLine.load line tag).valid = true := by
  rfl

theorem CacheLine_store_dirty (line : CacheLineState) (tag : Nat) :
  (CacheLine.store line tag).dirty = true := by
  rfl

theorem CacheLine_invalidate_clears (line : CacheLineState) :
  (CacheLine.invalidate line).valid = false := by
  rfl

theorem CacheLine_flush_clears_dirty (line : CacheLineState) :
  (CacheLine.flush line).dirty = false := by
  rfl

end Memory
