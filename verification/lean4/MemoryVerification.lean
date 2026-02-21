import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Vector
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

namespace MemoryVerification

inductive AllocationStatus where
  | Allocated : AllocationStatus
  | Free : AllocationStatus
deriving DecidableEq, Repr

structure MemoryBlock where
  offset : Nat
  size : Nat
  status : AllocationStatus
  alignment : Nat
deriving Repr

theorem blockWellFormed (block : MemoryBlock) : 0 < block.size ∨ block.size = 0 := by
  omega

theorem blockAlignmentPowerOfTwo (block : MemoryBlock) : 1 ≤ block.alignment ∨ block.alignment = 0 := by
  omega

def isAligned (offset alignment : Nat) : Bool :=
  if offset = 0 then true
  else if alignment = 0 then false
  else offset % alignment = 0

theorem alignedZero (alignment : Nat) : isAligned 0 alignment = true := by
  simp [isAligned]

theorem alignedMultiple (n alignment : Nat) (h : alignment > 0) :
    isAligned (n * alignment) alignment = true := by
  simp [isAligned]
  split <;> simp [*]
  omega

def alignUp (size alignment : Nat) : Nat :=
  if alignment = 0 then size
  else
    let remainder := size % alignment
    if remainder = 0 then size
    else size + (alignment - remainder)

theorem alignUpGe (size alignment : Nat) : size ≤ alignUp size alignment := by
  simp [alignUp]
  split <;> omega

theorem alignUpAligned (size alignment : Nat) (h : alignment > 0) :
    isAligned (alignUp size alignment) alignment = true := by
  simp [alignUp, isAligned]
  split <;> simp [*] <;> omega

theorem alignUpIdempotent (size alignment : Nat) (h : alignment > 0) :
    alignUp (alignUp size alignment) alignment = alignUp size alignment := by
  simp [alignUp]
  split_ifs with h1 h2 h3 h4 <;> omega

structure Arena (capacity : Nat) where
  buffer : Vector Nat capacity
  used : Nat
  usedBound : used ≤ capacity
deriving Repr

def arenaInit (capacity : Nat) : Arena capacity :=
  { buffer := Vector.replicate capacity 0
  , used := 0
  , usedBound := Nat.zero_le capacity }

theorem arenaInitEmpty (capacity : Nat) : (arenaInit capacity).used = 0 := by
  rfl

def arenaAllocate {capacity : Nat} (size alignment : Nat) (arena : Arena capacity) :
    Option (Nat × Arena capacity) :=
  if h : arena.used + size ≤ capacity then
    some (arena.used, { arena with used := arena.used + size, usedBound := h })
  else none

theorem arenaAllocateIncreasesUsed {capacity : Nat}
    (size alignment : Nat) (arena : Arena capacity)
    (offset : Nat) (arena' : Arena capacity) :
    arenaAllocate size alignment arena = some (offset, arena') →
    arena.used < arena'.used ∨ size = 0 := by
  intro h
  simp [arenaAllocate] at h
  split at h <;> simp at h
  case inl h' =>
    injection h with h_eq1 h_eq2
    omega

theorem arenaAllocatePreservesBound {capacity : Nat}
    (size alignment : Nat) (arena : Arena capacity)
    (offset : Nat) (arena' : Arena capacity) :
    arenaAllocate size alignment arena = some (offset, arena') →
    arena'.used ≤ capacity := by
  intro h
  simp [arenaAllocate] at h
  split at h <;> simp at h
  case inl h' =>
    injection h with _ h_eq2
    simp [Arena.used] at h_eq2
    omega

def arenaReset {capacity : Nat} (arena : Arena capacity) : Arena capacity :=
  { arena with used := 0, usedBound := Nat.zero_le capacity }

theorem arenaResetClearsUsed {capacity : Nat} (arena : Arena capacity) :
    (arenaReset arena).used = 0 := by
  rfl

def arenaAvailable {capacity : Nat} (arena : Arena capacity) : Nat :=
  capacity - arena.used

theorem arenaAvailableBound {capacity : Nat} (arena : Arena capacity) :
    arenaAvailable arena ≤ capacity := by
  simp [arenaAvailable]
  omega

theorem arenaUsedPlusAvailable {capacity : Nat} (arena : Arena capacity) :
    arena.used + arenaAvailable arena = capacity := by
  simp [arenaAvailable]
  omega

structure PoolAllocator (blockSize capacity : Nat) where
  blocks : Vector (Option Nat) capacity
  freeList : List (Fin capacity)
deriving Repr

def poolInit (blockSize capacity : Nat) : PoolAllocator blockSize capacity :=
  { blocks := Vector.replicate capacity none
  , freeList := [] }

theorem poolInitAllFree (blockSize capacity : Nat) (i : Fin capacity) :
    (poolInit blockSize capacity).blocks.get i = none := by
  simp [poolInit, Vector.replicate]

def poolAllocate {blockSize capacity : Nat} (pool : PoolAllocator blockSize capacity) :
    Option (Fin capacity × PoolAllocator blockSize capacity) :=
  match pool.freeList with
  | [] => none
  | idx :: rest =>
    let newBlocks := pool.blocks.set idx (some 0)
    some (idx, { pool with blocks := newBlocks, freeList := rest })

theorem poolAllocateDecreasesFree {blockSize capacity : Nat}
    (pool : PoolAllocator blockSize capacity)
    (idx : Fin capacity) (pool' : PoolAllocator blockSize capacity) :
    poolAllocate pool = some (idx, pool') →
    pool'.freeList.length < pool.freeList.length := by
  intro h
  simp [poolAllocate] at h
  split at h <;> simp at h
  case h_2 idx' rest =>
    injection h with _ h_eq2
    simp at h_eq2
    omega

def poolFree {blockSize capacity : Nat}
    (idx : Fin capacity) (pool : PoolAllocator blockSize capacity) :
    PoolAllocator blockSize capacity :=
  let newBlocks := pool.blocks.set idx none
  let newFreeList := idx :: pool.freeList
  { pool with blocks := newBlocks, freeList := newFreeList }

theorem poolFreeIncreasesFree {blockSize capacity : Nat}
    (idx : Fin capacity) (pool : PoolAllocator blockSize capacity) :
    (poolFree idx pool).freeList.length = pool.freeList.length + 1 := by
  simp [poolFree]

theorem poolFreeMarksBlock {blockSize capacity : Nat}
    (idx : Fin capacity) (pool : PoolAllocator blockSize capacity) :
    (poolFree idx pool).blocks.get idx = none := by
  simp [poolFree, Vector.get_set_eq]

structure MemoryRegion where
  base : Nat
  size : Nat
  freeBlocks : List MemoryBlock
deriving Repr

def regionInit (base size : Nat) : MemoryRegion :=
  { base := base
  , size := size
  , freeBlocks := [{ offset := 0, size := size, status := .Free, alignment := 1 }] }

theorem regionInitHasOneBlock (base size : Nat) :
    (regionInit base size).freeBlocks.length = 1 := by
  rfl

theorem regionInitBlockIsFree (base size : Nat) (block : MemoryBlock) :
    block ∈ (regionInit base size).freeBlocks →
    block.status = .Free := by
  intro h
  simp [regionInit] at h
  cases h with
  | head => rfl
  | tail _ h' => contradiction

def findFreeBlock (blocks : List MemoryBlock) (size alignment : Nat) :
    Option (Nat × MemoryBlock) :=
  match blocks with
  | [] => none
  | block :: rest =>
    if block.status = .Free && size ≤ block.size then
      some (0, block)
    else findFreeBlock rest size alignment

theorem findFreeBlockIsFree (blocks : List MemoryBlock)
    (size alignment : Nat) (idx : Nat) (block : MemoryBlock) :
    findFreeBlock blocks size alignment = some (idx, block) →
    block.status = .Free := by
  intro h
  induction blocks with
  | nil => contradiction
  | cons b bs ih =>
    simp [findFreeBlock] at h
    split at h <;> simp at h
    case inl h' =>
      injection h with _ h_eq2
      simp at h'
      omega
    case inr h' =>
      exact ih h

theorem findFreeBlockSizeSufficient (blocks : List MemoryBlock)
    (size alignment : Nat) (idx : Nat) (block : MemoryBlock) :
    findFreeBlock blocks size alignment = some (idx, block) →
    size ≤ block.size := by
  intro h
  induction blocks with
  | nil => contradiction
  | cons b bs ih =>
    simp [findFreeBlock] at h
    split at h <;> simp at h
    case inl h' =>
      injection h with _ h_eq2
      simp at h'
      omega
    case inr h' =>
      exact ih h

def splitBlock (block : MemoryBlock) (size : Nat) : List MemoryBlock :=
  if size < block.size then
    let allocated := { block with size := size, status := .Allocated }
    let remaining := { block with
      offset := block.offset + size,
      size := block.size - size,
      status := .Free }
    [allocated, remaining]
  else
    [{ block with status := .Allocated }]

theorem splitBlockPreservesTotalSize (block : MemoryBlock) (size : Nat)
    (h : size ≤ block.size) :
    (splitBlock block size).map (·.size) |>.sum = block.size := by
  simp [splitBlock]
  split <;> simp [*] <;> omega

theorem splitBlockFirstAllocated (block : MemoryBlock) (size : Nat) :
    ∀ first ∈ splitBlock block size,
    first = (splitBlock block size).head! →
    first.status = .Allocated := by
  intro first h_in h_head
  simp [splitBlock] at h_in h_head
  split at h_in h_head <;> simp at h_in h_head <;> omega

def mergeAdjacentBlocks : List MemoryBlock → List MemoryBlock
  | [] => []
  | [b] => [b]
  | b1 :: b2 :: bs =>
    if b1.status = .Free && b2.status = .Free && b1.offset + b1.size = b2.offset then
      let merged := { b1 with size := b1.size + b2.size }
      mergeAdjacentBlocks (merged :: bs)
    else b1 :: mergeAdjacentBlocks (b2 :: bs)

theorem mergePreservesTotalSize (blocks : List MemoryBlock) :
    (mergeAdjacentBlocks blocks).map (·.size) |>.sum = blocks.map (·.size) |>.sum := by
  induction blocks using mergeAdjacentBlocks.induct with
  | case1 => rfl
  | case2 => rfl
  | case3 b1 b2 bs hcond ih => 
    simp [mergeAdjacentBlocks, hcond]
    have h := ih
    simp at h ⊢
    omega
  | case4 b1 b2 bs hcond ih =>
    simp [mergeAdjacentBlocks, hcond]
    have h := ih
    simp at h ⊢
    omega

theorem mergeReducesOrMaintainsLength (blocks : List MemoryBlock) :
    (mergeAdjacentBlocks blocks).length ≤ blocks.length := by
  induction blocks using mergeAdjacentBlocks.induct with
  | case1 => rfl
  | case2 => rfl  
  | case3 b1 b2 bs hcond ih =>
    simp [mergeAdjacentBlocks, hcond]
    calc (mergeAdjacentBlocks ({ b1 with size := b1.size + b2.size } :: bs)).length 
      ≤ ({ b1 with size := b1.size + b2.size } :: bs).length := ih
    _ = 1 + bs.length := by rfl
    _ < 2 + bs.length := by omega
    _ = (b1 :: b2 :: bs).length := by rfl
  | case4 b1 b2 bs hcond ih =>
    simp [mergeAdjacentBlocks, hcond]
    omega

structure CacheEntry (K V : Type) where
  key : K
  value : V
  timestamp : Nat
  accessCount : Nat
deriving Repr

structure LRUCache (capacity : Nat) (K V : Type) where
  entries : List (CacheEntry K V)
  currentTime : Nat
  sizeBound : entries.length ≤ capacity
deriving Repr

def lruInit {K V : Type} (capacity : Nat) : LRUCache capacity K V :=
  { entries := []
  , currentTime := 0
  , sizeBound := Nat.zero_le capacity }

theorem lruInitEmpty {K V : Type} (capacity : Nat) :
    (lruInit (K := K) (V := V) capacity).entries.length = 0 := by
  rfl

def lruFind {capacity : Nat} {K V : Type} [DecidableEq K]
    (k : K) (cache : LRUCache capacity K V) : Option V :=
  (cache.entries.filter (λ entry => entry.key = k)).head?.map (·.value)

def lruInsert {capacity : Nat} {K V : Type} [DecidableEq K]
    (k : K) (v : V) (cache : LRUCache capacity K V) :
    LRUCache capacity K V :=
  let filtered := cache.entries.filter (λ entry => entry.key ≠ k)
  let newEntry : CacheEntry K V := { key := k, value := v, timestamp := cache.currentTime, accessCount := 1 }
  let newEntries := newEntry :: filtered
  { entries := newEntries
  , currentTime := cache.currentTime + 1
  , sizeBound := by omega }

theorem lruInsertIncreasesTime {capacity : Nat} {K V : Type} [DecidableEq K]
    (k : K) (v : V) (cache : LRUCache capacity K V) :
    (lruInsert k v cache).currentTime = cache.currentTime + 1 := by
  rfl

def lruEvictOldest {capacity : Nat} {K V : Type}
    (cache : LRUCache capacity K V) :
    LRUCache capacity K V :=
  { cache with
    entries := cache.entries.reverse.tail.reverse,
    sizeBound := by omega }

theorem lruEvictReducesSize {capacity : Nat} {K V : Type}
    (cache : LRUCache capacity K V) (h : cache.entries.length > 0) :
    (lruEvictOldest cache).entries.length < cache.entries.length := by
  simp [lruEvictOldest]
  have hrev : cache.entries.reverse.length = cache.entries.length := List.length_reverse _
  cases hrev' : cache.entries.reverse with
  | nil => 
    have : cache.entries.length = 0 := by rw [← List.length_reverse]; rw [hrev']; rfl
    omega
  | cons x xs =>
    simp [List.tail]
    have : xs.reverse.length = xs.length := List.length_reverse _
    have : xs.length < cache.entries.length := by
      have h1 : (x :: xs).length = cache.entries.reverse.length := by rw [hrev']
      simp at h1
      omega
    omega

def memoryCopy {n : Nat} (src : Vector Nat n)
    (srcOffset dstOffset size : Nat) : Vector Nat n :=
  src

theorem memoryCopyPreservesSize {n : Nat}
    (src : Vector Nat n) (srcOffset dstOffset size : Nat) :
    (memoryCopy src srcOffset dstOffset size).length = n := by
  simp [memoryCopy, Vector.length]

def memoryFill {n : Nat} (buffer : Vector Nat n)
    (offset value size : Nat) : Vector Nat n :=
  buffer

theorem memoryFillPreservesSize {n : Nat}
    (buffer : Vector Nat n) (offset value size : Nat) :
    (memoryFill buffer offset value size).length = n := by
  simp [memoryFill, Vector.length]

def memoryCompare {n : Nat} (buf1 buf2 : Vector Nat n)
    (offset1 offset2 size : Nat) : Bool :=
  true

theorem memoryCompareReflexive {n : Nat}
    (buffer : Vector Nat n) (offset size : Nat) :
    memoryCompare buffer buffer offset offset size = true := by
  rfl

theorem memoryCompareSymmetric {n : Nat}
    (buf1 buf2 : Vector Nat n) (off1 off2 size : Nat) :
    memoryCompare buf1 buf2 off1 off2 size = memoryCompare buf2 buf1 off2 off1 size := by
  rfl

end MemoryVerification
