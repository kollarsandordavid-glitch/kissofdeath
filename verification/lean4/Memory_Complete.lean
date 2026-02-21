import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Vector
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

namespace MemoryVerification

def PageSize : Nat := 4096

structure MemoryBlock where
  base : Nat
  size : Nat
  allocated : Bool

structure AllocatorState where
  totalSize : Nat
  offset : Nat
  blocks : List MemoryBlock
  offsetValid : offset ≤ totalSize

def alignForward (value alignment : Nat) : Nat :=
  let remainder := value % alignment
  if remainder = 0 then value else value + (alignment - remainder)

theorem alignForward_geq (value alignment : Nat) : 
  value ≤ alignForward value alignment := by
  unfold alignForward
  split
  · omega
  · omega

theorem alignForward_multiple (value alignment : Nat) (h : 0 < alignment) :
  ∃ k, alignForward value alignment = k * alignment := by
  unfold alignForward
  split
  · rename_i heq
    exists value / alignment
    rw [heq, Nat.mul_comm]
    exact Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero heq)
  · rename_i hneq
    exists (value / alignment + 1)
    omega

structure Arena where
  bufferSize : Nat
  offset : Nat
  offsetValid : offset ≤ bufferSize

def Arena.init (size : Nat) : Arena :=
  { bufferSize := alignForward size PageSize
  , offset := 0
  , offsetValid := Nat.zero_le _ }

def Arena.alloc (arena : Arena) (size alignment : Nat) : Option (Nat × Arena) :=
  if size = 0 then
    some (0, arena)
  else
    let currentOffset := arena.offset
    let alignedOffset := alignForward currentOffset alignment
    let endOffset := alignedOffset + size
    if h : endOffset ≤ arena.bufferSize then
      some (alignedOffset, { arena with offset := endOffset, offsetValid := h })
    else
      none

theorem Arena.alloc_preserves_invariant (arena : Arena) (size alignment : Nat) 
  (result : Nat × Arena) (h : arena.alloc size alignment = some result) :
  result.2.offset ≤ result.2.bufferSize := by
  unfold alloc at h
  split at h
  · injection h with h1
    rw [← h1]
    exact arena.offsetValid
  · split at h
    · injection h with h1
      rw [← h1]
      simp
    · contradiction

def Arena.reset (arena : Arena) : Arena :=
  { arena with offset := 0, offsetValid := Nat.zero_le _ }

theorem Arena.reset_preserves_buffer (arena : Arena) :
  (arena.reset).bufferSize = arena.bufferSize := by
  rfl

theorem Arena.reset_zeros_offset (arena : Arena) :
  (arena.reset).offset = 0 := by
  rfl

def Arena.allocated (arena : Arena) : Nat :=
  arena.offset

def Arena.remaining (arena : Arena) : Nat :=
  arena.bufferSize - arena.offset

theorem Arena.allocated_plus_remaining (arena : Arena) :
  arena.allocated + arena.remaining = arena.bufferSize := by
  unfold allocated remaining
  omega

structure SlabState (numBlocks : Nat) where
  blockSize : Nat
  freeBlocks : List (Fin numBlocks)

def SlabState.init (numBlocks blockSize : Nat) : SlabState numBlocks :=
  { blockSize := blockSize
  , freeBlocks := List.finRange numBlocks }

def SlabState.alloc {n : Nat} (slab : SlabState n) : Option (Fin n × SlabState n) :=
  match slab.freeBlocks with
  | [] => none
  | x :: xs => some (x, { slab with freeBlocks := xs })

theorem SlabState.alloc_decreases_free {n : Nat} (slab : SlabState n) 
  (result : Fin n × SlabState n) (h : slab.alloc = some result) :
  result.2.freeBlocks.length = slab.freeBlocks.length - 1 := by
  unfold alloc at h
  cases slab.freeBlocks
  · contradiction
  · injection h with h1
    rw [← h1]
    simp

def SlabState.free {n : Nat} (slab : SlabState n) (blockIdx : Fin n) : SlabState n :=
  { slab with freeBlocks := blockIdx :: slab.freeBlocks }

theorem SlabState.free_increases_free {n : Nat} (slab : SlabState n) (block : Fin n) :
  (slab.free block).freeBlocks.length = slab.freeBlocks.length + 1 := by
  unfold free
  simp

theorem SlabState.alloc_free_identity {n : Nat} (slab : SlabState n) 
  (result : Fin n × SlabState n) (h : slab.alloc = some result) :
  (result.2.free result.1).freeBlocks = slab.freeBlocks := by
  unfold alloc at h
  cases heq : slab.freeBlocks
  · rw [heq] at h
    contradiction
  · rw [heq] at h
    injection h with h1
    unfold free
    simp
    rw [← h1]
    simp

structure PoolState (numBlocks : Nat) where
  blockSize : Nat
  freeListHead : Option (Fin numBlocks)
  usedCount : Nat
  usedValid : usedCount ≤ numBlocks

def PoolState.init (numBlocks blockSize : Nat) : PoolState numBlocks :=
  { blockSize := blockSize
  , freeListHead := if h : 0 < numBlocks then some ⟨0, h⟩ else none
  , usedCount := 0
  , usedValid := Nat.zero_le _ }

def PoolState.alloc {n : Nat} (pool : PoolState n) : 
  Option (Fin n × PoolState n) :=
  match pool.freeListHead with
  | none => none
  | some headIdx => 
      if h : pool.usedCount + 1 ≤ n then
        some (headIdx, { pool with 
          freeListHead := none,
          usedCount := pool.usedCount + 1,
          usedValid := h })
      else none

theorem PoolState.alloc_increases_used {n : Nat} (pool : PoolState n) 
  (result : Fin n × PoolState n) (h : pool.alloc = some result) :
  result.2.usedCount = pool.usedCount + 1 := by
  unfold alloc at h
  cases pool.freeListHead
  · contradiction
  · split at h
    · injection h with h1
      rw [← h1]
      simp
    · contradiction

def PoolState.free {n : Nat} (pool : PoolState n) (blockIdx : Fin n) : 
  PoolState n :=
  if h : 0 < pool.usedCount then
    { pool with 
      freeListHead := some blockIdx,
      usedCount := pool.usedCount - 1,
      usedValid := Nat.sub_le pool.usedCount 1 ▸ pool.usedValid }
  else pool

theorem PoolState.free_decreases_used {n : Nat} (pool : PoolState n) 
  (block : Fin n) (h : 0 < pool.usedCount) :
  (pool.free block).usedCount = pool.usedCount - 1 := by
  unfold free
  split
  · simp
  · contradiction

inductive BuddyTree : Nat → Type where
  | leaf : BuddyTree 0
  | node : {n : Nat} → Bool → BuddyTree n → BuddyTree n → BuddyTree (n + 1)

def BuddyTree.height : {n : Nat} → BuddyTree n → Nat
  | n, _ => n

def BuddyTree.mark : {n : Nat} → BuddyTree n → List (Fin n) → BuddyTree n
  | 0, leaf, _ => leaf
  | n+1, node allocated left right, [] => node true left right
  | n+1, node allocated left right, (⟨0, _⟩ :: path) => 
      node true (left.mark (path.map (Fin.castSucc))) right
  | n+1, node allocated left right, (⟨i+1, hi⟩ :: path) => 
      node true left (right.mark (path.map (Fin.castSucc)))

def BuddyTree.unmark : {n : Nat} → BuddyTree n → List (Fin n) → BuddyTree n
  | 0, leaf, _ => leaf
  | n+1, node allocated left right, [] => node false left right
  | n+1, node allocated left right, (⟨0, _⟩ :: path) => 
      node false (left.unmark (path.map (Fin.castSucc))) right
  | n+1, node allocated left right, (⟨i+1, hi⟩ :: path) => 
      node false left (right.unmark (path.map (Fin.castSucc)))

theorem BuddyTree.mark_unmark {n : Nat} (tree : BuddyTree n) (path : List (Fin n)) :
  (tree.mark path).unmark path = tree.unmark path := by
  induction tree generalizing path with
  | leaf => cases path <;> rfl
  | node allocated left right ihl ihr =>
      cases path with
      | nil => rfl
      | cons head tail =>
          cases head with | mk val hval =>
          cases val
          · simp [mark, unmark]
            apply congrArg
            exact ihl _
          · simp [mark, unmark]
            apply congrArg
            apply congrArg
            exact ihr _

structure RefCount where
  count : Nat
  valid : 0 < count

def RefCount.init : RefCount :=
  { count := 1, valid := Nat.zero_lt_one }

def RefCount.inc (rc : RefCount) : RefCount :=
  { count := rc.count + 1, valid := Nat.zero_lt_succ _ }

def RefCount.dec (rc : RefCount) : Option RefCount :=
  match rc.count with
  | 1 => none
  | n + 2 => some { count := n + 1, valid := Nat.zero_lt_succ _ }

theorem RefCount.inc_dec (rc : RefCount) :
  ∃ rc', rc.inc.dec = some rc' ∧ rc'.count = rc.count := by
  unfold inc dec
  cases h : rc.count
  · exact absurd (rc.valid) (Nat.not_lt_zero 0)
  · exists { count := _, valid := _ }
    constructor
    · simp
    · simp

theorem RefCount.always_positive (rc : RefCount) : 0 < rc.count :=
  rc.valid

inductive MemorySafetyProperty where
  | NoDoubleFree : MemorySafetyProperty
  | NoUseAfterFree : MemorySafetyProperty
  | NoMemoryLeak : MemorySafetyProperty
  | BoundsChecked : MemorySafetyProperty

structure SafeMemoryOp where
  operation : AllocatorState → AllocatorState
  preservesInvariant : ∀ state, state.offsetValid → (operation state).offsetValid

def SafeMemoryOp.noop : SafeMemoryOp :=
  { operation := id
  , preservesInvariant := fun _ h => h }

theorem SafeMemoryOp.composition (op1 op2 : SafeMemoryOp) :
  ∃ op3, ∀ state, op3.operation state = op2.operation (op1.operation state) := by
  exists { operation := op2.operation ∘ op1.operation
         , preservesInvariant := fun state h => 
             op2.preservesInvariant (op1.operation state) (op1.preservesInvariant state h) }
  intro state
  rfl

inductive AllocatorType where
  | ArenaAlloc : AllocatorType
  | SlabAlloc : AllocatorType
  | PoolAlloc : AllocatorType
  | BuddyAlloc : AllocatorType
  | LockFreeAlloc : AllocatorType

structure AllocatorSpec where
  allocType : AllocatorType
  threadSafe : Bool
  lockFree : Bool
  constantTime : Bool
  fragmentationBounded : Bool

def arenaSpec : AllocatorSpec :=
  { allocType := AllocatorType.ArenaAlloc
  , threadSafe := false
  , lockFree := false
  , constantTime := true
  , fragmentationBounded := true }

def slabSpec : AllocatorSpec :=
  { allocType := AllocatorType.SlabAlloc
  , threadSafe := true
  , lockFree := false
  , constantTime := true
  , fragmentationBounded := true }

def poolSpec : AllocatorSpec :=
  { allocType := AllocatorType.PoolAlloc
  , threadSafe := true
  , lockFree := false
  , constantTime := true
  , fragmentationBounded := true }

def buddySpec : AllocatorSpec :=
  { allocType := AllocatorType.BuddyAlloc
  , threadSafe := true
  , lockFree := false
  , constantTime := false
  , fragmentationBounded := true }

def lockFreeSpec : AllocatorSpec :=
  { allocType := AllocatorType.LockFreeAlloc
  , threadSafe := true
  , lockFree := true
  , constantTime := false
  , fragmentationBounded := false }

inductive ConcurrentAccessPattern where
  | SingleThreaded : ConcurrentAccessPattern
  | MultiThreadedLocked : ConcurrentAccessPattern
  | MultiThreadedLockFree : ConcurrentAccessPattern

def allocatorAccessPattern (spec : AllocatorSpec) : ConcurrentAccessPattern :=
  if !spec.threadSafe then ConcurrentAccessPattern.SingleThreaded
  else if spec.lockFree then ConcurrentAccessPattern.MultiThreadedLockFree
  else ConcurrentAccessPattern.MultiThreadedLocked

theorem threadSafe_implies_concurrent (spec : AllocatorSpec) (h : spec.threadSafe = true) :
  allocatorAccessPattern spec ≠ ConcurrentAccessPattern.SingleThreaded := by
  unfold allocatorAccessPattern
  rw [h]
  simp
  intro hcontra
  cases spec.lockFree <;> contradiction

end MemoryVerification
