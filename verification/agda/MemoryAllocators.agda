{-# OPTIONS --safe #-}
{-# OPTIONS --without-K #-}

module MemoryAllocators where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; _<_; _≟_; s≤s; z≤n; _≤?_)
open import Data.Nat.Properties using (+-assoc; +-comm; *-assoc; *-comm; ≤-refl; ≤-trans; <-trans; n≤1+n; ≤-pred; m+n∸n≡m; +-mono-≤)
open import Data.List using (List; []; _∷_; length; map; foldr; filter; all)
open import Data.Vec using (Vec; []; _∷_; lookup; _++_; head; tail; splitAt)
open import Data.Fin using (Fin; zero; suc; toℕ; fromℕ<; inject₁; raise)
open import Data.Bool using (Bool; true; false; _∧_; _∨_; not; if_then_else_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; Σ; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_; id; _$_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Level using (Level; _⊔_)
open ≡-Reasoning

PageSize : ℕ
PageSize = 4096

record MemoryBlock : Set where
  constructor mkMemoryBlock
  field
    base : ℕ
    size : ℕ
    allocated : Bool

open MemoryBlock

data AllocatorState : Set where
  mkAllocatorState : (total-size : ℕ) → (offset : ℕ) → (blocks : List MemoryBlock) → AllocatorState

get-total-size : AllocatorState → ℕ
get-total-size (mkAllocatorState ts _ _) = ts

get-offset : AllocatorState → ℕ
get-offset (mkAllocatorState _ off _) = off

get-blocks : AllocatorState → List MemoryBlock
get-blocks (mkAllocatorState _ _ bs) = bs

alignForward : ℕ → ℕ → ℕ
alignForward value alignment = 
  let remainder = value ∸ (value ∸ alignment) * (value ∸ alignment)
  in if remainder ≟ 0 then value else value + (alignment ∸ remainder)

lemma-alignForward-geq : ∀ (value alignment : ℕ) → value ≤ alignForward value alignment
lemma-alignForward-geq value zero = ≤-refl
lemma-alignForward-geq value (suc alignment) with value ∸ (value ∸ suc alignment) * (value ∸ suc alignment) ≟ 0
... | yes p = ≤-refl
... | no ¬p = n≤1+n value

lemma-alignForward-multiple : ∀ (value alignment : ℕ) → ∃[ k ] (alignForward value alignment ≡ k * alignment)
lemma-alignForward-multiple value zero = zero , refl
lemma-alignForward-multiple value (suc alignment) with value ∸ (value ∸ suc alignment) * (value ∸ suc alignment) ≟ 0
... | yes p = value ∸ suc alignment , p
... | no ¬p = suc (value ∸ suc alignment) , refl

record Arena : Set where
  constructor mkArena
  field
    buffer-size : ℕ
    offset : ℕ
    offset-valid : offset ≤ buffer-size

open Arena

arena-init : (size : ℕ) → Arena
arena-init size = mkArena (alignForward size PageSize) 0 z≤n

arena-alloc : Arena → ℕ → ℕ → Maybe (ℕ × Arena)
arena-alloc arena size alignment with size ≟ 0
... | yes p = just (0 , arena)
... | no ¬p = 
  let current-offset = offset arena
      aligned-offset = alignForward current-offset alignment
      end = aligned-offset + size
  in if end ≤? buffer-size arena 
     then just (aligned-offset , record arena { offset = end ; offset-valid = ≤-trans (n≤1+n end) (offset-valid arena) })
     else nothing

theorem-arena-alloc-preserves-invariant : ∀ (arena : Arena) (size alignment : ℕ) →
  ∀ (result : ℕ × Arena) →
  arena-alloc arena size alignment ≡ just result →
  offset (proj₂ result) ≤ buffer-size (proj₂ result)
theorem-arena-alloc-preserves-invariant arena size alignment result eq with size ≟ 0
... | yes p rewrite eq = offset-valid arena
... | no ¬p with (alignForward (offset arena) alignment + size) ≤? buffer-size arena
...   | yes q rewrite eq = ≤-trans (n≤1+n (alignForward (offset arena) alignment + size)) (offset-valid arena)
...   | no ¬q = ⊥-elim (case eq of λ ())

arena-reset : Arena → Arena
arena-reset arena = record arena { offset = 0 ; offset-valid = z≤n }

theorem-arena-reset-preserves-buffer : ∀ (arena : Arena) →
  buffer-size (arena-reset arena) ≡ buffer-size arena
theorem-arena-reset-preserves-buffer arena = refl

theorem-arena-reset-zeros-offset : ∀ (arena : Arena) →
  offset (arena-reset arena) ≡ 0
theorem-arena-reset-zeros-offset arena = refl

arena-allocated : Arena → ℕ
arena-allocated arena = offset arena

arena-remaining : Arena → ℕ
arena-remaining arena = buffer-size arena ∸ offset arena

theorem-arena-allocated-plus-remaining : ∀ (arena : Arena) →
  arena-allocated arena + arena-remaining arena ≡ buffer-size arena
theorem-arena-allocated-plus-remaining arena = m+n∸n≡m (buffer-size arena) (offset arena) (offset-valid arena)

data SlabState : ℕ → Set where
  mkSlabState : (num-blocks : ℕ) → (block-size : ℕ) → (free-blocks : List (Fin num-blocks)) → SlabState num-blocks

slab-num-blocks : ∀ {n} → SlabState n → ℕ
slab-num-blocks {n} _ = n

slab-block-size : ∀ {n} → SlabState n → ℕ
slab-block-size (mkSlabState _ bs _) = bs

slab-free-blocks : ∀ {n} → SlabState n → List (Fin n)
slab-free-blocks (mkSlabState _ _ fb) = fb

slab-init : (num-blocks : ℕ) → (block-size : ℕ) → SlabState num-blocks
slab-init zero block-size = mkSlabState zero block-size []
slab-init (suc num-blocks) block-size = mkSlabState (suc num-blocks) block-size (build-free-list (suc num-blocks))
  where
    build-free-list : (n : ℕ) → List (Fin n)
    build-free-list zero = []
    build-free-list (suc m) = zero ∷ map suc (build-free-list m)

slab-alloc : ∀ {n} → SlabState n → Maybe (Fin n × SlabState n)
slab-alloc (mkSlabState num-blocks block-size []) = nothing
slab-alloc (mkSlabState num-blocks block-size (x ∷ xs)) = just (x , mkSlabState num-blocks block-size xs)

theorem-slab-alloc-decreases-free : ∀ {n} (slab : SlabState n) (result : Fin n × SlabState n) →
  slab-alloc slab ≡ just result →
  length (slab-free-blocks (proj₂ result)) ≡ length (slab-free-blocks slab) ∸ 1
theorem-slab-alloc-decreases-free (mkSlabState num-blocks block-size []) result ()
theorem-slab-alloc-decreases-free (mkSlabState num-blocks block-size (x ∷ xs)) result refl = refl

slab-free : ∀ {n} → SlabState n → Fin n → SlabState n
slab-free (mkSlabState num-blocks block-size free-blocks) block-idx = 
  mkSlabState num-blocks block-size (block-idx ∷ free-blocks)

theorem-slab-free-increases-free : ∀ {n} (slab : SlabState n) (block : Fin n) →
  length (slab-free-blocks (slab-free slab block)) ≡ suc (length (slab-free-blocks slab))
theorem-slab-free-increases-free (mkSlabState num-blocks block-size free-blocks) block = refl

theorem-slab-alloc-free-identity : ∀ {n} (slab : SlabState n) (result : Fin n × SlabState n) →
  slab-alloc slab ≡ just result →
  slab-free-blocks (slab-free (proj₂ result) (proj₁ result)) ≡ slab-free-blocks slab
theorem-slab-alloc-free-identity (mkSlabState num-blocks block-size []) result ()
theorem-slab-alloc-free-identity (mkSlabState num-blocks block-size (x ∷ xs)) result refl = refl

data PoolState : ℕ → Set where
  mkPoolState : (num-blocks : ℕ) → (block-size : ℕ) → (free-list-head : Maybe (Fin num-blocks)) → (used-count : ℕ) → PoolState num-blocks

pool-init : (num-blocks : ℕ) → (block-size : ℕ) → PoolState num-blocks
pool-init zero block-size = mkPoolState zero block-size nothing 0
pool-init (suc n) block-size = mkPoolState (suc n) block-size (just zero) 0

pool-alloc : ∀ {n} → PoolState n → Maybe (Fin n × PoolState n)
pool-alloc (mkPoolState num-blocks block-size nothing used) = nothing
pool-alloc (mkPoolState num-blocks block-size (just head-idx) used) = 
  just (head-idx , mkPoolState num-blocks block-size nothing (suc used))

theorem-pool-alloc-increases-used : ∀ {n} (pool : PoolState n) (result : Fin n × PoolState n) →
  pool-alloc pool ≡ just result →
  ∃[ used ] (proj₂ result ≡ mkPoolState n (proj₁ (proj₁ (pool-state-parts pool))) nothing (suc used))
  where
    pool-state-parts : ∀ {n} → PoolState n → (ℕ × ℕ × Maybe (Fin n) × ℕ)
    pool-state-parts (mkPoolState nb bs fh uc) = (bs , nb , fh , uc)
theorem-pool-alloc-increases-used (mkPoolState num-blocks block-size nothing used) result ()
theorem-pool-alloc-increases-used (mkPoolState num-blocks block-size (just head-idx) used) result refl = used , refl

pool-free : ∀ {n} → PoolState n → Fin n → PoolState n
pool-free (mkPoolState num-blocks block-size free-list-head zero) block-idx = 
  mkPoolState num-blocks block-size (just block-idx) zero
pool-free (mkPoolState num-blocks block-size free-list-head (suc used)) block-idx = 
  mkPoolState num-blocks block-size (just block-idx) used

theorem-pool-free-decreases-used : ∀ {n} (pool : PoolState n) (block : Fin n) (used : ℕ) →
  pool ≡ mkPoolState n (pool-block-size pool) (pool-free-head pool) (suc used) →
  pool-used-count (pool-free pool block) ≡ used
  where
    pool-block-size : ∀ {n} → PoolState n → ℕ
    pool-block-size (mkPoolState _ bs _ _) = bs
    pool-free-head : ∀ {n} → PoolState n → Maybe (Fin n)
    pool-free-head (mkPoolState _ _ fh _) = fh
    pool-used-count : ∀ {n} → PoolState n → ℕ
    pool-used-count (mkPoolState _ _ _ uc) = uc
theorem-pool-free-decreases-used (mkPoolState n bs fh (suc used)) block used refl = refl

data BuddyTree : ℕ → Set where
  leaf : BuddyTree 0
  node : ∀ {n} → Bool → BuddyTree n → BuddyTree n → BuddyTree (suc n)

buddy-tree-height : ∀ {n} → BuddyTree n → ℕ
buddy-tree-height {n} _ = n

buddy-tree-mark : ∀ {n} → BuddyTree n → List (Fin n) → BuddyTree n
buddy-tree-mark tree [] = tree
buddy-tree-mark leaf (x ∷ path) = leaf
buddy-tree-mark (node allocated left right) (zero ∷ path) = node true (buddy-tree-mark left path) right
buddy-tree-mark (node allocated left right) (suc idx ∷ path) = node true left (buddy-tree-mark right path)

buddy-tree-unmark : ∀ {n} → BuddyTree n → List (Fin n) → BuddyTree n
buddy-tree-unmark tree [] = tree
buddy-tree-unmark leaf (x ∷ path) = leaf
buddy-tree-unmark (node allocated left right) (zero ∷ path) = 
  let new-left = buddy-tree-unmark left path
  in node false new-left right
buddy-tree-unmark (node allocated left right) (suc idx ∷ path) = 
  let new-right = buddy-tree-unmark right path
  in node false left new-right

theorem-buddy-tree-mark-unmark : ∀ {n} (tree : BuddyTree n) (path : List (Fin n)) →
  buddy-tree-unmark (buddy-tree-mark tree path) path ≡ buddy-tree-unmark tree path
theorem-buddy-tree-mark-unmark tree [] = refl
theorem-buddy-tree-mark-unmark leaf (x ∷ path) = refl
theorem-buddy-tree-mark-unmark (node allocated left right) (zero ∷ path) = cong (λ l → node false l right) (theorem-buddy-tree-mark-unmark left path)
theorem-buddy-tree-mark-unmark (node allocated left right) (suc idx ∷ path) = cong (λ r → node false left r) (theorem-buddy-tree-mark-unmark right path)

record RefCount : Set where
  constructor mkRefCount
  field
    count : ℕ
    valid : 0 < count

open RefCount

refcount-init : RefCount
refcount-init = mkRefCount 1 (s≤s z≤n)

refcount-inc : RefCount → RefCount
refcount-inc rc = mkRefCount (suc (count rc)) (s≤s z≤n)

refcount-dec : RefCount → Maybe RefCount
refcount-dec (mkRefCount (suc zero) _) = nothing
refcount-dec (mkRefCount (suc (suc n)) _) = just (mkRefCount (suc n) (s≤s z≤n))

theorem-refcount-inc-dec : ∀ (rc : RefCount) →
  ∃[ rc' ] (refcount-dec (refcount-inc rc) ≡ just rc' ∧ count rc' ≡ count rc)
theorem-refcount-inc-dec (mkRefCount (suc n) valid) = mkRefCount (suc n) valid , refl , refl

theorem-refcount-always-positive : ∀ (rc : RefCount) → 0 < count rc
theorem-refcount-always-positive rc = valid rc

data MemorySafetyProperty : Set where
  NoDoubleFree : MemorySafetyProperty
  NoUseAfterFree : MemorySafetyProperty
  NoMemoryLeak : MemorySafetyProperty
  BoundsChecked : MemorySafetyProperty

record SafeMemoryOp : Set where
  constructor mkSafeMemoryOp
  field
    operation : AllocatorState → AllocatorState
    preserves-invariant : ∀ (state : AllocatorState) → get-offset state ≤ get-total-size state → get-offset (operation state) ≤ get-total-size (operation state)

safe-noop : SafeMemoryOp
safe-noop = mkSafeMemoryOp id (λ state inv → inv)

theorem-safe-composition : ∀ (op1 op2 : SafeMemoryOp) →
  ∃[ op3 ] (∀ (state : AllocatorState) → SafeMemoryOp.operation op3 state ≡ SafeMemoryOp.operation op2 (SafeMemoryOp.operation op1 state))
theorem-safe-composition op1 op2 = 
  mkSafeMemoryOp (SafeMemoryOp.operation op2 ∘ SafeMemoryOp.operation op1) 
    (λ state inv → SafeMemoryOp.preserves-invariant op2 (SafeMemoryOp.operation op1 state) (SafeMemoryOp.preserves-invariant op1 state inv)) , 
  λ state → refl

data AllocatorType : Set where
  ArenaAlloc : AllocatorType
  SlabAlloc : AllocatorType
  PoolAlloc : AllocatorType
  BuddyAlloc : AllocatorType
  LockFreeAlloc : AllocatorType

record AllocatorSpec : Set where
  constructor mkAllocatorSpec
  field
    alloc-type : AllocatorType
    thread-safe : Bool
    lock-free : Bool
    constant-time : Bool
    fragmentation-bounded : Bool

arena-spec : AllocatorSpec
arena-spec = mkAllocatorSpec ArenaAlloc false false true true

slab-spec : AllocatorSpec
slab-spec = mkAllocatorSpec SlabAlloc true false true true

pool-spec : AllocatorSpec
pool-spec = mkAllocatorSpec PoolAlloc true false true true

buddy-spec : AllocatorSpec
buddy-spec = mkAllocatorSpec BuddyAlloc true false false true

lockfree-spec : AllocatorSpec
lockfree-spec = mkAllocatorSpec LockFreeAlloc true true false false

theorem-allocator-spec-complete : ∀ (spec : AllocatorSpec) →
  ∃[ t ] (AllocatorSpec.alloc-type spec ≡ t)
theorem-allocator-spec-complete spec = AllocatorSpec.alloc-type spec , refl

data ConcurrentAccessPattern : Set where
  SingleThreaded : ConcurrentAccessPattern
  MultiThreadedLocked : ConcurrentAccessPattern
  MultiThreadedLockFree : ConcurrentAccessPattern

allocator-access-pattern : AllocatorSpec → ConcurrentAccessPattern
allocator-access-pattern spec with AllocatorSpec.thread-safe spec
... | false = SingleThreaded
... | true with AllocatorSpec.lock-free spec
...   | false = MultiThreadedLocked
...   | true = MultiThreadedLockFree

theorem-thread-safe-implies-concurrent : ∀ (spec : AllocatorSpec) →
  AllocatorSpec.thread-safe spec ≡ true →
  allocator-access-pattern spec ≢ SingleThreaded
theorem-thread-safe-implies-concurrent spec ts-true with AllocatorSpec.thread-safe spec
... | false = λ ()
... | true with AllocatorSpec.lock-free spec
...   | false = λ ()
...   | true = λ ()
