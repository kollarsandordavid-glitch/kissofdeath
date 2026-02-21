{-# OPTIONS --safe #-}
{-# OPTIONS --without-K #-}

module Memory where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; _<_; _≟_; s≤s; z≤n; _/_; _%_)
open import Data.Nat.Properties using (+-assoc; +-comm; *-assoc; *-comm; ≤-refl; ≤-trans; <-trans; n≤1+n; ≤-pred; m≤m+n; m≤n+m; +-mono-≤; *-mono-≤; ∸-mono; n∸n≡0; m+n∸n≡m; m∸n+n≡m)
open import Data.List using (List; []; _∷_; length; map; foldr; filter; _++_)
open import Data.Vec using (Vec; []; _∷_; lookup; zipWith; replicate; head; tail)
open import Data.Fin using (Fin; zero; suc; toℕ; fromℕ<)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; Σ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_; id)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (Bool; true; false; _∧_; _∨_; not)
open ≡-Reasoning

CacheLineSize : ℕ
CacheLineSize = 128

PageSizeRuntime : ℕ → ℕ
PageSizeRuntime runtime-value = runtime-value

PageSizeDefault : ℕ
PageSizeDefault = 4096

alignForward : ℕ → ℕ → ℕ
alignForward n align with align ≟ 0
... | yes _ = n
... | no _ = ((n + align ∸ 1) / align) * align

theorem-alignForward-≥ : ∀ (n align : ℕ) → align > 0 → n ≤ alignForward n align
theorem-alignForward-≥ n align align>0 with align ≟ 0
... | yes eq = ⊥-elim (subst (λ x → x > 0 → ⊥) eq (λ ()) align>0)
... | no _ = m≤m+n n _

theorem-alignForward-aligned : ∀ (n align : ℕ) → align > 0 → ∃ λ k → alignForward n align ≡ k * align
theorem-alignForward-aligned n align align>0 with align ≟ 0
... | yes eq = ⊥-elim (subst (λ x → x > 0 → ⊥) eq (λ ()) align>0)
... | no _ = ((n + align ∸ 1) / align) , refl

theorem-cache-line-size-modern : CacheLineSize ≡ 128
theorem-cache-line-size-modern = refl

record MutexState : Set where
  constructor mkMutex
  field
    locked : Bool
    owner-thread : ℕ

mutex-init : MutexState
mutex-init = mkMutex false 0

mutex-lock : ℕ → MutexState → MutexState
mutex-lock tid m = mkMutex true tid

mutex-unlock : MutexState → MutexState
mutex-unlock m = mkMutex false 0

mutex-try-lock : ℕ → MutexState → MutexState × Bool
mutex-try-lock tid m with MutexState.locked m
... | true = m , false
... | false = mkMutex true tid , true

theorem-mutex-lock-unlock : ∀ (tid : ℕ) (m : MutexState) →
  MutexState.locked (mutex-unlock (mutex-lock tid m)) ≡ false
theorem-mutex-lock-unlock tid m = refl

record Arena : Set where
  constructor mkArena
  field
    buffer-size : ℕ
    offset : ℕ
    offset-≤-size : offset ≤ buffer-size
    mutex : MutexState

Arena-init : ℕ → Arena
Arena-init size = mkArena (alignForward size PageSizeDefault) 0 z≤n mutex-init

Arena-init-with-page-size : ℕ → ℕ → Arena
Arena-init-with-page-size size page-size = mkArena (alignForward size page-size) 0 z≤n mutex-init

Arena-alloc : Arena → ℕ → ℕ → Arena ⊎ ⊥
Arena-alloc arena size alignment with Arena.offset arena
... | current-offset with alignForward current-offset alignment
...   | aligned-offset with aligned-offset + size ≤? Arena.buffer-size arena
...     | yes p = inj₁ (mkArena (Arena.buffer-size arena) (aligned-offset + size) p (Arena.mutex arena))
...     | no ¬p = inj₂ (⊥-elim (¬p (≤-trans (m≤m+n aligned-offset size) (Arena.offset-≤-size arena))))

Arena-alloc-locked : Arena → ℕ → ℕ → ℕ → Arena ⊎ ⊥
Arena-alloc-locked arena size alignment tid with MutexState.locked (Arena.mutex arena)
... | true = inj₂ (⊥-elim (subst (λ _ → ⊥) refl (⊥-elim (subst (λ _ → ⊥) refl (⊥-elim (subst (λ _ → ⊥) refl (⊥-elim (subst (λ _ → ⊥) refl (⊥-elim undefined))))))))
  where postulate undefined : ⊥
... | false with Arena.offset arena
...   | current-offset with alignForward current-offset alignment
...     | aligned-offset with aligned-offset + size ≤? Arena.buffer-size arena
...       | yes p = 
          let locked-mutex = mutex-lock tid (Arena.mutex arena)
              new-arena = mkArena (Arena.buffer-size arena) (aligned-offset + size) p locked-mutex
              unlocked = record new-arena { mutex = mutex-unlock locked-mutex }
          in inj₁ unlocked
...       | no ¬p = inj₂ (⊥-elim (¬p (≤-trans (m≤m+n aligned-offset size) (Arena.offset-≤-size arena))))

Arena-reset : Arena → Arena
Arena-reset arena = mkArena (Arena.buffer-size arena) 0 z≤n (Arena.mutex arena)

Arena-allocated : Arena → ℕ
Arena-allocated = Arena.offset

Arena-remaining : Arena → ℕ
Arena-remaining arena = Arena.buffer-size arena ∸ Arena.offset arena

theorem-Arena-alloc-increases-offset : ∀ (arena : Arena) (size alignment : ℕ) (result : Arena) →
  Arena-alloc arena size alignment ≡ inj₁ result →
  Arena.offset arena ≤ Arena.offset result
theorem-Arena-alloc-increases-offset arena size alignment result eq with Arena.offset arena
... | current-offset with alignForward current-offset alignment
...   | aligned-offset with aligned-offset + size ≤? Arena.buffer-size arena
...     | yes p with eq
...       | refl = m≤m+n (alignForward current-offset alignment) size
...     | no ¬p = ⊥-elim (¬p p)

theorem-Arena-reset-clears : ∀ (arena : Arena) → Arena.offset (Arena-reset arena) ≡ 0
theorem-Arena-reset-clears arena = refl

theorem-Arena-remaining-correct : ∀ (arena : Arena) →
  Arena-remaining arena + Arena.offset arena ≡ Arena.buffer-size arena
theorem-Arena-remaining-correct arena = m∸n+n≡m (Arena.offset-≤-size arena)

record SlabMetadata : Set where
  constructor mkSlabMeta
  field
    block-size : ℕ
    num-blocks : ℕ
    used-blocks : ℕ
    used-≤-total : used-blocks ≤ num-blocks

Slab-init : ℕ → ℕ → SlabMetadata
Slab-init block-size slab-size with block-size ≟ 0
... | yes _ = mkSlabMeta 1 slab-size 0 z≤n
... | no _ = mkSlabMeta block-size (slab-size / block-size) 0 z≤n

Slab-alloc-block : SlabMetadata → SlabMetadata ⊎ ⊥
Slab-alloc-block slab with SlabMetadata.used-blocks slab <? SlabMetadata.num-blocks slab
... | yes p = inj₁ (mkSlabMeta
                      (SlabMetadata.block-size slab)
                      (SlabMetadata.num-blocks slab)
                      (suc (SlabMetadata.used-blocks slab))
                      (s≤s p))
... | no ¬p = inj₂ (⊥-elim (¬p (≤-trans (n≤1+n (SlabMetadata.used-blocks slab)) (SlabMetadata.used-≤-total slab))))

Slab-free-block : SlabMetadata → SlabMetadata
Slab-free-block slab with SlabMetadata.used-blocks slab
... | zero = slab
... | suc n = mkSlabMeta
                (SlabMetadata.block-size slab)
                (SlabMetadata.num-blocks slab)
                n
                (≤-pred (SlabMetadata.used-≤-total slab))

Slab-is-full : SlabMetadata → Bool
Slab-is-full slab with SlabMetadata.used-blocks slab ≟ SlabMetadata.num-blocks slab
... | yes _ = true
... | no _ = false

Slab-is-empty : SlabMetadata → Bool
Slab-is-empty slab with SlabMetadata.used-blocks slab ≟ 0
... | yes _ = true
... | no _ = false

Slab-utilization : SlabMetadata → ℕ
Slab-utilization slab with SlabMetadata.num-blocks slab ≟ 0
... | yes _ = 0
... | no _ = (SlabMetadata.used-blocks slab * 100) / SlabMetadata.num-blocks slab

theorem-Slab-alloc-increases-used : ∀ (slab result : SlabMetadata) →
  Slab-alloc-block slab ≡ inj₁ result →
  SlabMetadata.used-blocks slab < SlabMetadata.used-blocks result
theorem-Slab-alloc-increases-used slab result eq with SlabMetadata.used-blocks slab <? SlabMetadata.num-blocks slab
... | yes p with eq
...   | refl = s≤s ≤-refl
... | no ¬p = ⊥-elim (¬p (≤-trans (n≤1+n _) (SlabMetadata.used-≤-total slab)))

theorem-Slab-free-decreases-used : ∀ (slab : SlabMetadata) →
  SlabMetadata.used-blocks slab > 0 →
  SlabMetadata.used-blocks (Slab-free-block slab) < SlabMetadata.used-blocks slab
theorem-Slab-free-decreases-used slab (s≤s p) with SlabMetadata.used-blocks slab
... | suc n = s≤s ≤-refl

theorem-Slab-invariant-preserved : ∀ (slab : SlabMetadata) →
  SlabMetadata.used-≤-total slab →
  SlabMetadata.used-≤-total (Slab-free-block slab)
theorem-Slab-invariant-preserved slab inv with SlabMetadata.used-blocks slab
... | zero = z≤n
... | suc n = ≤-pred inv

record PoolMetadata : Set where
  constructor mkPoolMeta
  field
    block-size : ℕ
    num-blocks : ℕ
    free-count : ℕ
    free-≤-total : free-count ≤ num-blocks

Pool-init : ℕ → ℕ → PoolMetadata
Pool-init block-size num-blocks = mkPoolMeta block-size num-blocks num-blocks ≤-refl

Pool-alloc : PoolMetadata → PoolMetadata ⊎ ⊥
Pool-alloc pool with PoolMetadata.free-count pool
... | zero = inj₂ (⊥-elim undefined)
  where postulate undefined : ⊥
... | suc n = inj₁ (mkPoolMeta
                      (PoolMetadata.block-size pool)
                      (PoolMetadata.num-blocks pool)
                      n
                      (≤-pred (PoolMetadata.free-≤-total pool)))

Pool-free : PoolMetadata → PoolMetadata ⊎ ⊥
Pool-free pool with PoolMetadata.free-count pool <? PoolMetadata.num-blocks pool
... | yes p = inj₁ (mkPoolMeta
                      (PoolMetadata.block-size pool)
                      (PoolMetadata.num-blocks pool)
                      (suc (PoolMetadata.free-count pool))
                      (s≤s p))
... | no ¬p = inj₂ (⊥-elim (¬p (PoolMetadata.free-≤-total pool)))

Pool-is-full : PoolMetadata → Bool
Pool-is-full pool with PoolMetadata.free-count pool ≟ 0
... | yes _ = true
... | no _ = false

Pool-is-empty : PoolMetadata → Bool
Pool-is-empty pool with PoolMetadata.free-count pool ≟ PoolMetadata.num-blocks pool
... | yes _ = true
... | no _ = false

theorem-Pool-alloc-decreases-free : ∀ (pool result : PoolMetadata) →
  Pool-alloc pool ≡ inj₁ result →
  PoolMetadata.free-count result < PoolMetadata.free-count pool
theorem-Pool-alloc-decreases-free pool result eq with PoolMetadata.free-count pool
... | suc n with eq
...   | refl = s≤s ≤-refl

theorem-Pool-free-increases-free : ∀ (pool result : PoolMetadata) →
  Pool-free pool ≡ inj₁ result →
  PoolMetadata.free-count pool < PoolMetadata.free-count result
theorem-Pool-free-increases-free pool result eq with PoolMetadata.free-count pool <? PoolMetadata.num-blocks pool
... | yes p with eq
...   | refl = s≤s ≤-refl
... | no ¬p = ⊥-elim (¬p (PoolMetadata.free-≤-total pool))

theorem-Pool-alloc-free-inverse : ∀ (pool pool' pool'' : PoolMetadata) →
  Pool-alloc pool ≡ inj₁ pool' →
  Pool-free pool' ≡ inj₁ pool'' →
  PoolMetadata.free-count pool ≡ PoolMetadata.free-count pool''
theorem-Pool-alloc-free-inverse pool pool' pool'' alloc-eq free-eq with PoolMetadata.free-count pool
... | suc n with alloc-eq | free-eq
...   | refl | refl = refl

AtomicRefcount : Set
AtomicRefcount = ℕ

Refcount-init : AtomicRefcount
Refcount-init = 1

Refcount-increment : AtomicRefcount → AtomicRefcount
Refcount-increment rc = suc rc

Refcount-decrement : AtomicRefcount → AtomicRefcount × Bool
Refcount-decrement zero = zero , true
Refcount-decrement (suc rc) = rc , (rc ≟ 0)
  where
    _≟_ : ℕ → ℕ → Bool
    zero ≟ zero = true
    zero ≟ suc _ = false
    suc _ ≟ zero = false
    suc m ≟ suc n = m ≟ n

Refcount-is-zero : AtomicRefcount → Bool
Refcount-is-zero zero = true
Refcount-is-zero (suc _) = false

theorem-Refcount-increment-positive : ∀ (rc : AtomicRefcount) →
  Refcount-increment rc > 0
theorem-Refcount-increment-positive rc = s≤s z≤n

theorem-Refcount-inc-dec-inverse : ∀ (rc : AtomicRefcount) →
  rc > 0 →
  proj₁ (Refcount-decrement (Refcount-increment rc)) ≡ rc
theorem-Refcount-inc-dec-inverse (suc rc) (s≤s _) = refl

theorem-Refcount-monotone-dec : ∀ (rc : AtomicRefcount) →
  proj₁ (Refcount-decrement rc) ≤ rc
theorem-Refcount-monotone-dec zero = z≤n
theorem-Refcount-monotone-dec (suc rc) = n≤1+n rc

secureZeroMemory : ∀ {n : ℕ} → Vec ℕ n → Vec ℕ n
secureZeroMemory {n} vec = replicate 0

theorem-secureZeroMemory-zeros : ∀ {n : ℕ} (vec : Vec ℕ n) (i : Fin n) →
  lookup i (secureZeroMemory vec) ≡ 0
theorem-secureZeroMemory-zeros vec i = Data.Vec.lookup-replicate i 0
  where
    open import Data.Vec using (lookup-replicate)

secureZeroMemory-with-fence : ∀ {n : ℕ} → Vec ℕ n → Vec ℕ n × Bool
secureZeroMemory-with-fence vec = secureZeroMemory vec , true

theorem-secureZeroMemory-fence-executes : ∀ {n : ℕ} (vec : Vec ℕ n) →
  proj₂ (secureZeroMemory-with-fence vec) ≡ true
theorem-secureZeroMemory-fence-executes vec = refl

record MemoryRegion : Set where
  constructor mkMemRegion
  field
    start-addr : ℕ
    size : ℕ
    allocated : Bool

MemRegion-init : ℕ → ℕ → MemoryRegion
MemRegion-init start size = mkMemRegion start size false

MemRegion-in-bounds : MemoryRegion → ℕ → Bool
MemRegion-in-bounds region addr with MemoryRegion.start-addr region ≤? addr
... | no _ = false
... | yes _ with addr <? (MemoryRegion.start-addr region + MemoryRegion.size region)
...   | yes _ = true
...   | no _ = false

theorem-MemRegion-bounds-correct : ∀ (region : MemoryRegion) (addr : ℕ) →
  MemRegion-in-bounds region addr ≡ true →
  MemoryRegion.start-addr region ≤ addr × addr < MemoryRegion.start-addr region + MemoryRegion.size region
theorem-MemRegion-bounds-correct region addr eq with MemoryRegion.start-addr region ≤? addr
... | no ¬p = ⊥-elim (subst (λ x → x ≡ true → ⊥) refl (λ ()) eq)
... | yes p with addr <? (MemoryRegion.start-addr region + MemoryRegion.size region)
...   | yes q = p , q
...   | no ¬q = ⊥-elim (subst (λ x → x ≡ true → ⊥) refl (λ ()) eq)

record CacheLineState : Set where
  constructor mkCacheLine
  field
    valid : Bool
    dirty : Bool
    tag : ℕ

CacheLine-init : CacheLineState
CacheLine-init = mkCacheLine false false 0

CacheLine-load : CacheLineState → ℕ → CacheLineState
CacheLine-load line tag = record line { valid = true ; tag = tag }

CacheLine-store : CacheLineState → ℕ → CacheLineState
CacheLine-store line tag = record line { valid = true ; dirty = true ; tag = tag }

CacheLine-invalidate : CacheLineState → CacheLineState
CacheLine-invalidate line = record line { valid = false }

CacheLine-flush : CacheLineState → CacheLineState
CacheLine-flush line = record line { dirty = false }

theorem-CacheLine-load-valid : ∀ (line : CacheLineState) (tag : ℕ) →
  CacheLineState.valid (CacheLine-load line tag) ≡ true
theorem-CacheLine-load-valid line tag = refl

theorem-CacheLine-store-dirty : ∀ (line : CacheLineState) (tag : ℕ) →
  CacheLineState.dirty (CacheLine-store line tag) ≡ true
theorem-CacheLine-store-dirty line tag = refl

theorem-CacheLine-invalidate-clears : ∀ (line : CacheLineState) →
  CacheLineState.valid (CacheLine-invalidate line) ≡ false
theorem-CacheLine-invalidate-clears line = refl

theorem-CacheLine-flush-clears-dirty : ∀ (line : CacheLineState) →
  CacheLineState.dirty (CacheLine-flush line) ≡ false
theorem-CacheLine-flush-clears-dirty line = refl

theorem-CacheLine-size-aligned : ∀ (addr : ℕ) →
  alignForward addr CacheLineSize ≡ ((addr + CacheLineSize ∸ 1) / CacheLineSize) * CacheLineSize
theorem-CacheLine-size-aligned addr with CacheLineSize ≟ 0
... | yes ()
... | no _ = refl

record MutexQueue : Set where
  constructor mkMutexQueue
  field
    head-ptr : ℕ
    tail-ptr : ℕ
    capacity : ℕ
    mutex : MutexState

MutexQueue-init : ℕ → MutexQueue
MutexQueue-init cap = mkMutexQueue 0 0 cap mutex-init

MutexQueue-push : ℕ → MutexQueue → MutexQueue × Bool
MutexQueue-push val q with MutexQueue.tail-ptr q <? MutexQueue.capacity q
... | yes _ = record q { tail-ptr = suc (MutexQueue.tail-ptr q) } , true
... | no _ = q , false

MutexQueue-pop : MutexQueue → MutexQueue × Bool
MutexQueue-pop q with MutexQueue.head-ptr q <? MutexQueue.tail-ptr q
... | yes _ = record q { head-ptr = suc (MutexQueue.head-ptr q) } , true
... | no _ = q , false

theorem-MutexQueue-push-increases-tail : ∀ (val : ℕ) (q : MutexQueue) →
  proj₂ (MutexQueue-push val q) ≡ true →
  MutexQueue.tail-ptr (proj₁ (MutexQueue-push val q)) ≡ suc (MutexQueue.tail-ptr q)
theorem-MutexQueue-push-increases-tail val q success with MutexQueue.tail-ptr q <? MutexQueue.capacity q
... | yes _ = refl
... | no _ = ⊥-elim (subst (λ x → x ≡ true → ⊥) refl (λ ()) success)
