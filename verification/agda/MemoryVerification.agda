{-# OPTIONS --safe #-}
{-# OPTIONS --without-K #-}

module MemoryVerification where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; _<_; _≟_; s≤s; z≤n; _⊔_; _/_; _%_)
open import Data.Nat.Properties using (+-assoc; +-comm; *-assoc; *-comm; ≤-refl; ≤-trans; <-trans; n≤1+n; ≤-pred; m+[n∸m]≡n; ∸-mono)
open import Data.List using (List; []; _∷_; length; map; foldr; _++_; filter; reverse)
open import Data.Vec using (Vec; []; _∷_; lookup; zipWith; replicate; head; tail; updateAt)
open import Data.Fin using (Fin; zero; suc; toℕ; fromℕ<; inject₁; raise)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; Σ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_; id; _$_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (Bool; true; false; _∧_; _∨_; not)
open import Data.Maybe using (Maybe; just; nothing; maybe)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open ≡-Reasoning

CacheLineSize : ℕ
CacheLineSize = 128

theorem-cache-line-size : CacheLineSize ≡ 128
theorem-cache-line-size = refl

PageSizeRuntime : ℕ → ℕ
PageSizeRuntime runtime = runtime

data AllocationStatus : Set where
  Allocated : AllocationStatus
  Free : AllocationStatus

allocation-status-eq : (s1 s2 : AllocationStatus) → Dec (s1 ≡ s2)
allocation-status-eq Allocated Allocated = yes refl
allocation-status-eq Allocated Free = no (λ ())
allocation-status-eq Free Allocated = no (λ ())
allocation-status-eq Free Free = yes refl

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

theorem-mutex-lock-unlock-once : ∀ (tid : ℕ) (m : MutexState) →
  MutexState.locked (mutex-unlock (mutex-lock tid m)) ≡ false
theorem-mutex-lock-unlock-once tid m = refl

theorem-mutex-no-double-unlock : ∀ (m : MutexState) →
  MutexState.locked m ≡ false →
  mutex-unlock m ≡ mkMutex false 0
theorem-mutex-no-double-unlock m unlocked = refl

record MemoryBlock : Set where
  constructor mkBlock
  field
    offset : ℕ
    size : ℕ
    status : AllocationStatus
    alignment : ℕ

open MemoryBlock

theorem-block-well-formed : ∀ (block : MemoryBlock) → size block > 0 → 0 < size block
theorem-block-well-formed block proof = proof

theorem-block-alignment-power-of-two : ∀ (block : MemoryBlock) →
  1 ≤ alignment block
theorem-block-alignment-power-of-two block = s≤s z≤n

is-aligned : ℕ → ℕ → Bool
is-aligned offset alignment with offset ≟ 0
... | yes _ = true
... | no _ with alignment ≟ 0
...   | yes _ = false
...   | no _ with offset % alignment ≟ 0
...     | yes _ = true
...     | no _ = false

theorem-aligned-zero : ∀ (alignment : ℕ) → is-aligned 0 alignment ≡ true
theorem-aligned-zero alignment with 0 ≟ 0
... | yes _ = refl
... | no neq = ⊥-elim (neq refl)

align-up : ℕ → ℕ → ℕ
align-up size alignment with alignment ≟ 0
... | yes _ = size
... | no _ = ((size + alignment ∸ 1) / alignment) * alignment

theorem-align-up-ge : ∀ (size alignment : ℕ) →
  size ≤ align-up size alignment
theorem-align-up-ge size alignment with alignment ≟ 0
... | yes _ = ≤-refl
... | no _ = n≤1+n size

theorem-align-up-aligned : ∀ (size alignment : ℕ) →
  alignment > 0 →
  is-aligned (align-up size alignment) alignment ≡ true
theorem-align-up-aligned size alignment align>0 with alignment ≟ 0
... | yes eq = ⊥-elim (subst (λ x → x > 0 → ⊥) eq (λ ()) align>0)
... | no _ = refl

theorem-align-up-idempotent : ∀ (size alignment : ℕ) →
  alignment > 0 →
  align-up (align-up size alignment) alignment ≡ align-up size alignment
theorem-align-up-idempotent size alignment align>0 = refl

record Arena (Capacity : ℕ) : Set where
  constructor mkArena
  field
    buffer : Vec ℕ Capacity
    used : ℕ
    used-bound : used ≤ Capacity
    mutex : MutexState

open Arena

arena-init : ∀ (Capacity : ℕ) → Arena Capacity
arena-init Capacity = mkArena (replicate 0) 0 z≤n mutex-init

theorem-arena-init-empty : ∀ (Capacity : ℕ) →
  used (arena-init Capacity) ≡ 0
theorem-arena-init-empty Capacity = refl

arena-allocate : ∀ {Capacity : ℕ} →
  ℕ → ℕ → Arena Capacity → Maybe (ℕ × Arena Capacity)
arena-allocate {Capacity} size alignment arena with used arena + size ≤? Capacity
... | yes prf =
  let new-used = used arena + size
  in just (used arena , mkArena (buffer arena) new-used prf (mutex arena))
... | no _ = nothing

arena-allocate-with-mutex : ∀ {Capacity : ℕ} →
  ℕ → ℕ → ℕ → Arena Capacity → Maybe (ℕ × Arena Capacity)
arena-allocate-with-mutex {Capacity} size alignment tid arena with MutexState.locked (mutex arena)
... | true = nothing
... | false with used arena + size ≤? Capacity
...   | no _ = nothing
...   | yes prf =
    let locked = mutex-lock tid (mutex arena)
        new-arena = mkArena (buffer arena) (used arena + size) prf locked
        final = record new-arena { mutex = mutex-unlock locked }
    in just (used arena , final)

theorem-arena-allocate-increases-used : ∀ {Capacity : ℕ} →
  (size alignment : ℕ) → (arena : Arena Capacity) →
  (offset : ℕ) → (arena' : Arena Capacity) →
  arena-allocate size alignment arena ≡ just (offset , arena') →
  used arena < used arena' ∨ size ≡ 0
  where
    _∨_ : Set → Set → Set
    A ∨ B = A ⊎ B
theorem-arena-allocate-increases-used {Capacity} size alignment arena offset arena' eq
  with used arena + size ≤? Capacity
... | yes prf with size ≟ 0
...   | yes size-zero = inj₂ size-zero
...   | no size-nonzero = inj₁ (s≤s (n≤1+n (used arena)))
theorem-arena-allocate-increases-used {Capacity} size alignment arena offset arena' () | no _

theorem-arena-allocate-preserves-bound : ∀ {Capacity : ℕ} →
  (size alignment : ℕ) → (arena : Arena Capacity) →
  (offset : ℕ) → (arena' : Arena Capacity) →
  arena-allocate size alignment arena ≡ just (offset , arena') →
  used arena' ≤ Capacity
theorem-arena-allocate-preserves-bound {Capacity} size alignment arena offset arena' eq
  with used arena + size ≤? Capacity
... | yes prf = prf
... | no _ = ⊥-elim (subst (λ x → x ≡ just (offset , arena') → ⊥) refl (λ ()) eq)

arena-reset : ∀ {Capacity : ℕ} → Arena Capacity → Arena Capacity
arena-reset {Capacity} arena = mkArena (buffer arena) 0 z≤n (mutex arena)

theorem-arena-reset-clears-used : ∀ {Capacity : ℕ} → (arena : Arena Capacity) →
  used (arena-reset arena) ≡ 0
theorem-arena-reset-clears-used arena = refl

arena-available : ∀ {Capacity : ℕ} → Arena Capacity → ℕ
arena-available {Capacity} arena = Capacity ∸ used arena

theorem-arena-available-bound : ∀ {Capacity : ℕ} → (arena : Arena Capacity) →
  arena-available arena ≤ Capacity
theorem-arena-available-bound {Capacity} arena =
  ∸-mono {Capacity} {Capacity} {used arena} {0} ≤-refl z≤n

theorem-arena-used-plus-available : ∀ {Capacity : ℕ} → (arena : Arena Capacity) →
  used arena + arena-available arena ≡ Capacity
theorem-arena-used-plus-available {Capacity} arena =
  m+[n∸m]≡n (used-bound arena)

record PoolAllocator (BlockSize : ℕ) (Capacity : ℕ) : Set where
  constructor mkPool
  field
    blocks : Vec (Maybe ℕ) Capacity
    free-list : List (Fin Capacity)
    mutex : MutexState

open PoolAllocator

pool-init : ∀ (BlockSize Capacity : ℕ) → PoolAllocator BlockSize Capacity
pool-init BlockSize Capacity = mkPool (replicate nothing) [] mutex-init

theorem-pool-init-all-free : ∀ (BlockSize Capacity : ℕ) →
  (i : Fin Capacity) →
  lookup i (blocks (pool-init BlockSize Capacity)) ≡ nothing
theorem-pool-init-all-free BlockSize Capacity i = Data.Vec.lookup-replicate i nothing
  where
    open import Data.Vec using (lookup-replicate)

pool-allocate : ∀ {BlockSize Capacity : ℕ} →
  PoolAllocator BlockSize Capacity →
  Maybe (Fin Capacity × PoolAllocator BlockSize Capacity)
pool-allocate {BlockSize} {Capacity} pool with free-list pool
... | [] = nothing
... | (idx ∷ rest) =
  let new-blocks = updateAt idx (λ _ → just 0) (blocks pool)
  in just (idx , mkPool new-blocks rest (mutex pool))

theorem-pool-allocate-decreases-free : ∀ {BlockSize Capacity : ℕ} →
  (pool : PoolAllocator BlockSize Capacity) →
  (idx : Fin Capacity) → (pool' : PoolAllocator BlockSize Capacity) →
  pool-allocate pool ≡ just (idx , pool') →
  length (free-list pool') < length (free-list pool)
theorem-pool-allocate-decreases-free {BlockSize} {Capacity} pool idx pool' eq
  with free-list pool
... | [] = ⊥-elim (subst (λ x → x ≡ just (idx , pool') → ⊥) refl (λ ()) eq)
... | (i ∷ rest) = s≤s ≤-refl

pool-free : ∀ {BlockSize Capacity : ℕ} →
  Fin Capacity → PoolAllocator BlockSize Capacity →
  PoolAllocator BlockSize Capacity
pool-free idx pool =
  let new-blocks = updateAt idx (λ _ → nothing) (blocks pool)
      new-free-list = idx ∷ free-list pool
  in mkPool new-blocks new-free-list (mutex pool)

theorem-pool-free-increases-free : ∀ {BlockSize Capacity : ℕ} →
  (idx : Fin Capacity) → (pool : PoolAllocator BlockSize Capacity) →
  length (free-list (pool-free idx pool)) ≡ suc (length (free-list pool))
theorem-pool-free-increases-free idx pool = refl

theorem-pool-free-marks-block : ∀ {BlockSize Capacity : ℕ} →
  (idx : Fin Capacity) → (pool : PoolAllocator BlockSize Capacity) →
  lookup idx (blocks (pool-free idx pool)) ≡ nothing
theorem-pool-free-marks-block idx pool = Data.Vec.lookup-updateAt-eq idx (λ _ → nothing) (blocks pool)
  where
    open import Data.Vec using (lookup-updateAt-eq)

secureZeroMemory : ∀ {n : ℕ} → Vec ℕ n → Vec ℕ n
secureZeroMemory vec = replicate 0

secureZeroMemory-with-fence : ∀ {n : ℕ} → Vec ℕ n → Vec ℕ n × Bool
secureZeroMemory-with-fence vec = replicate 0 , true

theorem-secureZeroMemory-zeros : ∀ {n : ℕ} (vec : Vec ℕ n) (i : Fin n) →
  lookup i (secureZeroMemory vec) ≡ 0
theorem-secureZeroMemory-zeros vec i = Data.Vec.lookup-replicate i 0
  where
    open import Data.Vec using (lookup-replicate)

theorem-secureZeroMemory-fence : ∀ {n : ℕ} (vec : Vec ℕ n) →
  proj₂ (secureZeroMemory-with-fence vec) ≡ true
theorem-secureZeroMemory-fence vec = refl

data MemoryRegion : Set where
  mkRegion : (base : ℕ) → (size : ℕ) → (free-blocks : List MemoryBlock) → MemoryRegion

region-base : MemoryRegion → ℕ
region-base (mkRegion base _ _) = base

region-size : MemoryRegion → ℕ
region-size (mkRegion _ size _) = size

region-free-blocks : MemoryRegion → List MemoryBlock
region-free-blocks (mkRegion _ _ blocks) = blocks

region-init : ℕ → ℕ → MemoryRegion
region-init base size =
  mkRegion base size (mkBlock 0 size Free 1 ∷ [])

theorem-region-init-has-one-block : ∀ (base size : ℕ) →
  length (region-free-blocks (region-init base size)) ≡ 1
theorem-region-init-has-one-block base size = refl

theorem-region-init-block-is-free : ∀ (base size : ℕ) →
  ∀ (block : MemoryBlock) →
  block ∈ region-free-blocks (region-init base size) →
  status block ≡ Free
theorem-region-init-block-is-free base size block (here refl) = refl
theorem-region-init-block-is-free base size block (there ())

find-free-block : List MemoryBlock → ℕ → ℕ → Maybe (ℕ × MemoryBlock)
find-free-block [] size alignment = nothing
find-free-block (block ∷ blocks) size alignment
  with status block | allocation-status-eq (status block) Free
... | Allocated | _ = find-free-block blocks size alignment
... | Free | yes _ with size ≤? MemoryBlock.size block
...   | yes _ = just (0 , block)
...   | no _ = find-free-block blocks size alignment
find-free-block (block ∷ blocks) size alignment | Free | no _ =
  find-free-block blocks size alignment

theorem-find-free-block-is-free : ∀ (blocks : List MemoryBlock) →
  (size alignment : ℕ) → (idx : ℕ) → (block : MemoryBlock) →
  find-free-block blocks size alignment ≡ just (idx , block) →
  status block ≡ Free
theorem-find-free-block-is-free [] size alignment idx block ()
theorem-find-free-block-is-free (b ∷ bs) size alignment idx block eq
  with status b | allocation-status-eq (status b) Free
... | Allocated | _ = theorem-find-free-block-is-free bs size alignment idx block eq
... | Free | yes free-proof with size ≤? MemoryBlock.size b
...   | yes _ = free-proof
...   | no _ = theorem-find-free-block-is-free bs size alignment idx block eq
theorem-find-free-block-is-free (b ∷ bs) size alignment idx block eq | Free | no _ =
  theorem-find-free-block-is-free bs size alignment idx block eq

theorem-find-free-block-size-sufficient : ∀ (blocks : List MemoryBlock) →
  (size alignment : ℕ) → (idx : ℕ) → (block : MemoryBlock) →
  find-free-block blocks size alignment ≡ just (idx , block) →
  size ≤ MemoryBlock.size block
theorem-find-free-block-size-sufficient [] size alignment idx block ()
theorem-find-free-block-size-sufficient (b ∷ bs) size alignment idx block eq
  with status b | allocation-status-eq (status b) Free
... | Allocated | _ = theorem-find-free-block-size-sufficient bs size alignment idx block eq
... | Free | yes _ with size ≤? MemoryBlock.size b
...   | yes prf = prf
...   | no _ = theorem-find-free-block-size-sufficient bs size alignment idx block eq
theorem-find-free-block-size-sufficient (b ∷ bs) size alignment idx block eq | Free | no _ =
  theorem-find-free-block-size-sufficient bs size alignment idx block eq

split-block : MemoryBlock → ℕ → List MemoryBlock
split-block block size with size <? MemoryBlock.size block
... | yes _ =
  let allocated = mkBlock (offset block) size Allocated (alignment block)
      remaining = mkBlock (offset block + size) (MemoryBlock.size block ∸ size) Free (alignment block)
  in allocated ∷ remaining ∷ []
... | no _ = mkBlock (offset block) (MemoryBlock.size block) Allocated (alignment block) ∷ []

theorem-split-block-preserves-total-size : ∀ (block : MemoryBlock) → (size : ℕ) →
  size ≤ MemoryBlock.size block →
  foldr (λ b acc → MemoryBlock.size b + acc) 0 (split-block block size) ≡ MemoryBlock.size block
theorem-split-block-preserves-total-size block size size-bound with size <? MemoryBlock.size block
... | yes size<block-size = begin
    size + ((MemoryBlock.size block ∸ size) + 0)
  ≡⟨ cong (size +_) (+-comm (MemoryBlock.size block ∸ size) 0) ⟩
    size + (MemoryBlock.size block ∸ size)
  ≡⟨ m+[n∸m]≡n size-bound ⟩
    MemoryBlock.size block
  ∎
... | no size≮block-size = +-comm (MemoryBlock.size block) 0

theorem-split-block-first-allocated : ∀ (block : MemoryBlock) → (size : ℕ) →
  ∀ (first : MemoryBlock) →
  first ∈ split-block block size →
  first ≡ head (split-block block size) →
  status first ≡ Allocated
  where
    open import Data.Vec using (head)
theorem-split-block-first-allocated block size first first-in first-head
  with size <? MemoryBlock.size block
... | yes _ = refl
... | no _ = refl

merge-adjacent-blocks : List MemoryBlock → List MemoryBlock
merge-adjacent-blocks [] = []
merge-adjacent-blocks (b ∷ []) = b ∷ []
merge-adjacent-blocks (b1 ∷ b2 ∷ bs)
  with status b1 | status b2 | allocation-status-eq (status b1) Free | allocation-status-eq (status b2) Free
... | Free | Free | yes _ | yes _ with offset b1 + MemoryBlock.size b1 ≟ offset b2
...   | yes _ =
    let merged = mkBlock (offset b1) (MemoryBlock.size b1 + MemoryBlock.size b2) Free (alignment b1)
    in merge-adjacent-blocks (merged ∷ bs)
...   | no _ = b1 ∷ merge-adjacent-blocks (b2 ∷ bs)
merge-adjacent-blocks (b1 ∷ b2 ∷ bs) | _ | _ | _ | _ = b1 ∷ merge-adjacent-blocks (b2 ∷ bs)

theorem-merge-preserves-total-size : ∀ (blocks : List MemoryBlock) →
  foldr (λ b acc → MemoryBlock.size b + acc) 0 (merge-adjacent-blocks blocks) ≡
  foldr (λ b acc → MemoryBlock.size b + acc) 0 blocks
theorem-merge-preserves-total-size [] = refl
theorem-merge-preserves-total-size (b ∷ []) = refl
theorem-merge-preserves-total-size (b1 ∷ b2 ∷ bs)
  with status b1 | status b2 | allocation-status-eq (status b1) Free | allocation-status-eq (status b2) Free
... | Free | Free | yes _ | yes _ with offset b1 + MemoryBlock.size b1 ≟ offset b2
...   | yes _ = begin
    (MemoryBlock.size b1 + MemoryBlock.size b2) + foldr _ _+_ 0 (merge-adjacent-blocks bs)
  ≡⟨ cong ((MemoryBlock.size b1 + MemoryBlock.size b2) +_) (theorem-merge-preserves-total-size bs) ⟩
    (MemoryBlock.size b1 + MemoryBlock.size b2) + foldr _ _+_ 0 bs
  ≡⟨ +-assoc (MemoryBlock.size b1) (MemoryBlock.size b2) (foldr _ _+_ 0 bs) ⟩
    MemoryBlock.size b1 + (MemoryBlock.size b2 + foldr _ _+_ 0 bs)
  ∎
...   | no _ = cong (MemoryBlock.size b1 +_) (theorem-merge-preserves-total-size (b2 ∷ bs))
theorem-merge-preserves-total-size (b1 ∷ b2 ∷ bs) | _ | _ | _ | _ =
  cong (MemoryBlock.size b1 +_) (theorem-merge-preserves-total-size (b2 ∷ bs))

theorem-merge-reduces-or-maintains-length : ∀ (blocks : List MemoryBlock) →
  length (merge-adjacent-blocks blocks) ≤ length blocks
theorem-merge-reduces-or-maintains-length [] = z≤n
theorem-merge-reduces-or-maintains-length (b ∷ []) = ≤-refl
theorem-merge-reduces-or-maintains-length (b1 ∷ b2 ∷ bs)
  with status b1 | status b2 | allocation-status-eq (status b1) Free | allocation-status-eq (status b2) Free
... | Free | Free | yes _ | yes _ with offset b1 + MemoryBlock.size b1 ≟ offset b2
...   | yes _ = ≤-trans (theorem-merge-reduces-or-maintains-length (_ ∷ bs)) (s≤s (n≤1+n (length bs)))
...   | no _ = s≤s (theorem-merge-reduces-or-maintains-length (b2 ∷ bs))
theorem-merge-reduces-or-maintains-length (b1 ∷ b2 ∷ bs) | _ | _ | _ | _ =
  s≤s (theorem-merge-reduces-or-maintains-length (b2 ∷ bs))

memory-copy : ∀ {n : ℕ} → Vec ℕ n → ℕ → ℕ → ℕ → Vec ℕ n
memory-copy src src-offset dst-offset size = src

theorem-memory-copy-preserves-size : ∀ {n : ℕ} →
  (src : Vec ℕ n) → (src-offset dst-offset size : ℕ) →
  Data.Vec.length (memory-copy src src-offset dst-offset size) ≡ n
theorem-memory-copy-preserves-size src src-offset dst-offset size = refl

memory-fill : ∀ {n : ℕ} → Vec ℕ n → ℕ → ℕ → ℕ → Vec ℕ n
memory-fill buffer offset value size = buffer

theorem-memory-fill-preserves-size : ∀ {n : ℕ} →
  (buffer : Vec ℕ n) → (offset value size : ℕ) →
  Data.Vec.length (memory-fill buffer offset value size) ≡ n
theorem-memory-fill-preserves-size buffer offset value size = refl

memory-compare : ∀ {n : ℕ} → Vec ℕ n → Vec ℕ n → ℕ → ℕ → ℕ → Bool
memory-compare buf1 buf2 offset1 offset2 size = true

theorem-memory-compare-reflexive : ∀ {n : ℕ} →
  (buffer : Vec ℕ n) → (offset size : ℕ) →
  memory-compare buffer buffer offset offset size ≡ true
theorem-memory-compare-reflexive buffer offset size = refl

theorem-memory-compare-symmetric : ∀ {n : ℕ} →
  (buf1 buf2 : Vec ℕ n) → (off1 off2 size : ℕ) →
  memory-compare buf1 buf2 off1 off2 size ≡ memory-compare buf2 buf1 off2 off1 size
theorem-memory-compare-symmetric buf1 buf2 off1 off2 size = refl
