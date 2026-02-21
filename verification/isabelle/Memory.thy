theory Memory
  imports Complex_Main Types
begin

definition CacheLineSize :: nat where
  "CacheLineSize \<equiv> 128"

lemma cache_line_size_modern: "CacheLineSize = 128"
  by (simp add: CacheLineSize_def)

definition PageSizeRuntime :: "nat \<Rightarrow> nat" where
  "PageSizeRuntime runtime_value \<equiv> runtime_value"

definition PageSizeDefault :: nat where
  "PageSizeDefault \<equiv> 4096"

definition PageSize :: "nat \<Rightarrow> nat" where
  "PageSize runtime_value \<equiv> PageSizeRuntime runtime_value"

lemma page_size_is_runtime:
  "PageSize ps = ps"
  by (simp add: PageSize_def PageSizeRuntime_def)

definition align_forward_rt :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "align_forward_rt n alignment page_size \<equiv> ((n + alignment - 1) div alignment) * alignment"

record mutex_state =
  mutex_locked :: bool
  mutex_owner_thread :: nat

definition mutex_init :: "mutex_state" where
  "mutex_init \<equiv> \<lparr> mutex_locked = False, mutex_owner_thread = 0 \<rparr>"

definition mutex_lock :: "nat \<Rightarrow> mutex_state \<Rightarrow> mutex_state" where
  "mutex_lock tid m \<equiv> \<lparr> mutex_locked = True, mutex_owner_thread = tid \<rparr>"

definition mutex_unlock :: "mutex_state \<Rightarrow> mutex_state" where
  "mutex_unlock m \<equiv> \<lparr> mutex_locked = False, mutex_owner_thread = 0 \<rparr>"

definition mutex_try_lock :: "nat \<Rightarrow> mutex_state \<Rightarrow> (mutex_state \<times> bool)" where
  "mutex_try_lock tid m \<equiv>
    if mutex_locked m then (m, False)
    else (\<lparr> mutex_locked = True, mutex_owner_thread = tid \<rparr>, True)"

lemma mutex_lock_unlock:
  "mutex_locked (mutex_unlock (mutex_lock tid m)) = False"
  by (simp add: mutex_unlock_def mutex_lock_def)

lemma mutex_no_double_unlock:
  "mutex_locked m = False \<Longrightarrow> mutex_unlock m = \<lparr> mutex_locked = False, mutex_owner_thread = 0 \<rparr>"
  by (simp add: mutex_unlock_def)

fun align_forward :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "align_forward n align = ((n + align - 1) div align) * align"

theorem align_forward_ge:
  assumes "align > 0"
  shows "n \<le> align_forward n align"
  using assms by (simp add: align_forward.simps)

theorem align_forward_aligned:
  assumes "align > 0"
  shows "\<exists>k. align_forward n align = k * align"
  using assms by (simp add: align_forward.simps) (metis mult.commute)

record arena =
  buffer_size :: nat
  offset :: nat
  offset_le_size :: "offset \<le> buffer_size"

definition arena_init :: "nat \<Rightarrow> nat \<Rightarrow> arena" where
  "arena_init size page_size \<equiv> \<lparr>
    buffer_size = align_forward_rt size page_size page_size,
    offset = 0,
    offset_le_size = by simp \<rparr>"

definition arena_init_default :: "nat \<Rightarrow> arena" where
  "arena_init_default size \<equiv> arena_init size PageSizeDefault"

definition arena_alloc :: "arena \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> arena option" where
  "arena_alloc ar size alignment \<equiv>
    let current_offset = offset ar;
        aligned_offset = align_forward current_offset alignment;
        end_offset = aligned_offset + size
    in if end_offset \<le> buffer_size ar
       then Some \<lparr> buffer_size = buffer_size ar,
                    offset = end_offset,
                    offset_le_size = by (simp add: end_offset_def) \<rparr>
       else None"

definition arena_reset :: "arena \<Rightarrow> arena" where
  "arena_reset ar \<equiv> \<lparr> buffer_size = buffer_size ar,
                        offset = 0,
                        offset_le_size = by simp \<rparr>"

definition arena_allocated :: "arena \<Rightarrow> nat" where
  "arena_allocated ar \<equiv> offset ar"

definition arena_remaining :: "arena \<Rightarrow> nat" where
  "arena_remaining ar \<equiv> buffer_size ar - offset ar"

theorem arena_alloc_increases_offset:
  assumes "arena_alloc ar size alignment = Some result"
  shows "offset ar \<le> offset result"
  using assms by (simp add: arena_alloc_def Let_def split: if_splits)

theorem arena_reset_clears:
  "offset (arena_reset ar) = 0"
  by (simp add: arena_reset_def)

theorem arena_remaining_correct:
  "arena_remaining ar + offset ar = buffer_size ar"
  using arena.offset_le_size by (simp add: arena_remaining_def)

record slab_metadata =
  block_size :: nat
  num_blocks :: nat
  used_blocks :: nat
  used_le_total :: "used_blocks \<le> num_blocks"

definition slab_init :: "nat \<Rightarrow> nat \<Rightarrow> slab_metadata" where
  "slab_init block_size slab_size \<equiv> \<lparr>
    block_size = block_size,
    num_blocks = slab_size div block_size,
    used_blocks = 0,
    used_le_total = by simp \<rparr>"

definition slab_alloc_block :: "slab_metadata \<Rightarrow> slab_metadata option" where
  "slab_alloc_block slab \<equiv>
    if used_blocks slab < num_blocks slab
    then Some \<lparr> block_size = block_size slab,
                 num_blocks = num_blocks slab,
                 used_blocks = Suc (used_blocks slab),
                 used_le_total = by (simp add: Suc_le_eq) \<rparr>
    else None"

definition slab_free_block :: "slab_metadata \<Rightarrow> slab_metadata" where
  "slab_free_block slab \<equiv>
    (case used_blocks slab of
       0 \<Rightarrow> slab
     | Suc n \<Rightarrow> \<lparr> block_size = block_size slab,
                   num_blocks = num_blocks slab,
                   used_blocks = n,
                   used_le_total = by (simp add: Suc_le_eq used_le_total slab) \<rparr>)"

definition slab_is_full :: "slab_metadata \<Rightarrow> bool" where
  "slab_is_full slab \<equiv> used_blocks slab = num_blocks slab"

definition slab_is_empty :: "slab_metadata \<Rightarrow> bool" where
  "slab_is_empty slab \<equiv> used_blocks slab = 0"

definition slab_utilization :: "slab_metadata \<Rightarrow> nat" where
  "slab_utilization slab \<equiv> (used_blocks slab * 100) div num_blocks slab"

theorem slab_alloc_increases_used:
  assumes "slab_alloc_block slab = Some result"
  shows "used_blocks slab < used_blocks result"
  using assms by (simp add: slab_alloc_block_def split: if_splits)

theorem slab_free_decreases_used:
  assumes "used_blocks slab > 0"
  shows "used_blocks (slab_free_block slab) < used_blocks slab"
  using assms by (simp add: slab_free_block_def split: nat.splits)

theorem slab_invariant_preserved:
  "used_le_total (slab_free_block slab)"
  by (simp add: slab_free_block_def split: nat.splits)

record pool_metadata =
  pool_block_size :: nat
  pool_num_blocks :: nat
  free_count :: nat
  free_le_total :: "free_count \<le> pool_num_blocks"

definition pool_init :: "nat \<Rightarrow> nat \<Rightarrow> pool_metadata" where
  "pool_init block_size num_blocks \<equiv> \<lparr>
    pool_block_size = block_size,
    pool_num_blocks = num_blocks,
    free_count = num_blocks,
    free_le_total = by simp \<rparr>"

definition pool_alloc :: "pool_metadata \<Rightarrow> pool_metadata option" where
  "pool_alloc pool \<equiv>
    (case free_count pool of
       0 \<Rightarrow> None
     | Suc n \<Rightarrow> Some \<lparr> pool_block_size = pool_block_size pool,
                       pool_num_blocks = pool_num_blocks pool,
                       free_count = n,
                       free_le_total = by (simp add: Suc_le_eq free_le_total pool) \<rparr>)"

definition pool_free :: "pool_metadata \<Rightarrow> pool_metadata option" where
  "pool_free pool \<equiv>
    if free_count pool < pool_num_blocks pool
    then Some \<lparr> pool_block_size = pool_block_size pool,
                 pool_num_blocks = pool_num_blocks pool,
                 free_count = Suc (free_count pool),
                 free_le_total = by (simp add: Suc_le_eq) \<rparr>
    else None"

definition pool_is_full :: "pool_metadata \<Rightarrow> bool" where
  "pool_is_full pool \<equiv> free_count pool = 0"

definition pool_is_empty :: "pool_metadata \<Rightarrow> bool" where
  "pool_is_empty pool \<equiv> free_count pool = pool_num_blocks pool"

theorem pool_alloc_decreases_free:
  assumes "pool_alloc pool = Some result"
  shows "free_count result < free_count pool"
  using assms by (simp add: pool_alloc_def split: nat.splits)

theorem pool_free_increases_free:
  assumes "pool_free pool = Some result"
  shows "free_count pool < free_count result"
  using assms by (simp add: pool_free_def split: if_splits)

theorem pool_alloc_free_inverse:
  assumes "pool_alloc pool = Some pool'"
  and "pool_free pool' = Some pool''"
  shows "free_count pool = free_count pool''"
  using assms by (simp add: pool_alloc_def pool_free_def split: nat.splits if_splits)

record buddy_metadata =
  total_size :: nat
  min_block_size :: nat
  max_order :: nat
  free_lists :: "nat list"
  total_size_pow2 :: "\<exists>k. total_size = min_block_size * (2^k)"

definition buddy_init :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> buddy_metadata" where
  "buddy_init total_size min_block max_order \<equiv> \<lparr>
    total_size = total_size,
    min_block_size = min_block,
    max_order = max_order,
    free_lists = 1 # replicate max_order 0,
    total_size_pow2 = by (rule exI[where x=max_order]) simp \<rparr>"

fun buddy_order_for_size :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "buddy_order_for_size size min_block =
    (if size \<le> min_block then 0
     else Suc (buddy_order_for_size (size div 2) min_block))"

definition buddy_alloc_order :: "buddy_metadata \<Rightarrow> nat \<Rightarrow> buddy_metadata option" where
  "buddy_alloc_order buddy order \<equiv>
    if order < length (free_lists buddy) then
      let count = free_lists buddy ! order
      in if count > 0 then
           let new_free_lists = (free_lists buddy)[order := count - 1]
           in Some \<lparr> total_size = total_size buddy,
                       min_block_size = min_block_size buddy,
                       max_order = max_order buddy,
                       free_lists = new_free_lists,
                       total_size_pow2 = total_size_pow2 buddy \<rparr>
         else None
    else None"

definition buddy_free_order :: "buddy_metadata \<Rightarrow> nat \<Rightarrow> buddy_metadata" where
  "buddy_free_order buddy order \<equiv>
    if order < length (free_lists buddy) then
      let count = free_lists buddy ! order;
          new_free_lists = (free_lists buddy)[order := count + 1]
      in \<lparr> total_size = total_size buddy,
            min_block_size = min_block_size buddy,
            max_order = max_order buddy,
            free_lists = new_free_lists,
            total_size_pow2 = total_size_pow2 buddy \<rparr>
    else buddy"

theorem buddy_size_invariant:
  "\<exists>k. total_size buddy = min_block_size buddy * (2^k)"
  using buddy_metadata.total_size_pow2 by auto

type_synonym atomic_refcount = nat

definition refcount_init :: atomic_refcount where
  "refcount_init \<equiv> 1"

definition refcount_increment :: "atomic_refcount \<Rightarrow> atomic_refcount" where
  "refcount_increment rc \<equiv> rc + 1"

definition refcount_decrement :: "atomic_refcount \<Rightarrow> atomic_refcount" where
  "refcount_decrement rc \<equiv> (if rc = 0 then 0 else rc - 1)"

definition refcount_is_zero :: "atomic_refcount \<Rightarrow> bool" where
  "refcount_is_zero rc \<equiv> rc = 0"

theorem refcount_increment_positive:
  "refcount_increment rc > 0"
  by (simp add: refcount_increment_def)

theorem refcount_inc_dec_inverse:
  assumes "rc > 0"
  shows "refcount_decrement (refcount_increment rc) = rc"
  using assms by (simp add: refcount_increment_def refcount_decrement_def)

theorem refcount_monotone_dec:
  "refcount_decrement rc \<le> rc"
  by (simp add: refcount_decrement_def)

record memory_region =
  start_addr :: nat
  mem_size :: nat
  allocated :: bool

definition memregion_init :: "nat \<Rightarrow> nat \<Rightarrow> memory_region" where
  "memregion_init start size \<equiv> \<lparr> start_addr = start,
                                    mem_size = size,
                                    allocated = False \<rparr>"

definition memregion_in_bounds :: "memory_region \<Rightarrow> nat \<Rightarrow> bool" where
  "memregion_in_bounds region addr \<equiv>
    start_addr region \<le> addr \<and> addr < start_addr region + mem_size region"

theorem memregion_bounds_correct:
  assumes "memregion_in_bounds region addr"
  shows "start_addr region \<le> addr \<and> addr < start_addr region + mem_size region"
  using assms by (simp add: memregion_in_bounds_def)

record cache_line_state =
  valid :: bool
  dirty :: bool
  tag :: nat

definition cacheline_init :: cache_line_state where
  "cacheline_init \<equiv> \<lparr> valid = False, dirty = False, tag = 0 \<rparr>"

definition cacheline_load :: "cache_line_state \<Rightarrow> nat \<Rightarrow> cache_line_state" where
  "cacheline_load line tag \<equiv> line\<lparr> valid := True, tag := tag \<rparr>"

definition cacheline_store :: "cache_line_state \<Rightarrow> nat \<Rightarrow> cache_line_state" where
  "cacheline_store line tag \<equiv> line\<lparr> valid := True, dirty := True, tag := tag \<rparr>"

definition cacheline_invalidate :: "cache_line_state \<Rightarrow> cache_line_state" where
  "cacheline_invalidate line \<equiv> line\<lparr> valid := False \<rparr>"

definition cacheline_flush :: "cache_line_state \<Rightarrow> cache_line_state" where
  "cacheline_flush line \<equiv> line\<lparr> dirty := False \<rparr>"

theorem cacheline_load_valid:
  "valid (cacheline_load line tag)"
  by (simp add: cacheline_load_def)

theorem cacheline_store_dirty:
  "dirty (cacheline_store line tag)"
  by (simp add: cacheline_store_def)

theorem cacheline_invalidate_clears:
  "\<not> valid (cacheline_invalidate line)"
  by (simp add: cacheline_invalidate_def)

theorem cacheline_flush_clears_dirty:
  "\<not> dirty (cacheline_flush line)"
  by (simp add: cacheline_flush_def)

end
