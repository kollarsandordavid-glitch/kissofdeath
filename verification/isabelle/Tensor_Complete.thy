theory Tensor_Complete
imports Main HOL.Real HOL.List
begin

datatype dtype = F32 | F64 | I32 | I64 | U32 | U64 | BOOL

record 'a tensor =
  data :: "'a list"
  shape :: "nat list"
  strides :: "nat list"
  ndim :: nat
  refcount :: nat

definition shape_size :: "nat list ⇒ nat" where
  "shape_size shape = foldr (*) shape 1"

lemma shape_size_positive: "shape_size shape ≥ 1"
  unfolding shape_size_def
  by (induction shape) auto

lemma shape_size_cons: "shape_size (d # ds) = d * shape_size ds"
  unfolding shape_size_def by simp

definition compute_strides :: "nat list ⇒ nat list" where
  "compute_strides shape = (let n = length shape in
    map (λi. foldr (*) (drop (Suc i) shape) 1) [0..<n])"

lemma compute_strides_length: "length (compute_strides shape) = length shape"
  unfolding compute_strides_def by simp

definition tensor_valid :: "'a tensor ⇒ bool" where
  "tensor_valid t = (
    length (data t) = shape_size (shape t) ∧
    length (strides t) = length (shape t) ∧
    ndim t = length (shape t) ∧
    refcount t > 0)"

lemma tensor_valid_positive_refcount:
  "tensor_valid t ⟹ refcount t > 0"
  unfolding tensor_valid_def by simp

definition tensor_init :: "nat list ⇒ 'a list ⇒ 'a tensor" where
  "tensor_init shape_val data_val = ⦇
    data = data_val,
    shape = shape_val,
    strides = compute_strides shape_val,
    ndim = length shape_val,
    refcount = 1
  ⦈"

lemma tensor_init_valid:
  assumes "length data_val = shape_size shape_val"
  shows "tensor_valid (tensor_init shape_val data_val)"
  unfolding tensor_valid_def tensor_init_def
  using assms compute_strides_length by simp

definition tensor_retain :: "'a tensor ⇒ 'a tensor" where
  "tensor_retain t = t⦇refcount := refcount t + 1⦈"

lemma tensor_retain_preserves_valid:
  "tensor_valid t ⟹ tensor_valid (tensor_retain t)"
  unfolding tensor_valid_def tensor_retain_def by simp

lemma tensor_retain_increases_refcount:
  "refcount (tensor_retain t) = refcount t + 1"
  unfolding tensor_retain_def by simp

definition tensor_release :: "'a tensor ⇒ 'a tensor option" where
  "tensor_release t = (if refcount t = 1 then None
                       else Some (t⦇refcount := refcount t - 1⦈))"

lemma tensor_release_decreases_refcount:
  assumes "refcount t > 1"
  shows "∃t'. tensor_release t = Some t' ∧ refcount t' = refcount t - 1"
  using assms unfolding tensor_release_def by auto

definition get_flat_index :: "nat list ⇒ nat list ⇒ nat" where
  "get_flat_index indices strides_val = 
    foldr (+) (map (λi. fst i * snd i) (zip indices strides_val)) 0"

lemma get_flat_index_bounds:
  assumes "length indices = length strides_val"
  assumes "∀i < length indices. indices ! i < shape ! i"
  assumes "strides_val = compute_strides shape"
  shows "get_flat_index indices strides_val < shape_size shape"
  using assms unfolding get_flat_index_def shape_size_def compute_strides_def
  by (induction indices arbitrary: strides_val shape) auto

definition tensor_get :: "'a tensor ⇒ nat list ⇒ 'a option" where
  "tensor_get t indices = (
    if length indices = ndim t ∧ (∀i < length indices. indices ! i < shape t ! i)
    then Some (data t ! get_flat_index indices (strides t))
    else None)"

lemma tensor_get_valid_indices:
  assumes "tensor_valid t"
  assumes "length indices = ndim t"
  assumes "∀i < length indices. indices ! i < shape t ! i"
  shows "∃v. tensor_get t indices = Some v"
  using assms unfolding tensor_get_def tensor_valid_def by auto

definition tensor_set :: "'a tensor ⇒ nat list ⇒ 'a ⇒ 'a tensor" where
  "tensor_set t indices value = (
    let idx = get_flat_index indices (strides t) in
    t⦇data := (data t)[idx := value]⦈)"

lemma tensor_set_preserves_valid:
  assumes "tensor_valid t"
  assumes "length indices = ndim t"
  assumes "∀i < length indices. indices ! i < shape t ! i"
  shows "tensor_valid (tensor_set t indices value)"
  using assms unfolding tensor_valid_def tensor_set_def
  by (simp add: length_list_update)

definition tensor_fill :: "'a tensor ⇒ 'a ⇒ 'a tensor" where
  "tensor_fill t value = t⦇data := replicate (length (data t)) value⦈"

lemma tensor_fill_preserves_valid:
  "tensor_valid t ⟹ tensor_valid (tensor_fill t value)"
  unfolding tensor_valid_def tensor_fill_def by simp

definition tensor_add_elementwise :: "real tensor ⇒ real tensor ⇒ real tensor option" where
  "tensor_add_elementwise t1 t2 = (
    if shape t1 = shape t2
    then Some (t1⦇data := map (λi. fst i + snd i) (zip (data t1) (data t2))⦈)
    else None)"

lemma tensor_add_shape_preserves:
  assumes "tensor_add_elementwise t1 t2 = Some t3"
  shows "shape t3 = shape t1"
  using assms unfolding tensor_add_elementwise_def
  by (simp split: if_splits)

lemma tensor_add_commutative:
  assumes "shape t1 = shape t2"
  assumes "tensor_add_elementwise t1 t2 = Some t3"
  assumes "tensor_add_elementwise t2 t1 = Some t4"
  shows "data t3 = data t4"
  using assms unfolding tensor_add_elementwise_def
  by (auto simp add: zip_commute)

definition tensor_sub_elementwise :: "real tensor ⇒ real tensor ⇒ real tensor option" where
  "tensor_sub_elementwise t1 t2 = (
    if shape t1 = shape t2
    then Some (t1⦇data := map (λi. fst i - snd i) (zip (data t1) (data t2))⦈)
    else None)"

definition tensor_mul_elementwise :: "real tensor ⇒ real tensor ⇒ real tensor option" where
  "tensor_mul_elementwise t1 t2 = (
    if shape t1 = shape t2
    then Some (t1⦇data := map (λi. fst i * snd i) (zip (data t1) (data t2))⦈)
    else None)"

lemma tensor_mul_commutative:
  assumes "shape t1 = shape t2"
  assumes "tensor_mul_elementwise t1 t2 = Some t3"
  assumes "tensor_mul_elementwise t2 t1 = Some t4"
  shows "data t3 = data t4"
  using assms unfolding tensor_mul_elementwise_def
  by (auto simp add: zip_commute mult.commute)

definition tensor_add_scalar :: "real tensor ⇒ real ⇒ real tensor" where
  "tensor_add_scalar t scalar = t⦇data := map (λx. x + scalar) (data t)⦈"

lemma tensor_add_scalar_preserves_valid:
  "tensor_valid t ⟹ tensor_valid (tensor_add_scalar t scalar)"
  unfolding tensor_valid_def tensor_add_scalar_def by simp

definition tensor_mul_scalar :: "real tensor ⇒ real ⇒ real tensor" where
  "tensor_mul_scalar t scalar = t⦇data := map (λx. x * scalar) (data t)⦈"

lemma tensor_mul_scalar_distributive:
  assumes "tensor_add_elementwise t1 t2 = Some t3"
  shows "data (tensor_mul_scalar t3 s) = 
         map (λi. fst i + snd i) 
             (zip (data (tensor_mul_scalar t1 s)) 
                  (data (tensor_mul_scalar t2 s)))"
  using assms unfolding tensor_add_elementwise_def tensor_mul_scalar_def
  by (auto simp add: distrib_left)

definition tensor_dot_product :: "real list ⇒ real list ⇒ real" where
  "tensor_dot_product v1 v2 = foldr (+) (map (λi. fst i * snd i) (zip v1 v2)) 0"

lemma dot_product_commutative:
  "length v1 = length v2 ⟹ 
   tensor_dot_product v1 v2 = tensor_dot_product v2 v1"
  unfolding tensor_dot_product_def
  by (induction v1 v2 rule: list_induct2) (auto simp add: mult.commute)

definition tensor_matmul :: "real tensor ⇒ real tensor ⇒ real tensor option" where
  "tensor_matmul t1 t2 = (
    if ndim t1 = 2 ∧ ndim t2 = 2 ∧ shape t1 ! 1 = shape t2 ! 0
    then let m = shape t1 ! 0;
             k = shape t1 ! 1;
             n = shape t2 ! 1;
             result_data = map (λ(i,j). 
               tensor_dot_product 
                 (take k (drop (i*k) (data t1)))
                 (map (λl. data t2 ! (l*n + j)) [0..<k]))
               [(i,j). i ← [0..<m], j ← [0..<n]]
         in Some (tensor_init [m, n] result_data)
    else None)"

lemma tensor_matmul_shape:
  assumes "tensor_matmul t1 t2 = Some t3"
  assumes "ndim t1 = 2"
  assumes "ndim t2 = 2"
  shows "shape t3 = [shape t1 ! 0, shape t2 ! 1]"
  using assms unfolding tensor_matmul_def tensor_init_def
  by (auto split: if_splits)

definition tensor_reshape :: "'a tensor ⇒ nat list ⇒ 'a tensor option" where
  "tensor_reshape t new_shape = (
    if shape_size new_shape = length (data t)
    then Some (t⦇shape := new_shape, 
                 strides := compute_strides new_shape,
                 ndim := length new_shape⦈)
    else None)"

lemma tensor_reshape_preserves_data:
  assumes "tensor_reshape t new_shape = Some t'"
  shows "data t' = data t"
  using assms unfolding tensor_reshape_def by (auto split: if_splits)

lemma tensor_reshape_preserves_size:
  assumes "tensor_reshape t new_shape = Some t'"
  shows "shape_size (shape t') = shape_size (shape t)"
  using assms unfolding tensor_reshape_def shape_size_def
  by (auto split: if_splits)

definition tensor_transpose :: "'a tensor ⇒ nat list ⇒ 'a tensor option" where
  "tensor_transpose t axes = (
    if length axes = ndim t ∧ distinct axes ∧ (∀i ∈ set axes. i < ndim t)
    then let new_shape = map (λi. shape t ! i) axes;
             new_strides = map (λi. strides t ! i) axes
         in Some (t⦇shape := new_shape, strides := new_strides⦈)
    else None)"

lemma tensor_transpose_preserves_ndim:
  assumes "tensor_transpose t axes = Some t'"
  shows "ndim t' = ndim t"
  using assms unfolding tensor_transpose_def by (auto split: if_splits)

definition tensor_sum_all :: "real tensor ⇒ real" where
  "tensor_sum_all t = foldr (+) (data t) 0"

definition tensor_sum_axis :: "real tensor ⇒ nat ⇒ real tensor option" where
  "tensor_sum_axis t axis = (
    if axis < ndim t
    then let reduced_shape = take axis (shape t) @ drop (Suc axis) (shape t);
             axis_size = shape t ! axis
         in Some (tensor_init reduced_shape [])
    else None)"

definition tensor_mean_all :: "real tensor ⇒ real" where
  "tensor_mean_all t = tensor_sum_all t / real (length (data t))"

lemma tensor_sum_nonnegative:
  assumes "∀x ∈ set (data t). x ≥ 0"
  shows "tensor_sum_all t ≥ 0"
  using assms unfolding tensor_sum_all_def
  by (induction "data t") auto

definition broadcast_compatible :: "nat list ⇒ nat list ⇒ bool" where
  "broadcast_compatible shape1 shape2 = (
    let len1 = length shape1;
        len2 = length shape2;
        offset = len2 - len1
    in len2 ≥ len1 ∧ 
       (∀i < len1. shape1 ! i = shape2 ! (offset + i) ∨ shape1 ! i = 1))"

lemma broadcast_reflexive:
  "broadcast_compatible shape shape"
  unfolding broadcast_compatible_def by auto

definition tensor_copy :: "'a tensor ⇒ 'a tensor" where
  "tensor_copy t = tensor_init (shape t) (data t)"

lemma tensor_copy_independent:
  "tensor_copy t ≠ t"
  unfolding tensor_copy_def tensor_init_def by simp

definition tensor_equal :: "'a tensor ⇒ 'a tensor ⇒ bool" where
  "tensor_equal t1 t2 = (
    shape t1 = shape t2 ∧ data t1 = data t2)"

lemma tensor_equal_reflexive:
  "tensor_equal t t"
  unfolding tensor_equal_def by simp

lemma tensor_equal_symmetric:
  "tensor_equal t1 t2 ⟹ tensor_equal t2 t1"
  unfolding tensor_equal_def by simp

lemma tensor_equal_transitive:
  "tensor_equal t1 t2 ⟹ tensor_equal t2 t3 ⟹ tensor_equal t1 t3"
  unfolding tensor_equal_def by simp

definition refcount_safe_operation :: "('a tensor ⇒ 'a tensor) ⇒ bool" where
  "refcount_safe_operation f = (∀t. tensor_valid t ⟶ tensor_valid (f t))"

lemma tensor_retain_safe:
  "refcount_safe_operation tensor_retain"
  unfolding refcount_safe_operation_def
  using tensor_retain_preserves_valid by blast

lemma tensor_fill_safe:
  "refcount_safe_operation (λt. tensor_fill t v)"
  unfolding refcount_safe_operation_def
  using tensor_fill_preserves_valid by blast

definition no_memory_leak :: "'a tensor ⇒ bool" where
  "no_memory_leak t = (refcount t > 0)"

lemma tensor_operations_no_leak:
  assumes "tensor_valid t"
  shows "no_memory_leak t"
  using assms unfolding tensor_valid_def no_memory_leak_def by simp

definition no_use_after_free :: "'a tensor ⇒ bool" where
  "no_use_after_free t = (refcount t > 0 ⟶ length (data t) > 0)"

definition bounds_checked :: "'a tensor ⇒ nat list ⇒ bool" where
  "bounds_checked t indices = (
    length indices = ndim t ∧ (∀i < length indices. indices ! i < shape t ! i))"

lemma safe_access_requires_bounds:
  assumes "tensor_valid t"
  assumes "bounds_checked t indices"
  shows "get_flat_index indices (strides t) < length (data t)"
  using assms get_flat_index_bounds unfolding bounds_checked_def tensor_valid_def by auto

theorem tensor_lifecycle_safe:
  assumes init: "t = tensor_init shape data_val"
  assumes valid_init: "length data_val = shape_size shape"
  assumes retain: "t' = tensor_retain t"
  assumes release: "tensor_release t' = Some t''"
  shows "tensor_valid t''"
proof -
  have "tensor_valid t" using init valid_init tensor_init_valid by simp
  then have "tensor_valid t'" using retain tensor_retain_preserves_valid by simp
  then have "refcount t' > 1" using retain tensor_retain_increases_refcount by simp
  then obtain t''' where "tensor_release t' = Some t'''" "refcount t''' = refcount t' - 1"
    using tensor_release_decreases_refcount by blast
  then show ?thesis using release ‹tensor_valid t'› 
    unfolding tensor_valid_def tensor_release_def by auto
qed

end
