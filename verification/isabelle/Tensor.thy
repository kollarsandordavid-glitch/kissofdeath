theory Tensor
  imports Complex_Main Memory
begin

primrec shape_size :: "nat list \<Rightarrow> nat" where
  "shape_size [] = 1" |
  "shape_size (d # ds) = d * shape_size ds"

lemma shape_size_positive:
  assumes "\<forall>d \<in> set shape. d > 0"
  shows "shape_size shape > 0"
  using assms by (induction shape) auto

fun compute_strides :: "nat list \<Rightarrow> nat list" where
  "compute_strides [] = []" |
  "compute_strides [x] = [1]" |
  "compute_strides (x # xs) =
    (case compute_strides xs of
       [] \<Rightarrow> [1]
     | s # ss \<Rightarrow> (s * x) # (s # ss))"

datatype tensor_error = OutOfBounds | ShapeMismatch | InvalidAxis | TensorOverflow | AllocationFailed | DivisionByZero

datatype cow_state = Exclusive | Shared

record refcount_state =
  rc_count :: nat

record mutex_state =
  mtx_locked :: bool
  mtx_owner_id :: nat

definition mutex_init :: "mutex_state" where
  "mutex_init \<equiv> \<lparr> mtx_locked = False, mtx_owner_id = 0 \<rparr>"

definition mutex_lock :: "nat \<Rightarrow> mutex_state \<Rightarrow> mutex_state" where
  "mutex_lock tid m \<equiv> \<lparr> mtx_locked = True, mtx_owner_id = tid \<rparr>"

definition mutex_unlock :: "mutex_state \<Rightarrow> mutex_state" where
  "mutex_unlock m \<equiv> \<lparr> mtx_locked = False, mtx_owner_id = 0 \<rparr>"

definition refcount_init :: "refcount_state" where
  "refcount_init \<equiv> \<lparr> rc_count = 1 \<rparr>"

definition refcount_increment :: "refcount_state \<Rightarrow> refcount_state" where
  "refcount_increment rc \<equiv> \<lparr> rc_count = rc_count rc + 1 \<rparr>"

record ('shape) tensor_spec =
  data_vec :: "nat list"
  tensor_refcount :: refcount_state
  tensor_cow_state :: cow_state
  tensor_mutex :: mutex_state
  shape_constraint :: "length data_vec = shape_size shape"

definition tensor_init :: "nat list \<Rightarrow> ('shape) tensor_spec" where
  "tensor_init shape \<equiv> \<lparr>
    data_vec = replicate (shape_size shape) 0,
    tensor_refcount = refcount_init,
    tensor_cow_state = Exclusive,
    tensor_mutex = mutex_init,
    shape_constraint = by simp \<rparr>"

definition tensor_retain :: "('shape) tensor_spec \<Rightarrow> ('shape) tensor_spec" where
  "tensor_retain t \<equiv> t\<lparr> tensor_refcount := refcount_increment (tensor_refcount t),
                         tensor_cow_state := Shared \<rparr>"

definition tensor_mark_shared :: "('shape) tensor_spec \<Rightarrow> ('shape) tensor_spec" where
  "tensor_mark_shared t \<equiv> t\<lparr> tensor_cow_state := Shared \<rparr>"

definition copy_data_vec :: "nat list \<Rightarrow> nat list" where
  "copy_data_vec xs \<equiv> map id xs"

definition tensor_ensure_writable :: "('shape) tensor_spec \<Rightarrow> (('shape) tensor_spec \<times> bool)" where
  "tensor_ensure_writable t \<equiv>
    (case tensor_cow_state t of
       Exclusive \<Rightarrow> (t, False)
     | Shared \<Rightarrow> (\<lparr> data_vec = copy_data_vec (data_vec t),
                    tensor_refcount = refcount_init,
                    tensor_cow_state = Exclusive,
                    tensor_mutex = mutex_init,
                    shape_constraint = shape_constraint t \<rparr>, True))"

lemma copy_data_vec_preserves_values:
  "copy_data_vec xs = xs"
  by (simp add: copy_data_vec_def)

lemma ensure_writable_fresh_data:
  "tensor_cow_state t = Shared \<Longrightarrow>
   data_vec (fst (tensor_ensure_writable t)) = copy_data_vec (data_vec t)"
  by (simp add: tensor_ensure_writable_def)

lemma ensure_writable_exclusive:
  "tensor_cow_state (fst (tensor_ensure_writable t)) = Exclusive"
  by (simp add: tensor_ensure_writable_def split: cow_state.splits)

lemma ensure_writable_fresh_refcount:
  "snd (tensor_ensure_writable t) = True \<Longrightarrow>
   rc_count (tensor_refcount (fst (tensor_ensure_writable t))) = 1"
  by (simp add: tensor_ensure_writable_def refcount_init_def split: cow_state.splits)

lemma ensure_writable_fresh_mutex:
  "snd (tensor_ensure_writable t) = True \<Longrightarrow>
   mtx_locked (tensor_mutex (fst (tensor_ensure_writable t))) = False"
  by (simp add: tensor_ensure_writable_def mutex_init_def split: cow_state.splits)

lemma cow_writer_gets_fresh_resources:
  "tensor_cow_state t = Shared \<Longrightarrow>
   let result = fst (tensor_ensure_writable t)
   in rc_count (tensor_refcount result) = 1 \<and>
      tensor_cow_state result = Exclusive \<and>
      mtx_locked (tensor_mutex result) = False"
  by (simp add: tensor_ensure_writable_def refcount_init_def mutex_init_def)

definition tensor_view :: "('shape) tensor_spec \<Rightarrow> ('shape) tensor_spec" where
  "tensor_view t \<equiv> tensor_retain (tensor_mark_shared t)"

lemma view_shares_data:
  "data_vec (tensor_view t) = data_vec t"
  by (simp add: tensor_view_def tensor_retain_def tensor_mark_shared_def)

lemma view_increments_refcount:
  "rc_count (tensor_refcount (tensor_view t)) = rc_count (tensor_refcount t) + 1"
  by (simp add: tensor_view_def tensor_retain_def tensor_mark_shared_def refcount_increment_def)

lemma view_marks_shared:
  "tensor_cow_state (tensor_view t) = Shared"
  by (simp add: tensor_view_def tensor_retain_def tensor_mark_shared_def)

definition tensor_release :: "('shape) tensor_spec \<Rightarrow> ('shape) tensor_spec option" where
  "tensor_release t \<equiv>
    (case rc_count (tensor_refcount t) of
       0 \<Rightarrow> None
     | Suc 0 \<Rightarrow> None
     | Suc (Suc n) \<Rightarrow> Some (t\<lparr> tensor_refcount := \<lparr> rc_count = Suc n \<rparr> \<rparr>))"

lemma cow_aliases_keep_shared:
  "let view1 = tensor_view t; view2 = tensor_view view1
   in tensor_cow_state view1 = Shared \<and> tensor_cow_state view2 = Shared"
  by (simp add: tensor_view_def tensor_retain_def tensor_mark_shared_def)

lemma cow_isolation:
  "let view1 = tensor_view t; modified = fst (tensor_ensure_writable view1)
   in tensor_cow_state modified = Exclusive"
  by (simp add: tensor_view_def tensor_retain_def tensor_mark_shared_def tensor_ensure_writable_def)

lemma mutex_unlock_once:
  "let locked = mutex_lock 1 (tensor_mutex t);
       unlocked = mutex_unlock locked
   in mtx_locked unlocked = False"
  by (simp add: mutex_lock_def mutex_unlock_def)

fun compute_flat_index :: "nat list \<Rightarrow> nat list \<Rightarrow> nat" where
  "compute_flat_index [] [] = 0" |
  "compute_flat_index (i # is) (s # ss) = i * s + compute_flat_index is ss" |
  "compute_flat_index _ _ = 0"

definition tensor_get :: "('shape) tensor_spec \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat" where
  "tensor_get t shape indices \<equiv>
    let strides = compute_strides shape;
        flat_idx = compute_flat_index indices strides
    in if flat_idx < length (data_vec t)
       then data_vec t ! flat_idx
       else 0"

definition tensor_set :: "('shape) tensor_spec \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> ('shape) tensor_spec" where
  "tensor_set t shape indices value \<equiv>
    let strides = compute_strides shape;
        flat_idx = compute_flat_index indices strides
    in if flat_idx < length (data_vec t)
       then t\<lparr> data_vec := (data_vec t)[flat_idx := value] \<rparr>
       else t"

definition tensor_fill :: "('shape) tensor_spec \<Rightarrow> nat \<Rightarrow> ('shape) tensor_spec" where
  "tensor_fill t value \<equiv> t\<lparr> data_vec := replicate (length (data_vec t)) value \<rparr>"

definition tensor_add_pointwise :: "('shape) tensor_spec \<Rightarrow> ('shape) tensor_spec \<Rightarrow> ('shape) tensor_spec" where
  "tensor_add_pointwise t1 t2 \<equiv>
    t1\<lparr> data_vec := map (\<lambda>(x, y). x + y) (zip (data_vec t1) (data_vec t2)) \<rparr>"

definition tensor_sub_pointwise :: "('shape) tensor_spec \<Rightarrow> ('shape) tensor_spec \<Rightarrow> ('shape) tensor_spec" where
  "tensor_sub_pointwise t1 t2 \<equiv>
    t1\<lparr> data_vec := map (\<lambda>(x, y). x - y) (zip (data_vec t1) (data_vec t2)) \<rparr>"

definition tensor_mul_pointwise :: "('shape) tensor_spec \<Rightarrow> ('shape) tensor_spec \<Rightarrow> ('shape) tensor_spec" where
  "tensor_mul_pointwise t1 t2 \<equiv>
    t1\<lparr> data_vec := map (\<lambda>(x, y). x * y) (zip (data_vec t1) (data_vec t2)) \<rparr>"

definition tensor_scalar_add :: "('shape) tensor_spec \<Rightarrow> nat \<Rightarrow> ('shape) tensor_spec" where
  "tensor_scalar_add t scalar \<equiv>
    t\<lparr> data_vec := map (\<lambda>x. x + scalar) (data_vec t) \<rparr>"

definition tensor_scalar_mul :: "('shape) tensor_spec \<Rightarrow> nat \<Rightarrow> ('shape) tensor_spec" where
  "tensor_scalar_mul t scalar \<equiv>
    t\<lparr> data_vec := map (\<lambda>x. x * scalar) (data_vec t) \<rparr>"

definition tensor_sum_all :: "('shape) tensor_spec \<Rightarrow> nat" where
  "tensor_sum_all t \<equiv> sum_list (data_vec t)"

definition tensor_max_element :: "('shape) tensor_spec \<Rightarrow> nat" where
  "tensor_max_element t \<equiv> fold max (data_vec t) 0"

definition tensor_min_element :: "('shape) tensor_spec \<Rightarrow> nat" where
  "tensor_min_element t \<equiv> fold min (data_vec t) 1000000000"

theorem tensor_retain_increases_refcount:
  "rc_count (tensor_refcount (tensor_retain t)) = rc_count (tensor_refcount t) + 1"
  by (simp add: tensor_retain_def refcount_increment_def)

theorem tensor_retain_marks_shared:
  "tensor_cow_state (tensor_retain t) = Shared"
  by (simp add: tensor_retain_def)

theorem tensor_add_comm:
  assumes "length (data_vec t1) = length (data_vec t2)"
  shows "data_vec (tensor_add_pointwise t1 t2) = data_vec (tensor_add_pointwise t2 t1)"
  using assms by (simp add: tensor_add_pointwise_def zip_commute case_prod_unfold add.commute)

theorem tensor_add_assoc:
  assumes "length (data_vec t1) = length (data_vec t2)"
  and "length (data_vec t2) = length (data_vec t3)"
  shows "data_vec (tensor_add_pointwise (tensor_add_pointwise t1 t2) t3) =
         data_vec (tensor_add_pointwise t1 (tensor_add_pointwise t2 t3))"
  using assms by (simp add: tensor_add_pointwise_def add.assoc)

theorem tensor_mul_comm:
  assumes "length (data_vec t1) = length (data_vec t2)"
  shows "data_vec (tensor_mul_pointwise t1 t2) = data_vec (tensor_mul_pointwise t2 t1)"
  using assms by (simp add: tensor_mul_pointwise_def zip_commute case_prod_unfold mult.commute)

theorem tensor_mul_assoc:
  assumes "length (data_vec t1) = length (data_vec t2)"
  and "length (data_vec t2) = length (data_vec t3)"
  shows "data_vec (tensor_mul_pointwise (tensor_mul_pointwise t1 t2) t3) =
         data_vec (tensor_mul_pointwise t1 (tensor_mul_pointwise t2 t3))"
  using assms by (simp add: tensor_mul_pointwise_def mult.assoc)

theorem tensor_scalar_mul_distributive:
  assumes "length (data_vec t1) = length (data_vec t2)"
  shows "data_vec (tensor_scalar_mul (tensor_add_pointwise t1 t2) s) =
         data_vec (tensor_add_pointwise (tensor_scalar_mul t1 s) (tensor_scalar_mul t2 s))"
  using assms by (simp add: tensor_scalar_mul_def tensor_add_pointwise_def ring_distribs)

theorem tensor_fill_all_equal:
  assumes "i < length (data_vec t)" and "j < length (data_vec t)"
  shows "data_vec (tensor_fill t v) ! i = data_vec (tensor_fill t v) ! j"
  using assms by (simp add: tensor_fill_def)

theorem tensor_sum_add:
  assumes "length (data_vec t1) = length (data_vec t2)"
  shows "tensor_sum_all (tensor_add_pointwise t1 t2) =
         tensor_sum_all t1 + tensor_sum_all t2"
  using assms by (simp add: tensor_sum_all_def tensor_add_pointwise_def sum_list_addf)

definition reshape_valid :: "nat list \<Rightarrow> nat list \<Rightarrow> bool" where
  "reshape_valid old_shape new_shape \<equiv> shape_size old_shape = shape_size new_shape"

theorem reshape_preserves_size:
  assumes "reshape_valid old_shape new_shape"
  shows "shape_size old_shape = shape_size new_shape"
  using assms by (simp add: reshape_valid_def)

fun broadcast_compatible :: "nat list \<Rightarrow> nat list \<Rightarrow> bool" where
  "broadcast_compatible [] [] = True" |
  "broadcast_compatible [] (d # ds) = broadcast_compatible [] ds" |
  "broadcast_compatible (d # ds) [] = broadcast_compatible ds []" |
  "broadcast_compatible (d1 # ds1) (d2 # ds2) =
    (d1 = d2 \<or> d1 = 1 \<or> d2 = 1) \<and> broadcast_compatible ds1 ds2"

fun slice_in_bounds :: "nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> bool" where
  "slice_in_bounds [] [] [] = True" |
  "slice_in_bounds (d # ds) (s # starts) (e # ends) =
    (s \<le> e \<and> e \<le> d \<and> slice_in_bounds ds starts ends)" |
  "slice_in_bounds _ _ _ = False"

definition transpose_axes_valid :: "nat list \<Rightarrow> nat list \<Rightarrow> bool" where
  "transpose_axes_valid shape axes \<equiv>
    length shape = length axes \<and> distinct axes"

fun matmul_shapes_compatible :: "nat list \<Rightarrow> nat list \<Rightarrow> bool" where
  "matmul_shapes_compatible [m, n] [n', k] = (n = n')" |
  "matmul_shapes_compatible _ _ = False"

fun compute_matmul_output_shape :: "nat list \<Rightarrow> nat list \<Rightarrow> nat list" where
  "compute_matmul_output_shape [m, n] [n', k] = (if n = n' then [m, k] else [])" |
  "compute_matmul_output_shape _ _ = []"

fun conv2d_shapes_valid :: "nat list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "conv2d_shapes_valid [batch, in_h, in_w, in_c] [k_h, k_w, k_in_c, k_out_c] stride padding =
    (in_c = k_in_c \<and> stride > 0 \<and> k_h \<le> in_h + 2 * padding \<and> k_w \<le> in_w + 2 * padding)" |
  "conv2d_shapes_valid _ _ _ _ = False"

fun pool2d_shapes_valid :: "nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "pool2d_shapes_valid [batch, in_h, in_w, channels] pool_h pool_w stride =
    (stride > 0 \<and> pool_h \<le> in_h \<and> pool_w \<le> in_w)" |
  "pool2d_shapes_valid _ _ _ _ = False"

theorem broadcast_symmetric:
  "broadcast_compatible s1 s2 \<Longrightarrow> broadcast_compatible s2 s1"
  by (induction s1 s2 rule: broadcast_compatible.induct) auto

theorem matmul_output_size_positive:
  assumes "matmul_shapes_compatible s1 s2"
  shows "shape_size (compute_matmul_output_shape s1 s2) > 0"
  using assms by (cases s1; cases s2) auto

end
