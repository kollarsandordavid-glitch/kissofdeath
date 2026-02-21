theory TensorModel
  imports Complex_Main "HOL-Library.Countable"
begin

datatype dtype = F32 | F64 | I32 | I64 | U32 | U64 | BOOL

datatype layout = ROW_MAJOR | COLUMN_MAJOR | STRIDED

datatype device = CPU | GPU | TPU

datatype ownership = OWNED | BORROWED | VIEW

primrec shape_size :: "nat list \<Rightarrow> nat" where
  "shape_size [] = 1"
| "shape_size (d # ds) = d * shape_size ds"

record ('shape) tensor =
  data_vec :: "nat list"
  layout :: layout
  device :: device
  ownership :: ownership

definition tensor_shape_valid :: "nat list \<Rightarrow> ('shape) tensor \<Rightarrow> bool" where
  "tensor_shape_valid shape t \<equiv> length (data_vec t) = shape_size shape"

lemma shape_size_positive: "shape_size shape \<ge> 1"
  by (induction shape) auto

theorem shape_consistency:
  assumes "tensor_shape_valid shape t"
  shows "length (data_vec t) = shape_size shape"
  using assms by (simp add: tensor_shape_valid_def)

definition memory_bounds :: "nat list \<Rightarrow> ('shape) tensor \<Rightarrow> nat \<Rightarrow> bool" where
  "memory_bounds shape t i \<equiv> 
    tensor_shape_valid shape t \<and> i < length (data_vec t)"

theorem memory_bounds_correct:
  assumes "tensor_shape_valid shape t"
  assumes "i < shape_size shape"
  shows "memory_bounds shape t i"
  using assms by (simp add: memory_bounds_def tensor_shape_valid_def)

definition layout_transform :: "('shape) tensor \<Rightarrow> layout \<Rightarrow> ('shape) tensor" where
  "layout_transform t new_layout \<equiv> t\<lparr> layout := new_layout \<rparr>"

theorem layout_transform_preserves_data:
  "data_vec (layout_transform t new_layout) = data_vec t"
  by (simp add: layout_transform_def)

theorem layout_transform_preserves_device:
  "device (layout_transform t new_layout) = device t"
  by (simp add: layout_transform_def)

theorem layout_transform_changes_layout:
  "layout (layout_transform t new_layout) = new_layout"
  by (simp add: layout_transform_def)

definition tensor_map :: "(nat \<Rightarrow> nat) \<Rightarrow> ('shape) tensor \<Rightarrow> ('shape) tensor" where
  "tensor_map f t \<equiv> t\<lparr> data_vec := map f (data_vec t) \<rparr>"

theorem tensor_map_preserves_length:
  "length (data_vec (tensor_map f t)) = length (data_vec t)"
  by (simp add: tensor_map_def)

definition tensor_zipWith :: "(nat \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow> ('shape) tensor \<Rightarrow> ('shape) tensor \<Rightarrow> ('shape) tensor" where
  "tensor_zipWith f t1 t2 \<equiv> 
    t1\<lparr> data_vec := map (\<lambda>(x, y). f x y) (zip (data_vec t1) (data_vec t2)) \<rparr>"

definition tensor_fold :: "(nat \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> ('shape) tensor \<Rightarrow> nat" where
  "tensor_fold f z t \<equiv> foldl f z (data_vec t)"

definition tensor_replicate :: "nat list \<Rightarrow> nat \<Rightarrow> ('shape) tensor" where
  "tensor_replicate shape v \<equiv> 
    \<lparr> data_vec = replicate (shape_size shape) v
    , layout = ROW_MAJOR
    , device = CPU
    , ownership = OWNED \<rparr>"

theorem tensor_replicate_all_equal:
  assumes "i < shape_size shape"
  assumes "j < shape_size shape"
  shows "data_vec (tensor_replicate shape v) ! i = 
         data_vec (tensor_replicate shape v) ! j"
  by (simp add: tensor_replicate_def)

definition tensor_zero :: "nat list \<Rightarrow> ('shape) tensor" where
  "tensor_zero shape \<equiv> tensor_replicate shape 0"

theorem tensor_zero_is_zero:
  assumes "i < shape_size shape"
  shows "data_vec (tensor_zero shape) ! i = 0"
  by (simp add: tensor_zero_def tensor_replicate_def)

definition tensor_add :: "('shape) tensor \<Rightarrow> ('shape) tensor \<Rightarrow> ('shape) tensor" where
  "tensor_add t1 t2 \<equiv> tensor_zipWith (+) t1 t2"

theorem tensor_add_comm:
  assumes "length (data_vec t1) = length (data_vec t2)"
  shows "data_vec (tensor_add t1 t2) = data_vec (tensor_add t2 t1)"
  by (simp add: tensor_add_def tensor_zipWith_def zip_commute add.commute)

theorem tensor_add_assoc:
  assumes "length (data_vec t1) = length (data_vec t2)"
  assumes "length (data_vec t2) = length (data_vec t3)"
  shows "data_vec (tensor_add (tensor_add t1 t2) t3) = 
         data_vec (tensor_add t1 (tensor_add t2 t3))"
  by (simp add: tensor_add_def tensor_zipWith_def add.assoc)

definition tensor_mul :: "('shape) tensor \<Rightarrow> ('shape) tensor \<Rightarrow> ('shape) tensor" where
  "tensor_mul t1 t2 \<equiv> tensor_zipWith (*) t1 t2"

theorem tensor_mul_comm:
  assumes "length (data_vec t1) = length (data_vec t2)"
  shows "data_vec (tensor_mul t1 t2) = data_vec (tensor_mul t2 t1)"
  by (simp add: tensor_mul_def tensor_zipWith_def mult.commute)

theorem tensor_mul_assoc:
  assumes "length (data_vec t1) = length (data_vec t2)"
  assumes "length (data_vec t2) = length (data_vec t3)"
  shows "data_vec (tensor_mul (tensor_mul t1 t2) t3) = 
         data_vec (tensor_mul t1 (tensor_mul t2 t3))"
  by (simp add: tensor_mul_def tensor_zipWith_def mult.assoc)

definition tensor_scalar_mul :: "nat \<Rightarrow> ('shape) tensor \<Rightarrow> ('shape) tensor" where
  "tensor_scalar_mul scalar t \<equiv> tensor_map (\<lambda>x. scalar * x) t"

theorem tensor_scalar_mul_distributive:
  assumes "length (data_vec t1) = length (data_vec t2)"
  shows "data_vec (tensor_scalar_mul s (tensor_add t1 t2)) =
         data_vec (tensor_add (tensor_scalar_mul s t1) (tensor_scalar_mul s t2))"
  by (simp add: tensor_scalar_mul_def tensor_add_def tensor_map_def tensor_zipWith_def
      ring_distribs)

definition tensor_sum :: "('shape) tensor \<Rightarrow> nat" where
  "tensor_sum t \<equiv> tensor_fold (+) 0 t"

theorem tensor_sum_zero:
  "tensor_sum (tensor_zero shape) = 0"
  by (simp add: tensor_sum_def tensor_fold_def tensor_zero_def tensor_replicate_def)

theorem tensor_sum_add:
  assumes "length (data_vec t1) = length (data_vec t2)"
  shows "tensor_sum (tensor_add t1 t2) = tensor_sum t1 + tensor_sum t2"
  by (simp add: tensor_sum_def tensor_add_def tensor_fold_def tensor_zipWith_def)

definition aliasing_rule :: "('shape) tensor \<Rightarrow> ('shape) tensor \<Rightarrow> bool" where
  "aliasing_rule t1 t2 \<equiv>
    ownership t1 = OWNED \<and> ownership t2 = OWNED \<longrightarrow>
    data_vec t1 \<noteq> data_vec t2"

definition device_affinity_preserving :: 
  "('shape) tensor \<Rightarrow> (('shape) tensor \<Rightarrow> ('shape) tensor) \<Rightarrow> 
   (('shape) tensor \<Rightarrow> bool) \<Rightarrow> bool" where
  "device_affinity_preserving t op dev_preserves \<equiv>
    dev_preserves t \<longrightarrow> device (op t) = device t"

end
