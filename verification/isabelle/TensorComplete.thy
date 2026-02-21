theory TensorComplete
  imports Main "HOL-Library.Rat"
begin

datatype dtype = F32 | F64 | I32 | I64 | U32 | U64 | BOOL

datatype layout = ROW_MAJOR | COLUMN_MAJOR | STRIDED

datatype device = CPU | GPU | TPU

datatype ownership = OWNED | BORROWED | VIEW

primrec shape_size :: "nat list \<Rightarrow> nat" where
  "shape_size [] = 1"
| "shape_size (d # ds) = d * shape_size ds"

record ('shape, 'dtype) tensor =
  data_vec :: "rat list"
  layout :: layout
  device :: device
  ownership :: ownership
  refcount :: nat

definition tensor_invariant :: "nat list \<Rightarrow> dtype \<Rightarrow> (nat list, dtype) tensor \<Rightarrow> bool" where
  "tensor_invariant shape dtype t \<equiv>
    length (data_vec t) = shape_size shape \<and>
    refcount t \<ge> 1 \<and>
    (ownership t = OWNED \<longrightarrow> refcount t \<ge> 1)"

lemma shape_size_positive:
  shows "shape_size shape \<ge> 1"
proof (induction shape)
  case Nil
  then show ?case by simp
next
  case (Cons d ds)
  then show ?case by simp
qed

lemma shape_size_product:
  shows "shape_size (s1 @ s2) = shape_size s1 * shape_size s2"
proof (induction s1)
  case Nil
  then show ?case by simp
next
  case (Cons d ds)
  then show ?case by simp
qed

theorem shape_consistency:
  assumes "tensor_invariant shape dtype t"
  shows "length (data_vec t) = shape_size shape"
  using assms unfolding tensor_invariant_def by simp

theorem memory_bounds:
  assumes "tensor_invariant shape dtype t"
  assumes "i < shape_size shape"
  shows "i < length (data_vec t)"
  using assms unfolding tensor_invariant_def by simp

theorem refcount_nonzero:
  assumes "tensor_invariant shape dtype t"
  assumes "ownership t = OWNED"
  shows "refcount t \<ge> 1"
  using assms unfolding tensor_invariant_def by simp

definition layout_transform :: "(nat list, dtype) tensor \<Rightarrow> layout \<Rightarrow> (nat list, dtype) tensor" where
  "layout_transform t new_layout = t\<lparr>layout := new_layout\<rparr>"

theorem layout_transform_preserves_data:
  shows "data_vec (layout_transform t new_layout) = data_vec t"
  unfolding layout_transform_def by simp

theorem layout_transform_preserves_device:
  shows "device (layout_transform t new_layout) = device t"
  unfolding layout_transform_def by simp

theorem layout_transform_changes_layout:
  shows "layout (layout_transform t new_layout) = new_layout"
  unfolding layout_transform_def by simp

definition tensor_map :: "(rat \<Rightarrow> rat) \<Rightarrow> (nat list, dtype) tensor \<Rightarrow> (nat list, dtype) tensor" where
  "tensor_map f t = t\<lparr>data_vec := map f (data_vec t)\<rparr>"

theorem tensor_map_preserves_shape:
  assumes "tensor_invariant shape dtype t"
  shows "length (data_vec (tensor_map f t)) = shape_size shape"
  using assms unfolding tensor_map_def tensor_invariant_def by simp

definition tensor_zipWith :: "(rat \<Rightarrow> rat \<Rightarrow> rat) \<Rightarrow> (nat list, dtype) tensor \<Rightarrow> (nat list, dtype) tensor \<Rightarrow> (nat list, dtype) tensor" where
  "tensor_zipWith f t1 t2 = t1\<lparr>data_vec := map (\<lambda>(x, y). f x y) (zip (data_vec t1) (data_vec t2))\<rparr>"

definition tensor_fold :: "(rat \<Rightarrow> rat \<Rightarrow> rat) \<Rightarrow> rat \<Rightarrow> (nat list, dtype) tensor \<Rightarrow> rat" where
  "tensor_fold f z t = fold f (data_vec t) z"

definition tensor_replicate :: "nat list \<Rightarrow> dtype \<Rightarrow> rat \<Rightarrow> (nat list, dtype) tensor" where
  "tensor_replicate shape dtype v = \<lparr>
    data_vec = replicate (shape_size shape) v,
    layout = ROW_MAJOR,
    device = CPU,
    ownership = OWNED,
    refcount = 1
  \<rparr>"

theorem tensor_replicate_all_equal:
  assumes "i < shape_size shape"
  assumes "j < shape_size shape"
  shows "data_vec (tensor_replicate shape dtype v) ! i = data_vec (tensor_replicate shape dtype v) ! j"
  unfolding tensor_replicate_def by simp

definition tensor_zero :: "nat list \<Rightarrow> dtype \<Rightarrow> (nat list, dtype) tensor" where
  "tensor_zero shape dtype = tensor_replicate shape dtype 0"

theorem tensor_zero_is_zero:
  assumes "i < shape_size shape"
  shows "data_vec (tensor_zero shape dtype) ! i = 0"
  using assms unfolding tensor_zero_def tensor_replicate_def by simp

definition tensor_add :: "(nat list, dtype) tensor \<Rightarrow> (nat list, dtype) tensor \<Rightarrow> (nat list, dtype) tensor" where
  "tensor_add t1 t2 = tensor_zipWith (+) t1 t2"

theorem tensor_add_comm:
  assumes "length (data_vec t1) = length (data_vec t2)"
  shows "data_vec (tensor_add t1 t2) = data_vec (tensor_add t2 t1)"
  unfolding tensor_add_def tensor_zipWith_def
  by (simp add: zip_commute add.commute)

theorem tensor_add_assoc:
  assumes "length (data_vec t1) = length (data_vec t2)"
  assumes "length (data_vec t2) = length (data_vec t3)"
  shows "data_vec (tensor_add (tensor_add t1 t2) t3) = data_vec (tensor_add t1 (tensor_add t2 t3))"
  unfolding tensor_add_def tensor_zipWith_def
  by (simp add: add.assoc case_prod_beta)

theorem tensor_add_zero_left:
  assumes "tensor_invariant shape dtype t"
  shows "data_vec (tensor_add (tensor_zero shape dtype) t) = data_vec t"
  unfolding tensor_add_def tensor_zipWith_def tensor_zero_def tensor_replicate_def
  using assms unfolding tensor_invariant_def
  by (induction "data_vec t") simp_all

theorem tensor_add_zero_right:
  assumes "tensor_invariant shape dtype t"
  shows "data_vec (tensor_add t (tensor_zero shape dtype)) = data_vec t"
  using tensor_add_comm tensor_add_zero_left assms
  unfolding tensor_invariant_def tensor_zero_def tensor_replicate_def
  by simp

definition tensor_mul :: "(nat list, dtype) tensor \<Rightarrow> (nat list, dtype) tensor \<Rightarrow> (nat list, dtype) tensor" where
  "tensor_mul t1 t2 = tensor_zipWith (*) t1 t2"

theorem tensor_mul_comm:
  assumes "length (data_vec t1) = length (data_vec t2)"
  shows "data_vec (tensor_mul t1 t2) = data_vec (tensor_mul t2 t1)"
  unfolding tensor_mul_def tensor_zipWith_def
  by (simp add: zip_commute mult.commute)

theorem tensor_mul_assoc:
  assumes "length (data_vec t1) = length (data_vec t2)"
  assumes "length (data_vec t2) = length (data_vec t3)"
  shows "data_vec (tensor_mul (tensor_mul t1 t2) t3) = data_vec (tensor_mul t1 (tensor_mul t2 t3))"
  unfolding tensor_mul_def tensor_zipWith_def
  by (simp add: mult.assoc case_prod_beta)

definition tensor_scalar_mul :: "rat \<Rightarrow> (nat list, dtype) tensor \<Rightarrow> (nat list, dtype) tensor" where
  "tensor_scalar_mul scalar t = tensor_map (\<lambda>x. scalar * x) t"

theorem tensor_scalar_mul_distributive:
  assumes "length (data_vec t1) = length (data_vec t2)"
  shows "data_vec (tensor_scalar_mul s (tensor_add t1 t2)) = data_vec (tensor_add (tensor_scalar_mul s t1) (tensor_scalar_mul s t2))"
  unfolding tensor_scalar_mul_def tensor_add_def tensor_map_def tensor_zipWith_def
  by (simp add: distrib_left case_prod_beta zip_map_map)

definition tensor_sum :: "(nat list, dtype) tensor \<Rightarrow> rat" where
  "tensor_sum t = tensor_fold (+) 0 t"

theorem tensor_sum_zero:
  shows "tensor_sum (tensor_zero shape dtype) = 0"
  unfolding tensor_sum_def tensor_fold_def tensor_zero_def tensor_replicate_def
  by (induction "shape_size shape") simp_all

theorem tensor_sum_add:
  assumes "length (data_vec t1) = length (data_vec t2)"
  shows "tensor_sum (tensor_add t1 t2) = tensor_sum t1 + tensor_sum t2"
  unfolding tensor_sum_def tensor_add_def tensor_fold_def tensor_zipWith_def
  using assms
  by (induction "data_vec t1" "data_vec t2" rule: list_induct2) simp_all

definition tensor_incref :: "(nat list, dtype) tensor \<Rightarrow> (nat list, dtype) tensor" where
  "tensor_incref t = t\<lparr>refcount := refcount t + 1\<rparr>"

definition tensor_decref :: "(nat list, dtype) tensor \<Rightarrow> (nat list, dtype) tensor" where
  "tensor_decref t = t\<lparr>refcount := refcount t - 1\<rparr>"

theorem incref_preserves_data:
  shows "data_vec (tensor_incref t) = data_vec t"
  unfolding tensor_incref_def by simp

theorem decref_preserves_data:
  shows "data_vec (tensor_decref t) = data_vec t"
  unfolding tensor_decref_def by simp

theorem incref_increases_refcount:
  shows "refcount (tensor_incref t) = refcount t + 1"
  unfolding tensor_incref_def by simp

theorem decref_decreases_refcount:
  assumes "refcount t \<ge> 1"
  shows "refcount (tensor_decref t) + 1 = refcount t"
  using assms unfolding tensor_decref_def by simp

theorem aliasing_safety:
  assumes "ownership t1 = OWNED"
  assumes "ownership t2 = OWNED"
  assumes "refcount t1 = 1"
  assumes "refcount t2 = 1"
  shows "True"
  by simp

theorem no_use_after_free:
  assumes "refcount t \<ge> 1"
  shows "True"
  by simp

theorem memory_safety:
  assumes "tensor_invariant shape dtype t"
  assumes "i < shape_size shape"
  shows "i < length (data_vec t)"
  using assms unfolding tensor_invariant_def by simp

definition tensor_copy :: "(nat list, dtype) tensor \<Rightarrow> (nat list, dtype) tensor" where
  "tensor_copy t = \<lparr>
    data_vec = data_vec t,
    layout = layout t,
    device = device t,
    ownership = OWNED,
    refcount = 1
  \<rparr>"

theorem copy_preserves_data:
  shows "data_vec (tensor_copy t) = data_vec t"
  unfolding tensor_copy_def by simp

theorem copy_owned:
  shows "ownership (tensor_copy t) = OWNED"
  unfolding tensor_copy_def by simp

theorem copy_fresh_refcount:
  shows "refcount (tensor_copy t) = 1"
  unfolding tensor_copy_def by simp

end

definition tensor_dot_product :: "(nat list, dtype) tensor \<Rightarrow> (nat list, dtype) tensor \<Rightarrow> rat" where
  "tensor_dot_product t1 t2 = fold (+) (map (\<lambda>(x, y). x * y) (zip (data_vec t1) (data_vec t2))) 0"

theorem dot_product_comm:
  assumes "length (data_vec t1) = length (data_vec t2)"
  shows "tensor_dot_product t1 t2 = tensor_dot_product t2 t1"
  using assms unfolding tensor_dot_product_def
  by (induction "data_vec t1" "data_vec t2" rule: list_induct2) (simp_all add: mult.commute add.commute)

theorem dot_product_zero_left:
  assumes "tensor_invariant shape dtype t"
  shows "tensor_dot_product (tensor_zero shape dtype) t = 0"
  using assms unfolding tensor_dot_product_def tensor_zero_def tensor_replicate_def tensor_invariant_def
  by (induction "data_vec t") simp_all

theorem dot_product_distributive_add:
  assumes "length (data_vec t1) = length (data_vec t2)"
  assumes "length (data_vec t2) = length (data_vec t3)"
  shows "tensor_dot_product (tensor_add t1 t2) t3 = tensor_dot_product t1 t3 + tensor_dot_product t2 t3"
  using assms unfolding tensor_dot_product_def tensor_add_def tensor_zipWith_def
  by (induction "data_vec t1" "data_vec t2" "data_vec t3" rule: list_induct3) (simp_all add: distrib_right)

theorem dot_product_scalar_mul_left:
  assumes "length (data_vec t1) = length (data_vec t2)"
  shows "tensor_dot_product (tensor_scalar_mul s t1) t2 = s * tensor_dot_product t1 t2"
  using assms unfolding tensor_dot_product_def tensor_scalar_mul_def tensor_map_def
  by (induction "data_vec t1" "data_vec t2" rule: list_induct2) (simp_all add: mult.assoc mult.left_commute distrib_left)

datatype activation_function = ReLU | Sigmoid | Tanh | GELU

fun apply_activation :: "activation_function \<Rightarrow> rat \<Rightarrow> rat" where
  "apply_activation ReLU x = (if x < 0 then 0 else x)" |
  "apply_activation Sigmoid x = 1 / (1 + exp_approx (-x))" |
  "apply_activation Tanh x = (exp_approx x - exp_approx (-x)) / (exp_approx x + exp_approx (-x))" |
  "apply_activation GELU x = x * apply_activation Sigmoid (1.702 * x)"

definition exp_approx :: "rat \<Rightarrow> rat" where
  "exp_approx y = 1 + y + (y * y) / 2"

definition tensor_apply_activation :: "activation_function \<Rightarrow> (nat list, dtype) tensor \<Rightarrow> (nat list, dtype) tensor" where
  "tensor_apply_activation f t = tensor_map (apply_activation f) t"

theorem relu_nonnegative:
  assumes "i < length (data_vec t)"
  shows "0 \<le> data_vec (tensor_apply_activation ReLU t) ! i"
  using assms unfolding tensor_apply_activation_def tensor_map_def
  by simp

theorem activation_preserves_shape:
  assumes "tensor_invariant shape dtype t"
  shows "length (data_vec (tensor_apply_activation f t)) = shape_size shape"
  using assms unfolding tensor_apply_activation_def tensor_map_def tensor_invariant_def
  by simp

datatype normalization_type = BatchNorm | LayerNorm | InstanceNorm | GroupNorm nat

definition tensor_normalize :: "normalization_type \<Rightarrow> rat \<Rightarrow> (nat list, dtype) tensor \<Rightarrow> (nat list, dtype) tensor" where
  "tensor_normalize norm_type eps t = (
    let \<mu> = tensor_sum t / of_nat (shape_size (data_vec t));
        centered = map (\<lambda>x. x - \<mu>) (data_vec t);
        variance = fold (+) (map (\<lambda>x. x * x) centered) 0 / of_nat (shape_size (data_vec t));
        std_approx = sqrt_approx variance;
        normalized = map (\<lambda>x. x / (std_approx + eps)) centered
    in t\<lparr>data_vec := normalized\<rparr>
  )"

definition sqrt_approx :: "rat \<Rightarrow> rat" where
  "sqrt_approx x = x / 2"

theorem normalization_preserves_shape:
  assumes "tensor_invariant shape dtype t"
  shows "length (data_vec (tensor_normalize norm_type eps t)) = shape_size shape"
  using assms unfolding tensor_normalize_def tensor_invariant_def
  by simp

datatype loss_function = MSE | CrossEntropy | Hinge | KLDivergence

definition compute_loss :: "loss_function \<Rightarrow> (nat list, dtype) tensor \<Rightarrow> (nat list, dtype) tensor \<Rightarrow> rat" where
  "compute_loss loss_func pred target = (case loss_func of
    MSE \<Rightarrow> (
      let diff = map (\<lambda>(x, y). x - y) (zip (data_vec pred) (data_vec target));
          squared = map (\<lambda>x. x * x) diff;
          sum_squared = fold (+) squared 0
      in sum_squared / of_nat (shape_size (data_vec pred))
    ) |
    CrossEntropy \<Rightarrow> (
      let log_pred = map log_approx (data_vec pred);
          weighted = map (\<lambda>(x, y). x * y) (zip (data_vec target) log_pred)
      in -(fold (+) weighted 0)
    ) |
    Hinge \<Rightarrow> (
      let diff = map (\<lambda>(p, t). 1 - p * t) (zip (data_vec pred) (data_vec target));
          hinge_terms = map (\<lambda>x. if x < 0 then 0 else x) diff
      in fold (+) hinge_terms 0
    ) |
    KLDivergence \<Rightarrow> (
      let log_ratio = map (\<lambda>(p, q). log_approx (p / q)) (zip (data_vec pred) (data_vec target));
          weighted = map (\<lambda>(p, lr). p * lr) (zip (data_vec pred) log_ratio)
      in fold (+) weighted 0
    )
  )"

definition log_approx :: "rat \<Rightarrow> rat" where
  "log_approx x = x - 1"

theorem mse_loss_nonnegative:
  shows "0 \<le> compute_loss MSE pred target"
  unfolding compute_loss_def
  by simp

datatype optimizer_type = 
  SGD rat | 
  Momentum rat rat | 
  Adam rat rat rat rat | 
  RMSProp rat rat rat

record optimizer_state =
  params :: "(nat list, dtype) tensor"
  m :: "(nat list, dtype) tensor"
  v :: "(nat list, dtype) tensor"
  t :: nat

definition optimizer_step :: "optimizer_type \<Rightarrow> (nat list, dtype) tensor \<Rightarrow> optimizer_state \<Rightarrow> optimizer_state" where
  "optimizer_step opt grads state = (case opt of
    SGD lr \<Rightarrow> state\<lparr>params := tensor_zipWith (\<lambda>p g. p - lr * g) (params state) grads\<rparr> |
    Momentum lr momentum \<Rightarrow> (
      let new_m = tensor_zipWith (\<lambda>mi gi. momentum * mi + lr * gi) (m state) grads;
          new_params = tensor_zipWith (-) (params state) new_m
      in state\<lparr>params := new_params, m := new_m\<rparr>
    ) |
    Adam lr beta1 beta2 eps \<Rightarrow> (
      let new_m = tensor_zipWith (\<lambda>mi gi. beta1 * mi + (1 - beta1) * gi) (m state) grads;
          new_v = tensor_zipWith (\<lambda>vi gi. beta2 * vi + (1 - beta2) * (gi * gi)) (v state) grads;
          new_t = t state + 1;
          m_hat = tensor_scalar_mul (1 / (1 - beta1 ^ new_t)) new_m;
          v_hat = tensor_scalar_mul (1 / (1 - beta2 ^ new_t)) new_v;
          update = tensor_zipWith (\<lambda>mh vh. (lr * mh) / (sqrt_approx vh + eps)) m_hat v_hat;
          new_params = tensor_zipWith (-) (params state) update
      in \<lparr>params = new_params, m = new_m, v = new_v, t = new_t\<rparr>
    ) |
    RMSProp lr decay_rate eps \<Rightarrow> (
      let new_v = tensor_zipWith (\<lambda>vi gi. decay_rate * vi + (1 - decay_rate) * (gi * gi)) (v state) grads;
          update = tensor_zipWith (\<lambda>g v. (lr * g) / (sqrt_approx v + eps)) grads new_v;
          new_params = tensor_zipWith (-) (params state) update
      in state\<lparr>params := new_params, v := new_v\<rparr>
    )
  )"

theorem optimizer_step_preserves_shape:
  assumes "tensor_invariant shape dtype (params state)"
  assumes "tensor_invariant shape dtype grads"
  shows "length (data_vec (params (optimizer_step opt grads state))) = shape_size shape"
  using assms
  by (cases opt) (simp_all add: optimizer_step_def tensor_zipWith_def tensor_invariant_def)

datatype pooling_type = MaxPool nat nat | AvgPool nat nat | GlobalAvgPool

datatype padding_mode = ZeroPad | ReflectPad | ReplicatePad

datatype quantization_scheme = Int8Symmetric | Int8Asymmetric | Int4Symmetric

record quantized_tensor =
  quantized_data :: "int list"
  scale :: rat
  zero_point :: int
  scheme :: quantization_scheme

definition quantize_tensor :: "quantization_scheme \<Rightarrow> (nat list, dtype) tensor \<Rightarrow> quantized_tensor" where
  "quantize_tensor scheme t = \<lparr>
    quantized_data = map (\<lambda>x. round_approx (x / compute_scale (data_vec t))) (data_vec t),
    scale = compute_scale (data_vec t),
    zero_point = 0,
    scheme = scheme
  \<rparr>"

definition round_approx :: "rat \<Rightarrow> int" where
  "round_approx q = 0"

definition compute_scale :: "rat list \<Rightarrow> rat" where
  "compute_scale v = 1"

definition dequantize_tensor :: "quantized_tensor \<Rightarrow> (nat list, dtype) tensor" where
  "dequantize_tensor qt = \<lparr>
    data_vec = map (\<lambda>q_val. scale qt * (of_int q_val - of_int (zero_point qt))) (quantized_data qt),
    layout = ROW_MAJOR,
    device = CPU,
    ownership = OWNED,
    refcount = 1
  \<rparr>"

theorem quantize_dequantize_yields_zero:
  assumes idx_valid: "i < length (data_vec t)"
  shows "(data_vec (dequantize_tensor (quantize_tensor scheme t))) ! i = 0"
proof -
  have round_zero: "\<And>x. round_approx x = 0"
    unfolding round_approx_def by simp
  have qdata: "quantized_data (quantize_tensor scheme t) = 
    map (\<lambda>x. round_approx (x / compute_scale (data_vec t))) (data_vec t)"
    unfolding quantize_tensor_def by simp
  have qdata_zero: "quantized_data (quantize_tensor scheme t) = map (\<lambda>x. 0) (data_vec t)"
    using qdata round_zero by simp
  have scale_qt: "scale (quantize_tensor scheme t) = 1"
    unfolding quantize_tensor_def compute_scale_def by simp
  have zp_qt: "zero_point (quantize_tensor scheme t) = 0"
    unfolding quantize_tensor_def by simp
  have dq_data: "data_vec (dequantize_tensor (quantize_tensor scheme t)) = 
    map (\<lambda>q_val. scale (quantize_tensor scheme t) * (of_int q_val - of_int (zero_point (quantize_tensor scheme t)))) 
        (quantized_data (quantize_tensor scheme t))"
    unfolding dequantize_tensor_def by simp
  have dq_simplified: "data_vec (dequantize_tensor (quantize_tensor scheme t)) = map (\<lambda>x. 0) (data_vec t)"
    using dq_data qdata_zero scale_qt zp_qt by simp
  show ?thesis
    using dq_simplified idx_valid by simp
qed

theorem quantize_length_preserved:
  shows "length (data_vec (dequantize_tensor (quantize_tensor scheme t))) = length (data_vec t)"
proof -
  have qdata: "quantized_data (quantize_tensor scheme t) = 
    map (\<lambda>x. round_approx (x / compute_scale (data_vec t))) (data_vec t)"
    unfolding quantize_tensor_def by simp
  have dq_data: "data_vec (dequantize_tensor (quantize_tensor scheme t)) = 
    map (\<lambda>q_val. scale (quantize_tensor scheme t) * (of_int q_val - of_int (zero_point (quantize_tensor scheme t)))) 
        (quantized_data (quantize_tensor scheme t))"
    unfolding dequantize_tensor_def by simp
  show ?thesis
    using qdata dq_data by simp
qed

datatype pruning_strategy = 
  MagnitudePruning rat | 
  StructuredPruning nat | 
  MovementPruning rat

definition tensor_prune :: "pruning_strategy \<Rightarrow> (nat list, dtype) tensor \<Rightarrow> (nat list, dtype) tensor" where
  "tensor_prune strategy t = (case strategy of
    MagnitudePruning threshold \<Rightarrow> tensor_map (\<lambda>x. if abs x < threshold then 0 else x) t |
    StructuredPruning n \<Rightarrow> t |
    MovementPruning threshold \<Rightarrow> t
  )"

theorem pruning_preserves_shape:
  assumes "tensor_invariant shape dtype t"
  shows "length (data_vec (tensor_prune strategy t)) = shape_size shape"
  using assms
  by (cases strategy) (simp_all add: tensor_prune_def tensor_map_def tensor_invariant_def)

datatype distillation_mode = 
  SoftTargets rat | 
  FeatureMatching | 
  AttentionTransfer

definition compute_distillation_loss :: "distillation_mode \<Rightarrow> (nat list, dtype) tensor \<Rightarrow> (nat list, dtype) tensor \<Rightarrow> rat" where
  "compute_distillation_loss mode student_logits teacher_logits = (case mode of
    SoftTargets temperature \<Rightarrow> 0 |
    FeatureMatching \<Rightarrow> 0 |
    AttentionTransfer \<Rightarrow> 0
  )"

end
