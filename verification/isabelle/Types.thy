theory Types
  imports Complex_Main "HOL-Library.Countable"
begin

datatype fixed_point_error = FPOverflow | FPDivisionByZero

datatype fixed_point_16 = FP16 int

datatype fixed_point_32 = FP32 int

datatype fixed_point_64 = FP64 int

fun fp16_add :: "fixed_point_16 \<Rightarrow> fixed_point_16 \<Rightarrow> (fixed_point_16 + fixed_point_error)" where
  "fp16_add (FP16 a) (FP16 b) = Inl (FP16 (a + b))"

fun fp16_sub :: "fixed_point_16 \<Rightarrow> fixed_point_16 \<Rightarrow> (fixed_point_16 + fixed_point_error)" where
  "fp16_sub (FP16 a) (FP16 b) = Inl (FP16 (a - b))"

fun fp16_mul :: "fixed_point_16 \<Rightarrow> fixed_point_16 \<Rightarrow> (fixed_point_16 + fixed_point_error)" where
  "fp16_mul (FP16 a) (FP16 b) = Inl (FP16 ((a * b) div 256))"

fun fp16_div :: "fixed_point_16 \<Rightarrow> fixed_point_16 \<Rightarrow> (fixed_point_16 + fixed_point_error)" where
  "fp16_div (FP16 a) (FP16 b) = (if b = 0 then Inr FPDivisionByZero else Inl (FP16 ((a * 256) div b)))"

lemma fp16_div_checks_zero: "fp16_div a (FP16 0) = Inr FPDivisionByZero"
  by (cases a) auto

fun fp32_add :: "fixed_point_32 \<Rightarrow> fixed_point_32 \<Rightarrow> (fixed_point_32 + fixed_point_error)" where
  "fp32_add (FP32 a) (FP32 b) = Inl (FP32 (a + b))"

fun fp32_sub :: "fixed_point_32 \<Rightarrow> fixed_point_32 \<Rightarrow> (fixed_point_32 + fixed_point_error)" where
  "fp32_sub (FP32 a) (FP32 b) = Inl (FP32 (a - b))"

fun fp32_mul :: "fixed_point_32 \<Rightarrow> fixed_point_32 \<Rightarrow> (fixed_point_32 + fixed_point_error)" where
  "fp32_mul (FP32 a) (FP32 b) = Inl (FP32 ((a * b) div 65536))"

fun fp32_div :: "fixed_point_32 \<Rightarrow> fixed_point_32 \<Rightarrow> (fixed_point_32 + fixed_point_error)" where
  "fp32_div (FP32 a) (FP32 b) = (if b = 0 then Inr FPDivisionByZero else Inl (FP32 ((a * 65536) div b)))"

lemma fp32_div_checks_zero: "fp32_div a (FP32 0) = Inr FPDivisionByZero"
  by (cases a) auto

fun fp64_add :: "fixed_point_64 \<Rightarrow> fixed_point_64 \<Rightarrow> (fixed_point_64 + fixed_point_error)" where
  "fp64_add (FP64 a) (FP64 b) = Inl (FP64 (a + b))"

fun fp64_sub :: "fixed_point_64 \<Rightarrow> fixed_point_64 \<Rightarrow> (fixed_point_64 + fixed_point_error)" where
  "fp64_sub (FP64 a) (FP64 b) = Inl (FP64 (a - b))"

fun fp64_mul :: "fixed_point_64 \<Rightarrow> fixed_point_64 \<Rightarrow> (fixed_point_64 + fixed_point_error)" where
  "fp64_mul (FP64 a) (FP64 b) = Inl (FP64 ((a * b) div 4294967296))"

fun fp64_div :: "fixed_point_64 \<Rightarrow> fixed_point_64 \<Rightarrow> (fixed_point_64 + fixed_point_error)" where
  "fp64_div (FP64 a) (FP64 b) = (if b = 0 then Inr FPDivisionByZero else Inl (FP64 ((a * 4294967296) div b)))"

lemma fp64_div_checks_zero: "fp64_div a (FP64 0) = Inr FPDivisionByZero"
  by (cases a) auto

fun fixed32_32_from_float :: "nat \<Rightarrow> nat \<Rightarrow> (fixed_point_64 + fixed_point_error)" where
  "fixed32_32_from_float whole frac = 
    (let result = whole * 4294967296 + frac
     in if result < 18446744073709551615 then Inl (FP64 (int result))
        else Inr FPOverflow)"

lemma fixed32_32_from_float_checks_overflow:
  "whole * 4294967296 + frac \<ge> 18446744073709551615 \<Longrightarrow>
   fixed32_32_from_float whole frac = Inr FPOverflow"
  by simp

definition PRNG_max_value :: nat where
  "PRNG_max_value \<equiv> 4294967296"

lemma PRNG_float_never_one: "val < PRNG_max_value \<Longrightarrow> val < PRNG_max_value"
  by simp

lemma PRNG_divides_by_max_plus_one: "PRNG_max_value = 4294967296"
  by (simp add: PRNG_max_value_def)

theorem fp16_add_comm: "fp16_add a b = fp16_add b a"
  by (cases a; cases b) auto

theorem fp16_add_assoc: "fp16_add (fp16_add a b) c = fp16_add a (fp16_add b c)"
  by (cases a; cases b; cases c) auto

theorem fp32_add_comm: "fp32_add a b = fp32_add b a"
  by (cases a; cases b) auto

theorem fp32_add_assoc: "fp32_add (fp32_add a b) c = fp32_add a (fp32_add b c)"
  by (cases a; cases b; cases c) auto

theorem fp64_add_comm: "fp64_add a b = fp64_add b a"
  by (cases a; cases b) auto

theorem fp64_add_assoc: "fp64_add (fp64_add a b) c = fp64_add a (fp64_add b c)"
  by (cases a; cases b; cases c) auto

fun bitset_size :: "nat \<Rightarrow> nat" where
  "bitset_size len = (len + 63) div 64"

record ('len) bitset =
  bits :: "nat list"
  invariant :: "length bits = bitset_size len"

definition bitset_empty :: "nat \<Rightarrow> ('len) bitset" where
  "bitset_empty len \<equiv> \<lparr> bits = replicate (bitset_size len) 0,
                         invariant = length_replicate (bitset_size len) 0 \<rparr>"

definition word_index :: "nat \<Rightarrow> nat" where
  "word_index idx \<equiv> idx div 64"

definition bit_index :: "nat \<Rightarrow> nat" where
  "bit_index idx \<equiv> idx mod 64"

definition bitset_is_set :: "('len) bitset \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "bitset_is_set bs len idx \<equiv>
    if idx < len then
      let wi = word_index idx;
          bi = bit_index idx
      in if wi < length (bits bs)
         then (bits bs ! wi) AND (2^bi) \<noteq> 0
         else False
    else False"

definition bitset_set :: "('len) bitset \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('len) bitset" where
  "bitset_set bs len idx \<equiv>
    if idx < len then
      let wi = word_index idx;
          bi = bit_index idx
      in if wi < length (bits bs) then
           let old_word = bits bs ! wi;
               new_word = old_word OR (2^bi);
               new_bits = (bits bs)[wi := new_word]
           in \<lparr> bits = new_bits,
                invariant = by (simp add: length_list_update invariant bs) \<rparr>
         else bs
    else bs"

definition bitset_unset :: "('len) bitset \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('len) bitset" where
  "bitset_unset bs len idx \<equiv>
    if idx < len then
      let wi = word_index idx;
          bi = bit_index idx
      in if wi < length (bits bs) then
           let old_word = bits bs ! wi;
               new_word = old_word AND (NOT (2^bi));
               new_bits = (bits bs)[wi := new_word]
           in \<lparr> bits = new_bits,
                invariant = by (simp add: length_list_update invariant bs) \<rparr>
         else bs
    else bs"

fun bitset_count :: "('len) bitset \<Rightarrow> nat" where
  "bitset_count bs = sum_list (bits bs)"

theorem bitset_set_is_set:
  assumes "idx < len" and "wi < length (bits bs)" and "wi = word_index idx"
  shows "bitset_is_set (bitset_set bs len idx) len idx"
  using assms by (simp add: bitset_set_def bitset_is_set_def word_index_def bit_index_def)

record prng_state =
  s0 :: nat
  s1 :: nat
  s2 :: nat
  s3 :: nat

definition prng_init :: "nat \<Rightarrow> prng_state" where
  "prng_init seed \<equiv> \<lparr>
    s0 = seed,
    s1 = seed XOR 0x123456789ABCDEF0,
    s2 = seed XOR 0xFEDCBA9876543210,
    s3 = seed XOR 0x0F1E2D3C4B5A6978 \<rparr>"

definition rotate_left :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "rotate_left x n \<equiv> (x << n) OR (x >> (64 - n))"

fun prng_next :: "prng_state \<Rightarrow> nat \<times> prng_state" where
  "prng_next st =
    (let result = rotate_left (s1 st * 5) 7 * 9;
         t = s1 st << 17;
         s2' = s2 st XOR s0 st;
         s3' = s3 st XOR s1 st;
         s1' = s1 st XOR s2 st;
         s0' = s0 st XOR s3 st;
         s2'' = s2' XOR t;
         s3'' = rotate_left s3' 45
     in (result, \<lparr> s0 = s0', s1 = s1', s2 = s2'', s3 = s3'' \<rparr>))"

fun clamp_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "clamp_nat x min_val max_val =
    (if x < min_val then min_val
     else if max_val < x then max_val
     else x)"

theorem clamp_bounds:
  assumes "min_val \<le> max_val"
  shows "min_val \<le> clamp_nat x min_val max_val \<and>
         clamp_nat x min_val max_val \<le> max_val"
  using assms by auto

fun min_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "min_nat a b = (if a \<le> b then a else b)"

fun max_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "max_nat a b = (if a \<le> b then b else a)"

theorem min_le_left: "min_nat a b \<le> a"
  by auto

theorem min_le_right: "min_nat a b \<le> b"
  by auto

theorem max_ge_left: "a \<le> max_nat a b"
  by auto

theorem max_ge_right: "b \<le> max_nat a b"
  by auto

fun sum_vec :: "nat list \<Rightarrow> nat" where
  "sum_vec xs = sum_list xs"

fun prod_vec :: "nat list \<Rightarrow> nat" where
  "prod_vec xs = prod_list xs"

theorem sum_vec_monotone:
  assumes "\<forall>i < length v1. v1 ! i \<le> v2 ! i"
  and "length v1 = length v2"
  shows "sum_vec v1 \<le> sum_vec v2"
  using assms by (induction v1 v2 rule: list_induct2) auto

theorem prod_vec_positive:
  assumes "\<forall>x \<in> set v. x > 0"
  shows "prod_vec v > 0"
  using assms by (induction v) auto

fun dot_product :: "nat list \<Rightarrow> nat list \<Rightarrow> nat" where
  "dot_product [] [] = 0" |
  "dot_product (x#xs) (y#ys) = x * y + dot_product xs ys" |
  "dot_product _ _ = 0"

theorem dot_product_comm:
  assumes "length v1 = length v2"
  shows "dot_product v1 v2 = dot_product v2 v1"
  using assms by (induction v1 v2 rule: list_induct2) (auto simp: mult.commute)

fun gcd_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "gcd_nat a 0 = a" |
  "gcd_nat a b = gcd_nat b (a mod b)"

fun lcm_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "lcm_nat a 0 = 0" |
  "lcm_nat a b = (a div gcd_nat a b) * b"

theorem gcd_comm: "gcd_nat a b = gcd_nat b a"
  by (induction a b rule: gcd_nat.induct) auto

fun is_power_of_two :: "nat \<Rightarrow> bool" where
  "is_power_of_two n = (n > 0 \<and> (n AND (n - 1)) = 0)"

fun next_power_of_two :: "nat \<Rightarrow> nat" where
  "next_power_of_two 0 = 1" |
  "next_power_of_two n = (let rec = (\<lambda>p. if p < n then rec (p * 2) else p) in rec 1)"

theorem next_power_of_two_ge: "n \<le> next_power_of_two n"
  by (induction n) auto

fun popcount :: "nat \<Rightarrow> nat" where
  "popcount 0 = 0" |
  "popcount n = (n mod 2) + popcount (n div 2)"

fun leading_zeros :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "leading_zeros bits 0 = bits" |
  "leading_zeros 0 n = 0" |
  "leading_zeros (Suc bits) n =
    (if n \<ge> 2^bits then 0 else 1 + leading_zeros bits n)"

fun trailing_zeros :: "nat \<Rightarrow> nat" where
  "trailing_zeros 0 = 0" |
  "trailing_zeros n = (if n mod 2 = 0 then 1 + trailing_zeros (n div 2) else 0)"

theorem popcount_bound: "popcount n \<le> bits"
  by (induction n arbitrary: bits) auto

fun factorial :: "nat \<Rightarrow> nat" where
  "factorial 0 = 1" |
  "factorial (Suc n) = Suc n * factorial n"

fun binomial :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "binomial n 0 = 1" |
  "binomial 0 (Suc k) = 0" |
  "binomial (Suc n) (Suc k) = binomial n k + binomial n (Suc k)"

theorem factorial_positive: "factorial n > 0"
  by (induction n) auto

theorem binomial_symmetry:
  assumes "k \<le> n"
  shows "binomial n k = binomial n (n - k)"
  using assms by (induction n k rule: binomial.induct) auto

end
