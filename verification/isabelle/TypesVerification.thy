theory TypesVerification
imports Main HOL.Real HOL.Rat
begin

datatype dtype = F32 | F64 | I32 | I64

record fixed_point_16 =
  value :: int

record fixed_point_32 =
  value :: int

record fixed_point_64 =
  value :: int

definition fp16_add :: "fixed_point_16 ⇒ fixed_point_16 ⇒ fixed_point_16" where
  "fp16_add a b = ⦇value = value a + value b⦈"

definition fp16_sub :: "fixed_point_16 ⇒ fixed_point_16 ⇒ fixed_point_16" where
  "fp16_sub a b = ⦇value = value a - value b⦈"

definition fp16_mul :: "fixed_point_16 ⇒ fixed_point_16 ⇒ fixed_point_16" where
  "fp16_mul a b = ⦇value = (value a * value b + 128) div 256⦈"

lemma fp16_add_comm:
  "fp16_add a b = fp16_add b a"
  by (simp add: fp16_add_def)

lemma fp16_add_assoc:
  "fp16_add (fp16_add a b) c = fp16_add a (fp16_add b c)"
  by (simp add: fp16_add_def)

lemma fp16_add_zero:
  "fp16_add a ⦇value = 0⦈ = a"
  by (simp add: fp16_add_def)

definition fp32_add :: "fixed_point_32 ⇒ fixed_point_32 ⇒ fixed_point_32" where
  "fp32_add a b = ⦇value = value a + value b⦈"

definition fp32_sub :: "fixed_point_32 ⇒ fixed_point_32 ⇒ fixed_point_32" where
  "fp32_sub a b = ⦇value = value a - value b⦈"

definition fp32_mul :: "fixed_point_32 ⇒ fixed_point_32 ⇒ fixed_point_32" where
  "fp32_mul a b = ⦇value = (value a * value b) div 65536⦈"

lemma fp32_add_comm:
  "fp32_add a b = fp32_add b a"
  by (simp add: fp32_add_def)

lemma fp32_add_assoc:
  "fp32_add (fp32_add a b) c = fp32_add a (fp32_add b c)"
  by (simp add: fp32_add_def)

lemma fp32_mul_comm:
  "fp32_mul a b = fp32_mul b a"
  by (simp add: fp32_mul_def)

lemma fp32_distributive:
  "fp32_mul a (fp32_add b c) = fp32_add (fp32_mul a b) (fp32_mul a c)"
  by (simp add: fp32_mul_def fp32_add_def algebra_simps)

definition fp64_add :: "fixed_point_64 ⇒ fixed_point_64 ⇒ fixed_point_64" where
  "fp64_add a b = ⦇value = value a + value b⦈"

definition fp64_sub :: "fixed_point_64 ⇒ fixed_point_64 ⇒ fixed_point_64" where
  "fp64_sub a b = ⦇value = value a - value b⦈"

definition fp64_mul :: "fixed_point_64 ⇒ fixed_point_64 ⇒ fixed_point_64" where
  "fp64_mul a b = ⦇value = (value a * value b) div 4294967296⦈"

lemma fp64_add_comm:
  "fp64_add a b = fp64_add b a"
  by (simp add: fp64_add_def)

lemma fp64_add_assoc:
  "fp64_add (fp64_add a b) c = fp64_add a (fp64_add b c)"
  by (simp add: fp64_add_def)

definition clamp :: "nat ⇒ nat ⇒ nat ⇒ nat" where
  "clamp n min_val max_val = (if n < min_val then min_val else if n > max_val then max_val else n)"

lemma clamp_min:
  "min_val ≤ max_val ⟹ min_val ≤ clamp n min_val max_val"
  by (simp add: clamp_def)

lemma clamp_max:
  "min_val ≤ max_val ⟹ clamp n min_val max_val ≤ max_val"
  by (simp add: clamp_def)

lemma clamp_idempotent:
  "clamp (clamp n min_val max_val) min_val max_val = clamp n min_val max_val"
  by (simp add: clamp_def)

definition gcd_nat :: "nat ⇒ nat ⇒ nat" where
  "gcd_nat a b = gcd a b"

lemma gcd_comm:
  "gcd_nat a b = gcd_nat b a"
  by (simp add: gcd_nat_def gcd.commute)

definition power_nat :: "nat ⇒ nat ⇒ nat" where
  "power_nat base exp = base ^ exp"

lemma power_zero:
  "power_nat base 0 = 1"
  by (simp add: power_nat_def)

lemma power_one:
  "power_nat 1 exp = 1"
  by (simp add: power_nat_def)

lemma power_add:
  "power_nat base (m + n) = power_nat base m * power_nat base n"
  by (simp add: power_nat_def power_add)

lemma power_mult:
  "power_nat base (m * n) = power_nat (power_nat base m) n"
  by (simp add: power_nat_def power_mult)

record complex_fixed_point =
  real_part :: fixed_point_32
  imag_part :: fixed_point_32

definition complex_add :: "complex_fixed_point ⇒ complex_fixed_point ⇒ complex_fixed_point" where
  "complex_add a b = ⦇real_part = fp32_add (real_part a) (real_part b),
                       imag_part = fp32_add (imag_part a) (imag_part b)⦈"

definition complex_sub :: "complex_fixed_point ⇒ complex_fixed_point ⇒ complex_fixed_point" where
  "complex_sub a b = ⦇real_part = fp32_sub (real_part a) (real_part b),
                       imag_part = fp32_sub (imag_part a) (imag_part b)⦈"

definition complex_mul :: "complex_fixed_point ⇒ complex_fixed_point ⇒ complex_fixed_point" where
  "complex_mul a b = ⦇real_part = fp32_sub (fp32_mul (real_part a) (real_part b))
                                             (fp32_mul (imag_part a) (imag_part b)),
                       imag_part = fp32_add (fp32_mul (real_part a) (imag_part b))
                                             (fp32_mul (imag_part a) (real_part b))⦈"

lemma complex_add_comm:
  "complex_add a b = complex_add b a"
  by (simp add: complex_add_def fp32_add_comm)

lemma complex_add_assoc:
  "complex_add (complex_add a b) c = complex_add a (complex_add b c)"
  by (simp add: complex_add_def fp32_add_assoc)

definition factorial_nat :: "nat ⇒ nat" where
  "factorial_nat n = fact n"

lemma factorial_positive:
  "1 ≤ factorial_nat n"
  by (simp add: factorial_nat_def)

lemma factorial_monotone:
  "factorial_nat n ≤ factorial_nat (Suc n)"
  by (simp add: factorial_nat_def)

definition binomial_coeff :: "nat ⇒ nat ⇒ nat" where
  "binomial_coeff n k = (if k ≤ n then n choose k else 0)"

lemma binomial_symm:
  "k ≤ n ⟹ binomial_coeff n k = binomial_coeff n (n - k)"
  by (simp add: binomial_coeff_def binomial_symmetric)

lemma binomial_pascal:
  "k ≤ n ⟹ binomial_coeff (Suc n) (Suc k) = binomial_coeff n k + binomial_coeff n (Suc k)"
  by (simp add: binomial_coeff_def choose_reduce_nat)

end
