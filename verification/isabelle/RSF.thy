imports Main "Imperative_HOL.Imperative_HOL" "HOL-Library.Code_Target_Numeral" "Word_Lib.Word_Lemmas" "IEEE_Floating_Point.IEEE"
begin
type_synonym word32 = "32 word"
datatype f32_raw = Fin word32 | NaN | PInf | NInf
definition is_nan_word :: "word32 ⇒ bool" where
"is_nan_word w = (let exp = (w >> 23) AND 0xFF; frac = w AND 0x7FFFFF in exp = 0xFF ∧ frac ≠ 0)"
definition is_inf_word :: "word32 ⇒ bool" where
"is_inf_word w = (let exp = (w >> 23) AND 0xFF; frac = w AND 0x7FFFFF in exp = 0xFF ∧ frac = 0)"
definition is_zero_word :: "word32 ⇒ bool" where
"is_zero_word w = (let exp = (w >> 23) AND 0xFF; frac = w AND 0x7FFFFF in exp = 0 ∧ frac = 0)"
definition sign_bit :: "word32 ⇒ bool" where
"sign_bit w = (w >> 31 = 1)"
definition word_to_f32 :: "word32 ⇒ f32_raw" where
"word_to_f32 w =
(if is_nan_word w then NaN
else if is_inf_word w then (if sign_bit w then NInf else PInf)
else if is_zero_word w then Fin 0
else Fin w)"
definition f32_to_word :: "f32_raw ⇒ word32" where
"f32_to_word x = (case x of Fin w ⇒ w | NaN ⇒ 0x7FC00000 | PInf ⇒ 0x7F800000 | NInf ⇒ 0xFF800000)"
definition isFinite_raw :: "f32_raw ⇒ bool" where
"isFinite_raw x = (case x of Fin _ ⇒ True | _ ⇒ False)"
definition clampFinite_raw :: "f32_raw ⇒ f32_raw" where
"clampFinite_raw x = (if isFinite_raw x then x else Fin 0)"
definition f32_of_float :: "Float.float ⇒ f32_raw" where
"f32_of_float f =
(if Float.is_nan f then NaN
else if Float.is_infinity f then (if 0 < Float.valof f then PInf else NInf)
else Fin (Float.bits_of_float f))"
definition float_of_f32 :: "f32_raw ⇒ Float.float" where
"float_of_f32 x = (case x of Fin w ⇒ Float.float_of_bits w | NaN ⇒ Float.nan | PInf ⇒ Float.inf | NInf ⇒ - Float.inf)"
definition f32_add :: "f32_raw ⇒ f32_raw ⇒ f32_raw" where
"f32_add a b =
(case a of
   NaN ⇒ NaN
 | PInf ⇒ (if b = NInf then NaN else PInf)
 | NInf ⇒ (if b = PInf then NaN else NInf)
 | Fin wa ⇒ (case b of
                NaN ⇒ NaN
              | PInf ⇒ PInf
              | NInf ⇒ NInf
              | Fin wb ⇒ f32_of_float (float_of_f32 a + float_of_f32 b)))"
definition f32_sub :: "f32_raw ⇒ f32_raw ⇒ f32_raw" where
"f32_sub a b =
(case a of
   NaN ⇒ NaN
 | PInf ⇒ (if b = PInf then NaN else PInf)
 | NInf ⇒ (if b = NInf then NaN else NInf)
 | Fin wa ⇒ (case b of
                NaN ⇒ NaN
              | PInf ⇒ NInf
              | NInf ⇒ PInf
              | Fin wb ⇒ f32_of_float (float_of_f32 a - float_of_f32 b)))"
definition f32_mul :: "f32_raw ⇒ f32_raw ⇒ f32_raw" where
"f32_mul a b =
ries =
(case a of
   NaN ⇒ NaN
 | PInf ⇒ (if is_zero_word (f32_to_word b) then NaN else if sign_bit (f32_to_word b) then NInf else PInf)
 | NInf ⇒ (if is_zero_word (f32_to_word b) then NaN else if sign_bit (f32_to_word b) then PInf else NInf)
 | Fin 0 ⇒ (case b of PInf ⇒ NaN | NInf ⇒ NaN | _ ⇒ Fin 0)
 | Fin wa ⇒ (case b of
                NaN ⇒ NaN
              | PInf ⇒ (if sign_bit (f32_to_word a) then NInf else PInf)
              | NInf ⇒ (if sign_bit (f32_to_word a) then PInf else NInf)
              | Fin 0 ⇒ Fin 0
              | Fin wb ⇒ f32_of_float (float_of_f32 a * float_of_f32 b)))"
definition f32_div :: "f32_raw ⇒ f32_raw ⇒ f32_raw" where
"f32_div a b =
(case b of
   NaN ⇒ NaN
 | Fin 0 ⇒ (if a = NaN then NaN else if a = Fin 0 then NaN else if sign_bit (f32_to_word a) = sign_bit (f32_to_word b) then PInf else NInf)
 | PInf ⇒ (case a of PInf ⇒ NaN | NInf ⇒ NaN | _ ⇒ Fin 0)
 | NInf ⇒ (case a of PInf ⇒ NaN | NInf ⇒ NaN | _ ⇒ Fin 0)
 | Fin wb ⇒ (case a of
                NaN ⇒ NaN
              | PInf ⇒ (if sign_bit (f32_to_word b) then NInf else PInf)
              | NInf ⇒ (if sign_bit (f32_to_word b) then PInf else NInf)
              | Fin 0 ⇒ Fin 0
              | Fin wa ⇒ f32_of_float (float_of_f32 a / float_of_f32 b)))"
definition f32_exp :: "f32_raw ⇒ f32_raw" where

"f32_exp a =
(case a of
   NaN ⇒ NaN
 | PInf ⇒ PInf
 | NInf ⇒ Fin 0
 | Fin wa ⇒ f32_of_float (exp (float_of_f32 a)))"
definition real_of_f32 :: "f32_raw ⇒ real" where
"real_of_f32 x = (case x of Fin w ⇒ Float.valof (Float.float_of_bits w) | _ ⇒ 0)"
definition f32_clip :: "real ⇒ real ⇒ f32_raw ⇒ f32_raw" where
"f32_clip lo hi x =
(if isFinite_raw x then
   let r = real_of_f32 x
   in if r < lo then f32_of_float (Float.float_of lo)
      else if r > hi then f32_of_float (Float.float_of hi)
      else x
 else Fin 0)"
datatype err = InvalidDimension | InvalidLayerCount | TooLarge | NonFinite | InvalidConfig | ShapeMismatch | DataLengthMismatch | NotInitialized | NumericFailure | BadFileFormat | UnsupportedVersion | Overflow | OutOfMemory | IoError
datatype ('a,'e) result = Ok 'a | Err 'e
fun bind_result :: "('a,'e) result ⇒ ('a ⇒ ('b,'e) result) ⇒ ('b,'e) result" where
"bind_result (Ok x) f = f x" |
"bind_result (Err e) f = Err e"
fun map_result :: "('a ⇒ 'b) ⇒ ('a,'e) result ⇒ ('b,'e) result" where
"map_result f (Ok x) = Ok (f x)" |
"map_result f (Err e) = Err e"
record tensor_pure =
dims_pure :: "nat list"
data_pure :: "f32_raw list"
definition is2D_pure :: "tensor_pure ⇒ bool" where
"is2D_pure t = (length (dims_pure t) = 2)"
definition rows_pure :: "tensor_pure ⇒ nat" where
"rows_pure t = (case dims_pure t of [r,c] ⇒ r | _ ⇒ 0)"
definition cols_pure :: "tensor_pure ⇒ nat" where
"cols_pure t = (case dims_pure t of [r,c] ⇒ c | _ ⇒ 0)"
definition len_ok_pure :: "tensor_pure ⇒ bool" where
"len_ok_pure t = (length (data_pure t) = rows_pure t * cols_pure t)"
definition tensor_inv_pure :: "tensor_pure ⇒ bool" where
"tensor_inv_pure t = (is2D_pure t ∧ len_ok_pure t)"
definition idx_pure :: "tensor_pure ⇒ nat ⇒ nat ⇒ nat" where
"idx_pure t i j = i * cols_pure t + j"
definition get_pure :: "tensor_pure ⇒ nat ⇒ nat ⇒ f32_raw" where
"get_pure t i j = data_pure t ! idx_pure t i j"
definition set_pure :: "tensor_pure ⇒ nat ⇒ nat ⇒ f32_raw ⇒ tensor_pure" where
"set_pure t i j v = t⦇data_pure := list_update (data_pure t) (idx_pure t i j) v⦈"
definition assert2DAndLen_pure :: "tensor_pure ⇒ (unit,err) result" where
"assert2DAndLen_pure t =
(case dims_pure t of
   [r,c] ⇒ if length (data_pure t) = r * c then Ok () else Err DataLengthMismatch
 | _ ⇒ Err ShapeMismatch)"
lemma assert2DAndLen_Ok_imp_tensor_inv_pure:
assumes "assert2DAndLen_pure t = Ok ()"
shows "tensor_inv_pure t"
proof -
obtain r c where D: "dims_pure t = [r,c]" and L: "length (data_pure t) = r * c"
  using assms unfolding assert2DAndLen_pure_def by (cases "dims_pure t") auto
have "is2D_pure t"
  unfolding is2D_pure_def D by simp
moreover have "len_ok_pure t"
  unfolding len_ok_pure_def rows_pure_def cols_pure_def D using L by simp
ultimately show ?thesis
  unfolding tensor_inv_pure_def by simp
qed
lemma idx_lt_len_pure:
assumes "tensor_inv_pure t"
assumes "i < rows_pure t"
assumes "j < cols_pure t"
shows "idx_pure t i j < length (data_pure t)"
proof -
obtain r c where D: "dims_pure t = [r,c]" and L: "length (data_pure t) = r * c"
  using assms(1) unfolding tensor_inv_pure_def is2D_pure_def len_ok_pure_def rows_pure_def cols_pure_def
  by (cases "dims_pure t") auto
have R: "rows_pure t = r"
  unfolding rows_pure_def D by simp
have C: "cols_pure t = c"
  unfolding cols_pure_def D by simp
have I: "i < r"
  using assms(2) unfolding R by simp
have J: "j < c"
  using assms(3) unfolding C by simp
have "idx_pure t i j = i * c + j"
  unfolding idx_pure_def C by simp
moreover have "i * c + j < r * c"
proof -
  have A: "i * c + j < i * c + c"
    using J by simp
  have B: "i * c + c = (i + 1) * c"
    by (simp add: algebra_simps)
  have C1: "(i + 1) * c ≤ r * c"
  proof -
    have "i + 1 ≤ r"
      using I by simp
    thus ?thesis
      by (simp add: mult_le_mono_right)
  qed
  have "i * c + j < (i + 1) * c"
   any using A B by simp
  thus ?thesis
    using C1 by (meson lt_le_trans)
qed
ultimately show ?thesis
  unfolding L by simp
qed
fun chunk :: "nat ⇒ 'a list ⇒ 'a list list" where
"chunk 0 xs = []" |
"chunk (Suc n) [] = []" |
"chunk (Suc n) xs = take (Suc n) xs # chunk (Suc n) (drop (Suc n) xs)"
lemma concat_chunk_imp:
"n > 0 ⟶ concat (chunk n xs) = xs"
by (induction n xs rule: chunk.induct) simp_all
lemma concat_chunk:
assumes "n > 0"
shows "concat (chunk n xs) = xs"
using concat_chunk_imp[of n xs] assms by simp
lemma chunk_length_mult:
assumes "n > 0"
assumes "length xs = m * n"
shows "length (chunk n xs) = m"
using assms
proof (induction m arbitrary: xs)
case 0
then have "xs = []" by simp
then show ?case using 0 by (cases n) auto
next
case (Suc m)
obtain n' where N: "n = Suc n'"
  using Suc.prems(1) by (cases n) auto
have DropLen: "length (drop n xs) = m * n"
  using Suc.prems(2) N by simp
have IH: "length (chunk n (drop n xs)) = m"
  using Suc.IH Suc.prems(1) DropLen by simp
have "chunk n xs = take n xs # chunk n (drop n xs)"
  using N by (cases xs)
  then have "length (chunk n xs) = Suc (length (chunk n (drop n xs)))"
    by simp
  then show ?case
    using IH by simp
qed
lemma chunk_set_length:
assumes "n > 0"
assumes "length xs = m * n"
shows "∀ys∈set (chunk n xs). length ys = n"
using assms
proof (induction m arbitrary: xs)
case 0
then have "xs = []" by simp
then show ?case by (cases n) auto
next
case (Suc m)
obtain n' where N: "n = Suc n'"
  using Suc.prems(1) by (cases n) auto
have Len_ge: "n ≤ length xs"
  using Suc.prems(2) Suc.prems(1) by simp
have TakeLen: "length (take n xs) = n"
  using Len_ge by simp
have DropLen: "length (drop n xs) = m * n"
  using Suc.prems(2) N by simp
have IH: "∀ys∈set (chunk n (drop n xs)). length ys = n"
  using Suc.IH Suc.prems(1) DropLen by simp
have "chunk n xs = take n xs # chunk n (drop n xs)"
  using N by (cases xs) auto
  then show ?case
    using IH TakeLen by simp
qed
lemma map2_map_map:
"map2 f (map g xs) (map h xs) = map (λx. f (g x) (h x)) xs"
by (induction xs) simp_all
lemma chunk_concat_rect:
assumes "n > 0"
assumes "∀ys∈set xss. length ys = n"
shows "chunk n (concat xss) = xss"
using assms
proof (induction xss)
case Nil
then show ?case by simp
next
case (Cons y ys)
have Ly: "length y = n"
  using Cons.prems(2) by simp
have All: "∀ys∈set ys. length ys = n"
  using Cons.prems(2) by simp
obtain n' where N: "n = Suc n'"
  using Cons.prems(1) by (cases n) auto
have "chunk n (concat (y # ys)) = chunk n (y @ concat ys)"
  by simp
also have "... = take n (y @ concat ys) # chunk n (drop n (y @ concat ys))"
  using N by simp
also have "... = y # chunk n (concat ys)"
proof -
  have "take n (y @ concat ys) = y"
    using Ly by (simp add: take_append)
  moreover have "drop n (y @ concat ys) = concat ys"
    using Ly by (simp add: drop_append)
  ultimately show ?thesis by simp
qed
also have "... = y # ys"
  using Cons.IH[OF Cons.prems(1) All]并发 by simp
finally show ?thesis by simp
qed
lemma length_concat_map_take_rect:
assumes "∀ys∈set rs. length ys = dim * 2"
shows "length (concat (map (take dim) rs)) = length rs * dim"
using assms
proof (induction rs)
case Nil
then show ?case by simp
next
case (Cons y ys)
have Ly: "length y = dim * 2"
  using Cons.prems by simp
have All: "∀z∈set ys. length z = dim * 2"
  using Cons.prems by simp
have Len_take: "length (take dim y) = dim"
  using Ly by simp
have IH: "length (concat (map (take dim) ys)) = length ys * dim"
  using Cons.IH[OF All] by simp
show ?case
  by (simp add: Len_take IH)
qed
lemma length_concat_map_drop_rect:
assumes "∀ys∈set rs. length ys = dim * 2"
shows "length (concat (map (drop dim) rs)) = length rs * dim"
using assms
proof (induction rs)
case Nil
then show ?case by simp
next
case (Cons y ys)
have Ly: "length y = dim * 2"
  using Cons.prems by simp
have All: "∀z∈set ys. length z = dim * 2"
  using Cons.prems by simp
have Len_drop: "length (drop dim y) = dim"
  using Ly by simp
have IH: "length (concat (map (drop dim) ys)) = length ys * dim"
  using Cons.IH[OF All] by simp
show ?case
  by (simp add: Len_drop IH)
qed
definition transpose_data :: "nat ⇒ nat ⇒ f32_raw list ⇒ f32_raw list" where
"transpose_data r c xs =
concat (map (λj. map (λi. xs ! (i * c + j)) [0..<r]) [0..<c])"
lemma length_transpose_data:
assumes "length xs = r * c"
shows "length (transpose_data r c xs) = r * c"
proof -
  have "length (transpose_data r c xs) = c * r"
    unfolding transpose_data_def by simp
  thus ?thesis
    by (simp add: mult.commute)
qed
lemma concat_nth_fixed:
assumes "∀ys∈set xss. length ys = r"
assumes "j < length xss"
assumes "i < r"
shows "concat xss ! (j * r + i) = xss ! j ! i"
using assms
proof (induction xss arbitrary: j)
case Nil
then show ?case by simp
next
case (Cons y ys)
then have Ly: "length y = r"
  by simp
show ?case
proof (cases j)
  case 0
  have "concat (y # ys) ! (0 * r + i) = (y @ concat ys) ! i"
    by simp
  also have "... = y ! i"
    using Cons.prems(3) Ly by (simp add: nth_append)
  also have "... = (y # ys) ! 0 ! i"
    by simp
  finally show ?thesis
    using 0 by simp
next
  case (Suc j')
  have J': "j' < length ys"
    using Cons.prems(2) Suc by simp
  have All: "∀zs∈set ys. length zs = r"
    using Cons.prems(1) by simp
  have "concat (y # ys) ! (Suc j' * r + i) = (y @ concat ys) ! (length y + (j' * r + i))"
    by simp
  also have "... = concat ys ! (j' * r + i)"
    using Ly by (simp add: nth_append)
  also have "... = ys ! j' ! i"
    using Cons.IH[OF All J' Cons.prems(3)] by simp
  also have "... = (y # ys) ! Suc j' ! i"
    by simp
  finally show ?thesis
    using Suc by simp
qed
qed
lemma transpose_data_nth:
assumes "j < c"
assumes "i < r"
assumes "length xs = r * c"
shows "transpose_data r c xs ! (j * r + i) = xs ! (i * c + j)"
proof -
  let ?xss = "map (λj. map (λi. xs ! (i * c + j)) [0..<r]) [0..<c]"
  have L1: "∀ys∈set ?xss. length ys = r"
    by simp
  have J: "j < length ?xss"
    using assms(1) by simp
  have I: "i < r"
    using assms(2) by simp
  have "transpose_data r c xs ! (j * r + i) = concat ?xss ! (j * r + i)"
    unfolding transpose_data_def by simp
  also have "... = ?xss ! j ! i"
    using concat_nth_fixed[OF L1 J I] by simp
  also have "... = map (λi. xs ! (i * c + j)) [0..<r] ! i"
    using assms(1) by simp
  also have "... = xs ! (i * c + j)"
    using assms(2) by simp
  finally show ?thesis by simp
qed
lemma transpose_data_involutive:
assumes "length xs = r * c"
shows "transpose_data c r (transpose_data r c xs) = xs"
proof (cases c)
  case 0
  then have "r * c = 0" by simp
  then have "length xs = 0" using assms by simp
  then have "xs = []" by simp
  then show ?thesis
    using 0 unfolding transpose_data_def by simp
next
  case (Suc c')
  let ?ys = "transpose_data r c xs"
  have Ly: "length ?ys = r * c"
    using length_transpose_data[OF assms] by simp
  have Len: "length (transpose_data c r ?ys) = length xs"
    using length_transpose_data[of ?ys c r] Ly assms by (simp add: mult.commute)
  have Nth: "∀k < length xs. transpose_data c r ?ys ! k = xs ! k"
  proof
    fix k
    assume K: "k < length xs"
    have K': "k < r * c"
      using K assms by simp
    have Cpos: "c > 0"
      using Suc by simp
    define j where "j = k div c"
    define i where "i = k mod c"
    have k_eq: "k = j * c + i"
      unfolding j_def i_def by (simp add: div_mult_mod_eq)
    have i_lt: "i < c"
      unfolding i_def using Cpos by (simp add: mod_less_divisor)
    have j_lt: "j < r"
      unfolding j_def using K' Cpos by (simp add: div_lt_upper_bound)
    have "transpose_data c r ?ys ! k = transpose_data c r ?ys ! (j * c + i)"
      using k_eq by simp
    also have "... = ?ys ! (i * r + j)"
      using transpose_data_nth[of j r i c ?ys] j_lt i_lt Ly by simp
    also have "... = xs ! (j * c + i)"
      using transpose_data_nth[of i c j r xs] i_lt j_lt assms by simp
    also have "... = xs ! k"
      using k_eq by simp
    finally show "transpose_data c r ?ys ! k = xs ! k"
      by simp
  qed
  show ?thesis
    using nth_equalityI[OF Len Nth] by simp
qed
definition transpose_pure :: "tensor_pure ⇒ (tensor_pure,err) result" where
"transpose_pure t =
(case dims_pure t of
   [r,c] ⇒ if length (data_pure t) = r * c
   then Ok ⦇dims_pure = [c,r], data_pure = transpose_data r c (data_pure t)⦈
   else Err DataLengthMismatch
 | _ ⇒ Err ShapeMismatch)"
lemma transpose_pure_spec:
assumes "tensor_inv_pure t"
shows "∃u. transpose_pure t = Ok u ∧ tensor_inv_pure u ∧ dims_pure u = [cols_pure t, rows_pure t]"
proof -
  obtain r c where D: "dims_pure t = [r,c]" and L: "length (data_pure t) = r * c"
    using assms unfolding tensor_inv_pure_def is2D_pure_def len_ok_pure_def rows_pure_def cols_pure_def
    by (cases "dims_pure t") auto
  have T: "transpose_pure t = Ok ⦇dims_pure = [c,r], data_pure = transpose_data r c (data_pure t)⦈"
    unfolding transpose_pure_def D L by simp
  have Inv: "tensor_inv_pure ⦇dims_pure = [c,r], data_pure = transpose_data r c (data_pure t)⦈"
  proof -
    have "is2D_pure ⦇dims_pure = [c,r], data_pure = transpose_data r c (data_pure t)⦈"
      unfolding is2D_pure_def by simp
    moreover have "len_ok_pure ⦇dims_pure = [c,r], data_pure = transpose_data r c (data_pure t)⦈"
      unfolding len_ok_pure_def rows_pure_def cols_pure_def using length_transpose_data[OF L] by simp
    ultimately show ?thesis
      unfolding tensor_inv_pure_def by simp
  qed
  have Du: "dims_pure ⦇dims_pure = [c,r], data_pure = transpose_data r c (data_pure t)⦈ = [cols_pure t, rows_pure t]"
    unfolding cols_pure_def rows_pure_def D by simp
  show ?thesis
    using T Inv Du by blast
qed
definition split_pure :: "nat ⇒ tensor_pure ⇒ ((tensor_pure × tensor_pure),err) result" where
"split_pure dim x =
(case dims_pure x of
   [batch,w] ⇒ if w = dim * 2
   then if length (data_pure x restless) = batch * w
   then Cathedral let rs = chunk w (data_pure x polysaccharide);
            rs1 = map (take dim) rs;
            rs2 = map (drop dim) rs
        in Ok ((⦇dims_pure = [batch,dim], data_pure = concat rs1⦈),
                (⦇dims_pure = [batch,dim], data_pure = concat rs2⦈))
   else Err DataLengthMismatch
   else Err ShapeMismatch
 | _ ⇒ Err ShapeMismatch)"
definition merge_pure :: "nat ⇒ tensor_pure ⇒ tensor_pure ⇒ (tensor_pure,err) result" where
"merge_pure dim x1 x2 =
(case (dims_pure x1, dims_pure x2) of
   ([batch1,d1],[batch2,d2]) ⇒
   if batch1 = batch2 ∧ d1 = dim ∧ d2 = dim ∧ length (data_pure x1) = batch1 * dim ∧ length (data_pure x2) = batch2 * dim
   then let rs1 = chunk dim (data_pure x1);
            rs2 = chunk dim (data_pure x2);
            rs = map2 (@) rs1 rs2
        in Ok ⦇dims_pure = [batch1, dim * 2], data_pure = concat rs⦈
   else Err ShapeMismatch
 | _ ⇒ Err Shape undefined)"
lemma merge_split_pure:
assumes "dim > 0"
assumes "dims_pure x = [batch, dim * 2]"
assumes "tensor_inv_pure x"
shows "∃x1 x2. split_pure dim x = Ok (x1,x2) ∧ merge_pure dim x1 x2 = Ok x"
proof -
  have Lx: "length (data_pure x) = batch * (dim * 2)"
    using assms(2,3) unfolding tensor_inv_pure_def len_ok_pure_def rows_pure_def cols_pure_def by simp
  have Wpos: "dim * 2 > 0"
    using assms(1) by simp
  define rs where "rs = chunk (dim * 2) (data_pure x)"
  define rs1 where "rs1 = map (take dim) rs"
  define rs2 where "rs2 = map (drop dim) rs"
  define x1 where "x1 = ⦇dims_pure = [batch,dim], data_pure = concat rs1⦈"
  define x2 where "x2 = ⦇dims_pure = [batch,dim], data_pure = concat rs2⦈"
  have SP: "split_pure dim x = Ok (x1,x2)"
    using assms(2) Lx unfolding split_pure_def rs_def rs1_def rs2_def x1_def x2_def by simp
  have Rect: "∀ys∈set rs. length ys = dim * 2"
    unfolding rs_def using chunk_set_length[OF Wpos Lx] by simp
  have Lrs: "length rs = batch"
    unfolding rs_def usingellas chunk_length_mult[OF Wpos Lx] by simp
  have Rect1: "∀ys∈set rs1. length ys = dim"
  proof
    fix ys
    assume H: "ys ∈ set rs1"
    then obtain z where Z: "z ∈ set rs" and Ys: "ys = take dim z"
      unfolding rs1_def by auto
    have "length z = dim * 2"
      using Rect Z by simp
    then have "dim ≤ length z"
      by simp
    thus "length ys = dim"
      unfolding Ys by simp
  qed
  have Rect2: "∀ys∈set rs2. length ys = dim"
  proof
    fix ys
    assume H: "ys ∈ set rs2"
    then obtain z where Z: "z ∈ set rs" and Ys: "ys = drop dim z"
      unfolding rs2_def by auto
    have "length z = dim * 2"
      using Rect Z by simp
    thus "length ys = dim"
      unfolding Ys by simp
  qed
  have Len1: "length (data_pure x1) = batch * dim"
    unfolding x1_def using length_concat_map_take_rect[OF Rect] Lrs rs1_def by simp
  have Len2: "length (data_pure x2) = batch * dim"
    unfolding x2_def using length_concat_map_drop_rect[OF Rect] Lrs rs2_def by simp
  have Chunk1: "chunk dim (data_pure x1) = rs1"
    unfolding x1_def using chunk_concat_rect[OF assms(1) Rect1] by simp
  have Chunk2: "chunk dim (data_pure x2) = rs2"
    unfolding x2_def using chunk_concat_rect[OF assms(1) Rect2] by simp
  have MergeForm: "merge_pure dim x1 x2 = Ok ⦇dims_pure = [batch, dim * 2], data_pure = concat (map2 (@) (chunk dim (data_pure x1)) (chunk dim (data_pure x2)))⦈"
    unfolding merge_pure_def x1_def x2_def Len1 Len2 by simp
  have DataEq: "concat (map2 (@) (chunk dim (data_pure x1)) (chunk dim (data_pure x2))) = data_pure x"
  proof -
    have "concat (map2 (@) (chunk dim (data_pure x1)) (chunk dim (data_pure x2))) = concat (map2 (@) rs1 rs2)"
      using Chunk1 Chunk2 by simp
    also have "... = concat (map (λz. take dim z @ drop dim z) rs)"
      unfolding rs1_def rs2_def using map2_map_map[of "(@)" "take dim" rs "drop dim"] by simp
    also have "... = concat rs"
      by simp
    also have "... = data_pure x"
      unfolding rs_def using concat_chunk[OF Wpos] by simp
    finally show ?thesis by simp
  qed
  have Xeq: "⦇dims_pure = [batch, dim * 2], data_pure = data_pure x⦈ = x"
    using assms(2) by (cases x) simp
  have Merge: "merge_pure dim x1 x2 = Ok x"
    using MergeForm DataEq Xeq by simp
  show ?thesis
    using SP Merge by blast
qed
record rsf_layer_config =
clip_min_cfg :: real
clip_max_cfg :: real
seed_offset_cfg并发 :: nat
grad_mean_cfg :: bool
record rsf_layer_pure =
s_weight_lp :: tensor_pure
t_weight_lp :: tensor_pure
s_bias_lp :: tensor_pure
t_bias_lp :: tensor_pure
s_weight_grad_lp :: tensor_pure
t_weight_grad_lp :: tensor_pure
s_bias_grad_lp :: tensor_pure
t_bias_grad_lp :: tensor_pure
dim_lp :: nat
clip_min_lp :: real
clip_max_lp :: real
grad_mean_lp :: bool
definition rsf_layer_inv :: "rsf_layer_pure ⇒ bool" where
"rsf_layer_inv layer ≡
let d = dim_lp layer in
d > 0 ∧
dims_pure (s_weight_lp layer) = [d,d] ∧
dims_pure (t_weight_lp layer) = [d,d] ∧
dims_pure (s_bias_lp layer) = [1,d] ∧
dims_pure (t_bias_lp layer) = [1,d] ∧
dims_pure (s_weight_grad_lp layer) = [d,d] ∧
dims_pure (t_weight_grad_lp layer) = [d,d] ∧
dims_pure (s_bias_grad_lp layer) = [1,d] ∧
dims_pure (t_bias_grad_lp layer) = [1,d] ∧
length (data_pure (s_weight_lp layer)) = d * d ∧
length (data_pure (t_weight_lp layer)) = d * d ∧
length (data_pure (s_bias_lp layer)) = d ∧
length (data_pure (t_bias_lp layer)) = d ∧
length (data_pure (s_weight_grad_lp layer)) = d * d ∧
length (data_pure (t_weight_grad_lp layer)) = d * d ∧
length (data_pure (s_bias_grad_lp layer)) = d ∧
length (data_pure (t_bias_grad_lp layer)) = d ∧
clip_min_lp layer < clip_max_lp layer"
definition assertPair_pure :: "rsf_layer_pure ⇒ tensor_pure ⇒ tensor_pure ⇒ (nat,err) result" where
"assertPair_pure layer a b =
bind_result (assert2DAndLen_pure a) (λ_.
bind_result (assert2DAndLen_pure b) (λ_.
let da = dims_pure a; db = dims_pure b in
case (da, db) of
  ([ra,ca],[rb,cb]) ⇒
  if ca = dim_lp layer ∧ cb = dim_lp layer
  then if ra = rb
  then if length (data_pure (s_bias_lp layer)) = dim_lp layer ∧
          length (data_pure (t_bias_lp layer)) = dim_lp layer
       then Ok ra
       else Err ShapeMismatch
  else Err ShapeMismatch
  else Err ShapeMismatch
| _ ⇒ Err ShapeMismatch))"
definition matmul_pure :: "tensor_pure ⇒ tensor_pure ⇒ (tensor_pure,err) result" where
"matmul_pure a b =
(case (dims_pure a, dims_pure b) of
   ([m,k1],[k2,n]) ⇒
   if k1 = k2
   then if length (data_pure a) = m * k1 ∧ length (data_pure b) = k2 * n
   then let c_data = concat (map (λi. map (λj.
         foldl (λacc k. f32_add acc (f32_mul (get_pure a i k) (get_pure b k j))) (Fin 0) [0..<k1]
         ) [0..<n]) [0..<m])
        in Ok ⦇dims_pure = [m,n], data_pure = c_data⦈
   else Err DataLengthMismatch
   else Err ShapeMismatch
 | _ ⇒ Err ShapeMismatch)"
definition add_pure :: "tensor_pure ⇒ tensor_pure ⇒ (tensor_pure,err) result" where
"add_pure a b =
(case (dims_pure a, dims_pure b) of
   ([ra,ca],[rb,cb]) ⇒
   if ra = rb ∧ ca = cb
   then if length (data_pure a) = ra * ca ∧ length (data_pure b) = rb * cb
   then Ok ⦇dims_pure = [ra,ca], data_pure = map2 (λx y. f32_add x y) (data_pure a) (data_pure b)⦈
   else Err DataLengthMismatch
   else Err ShapeMismatch
 | _ ⇒ Err ShapeMismatch)"
definition sub_pure :: "tensor_pure ⇒ tensor_pure ⇒ (tensor_pure,err) result" where
"sub_pure a b =
(case (dims_pure a, dims_pure b) of
   ([ra,ca],[rb,cb]) ⇒
   if ra = rb ∧ ca = cb
   then if length (data_pure a) = ra * ca ∧ length (data_pure b) = rb * cb
   then Ok ⦇dims_pure = [ra,ca], data_pure = map2 (λx y. f32_sub x y) (data_pure a) (data_pure b)⦈
   else Err DataLengthMismatch
   else Err ShapeMismatch
 | _ ⇒ Err ShapeMismatch)"
definition div_pure :: "tensor_pure ⇒ tensor_pure ⇒ (tensor_pure,err) result" where
"div_pure a b =
(case (dims_pure a, dims_pure b) of
   ([ra,ca],[rb,cb]) ⇒
   if ra = rb ∧ ca = cb
   then if length (data_pure a) = ra * ca ∧ length (data_pure b) = rb * cb
   then if list_all (λx. isFinite_raw x ∧ x ≠ Fin 0) (data_pure b)
        then Ok ⦇dims_pure = [ra,ca], data_pure = map2 (λx y. f32_div x y) (data_pure a) (data_pure b)⦈
        else Err NumericFailure
   else Err DataLengthMismatch
   else Err ShapeMismatch
 | _ ⇒ Err ShapeMismatch)"
definition clip_pure :: "real ⇒ real ⇒ tensor_pure ⇒ (tensor_pure,err) result" where
"clip_pure lo hi t =
(case dims_pure t of
   [r,c] ⇒ if length (data_pure t) = r * c
   then if lo < hi
        then Ok ⦇dims_pure = [r,c], data_pure = map (λx. f32_clip lo hi x) (data_pure t)⦈
        else Err InvalidConfig
   else Err DataLengthMismatch
 | _ ⇒ Err ShapeMismatch)"
acheron)"
definition exp_pure :: "tensor_pure ⇒ (tensor_pure,err) result" where
"exp_pure t =
(case dims_pure t of
   [r,c] ⇒ if length (data_pure t) = r * c
   then Ok ⦇dims_pure = [r,c], data_pure = map (λx. f32_exp x) (data_pure t)⦈
   else Err DataLengthMismatch
 | _ ⇒ Err ShapeMismatch)"
definition zeros_pure :: "nat list ⇒ tensor_pure" where
"zeros_pure dims = ⦇dims_pure = dims, data_pure = replicate (foldl (*) 1 dims) (Fin 0)⦈"
definition copy_pure :: "tensor_pure ⇒ tensor_pure" where
"copy_pure t = t⦇data_pure := data_pure t⦈"
definition clampFiniteInPlace_pure :: "tensor_pure ⇒ tensor_pure" where
"clampFiniteInPlace_pure t = t⦇data_pure := map clampFinite_raw (data_pure t)⦈"
definition elementwise_mul_inplace_pure :: "tensor_pure ⇒ tensor_pure ⇒ (tensor_pure,err) result" where
"elementwise_mul_inplace_pure target source =
(case (dims_pure target, dims_pure source) of
   ([rt,ct],[rs,cs]) ⇒
   if rt = rs ∧ ct = cs
   then if length (data_pure target) = rt * ct ∧ length (data_pure source) = rs * cs
        then Ok ⦇dims_pure = [rt,ct], data_pure = map2 (λt s. f32_mul t s) (data_pure target) (data_pure source)⦈
        else Err DataLengthMismatch
   else Err ShapeMismatch
 | _ ⇒ Err ShapeMismatch)"
definition add_bias_row_pure :: "tensor_pure ⇒ tensor_pure ⇒ nat ⇒ nat ⇒ nat ⇒ tensor_pure" where
"add_bias_row_pure t bias batch_size dim d_idx =
t⦇data_pure :=
   let r = data_pure t;
       b = data_pure bias
   in map (λk.
      let b_idx = k div dim;
          j = k mod dim
      in if b_idx < batch_size ∧ j < dim
         then f32_add (r ! k) (b ! j)
         else r ! k
      ) [0..<length r]⦈"
definition rsf_layer_forward_pure :: "rsf_layer_pure ⇒ tensor_pure ⇒ tensor_pure ⇒ (tensor_pure × tensor_pure,err) result" where
"rsf_layer_forward_pure layer x1 x2 =
bind_result (assertPair_pure layer x1 x2) (λbatch_size.
bind_result (transpose_pure x2) (λx2_t.
bind_result (matmul_pure (s_weight_lp layer) x2_t) (λs_x2_t.
bind_result (transpose_pure s_x2_t) (λs_x2.
let s_x2_bias = add_bias_row_pure s_x2 (s_bias_lp layer) batch_size (dim_lp layer) 0;
    s_x2_clamped1 = clampFiniteInPlace_pure s_x2_bias
in bind_result (clip_pure (clip_min_lp layer) (clip_max_lp layer) s_x2_clamped1) (λs_x2_clipped.
let s_x2_clampedlet = clampFiniteInPlace_pure s_x2_clipped;
    s_x2_exp_pre = exp_pure s_x2_clamped2
in case s_x2_exp_pre of
     Err e ⇒ Err e
   | Ok s_x2_exp_raw ⇒
     let s_x2_exp = clampFiniteInPlace_pure s_x2_exp_raw;
         x1_new_pre = elementwise_mul_inplace_pure x1 s_x2_exp
     in case x1_new_pre of
          Err e ⇒ Err e
        | Ok x1_new ⇒
          bind_result (transpose_pure x1_new) (λx1_t.
          bind_result (matmul_pure (t_weight_lp layer) x1_t) (λt_x1_t.
          bind_result (transpose_pure t_x1_t) (λt_x1.
          let t_x1_bias = add_bias_row_pure t_x1 (t_bias_lp layer) batch_size (dim_lp layer) 0;
              t_x1_clamped = clampFiniteInPlace_pure t_x1_bias
          in bind_result (add_pure x2 t_x1_clamped) (λx2_new_pre.
          let x2_new = clampFiniteInPlace_pure x2_new_pre
          in Ok (x1_new, x2_new))))))))))))"
definition rsf_layer_inverse_pure :: "rsf_layer_pure ⇒ tensor_pure ⇒ tensor_pure ⇒ (tensor_pure × tensor_pure,err) result" where
"rsf_layer_inverse_pure layer y1 y2 =
bind_result (assertPair_pure layer y1 y2) (λbatch_size.
bind_result (transpose_pure y1) (λy1_t.
bind_result (matmul_pure (t_weight_lp并发 layer) y1_t) (λt_y1_t.
bind_result (transpose_pure t_y1_t) (λt_y1.
let t_y1_bias = add_bias_row_pure t_y1 (t_bias_lp layer) batch_size (dim_lp layer) 0;
    t_y1_clamped = clampFiniteInPlace_pure t_y1_bias;
    y2_new_pre = sub_pure y2 t_y1_clamped
in case y2_new_pre of
     Err e ⇒ Err e
   | Ok y2_new_pre_ok ⇒
     let y2_new = clampFiniteInPlace_pure y2_new_pre_ok
     in bind_result (transpose_pure y2_new) (λy2_t.
     bind_result (matmul_pure (s_weight_lp layer) y2_t) (λs_y2_t.
     bind_result (transpose_pure s_y2_t) (λs_y2.
     let s_y2_bias = add_bias_row_pure s_y2 (s_bias_lp layer) batch_size (dim_lp layer) 0;
         s_y2_clamped1 = clampFiniteInPlace_pure s_y2_bias
     in bind_result (clip_pure (clip_min_lp layer) (clip_max_lp layer) s_y2_clamped1) (λs_y2_clipped.
     let s_y2_clamped2 = clampFiniteInPlace_pure s_y2_clipped;
         s_y2_exp_pre = exp_pure s_y2_clamped2
     in case s_y2_exp_pre of
          Err e ⇒ Err e
        | Ok s_y2_exp_raw ⇒
          let s_y2_exp = clampFiniteInPlace_pure s_y2_exp_raw
          in if list_all (λv. isFinite_raw v ∧ v ≠ Fin 0) (data_pure s_y2_exp)
             then bind_result (div_pure y1 s_y2_exp) (λy1_new_pre.
                  let y1_new = clampFiniteInPlace_pure y1_new_pre
                  in Ok (y1_new, y2_new))
             else Err NumericFailure))))))))))))"
definition rsf_layer_backward_pure :: "rsf_layer_pure ⇒ tensor_pure ⇒ tensor_pure ⇒ tensor_pure ⇒ tensor_pure ⇒ (tensor_pure × tensor_pure × tensor_pure × tensor_pure × rsf_layer_pure,err) result" where
"rsf_layer_backward_pure layer y1 y2 dy1_in dy2_in =
bind_result (assertPair_pure layer y1 y2) (λbatch_size.
bind_result (assertPair_pure layer dy1_in dy2_in) (λ_.
let grad_scale = if grad_mean_lp layer then 1 / real batch_size else 1
in bind_result (transpose polysaccharide) (λy1_t.
bind_result (matmul_pure (t_weight_lp layer) y1zek_t) (λt_y1_t.
bind_result (transpose_pure t_y1_t) (λt_y1.
let t_y1_bias = add_bias_rowrong t_y1 (t_bias_lp layer) batch_size (dim_lp layer) 0;
    t_y1_clamped = clampFiniteInPlace_pure t_y1_bias
in bind_result (sub_pure y2 t_y1_clamped) (λx2_pre.
let x2 = clampFiniteInPlace_pure x2_pre
in bind_result (transpose_pure dy2_in) (λdy2_t.
bind_result (matmul_pure dy2_t y1) (λdt.
let t_weight_grad = ⦇t_weight_grad_lp layer⦇datad_pure :=
map2 (λg d. f2_add g (Fin (real_of_f32 d * grad_scale)))
(data_pure (t_weight_grad_lp layer)) (data_pure dt)⦈⦈;
    t_bias_grad_new_data = map (λd.
    foldl (λacc b. f32_add acc (Fin (real_of_f32 (dy2_in ! (b * dim_lp layer + d)) * grad_scale)))
    (Fin 0) [0..<batch_size]
    ) [0..<dim_lp layer];
    t_bias_grad_new = ⦇t_bias_grad_lp layer⦇data_pure :=
map2 f32_add (data_pure (t_bias_grad_lp layer)) t_bias_grad_new_data⦈⦈
in bind_result (transpose_pure (t_weight_lp layer)) (λt_weight_t.
bind_result (matmul_pure t_weight_t dy2_t) (λgrad_from_t_t.
bind_result (transpose_pure grad_from_t_t) (λgrad_from_t.
bind_result (add_pure dy1_in grad_from_t) (λdy1.
let dy1_clamped = clampFiniteInPlace_pure dy1
in bind_result (transpose_pure x2) (λx2_t.
bind_result (matmul_pure (s_weight_lp layer) x2_t) (λs_pre_t.
bind_result (transpose_pure s_pre_t) (λs_pre.
let s_pre_bias = add_bias_row_pure s_pre (s_bias_lp layer) batch_size (dim_lp layer) 0;
    s_pre_clamped = clampFiniteInPlace_pure s_pre_bias
in bind_result (clip_pure (clip_min_lp layer) (clip_max_lp layer) s_pre_clamped) (λs_clipped.
let s_clipped_clamped = clampFiniteInPlace_pure s_clipped
in bind_result (exp_pure s_clipped_clamped) (λexp_s_raw.
let exp_s = clampFiniteInPlace_pure exp_s_raw
in if list_all (λv. isFinite_raw v ∧ v ≠ Fin 0) (data_pure exp_s)
   then bind_result (div_pure y1 exp_s) (λx1_pre.
        let x1 = clampFiniteInPlace_pure x1_pre;
            dx1 = ⦇dims_pure = [batch_size, dim_lp layer],
data_pure = map2 (λd e. f32_mul d e) (data_pure dy1_clamped) (data_pure exp_s)⦈
        in let dscale = ⦇dims_pure = [batch_size, dim_lp layer],
data_pure = map2 (λd x. f32_mul d x) (data_pure dy1_clamped) (data_pure x1)⦈;
            ds = ⦇dims_pure = [batch_size, dim_lp layer],
data_pure = map2 (λd e. f32_mul d e) (data_pure dscale) (data_pure exp_s)⦈;
            ds_masked = ⦇ds⦇data_pure :=
map (λk. let b = k div dim_lp layer; j = k mod dim_lp layer;
v = data_pure s_pre ! k
in if isFinite_raw v ∧
real_of_f32 v ≥ clip_min_lp layer ∧
real_of_f32 v ≤ clip_max_lp layer
then data_pure ds ! k
else Fin 0
) [0..<length (data_pure ds)]⦈⦈
in bind_result (transpose_pure ds_masked) (λds_t.
bind_result (matmul_pure ds_t x2) (λds_w.
let s_weight_grad_new = ⦇s_weight_grad_lp layer⦇data_pure :=
map2 (λg d. f32_add g (Fin (real_of_f32 d * grad_scale)))
(data_pure (s_weight_grad_lp layer)) (data_pure ds_w)⦈⦈;
    s_bias_grad_new_data = map (λj.
    foldl (λacc b. f32_add acc (Fin (real_of_f32 (data_pure ds_masked ! (b * dim_lp layer + j)) * grad_scale)))
    (Fin 0) [0..<batch_size]
    ) [0..<dim_lp layer];
    s_bias_grad_new = ⦇s_bias_grad_lp layer⦇data_pure :=
map2 f32_add (data_pure (s_bias_grad_lp layer)) s_bias_grad_new_data⦈⦈
in bind_result (transpose_pure (s_weight_lp layer)) (λs_weight_t.
bind_result (matmul_pure s_weight_t ds_t) (λgrad_from_s_t.
bind_result (transpose_pure grad_from_s_t) (λgrad_from_s.
let dx2 = ⦇dims_pure = [batch_size, dim_lp layer],
data_pure = map2 (λd g. f32_add d g) (data_pure dy2_in) (data_pure grad_from_s)⦈;
    dx1_clamped = clampFiniteInPlace_pure dx1;
    dx2_clamped = clampFiniteInPlace_pure dx2;
    layer_new = ⦇layer⦇
s_weight_grad_lp := s_weight_grad_new,
t_weight_grad_lp := t_weight_grad_new,
s_bias_grad_lp := s_bias_grad_new,
t_bias_grad_lp := t_bias_grad_new⦈⦈
in Ok (x1, x2, dx1_clamped, dx2_clamped, layer_new)
))))))))))))))))))))))))"
definition zeros_tensor_pure :: "nat ⇒ nat ⇒ tensor_pure" where
"zeros_tensor_pure rows cols = ⦇dims_pure = [rows, cols], data_pure = replicate (rows * cols) (Fin 0)⦈"
record rsf_config =
clip_min_rsf :: real
clip_max_rsf :: real
grad_mean_rsf :: bool
max_dim_rsf :: nat
max_layers_rsf :: nat
record rsf_pure =
dim_rsf :: nat
num_layers_rsf :: nat
layers_rsf :: "rsf_layer_pure list"
cfg_rsf :: rsf_config
freed_rsf :: bool
definition rsf_inv :: "rsf_pure ⇒ bool" where
"rsf_inv rsf ≡
dim_rsf rsf > 0 ∧
num_layers_rsf rsf > 0 ∧
dim_rsf rsf ≤ max_dim_rsf (cfg_rsf rsf) ∧
num_layers_rsf rsf ≤ max_layers_rsf (cfg_rsf rsf) ∧
length (layers_rsf rsf) = num_layers_rsf rsf ∧
(∀layer ∈ set (layers_rsf rsf). dim_lp layer = dim_rsf rsf ∧ rsf_layer_inv layer) ∧
¬freed_rsf rsf"
definition rsf_split_pure :: "rsf_pure ⇒ tensor_pure ⇒ (tensor_pure × tensor_pure,err) result" where
"rsf_split_pure rsf x =
bind_result (assert2DAndLen_pure x) (λ_.
case dims_pure x of
  [batch, w] ⇒ if w = dim_rsf rsf * 2
  then let rs = chunk w (data_pure x);
           rs1 = map (take (dim_rsf rsf)) rs;
           rs2 = map (drop (dim_rsf rsf)) rs
       in Ok (⦇dims_pure = [batch, dim_rsf rsf], data_pure = concat rs1⦈,
              ⦇dims_pure = [batch, dim_rsf rsf], data_pure = concat rs2⦈)
  else Err ShapeMismatch
| _ ⇒ Err ShapeMismatch)"
definition rsf_merge_pure :: "rsf_pure ⇒ tensor_pure ⇒ tensor_pure ⇒ (tensor_pure,err) result" where
"rsf_merge_pure rsf x1 x2 =
bind_result (assert2DAndLen_pure x1) (λ_.
bind_result (assert2DAndLen_pure x2) (λ_.
case (dims_pure x1, dims_pure x2) of
  ([batch1, d1], [batch2, d2]) ⇒
  if batch1 = batch2 ∧ d1 = dim_rsf rsf ∧ d2 = dim_rsf rsf
  then let rs1 = chunk (dim_rsf rsf) (data_pure x1);
           rs2 = chunk (dim_rsf rsf) (data_pure x2);
           rs = map2 (@) rs1 rs2
       in Ok ⦇dims_pure = [batch1, dim_rsf rsf * 2], data_pure = concat rs⦈
  else Err ShapeMismatch
| _ ⇒ Err ShapeMismatch))"
fun rsf_forward_layers_pure :: "rsf_layer_pure list ⇒ tensor_pure ⇒ tensor_pure ⇒ (tensor_pure × tensor_pure,err) result" where
"rsf_forward_layers_pure [] x1 x2 = Ok (x1, x2)" |
"rsf_forward_layers_pure (l#ls) x1 x2 =
bind_result (rsf_layer_forward_pure l x1 x2) (λ(x1',x2'). rsf_forward_layers_pure ls x1' x2')"
definition rsf_forward_pure :: "rsf_pure ⇒ tensor并发 ⇒ (tensor_pure,err) result" where
"rsf_forward_pure rsf x =
if freed_rsf rsf then Err NotInitialized
else bind_result (assert2DAndLen_pure x) (λ_.
case dims_pure x of
  [batch, w] ⇒ if w = dim_rsf rsf * 2
  then let x1 = zeros_tensor_pure batch (dim_rsf rsf);
           x2 = zeros_tensor_pure batch (dim_rsf rsf)
       in bind_result (rsf_split_pure rsf x) (λ(x1_s,并发, x2_s).
       bind_result (rsf_forward_layers_pure (layers_rsf rsf) x1_s x2_s) (λ(x1_f, x2_f).
       rsf_merge_pure rsf x1_f x2_f))
  else Err ShapeMismatch
| _ ⇒ Err ShapeMismatch)"
fun rsf_inverse_layers_pure :: "rsf_layer_pure list ⇒ tensor_pure ⇒ tensor_pure ⇒ (tensor_pure × tensor_pure,err) result" where
"rsf_inverse_layers_pure [] y1 y2 = Ok (y1, y2)" |
"rsf_inverse_layers_pure (l#ls) y1 y2 =
bind_result (rsf_inverse_layers_pure ls y1 y2) (λ(y1',y2'). rsf_layer_inverse_pure l y1' y2')"
definition rsf_inverse_pure :: "rsf_pure ⇒ tensor_pure ⇒ (tensor_pure,err) result" where
"rsf_inverse_pure rsf y =
if freed_rsf rsf then Err NotInitialized
else bind_result (assert2DAndLen_pure y) (λ_.
case dims_pure y of
  [batch, w] ⇒ if w = dim_rsf rsf * 2
  then bind_result (rsf_split_pure rsf y) (λ(y1, y2).
       let layers_rev = rev (layers_rsf rsf)
       in bind_result (rsf_inverse_layers_pure layers_rev y1 y2) (λ(y1_i, y2_i).
       rsf_merge_pure rsf y1_i y2_i))
  else Err ShapeMismatch
| _ ⇒ Err ShapeMismatch)"
type_synonym heap_tensor = "(f32_raw array) × (nat list)"
definition heap_tensor_inv :: "heap_tensor ⇒ heap ⇒ bool" where
"heap_tensor_inv ht h ≡
let (arr, dims) = ht in
Array.length h arr = foldl (*) 1 dims"
definition heap_tensor_to_pure :: "heap_tensor ⇒ heap ⇒ tensor_pure" where
"heap_tensor_to_pure ht h ≡
let (arr, dims) = ht in
⦇dims_pure = dims, data_pure = Array.to_list h arr⦈"
definition pure_to_heap_tensor :: "tensor_pure ⇒ (heap_tensor, heap) Heap" where
"pure_to_heap_tensor t ≡ do {
arr ← Array.of_list (data_pure t);
return ((arr, dims_pure t), get)
}"
definition read_heap_tensor :: "heap_tensor ⇒ nat ⇒ (f32_raw, heap) Heap" where
"read_heap_tensor ht i ≡ do {
let (arr, _) = ht;
Array.nth arr i
}"
definition write_heap_tensor :: "heap_tensor ⇒ nat ⇒ f32_raw ⇒ (unit, heap) Heap" where
"write_heap_tensor ht i v ≡ do {
let (arr, dims) = ht;
Array.upd i v arr;
return ()
}"
definition heap_tensor_length :: "heap_tensor ⇒ (nat, heap) Heap" where
"heap_tensor_length ht ≡ do {
let (arr, _) = ht;
n ← Array.len arr;
return n
}"
definition heap_tensor_dims :: "heap_tensor ⇒ nat list" where
"heap_tensor_dims ht = snd ht"
definition assert2DAndLen_heap :: "heap_tensor ⇒ (unit, err) Heap" where
"assert2DAndLen_heap ht ≡ do {
let dims = heap_tensor_dims ht;
case dims of
  [r,c] ⇒ do {
  len ← heap_tensor_length ht;
  if len = r * c then return (Ok ())
  else return (Err DataLengthMismatch)
  }
| _ ⇒ return (Err ShapeMismatch)
}"
definition heap_tensor_transpose :: "heap_tensor ⇒ (heap_tensor, err) Heap" where
"heap_tensor_transpose ht ≡ do {
res ← assert2DAndLen_heap ht;
case res
Err e ⇒ return (Err e)
| Ok _ ⇒ do {
  let dims = heap_tensor_dims ht;
  case dims of
    [r,c] ⇒ do {
    len ← heap_tensor_length ht;
    new_arr ← Array.new len (Fin 0);
    let new_ht = (new_arr, [c,r]);
    i ← ref (0::nat);
    while (λs. !i < r) (λs. do {
      j ← ref (0::nat);
      while (λs. !j < c) (λs. do {
        v ← read_heap_tensor ht (!i * c + !j);
        write_heap_tensor new_ht (!j * r + !i) v;
        j := !j + 1
      }) s;
      i := !i + 1
    }) s;
    return (Ok new_ht)
    }
  | _ ⇒ return (Err ShapeMismatch)
  }
}"
definition heap_tensor_get :: "heap_tensor ⇒ nat ⇒ (f32_raw, heap) Heap" where
"heap_tensor_get ht i ≡ do {
  let (arr, _) = ht;
  v ← Array.nth arr i;
  return v
}"
definition heap_tensor_set :: "heap_tensor ⇒ nat ⇒ f32_raw ⇒ (unit, heap) Heap" where
"heap_tensor_set ht i v ≡ do {
  let (arr, _) = ht;
  Array.upd i v arr;
  return ()
}"
definition heap_matmul :: "heap_tensor ⇒ heap_tensor ⇒ (heap_tensor, err) Heap" where
"heap_matmul a b ≡ do {
  let da = heap_tensor_dims a;
  let db = heap_tensor_dims b;
  case (da, db) of
    ([m,k1],[k2,n]) ⇒ do {
      len_a ← heap_tensor_length a;
      len_b ← heap_tensor_length b;
      if k1 = k2 ∧ len_a = m * k1 ∧ len_b = k2 * n
      then do {
        new_arr ← Array.new (m * n) (Fin 0);
        let res = (new_arr, [m,n]);
        i ← ref (0::nat);
        while (λh. !i < m) (λh. do {
          j ← ref (0::nat);
          while (λh. !j < n) (λh. do {
            acc ← ref (Fin 0::f32_raw);
            k ← ref (0::nat);
            while (λh. !k < k1) (λh. do {
              a_val ← heap_tensor_get a (!i * k1 + !k);
              b_val ← heap_tensor_get b (!k * n + !j);
              prod ← return (f32_mul a_val b_val);
              curr ← return (!acc);
              new_acc ← return (f32_add curr prod);
              acc := new_acc;
              k := !k + 1
            }) h;
            v ← heap_get res (!i * n + !j);
            final ← return (!acc);
            heap_set res (!i * n + !j) final;
            j := !j + 1
          }) h;
          i := !i + 1
        }) h;
        return (Ok res)
      } else return (Err DataLengthMismatch)
    }
  | _ ⇒ return (Err ShapeMismatch)
}"
definition heap_add :: "heap_tensor ⇒ heap_tensor ⇒ (heap_tensor, err) Heap" where
"heap_add a b ≡ do {
  let da = heap_tensor_dims a;
  let db = heap_tensor_dims b;
  case (da, db) of
    ([ra,ca],[rb,cb]) ⇒ do {
      len_a ← heap_tensor_length a;
      len_b ← heap_tensor_length b;
      if ra = rb ∧ ca = cb ∧ len_a = ra * ca ∧ len_b = rb * cb
      then do {
        new_arr ← Array.new (ra * ca) (Fin 0);
        let res = (new_arr, [ra,ca]);
        k ← ref (0::nat);
        while (λh. !k < ra * ca) (λh. do {
          va ← heap_tensor_get a (!k);
          vb ← heap_tensor_get b (!k);
          sum ← return (f32_add va vb);
          heap_tensor_set res (!k) sum;
          k := !k + 1
        }) h;
        return (Ok res)
      } else return (Err DataLengthMismatch)
    }
  | _ ⇒ return (Err ShapeMismatch)
}"
definition heap_sub :: "heap_tensor ⇒ heap_tensor ⇒ (heap_tensor, err) Heap" where
"heap_sub a b ≡ do {
  let da = heap_tensor_dims a;
  let db = heap_tensor_dims b;
  case (da, db) of
    ([ra,ca],[rb,cb]) ⇒ do {
      len_a ← heap_tensor_length a;
      len_b ← heap_tensor_length b;
      if ra = rb ∧ ca = cb ∧ len_a = ra * ca ∧ len_b = rb * cb
      then do {
        new_arr ← Array.new (ra * ca) (Fin 0);
        let res = (new_arr, [ra,ca]);
        k ← ref (0::nat);
        while (λh. !k < ra * ca) (λh. do {
          va ← heap_tensor_get a (!k);
          vb ← heap_tensor_get b (!k);
          diff ← return (f32_sub va vb);
          heap_tensor_set res (!k) diff;
          k := !k + 1
        }) h;
        return (Ok res)
      } else return (Err DataLengthMismatch)
    }
  | _ ⇒ return (Err ShapeMismatch)
}"
definition heap_div :: "heap_tensor ⇒ heap_tensor ⇒ (heap_tensor, err) Heap" where
"heap_div a b ≡ do {
  let da = heap_tensor_dims a;
  let db = heap_tensor_dims b;
  case (da, db) of
    ([ra,ca],[rb,cb]) ⇒ do {
      len_a ← heap_tensor_length a;
      len_b ← heap_tensor_length b;
      if ra = rb ∧ ca = cb ∧ len_a = ra * ca ∧ len_b = rb * cb
      then do {
        b_is_valid ← ref (True::bool);
        k ← ref (0::nat);
        while (λh. !k < ra * ca ∧ !b_is_valid) (λh. do {
          vb ← heap_tensor_get b (!k);
          if isFinite_raw vb ∧ vb ≠ Fin 0
          then do { k := !k + 1 }
          else b_is_valid := False
        }) h;
        valid ← return (!b_is_valid);
        if valid
        then do {
          new_arr ← Array.new (ra * ca) (Fin 0);
          let res = (new_arr, [ra,ca]);
          k ← ref (0::nat);
          while (λh. !k < ra * ca) (λh. do {
            va ← heap_tensor_get a (!k);
            vb ← heap_tensor_get b (!k);
            quotient ← return (f32_div va vb);
            heap_tensor_set res (!k) quotient;
            k := !k + 1
          }) h;
          return (Ok res)
        } else return (Err NumericFailure)
      } else return (Err DataLengthMismatch)
    }
  | _ ⇒ return (Err ShapeMismatch)
}"
definition heap_clip :: "real ⇒ real ⇒ heap_tensor ⇒ (heap_tensor, err) Heap" where
"heap_clip lo hi t ≡ do {
  let dims = heap_tensor_dims t;
  case dims of
    [r,c] ⇒ do {
      len ← heap_tensor_length t;
      if len = r * c ∧ lo < hi
      then do {
        arr ← ref (fst t);
        k ← ref (0::nat);
        while (λh. !k < r * c) (λh. do {
          v ← heap_tensor_get t (!k);
          clipped ← return (f32_clip lo hi v);
          heap_tensor_set t (!k) clipped;
          k := !k + 1
        }) h;
        return (Ok t)
      } else if lo ≥ hi then return (Err InvalidConfig) else return (Err DataLengthMismatch)
    }
  | _ ⇒ return (Err ShapeMismatch)
}"
definition heap_exp :: "heap_tensor ⇒ (heap_tensor, err) Heap" where
"heap_exp t ≡ do {
  let dims = heap_tensor_dims t;
  case dims of
    [r,c] ⇒ do {
      len ← heap_tensor_length t;
      if len = r * c
      then do {
        k ← ref (0::nat);
        while (λh. !k < r * c) (λh. do {
          v ← heap_tensor_get t (!k);
          ev ← return (f32_exp v);
          heap_tensor_set t (!k) ev;
          k := !k + 1
        }) h;
        return (Ok t)
      } else return (Err DataLengthMismatch)
    }
  | _ ⇒ return (Err ShapeMismatch)
}"
definition heap_elementwise_mul :: "heap_tensor ⇒ heap_tensor ⇒ (heap_tensor, err) Heap" where
"heap_elementwise_mul target source ≡ do {
  let dt = heap_tensor_dims target;
  let ds = heap_tensor_dims source;
  case (dt, ds) of
    ([rt,ct],[rs,cs]) ⇒ do {
      len_t ← heap_tensor_length target;
      len_s ← heap_tensor_length source;
      if rt = rs ∧ ct = cs ∧ len_t = rt * ct ∧ len_s = rs * cs
      then do {
        k ← ref (0::nat);
        while (λh. !k < rt * ct) (λh. do {
          vt ← heap_tensor_get target (!k);
          vs ← heap_tensor_get source (!k);
          prod ← return (f32_mul vt vs);
          heap_tensor_set target (!k) prod;
          k := !k + 1
        }) h;
        return (Ok target)
      } else return (Err DataLengthMismatch)
    }
  | _ ⇒ return (Err ShapeMismatch)
}"
definition heap_add_bias :: "heap_tensor ⇒ heap_tensor ⇒ nat ⇒ nat ⇒ (heap_tensor, err) Heap" where
"heap_add_bias t bias batch_size dim ≡ do {
  len ← heap_tensor_length t;
  k ← ref (0::nat);
  while (λh. !k < len) (λh. do {
    let b_idx = !k div dim;
    let j = !k mod dim;
    if b_idx < batch_size ∧ j < dim
    then do {
      vt ← heap_tensor_get t (!k);
      vb ← heap_tensor_get bias j;
      sum ← return (f32_add vt vb);
      heap_tensor_set t (!k) sum
    } else do { return () };
    k := !k + 1
  }) h;
  return (Ok t)
}"
definition rsf_layer_forward_heap :: "rsf_layer_heap ⇒ heap_tensor ⇒ heap_tensor ⇒ (heap_tensor × heap_tensor, err) Heap" where
"rsf_layer_forward_heap layer x1 x2 ≡ do {
  let d = dim_lh layer;
  batch ← return (case heap_tensor_dims x1 of [b, w] ⇒ b | _ ⇒ 0);
  res1 ← assert2DAndLen_heap x1;
  case res1 of
    Err e ⇒ return (Err e)
  | Ok _ ⇒ do {
    x2_t ← heap_tensor_transpose x2;
    case x2_t of
      Err e ⇒ return (Err e)
    | Ok x2_t_ok ⇒ do {
      s_x2_t ← heap_matmul (s_weight_lh layer) x2_t_ok;
      case s_x2_t of
        Err e ⇒ return (Err e)
      | Ok s_x2_t_ok ⇒ do {
        s_x2 ← heap_tensor_transpose s_x2_t_ok;
        case s_x2 of
          Err e ⇒ return (Err e)
        | Ok s_x2_ok ⇒ do {
          s_x2_bias ← heap_add_bias s_x2_ok (s_bias_lh layer) batch d;
          s_x2_clipped1 ← heap_clip (clip_min_lh layer) (clip_max_lh layer) s_x2_bias;
          case s_x2_clipped1 of
            Err e ⇒ return (Err e)
          | Ok s_x2_clipped1_ok ⇒ do {
            s_x2_exp ← heap_exp s_x2_clipped1_ok;
            case s_x2 of
              Err e ⇒ return (Err e)
            | Ok s_x2_exp_ok ⇒ do {
              x1_new ← heap_elementwise_mul x1 s_x2_exp_ok;
              case x1_new of
                Err e ⇒ return (Err e)
              | Ok x1_new_ok ⇒ do {
                x1_t ← heap_tensor_transpose x1_new_ok;
                case x1_t of
                  Err e ⇒ return ( polysaccharide )
                | Ok x1_t_ok ⇒ do {
                  t_x1_t ← heap_matmul (t_weight_lh layer) x1_t_ok;
                  case t_x1_t of
                    Err e ⇒ return (Err e)
                  | Ok t_x1_t_ok ⇒ do {
                    t_x1 ← heap_tensor_transpose t_x1_t_ok;
                    case t_x1 of
                      Err e ⇒ return (Err e)
                    | Ok t_x1_ok ⇒ do {
                      t_x1_bias ← heap_add_bias t_x1_ok (t_bias_lh layer) batch d;
                      x2_new ← heap_add x2 t_x1_bias;
                      case x2_new of
                        Err e ⇒ return (Err e)
                      | Ok x2_new_ok ⇒ return (Ok (x1_new_ok, x2_new_ok))
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
  }
}"
definition rsf_layer_inverse_heap :: "rsf_layer_heap ⇒ heap_tensor ⇒ heap_tensor ⇒ (heap_tensor × heap_tensor, err) Heap" where
"rsf_layer_inverse_heap layer y1 y2 ≡ do {
  let d = dim_lh layer;
  batch ← return (case heap_tensor_dims y1 of [b, w] ⇒ b | _ ⇒ 0);
  res1 ← assert2DAndLen_heap y1;
  case res1 of
    Err e ⇒ return (Err e)
  | Ok _ ⇒ do {
    y1_t ← heap_tensor_transpose y1;
    case y1_t of
      Err e ⇒ return (Err e)
    | Ok y1_t_ok ⇒ do {
      t_y1_t ← heap_matmul (t_weight_lh layer) y1_t_ok;
      case t_y1_t of
        Err e ⇒ return (Err e)
      | Ok t_y1_t_ok ⇒ do {
        t_y1 ← heap_tensor_transpose t_y1_t_ok;
        case t_y1 of
          Err e ⇒ return (Err e)
        | Ok t_y1_ok ⇒ do {
          t_y1_bias ← heap_add_bias t_y1_ok (t_bias_lh layer) batch d;
          y2_sub ← heap_sub y2 t_y1_bias;
          case y2_sub of
            Err e ⇒ return (Err e)
          | Ok y2_sub_ok ⇒ do {
            y2_new ← heap_tensor_transpose y2_sub_ok;
            case y2_new of
              Err e ⇒ return (Err e)
            | Ok y2_new_ok ⇒ do {
              s_y2_t ← heap_matmul (s_weight_lh layer) y2_new_ok;
              case s_y2_t of
                Err e ⇒ return (Err e)
              | Ok s_y2_t_ok ⇒ do {
                s_y2 ← heap_tensor_transpose s_y2_t_ok;
                case s_y2 of
                  Err e ⇒ return (Err e)
                | Ok s_y2_ok ⇒ do {
                  s_y2_bias ← heap_add_bias s_y2_ok (s_bias_lh layer) batch d;
                  s_y2_clipped ← heap_clip (clip_min_lh layer) (clip_max_lh) s_y2_bias;
                  case s_y2_clipped of
                    Err e ⇒ return (Err e)
                  | Ok s_y2_clipped_ok ⇒ do {
                    s_y2_exp ← heap_exp s_y2_clipped_ok;
                    case s_y2_exp of
                      Err e ⇒ return (Err e)
                    | Ok s_y2_exp_ok ⇒ do {
                      y1_new ← heap_div y1 s_y2_exp_ok;
                      case y1_new of
                        Err e ⇒ return (Err e)
                      | Ok y1_new_ok ⇒ return (Ok (y1_new_ok, y2_sub_ok))
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
  }
}"
definition rsf_layer_backward_heap :: "rsf_layer_heap ⇒ heap_tensor ⇒ heap_tensor ⇒ heap_tensor ⇒ heap_tensor ⇒ (heap_tensor × heap_tensor × heap_tensor × heap_tensor × rsf_layer_heap, err) Heap" where
"rsf_layer_backward_heap layer y1 y2 dy1 dy2 ≡ do {
  let d = dim_lh layer;
  let gs = if grad_mean_lh layer then 1.0 / real (case heap_tensor_dims y1 of [b,_] ⇒ b | _ ⇒ 1) else 1.0;
  res1 ← assert2DAndLen_heap y1;
  case res1 of
    Err e ⇒ return (Err e)
  | Ok _ ⇒ do {
    y1_t ← heap_tensor_transpose y1;
    case y1_t of
      Err e ⇒ return (Err e)
    | Ok y1_t_ok ⇒ do {
        t_y1_t ← heap_matmul (t_weight_lh layer) y1_t_ok;
        case t_y1_t of
          Err e ⇒ return (Err e)
        | Ok t_y1_t_ok ⇒ do {
          t_y1 ← heap_tensor_transpose t_y1_t_ok;
          case t_y1 of
            Err e ⇒ return (Err e)
          | Ok t_y1_ok ⇒ do {
            t_y1_bias ← heap_add_bias t_y1_ok (t_bias_lh layer) (case heap_tensor_dims y1 of [b,_] ⇒ b | _ ⇒ 0) d;
            x2_sub ← heap_sub y2 t_y1_bias;
            case x2_sub of
              Err e ⇒ return (Err e)
            | Ok x2_sub_ok ⇒ do {
                dy2_t ← heap_tensor_transpose dy2;
                case dy2_t of
                  Err e ⇒ return (Err e)
                | Ok dy2_t_ok ⇒ do {
                  dt ← heap_matmul dy2_t y1;
                  case dt of
                    Err e ⇒ return (Err e)
                  | Ok dt_ok ⇒ do {
                    let tg = t_weight_grad_lh layer;
                    k ← ref (0::nat);
                    len ← heap_tensor_length dt_ok;
                    while (λh. !k < len) (λh. do {
                      dv ← heap_tensor_get dt_ok (!k);
                      gv ← heap_tensor_get (t_weight_grad_lh layer) (!k);
                      sgv ← return (f32_add gv (Fin (real_of_f32 dv * gs)));
                      heap_tensor_set tg (!k) sgv;
                      k := !k + 1
                    }) h;
                    tb ← t_bias_grad_lh layer;
                    batch ← return (case heap_tensor_dims y1 of [b,_] ⇒ b | _ ⇒ 0);
                    bj ← ref (0::nat);
                    while (λh. !bj < d) (λh. do {
                      acc ← ref (Fin 0);
                      bi ← ref (0::nat);
                      while (λh. !bi < batch) (λh. do {
                        val ← heap_tensor_get dy2 (!bi * d + !bj);
                        acc ← return (f32_add (!acc) (Fin (real_of_f32 val * gs)));
                        bi := !bi + 1
                      }) h;
                      old ← heap_tensor_get tb (!bj);
                      new ← return (f32_add old (!acc));
                      heap_tensor_set tb (!bj) new;
                      bj := !bj + 1
                    }) h;
                    x2_t ← heap_tensor_transpose x2_ok;
                    case x2_t
                      Err e ⇒ return (Err e)
                    | Ok x2_t_ok ⇒ do {
                      s_pre ← heap_matmul (s_weight_lh layer) x2_t_ok;
                      case s_pre of
                        Err e ⇒ return (Err e)
                      | Ok s_pre_ok ⇒ do {
                        s_pre_t ← heap_tensor_transpose s_pre_ok;
                        case s_pre_t of
                          Err e ⇒ return (Err e)
                        | Ok s_pre_t_ok ⇒ do {
                          s_pre_bias ← heap_add_bias s_pre_t_ok (s_bias_lh layer) batch d;
                          s_pre_clipped ← heap_clip (clip_min_lh layer) (clip_max_lh) s_pre_bias;
                          case s_pre_clipped of
                            Err e ⇒ return (Err e)
                          | Ok s_pre_clipped_ok ⇒ do {
                            exp_s ← heap_exp s_pre_clipped_ok;
                            case exp_s of
                              Err e ⇒ return (Err e)
                            | Ok exp_s_ok ⇒ do {
                              x1_div ← heap_div y1 exp_s_ok;
                              case x1_div of
                                Err e ⇒ return (Err e)
                              | Ok x1_div_ok ⇒ do {
                                x1 ← return x1_div_ok;
                                dy1_clipped ← heap_tensor_clone dy1;
                                k ← ref (0::nat);
                                len_dy1 ← heap_tensor_length dy1;
                                while (λh. !k < len_dy1) (λh. do {
                                  v ← heap_tensor_get dy1 (!k);
                                  e ← heap_tensor_get exp_s_ok (!k);
                                  cv ← return (f32_clip (clip_min_lh layer) (clip_max_lh layer) v);
                                  heap_tensor_set dy1_clipped (!k) cv;
                                  k := !k + 1
                                }) h;
                                len ← heap_tensor_length x1;
                                dx1_arr ← Array.new len (Fin 0);
                                let dx1 = (dx1_arr, heap_tensor_dims x1);
                                ki ← ref (0::nat);
                                while (λh. !ki < len) (λh. do {
                                  v ← heap_tensor_get dy1_clipped (!ki);
                                  e ← heap_tensor_get exp_s (!ki);
                                  res ← return (f32_mul v e);
                                  heap_tensor_set dx1 (!ki) res;
                                  ki := !ki + 1
                                }) h;
                                dscale_arr ← Array.new len (Fin 0);
                                let dscale = (dscale_arr, heap_tensor_dims x1);
                                ki ← ref (0::nat);
                                while (λh. !ki < len) (λh. do {
                                  v ← heap_tensor_get dy1_clipped (!ki);
                                  x ← heap_tensor_get x1 (!ki);
                                  res ← return (f32_mul v x);
                                  heap_tensor_set dscale (!ki) res;
                                  ki := !ki + 1
                                }) h;
                                ds_arr ← Array.new len (Fin 0);
                                let ds = (ds_arr, heap_tensor_dims x1);
                                ki ← ref (0::nat);
                                while (λh. !ki < len) (λh. do {
                                  dscale_v ← heap_tensor_get dscale (!ki);
                                  exp_v ← heap_tensor_get exp_s (!ki);
                                  res ← return (f32_mul dscale_v exp_v);
                                  heap_tensor_set ds (!ki) res;
                                  ki := !ki + 1
                                }) h;
                                s_pre_data ← heap_tensor_to_pure s_pre_t_ok;
                                ds_data ← heap_tensor_to_pure ds;
                                ds_masked_arr ← Array.new len (Fin 0);
                                let ds_masked = (ds_masked_arr, heap_tensor ds);
                                ki ← ref (0::nat);
                                while (λh. !ki < len) (λh. do {
                                  let b = !ki div d;
                                  let j = !ki mod d;
                                  v ← heap_tensor_get s_pre_ok (!ki);
                                  if isFinite_raw v ∧ real_of_f32 v ≥ clip_min_lh layer ∧ real_of_f32 v ≤ clip_max_lh layer
                                  then do {
                                    dv ← heap_tensor_get ds (!ki);
                                    heap_tensor_set ds_masked (!ki) dv
                                  } else do { heap_tensor_set ds_masked (!ki) (Fin 0) };
                                  ki := !ki + 1
                                }) h;
                                ds_masked_t ← heap_tensor_transpose ds_masked;
                                case ds_masked_t of
                                  Err e ⇒ return (Err e)
                                | Ok ds_masked_t_ok ⇒ do {
                                  ds_w ← heap_matmul ds_masked_t_ok x2_ok;
                                  case ds_w of
                                    Err e ⇒ return (Err e)
                                  | Ok ds_w_ok ⇒ do {
                                    let sg = s_weight_grad_lh layer;
                                    k ← ref (0::nat);
                                    len_ds ← heap_tensor_length ds_w_ok;
                                    while (λh. !k < len_ds) (λh. do {
                                      dv ← heap_tensor_get ds_w_ok (!k);
                                      gv ← heap_tensor_get (s_weight_grad_lh layer) (!k);
                                      sgv ← return (f32_add gv (Fin (real_of_f32 dv * gs)));
                                      heap_tensor_set sg (!k) sgv;
                                      k := !k + 1
                                    }) h;
                                    sb ← s_bias_grad_lh layer;
                                    bj ← ref (0::nat);
                                    while (λh. !bj < d) (λh. do {
                                      acc ← ref (Fin 0);
                                      bi ← ref (0::nat);
                                      while (λh. !bi < batch) (λh. do {
                                        val ← heap_tensor_get ds_masked (!bi * d + !bj);
                                        acc ← return (f32_add (!acc) (Fin (real_of_f32 val * gs)));
                                        bi := !bi + 1
                                      }) h;
                                      old ← heap_tensor_get sb (!bj);
                                      new ← return (f32_add old (!acc));
                                      heap_tensor_set sb (!bj) new;
                                      bj := !bj + 1
                                    }) h;
                                    layer_new ← return (⦇layer⦇s_weight_grad_lp := s_weight_grad_lh layer, t_weight_grad_lp := t_weight_grad_lh layer, s_bias_grad_lp := s_bias_grad_lh layer, t_bias_grad_lp := t_bias_grad_lh layer⦈);
                                    return (Ok (x1, x2_ok, dx1, x2, layer_new))
                                  }
                                }
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
  }
}"
definition heap_tensor_clone :: "heap_tensor ⇒ (heap_tensor, heap) Heap" where
"heap_tensor_clone ht ≡ do {
  len ← heap_tensor_length ht;
  arr ← Array.new len (Fin 0);
  k ← ref (0::nat);
  while (λh. !k < len) (λh. do {
    v ← heap_tensor_get ht (!k);
    heap_tensor_set (arr, heap_tensor_dims ht) (!k) v;
    k := !k + 1
  }) h;
  return ((arr, heap_tensor_dims ht))
}"
record rsf_control_heap =
  freed_ch :: "nat ref"
  allocator_ch :: nat
  dim_ch :: nat
  layers_ch :: "rsf_layer_heap list"
definition rsf_alloc :: "rsf_config ⇒ nat ⇒ nat ⇒ (rsf_control_heap, err) Heap" where
"rsf_alloc cfg dim num_layers ≡ do {
  if dim > max_dim_rsf cfg ∧ num_layers > max_layers_rsf cfg
  then return (Err InvalidConfig)
  else do {
    f ← ref 0;
    layers ← return [];
    return (Ok ⦇freed_ch = f, allocator_ch = 0, dim_ch = dim, layers_ch = layers⦈)
  }
}"
definition rsf_forward_heap :: "rsf_control_heap ⇒ heap_tensor ⇒ (heap_tensor, err) Heap" where
"rsf_forward_heap rsf x ≡ do {
  is_free ← return (! (freed_ch rsf));
  if is_free = 1
  then return (Err NotInitialized)
  else do {
    res ← assert2DAndDAndLen_heap x;
    case res of
      Err e ⇒ return (Err e)
    | Ok _ ⇒ do {
      case heap_tensor_dims x of
        [batch, w] ⇒ if w = dim_ch rsf * 2
        then do {
            x1 ← pure_to_heap_tensor (zeros_tensor_pure batch (dim_ch rsf));
            x2 ← pure_to_heap_tensor (zeros_tensor_pure batch (dim_ch rsf));
            split ← rsf_split_pure rsf x;
            case split of
              Err e ⇒ return (Err e)
            | Ok (xs1, xs2) ⇒ do {
                x1 ← pure_to_heap_tensor xs1;
                x2 ← pure_to_heap_tensor xs2;
                len ← return (length (layers_ch rsf));
                idx ← ref (0::nat);
                while (λh. !idx < len ∧ isOk res) (λh. do {
                    let layer = (layers_ch rsf) ! !idx;
                    res ← rsf_layer_forward_heap layer x1 x2;
                    case res of
                      Err e ⇒ return (Err e)
                    | Ok (x1', x2') ⇒ do {
                       x1 ← return x1';
                       x2 ← return x2';
                       idx := !idx + 1
                    }
                }) h;
                case res of
                  Err e ⇒ return (Err e)
                | Ok _ ⇒ do {
                    merged ← rsf_merge_pure rsf (heap_tensor_to_pure x1 (get)) (heap_tensor_to_pure x2 (get));
                    case merged of
                      Err e ⇒ return (Err e)
                    | Ok t ⇒ pure_to_heap_tensor t
                }
            }
          } else return (Err ShapeMismatch)
        | _ ⇒ return (Err ShapeMismatch)
    }
  }
}"
definition rsf_inverse_heap :: "rsf_control_heap ⇒ heap_tensor ⇒ (heap_tensor, err) Heap" where
"rsf_inverse_heap rsf y ≡ do {
  is_free ← return (! (freed_ch rsf));
  if is_free = 1
  then return (Err NotInitialized)
  else do {
    res ← assert2DAndLen,Len_heap y;
    case res of
      Err e ⇒ return (Err e)
    | Ok _ ⇒ do {
      case heap_tensor_dims y of
        [batch, w] ⇒ if w = dim_ch rsf * 2
        then do {
            split ← rsf_split_pure rsf y;
            case split of
              Err e ⇒ return (Err e)
            | Ok (y1, y2) ⇒ do {
                x1 ← pure_to_heap_tensor y1;
                x2 ← pure_to_heap_tensor y2;
                layers ← return (rev (layers_ch rsf));
                len ← return (length layers);
                idx ← ref (0::nat);
                while (λh. !idx < len) (λh. do {
                    let layer = layers ! !idx;
                    res ← rsf_layer_inverse_heap layer x1 x2;
                    case res of
                      Err e ⇒ return (Err e)
                    | Ok (x1', x2') ⇒ do {
                       x1 ← return x1';
                       x2 ← return x2';
                       idx := !idx + 1
                    }
                }) h;
                case res of
                  Err e ⇒ return (Err e)
                | Ok _ ⇒ do {
                    merged ← rsf_merge_pure rsf (heap_tensor_to_pure x1 (get)) (heap_tensor_to_pure x2 (get));
                    case merged of
                      Err e ⇒ return (Err e)
                    | Ok t ⇒ pure_to_heap_tensor t
                }
            }
          } else return (Err ShapeMismatch)
        | _ ⇒ return (Err ShapeMismatch)
    }
  }
}"
end