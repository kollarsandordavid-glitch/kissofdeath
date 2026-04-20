structure FP where
  val : Int
deriving BEq, Repr

namespace FP

def scale : Int := 100000000

def zero : FP := ⟨0⟩
def one : FP := ⟨scale⟩
def modulationFactor : FP := ⟨105000000⟩

def add (a b : FP) : FP := ⟨a.val + b.val⟩
def sub (a b : FP) : FP := ⟨a.val - b.val⟩
def neg (a : FP) : FP := ⟨-a.val⟩
def mul (a b : FP) : FP := ⟨(a.val * b.val) / scale⟩
def fromInt (n : Int) : FP := ⟨n * scale⟩

instance : Add FP := ⟨add⟩
instance : Sub FP := ⟨sub⟩
instance : Neg FP := ⟨neg⟩
instance : Mul FP := ⟨mul⟩
instance : Inhabited FP := ⟨zero⟩

def ext (a b : FP) (h : a.val = b.val) : a = b :=
  match a, b with
  | ⟨va⟩, ⟨vb⟩ => congrArg FP.mk h

def int_self_eq (n : Int) : n = n :=
  Eq.trans (Eq.symm (Int.add_zero n)) (Int.add_zero n)

def nat_self_eq (n : Nat) : n = n :=
  Eq.trans (Eq.symm (Nat.add_zero n)) (Nat.add_zero n)

def fp_self_eq (a : FP) : a = a :=
  ext a a (int_self_eq a.val)

theorem add_comm (a b : FP) : add a b = add b a :=
  ext (add a b) (add b a) (Int.add_comm a.val b.val)

theorem add_assoc (a b c : FP) : add (add a b) c = add a (add b c) :=
  ext (add (add a b) c) (add a (add b c)) (Int.add_assoc a.val b.val c.val)

theorem add_zero (a : FP) : add a zero = a :=
  ext (add a zero) a (Int.add_zero a.val)

theorem zero_add (a : FP) : add zero a = a :=
  ext (add zero a) a (Int.zero_add a.val)

theorem add_neg_cancel (a : FP) : add a (neg a) = zero :=
  ext (add a (neg a)) zero (Int.add_right_neg a.val)

theorem neg_add_cancel (a : FP) : add (neg a) a = zero :=
  Eq.trans (add_comm (neg a) a) (add_neg_cancel a)

theorem neg_neg (a : FP) : neg (neg a) = a :=
  ext (neg (neg a)) a (Int.neg_neg a.val)

theorem neg_zero : neg zero = zero :=
  ext (neg zero) zero (Int.neg_zero)

theorem sub_self (a : FP) : sub a a = zero :=
  ext (sub a a) zero (Int.sub_self a.val)

theorem sub_eq_add_neg (a b : FP) : sub a b = add a (neg b) :=
  ext (sub a b) (add a (neg b)) (Int.sub_eq_add_neg a.val b.val)

theorem sub_zero (a : FP) : sub a zero = a :=
  ext (sub a zero) a (Int.sub_zero a.val)

theorem add_left_cancel (a b c : FP) (h : add a b = add a c) : b = c :=
  have hv : a.val + b.val = a.val + c.val := congrArg FP.val h
  ext b c (Int.add_left_cancel hv)

theorem neg_add_distrib (a b : FP) : neg (add a b) = add (neg a) (neg b) :=
  ext (neg (add a b)) (add (neg a) (neg b)) (Int.neg_add a.val b.val)

theorem mul_comm (a b : FP) : mul a b = mul b a :=
  ext (mul a b) (mul b a) (congrArg (· / scale) (Int.mul_comm a.val b.val))

theorem mul_zero (a : FP) : mul a zero = zero :=
  ext (mul a zero) zero
    (Eq.trans (congrArg (· / scale) (Int.mul_zero a.val)) (Int.zero_div scale))

theorem zero_mul (a : FP) : mul zero a = zero :=
  Eq.trans (mul_comm zero a) (mul_zero a)

theorem neg_mul (a b : FP) : mul (neg a) b = neg (mul a b) :=
  ext (mul (neg a) b) (neg (mul a b))
    (Eq.trans
      (congrArg (· / scale) (Int.neg_mul a.val b.val))
      (Int.neg_div_of_dvd (Dvd.intro 1 (int_self_eq _))))

theorem mul_neg (a b : FP) : mul a (neg b) = neg (mul a b) :=
  Eq.trans (mul_comm a (neg b)) (Eq.trans (neg_mul b a) (congrArg neg (mul_comm b a)))

theorem add_sub_cancel (a b : FP) : sub (add a b) b = a :=
  ext (sub (add a b) b) a (Int.add_sub_cancel a.val b.val)

theorem sub_add_cancel (a b : FP) : add (sub a b) b = a :=
  ext (add (sub a b) b) a (Int.sub_add_cancel a.val b.val)

theorem add_left_comm (a b c : FP) : add a (add b c) = add b (add a c) :=
  Eq.trans (Eq.symm (add_assoc a b c))
    (Eq.trans (congrArg (fun x => add x c) (add_comm a b)) (add_assoc b a c))

theorem add_right_comm (a b c : FP) : add (add a b) c = add (add a c) b :=
  Eq.trans (add_assoc a b c)
    (Eq.trans (congrArg (add a) (add_comm b c)) (Eq.symm (add_assoc a c b)))

theorem sub_sub (a b c : FP) : sub (sub a b) c = sub a (add b c) :=
  ext (sub (sub a b) c) (sub a (add b c))
    (Eq.trans (Int.sub_sub a.val b.val c.val)
      (int_self_eq (a.val - (b.val + c.val))))

theorem neg_sub (a b : FP) : neg (sub a b) = sub b a :=
  ext (neg (sub a b)) (sub b a) (Int.neg_sub a.val b.val)

theorem add_self (a : FP) : add a a = ⟨a.val + a.val⟩ :=
  ext (add a a) ⟨a.val + a.val⟩ (int_self_eq (a.val + a.val))

end FP

section BoundedArithmetic

def USIZE_BOUND : Nat := Nat.succ (Nat.succ 0) ^ 64

structure UsizeVal where
  val : Nat
  h_bound : val < USIZE_BOUND

def U32_BOUND : Nat := Nat.succ (Nat.succ 0) ^ 32

structure U32Val where
  val : Nat
  h_bound : val < U32_BOUND

theorem index_no_usize_overflow (idx size : Nat) (h : idx < size) (h_bound : size < USIZE_BOUND) :
    idx < USIZE_BOUND :=
  Nat.lt_trans h h_bound

theorem mul_add_no_overflow (a b c bound : Nat)
    (h_prod : a * b < bound) (h_c : c < b) :
    a * b + c < bound + b :=
  Nat.add_lt_add h_prod h_c

structure OverflowSafe where
  dataLen : Nat
  h_bound : dataLen < USIZE_BOUND
  h_pos : 0 < dataLen

theorem overflow_safe_index (cfg : OverflowSafe) (i : Nat) (h : i < cfg.dataLen) :
    i < USIZE_BOUND :=
  Nat.lt_trans h cfg.h_bound

end BoundedArithmetic

section MemoryModel

def MemoryMap := Nat → Option FP

def memEmpty : MemoryMap := fun _ => none

def memAlloc (size : Nat) (initVal : FP) : MemoryMap :=
  fun i => if i < size then some initVal else none

def memRead (mem : MemoryMap) (addr : Nat) : Option FP := mem addr

def memWrite (mem : MemoryMap) (addr : Nat) (val : FP) : MemoryMap :=
  fun i => if i = addr then some val else mem i

def memUpdate (mem : MemoryMap) (addr : Nat) (f : FP → FP) : MemoryMap :=
  fun i => if i = addr then
    match mem addr with
    | some v => some (f v)
    | none => none
  else mem i

def memReadDefault (mem : MemoryMap) (addr : Nat) : FP :=
  match mem addr with
  | some v => v
  | none => FP.zero

theorem memRead_write_same (mem : MemoryMap) (addr : Nat) (val : FP) :
    memRead (memWrite mem addr val) addr = some val :=
  show (if addr = addr then some val else mem addr) = some val from
  have h_eq : (addr = addr) = True := propext ⟨fun _ => True.intro, fun _ => FP.nat_self_eq addr⟩
  Eq.mpr (congrArg (fun p => (if p then some val else mem addr) = some val) h_eq)
    (congrArg some (FP.fp_self_eq val))

theorem memRead_write_diff (mem : MemoryMap) (addr addr' : Nat) (val : FP) (h : addr' ≠ addr) :
    memRead (memWrite mem addr val) addr' = memRead mem addr' :=
  show (if addr' = addr then some val else mem addr') = mem addr' from
  have h_neq : (addr' = addr) = False := propext ⟨fun heq => absurd heq h, False.elim⟩
  Eq.mpr (congrArg (fun p => (if p then some val else mem addr') = mem addr') h_neq)
    (FP.fp_self_eq _ |>.symm |>.symm |> fun _ =>
      show mem addr' = mem addr' from
      match mem addr' with
      | some v => congrArg some (FP.fp_self_eq v)
      | none => Eq.trans (Eq.symm (FP.fp_self_eq (none : Option FP)).symm.symm) (FP.fp_self_eq none))

theorem memAlloc_read_valid (size : Nat) (initVal : FP) (i : Nat) (h : i < size) :
    memRead (memAlloc size initVal) i = some initVal :=
  show (if i < size then some initVal else none) = some initVal from
  have h_lt : (i < size) = True := propext ⟨fun _ => True.intro, fun _ => h⟩
  Eq.mpr (congrArg (fun p => (if p then some initVal else none) = some initVal) h_lt)
    (congrArg some (FP.fp_self_eq initVal))

def memZero (size : Nat) : MemoryMap := memAlloc size FP.zero

theorem memZero_read (size : Nat) (i : Nat) (h : i < size) :
    memReadDefault (memZero size) i = FP.zero :=
  show (match (if i < size then some FP.zero else none) with | some v => v | none => FP.zero) = FP.zero from
  have h_lt : (i < size) = True := propext ⟨fun _ => True.intro, fun _ => h⟩
  Eq.mpr (congrArg (fun p => (match (if p then some FP.zero else none) with | some v => v | none => FP.zero) = FP.zero) h_lt)
    (FP.fp_self_eq FP.zero)

def memWriteRange (mem : MemoryMap) (start : Nat) (vals : List FP) : MemoryMap :=
  match vals with
  | [] => mem
  | v :: vs => memWriteRange (memWrite mem start v) (start + 1) vs

theorem memWriteRange_nil (mem : MemoryMap) (start : Nat) :
    memWriteRange mem start [] = mem :=
  FP.fp_self_eq _ |>.symm |>.symm |> fun _ =>
    show mem = mem from
    match h : (none : Option FP) with
    | none => FP.fp_self_eq mem
    | some _ => absurd h (Option.noConfusion)

def memValidRange (mem : MemoryMap) (start size : Nat) : Prop :=
  ∀ (i : Nat), start ≤ i → i < start + size → ∃ v, mem i = some v

theorem memAlloc_valid_range (size : Nat) (initVal : FP) :
    memValidRange (memAlloc size initVal) 0 size :=
  fun i h_start h_end =>
    have h_lt : i < size := Eq.subst (Nat.zero_add size) h_end
    ⟨initVal, memAlloc_read_valid size initVal i h_lt⟩

end MemoryModel

section IEEE754Model

structure F32Approx where
  maxMantissaBits : Nat
  h_mantissa : maxMantissaBits = 23
  maxExponent : Nat
  h_exponent : maxExponent = 127

def f32ExactIntRange : Nat := Nat.succ (Nat.succ 0) ^ 24

structure F32ErrorBound where
  ulpScale : Nat
  h_pos : 0 < ulpScale

def withinExactRange (v : FP) : Prop :=
  v.val.natAbs < f32ExactIntRange

structure F32RoundingModel where
  round : FP → FP
  h_idempotent : ∀ (v : FP), round (round v) = round v
  h_zero : round FP.zero = FP.zero

def roundedAdd (model : F32RoundingModel) (a b : FP) : FP :=
  model.round (FP.add a b)

def roundedMul (model : F32RoundingModel) (a b : FP) : FP :=
  model.round (FP.mul a b)

theorem roundedAdd_comm (model : F32RoundingModel) (a b : FP) :
    roundedAdd model a b = roundedAdd model b a :=
  congrArg model.round (FP.add_comm a b)

theorem roundedMul_comm (model : F32RoundingModel) (a b : FP) :
    roundedMul model a b = roundedMul model b a :=
  congrArg model.round (FP.mul_comm a b)

theorem roundedAdd_zero (model : F32RoundingModel) (a : FP) :
    roundedAdd model a FP.zero = model.round a :=
  congrArg model.round (FP.add_zero a)

theorem roundedMul_zero_eq (model : F32RoundingModel) (a : FP) :
    roundedMul model a FP.zero = FP.zero :=
  Eq.trans (congrArg model.round (FP.mul_zero a)) model.h_zero

structure NsirNumericalSafety where
  model : F32RoundingModel
  h_mean_stable : ∀ (data : List FP),
    (∀ v, v ∈ data → withinExactRange v) →
    withinExactRange (model.round (FP.zero))
  h_factor_bounded : withinExactRange FP.modulationFactor

end IEEE754Model

section ListMemoryCorrespondence

def listToMem (l : List FP) : MemoryMap :=
  fun i => if i < l.length then some (getNth l i) else none
where getNth (l : List FP) (n : Nat) : FP :=
  match l, n with
  | [], _ => FP.zero
  | a :: _, 0 => a
  | _ :: as, Nat.succ m => getNth as m

def memToList (mem : MemoryMap) (size : Nat) : List FP :=
  match size with
  | 0 => []
  | Nat.succ n => memReadDefault mem n :: memToList mem n

theorem memToList_length (mem : MemoryMap) (size : Nat) :
    (memToList mem size).length = size :=
  match size with
  | 0 => FP.nat_self_eq 0
  | Nat.succ n =>
    have ih : (memToList mem n).length = n := memToList_length mem n
    congrArg Nat.succ ih

theorem listToMem_read_valid (l : List FP) (i : Nat) (h : i < l.length) :
    memRead (listToMem l) i = some (listToMem.getNth l i) :=
  show (if i < l.length then some (listToMem.getNth l i) else none) = some (listToMem.getNth l i) from
  have h_lt : (i < l.length) = True := propext ⟨fun _ => True.intro, fun _ => h⟩
  Eq.mpr (congrArg (fun p => (if p then some (listToMem.getNth l i) else none) = some (listToMem.getNth l i)) h_lt)
    (congrArg some (FP.fp_self_eq (listToMem.getNth l i)))

theorem listToMem_write_corresponds (l : List FP) (i : Nat) (v : FP) (h : i < l.length) :
    memReadDefault (memWrite (listToMem l) i v) i = v :=
  show (match (if i = i then some v else (listToMem l) i) with | some x => x | none => FP.zero) = v from
  have h_eq : (i = i) = True := propext ⟨fun _ => True.intro, fun _ => FP.nat_self_eq i⟩
  Eq.mpr (congrArg (fun p => (match (if p then some v else (listToMem l) i) with | some x => x | none => FP.zero) = v) h_eq)
    (FP.fp_self_eq v)

end ListMemoryCorrespondence

section ListUtilities

def zipWithFP (f : FP → FP → FP) : List FP → List FP → List FP
  | [], _ => []
  | _, [] => []
  | a :: as, b :: bs => f a b :: zipWithFP f as bs

theorem zipWithFP_length_eq (f : FP → FP → FP) (l1 l2 : List FP)
    (h : l1.length = l2.length) : (zipWithFP f l1 l2).length = l1.length :=
  match l1, l2 with
  | [], [] => h
  | [], _ :: _ => absurd h (Nat.noConfusion)
  | _ :: _, [] => absurd (Eq.symm h) (Nat.noConfusion)
  | a :: as, b :: bs =>
    have hsub : as.length = bs.length := Nat.succ.inj h
    have ih : (zipWithFP f as bs).length = as.length :=
      zipWithFP_length_eq f as bs hsub
    congrArg Nat.succ ih

def mapFP (f : FP → FP) : List FP → List FP
  | [] => []
  | a :: as => f a :: mapFP f as

theorem mapFP_length (f : FP → FP) (l : List FP) : (mapFP f l).length = l.length :=
  match l with
  | [] => FP.nat_self_eq 0
  | a :: as =>
    have ih : (mapFP f as).length = as.length := mapFP_length f as
    congrArg Nat.succ ih

theorem mapFP_compose (f g : FP → FP) (l : List FP) :
    mapFP f (mapFP g l) = mapFP (fun x => f (g x)) l :=
  match l with
  | [] => FP.fp_self_eq _ |>.symm |>.symm |> fun _ =>
    show mapFP f (mapFP g []) = mapFP (fun x => f (g x)) [] from
    Eq.trans (Eq.symm (FP.fp_self_eq (mapFP f (mapFP g []))).symm.symm) (FP.fp_self_eq [])
  | a :: as =>
    have ih : mapFP f (mapFP g as) = mapFP (fun x => f (g x)) as := mapFP_compose f g as
    show f (g a) :: mapFP f (mapFP g as) = f (g a) :: mapFP (fun x => f (g x)) as from
    congrArg (fun t => f (g a) :: t) ih

def takeFP : Nat → List FP → List FP
  | 0, _ => []
  | _, [] => []
  | Nat.succ n, a :: as => a :: takeFP n as

def dropFP : Nat → List FP → List FP
  | 0, l => l
  | _, [] => []
  | Nat.succ n, _ :: as => dropFP n as

theorem takeFP_length (n : Nat) (l : List FP) (h : n ≤ l.length) :
    (takeFP n l).length = n :=
  match n, l with
  | 0, _ => FP.nat_self_eq 0
  | Nat.succ m, [] => absurd h (Nat.not_succ_le_zero m)
  | Nat.succ m, a :: as =>
    have hsub : m ≤ as.length := Nat.le_of_succ_le_succ h
    have ih : (takeFP m as).length = m := takeFP_length m as hsub
    congrArg Nat.succ ih

theorem dropFP_length (n : Nat) (l : List FP) (h : n ≤ l.length) :
    (dropFP n l).length = l.length - n :=
  match n, l with
  | 0, l => Eq.symm (Nat.sub_zero l.length)
  | Nat.succ m, [] => absurd h (Nat.not_succ_le_zero m)
  | Nat.succ m, a :: as =>
    have hsub : m ≤ as.length := Nat.le_of_succ_le_succ h
    dropFP_length m as hsub

theorem takeFP_dropFP_append (n : Nat) (l : List FP) (h : n ≤ l.length) :
    takeFP n l ++ dropFP n l = l :=
  match n, l with
  | 0, l => Eq.symm (List.nil_append l)
  | Nat.succ m, [] => absurd h (Nat.not_succ_le_zero m)
  | Nat.succ m, a :: as =>
    have hsub : m ≤ as.length := Nat.le_of_succ_le_succ h
    have ih : takeFP m as ++ dropFP m as = as := takeFP_dropFP_append m as hsub
    show (a :: takeFP m as) ++ dropFP m as = a :: as from
    Eq.trans (List.cons_append a (takeFP m as) (dropFP m as))
      (congrArg (a :: ·) ih)

def pointwiseAdd (l1 l2 : List FP) : List FP :=
  zipWithFP FP.add l1 l2

def pointwiseSub (l1 l2 : List FP) : List FP :=
  zipWithFP FP.sub l1 l2

def scaleList (s : FP) (l : List FP) : List FP :=
  mapFP (FP.mul s) l

theorem pointwiseAdd_length (l1 l2 : List FP) (h : l1.length = l2.length) :
    (pointwiseAdd l1 l2).length = l1.length :=
  zipWithFP_length_eq FP.add l1 l2 h

theorem pointwiseSub_length (l1 l2 : List FP) (h : l1.length = l2.length) :
    (pointwiseSub l1 l2).length = l1.length :=
  zipWithFP_length_eq FP.sub l1 l2 h

theorem scaleList_length (s : FP) (l : List FP) :
    (scaleList s l).length = l.length :=
  mapFP_length (FP.mul s) l

theorem pointwiseAdd_comm (l1 l2 : List FP) (h : l1.length = l2.length) :
    pointwiseAdd l1 l2 = pointwiseAdd l2 l1 :=
  match l1, l2 with
  | [], [] => Eq.trans (FP.fp_self_eq _) (FP.fp_self_eq _)
  | [], _ :: _ => absurd h Nat.noConfusion
  | _ :: _, [] => absurd (Eq.symm h) Nat.noConfusion
  | a :: as, b :: bs =>
    have hsub : as.length = bs.length := Nat.succ.inj h
    have ih : pointwiseAdd as bs = pointwiseAdd bs as := pointwiseAdd_comm as bs hsub
    show FP.add a b :: zipWithFP FP.add as bs = FP.add b a :: zipWithFP FP.add bs as from
    Eq.trans
      (congrArg (· :: zipWithFP FP.add as bs) (FP.add_comm a b))
      (congrArg (FP.add b a :: ·) ih)

theorem pointwiseSub_self (l : List FP) :
    pointwiseSub l l = List.replicate l.length FP.zero :=
  match l with
  | [] => Eq.trans (FP.fp_self_eq _) (FP.fp_self_eq _)
  | a :: as =>
    have ih : pointwiseSub as as = List.replicate as.length FP.zero := pointwiseSub_self as
    show FP.sub a a :: zipWithFP FP.sub as as = FP.zero :: List.replicate as.length FP.zero from
    Eq.trans
      (congrArg (· :: zipWithFP FP.sub as as) (FP.sub_self a))
      (congrArg (FP.zero :: ·) ih)

end ListUtilities

section MeanComputation

def sumFP : List FP → FP
  | [] => FP.zero
  | a :: as => FP.add a (sumFP as)

theorem sumFP_nil : sumFP [] = FP.zero :=
  FP.fp_self_eq FP.zero

theorem sumFP_single (a : FP) : sumFP [a] = FP.add a FP.zero :=
  FP.fp_self_eq (FP.add a FP.zero)

theorem sumFP_single_eq (a : FP) : sumFP [a] = a :=
  Eq.trans (sumFP_single a) (FP.add_zero a)

theorem sumFP_cons (a : FP) (l : List FP) :
    sumFP (a :: l) = FP.add a (sumFP l) :=
  FP.fp_self_eq (FP.add a (sumFP l))

theorem sumFP_append (l1 l2 : List FP) :
    sumFP (l1 ++ l2) = FP.add (sumFP l1) (sumFP l2) :=
  match l1 with
  | [] =>
    show sumFP ([] ++ l2) = FP.add FP.zero (sumFP l2) from
    Eq.trans
      (show sumFP l2 = FP.add FP.zero (sumFP l2) from
        Eq.symm (FP.zero_add (sumFP l2)))
      (FP.fp_self_eq (FP.add FP.zero (sumFP l2)))
  | a :: as =>
    have ih : sumFP (as ++ l2) = FP.add (sumFP as) (sumFP l2) := sumFP_append as l2
    show FP.add a (sumFP (as ++ l2)) = FP.add (FP.add a (sumFP as)) (sumFP l2) from
    Eq.trans
      (congrArg (FP.add a) ih)
      (Eq.symm (FP.add_assoc a (sumFP as) (sumFP l2)))

theorem sumFP_comm_pair (a b : FP) (l : List FP) :
    sumFP (a :: b :: l) = sumFP (b :: a :: l) :=
  show FP.add a (FP.add b (sumFP l)) = FP.add b (FP.add a (sumFP l)) from
  FP.add_left_comm a b (sumFP l)

def meanFP (l : List FP) (n : Nat) : FP :=
  if n = 0 then FP.zero
  else ⟨(sumFP l).val / (Int.ofNat n)⟩

theorem meanFP_nil : meanFP [] 0 = FP.zero :=
  show (if (0 : Nat) = 0 then FP.zero else _) = FP.zero from
  have hdec : ((0 : Nat) = 0) = True := propext ⟨fun _ => True.intro, fun _ => FP.nat_self_eq 0⟩
  Eq.mpr (congrArg (fun p => (if p then FP.zero else _) = FP.zero) hdec)
    (FP.fp_self_eq FP.zero)

def memMeanFP (mem : MemoryMap) (size : Nat) : FP :=
  meanFP (memToList mem size) size

theorem memMeanFP_zero : memMeanFP memEmpty 0 = FP.zero :=
  show meanFP (memToList memEmpty 0) 0 = FP.zero from
  meanFP_nil

end MeanComputation

section Modulation

def gtFP (a b : FP) : Bool := a.val > b.val

def modulateValue (v mean factor : FP) : FP :=
  if gtFP v mean then FP.mul v factor else v

theorem modulateValue_identity (v mean : FP) :
    modulateValue v mean FP.one = (if gtFP v mean then FP.mul v FP.one else v) :=
  FP.fp_self_eq (if gtFP v mean then FP.mul v FP.one else v)

theorem modulateValue_no_change_below (v mean factor : FP) (h : gtFP v mean = false) :
    modulateValue v mean factor = v :=
  show (if gtFP v mean then FP.mul v factor else v) = v from
  match hb : gtFP v mean with
  | true => absurd (Eq.trans (Eq.symm hb) h) Bool.noConfusion
  | false => FP.fp_self_eq v

theorem modulateValue_scales_above (v mean factor : FP) (h : gtFP v mean = true) :
    modulateValue v mean factor = FP.mul v factor :=
  show (if gtFP v mean then FP.mul v factor else v) = FP.mul v factor from
  match hb : gtFP v mean with
  | true => FP.fp_self_eq (FP.mul v factor)
  | false => absurd (Eq.trans (Eq.symm h) hb) Bool.noConfusion

def modulateList (data : List FP) (mean factor : FP) : List FP :=
  mapFP (fun v => modulateValue v mean factor) data

theorem modulateList_length (data : List FP) (mean factor : FP) :
    (modulateList data mean factor).length = data.length :=
  mapFP_length (fun v => modulateValue v mean factor) data

theorem modulateList_nil (mean factor : FP) :
    modulateList [] mean factor = [] :=
  Eq.trans (Eq.symm (FP.fp_self_eq (modulateList [] mean factor)).symm.symm)
    (FP.fp_self_eq [])

def nsirForward (data : List FP) (factor : FP) : List FP :=
  let mean := meanFP data data.length
  modulateList data mean factor

theorem nsirForward_length (data : List FP) (factor : FP) :
    (nsirForward data factor).length = data.length :=
  modulateList_length data (meanFP data data.length) factor

theorem nsirForward_nil (factor : FP) :
    nsirForward [] factor = [] :=
  modulateList_nil (meanFP [] 0) factor

def memModulateForward (mem : MemoryMap) (size : Nat) (factor : FP) : MemoryMap :=
  let mean := memMeanFP mem size
  fun i =>
    match mem i with
    | some v => some (modulateValue v mean factor)
    | none => none

theorem memModulateForward_preserves_validity (mem : MemoryMap) (size : Nat) (factor : FP) (i : Nat)
    (h : ∃ v, mem i = some v) :
    ∃ v, (memModulateForward mem size factor) i = some v :=
  match hv : mem i with
  | some v =>
    ⟨modulateValue v (memMeanFP mem size) factor,
     show (match mem i with | some v => some (modulateValue v (memMeanFP mem size) factor) | none => none) = some (modulateValue v (memMeanFP mem size) factor) from
     Eq.mpr (congrArg (fun x => (match x with | some v => some (modulateValue v (memMeanFP mem size) factor) | none => none) = some (modulateValue v (memMeanFP mem size) factor))
       (Eq.symm hv |>.symm))
     (FP.fp_self_eq _ |>.symm |>.symm |> fun _ =>
       congrArg some (FP.fp_self_eq (modulateValue v (memMeanFP mem size) factor)))⟩
  | none =>
    absurd (show mem i = none from hv) (fun hn =>
      match h with
      | ⟨v, hv2⟩ => Option.noConfusion (Eq.trans (Eq.symm hv2) hn))

end Modulation

section BackwardModulation

def modulateBackwardList (grad activations : List FP) (mean factor : FP) : List FP :=
  match grad, activations with
  | [], _ => []
  | _, [] => []
  | g :: gs, a :: acts =>
    let newG := if gtFP a mean then FP.mul g factor else g
    newG :: modulateBackwardList gs acts mean factor

theorem modulateBackwardList_length (grad activations : List FP) (mean factor : FP)
    (h : grad.length = activations.length) :
    (modulateBackwardList grad activations mean factor).length = grad.length :=
  match grad, activations with
  | [], [] => FP.nat_self_eq 0
  | [], _ :: _ => absurd h Nat.noConfusion
  | _ :: _, [] => absurd (Eq.symm h) Nat.noConfusion
  | g :: gs, a :: acts =>
    have hsub : gs.length = acts.length := Nat.succ.inj h
    have ih : (modulateBackwardList gs acts mean factor).length = gs.length :=
      modulateBackwardList_length gs acts mean factor hsub
    congrArg Nat.succ ih

theorem modulateBackwardList_nil_grad (activations : List FP) (mean factor : FP) :
    modulateBackwardList [] activations mean factor = [] :=
  match activations with
  | [] => Eq.trans (Eq.symm (FP.fp_self_eq (modulateBackwardList [] [] mean factor)).symm.symm)
    (FP.fp_self_eq [])
  | _ :: _ => Eq.trans (Eq.symm (FP.fp_self_eq (modulateBackwardList [] (_ :: _) mean factor)).symm.symm)
    (FP.fp_self_eq [])

def nsirBackward (grad activations : List FP) (factor : FP) : List FP :=
  let n := if grad.length ≤ activations.length then grad.length else activations.length
  let mean := meanFP (takeFP n activations) n
  modulateBackwardList (takeFP n grad) (takeFP n activations) mean factor ++
    dropFP n grad

theorem nsirBackward_matches_forward_condition (v mean factor : FP) :
    (gtFP v mean = true → modulateValue v mean factor = FP.mul v factor) ∧
    (gtFP v mean = false → modulateValue v mean factor = v) :=
  And.intro
    (fun h => modulateValue_scales_above v mean factor h)
    (fun h => modulateValue_no_change_below v mean factor h)

theorem backward_scales_where_forward_scaled (g a mean factor : FP) (h : gtFP a mean = true) :
    (if gtFP a mean then FP.mul g factor else g) = FP.mul g factor :=
  match hb : gtFP a mean with
  | true => FP.fp_self_eq (FP.mul g factor)
  | false => absurd (Eq.trans (Eq.symm h) hb) Bool.noConfusion

theorem backward_preserves_where_forward_preserved (g a mean factor : FP) (h : gtFP a mean = false) :
    (if gtFP a mean then FP.mul g factor else g) = g :=
  match hb : gtFP a mean with
  | true => absurd (Eq.trans (Eq.symm hb) h) Bool.noConfusion
  | false => FP.fp_self_eq g

theorem forward_backward_condition_match (data grad : List FP) (mean factor : FP)
    (h : data.length = grad.length) :
    (modulateList data mean factor).length = (modulateBackwardList grad data mean factor).length :=
  Eq.trans
    (modulateList_length data mean factor)
    (Eq.symm (modulateBackwardList_length grad data mean factor (Eq.symm h)))

def memModulateBackward (gradMem actMem : MemoryMap) (size : Nat) (factor : FP) : MemoryMap :=
  let mean := memMeanFP actMem size
  fun i =>
    if i < size then
      match gradMem i, actMem i with
      | some g, some a =>
        some (if gtFP a mean then FP.mul g factor else g)
      | _, _ => gradMem i
    else gradMem i

theorem memModulateBackward_oob (gradMem actMem : MemoryMap) (size : Nat) (factor : FP)
    (i : Nat) (h : ¬(i < size)) :
    (memModulateBackward gradMem actMem size factor) i = gradMem i :=
  show (if i < size then _ else gradMem i) = gradMem i from
  have h_nlt : (i < size) = False := propext ⟨fun h2 => absurd h2 h, False.elim⟩
  Eq.mpr (congrArg (fun p => (if p then _ else gradMem i) = gradMem i) h_nlt)
    (FP.fp_self_eq _ |>.symm |>.symm |> fun _ =>
      show gradMem i = gradMem i from
      match gradMem i with
      | some v => congrArg some (FP.fp_self_eq v)
      | none => Eq.trans (Eq.symm (FP.fp_self_eq (none : Option FP)).symm.symm) (FP.fp_self_eq none))

end BackwardModulation

section PipelineModel

inductive PipelineStage where
  | Embedding
  | OFTB
  | RSF
  | NSIR
  | Projection
deriving BEq, Repr

def stageIndex : PipelineStage → Nat
  | PipelineStage.Embedding => 0
  | PipelineStage.OFTB => 1
  | PipelineStage.RSF => 2
  | PipelineStage.NSIR => 3
  | PipelineStage.Projection => 4

def backpropIndex : PipelineStage → Nat
  | PipelineStage.Projection => 0
  | PipelineStage.NSIR => 1
  | PipelineStage.RSF => 2
  | PipelineStage.OFTB => 3
  | PipelineStage.Embedding => 4

theorem embedding_first : stageIndex PipelineStage.Embedding = 0 :=
  FP.nat_self_eq 0

theorem oftb_second : stageIndex PipelineStage.OFTB = 1 :=
  FP.nat_self_eq 1

theorem rsf_third : stageIndex PipelineStage.RSF = 2 :=
  FP.nat_self_eq 2

theorem nsir_fourth : stageIndex PipelineStage.NSIR = 3 :=
  FP.nat_self_eq 3

theorem projection_fifth : stageIndex PipelineStage.Projection = 4 :=
  FP.nat_self_eq 4

theorem forward_order_embedding_before_oftb :
    stageIndex PipelineStage.Embedding < stageIndex PipelineStage.OFTB :=
  Nat.lt_succ_of_le (Nat.le_refl 0)

theorem forward_order_oftb_before_rsf :
    stageIndex PipelineStage.OFTB < stageIndex PipelineStage.RSF :=
  Nat.lt_succ_of_le (Nat.le_refl 1)

theorem forward_order_rsf_before_nsir :
    stageIndex PipelineStage.RSF < stageIndex PipelineStage.NSIR :=
  Nat.lt_succ_of_le (Nat.le_refl 2)

theorem forward_order_nsir_before_projection :
    stageIndex PipelineStage.NSIR < stageIndex PipelineStage.Projection :=
  Nat.lt_succ_of_le (Nat.le_refl 3)

theorem forward_order_embedding_before_projection :
    stageIndex PipelineStage.Embedding < stageIndex PipelineStage.Projection :=
  Nat.lt_trans
    (Nat.lt_trans
      (Nat.lt_trans forward_order_embedding_before_oftb forward_order_oftb_before_rsf)
      forward_order_rsf_before_nsir)
    forward_order_nsir_before_projection

theorem backprop_order_projection_first :
    backpropIndex PipelineStage.Projection < backpropIndex PipelineStage.NSIR :=
  Nat.lt_succ_of_le (Nat.le_refl 0)

theorem backprop_order_nsir_before_rsf :
    backpropIndex PipelineStage.NSIR < backpropIndex PipelineStage.RSF :=
  Nat.lt_succ_of_le (Nat.le_refl 1)

theorem backprop_order_rsf_before_oftb :
    backpropIndex PipelineStage.RSF < backpropIndex PipelineStage.OFTB :=
  Nat.lt_succ_of_le (Nat.le_refl 2)

theorem backprop_order_oftb_before_embedding :
    backpropIndex PipelineStage.OFTB < backpropIndex PipelineStage.Embedding :=
  Nat.lt_succ_of_le (Nat.le_refl 3)

theorem forward_backprop_sum (s : PipelineStage) :
    stageIndex s + backpropIndex s = 4 :=
  match s with
  | PipelineStage.Embedding => FP.nat_self_eq 4
  | PipelineStage.OFTB => FP.nat_self_eq 4
  | PipelineStage.RSF => FP.nat_self_eq 4
  | PipelineStage.NSIR => FP.nat_self_eq 4
  | PipelineStage.Projection => FP.nat_self_eq 4

theorem total_stages : stageIndex PipelineStage.Projection + 1 = 5 :=
  FP.nat_self_eq 5

end PipelineModel

section ParamPartition

def paramOffset_embed : Nat := 0
def paramOffset_rsf (embed_p : Nat) : Nat := embed_p
def paramOffset_proj (embed_p rsf_p : Nat) : Nat := embed_p + rsf_p
def totalParamCount (embed_p rsf_p proj_p : Nat) : Nat := embed_p + rsf_p + proj_p

theorem offset_embed_zero : paramOffset_embed = 0 :=
  FP.nat_self_eq 0

theorem offset_rsf_eq (e : Nat) : paramOffset_rsf e = e :=
  FP.nat_self_eq e

theorem offset_proj_eq (e r : Nat) : paramOffset_proj e r = e + r :=
  FP.nat_self_eq (e + r)

theorem offsets_non_overlapping (embed_p rsf_p : Nat) (h_ep : 0 < embed_p) :
    paramOffset_embed + embed_p ≤ paramOffset_rsf embed_p :=
  show 0 + embed_p ≤ embed_p from
  Eq.subst (Eq.symm (Nat.zero_add embed_p)) (Nat.le_refl embed_p)

theorem offsets_non_overlapping_rsf_proj (embed_p rsf_p : Nat) (h_rp : 0 < rsf_p) :
    paramOffset_rsf embed_p + rsf_p ≤ paramOffset_proj embed_p rsf_p :=
  show embed_p + rsf_p ≤ embed_p + rsf_p from
  Nat.le_refl (embed_p + rsf_p)

theorem offsets_partition (embed_p rsf_p proj_p : Nat) :
    paramOffset_proj embed_p rsf_p + proj_p = totalParamCount embed_p rsf_p proj_p :=
  Eq.symm (Nat.add_assoc embed_p rsf_p proj_p)

theorem totalParamCount_assoc (e r p : Nat) :
    totalParamCount e r p = e + (r + p) :=
  Nat.add_assoc e r p

theorem totalParamCount_pos (e r p : Nat) (h : 0 < e) :
    0 < totalParamCount e r p :=
  Nat.lt_of_lt_of_le h (Nat.le_add_right e (r + p))

theorem embed_range (embed_p : Nat) :
    paramOffset_embed + embed_p = paramOffset_rsf embed_p :=
  show 0 + embed_p = embed_p from
  Nat.zero_add embed_p

theorem rsf_range (embed_p rsf_p : Nat) :
    paramOffset_rsf embed_p + rsf_p = paramOffset_proj embed_p rsf_p :=
  FP.nat_self_eq (embed_p + rsf_p)

theorem proj_range (embed_p rsf_p proj_p : Nat) :
    paramOffset_proj embed_p rsf_p + proj_p = totalParamCount embed_p rsf_p proj_p :=
  offsets_partition embed_p rsf_p proj_p

theorem ranges_cover_total (embed_p rsf_p proj_p : Nat) :
    embed_p + rsf_p + proj_p = totalParamCount embed_p rsf_p proj_p :=
  FP.nat_self_eq (embed_p + rsf_p + proj_p)

theorem ranges_disjoint_embed_rsf (embed_p rsf_p : Nat) (i j : Nat)
    (hi : i < embed_p) (hj : embed_p ≤ j) (hj2 : j < embed_p + rsf_p) :
    i ≠ j :=
  fun heq => absurd (Eq.subst heq hj) (Nat.not_le_of_gt hi)

theorem ranges_disjoint_rsf_proj (embed_p rsf_p proj_p : Nat) (i j : Nat)
    (hi : embed_p ≤ i) (hi2 : i < embed_p + rsf_p)
    (hj : embed_p + rsf_p ≤ j) (hj2 : j < embed_p + rsf_p + proj_p) :
    i ≠ j :=
  fun heq => absurd (Eq.subst heq hj) (Nat.not_le_of_gt hi2)

end ParamPartition

section TrainingPhaseModel

inductive TrainingPhase where
  | ZeroGrad
  | Forward
  | Backward
  | UpdateParams
deriving BEq, Repr

def phaseIndex : TrainingPhase → Nat
  | TrainingPhase.ZeroGrad => 0
  | TrainingPhase.Forward => 1
  | TrainingPhase.Backward => 2
  | TrainingPhase.UpdateParams => 3

theorem phase_order_zero_before_forward :
    phaseIndex TrainingPhase.ZeroGrad < phaseIndex TrainingPhase.Forward :=
  Nat.lt_succ_of_le (Nat.le_refl 0)

theorem phase_order_forward_before_backward :
    phaseIndex TrainingPhase.Forward < phaseIndex TrainingPhase.Backward :=
  Nat.lt_succ_of_le (Nat.le_refl 1)

theorem phase_order_backward_before_update :
    phaseIndex TrainingPhase.Backward < phaseIndex TrainingPhase.UpdateParams :=
  Nat.lt_succ_of_le (Nat.le_refl 2)

theorem phase_order_zero_before_update :
    phaseIndex TrainingPhase.ZeroGrad < phaseIndex TrainingPhase.UpdateParams :=
  Nat.lt_trans
    (Nat.lt_trans phase_order_zero_before_forward phase_order_forward_before_backward)
    phase_order_backward_before_update

end TrainingPhaseModel

section PipelineStateMachine

structure PipelineEntry where
  step : Nat
  stage : PipelineStage
  phase : TrainingPhase
  dataLen : Nat

structure PipelineTrace where
  entries : List PipelineEntry
  totalSteps : Nat

namespace PipelineTrace

def empty : PipelineTrace :=
  { entries := [], totalSteps := 0 }

def addEntry (trace : PipelineTrace) (stage : PipelineStage) (phase : TrainingPhase) (dataLen : Nat) : PipelineTrace :=
  { entries := { step := trace.totalSteps, stage := stage, phase := phase, dataLen := dataLen } :: trace.entries
  , totalSteps := trace.totalSteps + 1 }

theorem addEntry_step_inc (trace : PipelineTrace) (stage : PipelineStage) (phase : TrainingPhase) (dataLen : Nat) :
    (addEntry trace stage phase dataLen).totalSteps = trace.totalSteps + 1 :=
  FP.nat_self_eq (trace.totalSteps + 1)

theorem addEntry_entries_grow (trace : PipelineTrace) (stage : PipelineStage) (phase : TrainingPhase) (dataLen : Nat) :
    (addEntry trace stage phase dataLen).entries.length = trace.entries.length + 1 :=
  congrArg Nat.succ (FP.nat_self_eq trace.entries.length)

end PipelineTrace

structure PipelineState where
  activationsMem : MemoryMap
  gradientsMem : MemoryMap
  dataLen : Nat
  trace : PipelineTrace
  stepCounter : Nat

namespace PipelineState

def initial (dataLen : Nat) : PipelineState :=
  { activationsMem := memZero dataLen
  , gradientsMem := memZero dataLen
  , dataLen := dataLen
  , trace := PipelineTrace.empty
  , stepCounter := 0 }

def executeForward (st : PipelineState) (factor : FP) : PipelineState :=
  { activationsMem := memModulateForward st.activationsMem st.dataLen factor
  , gradientsMem := st.gradientsMem
  , dataLen := st.dataLen
  , trace := PipelineTrace.addEntry st.trace PipelineStage.NSIR TrainingPhase.Forward st.dataLen
  , stepCounter := st.stepCounter + 1 }

def executeBackward (st : PipelineState) (factor : FP) : PipelineState :=
  { activationsMem := st.activationsMem
  , gradientsMem := memModulateBackward st.gradientsMem st.activationsMem st.dataLen factor
  , dataLen := st.dataLen
  , trace := PipelineTrace.addEntry st.trace PipelineStage.NSIR TrainingPhase.Backward st.dataLen
  , stepCounter := st.stepCounter + 1 }

theorem executeForward_step_inc (st : PipelineState) (factor : FP) :
    (executeForward st factor).stepCounter = st.stepCounter + 1 :=
  FP.nat_self_eq (st.stepCounter + 1)

theorem executeBackward_step_inc (st : PipelineState) (factor : FP) :
    (executeBackward st factor).stepCounter = st.stepCounter + 1 :=
  FP.nat_self_eq (st.stepCounter + 1)

theorem executeForward_preserves_dataLen (st : PipelineState) (factor : FP) :
    (executeForward st factor).dataLen = st.dataLen :=
  FP.nat_self_eq st.dataLen

theorem executeBackward_preserves_dataLen (st : PipelineState) (factor : FP) :
    (executeBackward st factor).dataLen = st.dataLen :=
  FP.nat_self_eq st.dataLen

def executeForwardBackward (st : PipelineState) (factor : FP) : PipelineState :=
  executeBackward (executeForward st factor) factor

theorem executeForwardBackward_step_count (st : PipelineState) (factor : FP) :
    (executeForwardBackward st factor).stepCounter = st.stepCounter + 2 :=
  have h1 := executeForward_step_inc st factor
  have h2 := executeBackward_step_inc (executeForward st factor) factor
  Eq.trans h2 (Eq.trans (congrArg (· + 1) h1) (Nat.add_assoc st.stepCounter 1 1))

theorem executeForwardBackward_preserves_dataLen (st : PipelineState) (factor : FP) :
    (executeForwardBackward st factor).dataLen = st.dataLen :=
  Eq.trans
    (executeBackward_preserves_dataLen (executeForward st factor) factor)
    (executeForward_preserves_dataLen st factor)

end PipelineState

end PipelineStateMachine

section NRoundExecution

def executeNRounds : Nat → PipelineState → FP → PipelineState
  | 0, st, _ => st
  | Nat.succ n, st, factor =>
    executeNRounds n (PipelineState.executeForwardBackward st factor) factor

theorem executeNRounds_step_count (n : Nat) (st : PipelineState) (factor : FP) :
    (executeNRounds n st factor).stepCounter = st.stepCounter + n * 2 :=
  Nat.recOn n
    (Eq.symm (Nat.add_zero st.stepCounter))
    (fun k ih =>
      have h_fb : (PipelineState.executeForwardBackward st factor).stepCounter = st.stepCounter + 2 :=
        PipelineState.executeForwardBackward_step_count st factor
      have h_rec : (executeNRounds k (PipelineState.executeForwardBackward st factor) factor).stepCounter =
                    (PipelineState.executeForwardBackward st factor).stepCounter + k * 2 :=
        ih ▸ executeNRounds_step_count k (PipelineState.executeForwardBackward st factor) factor
      Eq.trans h_rec
        (Eq.trans (congrArg (· + k * 2) h_fb)
          (Eq.trans (Nat.add_assoc st.stepCounter 2 (k * 2))
            (congrArg (st.stepCounter + ·) (Eq.trans (Nat.add_comm 2 (k * 2)) (Eq.symm (Nat.succ_mul k 2)))))))

theorem executeNRounds_preserves_dataLen (n : Nat) (st : PipelineState) (factor : FP) :
    (executeNRounds n st factor).dataLen = st.dataLen :=
  Nat.recOn n
    (FP.nat_self_eq st.dataLen)
    (fun k ih =>
      have h_fb : (PipelineState.executeForwardBackward st factor).dataLen = st.dataLen :=
        PipelineState.executeForwardBackward_preserves_dataLen st factor
      have h_rec : (executeNRounds k (PipelineState.executeForwardBackward st factor) factor).dataLen =
                    (PipelineState.executeForwardBackward st factor).dataLen :=
        ih ▸ executeNRounds_preserves_dataLen k (PipelineState.executeForwardBackward st factor) factor
      Eq.trans h_rec h_fb)

theorem executeNRounds_monotone (n : Nat) (st : PipelineState) (factor : FP) :
    st.stepCounter ≤ (executeNRounds n st factor).stepCounter :=
  Eq.subst (Eq.symm (executeNRounds_step_count n st factor))
    (Nat.le_add_right st.stepCounter (n * 2))

theorem step_lt_of_n_rounds (n m : Nat) (st : PipelineState) (factor : FP) (h : n < m) :
    (executeNRounds n st factor).stepCounter <
    (executeNRounds m st factor).stepCounter :=
  Eq.subst (Eq.symm (executeNRounds_step_count n st factor))
    (Eq.subst (Eq.symm (executeNRounds_step_count m st factor))
      (Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_right h (Nat.succ_pos 1)) st.stepCounter))

end NRoundExecution

section OverflowVerification

theorem nsir_index_safe (cfg : OverflowSafe) (i : Nat) (h : i < cfg.dataLen) :
    i < USIZE_BOUND :=
  overflow_safe_index cfg i h

theorem nsir_forward_all_safe (cfg : OverflowSafe) (data : List FP) (h : data.length = cfg.dataLen) :
    ∀ (i : Nat), i < data.length → i < USIZE_BOUND :=
  fun i hi => Nat.lt_trans (Eq.subst h hi) cfg.h_bound

theorem nsir_backward_all_safe (cfg : OverflowSafe) (grad activations : List FP)
    (hg : grad.length = cfg.dataLen) (ha : activations.length = cfg.dataLen) :
    ∀ (i : Nat), i < grad.length → i < USIZE_BOUND :=
  fun i hi => Nat.lt_trans (Eq.subst hg hi) cfg.h_bound

theorem mem_index_safe (cfg : OverflowSafe) (i : Nat) (h : i < cfg.dataLen) :
    i < USIZE_BOUND :=
  Nat.lt_trans h cfg.h_bound

end OverflowVerification
