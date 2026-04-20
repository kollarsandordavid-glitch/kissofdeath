structure Complex where
  re : Float
  im : Float
deriving Repr, Inhabited, BEq

namespace Complex

noncomputable def add (a b : Complex) : Complex := ⟨a.re + b.re, a.im + b.im⟩

noncomputable def sub (a b : Complex) : Complex := ⟨a.re - b.re, a.im - b.im⟩

noncomputable def mul (a b : Complex) : Complex :=
  ⟨a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re⟩

noncomputable def magnitudeSquared (c : Complex) : Float :=
  c.re * c.re + c.im * c.im

noncomputable def zero : Complex := ⟨0.0, 0.0⟩
noncomputable def one : Complex := ⟨1.0, 0.0⟩
noncomputable def i_unit : Complex := ⟨0.0, 1.0⟩
noncomputable def neg_i_unit : Complex := ⟨0.0, -1.0⟩

end Complex

theorem Complex.ext (a b : Complex) (hre : a.re = b.re) (him : a.im = b.im) : a = b :=
  match a, b with
  | ⟨_, _⟩, ⟨_, _⟩ => Eq.subst hre (Eq.subst him (Eq.refl _))

theorem Complex.add_re (a b : Complex) : (Complex.add a b).re = a.re + b.re := Eq.refl _
theorem Complex.add_im (a b : Complex) : (Complex.add a b).im = a.im + b.im := Eq.refl _
theorem Complex.sub_re (a b : Complex) : (Complex.sub a b).re = a.re - b.re := Eq.refl _
theorem Complex.sub_im (a b : Complex) : (Complex.sub a b).im = a.im - b.im := Eq.refl _
theorem Complex.mul_re (a b : Complex) : (Complex.mul a b).re = a.re * b.re - a.im * b.im := Eq.refl _
theorem Complex.mul_im (a b : Complex) : (Complex.mul a b).im = a.re * b.im + a.im * b.re := Eq.refl _

inductive EdgeQuality where
  | superposition : EdgeQuality
  | entangled : EdgeQuality
  | coherent : EdgeQuality
  | collapsed : EdgeQuality
  | fractal : EdgeQuality
deriving Repr, Inhabited, BEq, DecidableEq

namespace EdgeQuality

def toNat : EdgeQuality → Nat
  | .superposition => 0
  | .entangled => 1
  | .coherent => 2
  | .collapsed => 3
  | .fractal => 4

def toString : EdgeQuality → String
  | .superposition => "superposition"
  | .entangled => "entangled"
  | .coherent => "coherent"
  | .collapsed => "collapsed"
  | .fractal => "fractal"

def fromString (s : String) : Option EdgeQuality :=
  if s == "superposition" then some .superposition
  else if s == "entangled" then some .entangled
  else if s == "coherent" then some .coherent
  else if s == "collapsed" then some .collapsed
  else if s == "fractal" then some .fractal
  else none

def fromNat : Nat → Option EdgeQuality
  | 0 => some .superposition
  | 1 => some .entangled
  | 2 => some .coherent
  | 3 => some .collapsed
  | 4 => some .fractal
  | _ => none

end EdgeQuality

theorem EdgeQuality.superposition_ne_entangled : EdgeQuality.superposition ≠ EdgeQuality.entangled :=
  fun h => EdgeQuality.noConfusion h
theorem EdgeQuality.superposition_ne_coherent : EdgeQuality.superposition ≠ EdgeQuality.coherent :=
  fun h => EdgeQuality.noConfusion h
theorem EdgeQuality.superposition_ne_collapsed : EdgeQuality.superposition ≠ EdgeQuality.collapsed :=
  fun h => EdgeQuality.noConfusion h
theorem EdgeQuality.superposition_ne_fractal : EdgeQuality.superposition ≠ EdgeQuality.fractal :=
  fun h => EdgeQuality.noConfusion h
theorem EdgeQuality.entangled_ne_coherent : EdgeQuality.entangled ≠ EdgeQuality.coherent :=
  fun h => EdgeQuality.noConfusion h
theorem EdgeQuality.entangled_ne_collapsed : EdgeQuality.entangled ≠ EdgeQuality.collapsed :=
  fun h => EdgeQuality.noConfusion h
theorem EdgeQuality.entangled_ne_fractal : EdgeQuality.entangled ≠ EdgeQuality.fractal :=
  fun h => EdgeQuality.noConfusion h
theorem EdgeQuality.coherent_ne_collapsed : EdgeQuality.coherent ≠ EdgeQuality.collapsed :=
  fun h => EdgeQuality.noConfusion h
theorem EdgeQuality.coherent_ne_fractal : EdgeQuality.coherent ≠ EdgeQuality.fractal :=
  fun h => EdgeQuality.noConfusion h
theorem EdgeQuality.collapsed_ne_fractal : EdgeQuality.collapsed ≠ EdgeQuality.fractal :=
  fun h => EdgeQuality.noConfusion h

theorem EdgeQuality.fromNat_toNat (e : EdgeQuality) : EdgeQuality.fromNat (EdgeQuality.toNat e) = some e :=
  match e with
  | .superposition => Eq.refl _
  | .entangled => Eq.refl _
  | .coherent => Eq.refl _
  | .collapsed => Eq.refl _
  | .fractal => Eq.refl _

theorem EdgeQuality.toNat_injective (a b : EdgeQuality) (h : EdgeQuality.toNat a = EdgeQuality.toNat b) : a = b :=
  match a, b with
  | .superposition, .superposition => Eq.refl _
  | .superposition, .entangled => absurd h (fun h2 => Nat.noConfusion h2)
  | .superposition, .coherent => absurd h (fun h2 => Nat.noConfusion h2)
  | .superposition, .collapsed => absurd h (fun h2 => Nat.noConfusion h2)
  | .superposition, .fractal => absurd h (fun h2 => Nat.noConfusion h2)
  | .entangled, .superposition => absurd h (fun h2 => Nat.noConfusion h2)
  | .entangled, .entangled => Eq.refl _
  | .entangled, .coherent => absurd h (fun h2 => Nat.noConfusion h2)
  | .entangled, .collapsed => absurd h (fun h2 => Nat.noConfusion h2)
  | .entangled, .fractal => absurd h (fun h2 => Nat.noConfusion h2)
  | .coherent, .superposition => absurd h (fun h2 => Nat.noConfusion h2)
  | .coherent, .entangled => absurd h (fun h2 => Nat.noConfusion h2)
  | .coherent, .coherent => Eq.refl _
  | .coherent, .collapsed => absurd h (fun h2 => Nat.noConfusion h2)
  | .coherent, .fractal => absurd h (fun h2 => Nat.noConfusion h2)
  | .collapsed, .superposition => absurd h (fun h2 => Nat.noConfusion h2)
  | .collapsed, .entangled => absurd h (fun h2 => Nat.noConfusion h2)
  | .collapsed, .coherent => absurd h (fun h2 => Nat.noConfusion h2)
  | .collapsed, .collapsed => Eq.refl _
  | .collapsed, .fractal => absurd h (fun h2 => Nat.noConfusion h2)
  | .fractal, .superposition => absurd h (fun h2 => Nat.noConfusion h2)
  | .fractal, .entangled => absurd h (fun h2 => Nat.noConfusion h2)
  | .fractal, .coherent => absurd h (fun h2 => Nat.noConfusion h2)
  | .fractal, .collapsed => absurd h (fun h2 => Nat.noConfusion h2)
  | .fractal, .fractal => Eq.refl _

theorem EdgeQuality.toNat_lt_five (e : EdgeQuality) : EdgeQuality.toNat e < 5 :=
  match e with
  | .superposition => Nat.lt.step (Nat.lt.step (Nat.lt.step (Nat.lt.step Nat.lt.base)))
  | .entangled => Nat.lt.step (Nat.lt.step (Nat.lt.step Nat.lt.base))
  | .coherent => Nat.lt.step (Nat.lt.step Nat.lt.base)
  | .collapsed => Nat.lt.step Nat.lt.base
  | .fractal => Nat.lt.base

theorem EdgeQuality.all_constructors (e : EdgeQuality) :
    e = .superposition ∨ e = .entangled ∨ e = .coherent ∨ e = .collapsed ∨ e = .fractal :=
  match e with
  | .superposition => Or.inl (Eq.refl _)
  | .entangled => Or.inr (Or.inl (Eq.refl _))
  | .coherent => Or.inr (Or.inr (Or.inl (Eq.refl _)))
  | .collapsed => Or.inr (Or.inr (Or.inr (Or.inl (Eq.refl _))))
  | .fractal => Or.inr (Or.inr (Or.inr (Or.inr (Eq.refl _))))

theorem EdgeQuality.toString_inj (a b : EdgeQuality) (h : EdgeQuality.toString a = EdgeQuality.toString b) : a = b :=
  match a, b with
  | .superposition, .superposition => Eq.refl _
  | .superposition, .entangled => nomatch h
  | .superposition, .coherent => nomatch h
  | .superposition, .collapsed => nomatch h
  | .superposition, .fractal => nomatch h
  | .entangled, .superposition => nomatch h
  | .entangled, .entangled => Eq.refl _
  | .entangled, .coherent => nomatch h
  | .entangled, .collapsed => nomatch h
  | .entangled, .fractal => nomatch h
  | .coherent, .superposition => nomatch h
  | .coherent, .entangled => nomatch h
  | .coherent, .coherent => Eq.refl _
  | .coherent, .collapsed => nomatch h
  | .coherent, .fractal => nomatch h
  | .collapsed, .superposition => nomatch h
  | .collapsed, .entangled => nomatch h
  | .collapsed, .coherent => nomatch h
  | .collapsed, .collapsed => Eq.refl _
  | .collapsed, .fractal => nomatch h
  | .fractal, .superposition => nomatch h
  | .fractal, .entangled => nomatch h
  | .fractal, .coherent => nomatch h
  | .fractal, .collapsed => nomatch h
  | .fractal, .fractal => Eq.refl _

def StringMap (ν : Type) := List (String × ν)

namespace StringMap

def empty : StringMap ν := []

def get (m : StringMap ν) (k : String) : Option ν :=
  match m with
  | [] => none
  | (k', v) :: rest => if k' == k then some v else get rest k

def remove (m : StringMap ν) (k : String) : StringMap ν :=
  match m with
  | [] => []
  | (k', v') :: rest => if k' == k then remove rest k else (k', v') :: remove rest k

def insert (m : StringMap ν) (k : String) (v : ν) : StringMap ν :=
  (k, v) :: remove m k

def contains (m : StringMap ν) (k : String) : Bool :=
  match m with
  | [] => false
  | (k', _) :: rest => if k' == k then true else contains rest k

def size (m : StringMap ν) : Nat := m.length

def keys (m : StringMap ν) : List String := m.map Prod.fst

def values (m : StringMap ν) : List ν := m.map Prod.snd

def toList (m : StringMap ν) : List (String × ν) := m

def foldlKV (f : β → String → ν → β) (init : β) (m : StringMap ν) : β :=
  m.foldl (fun acc (k, v) => f acc k v) init

end StringMap

theorem StringMap.get_empty (k : String) : StringMap.get (StringMap.empty : StringMap ν) k = none := Eq.refl _

theorem StringMap.contains_empty (k : String) : StringMap.contains (StringMap.empty : StringMap ν) k = false := Eq.refl _

theorem StringMap.size_empty : StringMap.size (StringMap.empty : StringMap ν) = 0 := Eq.refl _

theorem StringMap.keys_empty : StringMap.keys (StringMap.empty : StringMap ν) = [] := Eq.refl _

theorem StringMap.insert_size_pos (m : StringMap ν) (k : String) (v : ν) :
    0 < StringMap.size (StringMap.insert m k v) :=
  Nat.succ_pos _

theorem StringMap.get_insert_self (m : StringMap ν) (k : String) (v : ν) (hbeq : (k == k) = true) :
    StringMap.get (StringMap.insert m k v) k = some v :=
  show (if k == k then some v else StringMap.get (StringMap.remove m k) k) = some v from
    Eq.mpr (congrArg (fun b => (if b then some v else StringMap.get (StringMap.remove m k) k) = some v) hbeq)
      (Eq.refl (some v))

theorem StringMap.contains_insert_self (m : StringMap ν) (k : String) (v : ν) (hbeq : (k == k) = true) :
    StringMap.contains (StringMap.insert m k v) k = true :=
  show (if k == k then true else StringMap.contains (StringMap.remove m k) k) = true from
    Eq.mpr (congrArg (fun b => (if b then true else StringMap.contains (StringMap.remove m k) k) = true) hbeq)
      (Eq.refl true)

theorem StringMap.remove_empty (k : String) : StringMap.remove (StringMap.empty : StringMap ν) k = [] := Eq.refl _

theorem StringMap.get_cons_ne (k k' : String) (v : ν) (rest : StringMap ν) (hne : (k' == k) = false) :
    StringMap.get ((k', v) :: rest) k = StringMap.get rest k :=
  show (if k' == k then some v else StringMap.get rest k) = StringMap.get rest k from
    Eq.mpr (congrArg (fun b => (if b then some v else StringMap.get rest k) = StringMap.get rest k) hne)
      (Eq.refl (StringMap.get rest k))

theorem StringMap.get_insert_ne (m : StringMap ν) (k k' : String) (v : ν)
    (hne : (k == k') = false) :
    StringMap.get (StringMap.insert m k' v) k = StringMap.get (StringMap.remove m k') k :=
  show (if k' == k then some v else StringMap.get (StringMap.remove m k') k) = StringMap.get (StringMap.remove m k') k from
    have hne2 : (k' == k) = false :=
      match hkk : k' == k with
      | true =>
        have : k' = k := eq_of_beq hkk
        have : k == k' = true := show k == k' = true from
          Eq.mpr (congrArg (fun s => (s == k') = true) (Eq.symm this)) hkk
        absurd this (fun h2 => Bool.noConfusion (Eq.trans (Eq.symm hne) h2))
      | false => Eq.refl _
    Eq.mpr (congrArg (fun b => (if b then some v else StringMap.get (StringMap.remove m k') k) = StringMap.get (StringMap.remove m k') k) hne2)
      (Eq.refl (StringMap.get (StringMap.remove m k') k))

theorem StringMap.get_remove_eq (m : StringMap ν) (k : String) :
    StringMap.get (StringMap.remove m k) k = none :=
  match m with
  | [] => Eq.refl _
  | (k', v') :: rest =>
    match hkk : k' == k with
    | true =>
      show StringMap.get (if k' == k then StringMap.remove rest k else (k', v') :: StringMap.remove rest k) k = none from
        Eq.mpr (congrArg (fun b => StringMap.get (if b then StringMap.remove rest k else (k', v') :: StringMap.remove rest k) k = none) hkk)
          (StringMap.get_remove_eq rest k)
    | false =>
      show StringMap.get (if k' == k then StringMap.remove rest k else (k', v') :: StringMap.remove rest k) k = none from
        Eq.mpr (congrArg (fun b => StringMap.get (if b then StringMap.remove rest k else (k', v') :: StringMap.remove rest k) k = none) hkk)
          (show StringMap.get ((k', v') :: StringMap.remove rest k) k = none from
            show (if k' == k then some v' else StringMap.get (StringMap.remove rest k) k) = none from
              Eq.mpr (congrArg (fun b => (if b then some v' else StringMap.get (StringMap.remove rest k) k) = none) hkk)
                (StringMap.get_remove_eq rest k))

theorem StringMap.remove_absent (k : String) (m : StringMap ν)
    (h : StringMap.contains m k = false) :
    StringMap.remove m k = m :=
  match m with
  | [] => Eq.refl _
  | (k', v') :: rest =>
    have hne : (k' == k) = false :=
      match hkk : k' == k with
      | true =>
        absurd (show StringMap.contains ((k', v') :: rest) k = true from
          show (if k' == k then true else StringMap.contains rest k) = true from
            Eq.mpr (congrArg (fun b => (if b then true else StringMap.contains rest k) = true) hkk) (Eq.refl true))
          (fun h2 => Bool.noConfusion (Eq.trans (Eq.symm h) h2))
      | false => Eq.refl _
    have hrest : StringMap.contains rest k = false :=
      have hexp : (if k' == k then true else StringMap.contains rest k) = false := h
      show StringMap.contains rest k = false from
        Eq.mpr (congrArg (fun b => (if b then true else StringMap.contains rest k) = false) hne |>.symm) hexp
    show (if k' == k then StringMap.remove rest k else (k', v') :: StringMap.remove rest k) = (k', v') :: rest from
      Eq.mpr (congrArg (fun b => (if b then StringMap.remove rest k else (k', v') :: StringMap.remove rest k) = (k', v') :: rest) hne)
        (congrArg ((k', v') :: ·) (StringMap.remove_absent k rest hrest))

structure Qubit where
  a : Complex
  b : Complex
deriving Repr, Inhabited, BEq

namespace Qubit

noncomputable def normSquared (q : Qubit) : Float :=
  (q.a.re * q.a.re + q.a.im * q.a.im) + (q.b.re * q.b.re + q.b.im * q.b.im)

noncomputable def basis0 : Qubit := ⟨⟨1.0, 0.0⟩, ⟨0.0, 0.0⟩⟩
noncomputable def basis1 : Qubit := ⟨⟨0.0, 0.0⟩, ⟨1.0, 0.0⟩⟩

noncomputable def normalize (q : Qubit) : Qubit :=
  let ns := normSquared q
  if Float.isNaN ns || Float.isInf ns then basis0
  else if !(ns > 0.0) then basis0
  else
    let inv := 1.0 / Float.sqrt ns
    let s : Complex := ⟨inv, 0.0⟩
    ⟨Complex.mul q.a s, Complex.mul q.b s⟩

noncomputable def init (alpha beta : Complex) : Qubit :=
  normalize ⟨alpha, beta⟩

noncomputable def prob0 (q : Qubit) : Float :=
  let v := q.a.re * q.a.re + q.a.im * q.a.im
  if v < 0.0 then 0.0 else if v > 1.0 then 1.0 else v

noncomputable def prob1 (q : Qubit) : Float :=
  let v := q.b.re * q.b.re + q.b.im * q.b.im
  if v < 0.0 then 0.0 else if v > 1.0 then 1.0 else v

end Qubit

theorem Qubit.basis0_a_re : Qubit.basis0.a.re = (1.0 : Float) := Eq.refl _
theorem Qubit.basis0_a_im : Qubit.basis0.a.im = (0.0 : Float) := Eq.refl _
theorem Qubit.basis0_b_re : Qubit.basis0.b.re = (0.0 : Float) := Eq.refl _
theorem Qubit.basis0_b_im : Qubit.basis0.b.im = (0.0 : Float) := Eq.refl _
theorem Qubit.basis1_a_re : Qubit.basis1.a.re = (0.0 : Float) := Eq.refl _
theorem Qubit.basis1_a_im : Qubit.basis1.a.im = (0.0 : Float) := Eq.refl _
theorem Qubit.basis1_b_re : Qubit.basis1.b.re = (1.0 : Float) := Eq.refl _
theorem Qubit.basis1_b_im : Qubit.basis1.b.im = (0.0 : Float) := Eq.refl _

theorem Qubit.ext (q1 q2 : Qubit) (ha : q1.a = q2.a) (hb : q1.b = q2.b) : q1 = q2 :=
  match q1, q2 with
  | ⟨_, _⟩, ⟨_, _⟩ => Eq.subst ha (Eq.subst hb (Eq.refl _))

theorem Qubit.basis0_ne_basis1 : Qubit.basis0 ≠ Qubit.basis1 :=
  fun h =>
    have ha : Qubit.basis0.a = Qubit.basis1.a := congrArg Qubit.a h
    have hare : Qubit.basis0.a.re = Qubit.basis1.a.re := congrArg Complex.re ha
    have hstr : Float.toString (1.0 : Float) = Float.toString (0.0 : Float) :=
      congrArg Float.toString hare
    have : "1.000000" = "0.000000" := hstr
    nomatch this

structure Node where
  id : String
  data : String
  qubit : Qubit
  phase : Float
  metadata : StringMap String
deriving Repr, Inhabited

namespace Node

noncomputable def init (id : String) (data : String) (qubit : Qubit) (phase : Float) : Node :=
  ⟨id, data, qubit, phase, StringMap.empty⟩

def setMetadata (n : Node) (key value : String) : Node :=
  { n with metadata := StringMap.insert n.metadata key value }

def getMetadata (n : Node) (key : String) : Option String :=
  StringMap.get n.metadata key

def clone (n : Node) : Node := ⟨n.id, n.data, n.qubit, n.phase, n.metadata⟩

end Node

theorem Node.init_id (i d : String) (q : Qubit) (p : Float) : (Node.init i d q p).id = i := Eq.refl _
theorem Node.init_data (i d : String) (q : Qubit) (p : Float) : (Node.init i d q p).data = d := Eq.refl _
theorem Node.init_qubit (i d : String) (q : Qubit) (p : Float) : (Node.init i d q p).qubit = q := Eq.refl _
theorem Node.init_phase (i d : String) (q : Qubit) (p : Float) : (Node.init i d q p).phase = p := Eq.refl _
theorem Node.init_metadata_empty (i d : String) (q : Qubit) (p : Float) : (Node.init i d q p).metadata = StringMap.empty := Eq.refl _
theorem Node.clone_eq (n : Node) : Node.clone n = n := match n with | ⟨_, _, _, _, _⟩ => Eq.refl _

theorem Node.setMetadata_preserves_id (n : Node) (k v : String) : (n.setMetadata k v).id = n.id :=
  match n with | ⟨_, _, _, _, _⟩ => Eq.refl _
theorem Node.setMetadata_preserves_data (n : Node) (k v : String) : (n.setMetadata k v).data = n.data :=
  match n with | ⟨_, _, _, _, _⟩ => Eq.refl _
theorem Node.setMetadata_preserves_qubit (n : Node) (k v : String) : (n.setMetadata k v).qubit = n.qubit :=
  match n with | ⟨_, _, _, _, _⟩ => Eq.refl _
theorem Node.setMetadata_preserves_phase (n : Node) (k v : String) : (n.setMetadata k v).phase = n.phase :=
  match n with | ⟨_, _, _, _, _⟩ => Eq.refl _

theorem Node.ext (a b : Node) (h1 : a.id = b.id) (h2 : a.data = b.data) (h3 : a.qubit = b.qubit)
    (h4 : a.phase = b.phase) (h5 : a.metadata = b.metadata) : a = b :=
  match a, b with
  | ⟨_, _, _, _, _⟩, ⟨_, _, _, _, _⟩ =>
    Eq.subst h1 (Eq.subst h2 (Eq.subst h3 (Eq.subst h4 (Eq.subst h5 (Eq.refl _)))))

theorem Node.getMetadata_after_setMetadata (n : Node) (k v : String) (hbeq : (k == k) = true) :
    (n.setMetadata k v).getMetadata k = some v :=
  StringMap.get_insert_self n.metadata k v hbeq

theorem Node.getMetadata_after_setMetadata_ne (n : Node) (k k' v : String) (hne : (k' == k) = false) :
    (n.setMetadata k' v).getMetadata k = StringMap.get (StringMap.remove n.metadata k') k :=
  show StringMap.get ((k', v) :: StringMap.remove n.metadata k') k =
    StringMap.get (StringMap.remove n.metadata k') k from
    show (if k' == k then some v else StringMap.get (StringMap.remove n.metadata k') k) =
      StringMap.get (StringMap.remove n.metadata k') k from
      Eq.mpr (congrArg (fun b => (if b then some v else StringMap.get (StringMap.remove n.metadata k') k) =
        StringMap.get (StringMap.remove n.metadata k') k) hne) (Eq.refl _)

structure Edge where
  source : String
  target : String
  quality : EdgeQuality
  weight : Float
  quantum_correlation : Complex
  fractal_dimension : Float
  metadata : StringMap String
deriving Repr, Inhabited

namespace Edge

noncomputable def init (source target : String) (quality : EdgeQuality) (weight : Float)
    (qc : Complex) (fd : Float) : Edge :=
  ⟨source, target, quality, weight, qc, fd, StringMap.empty⟩

def setMetadata (e : Edge) (key value : String) : Edge :=
  { e with metadata := StringMap.insert e.metadata key value }

def getMetadata (e : Edge) (key : String) : Option String :=
  StringMap.get e.metadata key

noncomputable def correlationMagnitude (e : Edge) : Float :=
  Float.sqrt (e.quantum_correlation.re * e.quantum_correlation.re +
    e.quantum_correlation.im * e.quantum_correlation.im)

def clone (e : Edge) : Edge :=
  ⟨e.source, e.target, e.quality, e.weight, e.quantum_correlation, e.fractal_dimension, e.metadata⟩

end Edge

theorem Edge.init_source (s t : String) (q : EdgeQuality) (w : Float) (qc : Complex) (fd : Float) :
    (Edge.init s t q w qc fd).source = s := Eq.refl _
theorem Edge.init_target (s t : String) (q : EdgeQuality) (w : Float) (qc : Complex) (fd : Float) :
    (Edge.init s t q w qc fd).target = t := Eq.refl _
theorem Edge.init_quality (s t : String) (q : EdgeQuality) (w : Float) (qc : Complex) (fd : Float) :
    (Edge.init s t q w qc fd).quality = q := Eq.refl _
theorem Edge.init_metadata_empty (s t : String) (q : EdgeQuality) (w : Float) (qc : Complex) (fd : Float) :
    (Edge.init s t q w qc fd).metadata = StringMap.empty := Eq.refl _
theorem Edge.clone_eq (e : Edge) : Edge.clone e = e := match e with | ⟨_, _, _, _, _, _, _⟩ => Eq.refl _

theorem Edge.setMetadata_preserves_source (e : Edge) (k v : String) :
    (e.setMetadata k v).source = e.source := match e with | ⟨_, _, _, _, _, _, _⟩ => Eq.refl _
theorem Edge.setMetadata_preserves_target (e : Edge) (k v : String) :
    (e.setMetadata k v).target = e.target := match e with | ⟨_, _, _, _, _, _, _⟩ => Eq.refl _
theorem Edge.setMetadata_preserves_quality (e : Edge) (k v : String) :
    (e.setMetadata k v).quality = e.quality := match e with | ⟨_, _, _, _, _, _, _⟩ => Eq.refl _

theorem Edge.ext (a b : Edge)
    (h1 : a.source = b.source) (h2 : a.target = b.target) (h3 : a.quality = b.quality)
    (h4 : a.weight = b.weight) (h5 : a.quantum_correlation = b.quantum_correlation)
    (h6 : a.fractal_dimension = b.fractal_dimension) (h7 : a.metadata = b.metadata) : a = b :=
  match a, b with
  | ⟨_, _, _, _, _, _, _⟩, ⟨_, _, _, _, _, _, _⟩ =>
    Eq.subst h1 (Eq.subst h2 (Eq.subst h3 (Eq.subst h4 (Eq.subst h5 (Eq.subst h6 (Eq.subst h7 (Eq.refl _)))))))

theorem Edge.getMetadata_after_setMetadata (e : Edge) (k v : String) (hbeq : (k == k) = true) :
    (e.setMetadata k v).getMetadata k = some v :=
  StringMap.get_insert_self e.metadata k v hbeq

structure EdgeKey where
  source : String
  target : String
deriving Repr, Inhabited, BEq, DecidableEq

structure PairKey where
  a : String
  b : String
deriving Repr, Inhabited, BEq, DecidableEq

theorem EdgeKey.ext (x y : EdgeKey) (hs : x.source = y.source) (ht : x.target = y.target) : x = y :=
  match x, y with | ⟨_, _⟩, ⟨_, _⟩ => Eq.subst hs (Eq.subst ht (Eq.refl _))

theorem PairKey.ext (x y : PairKey) (ha : x.a = y.a) (hb : x.b = y.b) : x = y :=
  match x, y with | ⟨_, _⟩, ⟨_, _⟩ => Eq.subst ha (Eq.subst hb (Eq.refl _))

structure TwoQubit where
  amp00 : Complex
  amp01 : Complex
  amp10 : Complex
  amp11 : Complex
deriving Repr, Inhabited

namespace TwoQubit

noncomputable def initBellPhiPlus : TwoQubit :=
  let inv_sqrt2 := 1.0 / Float.sqrt 2.0
  ⟨⟨inv_sqrt2, 0.0⟩, ⟨0.0, 0.0⟩, ⟨0.0, 0.0⟩, ⟨inv_sqrt2, 0.0⟩⟩

def amps (tq : TwoQubit) : Array Complex := #[tq.amp00, tq.amp01, tq.amp10, tq.amp11]

end TwoQubit

theorem TwoQubit.amps_size (tq : TwoQubit) : (TwoQubit.amps tq).size = 4 := Eq.refl _

structure Rng where
  state : UInt64
deriving Repr, Inhabited

namespace Rng

def init (seed : UInt64) : Rng := ⟨seed⟩

def next (r : Rng) : Rng × UInt64 :=
  let s0 := r.state
  let s1 := s0 ^^^ (s0 >>> 12)
  let s2 := s1 ^^^ (s1 <<< 25)
  let s3 := s2 ^^^ (s2 >>> 27)
  let val := s3 * 0x2545F4914F6CDD1D
  (⟨s3⟩, val)

noncomputable def nextFloat (r : Rng) : Rng × Float :=
  let (r', v) := next r
  let f := Float.ofNat (v.toNat % 1000000) / 1000000.0
  (r', f)

end Rng

theorem Rng.init_state (s : UInt64) : (Rng.init s).state = s := Eq.refl _

def sha256K : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
]

def sha256H0Init : Array UInt32 := #[
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
  0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19
]

def rotr32 (x : UInt32) (n : UInt32) : UInt32 :=
  (x >>> n) ||| (x <<< (32 - n))

def sha256Ch (x y z : UInt32) : UInt32 := (x &&& y) ^^^ (x.complement &&& z)
def sha256Maj (x y z : UInt32) : UInt32 := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)
def sha256BigSigma0 (x : UInt32) : UInt32 := rotr32 x 2 ^^^ rotr32 x 13 ^^^ rotr32 x 22
def sha256BigSigma1 (x : UInt32) : UInt32 := rotr32 x 6 ^^^ rotr32 x 11 ^^^ rotr32 x 25
def sha256SmallSigma0 (x : UInt32) : UInt32 := rotr32 x 7 ^^^ rotr32 x 18 ^^^ (x >>> 3)
def sha256SmallSigma1 (x : UInt32) : UInt32 := rotr32 x 17 ^^^ rotr32 x 19 ^^^ (x >>> 10)

def bytesToUInt32BE (b0 b1 b2 b3 : UInt8) : UInt32 :=
  (b0.toUInt32 <<< 24) ||| (b1.toUInt32 <<< 16) ||| (b2.toUInt32 <<< 8) ||| b3.toUInt32

def sha256Pad (msg : ByteArray) : ByteArray :=
  let len := msg.size
  let bitLen : UInt64 := UInt64.ofNat (len * 8)
  let withOne := msg.push 0x80
  let numBlocks := (len + 9 + 63) / 64
  let totalLen := numBlocks * 64
  let zeroCount := if totalLen >= withOne.size + 8 then totalLen - withOne.size - 8 else 0
  let rec addZeros (ba : ByteArray) (n : Nat) : ByteArray :=
    match n with
    | 0 => ba
    | Nat.succ n' => addZeros (ba.push 0x00) n'
  let padded := addZeros withOne zeroCount
  padded
    |>.push (UInt8.ofNat ((bitLen >>> 56).toNat % 256))
    |>.push (UInt8.ofNat ((bitLen >>> 48).toNat % 256))
    |>.push (UInt8.ofNat ((bitLen >>> 40).toNat % 256))
    |>.push (UInt8.ofNat ((bitLen >>> 32).toNat % 256))
    |>.push (UInt8.ofNat ((bitLen >>> 24).toNat % 256))
    |>.push (UInt8.ofNat ((bitLen >>> 16).toNat % 256))
    |>.push (UInt8.ofNat ((bitLen >>> 8).toNat % 256))
    |>.push (UInt8.ofNat (bitLen.toNat % 256))

def sha256ExpandMessage (block : ByteArray) (offset : Nat) : Array UInt32 :=
  let rec buildW (w : Array UInt32) (i : Nat) (fuel : Nat) : Array UInt32 :=
    match fuel with
    | 0 => w
    | Nat.succ fuel' =>
      if i >= 64 then w
      else if i < 16 then
        let b0 := block.get! (offset + i * 4)
        let b1 := block.get! (offset + i * 4 + 1)
        let b2 := block.get! (offset + i * 4 + 2)
        let b3 := block.get! (offset + i * 4 + 3)
        buildW (w.push (bytesToUInt32BE b0 b1 b2 b3)) (i + 1) fuel'
      else
        let s0 := sha256SmallSigma0 (w.get! (i - 15))
        let s1 := sha256SmallSigma1 (w.get! (i - 2))
        let newW := w.get! (i - 16) + s0 + w.get! (i - 7) + s1
        buildW (w.push newW) (i + 1) fuel'
  buildW (Array.mkEmpty 64) 0 64

def sha256Compress (hash : Array UInt32) (w : Array UInt32) : Array UInt32 :=
  let rec go (a b c d e f g h : UInt32) (i : Nat) (fuel : Nat) :
      UInt32 × UInt32 × UInt32 × UInt32 × UInt32 × UInt32 × UInt32 × UInt32 :=
    match fuel with
    | 0 => (a, b, c, d, e, f, g, h)
    | Nat.succ fuel' =>
      if i >= 64 then (a, b, c, d, e, f, g, h)
      else
        let t1 := h + sha256BigSigma1 e + sha256Ch e f g + sha256K.get! i + w.get! i
        let t2 := sha256BigSigma0 a + sha256Maj a b c
        go (t1 + t2) a b c (d + t1) e f g (i + 1) fuel'
  let (a', b', c', d', e', f', g', h') :=
    go (hash.get! 0) (hash.get! 1) (hash.get! 2) (hash.get! 3)
       (hash.get! 4) (hash.get! 5) (hash.get! 6) (hash.get! 7) 0 64
  #[hash.get! 0 + a', hash.get! 1 + b', hash.get! 2 + c', hash.get! 3 + d',
    hash.get! 4 + e', hash.get! 5 + f', hash.get! 6 + g', hash.get! 7 + h']

def sha256ProcessBlock (hash : Array UInt32) (block : ByteArray) (offset : Nat) : Array UInt32 :=
  sha256Compress hash (sha256ExpandMessage block offset)

def sha256Hash (msg : ByteArray) : Array UInt32 :=
  let padded := sha256Pad msg
  let numBlocks := padded.size / 64
  let rec processBlocks (hash : Array UInt32) (i : Nat) (fuel : Nat) : Array UInt32 :=
    match fuel with
    | 0 => hash
    | Nat.succ fuel' =>
      if i >= numBlocks then hash
      else processBlocks (sha256ProcessBlock hash padded (i * 64)) (i + 1) fuel'
  processBlocks sha256H0Init 0 numBlocks

def uint32ToHexChars (v : UInt32) : List Char :=
  let hexChar := fun (n : Nat) => if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)
  [ hexChar ((v.toNat >>> 28) % 16), hexChar ((v.toNat >>> 24) % 16),
    hexChar ((v.toNat >>> 20) % 16), hexChar ((v.toNat >>> 16) % 16),
    hexChar ((v.toNat >>> 12) % 16), hexChar ((v.toNat >>> 8) % 16),
    hexChar ((v.toNat >>> 4) % 16), hexChar (v.toNat % 16) ]

def sha256DigestHex (digest : Array UInt32) : String :=
  let rec buildChars (acc : List Char) (i : Nat) (fuel : Nat) : List Char :=
    match fuel with
    | 0 => acc
    | Nat.succ fuel' =>
      if i >= digest.size then acc
      else buildChars (acc ++ uint32ToHexChars (digest.get! i)) (i + 1) fuel'
  ⟨buildChars [] 0 digest.size⟩

def sha256String (s : String) : String :=
  sha256DigestHex (sha256Hash s.toUTF8)

def sha256Bytes (b : ByteArray) : String :=
  sha256DigestHex (sha256Hash b)

noncomputable def serializeFloat (f : Float) : ByteArray :=
  let s := Float.toString f
  s.toUTF8

def uint64ToBytes (v : UInt64) : ByteArray :=
  ByteArray.mk #[
    UInt8.ofNat (v.toNat % 256),
    UInt8.ofNat ((v.toNat >>> 8) % 256),
    UInt8.ofNat ((v.toNat >>> 16) % 256),
    UInt8.ofNat ((v.toNat >>> 24) % 256),
    UInt8.ofNat ((v.toNat >>> 32) % 256),
    UInt8.ofNat ((v.toNat >>> 40) % 256),
    UInt8.ofNat ((v.toNat >>> 48) % 256),
    UInt8.ofNat ((v.toNat >>> 56) % 256)
  ]

def xorBytesArr (a b : ByteArray) : ByteArray :=
  let maxLen := max a.size b.size
  let rec go (acc : ByteArray) (i : Nat) (fuel : Nat) : ByteArray :=
    match fuel with
    | 0 => acc
    | Nat.succ fuel' =>
      if i >= maxLen then acc
      else
        let av := if i < a.size then a.get! i else 0
        let bv := if i < b.size then b.get! i else 0
        go (acc.push (av ^^^ bv)) (i + 1) fuel'
  go ByteArray.empty 0 maxLen

noncomputable def shaUpdateBytes (acc : ByteArray) (b : ByteArray) : ByteArray :=
  acc ++ uint64ToBytes (UInt64.ofNat b.size) ++ b

noncomputable def shaUpdateF64 (acc : ByteArray) (v : Float) : ByteArray :=
  acc ++ serializeFloat v

def xorDigest (acc : ByteArray) (d : ByteArray) : ByteArray :=
  xorBytesArr acc d

def emptyDigest : ByteArray := ByteArray.mk (Array.mkArray 32 0)

def digestToBytes (digest : Array UInt32) : ByteArray :=
  let rec go (acc : ByteArray) (i : Nat) (fuel : Nat) : ByteArray :=
    match fuel with
    | 0 => acc
    | Nat.succ fuel' =>
      if i >= digest.size then acc
      else
        let w := digest.get! i
        let acc := acc.push (UInt8.ofNat ((w.toNat >>> 24) % 256))
        let acc := acc.push (UInt8.ofNat ((w.toNat >>> 16) % 256))
        let acc := acc.push (UInt8.ofNat ((w.toNat >>> 8) % 256))
        let acc := acc.push (UInt8.ofNat (w.toNat % 256))
        go acc (i + 1) fuel'
  go ByteArray.empty 0 digest.size

structure SelfSimilarRelationalGraph where
  nodes : StringMap Node
  edges : List (EdgeKey × List Edge)
  entanglements : List (PairKey × TwoQubit)
  quantum_register : StringMap Qubit
  topology_hash : String
  rng : Rng
deriving Repr, Inhabited

namespace SelfSimilarRelationalGraph

def nodeCount (g : SelfSimilarRelationalGraph) : Nat := StringMap.size g.nodes

def edgeCount (g : SelfSimilarRelationalGraph) : Nat :=
  g.edges.foldl (fun acc (_, el) => acc + el.length) 0

def getNode (g : SelfSimilarRelationalGraph) (nodeId : String) : Option Node :=
  StringMap.get g.nodes nodeId

def getQuantumState (g : SelfSimilarRelationalGraph) (nodeId : String) : Option Qubit :=
  StringMap.get g.quantum_register nodeId

def canonicalIdPtr (g : SelfSimilarRelationalGraph) (id : String) : Option String :=
  match StringMap.get g.nodes id with
  | some n => some n.id
  | none => none

def lookupEdges (g : SelfSimilarRelationalGraph) (key : EdgeKey) : Option (List Edge) :=
  match g.edges.find? (fun (k, _) => k == key) with
  | some (_, el) => some el
  | none => none

def getEdgesConst (g : SelfSimilarRelationalGraph) (source target : String) : Option (List Edge) :=
  lookupEdges g ⟨source, target⟩

noncomputable def computeNodeHash (n : Node) : ByteArray :=
  let acc := shaUpdateBytes ByteArray.empty n.id.toUTF8
  let acc := shaUpdateBytes acc n.data.toUTF8
  let acc := shaUpdateF64 acc n.phase
  let acc := shaUpdateF64 acc n.qubit.a.re
  let acc := shaUpdateF64 acc n.qubit.a.im
  let acc := shaUpdateF64 acc n.qubit.b.re
  let acc := shaUpdateF64 acc n.qubit.b.im
  let metaAcc := StringMap.foldlKV (fun macc k v =>
    let mh := shaUpdateBytes (shaUpdateBytes ByteArray.empty k.toUTF8) v.toUTF8
    xorDigest macc (digestToBytes (sha256Hash mh))
  ) emptyDigest n.metadata
  let acc := acc ++ metaAcc ++ uint64ToBytes (UInt64.ofNat (StringMap.size n.metadata))
  digestToBytes (sha256Hash acc)

noncomputable def computeEdgeHash (e : Edge) : ByteArray :=
  let acc := shaUpdateBytes ByteArray.empty (EdgeQuality.toString e.quality).toUTF8
  let acc := shaUpdateF64 acc e.weight
  let acc := shaUpdateF64 acc e.fractal_dimension
  let acc := shaUpdateF64 acc e.quantum_correlation.re
  let acc := shaUpdateF64 acc e.quantum_correlation.im
  let metaAcc := StringMap.foldlKV (fun macc k v =>
    let mh := shaUpdateBytes (shaUpdateBytes ByteArray.empty k.toUTF8) v.toUTF8
    xorDigest macc (digestToBytes (sha256Hash mh))
  ) emptyDigest e.metadata
  let acc := acc ++ metaAcc ++ uint64ToBytes (UInt64.ofNat (StringMap.size e.metadata))
  digestToBytes (sha256Hash acc)

noncomputable def computeTopologyHash (g : SelfSimilarRelationalGraph) : String :=
  let accNodes := g.nodes.foldl (fun acc (_, n) =>
    xorDigest acc (computeNodeHash n)) emptyDigest
  let nodeCountVal := StringMap.size g.nodes
  let accEdges := g.edges.foldl (fun acc (ek, edgeList) =>
    let edgesAcc := edgeList.foldl (fun eacc edge =>
      xorDigest eacc (computeEdgeHash edge)) emptyDigest
    let kh := shaUpdateBytes (shaUpdateBytes ByteArray.empty ek.source.toUTF8) ek.target.toUTF8
    let kh := kh ++ edgesAcc ++ uint64ToBytes (UInt64.ofNat edgeList.length)
    xorDigest acc (digestToBytes (sha256Hash kh))) emptyDigest
  let edgekeyCount := g.edges.length
  let totalEdgeCount := g.edges.foldl (fun acc (_, el) => acc + el.length) 0
  let accEnt := g.entanglements.foldl (fun acc (pk, tq) =>
    let h := shaUpdateBytes (shaUpdateBytes ByteArray.empty pk.a.toUTF8) pk.b.toUTF8
    let h := shaUpdateF64 (shaUpdateF64 (shaUpdateF64 (shaUpdateF64
      (shaUpdateF64 (shaUpdateF64 (shaUpdateF64 (shaUpdateF64 h
        tq.amp00.re) tq.amp00.im) tq.amp01.re) tq.amp01.im)
        tq.amp10.re) tq.amp10.im) tq.amp11.re) tq.amp11.im
    xorDigest acc (digestToBytes (sha256Hash h))) emptyDigest
  let entCount := g.entanglements.length
  let finalInput := accNodes
    ++ uint64ToBytes (UInt64.ofNat nodeCountVal)
    ++ accEdges
    ++ uint64ToBytes (UInt64.ofNat edgekeyCount)
    ++ uint64ToBytes (UInt64.ofNat totalEdgeCount)
    ++ accEnt
    ++ uint64ToBytes (UInt64.ofNat entCount)
  sha256DigestHex (sha256Hash finalInput)

noncomputable def updateTopologyHash (g : SelfSimilarRelationalGraph) : SelfSimilarRelationalGraph :=
  { g with topology_hash := computeTopologyHash g }

def getTopologyHashHex (g : SelfSimilarRelationalGraph) : String := g.topology_hash

noncomputable def empty (seed : UInt64) : SelfSimilarRelationalGraph :=
  updateTopologyHash ⟨StringMap.empty, [], [], StringMap.empty, "", Rng.init seed⟩

noncomputable def addNode (g : SelfSimilarRelationalGraph) (node : Node) : SelfSimilarRelationalGraph :=
  let nodes' := StringMap.insert g.nodes node.id node
  let qr' := StringMap.insert g.quantum_register node.id node.qubit
  updateTopologyHash { g with nodes := nodes', quantum_register := qr' }

def insertEdgeInList (edges : List (EdgeKey × List Edge)) (key : EdgeKey) (edge : Edge) :
    List (EdgeKey × List Edge) :=
  match edges with
  | [] => [(key, [edge])]
  | (k, el) :: rest =>
    if k == key then (k, el ++ [edge]) :: rest
    else (k, el) :: insertEdgeInList rest key edge

noncomputable def addEdge (g : SelfSimilarRelationalGraph) (source target : String) (edge : Edge) :
    Option SelfSimilarRelationalGraph :=
  match canonicalIdPtr g source, canonicalIdPtr g target with
  | some s, some t =>
    let storedEdge : Edge := { edge with source := s, target := t }
    let edges' := insertEdgeInList g.edges ⟨s, t⟩ storedEdge
    some (updateTopologyHash { g with edges := edges' })
  | _, _ => none

noncomputable def setQuantumState (g : SelfSimilarRelationalGraph) (nodeId : String) (q : Qubit) :
    Option SelfSimilarRelationalGraph :=
  match StringMap.get g.nodes nodeId with
  | some n =>
    let n' : Node := { n with qubit := q }
    let nodes' := StringMap.insert g.nodes nodeId n'
    let qr' := StringMap.insert g.quantum_register nodeId q
    some (updateTopologyHash { g with nodes := nodes', quantum_register := qr' })
  | none => none

noncomputable def applyQuantumGate (g : SelfSimilarRelationalGraph) (nodeId : String) (gate : Qubit → Qubit) :
    Option SelfSimilarRelationalGraph :=
  match StringMap.get g.nodes nodeId with
  | some n =>
    let q' := gate n.qubit
    let n' : Node := { n with qubit := q' }
    let nodes' := StringMap.insert g.nodes nodeId n'
    let qr' := StringMap.insert g.quantum_register nodeId q'
    some (updateTopologyHash { g with nodes := nodes', quantum_register := qr' })
  | none => none

def canonicalPairKey (a b : String) : PairKey :=
  if a < b then ⟨a, b⟩ else ⟨b, a⟩

noncomputable def entangleNodes (g : SelfSimilarRelationalGraph) (aId bId : String) :
    Option SelfSimilarRelationalGraph :=
  match canonicalIdPtr g aId, canonicalIdPtr g bId with
  | some a, some b =>
    let pk := canonicalPairKey a b
    let ent' := g.entanglements.filter (fun (k, _) => !(k == pk))
    let ent'' := (pk, TwoQubit.initBellPhiPlus) :: ent'
    let edgeAB := Edge.init a b .entangled 1.0 ⟨1.0, 0.0⟩ 0.0
    let edgeBA := Edge.init b a .entangled 1.0 ⟨1.0, 0.0⟩ 0.0
    let g1 := { g with entanglements := ent'' }
    match addEdge g1 a b edgeAB with
    | some g2 =>
      match addEdge g2 b a edgeBA with
      | some g3 => some g3
      | none => none
    | none => none
  | _, _ => none

def findEntanglement (ents : List (PairKey × TwoQubit)) (nodeId : String) :
    Option (PairKey × TwoQubit) :=
  ents.find? (fun (pk, _) => pk.a == nodeId || pk.b == nodeId)

def removeEntanglement (ents : List (PairKey × TwoQubit)) (nodeId : String) :
    List (PairKey × TwoQubit) :=
  ents.filter (fun (pk, _) => !(pk.a == nodeId || pk.b == nodeId))

def updateEdgeQualityAll (edges : List (EdgeKey × List Edge)) (key : EdgeKey) (q : EdgeQuality) :
    List (EdgeKey × List Edge) :=
  edges.map (fun (k, el) =>
    if k == key then
      (k, el.map (fun e => { e with quality := q }))
    else (k, el))

noncomputable def measure (g : SelfSimilarRelationalGraph) (nodeId : String) :
    Option (SelfSimilarRelationalGraph × Nat) :=
  match canonicalIdPtr g nodeId with
  | none => none
  | some nid =>
    match findEntanglement g.entanglements nid with
    | some (pk, state) =>
      let (rng', rf) := Rng.nextFloat g.rng
      let ampsArr := TwoQubit.amps state
      let probList := #[
        Complex.magnitudeSquared ampsArr[0]!,
        Complex.magnitudeSquared ampsArr[1]!,
        Complex.magnitudeSquared ampsArr[2]!,
        Complex.magnitudeSquared ampsArr[3]!
      ]
      let rec findOutcome (cum : Float) (idx : Nat) (fuel : Nat) : Nat :=
        match fuel with
        | 0 => 3
        | Nat.succ fuel' =>
          if idx >= 4 then 3
          else
            let cum' := cum + probList[idx]!
            if rf < cum' then idx
            else findOutcome cum' (idx + 1) fuel'
      let outcomeIdx := findOutcome 0.0 0 4
      let aId := pk.a
      let bId := pk.b
      let aQubit := match outcomeIdx with
        | 0 => Qubit.basis0 | 1 => Qubit.basis0
        | 2 => Qubit.basis1 | _ => Qubit.basis1
      let bQubit := match outcomeIdx with
        | 0 => Qubit.basis0 | 1 => Qubit.basis1
        | 2 => Qubit.basis0 | _ => Qubit.basis1
      let nodes1 := match StringMap.get g.nodes aId with
        | some na => StringMap.insert g.nodes aId { na with qubit := aQubit }
        | none => g.nodes
      let nodes2 := match StringMap.get nodes1 bId with
        | some nb => StringMap.insert nodes1 bId { nb with qubit := bQubit }
        | none => nodes1
      let qr' := StringMap.insert (StringMap.insert g.quantum_register aId aQubit) bId bQubit
      let ent' := removeEntanglement g.entanglements nid
      let edges' := updateEdgeQualityAll (updateEdgeQualityAll g.edges ⟨aId, bId⟩ .collapsed) ⟨bId, aId⟩ .collapsed
      let bit := if nid == aId then (outcomeIdx / 2) % 2 else outcomeIdx % 2
      let g' := updateTopologyHash { g with nodes := nodes2, edges := edges', entanglements := ent',
                                     quantum_register := qr', rng := rng' }
      some (g', bit)
    | none =>
      match StringMap.get g.nodes nid with
      | some n =>
        let (rng', rf) := Rng.nextFloat g.rng
        let p0 := Qubit.prob0 n.qubit
        let bit : Nat := if rf < p0 then 0 else 1
        let q' := if bit == 0 then Qubit.basis0 else Qubit.basis1
        let n' : Node := { n with qubit := q' }
        let nodes' := StringMap.insert g.nodes nid n'
        let qr' := StringMap.insert g.quantum_register nid q'
        let g' := updateTopologyHash { g with nodes := nodes', quantum_register := qr', rng := rng' }
        some (g', bit)
      | none => none

noncomputable def clear (g : SelfSimilarRelationalGraph) : SelfSimilarRelationalGraph :=
  updateTopologyHash { g with
    nodes := StringMap.empty, edges := [], entanglements := [], quantum_register := StringMap.empty }

def getAllNodeIds (g : SelfSimilarRelationalGraph) : List String :=
  (StringMap.keys g.nodes).mergeSort (· < ·)

noncomputable def encodeInformation (g : SelfSimilarRelationalGraph) (data : String) :
    SelfSimilarRelationalGraph × String :=
  let hashDigest := sha256Hash data.toUTF8
  let nodeId := sha256DigestHex hashDigest |>.take 16
  let node := Node.init nodeId data Qubit.basis0 0.0
  let g' := addNode g node
  let ids := getAllNodeIds g'
  let maxLinks := min (ids.length - 1) 3
  let rec linkNodes (remaining : List String) (gAcc : SelfSimilarRelationalGraph) (linked : Nat) :
      SelfSimilarRelationalGraph :=
    match remaining with
    | [] => gAcc
    | prevId :: rest =>
      if linked >= maxLinks then gAcc
      else if prevId == nodeId then linkNodes rest gAcc linked
      else
        match canonicalIdPtr gAcc nodeId, canonicalIdPtr gAcc prevId with
        | some src, some dst =>
          let e := Edge.init src dst .coherent 0.5 ⟨0.0, 0.0⟩ 0.0
          match addEdge gAcc src dst e with
          | some gNext => linkNodes rest gNext (linked + 1)
          | none => linkNodes rest gAcc linked
        | _, _ => linkNodes rest gAcc linked
  let g'' := linkNodes ids.reverse g' 0
  (g'', nodeId)

def decodeInformation (g : SelfSimilarRelationalGraph) (nodeId : String) : Option String :=
  match StringMap.get g.nodes nodeId with
  | some n => some n.data
  | none => none

noncomputable def exportNodeEmbeddings (g : SelfSimilarRelationalGraph) :
    List (Float × Float × Float × Float) :=
  g.nodes.map (fun (_, n) => (n.qubit.a.re, n.qubit.a.im, n.qubit.b.re, n.qubit.b.im))

noncomputable def importNodeEmbeddings (g : SelfSimilarRelationalGraph)
    (embeddings : List (Float × Float × Float × Float)) : SelfSimilarRelationalGraph :=
  let zipped := g.nodes.zip embeddings
  let nodes' := zipped.foldl (fun acc ((k, n), (ar, ai, br, bi)) =>
    StringMap.insert acc k { n with qubit := ⟨⟨ar, ai⟩, ⟨br, bi⟩⟩ }) StringMap.empty
  let qr' := nodes'.foldl (fun acc (k, n) =>
    StringMap.insert acc k n.qubit) StringMap.empty
  updateTopologyHash { g with nodes := nodes', quantum_register := qr' }

noncomputable def exportAdjacencyMatrix (g : SelfSimilarRelationalGraph) (nodeIds : List String) :
    List (List Float) :=
  nodeIds.map (fun src =>
    nodeIds.map (fun tgt =>
      let key := EdgeKey.mk src tgt
      match g.edges.find? (fun (k, _) => k == key) with
      | some (_, el) => Float.ofNat el.length
      | none => 0.0))

end SelfSimilarRelationalGraph

noncomputable def hadamardGate (q : Qubit) : Qubit :=
  let inv_sqrt2 := 1.0 / Float.sqrt 2.0
  let s : Complex := ⟨inv_sqrt2, 0.0⟩
  Qubit.normalize ⟨Complex.mul (Complex.add q.a q.b) s, Complex.mul (Complex.sub q.a q.b) s⟩

noncomputable def pauliXGate (q : Qubit) : Qubit :=
  Qubit.normalize ⟨q.b, q.a⟩

noncomputable def pauliYGate (q : Qubit) : Qubit :=
  Qubit.normalize ⟨Complex.mul Complex.neg_i_unit q.b, Complex.mul Complex.i_unit q.a⟩

noncomputable def pauliZGate (q : Qubit) : Qubit :=
  Qubit.normalize ⟨q.a, Complex.mul q.b ⟨-1.0, 0.0⟩⟩

def identityGate (q : Qubit) : Qubit := q

noncomputable def phaseGate (phase : Float) (q : Qubit) : Qubit :=
  let c_val := Float.cos phase
  let s_val := Float.sin phase
  Qubit.normalize ⟨q.a, Complex.mul q.b ⟨c_val, s_val⟩⟩

theorem identityGate_id (q : Qubit) : identityGate q = q := Eq.refl _
theorem identityGate_twice (q : Qubit) : identityGate (identityGate q) = q := Eq.refl _
theorem identityGate_preserves_a (q : Qubit) : (identityGate q).a = q.a := Eq.refl _
theorem identityGate_preserves_b (q : Qubit) : (identityGate q).b = q.b := Eq.refl _
theorem identityGate_eq_id : @identityGate = @id Qubit := funext fun q => Eq.refl _

theorem SelfSimilarRelationalGraph.updateTopologyHash_nodes (g : SelfSimilarRelationalGraph) :
    (SelfSimilarRelationalGraph.updateTopologyHash g).nodes = g.nodes := Eq.refl _
theorem SelfSimilarRelationalGraph.updateTopologyHash_edges (g : SelfSimilarRelationalGraph) :
    (SelfSimilarRelationalGraph.updateTopologyHash g).edges = g.edges := Eq.refl _
theorem SelfSimilarRelationalGraph.updateTopologyHash_entanglements (g : SelfSimilarRelationalGraph) :
    (SelfSimilarRelationalGraph.updateTopologyHash g).entanglements = g.entanglements := Eq.refl _
theorem SelfSimilarRelationalGraph.updateTopologyHash_quantum_register (g : SelfSimilarRelationalGraph) :
    (SelfSimilarRelationalGraph.updateTopologyHash g).quantum_register = g.quantum_register := Eq.refl _
theorem SelfSimilarRelationalGraph.updateTopologyHash_rng (g : SelfSimilarRelationalGraph) :
    (SelfSimilarRelationalGraph.updateTopologyHash g).rng = g.rng := Eq.refl _
theorem SelfSimilarRelationalGraph.updateTopologyHash_hash (g : SelfSimilarRelationalGraph) :
    (SelfSimilarRelationalGraph.updateTopologyHash g).topology_hash =
    SelfSimilarRelationalGraph.computeTopologyHash g := Eq.refl _
theorem SelfSimilarRelationalGraph.updateTopologyHash_nodeCount (g : SelfSimilarRelationalGraph) :
    SelfSimilarRelationalGraph.nodeCount (SelfSimilarRelationalGraph.updateTopologyHash g) =
    SelfSimilarRelationalGraph.nodeCount g := Eq.refl _
theorem SelfSimilarRelationalGraph.updateTopologyHash_edgeCount (g : SelfSimilarRelationalGraph) :
    SelfSimilarRelationalGraph.edgeCount (SelfSimilarRelationalGraph.updateTopologyHash g) =
    SelfSimilarRelationalGraph.edgeCount g := Eq.refl _

theorem SelfSimilarRelationalGraph.addNode_preserves_edges (g : SelfSimilarRelationalGraph) (n : Node) :
    (SelfSimilarRelationalGraph.addNode g n).edges = g.edges := Eq.refl _
theorem SelfSimilarRelationalGraph.addNode_preserves_entanglements (g : SelfSimilarRelationalGraph) (n : Node) :
    (SelfSimilarRelationalGraph.addNode g n).entanglements = g.entanglements := Eq.refl _
theorem SelfSimilarRelationalGraph.addNode_preserves_rng (g : SelfSimilarRelationalGraph) (n : Node) :
    (SelfSimilarRelationalGraph.addNode g n).rng = g.rng := Eq.refl _

theorem SelfSimilarRelationalGraph.addNode_nodeCount_positive (g : SelfSimilarRelationalGraph) (n : Node) :
    0 < SelfSimilarRelationalGraph.nodeCount (SelfSimilarRelationalGraph.addNode g n) :=
  show 0 < StringMap.size (StringMap.insert g.nodes n.id n) from Nat.succ_pos _

theorem SelfSimilarRelationalGraph.addNode_getNode_self (g : SelfSimilarRelationalGraph) (n : Node)
    (hbeq : (n.id == n.id) = true) :
    SelfSimilarRelationalGraph.getNode (SelfSimilarRelationalGraph.addNode g n) n.id = some n :=
  StringMap.get_insert_self g.nodes n.id n hbeq

theorem SelfSimilarRelationalGraph.addNode_getQuantumState (g : SelfSimilarRelationalGraph) (n : Node)
    (hbeq : (n.id == n.id) = true) :
    SelfSimilarRelationalGraph.getQuantumState (SelfSimilarRelationalGraph.addNode g n) n.id = some n.qubit :=
  StringMap.get_insert_self g.quantum_register n.id n.qubit hbeq

theorem SelfSimilarRelationalGraph.decodeInformation_after_addNode
    (g : SelfSimilarRelationalGraph) (n : Node)
    (hbeq : (n.id == n.id) = true) :
    SelfSimilarRelationalGraph.decodeInformation (SelfSimilarRelationalGraph.addNode g n) n.id = some n.data :=
  have hlookup : StringMap.get (StringMap.insert g.nodes n.id n) n.id = some n :=
    StringMap.get_insert_self g.nodes n.id n hbeq
  show (match StringMap.get (StringMap.insert g.nodes n.id n) n.id with
    | some nd => some nd.data | none => none) = some n.data from
    Eq.mpr (congrArg (fun x => (match x with | some nd => some nd.data | none => none) = some n.data) hlookup)
      (Eq.refl (some n.data))

theorem SelfSimilarRelationalGraph.addEdge_none_on_missing_source
    (g : SelfSimilarRelationalGraph) (s t : String) (e : Edge)
    (hs : SelfSimilarRelationalGraph.canonicalIdPtr g s = none) :
    SelfSimilarRelationalGraph.addEdge g s t e = none :=
  show (match SelfSimilarRelationalGraph.canonicalIdPtr g s, SelfSimilarRelationalGraph.canonicalIdPtr g t with
    | some _, some _ => _ | _, _ => none) = none from
    Eq.mpr (congrArg (fun x => (match x, SelfSimilarRelationalGraph.canonicalIdPtr g t with
      | some _, some _ => _ | _, _ => none) = none) hs) (Eq.refl none)

theorem SelfSimilarRelationalGraph.addEdge_none_on_missing_target
    (g : SelfSimilarRelationalGraph) (s t : String) (e : Edge)
    (hs : ∃ sv, SelfSimilarRelationalGraph.canonicalIdPtr g s = some sv)
    (ht : SelfSimilarRelationalGraph.canonicalIdPtr g t = none) :
    SelfSimilarRelationalGraph.addEdge g s t e = none :=
  match hs with
  | ⟨sv, hsv⟩ =>
    show (match SelfSimilarRelationalGraph.canonicalIdPtr g s, SelfSimilarRelationalGraph.canonicalIdPtr g t with
      | some _, some _ => _ | _, _ => none) = none from
      Eq.mpr (congrArg (fun x => (match SelfSimilarRelationalGraph.canonicalIdPtr g s, x with
        | some _, some _ => _ | _, _ => none) = none) ht)
        (Eq.mpr (congrArg (fun x => (match x, none with | some _, some _ => _ | _, _ => none) = none) hsv)
          (Eq.refl none))

theorem SelfSimilarRelationalGraph.setQuantumState_none_on_missing
    (g : SelfSimilarRelationalGraph) (nodeId : String) (q : Qubit)
    (h : StringMap.get g.nodes nodeId = none) :
    SelfSimilarRelationalGraph.setQuantumState g nodeId q = none :=
  show (match StringMap.get g.nodes nodeId with | some _ => _ | none => none) = none from
    Eq.mpr (congrArg (fun x => (match x with | some _ => _ | none => none) = none) h) (Eq.refl none)

theorem SelfSimilarRelationalGraph.applyQuantumGate_none_on_missing
    (g : SelfSimilarRelationalGraph) (nodeId : String) (gate : Qubit → Qubit)
    (h : StringMap.get g.nodes nodeId = none) :
    SelfSimilarRelationalGraph.applyQuantumGate g nodeId gate = none :=
  show (match StringMap.get g.nodes nodeId with | some _ => _ | none => none) = none from
    Eq.mpr (congrArg (fun x => (match x with | some _ => _ | none => none) = none) h) (Eq.refl none)

theorem SelfSimilarRelationalGraph.measure_none_on_missing
    (g : SelfSimilarRelationalGraph) (nodeId : String)
    (h : SelfSimilarRelationalGraph.canonicalIdPtr g nodeId = none) :
    SelfSimilarRelationalGraph.measure g nodeId = none :=
  show (match SelfSimilarRelationalGraph.canonicalIdPtr g nodeId with | none => none | some _ => _) = none from
    Eq.mpr (congrArg (fun x => (match x with | none => none | some _ => _) = none) h) (Eq.refl none)

theorem SelfSimilarRelationalGraph.entangleNodes_none_on_missing_first
    (g : SelfSimilarRelationalGraph) (aId bId : String)
    (h : SelfSimilarRelationalGraph.canonicalIdPtr g aId = none) :
    SelfSimilarRelationalGraph.entangleNodes g aId bId = none :=
  show (match SelfSimilarRelationalGraph.canonicalIdPtr g aId, SelfSimilarRelationalGraph.canonicalIdPtr g bId with
    | some _, some _ => _ | _, _ => none) = none from
    Eq.mpr (congrArg (fun x => (match x, SelfSimilarRelationalGraph.canonicalIdPtr g bId with
      | some _, some _ => _ | _, _ => none) = none) h) (Eq.refl none)

theorem SelfSimilarRelationalGraph.decodeInformation_none_when_absent
    (g : SelfSimilarRelationalGraph) (nodeId : String)
    (h : StringMap.get g.nodes nodeId = none) :
    SelfSimilarRelationalGraph.decodeInformation g nodeId = none :=
  show (match StringMap.get g.nodes nodeId with | some n => some n.data | none => none) = none from
    Eq.mpr (congrArg (fun x => (match x with | some n => some n.data | none => none) = none) h) (Eq.refl none)

theorem SelfSimilarRelationalGraph.clear_nodeCount (g : SelfSimilarRelationalGraph) :
    SelfSimilarRelationalGraph.nodeCount (SelfSimilarRelationalGraph.clear g) = 0 := Eq.refl _
theorem SelfSimilarRelationalGraph.clear_edgeCount (g : SelfSimilarRelationalGraph) :
    SelfSimilarRelationalGraph.edgeCount (SelfSimilarRelationalGraph.clear g) = 0 := Eq.refl _
theorem SelfSimilarRelationalGraph.clear_entanglements (g : SelfSimilarRelationalGraph) :
    (SelfSimilarRelationalGraph.clear g).entanglements = [] := Eq.refl _
theorem SelfSimilarRelationalGraph.clear_preserves_rng (g : SelfSimilarRelationalGraph) :
    (SelfSimilarRelationalGraph.clear g).rng = g.rng := Eq.refl _
theorem SelfSimilarRelationalGraph.clear_decodeInformation (g : SelfSimilarRelationalGraph) (id : String) :
    SelfSimilarRelationalGraph.decodeInformation (SelfSimilarRelationalGraph.clear g) id = none := Eq.refl _
theorem SelfSimilarRelationalGraph.clear_getNode (g : SelfSimilarRelationalGraph) (id : String) :
    SelfSimilarRelationalGraph.getNode (SelfSimilarRelationalGraph.clear g) id = none := Eq.refl _
theorem SelfSimilarRelationalGraph.clear_getQuantumState (g : SelfSimilarRelationalGraph) (id : String) :
    SelfSimilarRelationalGraph.getQuantumState (SelfSimilarRelationalGraph.clear g) id = none := Eq.refl _
theorem SelfSimilarRelationalGraph.clear_getAllNodeIds (g : SelfSimilarRelationalGraph) :
    SelfSimilarRelationalGraph.getAllNodeIds (SelfSimilarRelationalGraph.clear g) = [] := Eq.refl _

theorem SelfSimilarRelationalGraph.getEdgesConst_eq_lookupEdges
    (g : SelfSimilarRelationalGraph) (s t : String) :
    SelfSimilarRelationalGraph.getEdgesConst g s t =
    SelfSimilarRelationalGraph.lookupEdges g ⟨s, t⟩ := Eq.refl _

theorem SelfSimilarRelationalGraph.insertEdgeInList_nonempty
    (edges : List (EdgeKey × List Edge)) (key : EdgeKey) (edge : Edge) :
    SelfSimilarRelationalGraph.insertEdgeInList edges key edge ≠ [] :=
  match edges with
  | [] => fun h => List.noConfusion h
  | (_, _) :: _ => fun h => List.noConfusion h

theorem SelfSimilarRelationalGraph.findEntanglement_nil (nodeId : String) :
    SelfSimilarRelationalGraph.findEntanglement [] nodeId = none := Eq.refl _
theorem SelfSimilarRelationalGraph.removeEntanglement_nil (nodeId : String) :
    SelfSimilarRelationalGraph.removeEntanglement [] nodeId = [] := Eq.refl _
theorem SelfSimilarRelationalGraph.insertEdgeInList_nil (key : EdgeKey) (edge : Edge) :
    SelfSimilarRelationalGraph.insertEdgeInList [] key edge = [(key, [edge])] := Eq.refl _
theorem SelfSimilarRelationalGraph.updateEdgeQualityAll_nil (key : EdgeKey) (q : EdgeQuality) :
    SelfSimilarRelationalGraph.updateEdgeQualityAll [] key q = [] := Eq.refl _

theorem SelfSimilarRelationalGraph.updateEdgeQualityAll_length
    (edges : List (EdgeKey × List Edge)) (key : EdgeKey) (q : EdgeQuality) :
    (SelfSimilarRelationalGraph.updateEdgeQualityAll edges key q).length = edges.length :=
  List.length_map _ edges

theorem SelfSimilarRelationalGraph.removeEntanglement_length_le
    (ents : List (PairKey × TwoQubit)) (nodeId : String) :
    (SelfSimilarRelationalGraph.removeEntanglement ents nodeId).length ≤ ents.length :=
  List.length_filter_le _ ents

theorem SelfSimilarRelationalGraph.addNode_then_getNode_other
    (g : SelfSimilarRelationalGraph) (n : Node) (otherId : String)
    (hne : (n.id == otherId) = false) :
    SelfSimilarRelationalGraph.getNode (SelfSimilarRelationalGraph.addNode g n) otherId =
    StringMap.get (StringMap.remove g.nodes n.id) otherId :=
  show StringMap.get ((n.id, n) :: StringMap.remove g.nodes n.id) otherId =
    StringMap.get (StringMap.remove g.nodes n.id) otherId from
    show (if n.id == otherId then some n else StringMap.get (StringMap.remove g.nodes n.id) otherId) =
      StringMap.get (StringMap.remove g.nodes n.id) otherId from
      Eq.mpr (congrArg (fun b => (if b then some n else StringMap.get (StringMap.remove g.nodes n.id) otherId) =
        StringMap.get (StringMap.remove g.nodes n.id) otherId) hne) (Eq.refl _)

theorem SelfSimilarRelationalGraph.addNode_then_getQuantumState_other
    (g : SelfSimilarRelationalGraph) (n : Node) (otherId : String)
    (hne : (n.id == otherId) = false) :
    SelfSimilarRelationalGraph.getQuantumState (SelfSimilarRelationalGraph.addNode g n) otherId =
    StringMap.get (StringMap.remove g.quantum_register n.id) otherId :=
  show StringMap.get ((n.id, n.qubit) :: StringMap.remove g.quantum_register n.id) otherId =
    StringMap.get (StringMap.remove g.quantum_register n.id) otherId from
    show (if n.id == otherId then some n.qubit else StringMap.get (StringMap.remove g.quantum_register n.id) otherId) =
      StringMap.get (StringMap.remove g.quantum_register n.id) otherId from
      Eq.mpr (congrArg (fun b => (if b then some n.qubit else StringMap.get (StringMap.remove g.quantum_register n.id) otherId) =
        StringMap.get (StringMap.remove g.quantum_register n.id) otherId) hne) (Eq.refl _)

theorem SelfSimilarRelationalGraph.nodeCount_eq_nodes_size (g : SelfSimilarRelationalGraph) :
    SelfSimilarRelationalGraph.nodeCount g = StringMap.size g.nodes := Eq.refl _

theorem SelfSimilarRelationalGraph.addNode_updates_hash (g : SelfSimilarRelationalGraph) (n : Node) :
    (SelfSimilarRelationalGraph.addNode g n).topology_hash =
    SelfSimilarRelationalGraph.computeTopologyHash
      { g with nodes := StringMap.insert g.nodes n.id n,
               quantum_register := StringMap.insert g.quantum_register n.id n.qubit } := Eq.refl _

theorem SelfSimilarRelationalGraph.addEdge_preserves_quantum_register_when_found
    (g : SelfSimilarRelationalGraph) (s t : String) (e : Edge)
    (sv tv : String)
    (hs : SelfSimilarRelationalGraph.canonicalIdPtr g s = some sv)
    (ht : SelfSimilarRelationalGraph.canonicalIdPtr g t = some tv) :
    ∃ g', SelfSimilarRelationalGraph.addEdge g s t e = some g' ∧
          g'.quantum_register = g.quantum_register ∧
          g'.nodes = g.nodes ∧
          g'.entanglements = g.entanglements :=
  have hdef : SelfSimilarRelationalGraph.addEdge g s t e =
    some (SelfSimilarRelationalGraph.updateTopologyHash
      { g with edges := SelfSimilarRelationalGraph.insertEdgeInList g.edges ⟨sv, tv⟩ { e with source := sv, target := tv } }) :=
    show (match SelfSimilarRelationalGraph.canonicalIdPtr g s, SelfSimilarRelationalGraph.canonicalIdPtr g t with
      | some _, some _ => _ | _, _ => none) = _ from
      Eq.mpr (congrArg (fun x => (match x, SelfSimilarRelationalGraph.canonicalIdPtr g t with
        | some _, some _ => _ | _, _ => none) = _) hs)
        (Eq.mpr (congrArg (fun x => (match some sv, x with
          | some _, some _ => _ | _, _ => none) = _) ht)
          (Eq.refl _))
  let g' := SelfSimilarRelationalGraph.updateTopologyHash
    { g with edges := SelfSimilarRelationalGraph.insertEdgeInList g.edges ⟨sv, tv⟩ { e with source := sv, target := tv } }
  Exists.intro g' (And.intro hdef (And.intro (Eq.refl _) (And.intro (Eq.refl _) (Eq.refl _))))

theorem SelfSimilarRelationalGraph.setQuantumState_preserves_edges
    (g : SelfSimilarRelationalGraph) (nodeId : String) (q : Qubit)
    (hn : ∃ n, StringMap.get g.nodes nodeId = some n) :
    ∃ g', SelfSimilarRelationalGraph.setQuantumState g nodeId q = some g' ∧ g'.edges = g.edges :=
  match hn with
  | ⟨n, hn_eq⟩ =>
    let g' := SelfSimilarRelationalGraph.updateTopologyHash
      { g with nodes := StringMap.insert g.nodes nodeId { n with qubit := q },
               quantum_register := StringMap.insert g.quantum_register nodeId q }
    Exists.intro g'
      (And.intro
        (show (match StringMap.get g.nodes nodeId with | some _ => _ | none => none) = some g' from
          Eq.mpr (congrArg (fun x => (match x with | some _ => _ | none => none) = some g') hn_eq)
            (Eq.refl _))
        (Eq.refl _))

theorem SelfSimilarRelationalGraph.setQuantumState_preserves_entanglements
    (g : SelfSimilarRelationalGraph) (nodeId : String) (q : Qubit)
    (hn : ∃ n, StringMap.get g.nodes nodeId = some n) :
    ∃ g', SelfSimilarRelationalGraph.setQuantumState g nodeId q = some g' ∧
          g'.entanglements = g.entanglements :=
  match hn with
  | ⟨n, hn_eq⟩ =>
    let g' := SelfSimilarRelationalGraph.updateTopologyHash
      { g with nodes := StringMap.insert g.nodes nodeId { n with qubit := q },
               quantum_register := StringMap.insert g.quantum_register nodeId q }
    Exists.intro g'
      (And.intro
        (show (match StringMap.get g.nodes nodeId with | some _ => _ | none => none) = some g' from
          Eq.mpr (congrArg (fun x => (match x with | some _ => _ | none => none) = some g') hn_eq)
            (Eq.refl _))
        (Eq.refl _))

theorem SelfSimilarRelationalGraph.applyQuantumGate_preserves_edges
    (g : SelfSimilarRelationalGraph) (nodeId : String) (gate : Qubit → Qubit)
    (hn : ∃ n, StringMap.get g.nodes nodeId = some n) :
    ∃ g', SelfSimilarRelationalGraph.applyQuantumGate g nodeId gate = some g' ∧ g'.edges = g.edges :=
  match hn with
  | ⟨n, hn_eq⟩ =>
    let q' := gate n.qubit
    let g' := SelfSimilarRelationalGraph.updateTopologyHash
      { g with nodes := StringMap.insert g.nodes nodeId { n with qubit := q' },
               quantum_register := StringMap.insert g.quantum_register nodeId q' }
    Exists.intro g'
      (And.intro
        (show (match StringMap.get g.nodes nodeId with | some _ => _ | none => none) = some g' from
          Eq.mpr (congrArg (fun x => (match x with | some _ => _ | none => none) = some g') hn_eq)
            (Eq.refl _))
        (Eq.refl _))

theorem SelfSimilarRelationalGraph.addNode_then_decode
    (g : SelfSimilarRelationalGraph) (id data : String) (q : Qubit) (p : Float)
    (hbeq : (id == id) = true) :
    SelfSimilarRelationalGraph.decodeInformation
      (SelfSimilarRelationalGraph.addNode g (Node.init id data q p)) id = some data :=
  have hlookup : StringMap.get (StringMap.insert g.nodes id (Node.init id data q p)) id =
    some (Node.init id data q p) := StringMap.get_insert_self g.nodes id (Node.init id data q p) hbeq
  show (match StringMap.get (StringMap.insert g.nodes id (Node.init id data q p)) id with
    | some nd => some nd.data | none => none) = some data from
    Eq.mpr (congrArg (fun x => (match x with | some nd => some nd.data | none => none) = some data) hlookup)
      (Eq.refl (some data))

theorem SelfSimilarRelationalGraph.two_addNodes_second_present
    (g : SelfSimilarRelationalGraph) (n1 n2 : Node)
    (hbeq2 : (n2.id == n2.id) = true) :
    SelfSimilarRelationalGraph.getNode
      (SelfSimilarRelationalGraph.addNode (SelfSimilarRelationalGraph.addNode g n1) n2) n2.id = some n2 :=
  StringMap.get_insert_self (SelfSimilarRelationalGraph.addNode g n1).nodes n2.id n2 hbeq2

theorem SelfSimilarRelationalGraph.measure_returns_some_implies_canonical_exists
    (g : SelfSimilarRelationalGraph) (nodeId : String)
    (g' : SelfSimilarRelationalGraph) (bit : Nat)
    (hm : SelfSimilarRelationalGraph.measure g nodeId = some (g', bit)) :
    ∃ nid, SelfSimilarRelationalGraph.canonicalIdPtr g nodeId = some nid :=
  match hcan : SelfSimilarRelationalGraph.canonicalIdPtr g nodeId with
  | some nid => Exists.intro nid (Eq.refl _)
  | none =>
    absurd hm
      (fun hm2 =>
        have : SelfSimilarRelationalGraph.measure g nodeId = none :=
          show (match SelfSimilarRelationalGraph.canonicalIdPtr g nodeId with | none => none | some _ => _) = none from
            Eq.mpr (congrArg (fun x => (match x with | none => none | some _ => _) = none) hcan) (Eq.refl none)
        Option.noConfusion (Eq.trans (Eq.symm hm2) this))

theorem SelfSimilarRelationalGraph.exportNodeEmbeddings_length_eq_nodeCount
    (g : SelfSimilarRelationalGraph) :
    (SelfSimilarRelationalGraph.exportNodeEmbeddings g).length =
    SelfSimilarRelationalGraph.nodeCount g :=
  List.length_map _ g.nodes

theorem SelfSimilarRelationalGraph.addNode_then_clear_nodeCount
    (g : SelfSimilarRelationalGraph) (n : Node) :
    SelfSimilarRelationalGraph.nodeCount
      (SelfSimilarRelationalGraph.clear (SelfSimilarRelationalGraph.addNode g n)) = 0 := Eq.refl _

theorem SelfSimilarRelationalGraph.addNode_then_clear_edgeCount
    (g : SelfSimilarRelationalGraph) (n : Node) :
    SelfSimilarRelationalGraph.edgeCount
      (SelfSimilarRelationalGraph.clear (SelfSimilarRelationalGraph.addNode g n)) = 0 := Eq.refl _

theorem EdgeQuality.total_distinct :
    (EdgeQuality.superposition ≠ EdgeQuality.entangled) ∧
    (EdgeQuality.superposition ≠ EdgeQuality.coherent) ∧
    (EdgeQuality.superposition ≠ EdgeQuality.collapsed) ∧
    (EdgeQuality.superposition ≠ EdgeQuality.fractal) ∧
    (EdgeQuality.entangled ≠ EdgeQuality.coherent) ∧
    (EdgeQuality.entangled ≠ EdgeQuality.collapsed) ∧
    (EdgeQuality.entangled ≠ EdgeQuality.fractal) ∧
    (EdgeQuality.coherent ≠ EdgeQuality.collapsed) ∧
    (EdgeQuality.coherent ≠ EdgeQuality.fractal) ∧
    (EdgeQuality.collapsed ≠ EdgeQuality.fractal) :=
  And.intro EdgeQuality.superposition_ne_entangled
    (And.intro EdgeQuality.superposition_ne_coherent
      (And.intro EdgeQuality.superposition_ne_collapsed
        (And.intro EdgeQuality.superposition_ne_fractal
          (And.intro EdgeQuality.entangled_ne_coherent
            (And.intro EdgeQuality.entangled_ne_collapsed
              (And.intro EdgeQuality.entangled_ne_fractal
                (And.intro EdgeQuality.coherent_ne_collapsed
                  (And.intro EdgeQuality.coherent_ne_fractal
                    EdgeQuality.collapsed_ne_fractal))))))))

theorem Nat.zero_add_thm (n : Nat) : 0 + n = n :=
  Nat.recOn n (Eq.refl _) (fun n' ih => congrArg Nat.succ ih)

theorem Nat.add_zero_thm (n : Nat) : n + 0 = n := Eq.refl _

theorem Nat.succ_add_thm (m n : Nat) : Nat.succ m + n = Nat.succ (m + n) :=
  Nat.recOn n (Eq.refl _) (fun n' ih => congrArg Nat.succ ih)

theorem Nat.add_succ_thm (m n : Nat) : m + Nat.succ n = Nat.succ (m + n) := Eq.refl _

theorem Nat.add_comm_thm (m n : Nat) : m + n = n + m :=
  Nat.recOn n
    (Eq.trans (Nat.add_zero_thm m) (Eq.symm (Nat.zero_add_thm m)))
    (fun n' ih =>
      Eq.trans (Nat.add_succ_thm m n')
        (Eq.trans (congrArg Nat.succ ih) (Eq.symm (Nat.succ_add_thm n' m))))

theorem Nat.add_assoc_thm (a b c : Nat) : a + b + c = a + (b + c) :=
  Nat.recOn c (Eq.refl _) (fun c' ih => congrArg Nat.succ ih)

theorem Nat.succ_ne_zero_thm (n : Nat) : Nat.succ n ≠ 0 := fun h => Nat.noConfusion h
theorem Nat.zero_ne_succ_thm (n : Nat) : 0 ≠ Nat.succ n := fun h => Nat.noConfusion h

theorem Nat.succ_injective_thm (m n : Nat) (h : Nat.succ m = Nat.succ n) : m = n :=
  Nat.noConfusion h id

theorem Nat.le_of_eq_thm (a b : Nat) (h : a = b) : a ≤ b := Eq.subst h (Nat.le_refl a)

theorem Nat.add_le_add_left_thm (k m n : Nat) (h : m ≤ n) : k + m ≤ k + n :=
  Nat.recOn k
    (Eq.mpr (congrArg (· ≤ 0 + n) (Nat.zero_add_thm m))
      (Eq.mpr (congrArg (m ≤ ·) (Nat.zero_add_thm n)) h))
    (fun k' ih =>
      Eq.mpr (congrArg (· ≤ Nat.succ k' + n) (Nat.succ_add_thm k' m))
        (Eq.mpr (congrArg (Nat.succ (k' + m) ≤ ·) (Nat.succ_add_thm k' n))
          (Nat.succ_le_succ ih)))

theorem Nat.add_le_add_right_thm (m n k : Nat) (h : m ≤ n) : m + k ≤ n + k :=
  Eq.mpr (congrArg (· ≤ n + k) (Nat.add_comm_thm m k))
    (Eq.mpr (congrArg (k + m ≤ ·) (Nat.add_comm_thm n k))
      (Nat.add_le_add_left_thm k m n h))

theorem Nat.mul_one_thm (n : Nat) : n * 1 = n := Nat.add_zero_thm n

theorem Nat.one_mul_thm (n : Nat) : 1 * n = n :=
  Nat.recOn n (Eq.refl _) (fun n' ih => congrArg Nat.succ ih)

theorem Nat.min_self_thm (n : Nat) : min n n = n :=
  Nat.recOn n (Eq.refl _) (fun n' ih => congrArg Nat.succ ih)

theorem Option.some_ne_none_thm {α : Type} (a : α) : some a ≠ none := fun h => Option.noConfusion h
theorem Option.none_ne_some_thm {α : Type} (a : α) : (none : Option α) ≠ some a := fun h => Option.noConfusion h
theorem Option.some_injective_thm {α : Type} (a b : α) (h : some a = some b) : a = b := Option.noConfusion h id

theorem Bool.and_self_thm (b : Bool) : (b && b) = b := match b with | true => Eq.refl _ | false => Eq.refl _
theorem Bool.or_self_thm (b : Bool) : (b || b) = b := match b with | true => Eq.refl _ | false => Eq.refl _
theorem Bool.not_not_thm (b : Bool) : (!!b) = b := match b with | true => Eq.refl _ | false => Eq.refl _
theorem Bool.true_ne_false_thm : true ≠ false := fun h => Bool.noConfusion h
theorem Bool.false_ne_true_thm : false ≠ true := fun h => Bool.noConfusion h

theorem List.map_nil_thm (f : α → β) : List.map f [] = [] := Eq.refl _
theorem List.map_cons_thm (f : α → β) (x : α) (xs : List α) : List.map f (x :: xs) = f x :: List.map f xs := Eq.refl _

theorem List.map_id_thm (l : List α) : List.map id l = l :=
  List.recOn l (Eq.refl _) (fun x rest ih => congrArg (x :: ·) ih)

theorem List.map_comp_thm (f : β → γ) (g : α → β) (l : List α) :
    List.map f (List.map g l) = List.map (Function.comp f g) l :=
  List.recOn l (Eq.refl _) (fun x rest ih => congrArg (f (g x) :: ·) ih)

theorem List.length_map_thm (f : α → β) (l : List α) : (l.map f).length = l.length :=
  List.recOn l (Eq.refl _) (fun _ rest ih => congrArg Nat.succ ih)

theorem List.length_filter_le_thm (p : α → Bool) (l : List α) : (l.filter p).length ≤ l.length :=
  List.recOn l (Nat.le_refl 0)
    (fun x rest ih => match h : p x with | true => Nat.succ_le_succ ih | false => Nat.le_step ih)

theorem List.length_append_thm (l1 l2 : List α) : (l1 ++ l2).length = l1.length + l2.length :=
  List.recOn l1
    (Eq.symm (Nat.zero_add_thm l2.length))
    (fun x rest ih =>
      Eq.trans (congrArg Nat.succ ih) (Eq.symm (Nat.succ_add_thm rest.length l2.length)))

theorem List.append_nil_thm (xs : List α) : xs ++ [] = xs :=
  List.recOn xs (Eq.refl _) (fun x rest ih => congrArg (x :: ·) ih)

theorem List.length_replicate_thm (n : Nat) (a : α) : (List.replicate n a).length = n :=
  Nat.recOn n (Eq.refl _) (fun n' ih => congrArg Nat.succ ih)

theorem Prod.ext_iff_thm {α β : Type} (p q : α × β) : p = q ↔ p.1 = q.1 ∧ p.2 = q.2 :=
  ⟨fun h => And.intro (congrArg Prod.fst h) (congrArg Prod.snd h),
   fun ⟨h1, h2⟩ => match p, q with | (a, b), (c, d) => Eq.subst h1 (Eq.subst h2 (Eq.refl _))⟩

theorem StringMap.size_insert_le (m : StringMap ν) (k : String) (v : ν) :
    StringMap.size (StringMap.insert m k v) ≤ Nat.succ (StringMap.size m) :=
  show List.length ((k, v) :: StringMap.remove m k) ≤ Nat.succ (List.length m) from
    Nat.succ_le_succ (List.length_filter_le_thm _ m)

theorem SelfSimilarRelationalGraph.canonicalPairKey_cases (a b : String) :
    (SelfSimilarRelationalGraph.canonicalPairKey a b = ⟨a, b⟩ ∧ a < b) ∨
    (SelfSimilarRelationalGraph.canonicalPairKey a b = ⟨b, a⟩ ∧ ¬(a < b)) :=
  if h : a < b then
    Or.inl (And.intro
      (show (if a < b then PairKey.mk a b else PairKey.mk b a) = PairKey.mk a b from
        dite (a < b)
          (fun ht => Eq.mpr (congrArg (fun p => (if p then PairKey.mk a b else PairKey.mk b a) = PairKey.mk a b)
            (propext ⟨fun _ => True.intro, fun _ => ht⟩)) (Eq.refl _))
          (fun hf => absurd h hf))
      h)
  else
    Or.inr (And.intro
      (show (if a < b then PairKey.mk a b else PairKey.mk b a) = PairKey.mk b a from
        dite (a < b)
          (fun ht => absurd ht h)
          (fun hf => Eq.mpr (congrArg (fun p => (if p then PairKey.mk a b else PairKey.mk b a) = PairKey.mk b a)
            (propext ⟨fun ht => absurd ht hf, fun f => False.elim f⟩)) (Eq.refl _)))
      h)
