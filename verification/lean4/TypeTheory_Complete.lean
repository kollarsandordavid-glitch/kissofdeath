import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Basic
import Mathlib.Logic.Basic
import Mathlib.Tactic

namespace TypeTheoryVerification

inductive Universe : Type where
  | UZero : Universe
  | USucc : Universe → Universe
  | UMax : Universe → Universe → Universe
deriving DecidableEq

def Universe.level : Universe → Nat
  | UZero => 0
  | USucc u => u.level + 1
  | UMax u1 u2 => max u1.level u2.level

theorem Universe.level_succ (u : Universe) :
  (USucc u).level = u.level + 1 := by
  rfl

theorem Universe.level_max (u1 u2 : Universe) :
  (UMax u1 u2).level = max u1.level u2.level := by
  rfl

inductive TypeExpr : Type where
  | TVar : Nat → TypeExpr
  | TPi : String → TypeExpr → TypeExpr → TypeExpr
  | TSigma : String → TypeExpr → TypeExpr → TypeExpr
  | TId : TypeExpr → TypeExpr → TypeExpr → TypeExpr
  | TUniverse : Universe → TypeExpr
  | TNat : TypeExpr
  | TBool : TypeExpr
deriving DecidableEq

def TypeExpr.freeVars : TypeExpr → List Nat
  | TVar n => [n]
  | TPi _ t1 t2 => t1.freeVars ++ t2.freeVars
  | TSigma _ t1 t2 => t1.freeVars ++ t2.freeVars
  | TId t1 t2 t3 => t1.freeVars ++ t2.freeVars ++ t3.freeVars
  | TUniverse _ => []
  | TNat => []
  | TBool => []

inductive TermExpr : Type where
  | Var : Nat → TermExpr
  | Lambda : String → TypeExpr → TermExpr → TermExpr
  | App : TermExpr → TermExpr → TermExpr
  | Pair : TermExpr → TermExpr → TermExpr
  | Proj1 : TermExpr → TermExpr
  | Proj2 : TermExpr → TermExpr
  | Refl : TermExpr → TermExpr
  | J : TermExpr → TermExpr → TermExpr → TermExpr → TermExpr → TermExpr
  | Zero : TermExpr
  | Succ : TermExpr → TermExpr
  | NatRec : TermExpr → TermExpr → TermExpr → TermExpr
  | True : TermExpr
  | False : TermExpr
  | BoolRec : TermExpr → TermExpr → TermExpr → TermExpr
deriving DecidableEq

def TermExpr.freeVars : TermExpr → List Nat
  | Var n => [n]
  | Lambda _ _ body => body.freeVars
  | App f arg => f.freeVars ++ arg.freeVars
  | Pair fst snd => fst.freeVars ++ snd.freeVars
  | Proj1 p => p.freeVars
  | Proj2 p => p.freeVars
  | Refl t => t.freeVars
  | J a c d e f => a.freeVars ++ c.freeVars ++ d.freeVars ++ e.freeVars ++ f.freeVars
  | Zero => []
  | Succ n => n.freeVars
  | NatRec n base step => n.freeVars ++ base.freeVars ++ step.freeVars
  | True => []
  | False => []
  | BoolRec b tcase fcase => b.freeVars ++ tcase.freeVars ++ fcase.freeVars

def Context := List (String × TypeExpr)

def Context.lookup (ctx : Context) (name : String) : Option TypeExpr :=
  ctx.find? (fun p => p.1 == name) |>.map (·.2)

def Context.add (ctx : Context) (name : String) (type : TypeExpr) : Context :=
  (name, type) :: ctx

inductive HasType : Context → TermExpr → TypeExpr → Prop where
  | TVar : ∀ ctx name type, ctx.lookup name = some type → 
      HasType ctx (TermExpr.Var 0) type
  | TLambda : ∀ ctx name argType bodyType body,
      HasType (ctx.add name argType) body bodyType →
      HasType ctx (TermExpr.Lambda name argType body) 
        (TypeExpr.TPi name argType bodyType)
  | TApp : ∀ ctx f arg argType resultType name,
      HasType ctx f (TypeExpr.TPi name argType resultType) →
      HasType ctx arg argType →
      HasType ctx (TermExpr.App f arg) resultType
  | TPair : ∀ ctx fst snd fstType sndType name,
      HasType ctx fst fstType →
      HasType ctx snd sndType →
      HasType ctx (TermExpr.Pair fst snd) 
        (TypeExpr.TSigma name fstType sndType)
  | TProj1 : ∀ ctx p name fstType sndType,
      HasType ctx p (TypeExpr.TSigma name fstType sndType) →
      HasType ctx (TermExpr.Proj1 p) fstType
  | TProj2 : ∀ ctx p name fstType sndType,
      HasType ctx p (TypeExpr.TSigma name fstType sndType) →
      HasType ctx (TermExpr.Proj2 p) sndType
  | TRefl : ∀ ctx term type,
      HasType ctx term type →
      HasType ctx (TermExpr.Refl term) (TypeExpr.TId type term term)
  | TZero : ∀ ctx,
      HasType ctx TermExpr.Zero TypeExpr.TNat
  | TSucc : ∀ ctx n,
      HasType ctx n TypeExpr.TNat →
      HasType ctx (TermExpr.Succ n) TypeExpr.TNat
  | TNatRec : ∀ ctx n base step motive,
      HasType ctx n TypeExpr.TNat →
      HasType ctx base motive →
      HasType ctx step (TypeExpr.TPi "n" TypeExpr.TNat 
        (TypeExpr.TPi "ih" motive motive)) →
      HasType ctx (TermExpr.NatRec n base step) motive
  | TTrue : ∀ ctx,
      HasType ctx TermExpr.True TypeExpr.TBool
  | TFalse : ∀ ctx,
      HasType ctx TermExpr.False TypeExpr.TBool
  | TBoolRec : ∀ ctx b tcase fcase motive,
      HasType ctx b TypeExpr.TBool →
      HasType ctx tcase motive →
      HasType ctx fcase motive →
      HasType ctx (TermExpr.BoolRec b tcase fcase) motive

theorem type_preservation_lambda (ctx : Context) (name : String) 
  (argType bodyType : TypeExpr) (body : TermExpr) :
  HasType (ctx.add name argType) body bodyType →
  HasType ctx (TermExpr.Lambda name argType body) 
    (TypeExpr.TPi name argType bodyType) := by
  exact HasType.TLambda ctx name argType bodyType body

theorem type_preservation_app (ctx : Context) (f arg : TermExpr) 
  (argType resultType : TypeExpr) (name : String) :
  HasType ctx f (TypeExpr.TPi name argType resultType) →
  HasType ctx arg argType →
  HasType ctx (TermExpr.App f arg) resultType := by
  exact HasType.TApp ctx f arg argType resultType name

theorem type_preservation_pair (ctx : Context) (fst snd : TermExpr) 
  (fstType sndType : TypeExpr) (name : String) :
  HasType ctx fst fstType →
  HasType ctx snd sndType →
  HasType ctx (TermExpr.Pair fst snd) 
    (TypeExpr.TSigma name fstType sndType) := by
  exact HasType.TPair ctx fst snd fstType sndType name

inductive Reduces : TermExpr → TermExpr → Prop where
  | RBeta : ∀ name argType body arg,
      Reduces (TermExpr.App (TermExpr.Lambda name argType body) arg) body
  | RProj1 : ∀ fst snd,
      Reduces (TermExpr.Proj1 (TermExpr.Pair fst snd)) fst
  | RProj2 : ∀ fst snd,
      Reduces (TermExpr.Proj2 (TermExpr.Pair fst snd)) snd
  | RNatRecZero : ∀ base step,
      Reduces (TermExpr.NatRec TermExpr.Zero base step) base
  | RNatRecSucc : ∀ n base step,
      Reduces (TermExpr.NatRec (TermExpr.Succ n) base step)
        (TermExpr.App (TermExpr.App step n) (TermExpr.NatRec n base step))
  | RBoolRecTrue : ∀ tcase fcase,
      Reduces (TermExpr.BoolRec TermExpr.True tcase fcase) tcase
  | RBoolRecFalse : ∀ tcase fcase,
      Reduces (TermExpr.BoolRec TermExpr.False tcase fcase) fcase
  | RApp1 : ∀ f f' arg,
      Reduces f f' →
      Reduces (TermExpr.App f arg) (TermExpr.App f' arg)
  | RApp2 : ∀ f arg arg',
      Reduces arg arg' →
      Reduces (TermExpr.App f arg) (TermExpr.App f arg')

inductive ReducesStar : TermExpr → TermExpr → Prop where
  | RRefl : ∀ t, ReducesStar t t
  | RTrans : ∀ t1 t2 t3,
      Reduces t1 t2 →
      ReducesStar t2 t3 →
      ReducesStar t1 t3

theorem reduces_star_refl (t : TermExpr) : ReducesStar t t :=
  ReducesStar.RRefl t

theorem reduces_star_trans (t1 t2 t3 : TermExpr) :
  ReducesStar t1 t2 → ReducesStar t2 t3 → ReducesStar t1 t3 := by
  intro h12 h23
  induction h12 with
  | RRefl => exact h23
  | RTrans t1 t2 t2' hr hrs ih => exact ReducesStar.RTrans t1 t2 t3 hr (ih h23)

theorem subject_reduction (ctx : Context) (t t' : TermExpr) (ty : TypeExpr) :
  HasType ctx t ty → Reduces t t' → HasType ctx t' ty := by
  intro htype hreduce
  cases hreduce with
  | RBeta name argType body arg =>
    cases htype with
    | TApp _ _ _ _ resultType _ hf harg =>
      cases hf with
      | TLambda _ _ _ _ _ hbody =>
        exact hbody
  | RProj1 fst snd =>
    cases htype with
    | TProj1 _ _ _ fstType _ hp =>
      cases hp with
      | TPair _ _ _ _ _ _ hfst hsnd =>
        exact hfst
  | RProj2 fst snd =>
    cases htype with
    | TProj2 _ _ _ _ sndType hp =>
      cases hp with
      | TPair _ _ _ _ _ _ hfst hsnd =>
        exact hsnd
  | RNatRecZero base step =>
    cases htype with
    | TNatRec _ _ _ _ _ hn hbase hstep =>
      exact hbase
  | RNatRecSucc n base step =>
    cases htype with
    | TNatRec _ _ _ _ motive hn hbase hstep =>
      cases hn with
      | TSucc _ _ hn' =>
        have happ1 : HasType ctx (TermExpr.App step n) (TypeExpr.TPi "ih" motive motive) := 
          HasType.TApp ctx step n TypeExpr.TNat _ "n" hstep hn'
        have hih : HasType ctx (TermExpr.NatRec n base step) motive := 
          HasType.TNatRec ctx n base step motive hn' hbase hstep
        exact HasType.TApp ctx (TermExpr.App step n) (TermExpr.NatRec n base step) motive motive "ih" happ1 hih
  | RBoolRecTrue tcase fcase =>
    cases htype with
    | TBoolRec _ _ _ _ motive hb htcase hfcase =>
      exact htcase
  | RBoolRecFalse tcase fcase =>
    cases htype with
    | TBoolRec _ _ _ _ motive hb htcase hfcase =>
      exact hfcase
  | RApp1 f f' arg hredf =>
    cases htype with
    | TApp _ _ _ argType resultType name hf harg =>
      have hf' : HasType ctx f' (TypeExpr.TPi name argType resultType) := 
        subject_reduction ctx f f' (TypeExpr.TPi name argType resultType) hf hredf
      exact HasType.TApp ctx f' arg argType resultType name hf' harg
  | RApp2 f arg arg' hreda =>
    cases htype with
    | TApp _ _ _ argType resultType name hf harg =>
      have harg' : HasType ctx arg' argType := 
        subject_reduction ctx arg arg' argType harg hreda
      exact HasType.TApp ctx f arg' argType resultType name hf harg'

def normalize : TermExpr → TermExpr
  | TermExpr.App (TermExpr.Lambda _ _ body) arg => normalize body
  | TermExpr.Proj1 (TermExpr.Pair fst _) => normalize fst
  | TermExpr.Proj2 (TermExpr.Pair _ snd) => normalize snd
  | TermExpr.NatRec TermExpr.Zero base _ => normalize base
  | TermExpr.BoolRec TermExpr.True tcase _ => normalize tcase
  | TermExpr.BoolRec TermExpr.False _ fcase => normalize fcase
  | t => t

theorem normalize_reduces_star (t : TermExpr) :
  ReducesStar t (normalize t) := by
  induction t with
  | App f arg ihf iharg =>
      cases f with
      | Var n => exact ReducesStar.RRefl _
      | Lambda name argType body =>
        unfold normalize
        have hred : Reduces (TermExpr.App (TermExpr.Lambda name argType body) arg) body := 
          Reduces.RBeta name argType body arg
        exact ReducesStar.RTrans _ body (normalize body) hred (normalize_reduces_star body)
      | App f1 f2 => exact ReducesStar.RRefl _
      | Pair fst snd => exact ReducesStar.RRefl _
      | Proj1 p => exact ReducesStar.RRefl _
      | Proj2 p => exact ReducesStar.RRefl _
      | Refl t => exact ReducesStar.RRefl _
      | J a c d e f => exact ReducesStar.RRefl _
      | Zero => exact ReducesStar.RRefl _
      | Succ n => exact ReducesStar.RRefl _
      | NatRec n base step => exact ReducesStar.RRefl _
      | True => exact ReducesStar.RRefl _
      | False => exact ReducesStar.RRefl _
      | BoolRec b tcase fcase => exact ReducesStar.RRefl _
  | Proj1 p =>
      cases p with
      | Pair fst snd =>
        unfold normalize
        have hred : Reduces (TermExpr.Proj1 (TermExpr.Pair fst snd)) fst := Reduces.RProj1 fst snd
        exact ReducesStar.RTrans _ fst (normalize fst) hred (normalize_reduces_star fst)
      | _ => exact ReducesStar.RRefl _
  | Proj2 p =>
      cases p with
      | Pair fst snd =>
        unfold normalize
        have hred : Reduces (TermExpr.Proj2 (TermExpr.Pair fst snd)) snd := Reduces.RProj2 fst snd
        exact ReducesStar.RTrans _ snd (normalize snd) hred (normalize_reduces_star snd)
      | _ => exact ReducesStar.RRefl _
  | NatRec n base step =>
      cases n with
      | Zero =>
        unfold normalize
        have hred : Reduces (TermExpr.NatRec TermExpr.Zero base step) base := Reduces.RNatRecZero base step
        exact ReducesStar.RTrans _ base (normalize base) hred (normalize_reduces_star base)
      | _ => exact ReducesStar.RRefl _
  | BoolRec b tcase fcase =>
      cases b with
      | True =>
        unfold normalize
        have hred : Reduces (TermExpr.BoolRec TermExpr.True tcase fcase) tcase := Reduces.RBoolRecTrue tcase fcase
        exact ReducesStar.RTrans _ tcase (normalize tcase) hred (normalize_reduces_star tcase)
      | False =>
        unfold normalize
        have hred : Reduces (TermExpr.BoolRec TermExpr.False tcase fcase) fcase := Reduces.RBoolRecFalse tcase fcase
        exact ReducesStar.RTrans _ fcase (normalize fcase) hred (normalize_reduces_star fcase)
      | _ => exact ReducesStar.RRefl _
  | _ => exact ReducesStar.RRefl _

structure WellFormedContext (ctx : Context) : Prop where
  nodup : ctx.map (·.1) |>.Nodup
  typesValid : ∀ (name, type) ∈ ctx, True

theorem well_formed_context_empty : WellFormedContext [] := by
  constructor
  · exact List.nodup_nil
  · intro _ h
    cases h

theorem well_formed_context_add (ctx : Context) (name : String) (type : TypeExpr) :
  WellFormedContext ctx →
  name ∉ ctx.map (·.1) →
  WellFormedContext (ctx.add name type) := by
  intro hwf hnotin
  constructor
  · unfold Context.add
    simp
    exact ⟨hnotin, hwf.nodup⟩
  · intro pair hmem
    unfold Context.add at hmem
    simp at hmem
    cases hmem
    · trivial
    · exact hwf.typesValid pair (by assumption)

inductive NormalForm : TermExpr → Prop where
  | NVar : ∀ n, NormalForm (TermExpr.Var n)
  | NLambda : ∀ name type body, 
      NormalForm body → 
      NormalForm (TermExpr.Lambda name type body)
  | NPair : ∀ fst snd,
      NormalForm fst →
      NormalForm snd →
      NormalForm (TermExpr.Pair fst snd)
  | NZero : NormalForm TermExpr.Zero
  | NSucc : ∀ n,
      NormalForm n →
      NormalForm (TermExpr.Succ n)
  | NTrue : NormalForm TermExpr.True
  | NFalse : NormalForm TermExpr.False

theorem normal_form_not_reduces (t : TermExpr) :
  NormalForm t → ∀ t', ¬Reduces t t' := by
  intro hnf t' hreduce
  cases hnf <;> cases hreduce <;> contradiction

def isNormalForm : TermExpr → Bool
  | TermExpr.Var _ => true
  | TermExpr.Lambda _ _ body => isNormalForm body
  | TermExpr.Pair fst snd => isNormalForm fst && isNormalForm snd
  | TermExpr.Zero => true
  | TermExpr.Succ n => isNormalForm n
  | TermExpr.True => true
  | TermExpr.False => true
  | _ => false

theorem isNormalForm_sound (t : TermExpr) :
  isNormalForm t = true → NormalForm t := by
  intro h
  induction t with
  | Var n => exact NormalForm.NVar n
  | Lambda name type body ih =>
      simp [isNormalForm] at h
      exact NormalForm.NLambda name type body (ih h)
  | Pair fst snd ihfst ihsnd =>
      simp [isNormalForm] at h
      exact NormalForm.NPair fst snd (ihfst h.1) (ihsnd h.2)
  | Zero => exact NormalForm.NZero
  | Succ n ih =>
      simp [isNormalForm] at h
      exact NormalForm.NSucc n (ih h)
  | True => exact NormalForm.NTrue
  | False => exact NormalForm.NFalse
  | _ => simp [isNormalForm] at h

end TypeTheoryVerification
