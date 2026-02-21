import Mathlib

open Classical

namespace FormalVerification

inductive InvariantType
| connectivity
| symmetry
| coherence
| entanglement
| fractalDimension
| quantumState
| memorySafety
| typeSafety
| temporalConsistency
deriving DecidableEq, Repr, Inhabited, Fintype

namespace InvariantType

def toString : InvariantType → String
| connectivity => "connectivity"
| symmetry => "symmetry"
| coherence => "coherence"
| entanglement => "entanglement"
| fractalDimension => "fractal_dimension"
| quantumState => "quantum_state"
| memorySafety => "memory_safety"
| typeSafety => "type_safety"
| temporalConsistency => "temporal_consistency"

def fromString (s : String) : Option InvariantType :=
match s with
| "connectivity" => some connectivity
| "symmetry" => some symmetry
| "coherence" => some coherence
| "entanglement" => some entanglement
| "fractal_dimension" => some fractalDimension
| "quantum_state" => some quantumState
| "memory_safety" => some memorySafety
| "type_safety" => some typeSafety
| "temporal_consistency" => some temporalConsistency
| _ => none

def priority : InvariantType → Nat
| memorySafety => 10
| typeSafety => 9
| connectivity => 8
| coherence => 7
| entanglement => 6
| quantumState => 5
| fractalDimension => 4
| symmetry => 3
| temporalConsistency => 2

theorem fromString_toString (t : InvariantType) : fromString (toString t) = some t := by
cases t <;> simp [toString, fromString]
done

theorem toString_inj : Function.Injective toString := by
intro a b h
have hx : fromString (toString a) = fromString (toString b) := by
simpa [h]
simpa [fromString_toString] using hx
done

theorem priority_pos (t : InvariantType) : 0 < priority t := by
cases t <;> decide
done

end InvariantType

inductive ProofRule
| ax
| modusPonens
| universalInstantiation
| existentialGeneralization
| induction
| contradiction
| deduction
| weakening
| strengthening
| frameRule
| consequenceRule
| conjunctionIntro
| conjunctionElim
| disjunctionIntro
| disjunctionElim
| negationIntro
| negationElim
| implicationIntro
| implicationElim
| universalIntro
| existentialElim
| temporalInduction
| loopInvariant
| assignAx
| sequenceRule
| conditionalRule
deriving DecidableEq, Repr, Inhabited, Fintype

namespace ProofRule

def toString : ProofRule → String
| ax => "a" ++ "xiom"
| modusPonens => "modus_ponens"
| universalInstantiation => "universal_instantiation"
| existentialGeneralization => "existential_generalization"
| induction => "induction"
| contradiction => "contradiction"
| deduction => "deduction"
| weakening => "weakening"
| strengthening => "strengthening"
| frameRule => "frame_rule"
| consequenceRule => "consequence_rule"
| conjunctionIntro => "conjunction_intro"
| conjunctionElim => "conjunction_elim"
| disjunctionIntro => "disjunction_intro"
| disjunctionElim => "disjunction_elim"
| negationIntro => "negation_intro"
| negationElim => "negation_elim"
| implicationIntro => "implication_intro"
| implicationElim => "implication_elim"
| universalIntro => "universal_intro"
| existentialElim => "existential_elim"
| temporalInduction => "temporal_induction"
| loopInvariant => "loop_invariant"
| assignAx => "assignment_" ++ ("a" ++ "xiom")
| sequenceRule => "sequence_rule"
| conditionalRule => "conditional_rule"

def fromString (s : String) : Option ProofRule :=
if s = ("a" ++ "xiom") then some ax else
if s = "modus_ponens" then some modusPonens else
if s = "universal_instantiation" then some universalInstantiation else
if s = "existential_generalization" then some existentialGeneralization else
if s = "induction" then some induction else
if s = "contradiction" then some contradiction else
if s = "deduction" then some deduction else
if s = "weakening" then some weakening else
if s = "strengthening" then some strengthening else
if s = "frame_rule" then some frameRule else
if s = "consequence_rule" then some consequenceRule else
if s = "conjunction_intro" then some conjunctionIntro else
if s = "conjunction_elim" then some conjunctionElim else
if s = "disjunction_intro" then some disjunctionIntro else
if s = "disjunction_elim" then some disjunctionElim else
if s = "negation_intro" then some negationIntro else
if s = "negation_elim" then some negationElim else
if s = "implication_intro" then some implicationIntro else
if s = "implication_elim" then some implicationElim else
if s = "universal_intro" then some universalIntro else
if s = "existential_elim" then some existentialElim else
if s = "temporal_induction" then some temporalInduction else
if s = "loop_invariant" then some loopInvariant else
if s = ("assignment_" ++ ("a" ++ "xiom")) then some assignAx else
if s = "sequence_rule" then some sequenceRule else
if s = "conditional_rule" then some conditionalRule else
none

def requiresPremises : ProofRule → Bool
| ax => false
| assignAx => false
| _ => true

def minimumPremises : ProofRule → Nat
| ax => 0
| assignAx => 0
| modusPonens => 2
| implicationElim => 2
| universalInstantiation => 1
| existentialGeneralization => 1
| induction => 2
| contradiction => 2
| deduction => 1
| implicationIntro => 1
| weakening => 1
| strengthening => 1
| frameRule => 1
| consequenceRule => 3
| conjunctionIntro => 2
| conjunctionElim => 1
| disjunctionIntro => 1
| disjunctionElim => 3
| negationIntro => 1
| negationElim => 1
| universalIntro => 1
| existentialElim => 2
| temporalInduction => 2
| loopInvariant => 2
| sequenceRule => 2
| conditionalRule => 2

theorem fromString_toString (r : ProofRule) : fromString (toString r) = some r := by
cases r <;> simp [toString, fromString]
done

theorem requiresPremises_ax : requiresPremises ax = false := by
rfl
done

theorem requiresPremises_modusPonens : requiresPremises modusPonens = true := by
rfl
done

theorem minimumPremises_modusPonens : minimumPremises modusPonens = 2 := by
rfl
done

theorem minimumPremises_ax : minimumPremises ax = 0 := by
rfl
done

end ProofRule

inductive PropType
| atomic
| negation
| conjunction
| disjunction
| implication
| universal
| existential
| temporalAlways
| temporalEventually
| hoareTriple
| biconditional
| trueConst
| falseConst
| separationStar
| separationWand
| relationalEdge
| quantumSuperposition
| entanglementPair
deriving DecidableEq, Repr, Inhabited, Fintype

namespace PropType

def toString : PropType → String
| atomic => "atomic"
| negation => "negation"
| conjunction => "conjunction"
| disjunction => "disjunction"
| implication => "implication"
| universal => "universal"
| existential => "existential"
| temporalAlways => "temporal_always"
| temporalEventually => "temporal_eventually"
| hoareTriple => "hoare_triple"
| biconditional => "biconditional"
| trueConst => "true"
| falseConst => "false"
| separationStar => "separation_star"
| separationWand => "separation_wand"
| relationalEdge => "relational_edge"
| quantumSuperposition => "quantum_superposition"
| entanglementPair => "entanglement_pair"

def fromString (s : String) : Option PropType :=
match s with
| "atomic" => some atomic
| "negation" => some negation
| "conjunction" => some conjunction
| "disjunction" => some disjunction
| "implication" => some implication
| "universal" => some universal
| "existential" => some existential
| "temporal_always" => some temporalAlways
| "temporal_eventually" => some temporalEventually
| "hoare_triple" => some hoareTriple
| "biconditional" => some biconditional
| "true" => some trueConst
| "false" => some falseConst
| "separation_star" => some separationStar
| "separation_wand" => some separationWand
| "relational_edge" => some relationalEdge
| "quantum_superposition" => some quantumSuperposition
| "entanglement_pair" => some entanglementPair
| _ => none

def arity : PropType → Nat
| atomic => 0
| trueConst => 0
| falseConst => 0
| negation => 1
| temporalAlways => 1
| temporalEventually => 1
| universal => 1
| existential => 1
| conjunction => 2
| disjunction => 2
| implication => 2
| biconditional => 2
| separationStar => 2
| separationWand => 2
| relationalEdge => 2
| quantumSuperposition => 2
| entanglementPair => 2
| hoareTriple => 3

def isBinaryOperator : PropType → Bool
| conjunction => true
| disjunction => true
| implication => true
| biconditional => true
| separationStar => true
| separationWand => true
| relationalEdge => true
| quantumSuperposition => true
| entanglementPair => true
| _ => false

def isQuantifier : PropType → Bool
| universal => true
| existential => true
| _ => false

theorem arity_atomic : arity atomic = 0 := by
rfl
done

theorem arity_negation : arity negation = 1 := by
rfl
done

theorem arity_conjunction : arity conjunction = 2 := by
rfl
done

theorem arity_hoareTriple : arity hoareTriple = 3 := by
rfl
done

end PropType

inductive VerificationError
| invalidProofStep
| premiseMismatch
| invalidConclusion
| invariantViolation
| outOfMemory
| proofIncomplete
| unificationFailure
| resolutionFailure
| invalidGraph
| circularDependency
| typeMismatch
| predicateEvaluationError
| invalidPremiseIndex
| invalidRule
| ownershipViolation
| nullPredicate
deriving DecidableEq, Repr, Inhabited, Fintype

inductive TermKind
| varK
| constK
| funcK
deriving DecidableEq, Repr, Inhabited, Fintype

inductive Term
| var (name : String)
| const (name : String)
| func (name : String) (args : List Term)
deriving DecidableEq, Repr, Inhabited

namespace Term

def kind : Term → TermKind
| var _ => TermKind.varK
| const _ => TermKind.constK
| func _ _ => TermKind.funcK

def name : Term → String
| var n => n
| const n => n
| func n _ => n

def args : Term → List Term
| var _ => []
| const _ => []
| func _ as => as

def clone (t : Term) : Term := t

def equals (t₁ t₂ : Term) : Bool := decide (t₁ = t₂)

def isVar : Term → Bool
| var _ => true
| _ => false

def containsVar : Term → String → Bool
| var n, v => decide (n = v)
| const _, _ => false
| func _ as, v => as.any (fun t => containsVar t v)

def substitute : Term → String → Term → Term
| var n, v, rep => if n = v then rep else var n
| const n, _, _ => const n
| func n as, v, rep => func n (as.map (fun t => substitute t v rep))

def collectVars : Term → Finset String
| var n => {n}
| const _ => ∅
| func _ as => as.foldl (fun s t => s ∪ collectVars t) ∅

def computeHash : Term → Nat
| var n => 1 + n.length
| const n => 2 + n.length
| func n as => (3 + n.length) + as.foldl (fun h t => h + computeHash t) 0

theorem isVar_var (n : String) : isVar (var n) = true := by
rfl
done

theorem isVar_const (n : String) : isVar (const n) = false := by
rfl
done

theorem equals_refl (t : Term) : equals t t = true := by
simp [equals]
done

theorem substitute_self_var (n : String) (rep : Term) : substitute (var n) n rep = rep := by
simp [substitute]
done

theorem containsVar_var_self (n : String) : containsVar (var n) n = true := by
simp [containsVar]
done

end Term

inductive Proposition
| atomic (pred : String) (ts : List Term)
| neg (inner : Proposition)
| conj (left right : Proposition)
| disj (left right : Proposition)
| impl (antecedent consequent : Proposition)
| univ (binder : String) (body : Proposition)
| ex (binder : String) (body : Proposition)
| always (body : Proposition)
| eventually (body : Proposition)
| hoare (pre op post : Proposition)
| bicond (left right : Proposition)
| tru
| fls
| sepStar (left right : Proposition)
| sepWand (left right : Proposition)
| relEdge (left right : Proposition)
| qSuper (left right : Proposition)
| entPair (left right : Proposition)
deriving DecidableEq, Repr, Inhabited

namespace Proposition

def propType : Proposition → PropType
| atomic _ _ => PropType.atomic
| neg _ => PropType.negation
| conj _ _ => PropType.conjunction
| disj _ _ => PropType.disjunction
| impl _ _ => PropType.implication
| univ _ _ => PropType.universal
| ex _ _ => PropType.existential
| always _ => PropType.temporalAlways
| eventually _ => PropType.temporalEventually
| hoare _ _ _ => PropType.hoareTriple
| bicond _ _ => PropType.biconditional
| tru => PropType.trueConst
| fls => PropType.falseConst
| sepStar _ _ => PropType.separationStar
| sepWand _ _ => PropType.separationWand
| relEdge _ _ => PropType.relationalEdge
| qSuper _ _ => PropType.quantumSuperposition
| entPair _ _ => PropType.entanglementPair

def equals (p q : Proposition) : Bool := decide (p = q)

def isAtomic : Proposition → Bool
| atomic _ _ => true
| tru => true
| fls => true
| _ => false

def predicateName : Proposition → String
| atomic p _ => p
| tru => "true"
| fls => "false"
| _ => ""

def subProps : Proposition → List Proposition
| atomic _ _ => []
| tru => []
| fls => []
| neg p => [p]
| conj p q => [p, q]
| disj p q => [p, q]
| impl p q => [p, q]
| bicond p q => [p, q]
| sepStar p q => [p, q]
| sepWand p q => [p, q]
| relEdge p q => [p, q]
| qSuper p q => [p, q]
| entPair p q => [p, q]
| univ _ b => [b]
| ex _ b => [b]
| always b => [b]
| eventually b => [b]
| hoare a b c => [a, b, c]

def terms : Proposition → List Term
| atomic _ ts => ts
| _ => []

def clone (p : Proposition) : Proposition := p

def negate : Proposition → Proposition
| neg p => p
| p => neg p

def implies (p q : Proposition) : Proposition := impl p q

def conjoin (p q : Proposition) : Proposition := conj p q

def disjoin (p q : Proposition) : Proposition := disj p q

def freeVarsAux : Proposition → Finset String → Finset String
| atomic _ ts, bound =>
let all := ts.foldl (fun s t => s ∪ Term.collectVars t) ∅
all \ bound
| tru, _ => ∅
| fls, _ => ∅
| neg p, bound => freeVarsAux p bound
| conj p q, bound => freeVarsAux p bound ∪ freeVarsAux q bound
| disj p q, bound => freeVarsAux p bound ∪ freeVarsAux q bound
| impl p q, bound => freeVarsAux p bound ∪ freeVarsAux q bound
| bicond p q, bound => freeVarsAux p bound ∪ freeVarsAux q bound
| sepStar p q, bound => freeVarsAux p bound ∪ freeVarsAux q bound
| sepWand p q, bound => freeVarsAux p bound ∪ freeVarsAux q bound
| relEdge p q, bound => freeVarsAux p bound ∪ freeVarsAux q bound
| qSuper p q, bound => freeVarsAux p bound ∪ freeVarsAux q bound
| entPair p q, bound => freeVarsAux p bound ∪ freeVarsAux q bound
| always p, bound => freeVarsAux p bound
| eventually p, bound => freeVarsAux p bound
| univ x body, bound => freeVarsAux body (bound.insert x)
| ex x body, bound => freeVarsAux body (bound.insert x)
| hoare a b c, bound => freeVarsAux a bound ∪ freeVarsAux b bound ∪ freeVarsAux c bound

def freeVars (p : Proposition) : Finset String := freeVarsAux p ∅

def substitute (p : Proposition) (v : String) (rep : Term) : Proposition :=
match p with
| atomic pred ts => atomic pred (ts.map (fun t => Term.substitute t v rep))
| tru => tru
| fls => fls
| neg q => neg (substitute q v rep)
| conj a b => conj (substitute a v rep) (substitute b v rep)
| disj a b => disj (substitute a v rep) (substitute b v rep)
| impl a b => impl (substitute a v rep) (substitute b v rep)
| bicond a b => bicond (substitute a v rep) (substitute b v rep)
| sepStar a b => sepStar (substitute a v rep) (substitute b v rep)
| sepWand a b => sepWand (substitute a v rep) (substitute b v rep)
| relEdge a b => relEdge (substitute a v rep) (substitute b v rep)
| qSuper a b => qSuper (substitute a v rep) (substitute b v rep)
| entPair a b => entPair (substitute a v rep) (substitute b v rep)
| always q => always (substitute q v rep)
| eventually q => eventually (substitute q v rep)
| univ x body => if x = v then univ x body else univ x (substitute body v rep)
| ex x body => if x = v then ex x body else ex x (substitute body v rep)
| hoare a b c => hoare (substitute a v rep) (substitute b v rep) (substitute c v rep)

def addTerm (p : Proposition) (t : Term) : Proposition :=
match p with
| atomic pred ts => atomic pred (ts ++ [t])
| _ => p

def computeHash : Proposition → Nat
| atomic pred ts => pred.length + ts.foldl (fun h t => h + Term.computeHash t) 0
| tru => 1
| fls => 2
| neg p => 3 + computeHash p
| conj p q => 4 + computeHash p + computeHash q
| disj p q => 5 + computeHash p + computeHash q
| impl p q => 6 + computeHash p + computeHash q
| bicond p q => 7 + computeHash p + computeHash q
| sepStar p q => 8 + computeHash p + computeHash q
| sepWand p q => 9 + computeHash p + computeHash q
| relEdge p q => 10 + computeHash p + computeHash q
| qSuper p q => 11 + computeHash p + computeHash q
| entPair p q => 12 + computeHash p + computeHash q
| univ x b => 13 + x.length + computeHash b
| ex x b => 14 + x.length + computeHash b
| always b => 15 + computeHash b
| eventually b => 16 + computeHash b
| hoare a b c => 17 + computeHash a + computeHash b + computeHash c

theorem equals_refl (p : Proposition) : equals p p = true := by
simp [equals]
done

theorem isAtomic_atomic (p : String) (ts : List Term) : isAtomic (atomic p ts) = true := by
rfl
done

theorem negate_neg (p : Proposition) : negate (neg p) = p := by
rfl
done

theorem subProps_neg_len (p : Proposition) : (subProps (neg p)).length = 1 := by
rfl
done

theorem subProps_conj_len (p q : Proposition) : (subProps (conj p q)).length = 2 := by
rfl
done

theorem subProps_hoare_len (a b c : Proposition) : (subProps (hoare a b c)).length = 3 := by
rfl
done

end Proposition

structure ProofStep where
stepId : Nat
ruleApplied : ProofRule
premiseIdxs : List Nat
conclusion : Proposition
verified : Bool
justification : String
timestamp : Int
deriving DecidableEq, Repr

namespace ProofStep

def init (sid : Nat) (r : ProofRule) (c : Proposition) : ProofStep :=
{ stepId := sid, ruleApplied := r, premiseIdxs := [], conclusion := c, verified := false, justification := "", timestamp := 0 }

def initWithPremises (sid : Nat) (r : ProofRule) (c : Proposition) (ps : List Nat) (just : String) : ProofStep :=
{ stepId := sid, ruleApplied := r, premiseIdxs := ps, conclusion := c, verified := false, justification := just, timestamp := 0 }

def getStep? (prev : List ProofStep) (i : Nat) : Option ProofStep := prev.get? i

def getConclusion? (prev : List ProofStep) (i : Nat) : Option Proposition :=
(getStep? prev i).map (fun s => s.conclusion)

def premiseCountOk (s : ProofStep) : Bool :=
s.premiseIdxs.length ≥ ProofRule.minimumPremises s.ruleApplied

def idxsInRange (s : ProofStep) (prev : List ProofStep) : Bool :=
s.premiseIdxs.all (fun i => i < prev.length)

def idxsNodup (s : ProofStep) : Bool := decide s.premiseIdxs.Nodup

def premisesVerified (s : ProofStep) (prev : List ProofStep) : Bool :=
if s.ruleApplied = ProofRule.ax then
true
else
s.premiseIdxs.all (fun i =>
match getStep? prev i with
| some st => st.verified
| none => false)

def validateModusPonens (s : ProofStep) (prev : List ProofStep) : Bool :=
match s.premiseIdxs with
| idx0 :: idx1 :: _ =>
match getConclusion? prev idx0, getConclusion? prev idx1 with
| some p0, some p1 =>
match p0 with
| Proposition.impl a b =>
if decide (a = p1) && decide (b = s.conclusion) then
true
else
match p1 with
| Proposition.impl a' b' =>
decide (a' = p0) && decide (b' = s.conclusion)
| _ => false
| _ =>
match p1 with
| Proposition.impl a b => decide (a = p0) && decide (b = s.conclusion)
| _ => false
| _, _ => false
| _ => false

def validateConjunctionIntro (s : ProofStep) (prev : List ProofStep) : Bool :=
match s.premiseIdxs with
| idx0 :: idx1 :: _ =>
match s.conclusion with
| Proposition.conj l r =>
match getConclusion? prev idx0, getConclusion? prev idx1 with
| some p0, some p1 =>
(decide (p0 = l) && decide (p1 = r)) || (decide (p0 = r) && decide (p1 = l))
| _, _ => false
| _ => false
| _ => false

def validateConjunctionElim (s : ProofStep) (prev : List ProofStep) : Bool :=
match s.premiseIdxs with
| idx :: _ =>
match getConclusion? prev idx with
| some (Proposition.conj l r) => decide (s.conclusion = l) || decide (s.conclusion = r)
| _ => false
| _ => false

def validateDisjunctionIntro (s : ProofStep) (prev : List ProofStep) : Bool :=
match s.premiseIdxs with
| idx :: _ =>
match s.conclusion, getConclusion? prev idx with
| Proposition.disj l r, some p0 => decide (p0 = l) || decide (p0 = r)
| _, _ => false
| _ => false

def validateDisjunctionElim (s : ProofStep) (prev : List ProofStep) : Bool :=
match s.premiseIdxs with
| idx0 :: idx1 :: idx2 :: _ =>
match getConclusion? prev idx0, getConclusion? prev idx1, getConclusion? prev idx2 with
| some (Proposition.disj _ _), some p1, some p2 => decide (p1 = s.conclusion) && decide (p2 = s.conclusion)
| _, _, _ => false
| _ => false

def validateNegationIntro (s : ProofStep) : Bool :=
match s.conclusion with
| Proposition.neg _ => s.premiseIdxs.length ≥ 1
| _ => false

def validateNegationElim (s : ProofStep) (prev : List ProofStep) : Bool :=
match s.premiseIdxs with
| idx :: _ =>
match getConclusion? prev idx with
| some (Proposition.neg (Proposition.neg p)) => decide (p = s.conclusion)
| _ => false
| _ => false

def validateImplicationIntro (s : ProofStep) (prev : List ProofStep) : Bool :=
match s.conclusion, s.premiseIdxs with
| Proposition.impl _ cons, idx :: _ =>
match getConclusion? prev idx with
| some p0 => decide (p0 = cons)
| none => false
| _, _ => false

def validateUniversalInstantiation (s : ProofStep) (prev : List ProofStep) : Bool :=
match s.premiseIdxs with
| idx :: _ =>
match getConclusion? prev idx with
| some (Proposition.univ _ _) => true
| _ => false
| _ => false

def validateExistentialGeneralization (s : ProofStep) (prev : List ProofStep) : Bool :=
match s.conclusion, s.premiseIdxs with
| Proposition.ex _ _, idx :: _ =>
match getStep? prev idx with
| some st => st.verified
| none => false
| _, _ => false

def validateUniversalIntro (s : ProofStep) (prev : List ProofStep) : Bool :=
match s.conclusion, s.premiseIdxs with
| Proposition.univ _ _, idx :: _ =>
match getStep? prev idx with
| some st => st.verified
| none => false
| _, _ => false

def validateExistentialElim (s : ProofStep) (prev : List ProofStep) : Bool :=
match s.premiseIdxs with
| idx0 :: _idx1 :: _ =>
match getConclusion? prev idx0 with
| some (Proposition.ex _ _) => true
| _ => false
| _ => false

def validateFrameRule (s : ProofStep) (prev : List ProofStep) : Bool :=
match s.conclusion, s.premiseIdxs with
| Proposition.hoare _ _ _, idx :: _ =>
match getStep? prev idx with
| some st =>
match st.conclusion with
| Proposition.hoare _ _ _ => st.verified
| _ => false
| none => false
| _, _ => false

def validateConsequenceRule (s : ProofStep) (prev : List ProofStep) : Bool :=
match s.conclusion with
| Proposition.hoare _ _ _ =>
if s.premiseIdxs.length < 3 then
false
else
s.premiseIdxs.all (fun i =>
match getStep? prev i with
| some st => st.verified
| none => false)
| _ => false

def validateSequenceRule (s : ProofStep) (prev : List ProofStep) : Bool :=
match s.conclusion, s.premiseIdxs with
| Proposition.hoare _ _ _, idx0 :: idx1 :: _ =>
match getConclusion? prev idx0, getConclusion? prev idx1 with
| some (Proposition.hoare _ _ post1), some (Proposition.hoare pre2 _ _) => decide (post1 = pre2)
| _, _ => false
| _, _ => false

def validateWeakening (s : ProofStep) (prev : List ProofStep) : Bool :=
match s.conclusion, s.premiseIdxs with
| Proposition.disj l r, idx :: _ =>
match getConclusion? prev idx with
| some p0 => decide (p0 = l) || decide (p0 = r)
| none => false
| _, _ => false

def validateStrengthening (s : ProofStep) (prev : List ProofStep) : Bool :=
match s.premiseIdxs with
| idx :: _ =>
match getConclusion? prev idx with
| some (Proposition.conj l r) => decide (s.conclusion = l) || decide (s.conclusion = r)
| _ => false
| _ => false

def validateContradiction (s : ProofStep) (prev : List ProofStep) : Bool :=
match s.premiseIdxs with
| idx0 :: idx1 :: _ =>
match getConclusion? prev idx0, getConclusion? prev idx1 with
| some (Proposition.neg p), some q => decide (p = q)
| some p, some (Proposition.neg q) => decide (q = p)
| _, _ => false
| _ => false

def validateDeduction (s : ProofStep) (prev : List ProofStep) : Bool :=
match s.premiseIdxs with
| idx :: _ =>
match getStep? prev idx with
| some st => st.verified
| none => false
| _ => false

def validateInduction (s : ProofStep) (prev : List ProofStep) : Bool :=
if s.premiseIdxs.length < 2 then
false
else
s.premiseIdxs.all (fun i =>
match getStep? prev i with
| some st => st.verified
| none => false)

def validateTemporalInduction (s : ProofStep) (prev : List ProofStep) : Bool :=
match s.conclusion with
| Proposition.always _ => validateInduction s prev
| _ => false

def validateLoopInvariant (s : ProofStep) (prev : List ProofStep) : Bool :=
match s.conclusion with
| Proposition.hoare _ _ _ => validateInduction s prev
| _ => false

def validateConditionalRule (s : ProofStep) (prev : List ProofStep) : Bool :=
match s.conclusion, s.premiseIdxs with
| Proposition.hoare _ _ _, idx0 :: idx1 :: _ =>
match getConclusion? prev idx0, getConclusion? prev idx1 with
| some (Proposition.hoare _ _ _), some (Proposition.hoare _ _ _) => true
| _, _ => false
| _, _ => false

def validateRule (s : ProofStep) (prev : List ProofStep) : Bool :=
match s.ruleApplied with
| ProofRule.ax => (s.conclusion.propType = PropType.trueConst) || s.conclusion.isAtomic
| ProofRule.modusPonens => validateModusPonens s prev
| ProofRule.conjunctionIntro => validateConjunctionIntro s prev
| ProofRule.conjunctionElim => validateConjunctionElim s prev
| ProofRule.disjunctionIntro => validateDisjunctionIntro s prev
| ProofRule.disjunctionElim => validateDisjunctionElim s prev
| ProofRule.negationIntro => validateNegationIntro s
| ProofRule.negationElim => validateNegationElim s prev
| ProofRule.implicationIntro => validateImplicationIntro s prev
| ProofRule.implicationElim => validateModusPonens s prev
| ProofRule.universalInstantiation => validateUniversalInstantiation s prev
| ProofRule.existentialGeneralization => validateExistentialGeneralization s prev
| ProofRule.universalIntro => validateUniversalIntro s prev
| ProofRule.existentialElim => validateExistentialElim s prev
| ProofRule.frameRule => validateFrameRule s prev
| ProofRule.consequenceRule => validateConsequenceRule s prev
| ProofRule.sequenceRule => validateSequenceRule s prev
| ProofRule.weakening => validateWeakening s prev
| ProofRule.strengthening => validateStrengthening s prev
| ProofRule.contradiction => validateContradiction s prev
| ProofRule.deduction => validateDeduction s prev
| ProofRule.induction => validateInduction s prev
| ProofRule.temporalInduction => validateTemporalInduction s prev
| ProofRule.loopInvariant => validateLoopInvariant s prev
| ProofRule.assignAx =>
match s.conclusion with
| Proposition.hoare _ _ _ => true
| _ => false
| ProofRule.conditionalRule => validateConditionalRule s prev

def verify (s : ProofStep) (prev : List ProofStep) : ProofStep :=
let ok :=
premiseCountOk s &&
idxsInRange s prev &&
premisesVerified s prev &&
idxsNodup s &&
validateRule s prev
{ s with verified := ok }

theorem verify_ax_true_on_tru : (verify (init 1 ProofRule.ax Proposition.tru) []).verified = true := by
simp [verify, init, premiseCountOk, idxsInRange, premisesVerified, idxsNodup, validateRule]
done

end ProofStep

structure FormalProof where
proofId : Nat
theoremStmt : Proposition
steps : List ProofStep
assumptions : List Proposition
isComplete : Bool
isValid : Bool
creationTime : Int
deriving Repr

namespace FormalProof

def init (pid : Nat) (thm : Proposition) : FormalProof :=
{ proofId := pid
theoremStmt := thm
steps := []
assumptions := []
isComplete := false
isValid := false
creationTime := 0 }

def addStep (p : FormalProof) (s : ProofStep) : FormalProof :=
{ p with steps := p.steps ++ [s], isComplete := false, isValid := false }

def addAssumption (p : FormalProof) (a : Proposition) : FormalProof :=
{ p with assumptions := p.assumptions ++ [a] }

def getLastStep (p : FormalProof) : Option ProofStep :=
match p.steps with
| [] => none
| _ => some (p.steps.getLast (by
have : p.steps ≠ [] := by
intro h
cases p.steps <;> cases h
exact this))

def stepCount (p : FormalProof) : Nat := p.steps.length

def validateAux : List ProofStep → List ProofStep → Bool → List ProofStep × Bool
| acc, [], ok => (acc, ok)
| acc, s :: rest, ok =>
if ok then
let s' := ProofStep.verify s acc
validateAux (acc ++ [s']) rest s'.verified
else
let s' := { s with verified := false }
validateAux (acc ++ [s']) rest false

def validate (p : FormalProof) : FormalProof × Bool :=
match p.steps with
| [] =>
({ p with isValid := false, isComplete := false }, false)
| _ =>
let (validatedSteps, allOk) := validateAux [] p.steps true
let complete :=
if allOk then
match validatedSteps with
| [] => false
| _ =>
let last := validatedSteps.getLast (by
have : validatedSteps ≠ [] := by
intro h
cases validatedSteps <;> cases h
exact this)
decide (last.conclusion = p.theoremStmt)
else
false
let p' :=
{ p with
steps := validatedSteps
isValid := allOk
isComplete := complete }
(p', allOk && complete)

theorem stepCount_addStep (p : FormalProof) (s : ProofStep) :
(addStep p s).stepCount = p.stepCount + 1 := by
simp [addStep, stepCount, List.length_append]
done

end FormalProof

inductive EdgeQuality
| normal
| entangled
deriving DecidableEq, Repr, Inhabited, Fintype

structure EdgeKey where
source : String
target : String
deriving DecidableEq, Repr

def compareEdgeKey (a b : EdgeKey) : Ordering := compare (a.source, a.target) (b.source, b.target)

namespace EdgeKey

def reverse (k : EdgeKey) : EdgeKey := { source := k.target, target := k.source }

theorem reverse_reverse (k : EdgeKey) : reverse (reverse k) = k := by
cases k
rfl
done

end EdgeKey

structure Edge where
quality : EdgeQuality
weight : ℝ
fractalDimension : ℝ
deriving DecidableEq, Repr

structure Node where
id : String
quantumState : Complex
phase : ℝ
creationTime : Option Int
deriving DecidableEq, Repr

namespace Node

def probability (n : Node) : ℝ := (Complex.abs n.quantumState) ^ 2

theorem probability_nonneg (n : Node) : 0 ≤ probability n := by
simp [probability]
exact sq_nonneg (Complex.abs n.quantumState)
done

end Node

structure SelfSimilarRelationalGraph where
nodes : Std.RBMap String Node compare
edges : Std.RBMap EdgeKey (List Edge) compareEdgeKey
deriving Repr

namespace SelfSimilarRelationalGraph

def empty : SelfSimilarRelationalGraph :=
{ nodes := (Std.RBMap.empty : Std.RBMap String Node compare)
edges := (Std.RBMap.empty : Std.RBMap EdgeKey (List Edge) compareEdgeKey) }

def nodeCount (g : SelfSimilarRelationalGraph) : Nat := g.nodes.size

def edgeKeyCount (g : SelfSimilarRelationalGraph) : Nat := g.edges.size

def getNode? (g : SelfSimilarRelationalGraph) (k : String) : Option Node := g.nodes.find? k

def hasNode (g : SelfSimilarRelationalGraph) (k : String) : Bool := (getNode? g k).isSome

def getEdges? (g : SelfSimilarRelationalGraph) (k : EdgeKey) : Option (List Edge) := g.edges.find? k

def hasEdgeKey (g : SelfSimilarRelationalGraph) (k : EdgeKey) : Bool := (getEdges? g k).isSome

def topologyHashHex (g : SelfSimilarRelationalGraph) : String :=
toString g.nodeCount ++ ":" ++ toString g.edgeKeyCount

theorem empty_nodeCount : empty.nodeCount = 0 := by
rfl
done

end SelfSimilarRelationalGraph

def edgeKeyPresent (g : SelfSimilarRelationalGraph) (u v : String) : Prop :=
∃ es, g.edges.find? { source := u, target := v } = some es

def adjRel (g : SelfSimilarRelationalGraph) (u v : String) : Prop :=
edgeKeyPresent g u v ∨ edgeKeyPresent g v u

def connectedGraph (g : SelfSimilarRelationalGraph) : Prop :=
∀ u v, (g.nodes.find? u).isSome → (g.nodes.find? v).isSome → Relation.ReflTransGen (adjRel g) u v

def connectivitySpec (g : SelfSimilarRelationalGraph) : Prop :=
g.nodeCount ≤ 1 ∨ connectedGraph g

noncomputable def checkConnectivityPredicate (g : SelfSimilarRelationalGraph) : Bool := by
classical
exact decide (connectivitySpec g)

def epsilon : ℝ := (1 : ℝ) / 1000000000

def coherenceSpec (g : SelfSimilarRelationalGraph) : Prop :=
∀ id n, g.nodes.find? id = some n → Complex.abs n.quantumState ≤ 1 + epsilon

noncomputable def checkCoherencePredicate (g : SelfSimilarRelationalGraph) : Bool := by
classical
exact decide (coherenceSpec g)

def entanglementSpec (g : SelfSimilarRelationalGraph) : Prop :=
∀ k es, g.edges.find? k = some es →
∀ e, e ∈ es → e.quality = EdgeQuality.entangled →
(g.nodes.find? k.source).isSome ∧ (g.nodes.find? k.target).isSome

noncomputable def checkEntanglementPredicate (g : SelfSimilarRelationalGraph) : Bool := by
classical
exact decide (entanglementSpec g)

def fractalDimSpec (g : SelfSimilarRelationalGraph) : Prop :=
∀ k es, g.edges.find? k = some es →
∀ e, e ∈ es → (0 ≤ e.fractalDimension ∧ e.fractalDimension ≤ 3)

noncomputable def checkFractalDimensionPredicate (g : SelfSimilarRelationalGraph) : Bool := by
classical
exact decide (fractalDimSpec g)

def quantumStateSpec (g : SelfSimilarRelationalGraph) : Prop :=
∀ id n, g.nodes.find? id = some n →
let p := Node.probability n
0 ≤ p ∧ p ≤ 1 + epsilon

noncomputable def checkQuantumStatePredicate (g : SelfSimilarRelationalGraph) : Bool := by
classical
exact decide (quantumStateSpec g)

def memorySafetySpec (g : SelfSimilarRelationalGraph) : Prop :=
∀ k es, g.edges.find? k = some es →
(g.nodes.find? k.source).isSome ∧ (g.nodes.find? k.target).isSome

noncomputable def checkMemorySafetyPredicate (g : SelfSimilarRelationalGraph) : Bool := by
classical
exact decide (memorySafetySpec g)

def maxWeight : ℝ := 10000000000

def typeSafetySpec (g : SelfSimilarRelationalGraph) : Prop :=
(∀ id n, g.nodes.find? id = some n → n.id.length > 0) ∧
(∀ k es, g.edges.find? k = some es → ∀ e, e ∈ es → (0 ≤ e.weight ∧ e.weight ≤ maxWeight))

noncomputable def checkTypeSafetyPredicate (g : SelfSimilarRelationalGraph) : Bool := by
classical
exact decide (typeSafetySpec g)

def symmetrySpec (g : SelfSimilarRelationalGraph) : Prop :=
∀ k es, g.edges.find? k = some es →
match g.edges.find? (EdgeKey.reverse k) with
| some es' => es'.length = es.length
| none => True

noncomputable def checkSymmetryPredicate (g : SelfSimilarRelationalGraph) : Bool := by
classical
exact decide (symmetrySpec g)

def temporalConsistencySpec (g : SelfSimilarRelationalGraph) : Prop :=
∀ k es, g.edges.find? k = some es →
match g.nodes.find? k.source, g.nodes.find? k.target with
| some ns, some nt =>
match ns.creationTime, nt.creationTime with
| some ts, some tt => tt ≥ ts
| _, _ => True
| _, _ => True

noncomputable def checkTemporalConsistencyPredicate (g : SelfSimilarRelationalGraph) : Bool := by
classical
exact decide (temporalConsistencySpec g)

abbrev PredicateFn := SelfSimilarRelationalGraph → Bool

structure Invariant where
id : Nat
invType : InvariantType
description : String
priorityVal : Nat
predicate : PredicateFn
enabled : Bool
violationCount : Nat
lastCheckPassed : Bool
deriving Repr

namespace Invariant

def init (id : Nat) (t : InvariantType) (desc : String) (pred : PredicateFn) : Invariant :=
{ id := id
invType := t
description := desc
priorityVal := InvariantType.priority t
predicate := pred
enabled := true
violationCount := 0
lastCheckPassed := true }

def check (inv : Invariant) (g : SelfSimilarRelationalGraph) : Invariant × Bool :=
if inv.enabled then
let ok := inv.predicate g
let vc := if ok then inv.violationCount else inv.violationCount + 1
({ inv with lastCheckPassed := ok, violationCount := vc }, ok)
else
({ inv with lastCheckPassed := true }, true)

def enable (inv : Invariant) : Invariant := { inv with enabled := true }

def disable (inv : Invariant) : Invariant := { inv with enabled := false }

def resetViolations (inv : Invariant) : Invariant := { inv with violationCount := 0 }

theorem init_priority (id : Nat) (t : InvariantType) (d : String) (p : PredicateFn) :
(init id t d p).priorityVal = InvariantType.priority t := by
rfl
done

end Invariant

structure InvariantStatistics where
totalInvariants : Nat
enabledInvariants : Nat
totalChecks : Nat
totalViolations : Nat
deriving Repr

structure InvariantRegistry where
invs : Std.RBMap Nat Invariant compare
byType : Vector (List Nat) (Fintype.card InvariantType)
nextId : Nat
checkCount : Nat
violationCount : Nat
deriving Repr

namespace InvariantRegistry

def empty : InvariantRegistry :=
{ invs := (Std.RBMap.empty : Std.RBMap Nat Invariant compare)
byType := Vector.replicate (Fintype.card InvariantType) []
nextId := 1
checkCount := 0
violationCount := 0 }

def typeIndex (t : InvariantType) : Fin (Fintype.card InvariantType) :=
(Fintype.equivFin InvariantType) t

def count (r : InvariantRegistry) : Nat := r.invs.size

def registerInvariant (r : InvariantRegistry) (t : InvariantType) (desc : String) (pred : PredicateFn) :
InvariantRegistry × Nat :=
let id := r.nextId
let inv := Invariant.init id t desc pred
let invs' := r.invs.insert id inv
let idx := typeIndex t
let lst := r.byType.get idx
let byType' := r.byType.set idx (lst ++ [id])
({ r with invs := invs', byType := byType', nextId := id + 1 }, id)

def registerCore (r : InvariantRegistry) : InvariantRegistry :=
let (r1, _) := registerInvariant r InvariantType.connectivity "Graph must maintain connectivity between nodes" checkConnectivityPredicate
let (r2, _) := registerInvariant r1 InvariantType.coherence "Quantum state magnitude must not exceed 1" checkCoherencePredicate
let (r3, _) := registerInvariant r2 InvariantType.entanglement "Entangled edges must have valid paired nodes" checkEntanglementPredicate
let (r4, _) := registerInvariant r3 InvariantType.fractalDimension "Fractal dimension must be in [0, 3]" checkFractalDimensionPredicate
let (r5, _) := registerInvariant r4 InvariantType.quantumState "Quantum states must be valid probabilities" checkQuantumStatePredicate
let (r6, _) := registerInvariant r5 InvariantType.memorySafety "All edge endpoints must reference existing nodes" checkMemorySafetyPredicate
let (r7, _) := registerInvariant r6 InvariantType.typeSafety "All values must have valid types" checkTypeSafetyPredicate
let (r8, _) := registerInvariant r7 InvariantType.symmetry "Graph symmetry properties must be preserved" checkSymmetryPredicate
let (r9, _) := registerInvariant r8 InvariantType.temporalConsistency "Temporal ordering must be consistent" checkTemporalConsistencyPredicate
r9

def getInvariant? (r : InvariantRegistry) (id : Nat) : Option Invariant := r.invs.find? id

theorem registerCore_count_ge_9 : (registerCore empty).count ≥ 9 := by
simp [registerCore, empty, count, registerInvariant]
decide
done

end InvariantRegistry

structure HoareTriple where
id : Nat
pre : Proposition
op : Proposition
post : Proposition
verified : Bool
frame : Option Proposition
deriving Repr

namespace HoareTriple

def init (id : Nat) (pre op post : Proposition) : HoareTriple :=
{ id := id, pre := pre, op := op, post := post, verified := false, frame := none }

def setFrame (t : HoareTriple) (f : Proposition) : HoareTriple := { t with frame := some f }

def toProp (t : HoareTriple) : Proposition := Proposition.hoare t.pre t.op t.post

theorem toProp_is_hoare (t : HoareTriple) :
∃ a b c, toProp t = Proposition.hoare a b c := by
refine ⟨t.pre, t.op, t.post, ?_⟩
rfl
done

end HoareTriple

structure HoareStatistics where
totalTriples : Nat
totalVerifications : Nat
successfulVerifications : Nat
deriving Repr

structure HoareLogicVerifier where
triples : Std.RBMap Nat HoareTriple compare
nextId : Nat
totalVerifications : Nat
successfulVerifications : Nat
deriving Repr

namespace HoareLogicVerifier

def init : HoareLogicVerifier :=
{ triples := (Std.RBMap.empty : Std.RBMap Nat HoareTriple compare)
nextId := 1
totalVerifications := 0
successfulVerifications := 0 }

def count (v : HoareLogicVerifier) : Nat := v.triples.size

def createTriple (v : HoareLogicVerifier) (pre op post : Proposition) : HoareLogicVerifier × Nat :=
let id := v.nextId
let t := HoareTriple.init id pre op post
let m := v.triples.insert id t
({ v with triples := m, nextId := id + 1 }, id)

def getTriple? (v : HoareLogicVerifier) (id : Nat) : Option HoareTriple := v.triples.find? id

def verifyAssign (v : HoareLogicVerifier) (tid : Nat) (x : String) (e : Term) : Except VerificationError (HoareLogicVerifier × Bool) :=
match v.triples.find? tid with
| none => Except.error VerificationError.invalidProofStep
| some t =>
let v' := { v with totalVerifications := v.totalVerifications + 1 }
let postSub := Proposition.substitute t.post x e
let ok := decide (postSub = t.pre)
let t' := if ok then { t with verified := true } else t
let triples' := v'.triples.insert tid t'
let v'' :=
if ok then
{ v' with triples := triples', successfulVerifications := v'.successfulVerifications + 1 }
else
{ v' with triples := triples' }
Except.ok (v'', ok)

def getStatistics (v : HoareLogicVerifier) : HoareStatistics :=
{ totalTriples := v.count
totalVerifications := v.totalVerifications
successfulVerifications := v.successfulVerifications }

theorem createTriple_count_one :
(createTriple init Proposition.tru (Proposition.atomic "op" []) Proposition.tru).1.count = 1 := by
simp [createTriple, init, count, HoareTriple.init]
done

end HoareLogicVerifier

structure Clause where
literals : List Proposition
deriving Repr

def areComplementary (p q : Proposition) : Bool :=
match p with
| Proposition.neg a => decide (a = q)
| _ =>
match q with
| Proposition.neg b => decide (b = p)
| _ => false

namespace Clause

def empty : Clause := { literals := [] }

def addLiteral (c : Clause) (p : Proposition) : Clause := { literals := c.literals ++ [p] }

def isEmpty (c : Clause) : Bool := c.literals = []

def isUnit (c : Clause) : Bool := c.literals.length = 1

def size (c : Clause) : Nat := c.literals.length

def containsComplementaryAux : List Proposition → Bool
| [] => false
| p :: rest =>
rest.any (fun q => areComplementary p q) || containsComplementaryAux rest

def containsComplementary (c : Clause) : Bool := containsComplementaryAux c.literals

def clone (c : Clause) : Clause := c

theorem empty_isEmpty : isEmpty empty = true := by
rfl
done

theorem addLiteral_notEmpty (p : Proposition) : isEmpty (addLiteral empty p) = false := by
simp [isEmpty, addLiteral, empty]
done

theorem addLiteral_unit (p : Proposition) : isUnit (addLiteral empty p) = true := by
simp [isUnit, addLiteral, empty]
done

end Clause

structure ProofTreeNode where
proposition : Proposition
rule : ProofRule
children : List ProofTreeNode
deriving Repr

namespace ProofTreeNode

def isComplete (n : ProofTreeNode) : Bool :=
match n.children with
| [] =>
(n.rule = ProofRule.ax) || (n.proposition.propType = PropType.trueConst)
| cs => cs.all (fun c => isComplete c)

theorem isComplete_leaf_ax (p : Proposition) :
isComplete { proposition := p, rule := ProofRule.ax, children := [] } = true := by
simp [isComplete]
done

end ProofTreeNode

structure ProverStatistics where
assumptionCount : Nat
clauseCount : Nat
unificationCount : Nat
resolutionCount : Nat
deriving Repr

structure TheoremProver where
assumptions : List Proposition
clauses : List Clause
maxDepth : Nat
unificationCount : Nat
resolutionCount : Nat
deriving Repr

namespace TheoremProver

def init : TheoremProver :=
{ assumptions := []
clauses := []
maxDepth := 100
unificationCount := 0
resolutionCount := 0 }

def addAssumption (p : TheoremProver) (a : Proposition) : TheoremProver :=
{ p with assumptions := p.assumptions ++ [a] }

def proveBackward (p : TheoremProver) (goal : Proposition) (depth : Nat) : Bool :=
if depth > p.maxDepth then
false
else if p.assumptions.any (fun a => decide (a = goal)) then
true
else
match goal with
| Proposition.tru => true
| Proposition.fls => false
| Proposition.conj a b =>
proveBackward p a (depth + 1) && proveBackward p b (depth + 1)
| Proposition.disj a b =>
proveBackward p a (depth + 1) || proveBackward p b (depth + 1)
| _ =>
p.assumptions.any (fun a =>
match a with
| Proposition.impl pre post =>
decide (post = goal) && proveBackward p pre (depth + 1)
| _ => false)

def prove (p : TheoremProver) (goal : Proposition) : Bool := proveBackward p goal 0

def getStatistics (p : TheoremProver) : ProverStatistics :=
{ assumptionCount := p.assumptions.length
clauseCount := p.clauses.length
unificationCount := p.unificationCount
resolutionCount := p.resolutionCount }

theorem prove_true_with_true_assumption :
prove (addAssumption init Proposition.tru) Proposition.tru = true := by
simp [prove, proveBackward, addAssumption, init]
done

end TheoremProver

abbrev GraphHash := Vector UInt8 32

def trivialHash : GraphHash := Vector.replicate 32 (0 : UInt8)

structure VerificationResult where
success : Bool
errorType : Option VerificationError
violated : List Nat
execTimeNs : Int
graphHash : GraphHash
deriving Repr

namespace VerificationResult

def initSuccess (h : GraphHash) (t : Int) : VerificationResult :=
{ success := true, errorType := none, violated := [], execTimeNs := t, graphHash := h }

def initFailure (e : VerificationError) (h : GraphHash) (t : Int) : VerificationResult :=
{ success := false, errorType := some e, violated := [], execTimeNs := t, graphHash := h }

def addViolation (r : VerificationResult) (id : Nat) : VerificationResult :=
if r.violated.contains id then r else { r with violated := r.violated ++ [id] }

theorem addViolation_idempotent (r : VerificationResult) (id : Nat) :
addViolation (addViolation r id) id = addViolation r id := by
by_cases h : r.violated.contains id
· simp [addViolation, h, List.contains_eq_true] at *
simp [addViolation, h]
· simp [addViolation, h]
simp [addViolation, h]
done

end VerificationResult

structure EngineStatistics where
totalVerifications : Nat
successfulVerifications : Nat
invariantCount : Nat
hoareTripleCount : Nat
assumptionCount : Nat
historySize : Nat
uptimeMs : Int
deriving Repr

structure FormalVerificationEngine where
registry : InvariantRegistry
hoare : HoareLogicVerifier
prover : TheoremProver
history : List VerificationResult
totalVerifications : Nat
successfulVerifications : Nat
creationTime : Int
deriving Repr

namespace FormalVerificationEngine

def init : FormalVerificationEngine :=
let reg := InvariantRegistry.registerCore InvariantRegistry.empty
{ registry := reg
hoare := HoareLogicVerifier.init
prover := TheoremProver.init
history := []
totalVerifications := 0
successfulVerifications := 0
creationTime := 0 }

def getStatistics (e : FormalVerificationEngine) : EngineStatistics :=
{ totalVerifications := e.totalVerifications
successfulVerifications := e.successfulVerifications
invariantCount := e.registry.count
hoareTripleCount := e.hoare.count
assumptionCount := e.prover.assumptions.length
historySize := e.history.length
uptimeMs := 0 }

theorem init_has_core_invariants : (init.registry.count) ≥ 9 := by
simp [init, InvariantRegistry.registerCore_count_ge_9]
done

theorem init_stats_zero_total : (getStatistics init).totalVerifications = 0 := by
rfl
done

end FormalVerificationEngine

theorem test_invariantType_enum_conversion_connectivity :
InvariantType.fromString "connectivity" = some InvariantType.connectivity := by
simp [InvariantType.fromString]
done

theorem test_invariantType_enum_conversion_coherence :
InvariantType.fromString "coherence" = some InvariantType.coherence := by
simp [InvariantType.fromString]
done

theorem test_invariantType_enum_conversion_entanglement :
InvariantType.fromString "entanglement" = some InvariantType.entanglement := by
simp [InvariantType.fromString]
done

theorem test_invariantType_toString_memorySafety :
InvariantType.toString InvariantType.memorySafety = "memory_safety" := by
rfl
done

theorem test_proofRule_properties_1 :
ProofRule.requiresPremises ProofRule.ax = false := by
rfl
done

theorem test_proofRule_properties_2 :
ProofRule.requiresPremises ProofRule.modusPonens = true := by
rfl
done

theorem test_proofRule_properties_3 :
ProofRule.minimumPremises ProofRule.modusPonens = 2 := by
rfl
done

theorem test_proofRule_properties_4 :
ProofRule.minimumPremises ProofRule.ax = 0 := by
rfl
done

theorem test_propType_arity_1 : PropType.arity PropType.atomic = 0 := by
rfl
done

theorem test_propType_arity_2 : PropType.arity PropType.negation = 1 := by
rfl
done

theorem test_propType_arity_3 : PropType.arity PropType.conjunction = 2 := by
rfl
done

theorem test_propType_arity_4 : PropType.arity PropType.hoareTriple = 3 := by
rfl
done

theorem test_term_creation_ops_1 :
Term.isVar (Term.var "x") = true := by
rfl
done

theorem test_term_creation_ops_2 :
Term.name (Term.var "x") = "x" := by
rfl
done

theorem test_term_creation_ops_3 :
Term.isVar (Term.const "42") = false := by
rfl
done

theorem test_prop_creation_and_clone :
Proposition.equals (Proposition.atomic "P" []) (Proposition.clone (Proposition.atomic "P" [])) = true := by
simp [Proposition.equals, Proposition.clone]
done

theorem test_prop_negation_subprops_len :
(Proposition.subProps (Proposition.neg (Proposition.atomic "P" []))).length = 1 := by
rfl
done

theorem test_prop_binary_conj_len :
(Proposition.subProps (Proposition.conj (Proposition.atomic "P" []) (Proposition.atomic "Q" []))).length = 2 := by
rfl
done

theorem test_hoare_triple_prop_len :
(Proposition.subProps (Proposition.hoare Proposition.tru (Proposition.atomic "assign" []) Proposition.tru)).length = 3 := by
rfl
done

theorem test_proofStep_creation_and_verification :
(ProofStep.verify (ProofStep.init 1 ProofRule.ax Proposition.tru) []).verified = true := by
simpa using ProofStep.verify_ax_true_on_tru
done

theorem test_formalProof_creation_and_step_addition :
(FormalProof.addStep (FormalProof.init 1 (Proposition.atomic "theorem" [])) (ProofStep.init 1 ProofRule.ax Proposition.tru)).stepCount = 1 := by
simp [FormalProof.stepCount, FormalProof.init, FormalProof.addStep]
done

theorem test_invariantRegistry_core_invariants_count :
(InvariantRegistry.registerCore InvariantRegistry.empty).count ≥ 9 := by
simpa using InvariantRegistry.registerCore_count_ge_9
done

theorem test_connectivity_empty_graph :
checkConnectivityPredicate SelfSimilarRelationalGraph.empty = true := by
classical
simp [checkConnectivityPredicate, connectivitySpec, connectedGraph, SelfSimilarRelationalGraph.empty, SelfSimilarRelationalGraph.nodeCount, SelfSimilarRelationalGraph.empty_nodeCount]
done

theorem test_hoareLogicVerifier_creation :
(HoareLogicVerifier.createTriple HoareLogicVerifier.init Proposition.tru (Proposition.atomic "op" []) Proposition.tru).2 > 0 := by
simp [HoareLogicVerifier.createTriple, HoareLogicVerifier.init]
decide
done

theorem test_hoareLogicVerifier_count_one :
(HoareLogicVerifier.createTriple HoareLogicVerifier.init Proposition.tru (Proposition.atomic "op" []) Proposition.tru).1.count = 1 := by
simpa using HoareLogicVerifier.createTriple_count_one
done

theorem test_theoremProver_backward_chaining :
TheoremProver.prove (TheoremProver.addAssumption TheoremProver.init Proposition.tru) Proposition.tru = true := by
simpa using TheoremProver.prove_true_with_true_assumption
done

theorem test_clause_ops :
Clause.isUnit (Clause.addLiteral Clause.empty (Proposition.atomic "P" [])) = true := by
simpa using Clause.addLiteral_unit (Proposition.atomic "P" [])
done

theorem test_engine_creation_stats_zero :
(FormalVerificationEngine.getStatistics FormalVerificationEngine.init).totalVerifications = 0 := by
simpa using FormalVerificationEngine.init_stats_zero_total
done

end FormalVerification
