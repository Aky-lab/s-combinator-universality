import PureSFormal.PureS.SchedulerResponseInvariant
import PureSFormal.PureS.Dovetail

/-!
# H6 occurrence-boundary certificates for the pinned S construction

This module gives an exact nine-state congruence, root classifications for
literal upstream code and response constructors, generic occurrence-decomposition
and transfer theorems for finite templates with arbitrary/repeated holes, and
registered fresh/completed-shell occurrence rules with the literal frozen audit.

It does not prove that every scheduler step carries the required inherited
origin certificates, nor does it establish label-specific first-event provenance.
In particular, Endpoint is a hypothesis at generic continuation boundaries;
its response and static clock instances are discharged below, but complete
CLOCK/FUEL/context generation and stage induction are still separate obligations.
-/
namespace SOnlyProvenance

open PureSFormal.PureS

inductive State where
  | s | b | h | h0 | h1 | h2 | h3 | h4 | other
  deriving DecidableEq, Repr

/-- Exact finite congruence for the reserved prefix and its four arguments. -/
def delta : State → State → State
  | .s, .s => .b
  | .b, .s => .h
  | .b, .h => .h0
  | .h0, _ => .h1
  | .h1, _ => .h2
  | .h2, _ => .h3
  | .h3, _ => .h4
  | _, _ => .other

def classify : Term → State
  | .s => .s
  | .app l r => delta (classify l) (classify r)

theorem delta_ne_s (l r : State) : delta l r ≠ .s := by
  cases l <;> cases r <;> decide

theorem delta_b_iff (l r : State) : delta l r = .b ↔ l = .s ∧ r = .s := by
  cases l <;> cases r <;> decide

theorem delta_h_iff (l r : State) : delta l r = .h ↔ l = .b ∧ r = .s := by
  cases l <;> cases r <;> decide

theorem delta_h0_iff (l r : State) : delta l r = .h0 ↔ l = .b ∧ r = .h := by
  cases l <;> cases r <;> decide

theorem delta_h1_iff (l r : State) : delta l r = .h1 ↔ l = .h0 := by
  cases l <;> cases r <;> decide

theorem delta_h2_iff (l r : State) : delta l r = .h2 ↔ l = .h1 := by
  cases l <;> cases r <;> decide

theorem delta_h3_iff (l r : State) : delta l r = .h3 ↔ l = .h2 := by
  cases l <;> cases r <;> decide

theorem delta_h4_iff (l r : State) : delta l r = .h4 ↔ l = .h3 := by
  cases l <;> cases r <;> decide

@[simp] theorem classify_s_iff (t : Term) : classify t = .s ↔ t = .s := by
  cases t with
  | s => simp [classify]
  | app l r => simp [classify, delta_ne_s]

@[simp] theorem classify_b_iff (t : Term) : classify t = .b ↔ t = b := by
  cases t with
  | s => simp [classify, b]
  | app l r => simp [classify, delta_b_iff, b]

@[simp] theorem classify_h_iff (t : Term) : classify t = .h ↔ t = haltTag := by
  cases t with
  | s => simp [classify, haltTag]
  | app l r => simp [classify, delta_h_iff, haltTag]

@[simp] theorem classify_h0_iff (t : Term) : classify t = .h0 ↔ t = haltCode := by
  cases t with
  | s => simp [classify, haltCode]
  | app l r => simp [classify, delta_h0_iff, haltCode]

@[simp] theorem classify_h1_iff (t : Term) :
    classify t = .h1 ↔ ∃ a, t = .app haltCode a := by
  cases t with
  | s => simp [classify]
  | app l r => simp [classify, delta_h1_iff]

@[simp] theorem classify_h2_iff (t : Term) :
    classify t = .h2 ↔ ∃ a b, t = .app (.app haltCode a) b := by
  cases t with
  | s => simp [classify]
  | app l r => simp [classify, delta_h2_iff]

@[simp] theorem classify_h3_iff (t : Term) :
    classify t = .h3 ↔ ∃ a b c, t = .app (.app (.app haltCode a) b) c := by
  cases t with
  | s => simp [classify]
  | app l r => simp [classify, delta_h3_iff]

/-- Exact semantics for all finite trees of the accepting abstract state. -/
@[simp] theorem classify_h4_iff (t : Term) :
    classify t = .h4 ↔
      ∃ a b c d, t = .app (.app (.app (.app haltCode a) b) c) d := by
  cases t with
  | s => simp [classify]
  | app l r => simp [classify, delta_h4_iff]

/-- The dangerous endpoint class is exactly the reserved arity-five prefix. -/
theorem extension_h6_iff (endpoint audit : Term) :
    classify (.app endpoint audit) = .h4 ↔ classify endpoint = .h3 :=
  delta_h4_iff _ _

/-- The coarse generated-endpoint interface suffices for every K A boundary. -/
theorem safe_extension (endpoint audit : Term)
    (safe : classify endpoint = .other ∨ classify endpoint = .h4) :
    classify (.app endpoint audit) ≠ .h4 := by
  intro accepted
  have dangerous := (extension_h6_iff endpoint audit).mp accepted
  rcases safe with h | h <;> simp [h] at dangerous

/-- Unlike independent public grammar holes, all newborn Local audits are literal. -/
theorem fresh_audit (snapshot dispatch seed continuation : Term) :
    (Term.app (Term.app (Term.app (Term.app haltCode snapshot) dispatch) seed)
      continuation).subterm? [.left, .left, .left, .right] = some snapshot := by simp [Term.subterm?]

/-- Every H6 occurrence satisfies P, including in arbitrary audit holes. -/
def AllH6 (P : Term → Prop) : Term → Prop
  | .s => True
  | .app l r => AllH6 P l ∧ AllH6 P r ∧
      (classify (.app l r) = .h4 → P (.app l r))

@[simp] theorem allH6_s (P : Term → Prop) : AllH6 P .s := True.intro

/-- Generic occurrence-level lift. Holes need not be H6-free; their inherited
occurrences retain their supplied P proofs. -/
theorem app_no_new {P : Term → Prop} {l r : Term}
    (hl : AllH6 P l) (hr : AllH6 P r) (safe : classify l ≠ .h3) :
    AllH6 P (.app l r) := by
  refine ⟨hl, hr, ?_⟩
  intro accepted
  exact (safe ((extension_h6_iff l r).mp accepted)).elim

theorem app_registered_root {P : Term → Prop} {l r : Term}
    (hl : AllH6 P l) (hr : AllH6 P r) (registered : P (.app l r)) :
    AllH6 P (.app l r) := ⟨hl, hr, fun _ => registered⟩

/-- Endpoint status required at outer continuation/history boundaries. -/
def Endpoint (term : Term) : Prop :=
  classify term = .other ∨ classify term = .h4

theorem endpoint_ne_h3 {t : Term} (h : Endpoint t) : classify t ≠ .h3 := by
  rcases h with h | h <;> simp [h]

theorem endpoint_ne_s {t : Term} (h : Endpoint t) : classify t ≠ .s := by
  rcases h with h | h <;> simp [h]

theorem endpoint_extension {P : Term → Prop} {k audit : Term}
    (hk : AllH6 P k) (ha : AllH6 P audit) (safe : Endpoint k) :
    AllH6 P (.app k audit) ∧ classify (.app k audit) = .other := by
  constructor
  · exact app_no_new hk ha (endpoint_ne_h3 safe)
  · rcases safe with h | h <;> simp [classify, h, delta]

/-- An arbitrary history on an Other-headed spine cannot create an H6 root. -/
theorem applyArgs_other {P : Term → Prop} {head : Term}
    (arguments : List Term) (hh : AllH6 P head) (hc : classify head = .other)
    (ha : ∀ t ∈ arguments, AllH6 P t) :
    AllH6 P (Term.applyArgs head arguments) ∧
      classify (Term.applyArgs head arguments) = .other := by
  induction arguments generalizing head with
  | nil => exact ⟨hh, hc⟩
  | cons a tail ih =>
      have one : AllH6 P (.app head a) :=
        app_no_new hh (ha a (by simp)) (by simp [hc])
      have cls : classify (.app head a) = .other := by simp [classify, hc, delta]
      exact ih one cls (fun t ht => ha t (by simp [ht]))

/-- Arbitrary right payloads of S _ and S _ _ cannot manufacture H6. -/
theorem s_pair_carries {P : Term → Prop} {a b : Term}
    (ha : AllH6 P a) (hb : AllH6 P b) : AllH6 P (.app (.app .s a) b) := by
  apply app_no_new (app_no_new (allH6_s P) ha (by decide)) hb
  intro bad
  have impossible := (delta_h3_iff .s (classify a)).mp bad
  cases impossible

theorem s_one_carries {P : Term → Prop} {a : Term}
    (ha : AllH6 P a) : AllH6 P (.app .s a) :=
  app_no_new (allH6_s P) ha (by decide)

/-- chosen snapshots in generated whole carriers have Other head state. -/
theorem chosen_other (snapshot response : Term) (hs : Endpoint snapshot) :
    classify (chosen snapshot response) = .other := by
  rcases hs with hs | hs <;> simp [chosen, classify, hs, delta]

theorem chosen_carries {P : Term → Prop} {snapshot response : Term}
    (hs : AllH6 P snapshot) (hr : AllH6 P response) :
    AllH6 P (chosen snapshot response) := s_pair_carries hs hr

/-- Reserved literals contain no H6 occurrence, for any origin predicate. -/
theorem haltCode_carries (P : Term → Prop) : AllH6 P haltCode := by
  simp [haltCode, haltTag, b, AllH6, classify, delta]

theorem h_prefix1_carries {P : Term → Prop} {snapshot : Term}
    (hs : AllH6 P snapshot) : AllH6 P (.app haltCode snapshot) :=
  app_no_new (haltCode_carries P) hs (by decide)

/-- The only possible new H6 in the four-argument reserved shell is its
registered root. All fields may themselves contain previously registered H6s. -/
theorem fresh_shell_carries {P : Term → Prop} {snapshot dispatch seed cont : Term}
    (hs : AllH6 P snapshot) (hd : AllH6 P dispatch)
    (hw : AllH6 P seed) (hc : AllH6 P cont)
    (birth : P (.app (.app (.app (.app haltCode snapshot) dispatch) seed) cont)) :
    AllH6 P (.app (.app (.app (.app haltCode snapshot) dispatch) seed) cont) := by
  have p1 := h_prefix1_carries hs
  have p2 : AllH6 P (.app (.app haltCode snapshot) dispatch) :=
    app_no_new p1 hd (by simp [classify, haltCode, haltTag, b, delta])
  have p3 : AllH6 P (.app (.app (.app haltCode snapshot) dispatch) seed) :=
    app_no_new p2 hw (by simp [classify, haltCode, haltTag, b, delta])
  exact app_registered_root p3 hc birth

/-- Rebuilt completed-Local ancestors: every independent payload remains
licensed, and the one old shell root must keep its registered origin. -/
theorem completed_outer_carries {P : Term → Prop}
    {snapshot dispatch word seedAudit endpoint continuationAudit : Term}
    (hs : AllH6 P snapshot) (hd : AllH6 P dispatch) (hw : AllH6 P word)
    (hsa : AllH6 P seedAudit) (he : AllH6 P endpoint)
    (hca : AllH6 P continuationAudit) (safe : Endpoint endpoint)
    (registered : P (.app (.app (.app (.app haltCode snapshot) dispatch)
      (.app (.app .s word) seedAudit)) (.app endpoint continuationAudit))) :
    AllH6 P (.app (.app (.app (.app haltCode snapshot) dispatch)
      (.app (.app .s word) seedAudit)) (.app endpoint continuationAudit)) :=
  fresh_shell_carries hs hd (s_pair_carries hw hsa)
    (endpoint_extension he hca safe).1 registered

/-- The same frozen audit is retained under arbitrary dispatcher and endpoint
changes. This does not allow rewriting inside the snapshot hole itself. -/
theorem rebuilt_outer_audit (snapshot dispatch word seedAudit endpoint audit : Term) :
    (.app (.app (.app (.app haltCode snapshot) dispatch)
      (.app (.app .s word) seedAudit)) (.app endpoint audit) : Term).subterm?
        [.left, .left, .left, .right] = some snapshot := by
  simp [Term.subterm?]


/-! ## Literal static-code and generated endpoint classifications -/

@[simp] theorem classify_p : classify p = .other := rfl

@[simp] theorem classify_push (j next : Term) : classify (push j next) = .other := by
  cases h : classify next <;> simp [push, classify, h, delta]

@[simp] theorem classify_appender (bits : List Bool) : classify (appender bits) = .other := by
  cases bits <;> simp

@[simp] theorem classify_selectedAction (program : PureSFormal.CTS.Program)
    (label : ActionLabel program) : classify (selectedAction program label) = .other := by
  rcases label with ⟨phase, bit⟩
  cases bit <;> simp [selectedAction]

@[simp] theorem classify_compileDispatcher {Label : Type}
    (encode : Label → Term) (tree : Dispatcher.Tree Label)
    (leaves : ∀ label, classify (encode label) = .other) :
    classify (compileDispatcher encode tree) = .other := by
  induction tree with
  | leaf label => simp [compileDispatcher, leafCode, classify, b, leaves, delta]
  | node left right ihl ihr =>
      simp [compileDispatcher, nodeCode, fork, classify, b, ihl, ihr, delta]

@[simp] theorem classify_compileActions (program : PureSFormal.CTS.Program)
    (tree : Dispatcher.Tree (ActionLabel program)) :
    classify (compileActions program tree) = .other :=
  classify_compileDispatcher _ _ (classify_selectedAction program)

@[simp] theorem classify_C (n : Nat) : classify (C n) = .other := by
  induction n with
  | zero => rfl
  | succ n ih => simp [C, classify, b, ih, delta]

@[simp] theorem classify_valueTag (bit : Bool) : classify (valueTag bit) = .other := by
  cases bit <;> rfl

@[simp] theorem classify_live (bit : Bool) : classify (live bit) = .other := by
  simp [live, classify, b, delta]

@[simp] theorem classify_environment (actions : Term) (bits : List Bool) :
    classify (environmentCode actions bits) = .other := rfl

@[simp] theorem classify_act (actions : Term) : classify (actCode actions) = .other := rfl

@[simp] theorem classify_dispatcher (actions : Term) (bits : List Bool) :
    classify (dispatcherCode actions bits) = .other := rfl

@[simp] theorem classify_clockWrappers (n r : Nat) :
    classify (clockWrappers n r) = .other := by
  cases r <;> simp [clockWrappers, clockBase, classify, delta]

@[simp] theorem classify_clockExit (n r : Nat) (e : Term) :
    classify (Dovetail.clockExit n r e) = .other := by
  simp [Dovetail.clockExit, classify, delta]

@[simp] theorem classify_base (e continuation : Term)
    (hc : classify continuation = .other) :
    classify (baseCarrier e continuation) = .other := by
  simp [baseCarrier, classify, hc, delta]

@[simp] theorem classify_frame (actions : Term) (bits : List Bool) (continuation body : Term) :
    classify (frame (environmentCode actions bits) continuation body) = .other := rfl

@[simp] theorem classify_freshLocal (actions : Term) (bits : List Bool) (continuation carrier : Term) :
    classify (freshLocal actions bits continuation carrier) = .h4 := rfl

@[simp] theorem classify_frameFirst (actions : Term) (bits : List Bool) (continuation carrier : Term) :
    classify (SchedulerResponseInvariant.frameFirstRoot actions bits continuation carrier) = .other := rfl

@[simp] theorem classify_frameSecond (actions : Term) (bits : List Bool) (continuation carrier : Term) :
    classify (SchedulerResponseInvariant.frameSecondRoot actions bits continuation carrier) = .other := rfl

@[simp] theorem classify_liveCell (bit : Bool) (carrier : Term) :
    classify (extendAccumulator bit carrier) = .other := by
  simp [extendAccumulator, classify, delta]

/-- Every accumulator produced by any appender remains a safe whole endpoint. -/
theorem appenderAccumulator_endpoint (bits : List Bool) (initial : Term)
    (hi : Endpoint initial) : Endpoint (appenderAccumulator bits initial) := by
  induction bits generalizing initial with
  | nil => exact hi
  | cons bit rest ih => exact ih _ (Or.inl (classify_liveCell bit initial))

/-- These are the actual upstream response-root constructors, not sampled rows. -/
theorem response_endpoint
    {program : PureSFormal.CTS.Program} {tree : Dispatcher.Tree (ActionLabel program)}
    {route : Dispatcher.Route} {label : ActionLabel program}
    {path : Dispatcher.HasRoute tree route label}
    {bits : List Bool} {continuation carrier term : Term} {done : Bool}
    (row : SchedulerResponseInvariant.ResponseRootMutation program tree path bits continuation carrier done term) :
    Endpoint term := by
  cases row <;>
    simp [Endpoint, freshLocal, Carrier.activeShell, Carrier.shell, freshHField,
      Term.applyArgs, classify, haltCode, haltTag, b, delta,
      SchedulerResponseInvariant.frameFirstRoot,
      SchedulerResponseInvariant.frameSecondRoot, dispatcherCode, actCode]

/-! ## Exact template decomposition, with arbitrary and repeated holes -/

/-- Occurrence ancestry; equal subtrees at separate positions remain permitted. -/
inductive Descendant : Term → Term → Prop
  | root (t : Term) : Descendant t t
  | left {l r t : Term} : Descendant l t → Descendant (.app l r) t
  | right {l r t : Term} : Descendant r t → Descendant (.app l r) t

namespace Descendant

theorem app_cases {l r t : Term} (h : Descendant (.app l r) t) :
    t = .app l r ∨ Descendant l t ∨ Descendant r t := by
  cases h with
  | root => exact Or.inl rfl
  | left h => exact Or.inr (Or.inl h)
  | right h => exact Or.inr (Or.inr h)

theorem s_eq {t : Term} (h : Descendant .s t) : t = .s := by
  cases h
  rfl

end Descendant

/-- Finite templates expose exactly the scaffold nodes affected by a row or
rebuilt-context constructor. Equal variable indices denote exact copied terms. -/
inductive Template where
  | s
  | hole (index : Nat)
  | app (left right : Template)
  deriving Repr

namespace Template

def instantiate (substitution : Nat → Term) : Template → Term
  | .s => .s
  | .hole i => substitution i
  | .app l r => .app (instantiate substitution l) (instantiate substitution r)

def abstract (states : Nat → State) : Template → State
  | .s => .s
  | .hole i => states i
  | .app l r => delta (abstract states l) (abstract states r)

/-- No bounded concrete terms are used: classification commutes with every
substitution of arbitrarily large finite S trees. -/
theorem abstraction_exact (substitution : Nat → Term) (template : Template) :
    classify (instantiate substitution template) =
      abstract (fun i => classify (substitution i)) template := by
  induction template with
  | s => rfl
  | hole i => rfl
  | app l r ihl ihr => simp [instantiate, classify, abstract, ihl, ihr]

def holes : Template → List Nat
  | .s => []
  | .hole i => [i]
  | .app l r => holes l ++ holes r

def scaffold (substitution : Nat → Term) : Template → List Term
  | .s => [.s]
  | .hole _ => []
  | .app l r =>
      instantiate substitution (.app l r) :: (scaffold substitution l ++ scaffold substitution r)

/-- Every occurrence is either scaffold or inside a hole. No provenance of
arbitrary hole contents is inferred from the public carrier grammar. -/
theorem descendant_decomposition (substitution : Nat → Term) (template : Template)
    {found : Term} (occurs : Descendant (instantiate substitution template) found) :
    found ∈ scaffold substitution template ∨
      ∃ i ∈ holes template, Descendant (substitution i) found := by
  induction template with
  | s =>
      have eq := Descendant.s_eq occurs
      subst found
      exact Or.inl (by simp [scaffold])
  | hole i => exact Or.inr ⟨i, by simp [holes], occurs⟩
  | app l r ihl ihr =>
      rcases Descendant.app_cases occurs with eq | hl | hr
      · exact Or.inl (by simp [scaffold, instantiate, eq])
      · rcases ihl hl with hs | ⟨i, hi, ht⟩
        · exact Or.inl (by simp [scaffold, hs])
        · exact Or.inr ⟨i, by simp [holes, hi], ht⟩
      · rcases ihr hr with hs | ⟨i, hi, ht⟩
        · exact Or.inl (by simp [scaffold, hs])
        · exact Or.inr ⟨i, by simp [holes, hi], ht⟩

/-- The requested H6 occurrence-birth certificate. Finite state checks control
only scaffold cases; every hole occurrence requires its inherited certificate. -/
theorem h6_decomposition (substitution : Nat → Term) (template : Template)
    {found : Term} (occurs : Descendant (instantiate substitution template) found)
    (h6 : classify found = .h4) :
    (found ∈ scaffold substitution template ∧ classify found = .h4) ∨
      ∃ i ∈ holes template, Descendant (substitution i) found ∧ classify found = .h4 := by
  rcases descendant_decomposition substitution template occurs with hs | ⟨i, hi, ht⟩
  · exact Or.inl ⟨hs, h6⟩
  · exact Or.inr ⟨i, hi, ht, h6⟩

/-- A complete finite scaffold certificate lifts any inherited origin
predicate to every H6 occurrence after template instantiation. -/
theorem transfer (substitution : Nat → Term) (template : Template) (P : Term → Prop)
    (scaffoldOrigins : ∀ t ∈ scaffold substitution template, classify t = .h4 → P t)
    (holeOrigins : ∀ i ∈ holes template, ∀ t, Descendant (substitution i) t → classify t = .h4 → P t)
    {found : Term} (occurs : Descendant (instantiate substitution template) found)
    (h6 : classify found = .h4) : P found := by
  rcases h6_decomposition substitution template occurs h6 with ⟨hs, hh⟩ | ⟨i, hi, ht, hh⟩
  · exact scaffoldOrigins found hs hh
  · exact holeOrigins i hi found ht hh

end Template

#print axioms classify_h4_iff
#print axioms classify_compileActions
#print axioms response_endpoint
#print axioms Template.abstraction_exact
#print axioms Template.h6_decomposition
#print axioms Template.transfer
#print axioms completed_outer_carries
#print axioms rebuilt_outer_audit
end SOnlyProvenance
