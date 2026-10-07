import SOnlyProvenance

/-!
# Occurrence-value safety attached to actual response constructors

AllH6 transports a predicate on subtree values. These theorems do not maintain
address-indexed causal identities. The only additional root admitted by a
response-row certificate is its actual registered fresh response root. Arbitrary
hole contents require inherited certificates. Complete stage coverage and
labelled first-event exclusion remain separate obligations.
-/
namespace SOnlyProvenanceRows
open PureSFormal PureSFormal.PureS SOnlyProvenance
open SchedulerResponseInvariant

set_option maxHeartbeats 1000000

@[simp] theorem b_carries (P : Term → Prop) : AllH6 P b := by
  simp [b, AllH6, classify, delta]

@[simp] theorem p_carries (P : Term → Prop) : AllH6 P p := by
  simp [p, b, AllH6, classify, delta]

@[simp] theorem valueTag_carries (P : Term → Prop) (bit : Bool) :
    AllH6 P (valueTag bit) := by
  cases bit <;> simp [valueTag, v0, v1, C, b, AllH6, classify, delta]

@[simp] theorem live_carries (P : Term → Prop) (bit : Bool) :
    AllH6 P (live bit) :=
  app_no_new (b_carries P) (valueTag_carries P bit) (by decide)

@[simp] theorem appender_carries (P : Term → Prop) (bits : List Bool) :
    AllH6 P (appender bits) := by
  induction bits with
  | nil => exact p_carries P
  | cons bit rest ih => exact s_pair_carries (s_one_carries ih) (live_carries P bit)

@[simp] theorem selectedAction_carries (P : Term → Prop) (program : CTS.Program)
    (label : ActionLabel program) : AllH6 P (selectedAction program label) := by
  rcases label with ⟨phase, bit⟩
  cases bit <;> simp [selectedAction]

@[simp] theorem compileDispatcher_carries (P : Term → Prop) {Label : Type}
    (encode : Label → Term) (tree : Dispatcher.Tree Label)
    (leaves : ∀ label, AllH6 P (encode label)) :
    AllH6 P (compileDispatcher encode tree) := by
  induction tree with
  | leaf label => exact app_no_new (b_carries P) (leaves label) (by decide)
  | node l r ihl ihr => exact app_no_new (b_carries P) (s_pair_carries ihl ihr) (by decide)

@[simp] theorem compileActions_carries (P : Term → Prop) (program : CTS.Program)
    (tree : Dispatcher.Tree (ActionLabel program)) : AllH6 P (compileActions program tree) :=
  compileDispatcher_carries P _ _ (selectedAction_carries P program)

theorem live_fold_carries {P : Term → Prop} (bits : List Bool) (start : Term)
    (hs : AllH6 P start) :
    AllH6 P (bits.foldl (fun acc bit => .app (live bit) acc) start) := by
  induction bits generalizing start with
  | nil => exact hs
  | cons bit tail ih =>
      exact ih _ (app_no_new (live_carries P bit) hs (by simp))

@[simp] theorem word_carries (P : Term → Prop) (bits : List Bool) : AllH6 P (word bits) :=
  live_fold_carries bits _ (allH6_s P)

@[simp] theorem seed_carries (P : Term → Prop) (bits : List Bool) : AllH6 P (seedCode bits) :=
  s_one_carries (word_carries P bits)

@[simp] theorem environment_carries (P : Term → Prop) (program : CTS.Program)
    (tree : Dispatcher.Tree (ActionLabel program)) (bits : List Bool) :
    AllH6 P (environmentCode (compileActions program tree) bits) :=
  s_one_carries (s_pair_carries
    (s_pair_carries (haltCode_carries P) (compileActions_carries P program tree))
    (seed_carries P bits))

theorem other_app_carries {P : Term → Prop} {head arg : Term}
    (hh : AllH6 P head) (ha : AllH6 P arg) (hc : classify head = .other) :
    AllH6 P (.app head arg) := app_no_new hh ha (by simp [hc])

theorem other_app_class {head arg : Term} (h : classify head = .other) :
    classify (.app head arg) = .other := by simp [classify, h, delta]

theorem compiled_call_carries {P : Term → Prop} (program : CTS.Program)
    (tree : Dispatcher.Tree (ActionLabel program)) {carrier : Term}
    (hc : AllH6 P carrier) :
    AllH6 P (RouteGrammar.compiledCall (selectedAction program) tree carrier) :=
  other_app_carries (compileActions_carries P program tree) hc
    (classify_compileActions program tree)

theorem compiled_call_other (program : CTS.Program)
    (tree : Dispatcher.Tree (ActionLabel program)) (carrier : Term) :
    classify (RouteGrammar.compiledCall (selectedAction program) tree carrier) = .other :=
  other_app_class (classify_compileActions program tree)

theorem route_row_other {program : CTS.Program} {carrier : Term}
    {tree : Dispatcher.Tree (ActionLabel program)} {route : Dispatcher.Route}
    {label : ActionLabel program} {done : Bool} {term : Term}
    (progress : RouteMutation (selectedAction program) carrier tree route label done term)
    (hc : Endpoint carrier) : classify term = .other := by
  cases progress <;> apply chosen_other _ _ hc

/-- Every actual route intermediate is built only from inherited carrier
occurrences and H6-free literal action code. -/
theorem route_row_carries {P : Term → Prop} {program : CTS.Program} {carrier : Term}
    {tree : Dispatcher.Tree (ActionLabel program)} {route : Dispatcher.Route}
    {label : ActionLabel program} {done : Bool} {term : Term}
    (progress : RouteMutation (selectedAction program) carrier tree route label done term)
    (hc : AllH6 P carrier) (endpoint : Endpoint carrier) : AllH6 P term := by
  induction progress with
  | leaf label =>
      exact chosen_carries hc (other_app_carries (selectedAction_carries P program label) hc
        (classify_selectedAction program label))
  | @exposeLeft left right route label path =>
      apply chosen_carries hc
      apply other_app_carries (s_pair_carries
        (compileActions_carries P program left) (compileActions_carries P program right)) hc
      simp [classify, delta]
  | @exposeRight left right route label path =>
      apply chosen_carries hc
      apply other_app_carries (s_pair_carries
        (compileActions_carries P program left) (compileActions_carries P program right)) hc
      simp [classify, delta]
  | @selectLeft left right route label path =>
      exact chosen_carries hc (other_app_carries
        (compiled_call_carries program left hc) (compiled_call_carries program right hc)
        (compiled_call_other program left carrier))
  | @selectRight left right route label path =>
      exact chosen_carries hc (other_app_carries
        (compiled_call_carries program left hc) (compiled_call_carries program right hc)
        (compiled_call_other program left carrier))
  | @innerLeft left right route label done inner progress ih =>
      exact chosen_carries hc (other_app_carries ih
        (compiled_call_carries program right hc) (route_row_other progress endpoint))
  | @innerRight left right route label done inner progress ih =>
      exact chosen_carries hc (other_app_carries (compiled_call_carries program left hc)
        ih (compiled_call_other program left carrier))

theorem extend_carries {P : Term → Prop} (bit : Bool) {initial : Term}
    (hi : AllH6 P initial) : AllH6 P (extendAccumulator bit initial) :=
  other_app_carries (live_carries P bit) hi (classify_live bit)

theorem history_carries {P : Term → Prop} (bit : Bool) {initial : Term}
    (hi : AllH6 P initial) (endpoint : Endpoint initial) :
    AllH6 P (pushHistory bit initial) :=
  (endpoint_extension hi (extend_carries bit hi) endpoint).1

theorem pushFirst_other (bit : Bool) (rest : List Bool) (initial : Term) :
    classify (pushFirst bit rest initial) = .other := by
  simp [pushFirst, classify, delta]

theorem pushSecond_other (bit : Bool) (rest : List Bool) (initial : Term) :
    classify (pushSecond bit rest initial) = .other := by
  simp [pushSecond, classify, delta]

theorem pushFirst_carries {P : Term → Prop} (bit : Bool) (rest : List Bool)
    {initial : Term} (hi : AllH6 P initial) : AllH6 P (pushFirst bit rest initial) := by
  apply other_app_carries (s_pair_carries (appender_carries P rest) hi) (extend_carries bit hi)
  simp [classify, delta]

theorem pushSecond_carries {P : Term → Prop} (bit : Bool) (rest : List Bool)
    {initial : Term} (hi : AllH6 P initial) (endpoint : Endpoint initial) :
    AllH6 P (pushSecond bit rest initial) :=
  other_app_carries
    (other_app_carries (appender_carries P rest) (extend_carries bit hi) (classify_appender rest))
    (history_carries bit hi endpoint) (other_app_class (classify_appender rest))

/-- Both actual Push rows and every retained history are safe; arbitrary
old H6s in the initial carrier and outer history list remain inherited. -/
theorem action_row_carries {P : Term → Prop}
    {expected : Nat} {remaining : List Bool} {initial : Term} {outer : List Term}
    {done : Bool} {term : Term}
    (progress : ActionMutation expected remaining initial outer done term)
    (hi : AllH6 P initial) (endpoint : Endpoint initial)
    (ho : ∀ t ∈ outer, AllH6 P t) : AllH6 P term := by
  induction progress with
  | first bit rest initial outer count =>
      exact (applyArgs_other outer (pushFirst_carries bit rest hi)
        (pushFirst_other bit rest initial) ho).1
  | second bit rest initial outer count =>
      exact (applyArgs_other outer (pushSecond_carries bit rest hi endpoint)
        (pushSecond_other bit rest initial) ho).1
  | inner progress ih =>
      apply ih (extend_carries _ hi) (Or.inl (classify_liveCell _ _))
      intro t ht
      rcases List.mem_cons.mp ht with eq | ht
      · subst t
        exact history_carries _ hi endpoint
      · exact ho t ht

/-- C4 copies the actual predecessor into its new audit; an arbitrary new
unlicensed audit is never introduced by this theorem. -/
theorem c4_carries {P : Term → Prop} (bit : Bool) {predecessor : Term}
    (hp : AllH6 P predecessor) :
    AllH6 P (Carrier.tombstone bit predecessor predecessor) :=
  s_pair_carries hp (other_app_carries (valueTag_carries P bit) hp (classify_valueTag bit))


theorem withResponse_other {program : CTS.Program}
    {tree : Dispatcher.Tree (ActionLabel program)} {route : Dispatcher.Route}
    {label : ActionLabel program} (path : Dispatcher.HasRoute tree route label)
    (carrier response : Term) (endpoint : Endpoint carrier) :
    classify (PrimitiveRoute.withResponse (selectedAction program) tree route carrier response) = .other := by
  cases path <;> apply chosen_other _ _ endpoint

theorem withResponse_carries {P : Term → Prop} {program : CTS.Program}
    {tree : Dispatcher.Tree (ActionLabel program)} {route : Dispatcher.Route}
    {label : ActionLabel program} (path : Dispatcher.HasRoute tree route label)
    {carrier response : Term} (hc : AllH6 P carrier) (endpoint : Endpoint carrier)
    (hr : AllH6 P response) :
    AllH6 P (PrimitiveRoute.withResponse (selectedAction program) tree route carrier response) := by
  induction path with
  | leaf => exact chosen_carries hc hr
  | @left route label left right path ih =>
      exact chosen_carries hc (other_app_carries ih (compiled_call_carries program right hc)
        (withResponse_other path carrier response endpoint))
  | @right route label left right path ih =>
      exact chosen_carries hc (other_app_carries (compiled_call_carries program left hc) ih
        (compiled_call_other program left carrier))

theorem frameFirst_carries {P : Term → Prop} (program : CTS.Program)
    (tree : Dispatcher.Tree (ActionLabel program)) (bits : List Bool)
    {continuation carrier : Term} (hb : AllH6 P continuation)
    (bc : classify continuation = .other) (hv : AllH6 P carrier) :
    AllH6 P (frameFirstRoot (compileActions program tree) bits continuation carrier) := by
  have act : AllH6 P (actCode (compileActions program tree)) :=
    s_pair_carries (haltCode_carries P) (compileActions_carries P program tree)
  have dispatch : AllH6 P (dispatcherCode (compileActions program tree) bits) :=
    s_pair_carries act (seed_carries P bits)
  exact other_app_carries (other_app_carries dispatch hv (classify_dispatcher _ _))
    (other_app_carries hb hv bc) (other_app_class (classify_dispatcher _ _))

theorem frameSecond_carries {P : Term → Prop} (program : CTS.Program)
    (tree : Dispatcher.Tree (ActionLabel program)) (bits : List Bool)
    {continuation carrier : Term} (hb : AllH6 P continuation)
    (bc : classify continuation = .other) (hv : AllH6 P carrier) :
    AllH6 P (frameSecondRoot (compileActions program tree) bits continuation carrier) := by
  have act : AllH6 P (actCode (compileActions program tree)) :=
    s_pair_carries (haltCode_carries P) (compileActions_carries P program tree)
  have left := other_app_carries (other_app_carries act hv (classify_act _))
    (s_pair_carries (word_carries P bits) hv) (other_app_class (classify_act _))
  exact other_app_carries left (other_app_carries hb hv bc)
    (other_app_class (other_app_class (classify_act _)))

theorem activeShell_carries {P : Term → Prop} (bits : List Bool)
    {continuation carrier dispatch : Term}
    (hb : AllH6 P continuation) (bc : classify continuation = .other)
    (hv : AllH6 P carrier) (hd : AllH6 P dispatch)
    (registered : P (Carrier.activeShell bits continuation (freshHField carrier) dispatch carrier carrier)) :
    AllH6 P (Carrier.activeShell bits continuation (freshHField carrier) dispatch carrier carrier) :=
  fresh_shell_carries hv hd (s_pair_carries (word_carries P bits) hv)
    (other_app_carries hb hv bc) registered

/-- Every native FRAME/route/appender residual is covered by its actual pinned
constructor. The only additional licensed H6 value is the registered response
root itself; all other H6s must be inherited from input holes. -/
theorem response_row_carries {P : Term → Prop}
    {program : CTS.Program} {tree : Dispatcher.Tree (ActionLabel program)}
    {route : Dispatcher.Route} {label : ActionLabel program}
    {path : Dispatcher.HasRoute tree route label}
    {bits : List Bool} {continuation carrier term : Term} {done : Bool}
    (row : ResponseRootMutation program tree path bits continuation carrier done term)
    (hb : AllH6 P continuation) (bc : classify continuation = .other)
    (hv : AllH6 P carrier) (endpoint : Endpoint carrier)
    (registered : classify term = .h4 → P term) : AllH6 P term := by
  cases row with
  | frameFirst => exact frameFirst_carries program tree bits hb bc hv
  | frameSecond => exact frameSecond_carries program tree bits hb bc hv
  | frameThird =>
      exact activeShell_carries bits hb bc hv
        (other_app_carries (compileActions_carries P program tree) hv
          (classify_compileActions program tree)) (registered rfl)
  | routeIncomplete progress =>
      exact activeShell_carries bits hb bc hv (route_row_carries progress hv endpoint) (registered rfl)
  | routeCompleteEmpty progress empty =>
      exact activeShell_carries bits hb bc hv (route_row_carries progress hv endpoint) (registered rfl)
  | routeCompleteNonempty first rest progress nonempty =>
      exact activeShell_carries bits hb bc hv (route_row_carries progress hv endpoint) (registered rfl)
  | action progress =>
      exact activeShell_carries bits hb bc hv
        (withResponse_carries path hv endpoint
          (action_row_carries progress hv endpoint (by simp))) (registered rfl)

theorem allH6_of_descendants {P : Term → Prop} (source : Term)
    (licensed : ∀ found, Descendant source found → classify found = .h4 → P found) :
    AllH6 P source := by
  induction source with
  | s => trivial
  | app l r ihl ihr =>
      exact ⟨ihl (fun found h => licensed found (.left h)),
        ihr (fun found h => licensed found (.right h)),
        licensed (.app l r) (.root _)⟩

theorem allH6_descendant {P : Term → Prop} {source found : Term}
    (licensed : AllH6 P source) (occurs : Descendant source found)
    (h6 : classify found = .h4) : P found := by
  induction occurs with
  | root t =>
      cases t with
      | s => cases h6
      | app l r => exact licensed.2.2 h6
  | left h ih => exact ih licensed.1 h6
  | right h ih => exact ih licensed.2.1 h6

/-- An explicit value-containment conclusion, without an assumed origin
predicate. This is still not address-indexed causal-history tracking. -/
theorem response_h6_inherited_or_root
    {program : CTS.Program} {tree : Dispatcher.Tree (ActionLabel program)}
    {route : Dispatcher.Route} {label : ActionLabel program}
    {path : Dispatcher.HasRoute tree route label}
    {bits : List Bool} {continuation carrier term found : Term} {done : Bool}
    (row : ResponseRootMutation program tree path bits continuation carrier done term)
    (bc : classify continuation = .other) (endpoint : Endpoint carrier)
    (occurs : Descendant term found) (h6 : classify found = .h4) :
    Descendant continuation found ∨ Descendant carrier found ∨ found = term := by
  let P := fun t => Descendant continuation t ∨ Descendant carrier t ∨ t = term
  have hb : AllH6 P continuation := allH6_of_descendants continuation (fun _ h _ => Or.inl h)
  have hv : AllH6 P carrier := allH6_of_descendants carrier (fun _ h _ => Or.inr (Or.inl h))
  have hr : AllH6 P term := response_row_carries row hb bc hv endpoint
    (fun _ => Or.inr (Or.inr rfl))
  exact allH6_descendant hr occurs h6

/-- Every H6 response root has its literal input carrier at LLLR. -/
theorem response_root_audit
    {program : CTS.Program} {tree : Dispatcher.Tree (ActionLabel program)}
    {route : Dispatcher.Route} {label : ActionLabel program}
    {path : Dispatcher.HasRoute tree route label}
    {bits : List Bool} {continuation carrier term : Term} {done : Bool}
    (row : ResponseRootMutation program tree path bits continuation carrier done term)
    (h6 : classify term = .h4) :
    term.subterm? [.left, .left, .left, .right] = some carrier := by
  cases row with
  | frameFirst => have impossible : State.other = .h4 := h6; cases impossible
  | frameSecond => have impossible : State.other = .h4 := h6; cases impossible
  | frameThird => simp [freshLocal, Term.applyArgs, Term.subterm?]
  | routeIncomplete progress => simp [Carrier.activeShell, Carrier.shell, freshHField, Term.subterm?]
  | routeCompleteEmpty progress empty => simp [Carrier.activeShell, Carrier.shell, freshHField, Term.subterm?]
  | routeCompleteNonempty first rest progress nonempty => simp [Carrier.activeShell, Carrier.shell, freshHField, Term.subterm?]
  | action progress => simp [Carrier.activeShell, Carrier.shell, freshHField, Term.subterm?]


/-! ## Literal rebuilding contexts -/

theorem pending_carries {P : Term → Prop} (program : CTS.Program)
    (tree : Dispatcher.Tree (ActionLabel program)) (bits : List Bool)
    {continuation body : Term} (hb : AllH6 P continuation) (ht : AllH6 P body) :
    AllH6 P (frame (environmentCode (compileActions program tree) bits) continuation body) :=
  other_app_carries
    (other_app_carries (environment_carries P program tree bits) hb (classify_environment _ _))
    ht (other_app_class (classify_environment _ _))

/-- The direct active queue and retained beta may contain arbitrary previously
certified H6s. The literal fixed-code scaffold manufactures none. -/
theorem mutableBase_carries {P : Term → Prop} (program : CTS.Program)
    (tree : Dispatcher.Tree (ActionLabel program)) (bits : List Bool)
    {continuation queue beta : Term} (hb : AllH6 P continuation)
    (bc : classify continuation = .other) (hq : AllH6 P queue) (hbeta : AllH6 P beta) :
    AllH6 P (MutableBase.base (compileActions program tree) bits continuation queue beta) := by
  have act : AllH6 P (actCode (compileActions program tree)) :=
    s_pair_carries (haltCode_carries P) (compileActions_carries P program tree)
  have active : AllH6 P (MutableBase.activeEnvironment (compileActions program tree) queue) :=
    s_one_carries (s_pair_carries act (s_one_carries hq))
  have activeOther : classify (MutableBase.activeEnvironment (compileActions program tree) queue) = .other := rfl
  have dormant : AllH6 P (.app b (environmentCode (compileActions program tree) bits)) :=
    app_no_new (b_carries P) (environment_carries P program tree bits) (by decide)
  have alpha : AllH6 P (MutableBase.activeAlpha (compileActions program tree) bits continuation queue) :=
    other_app_carries (other_app_carries active dormant activeOther) hb (other_app_class activeOther)
  exact other_app_carries (other_app_carries hb alpha bc) hbeta (other_app_class bc)

/-- Queue-context rebuilding preserves old independent audit certificates. -/
theorem tombstone_context_carries {P : Term → Prop} (bit : Bool)
    {predecessor audit : Term} (hp : AllH6 P predecessor) (ha : AllH6 P audit) :
    AllH6 P (Carrier.tombstone bit predecessor audit) :=
  s_pair_carries hp (other_app_carries (valueTag_carries P bit) ha (classify_valueTag bit))

/-- Exact canonical action context, including an arbitrary-length retained
history list; the mutable accumulator hole need not be H6-free. -/
theorem action_context_carries {P : Term → Prop} (histories : List Term)
    {accumulator : Term} (ha : AllH6 P accumulator)
    (hh : ∀ t ∈ histories, AllH6 P t) :
    AllH6 P ((CanonicalTraversal.actionContext histories).plug accumulator) := by
  rw [CanonicalTraversal.actionContext_plug]
  exact (applyArgs_other histories
    (other_app_carries (p_carries P) ha classify_p)
    (other_app_class classify_p) hh).1

/-- Actual completed-shell syntax, with a rebuilt continuation child. The
existing root's label/audit-origin rule is supplied explicitly as registered. -/
theorem completed_context_carries {P : Term → Prop} (bits : List Bool)
    {snapshot dispatch seedAudit endpoint continuationAudit : Term}
    (hs : AllH6 P snapshot) (hd : AllH6 P dispatch) (hsa : AllH6 P seedAudit)
    (he : AllH6 P endpoint) (hca : AllH6 P continuationAudit) (safe : Endpoint endpoint)
    (registered : P (Carrier.completedShell bits (freshHField snapshot)
      dispatch seedAudit endpoint continuationAudit)) :
    AllH6 P (Carrier.completedShell bits (freshHField snapshot)
      dispatch seedAudit endpoint continuationAudit) :=
  completed_outer_carries hs hd (word_carries P bits) hsa he hca safe registered

/-- Endpoint discipline can be iterated through arbitrarily many literal
pending/completed ancestors; internal H5 prefixes are not whole endpoints. -/
inductive OuterContext (P : Term → Prop) : Context → Prop
  | hole : OuterContext P .hole
  | pending {inner : Context} (program : CTS.Program)
      (tree : Dispatcher.Tree (ActionLabel program)) (bits : List Bool)
      (continuation : Term) (hb : AllH6 P continuation)
      (inside : OuterContext P inner) :
      OuterContext P (.appRight (.app (environmentCode (compileActions program tree) bits)
        continuation) inner)
  | completed {inner : Context} (bits : List Bool)
      (snapshot dispatch seedAudit continuationAudit : Term)
      (hs : AllH6 P snapshot) (hd : AllH6 P dispatch)
      (hsa : AllH6 P seedAudit) (hca : AllH6 P continuationAudit)
      (registered : ∀ endpoint, Endpoint endpoint →
        P (Carrier.completedShell bits (freshHField snapshot)
          dispatch seedAudit endpoint continuationAudit))
      (inside : OuterContext P inner) :
      OuterContext P (.appRight
        (.app (.app (freshHField snapshot) dispatch) (.app (seedCode bits) seedAudit))
        (.appLeft inner continuationAudit))

/-- A constructor induction over complete rebuilt ancestor chains. It requires
the chain's own independent audit/root licenses and hence cannot be obtained
from an unrestricted public CompletedParents inhabitant alone. -/
theorem outer_context_carries {P : Term → Prop} {context : Context}
    (outer : OuterContext P context) {endpoint : Term}
    (he : AllH6 P endpoint) (safe : Endpoint endpoint) :
    AllH6 P (context.plug endpoint) ∧ Endpoint (context.plug endpoint) := by
  induction outer with
  | hole => exact ⟨he, safe⟩
  | @pending inner program tree bits continuation hb inside ih =>
      exact ⟨pending_carries program tree bits hb ih.1,
        Or.inl (classify_frame _ _ continuation _)⟩
  | @completed inner bits snapshot dispatch seedAudit continuationAudit hs hd hsa hca registered inside ih =>
      exact ⟨completed_context_carries bits hs hd hsa ih.1 hca ih.2
        (registered _ ih.2), Or.inr rfl⟩

#print axioms route_row_carries
#print axioms action_row_carries
#print axioms response_row_carries
#print axioms response_h6_inherited_or_root
#print axioms response_root_audit
#print axioms c4_carries
#print axioms mutableBase_carries
#print axioms action_context_carries
#print axioms outer_context_carries
end SOnlyProvenanceRows
