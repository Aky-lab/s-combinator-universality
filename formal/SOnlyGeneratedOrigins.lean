import SOnlyProvenanceRows
import SOnlyEventPattern
import SOnlyEventTransfer

/-!
# Extensional generated-origin invariant

A license constrains every fresh completed Local's exact label and literal
LLLR snapshot. It does not assert address-indexed causal identity. Local
preservation theorems below are attached to pinned response and selected-C4
constructors. Global job/stage closure is a separate conclusion, never a
premise disguised as a generated-origin assumption.
-/
namespace SOnlyGeneratedOrigins
open PureSFormal PureSFormal.PureS SOnlyProvenance SOnlyProvenanceRows
open CanonicalTraversal
set_option maxHeartbeats 3000000

abbrev OriginSet (program : CTS.Program) := ActionLabel program → Term → Prop

def RootLicensed (program : CTS.Program) (tree : Dispatcher.Tree (ActionLabel program))
    (allowed : OriginSet program) (term : Term) : Prop :=
  ∀ view, CheckpointDecoder.LocalShape program tree view term → view.status = .fresh →
    ∃ snapshot, term.subterm? SOnlyEventTransfer.auditAddress = some snapshot ∧
      allowed view.label snapshot

abbrev Licensed (program : CTS.Program) (tree : Dispatcher.Tree (ActionLabel program))
    (allowed : OriginSet program) (term : Term) := AllH6 (RootLicensed program tree allowed) term

/-- Parser uniqueness turns an actual exact-provenance completed root into
precisely one label/snapshot origin obligation. -/
theorem completed_root_licensed_iff
    {program : CTS.Program} {tree : Dispatcher.Tree (ActionLabel program)}
    (allowed : OriginSet program) (bits : List Bool)
    {snapshot dispatch accumulator continuation : Term}
    {route : Dispatcher.Route} {label : ActionLabel program}
    (shape : ReachableAudit.SnapshotDispatchAt program tree snapshot route label accumulator dispatch) :
    RootLicensed program tree allowed (LocalResponse.completed bits continuation snapshot dispatch) ↔
      allowed label snapshot := by
  constructor
  · intro licensed
    obtain ⟨actual, audit, ha⟩ := licensed _ (CheckpointDecoder.localShape_completed bits shape) rfl
    have eq : snapshot = actual := Option.some.inj
      ((SOnlyEventTransfer.completed_audit bits continuation snapshot dispatch).symm.trans audit)
    subst actual
    exact ha
  · intro ha view viewShape fresh
    have eq := Option.some.inj ((CheckpointDecoder.parseLocal?_complete viewShape).symm.trans
      (CheckpointDecoder.parseLocal?_completed bits shape))
    subst view
    exact ⟨snapshot, SOnlyEventTransfer.completed_audit _ _ _ _, ha⟩

/-- Every incomplete response root is vacuously licensed because the actual
local parser rejects it, not because its wildcard payloads are assumed safe. -/
theorem rejected_root_licensed
    {program : CTS.Program} {tree : Dispatcher.Tree (ActionLabel program)}
    (allowed : OriginSet program) {term : Term}
    (rejected : CheckpointDecoder.parseLocal? program tree term = none) :
    RootLicensed program tree allowed term := by
  intro view shape _
  have accepted := CheckpointDecoder.parseLocal?_complete shape
  rw [rejected] at accepted
  cases accepted

/-- Actual response intermediates introduce only their exact source label and
post-deletion snapshot. The old root-registration premise is discharged here. -/
theorem response_root_licensed
    {program : CTS.Program} {tree : Dispatcher.Tree (ActionLabel program)}
    (allowed : OriginSet program) {route : Dispatcher.Route} {label : ActionLabel program}
    {path : Dispatcher.HasRoute tree route label}
    {bits : List Bool} {continuation carrier term : Term} {done : Bool}
    (row : SchedulerResponseInvariant.ResponseRootMutation program tree path bits continuation carrier done term)
    (admissible : Carrier.Admissible continuation)
    (snapshotInv : ReachableAudit.Holds program tree bits continuation carrier)
    (origin : allowed label carrier) : RootLicensed program tree allowed term := by
  cases flag : done with
  | false => exact rejected_root_licensed allowed (row.failure admissible snapshotInv flag).localBoundary
  | true =>
      rw [row.done_eq flag]
      have shape : ReachableAudit.SnapshotDispatchAt program tree carrier route label
          (actionAccumulator program label carrier)
          (PrimitiveLocalResponse.completedRoute program tree route label carrier) := by
        refine ⟨?_⟩
        simpa [PrimitiveLocalResponse.completedRoute, ReachableAudit.actionResponse_initial] using
          SchedulerResponse.withResponse_snapshotRoute path carrier (actionResult program label carrier)
      exact (completed_root_licensed_iff allowed bits shape).mpr origin

/-- Full actual response rows, with inherited holes and a genuine current
label/snapshot origin, are globally licensed at every descendant. -/
theorem response_licensed
    {program : CTS.Program} {tree : Dispatcher.Tree (ActionLabel program)}
    (allowed : OriginSet program) {route : Dispatcher.Route} {label : ActionLabel program}
    {path : Dispatcher.HasRoute tree route label}
    {bits : List Bool} {continuation carrier term : Term} {done : Bool}
    (row : SchedulerResponseInvariant.ResponseRootMutation program tree path bits continuation carrier done term)
    (admissible : Carrier.Admissible continuation)
    (snapshotInv : ReachableAudit.Holds program tree bits continuation carrier)
    (hb : Licensed program tree allowed continuation) (bc : classify continuation = .other)
    (hv : Licensed program tree allowed carrier) (endpoint : Endpoint carrier)
    (origin : allowed label carrier) : Licensed program tree allowed term :=
  response_row_carries row hb bc hv endpoint
    (fun _ => response_root_licensed allowed row admissible snapshotInv origin)

/-- A carrier's public Holds certificate gives Endpoint once its actual clock
continuation has Other state; no claim about unrelated audit contents follows. -/
theorem holds_endpoint
    {program : CTS.Program} {tree : Dispatcher.Tree (ActionLabel program)}
    {bits : List Bool} {continuation carrier : Term}
    (bc : classify continuation = .other)
    (held : ReachableAudit.Holds program tree bits continuation carrier) : Endpoint carrier := by
  cases held with
  | base queue =>
      exact Or.inl (by simp [MutableBase.mutableBase, MutableBase.base, classify, bc, delta])
  | @«local» snapshot current accumulator result dispatch status route label snapshotInv currentInv between layer =>
      rw [layer.result_eq]
      cases status with
      | fresh => exact Or.inr rfl
      | marked =>
          left
          cases hs : classify snapshot <;>
            simp [ReachableAudit.haltField, Carrier.activeShell, Carrier.shell,
              Carrier.markedHField, haltTag, b, classify, hs, delta]

/-! ## Context replacement preserves inherited subtree-value certificates -/

def Preserves (P : Term → Prop) (context : Context) : Prop :=
  ∀ old new, AllH6 P (context.plug old) → AllH6 P new → AllH6 P (context.plug new)

theorem context_inner {P : Term → Prop} (context : Context) (term : Term)
    (h : AllH6 P (context.plug term)) : AllH6 P term := by
  induction context with
  | hole => exact h
  | appLeft inner right ih => exact ih h.1
  | appRight left inner ih => exact ih h.2.1

theorem preserves_hole (P : Term → Prop) : Preserves P .hole := by
  intro old new _ hn
  exact hn

theorem preserves_comp {P : Term → Prop} {outer inner : Context}
    (ho : Preserves P outer) (hi : Preserves P inner) : Preserves P (outer.comp inner) := by
  intro old new source target
  rw [Context.plug_comp] at source ⊢
  exact ho _ _ source (hi _ _ (context_inner outer _ source) target)

theorem queue_context_preserves {P : Term → Prop} {context : Context} {bits : List Bool}
    (queue : QueueContext context bits) : Preserves P context := by
  induction queue with
  | hole => exact preserves_hole P
  | live bit inner ih =>
      intro old new source target
      exact extend_carries bit (ih old new source.2.1 target)
  | tombstone bit audit inner ih =>
      intro old new source target
      exact tombstone_context_carries bit (ih old new source.1.2.1 target) source.2.1.2.1

theorem all_applyArgs_parts {P : Term → Prop} (head : Term) (args : List Term)
    (h : AllH6 P (Term.applyArgs head args)) :
    AllH6 P head ∧ ∀ t ∈ args, AllH6 P t := by
  induction args generalizing head with
  | nil => exact ⟨h, by simp⟩
  | cons arg tail ih =>
      have parts := ih (.app head arg) h
      refine ⟨parts.1.1, ?_⟩
      intro t ht
      rcases List.mem_cons.mp ht with eq | ht
      · subst t
        exact parts.1.2.1
      · exact parts.2 t ht

theorem action_context_preserves (P : Term → Prop) (histories : List Term) :
    Preserves P (actionContext histories) := by
  intro old new source target
  rw [actionContext_plug] at source
  exact action_context_carries histories target (all_applyArgs_parts _ _ source).2

theorem route_context_other
    {program : CTS.Program} {snapshot : Term} {tree : Dispatcher.Tree (ActionLabel program)}
    {route : Dispatcher.Route} {label : ActionLabel program} {context : Context}
    (selected : RouteContext (selectedAction program) snapshot tree route label context)
    (endpoint : Endpoint snapshot) (response : Term) : classify (context.plug response) = .other := by
  cases selected <;> apply chosen_other _ _ endpoint

theorem route_context_preserves {P : Term → Prop}
    {program : CTS.Program} {snapshot : Term} {tree : Dispatcher.Tree (ActionLabel program)}
    {route : Dispatcher.Route} {label : ActionLabel program} {context : Context}
    (selected : RouteContext (selectedAction program) snapshot tree route label context)
    (endpoint : Endpoint snapshot) : Preserves P context := by
  induction selected with
  | leaf label =>
      intro old new source target
      exact chosen_carries source.1.2.1 target
  | @left left right route label inner selected ih =>
      intro old new source target
      exact chosen_carries source.1.2.1
        (other_app_carries (ih old new source.2.1.1 target) source.2.1.2.1
          (route_context_other selected endpoint new))
  | @right left right route label inner selected ih =>
      intro old new source target
      exact chosen_carries source.1.2.1
        (other_app_carries source.2.1.1 (ih old new source.2.1.2.1 target)
          (compiled_call_other program left snapshot))

end SOnlyGeneratedOrigins
