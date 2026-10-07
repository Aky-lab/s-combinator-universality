import SOnlySchedulerOrigins
import PureSFormal.PureS.SchedulerCompletedContext

/-!
# Generated completed ancestors preserve literal origin licenses

Actual fresh and marked continuation-parent constructors preserve licenses for
any certified endpoint, including an H6 endpoint. The upward-closed parent
certificate permits extending the allowed origin set at the next response.
-/
namespace SOnlyGlobalAncestors
open PureSFormal PureSFormal.PureS SOnlyProvenance SOnlyProvenanceRows
open SOnlyGeneratedOrigins SOnlySchedulerOrigins
open SchedulerControl SchedulerInvariant
set_option maxHeartbeats 3000000

/-- An executed appender retains only licensed input values and histories. -/
theorem appenderResult_ordinary {P : Term → Prop} (bits : List Bool)
    {initial : Term} (hi : AllH6 P initial) (safe : Endpoint initial) :
    Ordinary P (appenderResult bits initial) := by
  induction bits generalizing initial with
  | nil => exact ordinary_app ⟨p_carries P, classify_p⟩ hi
  | cons bit rest ih =>
      rw [appenderResult_cons]
      exact ordinary_app (ih (extend_carries bit hi)
        (Or.inl (classify_liveCell bit initial))) (history_carries bit hi safe)

theorem actionResult_ordinary {P : Term → Prop} (program : CTS.Program)
    (label : ActionLabel program) {initial : Term}
    (hi : AllH6 P initial) (safe : Endpoint initial) :
    Ordinary P (actionResult program label initial) := by
  rcases label with ⟨phase, bit⟩
  cases bit with
  | false => exact ordinary_app ⟨p_carries P, classify_p⟩ hi
  | true => exact appenderResult_ordinary _ hi safe

theorem completedRoute_ordinary {P : Term → Prop} (program : CTS.Program)
    (dispatcher : ActionDispatcher program) (registers : Registers program)
    (bit : Bool) {carrier : Term} (hv : AllH6 P carrier) (safe : Endpoint carrier) :
    Ordinary P (SchedulerResponse.completedRoute program dispatcher registers bit carrier) := by
  exact ⟨withResponse_carries (dispatcher.route_valid (registers.phase, bit)) hv safe
      (actionResult_ordinary program (registers.phase, bit) hv safe).1,
    withResponse_other (dispatcher.route_valid (registers.phase, bit)) _ _ safe⟩

/-- The continuation may itself be a completed fresh Local. Only Endpoint,
not the narrower Other state, is needed at its literal audit application. -/
theorem completed_licensed (program : CTS.Program)
    (dispatcher : ActionDispatcher program) (allowed : OriginSet program)
    (registers : Registers program) (bit : Bool) (bits : List Bool)
    {continuation carrier : Term}
    (hb : Licensed program dispatcher.tree allowed continuation)
    (continuationSafe : Endpoint continuation)
    (hv : Licensed program dispatcher.tree allowed carrier) (carrierSafe : Endpoint carrier)
    (origin : allowed (registers.phase, bit) carrier) :
    Licensed program dispatcher.tree allowed
      (LocalResponse.completed bits continuation carrier
        (SchedulerResponse.completedRoute program dispatcher registers bit carrier)) := by
  have registered := (completed_root_licensed_iff allowed bits (continuation := continuation)
    (SchedulerResponse.completedRoute_snapshotDispatch program dispatcher registers bit carrier)).mpr origin
  exact fresh_shell_carries hv
    (completedRoute_ordinary program dispatcher registers bit hv carrierSafe).1
    (s_pair_carries (word_carries _ bits) hv)
    (endpoint_extension hb hv continuationSafe).1 registered

/-- Literal fresh continuation ancestors retain their own exact label/audit
license while accepting every licensed whole continuation endpoint. -/
theorem freshContinuationParents_wraps (program : CTS.Program)
    (dispatcher : ActionDispatcher program) (allowed : OriginSet program)
    (registers : Registers program) (bit : Bool) (bits : List Bool)
    {carrier : Term} {parents : List ParentFrame}
    (outer : Wraps (RootLicensed program dispatcher.tree allowed) parents)
    (hv : Licensed program dispatcher.tree allowed carrier) (safe : Endpoint carrier)
    (origin : allowed (registers.phase, bit) carrier) :
    Wraps (RootLicensed program dispatcher.tree allowed)
      (SchedulerRootContinuation.freshContinuationParents program dispatcher
        registers bit bits carrier parents) := by
  intro endpoint endpointSafe licensed
  rw [SchedulerCompletedContext.CompletedParents.rebuild_freshContinuationParents]
  exact outer _ (Or.inr rfl)
    (completed_licensed program dispatcher allowed registers bit bits licensed endpointSafe hv safe origin)

/-- Marking changes the reserved head to an ordinary head without creating
any fresh H6 value in the copied carrier fields. -/
theorem markedHField_ordinary {P : Term → Prop} {left right : Term}
    (hl : AllH6 P left) (hr : AllH6 P right) :
    Ordinary P (Carrier.markedHField left right) := by
  constructor
  · exact s_pair_carries hl (app_no_new
      (by simp [haltTag, b, AllH6, classify, delta]) hr (by decide))
  · cases hc : classify left <;>
      simp [Carrier.markedHField, haltTag, b, classify, hc, delta]

theorem markedCompleted_ordinary {P : Term → Prop} (bits : List Bool)
    {continuation carrier dispatch : Term}
    (hv : AllH6 P carrier) (hd : AllH6 P dispatch)
    (call : AllH6 P (.app continuation carrier)) :
    Ordinary P (LocalResponse.markedCompleted bits continuation carrier dispatch) :=
  ordinary_app (ordinary_app (ordinary_app (markedHField_ordinary hv hv) hd)
    (s_pair_carries (word_carries P bits) hv)) call

/-- Licensing the old complete shell suffices to license its actual marker
sample; the old root registration is not reused as a new fresh birth. -/
theorem markedCompleted_of_completed {P : Term → Prop} (bits : List Bool)
    {continuation carrier dispatch : Term}
    (fresh : AllH6 P (LocalResponse.completed bits continuation carrier dispatch)) :
    Ordinary P (LocalResponse.markedCompleted bits continuation carrier dispatch) := by
  exact markedCompleted_ordinary bits fresh.1.1.1.2.1 fresh.1.1.2.1 fresh.2.1

theorem markedContinuationParents_wraps {P : Term → Prop} (program : CTS.Program)
    (dispatcher : ActionDispatcher program) (registers : Registers program)
    (bit : Bool) (bits : List Bool) {carrier : Term} {parents : List ParentFrame}
    (outer : Wraps P parents) (hv : AllH6 P carrier) (safe : Endpoint carrier) :
    Wraps P (SchedulerRootContinuation.markedContinuationParents program dispatcher
      registers bit bits carrier parents) := by
  intro endpoint endpointSafe licensed
  rw [SchedulerCompletedContext.CompletedParents.rebuild_markedContinuationParents]
  have marked := markedCompleted_ordinary bits hv
    (completedRoute_ordinary program dispatcher registers bit hv safe).1
    (endpoint_extension licensed hv endpointSafe).1
  exact outer _ (Or.inl marked.2) marked.1

/-- A licensed old completed response also supplies all retained marked-parent
holes directly, without re-executing its route proof. -/
theorem markedContinuationParents_wraps_of_completed {P : Term → Prop}
    (program : CTS.Program) (dispatcher : ActionDispatcher program)
    (registers : Registers program) (bit : Bool) (bits : List Bool)
    (continuation carrier : Term) {parents : List ParentFrame}
    (outer : Wraps P parents)
    (fresh : AllH6 P (LocalResponse.completed bits continuation carrier
      (SchedulerResponse.completedRoute program dispatcher registers bit carrier))) :
    Wraps P (SchedulerRootContinuation.markedContinuationParents program dispatcher
      registers bit bits carrier parents) := by
  intro endpoint endpointSafe licensed
  rw [SchedulerCompletedContext.CompletedParents.rebuild_markedContinuationParents]
  have hv : AllH6 P carrier := fresh.1.1.1.2.1
  have hd := fresh.1.1.2.1
  have marked := markedCompleted_ordinary bits hv hd
    (endpoint_extension licensed hv endpointSafe).1
  exact outer _ (Or.inl marked.2) marked.1

/-- The literal registered marker configuration, including every old parent. -/
theorem normalMarker_licensed_of_completed {P : Term → Prop} (program : CTS.Program)
    (dispatcher : ActionDispatcher program) (registers : Registers program)
    (bit : Bool) (bits : List Bool) (continuation carrier : Term)
    (parents : List ParentFrame) (outer : Wraps P parents)
    (fresh : AllH6 P (LocalResponse.completed bits continuation carrier
      (SchedulerResponse.completedRoute program dispatcher registers bit carrier))) :
    AllH6 P (SchedulerRootContinuation.normalMarkerMutationConfiguration program
      dispatcher registers bit bits continuation carrier parents).cursor.erase := by
  rw [SchedulerRootContinuation.normalMarkerMutation_erase]
  have marked := markedCompleted_of_completed bits fresh
  exact outer _ (Or.inl marked.2) marked.1

theorem normalMarker_licensed {P : Term → Prop} (program : CTS.Program)
    (dispatcher : ActionDispatcher program) (registers : Registers program)
    (bit : Bool) (bits : List Bool) (continuation carrier : Term)
    (parents : List ParentFrame) (outer : Wraps P parents)
    (hb : AllH6 P continuation) (continuationSafe : Endpoint continuation)
    (hv : AllH6 P carrier) (carrierSafe : Endpoint carrier) :
    AllH6 P (SchedulerRootContinuation.normalMarkerMutationConfiguration program
      dispatcher registers bit bits continuation carrier parents).cursor.erase := by
  rw [SchedulerRootContinuation.normalMarkerMutation_erase]
  have marked := markedCompleted_ordinary bits hv
    (completedRoute_ordinary program dispatcher registers bit hv carrierSafe).1
    (endpoint_extension hb hv continuationSafe).1
  exact outer _ (Or.inl marked.2) marked.1

/-- The EMPTY marker has the same literal term, selected by the false action. -/
theorem emptyMarker_licensed {P : Term → Prop} (program : CTS.Program)
    (dispatcher : ActionDispatcher program) (registers : Registers program)
    (bits : List Bool) (continuation carrier : Term) (parents : List ParentFrame)
    (outer : Wraps P parents)
    (hb : AllH6 P continuation) (continuationSafe : Endpoint continuation)
    (hv : AllH6 P carrier) (carrierSafe : Endpoint carrier) :
    AllH6 P (SchedulerRootContinuation.emptyMarkerMutationConfiguration program
      dispatcher registers bits continuation carrier parents).cursor.erase :=
  normalMarker_licensed program dispatcher registers false bits continuation carrier
    parents outer hb continuationSafe hv carrierSafe

/-- Every focus inherits the whole rebuilt term's subtree-value license. -/
theorem rebuild_inner {P : Term → Prop} (parents : List ParentFrame) (focus : Term)
    (whole : AllH6 P (Cursor.rebuild parents focus)) : AllH6 P focus := by
  induction parents generalizing focus with
  | nil => exact whole
  | cons parent parents ih =>
      have inner := ih (parent.fill focus) whole
      cases parent with
      | left right => exact inner.1
      | right left => exact inner.2.1

theorem normalMarker_licensed_of_erase {P : Term → Prop} (program : CTS.Program)
    (dispatcher : ActionDispatcher program) (registers : Registers program)
    (bit : Bool) (bits : List Bool) (continuation carrier : Term)
    (parents : List ParentFrame) (outer : Wraps P parents)
    (fresh : AllH6 P (SchedulerResponse.completedCursor program dispatcher
      registers bit bits continuation carrier parents).erase) :
    AllH6 P (SchedulerRootContinuation.normalMarkerMutationConfiguration program
      dispatcher registers bit bits continuation carrier parents).cursor.erase :=
  normalMarker_licensed_of_completed program dispatcher registers bit bits
    continuation carrier parents outer (rebuild_inner parents _ fresh)

private theorem licensed_weaken {program : CTS.Program}
    {tree : Dispatcher.Tree (ActionLabel program)} {allowed larger : OriginSet program}
    (included : ∀ label snapshot, allowed label snapshot → larger label snapshot)
    {term : Term} (licensed : Licensed program tree allowed term) :
    Licensed program tree larger term := by
  induction term with
  | s => trivial
  | app left right ihl ihr =>
      refine ⟨ihl licensed.1, ihr licensed.2.1, ?_⟩
      intro h6 view shape fresh
      obtain ⟨snapshot, audit, origin⟩ := licensed.2.2 h6 view shape fresh
      exact ⟨snapshot, audit, included _ _ origin⟩

/-- Upward closure is essential: an arbitrary single-predicate Wraps proof
cannot be transported when a later response adds a new licensed origin. -/
def LicensedParents (program : CTS.Program) (dispatcher : ActionDispatcher program)
    (allowed : OriginSet program) (parents : List ParentFrame) : Prop :=
  ∀ larger : OriginSet program,
    (∀ label snapshot, allowed label snapshot → larger label snapshot) →
      Wraps (RootLicensed program dispatcher.tree larger) parents

namespace LicensedParents

theorem wraps {program : CTS.Program} {dispatcher : ActionDispatcher program}
    {allowed : OriginSet program} {parents : List ParentFrame}
    (outer : LicensedParents program dispatcher allowed parents) :
    Wraps (RootLicensed program dispatcher.tree allowed) parents :=
  outer allowed (fun _ _ origin => origin)

theorem mono {program : CTS.Program} {dispatcher : ActionDispatcher program}
    {allowed larger : OriginSet program} {parents : List ParentFrame}
    (outer : LicensedParents program dispatcher allowed parents)
    (included : ∀ label snapshot, allowed label snapshot → larger label snapshot) :
    LicensedParents program dispatcher larger parents := by
  intro final inclusion
  exact outer final (fun label snapshot origin => inclusion _ _ (included label snapshot origin))

theorem nil (program : CTS.Program) (dispatcher : ActionDispatcher program)
    (allowed : OriginSet program) : LicensedParents program dispatcher allowed [] := by
  intro larger _
  exact wraps_nil _

theorem fresh {program : CTS.Program} {dispatcher : ActionDispatcher program}
    {allowed : OriginSet program} {parents : List ParentFrame}
    (outer : LicensedParents program dispatcher allowed parents)
    (registers : Registers program) (bit : Bool) (bits : List Bool) {carrier : Term}
    (hv : Licensed program dispatcher.tree allowed carrier) (safe : Endpoint carrier)
    (origin : allowed (registers.phase, bit) carrier) :
    LicensedParents program dispatcher allowed
      (SchedulerRootContinuation.freshContinuationParents program dispatcher
        registers bit bits carrier parents) := by
  intro larger inclusion
  exact freshContinuationParents_wraps program dispatcher larger registers bit bits
    (outer larger inclusion) (licensed_weaken inclusion hv) safe (inclusion _ _ origin)

theorem marked {program : CTS.Program} {dispatcher : ActionDispatcher program}
    {allowed : OriginSet program} {parents : List ParentFrame}
    (outer : LicensedParents program dispatcher allowed parents)
    (registers : Registers program) (bit : Bool) (bits : List Bool) {carrier : Term}
    (hv : Licensed program dispatcher.tree allowed carrier) (safe : Endpoint carrier) :
    LicensedParents program dispatcher allowed
      (SchedulerRootContinuation.markedContinuationParents program dispatcher
        registers bit bits carrier parents) := by
  intro larger inclusion
  exact markedContinuationParents_wraps program dispatcher registers bit bits
    (outer larger inclusion) (licensed_weaken inclusion hv) safe

theorem empty {program : CTS.Program} {dispatcher : ActionDispatcher program}
    {allowed : OriginSet program} {parents : List ParentFrame}
    (outer : LicensedParents program dispatcher allowed parents)
    (registers : Registers program) (bits : List Bool) {carrier : Term}
    (hv : Licensed program dispatcher.tree allowed carrier) (safe : Endpoint carrier) :
    LicensedParents program dispatcher allowed
      (SchedulerRootContinuation.emptyContinuationParents program dispatcher
        registers bits carrier parents) :=
  outer.marked registers false bits hv safe

theorem pending {program : CTS.Program} {dispatcher : ActionDispatcher program}
    {allowed : OriginSet program} {parents : List ParentFrame}
    (outer : LicensedParents program dispatcher allowed parents) (bits : List Bool)
    {continuation : Term} (hb : Licensed program dispatcher.tree allowed continuation)
    (depth : Nat) :
    LicensedParents program dispatcher allowed
      (PrimitiveFuel.pendingParents (environmentCode (compileActions program dispatcher.tree) bits)
        continuation depth parents) := by
  intro larger inclusion
  exact pending_wraps program dispatcher bits (licensed_weaken inclusion hb) (outer larger inclusion) depth

theorem left {program : CTS.Program} {dispatcher : ActionDispatcher program}
    {allowed : OriginSet program} {parents : List ParentFrame}
    (outer : LicensedParents program dispatcher allowed parents) {audit : Term}
    (ha : Licensed program dispatcher.tree allowed audit) :
    LicensedParents program dispatcher allowed (.left audit :: parents) := by
  intro larger inclusion
  exact wraps_left (outer larger inclusion) (licensed_weaken inclusion ha)

theorem right {program : CTS.Program} {dispatcher : ActionDispatcher program}
    {allowed : OriginSet program} {parents : List ParentFrame}
    (outer : LicensedParents program dispatcher allowed parents) {head : Term}
    (hh : Licensed program dispatcher.tree allowed head) (hc : classify head = .other) :
    LicensedParents program dispatcher allowed (.right head :: parents) := by
  intro larger inclusion
  exact wraps_right (outer larger inclusion) (licensed_weaken inclusion hh) hc

theorem clock_wrappers {program : CTS.Program} {dispatcher : ActionDispatcher program}
    {allowed : OriginSet program} {parents : List ParentFrame}
    (outer : LicensedParents program dispatcher allowed parents) (stage wrappers : Nat) :
    LicensedParents program dispatcher allowed
      (PrimitiveClock.wrapperParents stage wrappers parents) := by
  intro larger inclusion
  exact clock_wrappers_wraps (outer larger inclusion) stage wrappers

end LicensedParents

#print axioms completed_licensed
#print axioms freshContinuationParents_wraps
#print axioms markedContinuationParents_wraps
#print axioms normalMarker_licensed_of_completed
#print axioms normalMarker_licensed
#print axioms emptyMarker_licensed
#print axioms markedContinuationParents_wraps_of_completed
#print axioms LicensedParents.fresh
#print axioms LicensedParents.marked
#print axioms LicensedParents.mono
end SOnlyGlobalAncestors
