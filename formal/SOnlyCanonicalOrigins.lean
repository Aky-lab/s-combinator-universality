import SOnlyGeneratedOrigins

/-!
# Canonical selected-C4 preservation of licensed Local origins

This module proves preservation through the actual SelectedFront context
constructors. The Local/route/action path is treated as a coupled context so
that its old completed root keeps the same label and snapshot. No closure of
arbitrary dispatcher replacement is assumed, and old audits may contain any
already licensed descendants.
-/
namespace SOnlyCanonicalOrigins

open PureSFormal PureSFormal.PureS
open SOnlyProvenance SOnlyProvenanceRows SOnlyGeneratedOrigins
open CanonicalTraversal

set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

private theorem comp_assoc (outer middle inner : Context) :
    (outer.comp middle).comp inner = outer.comp (middle.comp inner) := by
  induction outer with
  | hole => rfl
  | appLeft context right ih => simpa only [Context.comp] using congrArg (Context.appLeft · right) ih
  | appRight left context ih => simpa only [Context.comp] using congrArg (Context.appRight left) ih

/-- Rebuilding a registered Base changes only its queue. The continuation and
retained beta inherit their licenses from the actual old whole carrier. -/
theorem base_queue_preserves
    (program : CTS.Program) (tree : Dispatcher.Tree (ActionLabel program))
    (bits : List Bool) (continuation beta : Term)
    (bc : classify continuation = .other) (P : Term → Prop) :
    Preserves P (MutableBase.queueContext (compileActions program tree) bits continuation beta) := by
  intro old new source target
  rw [MutableBase.queueContext_plug] at source ⊢
  exact mutableBase_carries program tree bits source.1.1 bc target source.2.1

/-- A fresh completed root keeps its original label and frozen snapshot when
its exact route/action accumulator changes. Independent inherited subtrees
are checked separately; only the coupled parser shape licenses the root. -/
theorem fresh_completed_preserves
    {program : CTS.Program} {tree : Dispatcher.Tree (ActionLabel program)}
    (allowed : OriginSet program) (bits : List Bool)
    {continuation snapshot oldDispatch newDispatch oldAccumulator newAccumulator : Term}
    {route : Dispatcher.Route} {label : ActionLabel program}
    (oldShape : ReachableAudit.SnapshotDispatchAt program tree snapshot route label oldAccumulator oldDispatch)
    (newShape : ReachableAudit.SnapshotDispatchAt program tree snapshot route label newAccumulator newDispatch)
    (source : Licensed program tree allowed (LocalResponse.completed bits continuation snapshot oldDispatch))
    (target : Licensed program tree allowed newDispatch)
    (bc : classify continuation = .other) :
    Licensed program tree allowed (LocalResponse.completed bits continuation snapshot newDispatch) := by
  have root : RootLicensed program tree allowed (LocalResponse.completed bits continuation snapshot oldDispatch) :=
    source.2.2 rfl
  have origin := (completed_root_licensed_iff allowed bits oldShape).mp root
  have nextRoot := (completed_root_licensed_iff allowed bits (continuation := continuation) newShape).mpr origin
  exact activeShell_carries bits source.2.1.1 bc source.1.1.1.2.1 target nextRoot

/-- Marked shells have no H6 root; replacing only the dispatcher preserves all
other inherited fields, with Endpoint excluding a counterfeit marked head. -/
theorem marked_dispatch_preserves
    {P : Term → Prop} (bits : List Bool)
    {continuation snapshot oldDispatch newDispatch : Term}
    (endpoint : Endpoint snapshot)
    (source : AllH6 P (Carrier.activeShell bits continuation
      (ReachableAudit.haltField .marked snapshot) oldDispatch snapshot snapshot))
    (target : AllH6 P newDispatch) :
    AllH6 P (Carrier.activeShell bits continuation
      (ReachableAudit.haltField .marked snapshot) newDispatch snapshot snapshot) := by
  have markedOther : classify (ReachableAudit.haltField .marked snapshot) = .other := by
    rcases endpoint with other | fresh <;>
      simp [ReachableAudit.haltField, Carrier.markedHField, classify, *, delta]
  exact other_app_carries
    (other_app_carries (other_app_carries source.1.1.1 target markedOther)
      source.1.2.1 (other_app_class markedOther))
    source.2.1 (other_app_class (other_app_class markedOther))

/-- The registered Local dispatcher, selected route, and action-history spine
must be coupled. This context preserves the old root's actual label/audit
while allowing an arbitrary new licensed accumulator at its hole. -/
theorem local_route_action_preserves
    {program : CTS.Program} {tree : Dispatcher.Tree (ActionLabel program)}
    (allowed : OriginSet program) (bits : List Bool)
    (continuation snapshot : Term) (status : ReachableAudit.HaltState)
    {route : Dispatcher.Route} {label : ActionLabel program} {routeContext : Context}
    (selected : RouteContext (selectedAction program) snapshot tree route label routeContext)
    (bc : classify continuation = .other) (endpoint : Endpoint snapshot) :
    Preserves (RootLicensed program tree allowed)
      ((localDispatcherContext bits continuation (ReachableAudit.haltField status snapshot) snapshot snapshot).comp
        (routeContext.comp (actionContext (actionHistories program label snapshot)))) := by
  intro old new source target
  let oldDispatch := routeContext.plug (ReachableAudit.actionResponse program label snapshot old)
  let newDispatch := routeContext.plug (ReachableAudit.actionResponse program label snapshot new)
  have oldShape : ReachableAudit.SnapshotDispatchAt program tree snapshot route label old oldDispatch :=
    ⟨selected.snapshotRoute _⟩
  have newShape : ReachableAudit.SnapshotDispatchAt program tree snapshot route label new newDispatch :=
    ⟨selected.snapshotRoute _⟩
  have source' : Licensed program tree allowed
      (Carrier.activeShell bits continuation (ReachableAudit.haltField status snapshot)
        oldDispatch snapshot snapshot) := by
    simpa only [Context.plug_comp, localDispatcherContext_plug, actionContext_plug,
      ReachableAudit.actionResponse, oldDispatch] using source
  have oldDispatchLicensed : Licensed program tree allowed oldDispatch := source'.1.1.2.1
  have dispatcherPreserves := preserves_comp
    (route_context_preserves selected endpoint)
    (action_context_preserves (RootLicensed program tree allowed) (actionHistories program label snapshot))
  have newDispatchLicensed : Licensed program tree allowed newDispatch := by
    have oldAtHole : AllH6 (RootLicensed program tree allowed)
        ((routeContext.comp (actionContext (actionHistories program label snapshot))).plug old) := by
      simpa only [Context.plug_comp, actionContext_plug, ReachableAudit.actionResponse, oldDispatch] using oldDispatchLicensed
    have next := dispatcherPreserves old new oldAtHole target
    simpa only [Context.plug_comp, actionContext_plug, ReachableAudit.actionResponse, newDispatch] using next
  have target' : Licensed program tree allowed
      (Carrier.activeShell bits continuation (ReachableAudit.haltField status snapshot)
        newDispatch snapshot snapshot) := by
    cases status with
    | fresh => exact fresh_completed_preserves allowed bits oldShape newShape source' newDispatchLicensed bc
    | marked => exact marked_dispatch_preserves bits endpoint source' newDispatchLicensed
  simpa only [Context.plug_comp, localDispatcherContext_plug, actionContext_plug,
    ReachableAudit.actionResponse, newDispatch] using target'

/-- Every actual canonical selected-front context preserves inherited Local
origins when replacing its focused cell by a licensed term. -/
theorem selectedFront_context_preserves
    {program : CTS.Program} {tree : Dispatcher.Tree (ActionLabel program)}
    (allowed : OriginSet program) {bits : List Bool} {continuation source : Term}
    {bit : Bool} {suffix : List Bool} {outerContext : Context}
    (selected : SelectedFront program tree bits continuation source bit suffix outerContext)
    (bc : classify continuation = .other) :
    Preserves (RootLicensed program tree allowed) outerContext := by
  induction selected with
  | @base queueContext cellOuter bit suffix cellAddress queue selected =>
      exact preserves_comp (base_queue_preserves program tree bits continuation _ bc _)
        (queue_context_preserves (QueueContext.ofOuterContext selected.outerShape))
  | @inside snapshot currentContext segmentContext routeContext currentOuter bit
      currentSuffix appended status route label snapshotInv current segment selectedRoute inner ih =>
      have localPreserves := local_route_action_preserves allowed bits continuation snapshot status
        selectedRoute bc (holds_endpoint bc snapshotInv)
      have rest := preserves_comp (queue_context_preserves segment) ih
      simpa only [comp_assoc] using preserves_comp localPreserves rest
  | @segment snapshot currentContext segmentContext routeContext cellOuter bit
      suffix cellAddress status route label snapshotInv current queue selectedRoute selected =>
      have localPreserves := local_route_action_preserves allowed bits continuation snapshot status
        selectedRoute bc (holds_endpoint bc snapshotInv)
      have rest := queue_context_preserves (P := RootLicensed program tree allowed) (QueueContext.ofOuterContext selected.outerShape)
      simpa only [comp_assoc] using preserves_comp localPreserves rest

/-- Canonical C4 replaces the chosen live cell by two exact predecessor copies.
The full ancestor path, including nested completed Locals, preserves licenses. -/
theorem selectedFront_delete_licensed
    {program : CTS.Program} {tree : Dispatcher.Tree (ActionLabel program)}
    (allowed : OriginSet program) {bits : List Bool} {continuation source target predecessor : Term}
    {bit : Bool} {suffix : List Bool} {outerContext : Context}
    (selected : SelectedFront program tree bits continuation source bit suffix outerContext)
    (certificate : FrontCertificate source target bit suffix predecessor outerContext)
    (bc : classify continuation = .other)
    (licensed : Licensed program tree allowed source) :
    Licensed program tree allowed target := by
  have sourcePlug : Licensed program tree allowed
      (outerContext.plug (.app (live bit) predecessor)) := certificate.source_eq ▸ licensed
  have predecessorLicensed : Licensed program tree allowed predecessor :=
    (context_inner outerContext _ sourcePlug).2.1
  rw [certificate.target_eq]
  exact selectedFront_context_preserves allowed selected bc _ _ sourcePlug (c4_carries bit predecessorLicensed)

/-- The actual scheduler SelectedResponseTrace's deleted carrier inherits all
old Local label/audit licenses. No new origin is introduced by deletion. -/
theorem selectedResponse_deleted_licensed
    {program : CTS.Program} {dispatcher : ActionDispatcher program}
    (allowed : OriginSet program) {bits : List Bool} {continuation source : Term}
    {admissible : Carrier.Admissible continuation}
    {registers : SchedulerControl.Registers program} {bit : Bool} {suffix : List Bool}
    {outerContext fullContext innerContext targetContext : Context}
    {parents : List ParentFrame} {ticks : Nat}
    (trace : SchedulerCycle.SelectedResponseTrace program dispatcher bits continuation source admissible
      registers bit suffix outerContext fullContext innerContext targetContext parents ticks)
    (bc : classify continuation = .other)
    (licensed : Licensed program dispatcher.tree allowed source) :
    Licensed program dispatcher.tree allowed
      (SchedulerCycle.deletedCarrier bit outerContext innerContext) := by
  obtain ⟨_, _, certificate⟩ := SchedulerAscent.selectedFront_deleteAtPath
    trace.selected trace.sourceDescent trace.path
  exact selectedFront_delete_licensed allowed trace.selected certificate bc licensed

end SOnlyCanonicalOrigins

#print axioms SOnlyCanonicalOrigins.local_route_action_preserves
#print axioms SOnlyCanonicalOrigins.selectedFront_context_preserves
#print axioms SOnlyCanonicalOrigins.selectedFront_delete_licensed
#print axioms SOnlyCanonicalOrigins.selectedResponse_deleted_licensed
