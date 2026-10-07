import SOnly38
import PureSFormal.Research.RootResetCompletedLocalPatterns

/-!
# A label-specific independent-hole event pattern

The imported completed-Local pattern theorem forgets which member of its
finite pattern list matched. This module keeps the structural dispatcher
route and label, constructing exactly the single target pattern F17.
It proves syntax/parser equivalence on arbitrary finite S trees and proves
that a genuine phase-17/true completed response matches it. It does not infer
that arbitrary descendant matches have generated scheduler provenance.
-/
namespace SOnlyEventPattern

open PureSFormal PureSFormal.PureS PureSFormal.Research
open RootResetCompletedLocalPatterns

set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

/-- Keep the chosen structural route instead of collecting all routes. Invalid
routes get an arbitrary default; all theorems below require a genuine route. -/
def routePattern (program : CTS.Program) :
    Dispatcher.Tree (ActionLabel program) → Dispatcher.Route → Pattern
  | .leaf label, [] => chosenPattern (actionPattern (ActionParser.historyCount program label))
  | .node left right, .left :: route =>
      chosenPattern (.app (routePattern program left route)
        (callPattern (compileDispatcher (selectedAction program) right)))
  | .node left right, .right :: route =>
      chosenPattern (.app (callPattern (compileDispatcher (selectedAction program) left))
        (routePattern program right route))
  | _, _ => .s

/-- The fixed pattern has independent holes, literal dormant sibling code,
route 0100011, and exactly nineteen completed action-history arguments. -/
def targetPattern : Pattern :=
  localPattern .fresh (routePattern SOnly38.program SOnly38.dispatcher.tree SOnly38.targetRoute)

theorem target_history_count :
    ActionParser.historyCount SOnly38.program SOnly38.targetLabel = 19 := by decide

/-- A matched route pattern fixes both the route and label, even for fabricated
payloads and equal appender codes belonging to different labels. -/
theorem routePattern_sound
    {program : CTS.Program} {tree : Dispatcher.Tree (ActionLabel program)}
    {route : Dispatcher.Route} {label : ActionLabel program}
    (path : Dispatcher.HasRoute tree route label) (source : Term)
    (matched : (routePattern program tree route).matchesBool source = true) :
    ∃ accumulator, DispatchParser.DispatchShape program tree route label accumulator source := by
  induction path generalizing source with
  | leaf label =>
      obtain ⟨audit, response, sourceEq, actionMatches⟩ := chosen_sound matched
      obtain ⟨accumulator, histories, countEq, responseEq⟩ := action_sound _ response actionMatches
      subst source
      exact ⟨accumulator, response, histories, .leaf label audit response, countEq, responseEq⟩
  | @left route label left right path ih =>
      obtain ⟨outerAudit, fork, sourceEq, forkMatches⟩ := chosen_sound matched
      obtain ⟨activeTerm, dormantTerm, forkEq, activeMatches, dormantMatches⟩ := app_matches forkMatches
      obtain ⟨dormantAudit, dormantEq⟩ := call_sound dormantMatches
      obtain ⟨accumulator, response, histories, inner, countEq, responseEq⟩ := ih activeTerm activeMatches
      subst source
      subst fork
      subst dormantTerm
      exact ⟨accumulator, response, histories, .left outerAudit dormantAudit inner, countEq, responseEq⟩
  | @right route label left right path ih =>
      obtain ⟨outerAudit, fork, sourceEq, forkMatches⟩ := chosen_sound matched
      obtain ⟨dormantTerm, activeTerm, forkEq, dormantMatches, activeMatches⟩ := app_matches forkMatches
      obtain ⟨dormantAudit, dormantEq⟩ := call_sound dormantMatches
      obtain ⟨accumulator, response, histories, inner, countEq, responseEq⟩ := ih activeTerm activeMatches
      subst source
      subst fork
      subst dormantTerm
      exact ⟨accumulator, response, histories, .right outerAudit dormantAudit inner, countEq, responseEq⟩

/-- Public route/action shape matches the exact route-specific pattern. -/
theorem routePattern_matches
    {program : CTS.Program} {tree : Dispatcher.Tree (ActionLabel program)}
    {route : Dispatcher.Route} {label : ActionLabel program} {accumulator field : Term}
    (shape : DispatchParser.DispatchShape program tree route label accumulator field) :
    (routePattern program tree route).matchesBool field = true := by
  obtain ⟨response, histories, routeShape, historyCount, responseEq⟩ := shape
  have actionMatches : (actionPattern (ActionParser.historyCount program label)).matchesBool response = true := by
    rw [responseEq, ← historyCount]
    exact action_matches accumulator histories
  induction routeShape with
  | leaf label audit response => exact actionMatches
  | @left left right route label response active outerAudit dormantAudit inner ih =>
      have matched := ih historyCount responseEq actionMatches
      simp only [routePattern, chosenPattern, callPattern, RouteGrammar.selectedLeft,
        RouteGrammar.compiledCall, chosen, Pattern.matchesBool, literal_self,
        matched, Bool.and_true]
  | @right left right route label response active outerAudit dormantAudit inner ih =>
      have matched := ih historyCount responseEq actionMatches
      simp only [routePattern, chosenPattern, callPattern, RouteGrammar.selectedRight,
        RouteGrammar.compiledCall, chosen, Pattern.matchesBool, literal_self,
        matched, Bool.and_true]

/-- Label-specific local soundness; no equality of any two holes is required. -/
theorem localPattern_sound
    {program : CTS.Program} {tree : Dispatcher.Tree (ActionLabel program)}
    {route : Dispatcher.Route} {label : ActionLabel program}
    (path : Dispatcher.HasRoute tree route label)
    (status : CheckpointDecoder.HaltStatus) (source : Term)
    (matched : (localPattern status (routePattern program tree route)).matchesBool source = true) :
    ∃ view : CheckpointDecoder.LocalView program,
      view.status = status ∧ view.route = route ∧ view.label = label ∧
      CheckpointDecoder.LocalShape program tree view source := by
  obtain ⟨left, right, sourceEq, leftMatches, rightMatches⟩ := app_matches matched
  obtain ⟨continuation, continuationAudit, rightEq, _, _⟩ := app_matches rightMatches
  obtain ⟨head, seed, leftEq, headMatches, seedMatches⟩ := app_matches leftMatches
  obtain ⟨haltField, dispatcher, headEq, haltMatched, dispatcherMatched⟩ := app_matches headMatches
  obtain ⟨seedHead, seedAudit, seedEq, seedHeadMatches, _⟩ := app_matches seedMatches
  obtain ⟨sHead, payload, seedHeadEq, sMatched, _⟩ := app_matches seedHeadMatches
  have sEq : sHead = .s := (Pattern.matches_s_iff sHead).mp (Pattern.matchesBool_sound sMatched)
  have haltShape := halt_sound status haltField haltMatched
  obtain ⟨accumulator, dispatchShape⟩ := routePattern_sound path dispatcher dispatcherMatched
  refine ⟨⟨status, route, label, accumulator, payload, continuation⟩, rfl, rfl, rfl,
    ⟨haltField, dispatcher, seedAudit, continuationAudit, haltShape, dispatchShape, ?_⟩⟩
  rw [sourceEq, leftEq, headEq, rightEq, seedEq, seedHeadEq, sEq]
  rfl

theorem localPattern_matches
    {program : CTS.Program} {tree : Dispatcher.Tree (ActionLabel program)}
    {view : CheckpointDecoder.LocalView program} {source : Term}
    (shape : CheckpointDecoder.LocalShape program tree view source) :
    (localPattern view.status (routePattern program tree view.route)).matchesBool source = true := by
  obtain ⟨haltField, dispatcher, seedAudit, continuationAudit, haltShape, dispatchShape, sourceEq⟩ := shape
  have matched := routePattern_matches dispatchShape
  rw [sourceEq]
  simp only [localPattern, CheckpointDecoder.openShell, Pattern.matchesBool,
    halt_matches haltShape, matched, Bool.and_true]

/-- Exact F17 semantics on all finite trees, including off-trajectory trees. -/
theorem targetPattern_iff (source : Term) :
    targetPattern.matchesBool source = true ↔
      ∃ view : CheckpointDecoder.LocalView SOnly38.program,
        view.status = .fresh ∧ view.route = SOnly38.targetRoute ∧
        view.label = SOnly38.targetLabel ∧
        CheckpointDecoder.LocalShape SOnly38.program SOnly38.dispatcher.tree view source := by
  constructor
  · exact localPattern_sound SOnly38.target_has_route .fresh source
  · rintro ⟨view, statusEq, routeEq, _, shape⟩
    have matched := localPattern_matches shape
    simpa only [targetPattern, statusEq, routeEq] using matched

/-- A real target response is accepted at creation. No queue interpretation
is needed for this syntax theorem; source semantics comes from its trace. -/
theorem completed_target_matches (registers : SchedulerControl.Registers SOnly38.program)
    (phaseEq : registers.phase = SOnly38.targetPhase)
    (bits : List Bool) (continuation snapshot : Term) :
    targetPattern.matchesBool
      (LocalResponse.completed bits continuation snapshot
        (SchedulerResponse.completedRoute SOnly38.program SOnly38.dispatcher
          registers true snapshot)) = true := by
  have dispatchShape := (SchedulerResponse.completedRoute_snapshotDispatch
    SOnly38.program SOnly38.dispatcher registers true snapshot).toDispatchShape
  have matched := routePattern_matches dispatchShape
  have labelEq : (registers.phase, true) = SOnly38.targetLabel := by
    rw [phaseEq]
    rfl
  rw [labelEq, SOnly38.target_selected_route] at matched
  simp only [targetPattern, localPattern, haltPattern, LocalResponse.completed,
    Carrier.activeShell, Carrier.shell, freshHField, seedCode, Pattern.matchesBool,
    literal_self, matched, Bool.and_true]

end SOnlyEventPattern

#print axioms SOnlyEventPattern.target_history_count
#print axioms SOnlyEventPattern.routePattern_sound
#print axioms SOnlyEventPattern.routePattern_matches
#print axioms SOnlyEventPattern.targetPattern_iff
#print axioms SOnlyEventPattern.completed_target_matches
