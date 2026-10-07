import SOnlyFirstEventOrigins
import SOnlyGlobalAncestors

/-!
# Exact first target acceptance within the actual response

The concrete paired script enumeration has 55 proper target-response samples
and one completed sample. Prior origins remain unchanged through every proper
sample, including the entry tree. At the 56th contraction every accepted
occurrence has the same literal frozen carrier. Generated outer-parent and
input-carrier certificates are explicit local induction inputs; this module
does not assume global origin closure or claim global trajectory firstness.
-/
namespace SOnlyFirstEventResponse
open PureSFormal PureSFormal.PureS PureSFormal.Research
open SOnlyProvenance SOnlyProvenanceRows SOnlyGeneratedOrigins
open SOnlySchedulerOrigins SOnlyGlobalAncestors SOnlyFirstEventOrigins
open SchedulerControl SchedulerInvariant SchedulerResponseInvariant SchedulerCycle
open SOnlyEventPattern SOnlyEventTransfer
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

theorem response_endpoint
    {program : CTS.Program} {tree : Dispatcher.Tree (ActionLabel program)}
    {route : Dispatcher.Route} {label : ActionLabel program}
    {path : Dispatcher.HasRoute tree route label}
    {bits : List Bool} {continuation carrier term : Term} {done : Bool}
    (row : ResponseRootMutation program tree path bits continuation carrier done term) :
    Endpoint term := by
  cases row with
  | frameFirst => exact Or.inl rfl
  | frameSecond => exact Or.inl rfl
  | frameThird => exact Or.inr rfl
  | routeIncomplete _ => exact Or.inr rfl
  | routeCompleteEmpty _ _ => exact Or.inr rfl
  | routeCompleteNonempty _ _ _ _ => exact Or.inr rfl
  | action _ => exact Or.inr rfl

/-- Unique-final flags separate the actual paired list's old origins from the
single completed origin extension. This is an induction on real script rows. -/
theorem responsePairs_licensed_split
    {program : CTS.Program} {dispatcher : ActionDispatcher program}
    (allowed : OriginSet program)
    {registers : Registers program} {bit : Bool} {bits : List Bool}
    {continuation carrier : Term} {parents : List ParentFrame}
    (admissible : Carrier.Admissible continuation)
    (held : ReachableAudit.Holds program dispatcher.tree bits continuation carrier)
    (hb : Licensed program dispatcher.tree allowed continuation)
    (bc : classify continuation = .other)
    (hv : Licensed program dispatcher.tree allowed carrier)
    (outer : LicensedParents program dispatcher allowed parents)
    {configurations : List (SchedulerInvariant.Configuration program dispatcher)} {entries : List (Bool × Term)}
    (pairs : ResponseSamplePairs program dispatcher registers bit bits continuation carrier parents configurations entries)
    (flags : FinalResponseFlags entries) :
    ∃ leading checkpoint,
      configurations = leading ++ [checkpoint] ∧
      SamplesLicensed (RootLicensed program dispatcher.tree allowed) leading ∧
      Licensed program dispatcher.tree (AddOrigin allowed (registers.phase, bit) carrier) checkpoint.cursor.erase ∧
      checkpoint.cursor.erase = Cursor.rebuild parents
        (LocalResponse.completed bits continuation carrier
          (SchedulerResponse.completedRoute program dispatcher registers bit carrier)) := by
  induction pairs with
  | nil => cases flags
  | @cons pc cursor done term position eraseEq root configurationTail entryTail tail ih =>
      cases flags with
      | last finalTerm =>
          cases tail with
          | nil =>
              refine ⟨[], ⟨some (.script (.normalResponse (registers.phase, bit)) pc registers), cursor⟩,
                rfl, ?_, ?_, ?_⟩
              · intro sample member; cases member
              · rw [eraseEq]
                exact (outer.mono (fun _ _ h => Or.inl h)).wraps term (response_endpoint root)
                  (response_licensed_add allowed root admissible held hb bc hv)
              · rw [eraseEq]
                exact congrArg (Cursor.rebuild parents) (root.done_eq rfl)
      | silent silentTerm rest =>
          obtain ⟨leading, checkpoint, tailEq, prior, final, erased⟩ := ih rest
          refine ⟨⟨some (.script (.normalResponse (registers.phase, bit)) pc registers), cursor⟩ :: leading,
            checkpoint, ?_, ?_, final, erased⟩
          · simp only [tailEq, List.cons_append]
          · intro sample member
            rcases List.mem_cons.mp member with eq | later
            · subst sample
              change Licensed program dispatcher.tree allowed cursor.erase
              rw [eraseEq]
              exact outer.wraps term (response_endpoint root)
                (incomplete_response_licensed allowed root admissible held hb bc hv)
            · exact prior sample later

/-- Cursor-only bridges preserve the actual whole S tree. -/
theorem zeroRun_erase {Control : Type} {machine : FiniteController.Machine Control}
    {ticks : Nat} {before after : FiniteController.Configuration Control}
    (bridge : ZeroMutationRun machine ticks before after) : before.cursor.erase = after.cursor.erase := by
  have steps := FiniteController.run_projects_stepsN machine ticks before
  rw [bridge.count_eq, bridge.run_eq] at steps
  exact StepsN.eq_of_zero steps

/-- Every offset strictly below 56 is observer-silent, and the exact final
sample has the one-pair enlarged origin set. The offset zero is included. -/
theorem target_response_sharp
    (inputBits : List Bool) (allowed : OriginSet SOnly38.program)
    (registers : Registers SOnly38.program) (phaseEq : registers.phase = SOnly38.targetPhase)
    (seedBits : List Bool) (continuation carrier : Term) (parents : List ParentFrame)
    (admissible : Carrier.Admissible continuation)
    (held : ReachableAudit.Holds SOnly38.program SOnly38.dispatcher.tree seedBits continuation carrier)
    (hb : Licensed SOnly38.program SOnly38.dispatcher.tree allowed continuation)
    (bc : classify continuation = .other)
    (hv : Licensed SOnly38.program SOnly38.dispatcher.tree allowed carrier)
    (outer : LicensedParents SOnly38.program SOnly38.dispatcher allowed parents)
    (excludes : ∀ audit, ¬ allowed SOnly38.targetLabel audit)
    (sampleIndex bridgeTicks : Nat)
    (before : SchedulerInvariant.Configuration SOnly38.program SOnly38.dispatcher)
    (beforeEq : (persistentSystem inputBits).contractionRun sampleIndex = before)
    (bridge : ZeroMutationRun (SchedulerControl.machine SOnly38.program SOnly38.dispatcher)
      bridgeTicks before
      (SchedulerResponse.responseStartConfiguration SOnly38.program SOnly38.dispatcher
        registers true seedBits continuation carrier parents)) :
    (∀ offset, offset < 56 → SOnlyObserver.event (SOnly38.trajectory inputBits (sampleIndex + offset)) = false) ∧
    Licensed SOnly38.program SOnly38.dispatcher.tree (AddOrigin allowed SOnly38.targetLabel carrier)
      (SOnly38.trajectory inputBits (sampleIndex + 56)) ∧
    SOnlyObserver.event (SOnly38.trajectory inputBits (sampleIndex + 56)) = true := by
  obtain ⟨configurations, scriptChain, pairs⟩ := normalResponse_exactPairedMutationChain
    SOnly38.program SOnly38.dispatcher registers true seedBits continuation carrier parents
  have flags := responseEntries_finalFlags SOnly38.program
    (SOnly38.dispatcher.route_valid (registers.phase, true)) seedBits continuation carrier
  obtain ⟨leading, checkpoint, decomposition, prior, final, erased⟩ :=
    responsePairs_licensed_split allowed admissible held hb bc hv outer pairs flags
  have labelEq : (registers.phase, true) = SOnly38.targetLabel := by rw [phaseEq]; rfl
  have count : configurations.length = 56 := by
    have count := pairs.length_eq.trans (responseEntries_length SOnly38.program
      (SOnly38.dispatcher.route_valid (registers.phase, true)) seedBits continuation carrier)
    rw [labelEq, SOnly38.target_selected_route, SOnlyEventResponse.target_response_cost] at count
    exact count
  have leadingCount : leading.length = 55 := by rw [decomposition, List.length_append] at count; simp at count; omega
  have chain := ExactMutationChain.prepend bridge scriptChain
  have finalEq : SOnly38.trajectory inputBits (sampleIndex + 56) = checkpoint.cursor.erase := by
    have atIndex : configurations[55]? = some checkpoint := by
      rw [decomposition, ← leadingCount]
      simp
    have sampled := exactChain_rootReset_sample inputBits chain beforeEq atIndex
    simpa only [Nat.add_assoc] using sampled
  refine ⟨?_, ?_, ?_⟩
  · intro offset bound
    cases offset with
    | zero =>
        rw [Nat.add_zero, trajectory_eq_contractionRun, beforeEq, zeroRun_erase bridge]
        apply event_false_of_excludes _ excludes
        exact outer.wraps _ (Or.inl (classify_frame _ _ _ _))
          (pending_carries SOnly38.program SOnly38.dispatcher.tree seedBits hb hv)
    | succ index =>
        have inRange : index < leading.length := by rw [leadingCount]; omega
        let sample := leading[index]
        have atIndex : configurations[index]? = some sample := by
          rw [decomposition, List.getElem?_append_left (by omega)]
          simp [sample, inRange]
        have sampled := exactChain_rootReset_sample inputBits chain beforeEq atIndex
        have licensed := prior sample (List.getElem_mem inRange)
        rw [show sampleIndex + (index + 1) = sampleIndex + index + 1 by omega, sampled]
        exact event_false_of_excludes licensed excludes
  · rw [finalEq]
    simpa only [labelEq] using final
  · rw [finalEq, erased]
    apply (SOnlyObserver.event_iff_matches _).mpr
    let cursor : Cursor := ⟨LocalResponse.completed seedBits continuation carrier
      (SchedulerResponse.completedRoute SOnly38.program SOnly38.dispatcher registers true carrier), parents⟩
    exact ⟨RootResetSelectorContract.cursorAddress cursor, cursor.focus,
      RootResetSelectorContract.subterm?_erase_cursorAddress cursor,
      completed_target_matches registers phaseEq seedBits continuation carrier⟩

set_option linter.constructorNameAsVariable false in
/-- All matches at the actual first response acceptance reconstruct the same
pre-transition bitword, and the fixed preorder reader returns its value. -/
theorem target_response_all_witnesses
    (inputBits : List Bool) (allowed : OriginSet SOnly38.program)
    (registers : Registers SOnly38.program) (phaseEq : registers.phase = SOnly38.targetPhase)
    (seedBits : List Bool) (continuation carrier : Term) (parents : List ParentFrame)
    (admissible : Carrier.Admissible continuation)
    (held : ReachableAudit.Holds SOnly38.program SOnly38.dispatcher.tree seedBits continuation carrier)
    (hb : Licensed SOnly38.program SOnly38.dispatcher.tree allowed continuation)
    (bc : classify continuation = .other)
    (hv : Licensed SOnly38.program SOnly38.dispatcher.tree allowed carrier)
    (outer : LicensedParents SOnly38.program SOnly38.dispatcher allowed parents)
    (excludes : ∀ audit, ¬ allowed SOnly38.targetLabel audit)
    (suffix : List Bool)
    (decoded : CarrierDecoder.decode? SOnly38.program SOnly38.dispatcher.tree
      seedBits continuation admissible carrier = some suffix)
    (value : Nat) (numerical : SOnlyResultBits.readMachineBits (true :: suffix) = some value)
    (sampleIndex bridgeTicks : Nat)
    (before : SchedulerInvariant.Configuration SOnly38.program SOnly38.dispatcher)
    (beforeEq : (persistentSystem inputBits).contractionRun sampleIndex = before)
    (bridge : ZeroMutationRun (SchedulerControl.machine SOnly38.program SOnly38.dispatcher)
      bridgeTicks before
      (SchedulerResponse.responseStartConfiguration SOnly38.program SOnly38.dispatcher
        registers true seedBits continuation carrier parents)) :
    (∀ offset, offset < 56 → SOnlyObserver.event (SOnly38.trajectory inputBits (sampleIndex + offset)) = false) ∧
    SOnlyObserver.event (SOnly38.trajectory inputBits (sampleIndex + 56)) = true ∧
    (∀ address shell, (SOnly38.trajectory inputBits (sampleIndex + 56)).subterm? address = some shell →
      targetPattern.matchesBool shell = true →
      shell.subterm? auditAddress = some carrier ∧ SOnlyWitnessResult.readShell shell = some value) ∧
    SOnlyCurrentDecoder.read (SOnly38.trajectory inputBits (sampleIndex + 56)) = some value := by
  obtain ⟨silent, licensed, accepted⟩ := target_response_sharp inputBits allowed registers phaseEq
    seedBits continuation carrier parents admissible held hb bc hv outer excludes
    sampleIndex bridgeTicks before beforeEq bridge
  generalize treeEq : SOnly38.trajectory inputBits (sampleIndex + 56) = whole at licensed accepted ⊢
  have publicDecode := CheckpointRun.decodeCarrier?_of_decode SOnly38.program SOnly38.dispatcher.tree
    seedBits continuation admissible decoded
  refine ⟨silent, accepted, ?_, ?_⟩
  · intro address shell located matched
    refine ⟨all_target_audits licensed excludes located matched, ?_⟩
    unfold SOnlyWitnessResult.readShell
    rw [all_target_prestates licensed excludes publicDecode located matched]
    exact numerical
  · exact current_read_of_added_origin licensed excludes accepted publicDecode numerical

/-- The actual selected-response constructor discharges both the deleted
carrier's origin certificate and its public audit-decode premise. -/
theorem selectedTarget_response_all_witnesses
    (inputBits seedBits : List Bool) (allowed : OriginSet SOnly38.program)
    (continuation source : Term) (admissible : Carrier.Admissible continuation)
    (registers : Registers SOnly38.program) (phaseEq : registers.phase = SOnly38.targetPhase)
    (suffix : List Bool) (outerContext fullContext innerContext targetContext : Context)
    (parents : List ParentFrame) (responseTicks : Nat)
    (response : SelectedResponseTrace SOnly38.program SOnly38.dispatcher seedBits continuation source
      admissible registers true suffix outerContext fullContext innerContext targetContext parents responseTicks)
    (hb : Licensed SOnly38.program SOnly38.dispatcher.tree allowed continuation)
    (bc : classify continuation = .other)
    (sourceLicensed : Licensed SOnly38.program SOnly38.dispatcher.tree allowed source)
    (outer : LicensedParents SOnly38.program SOnly38.dispatcher allowed parents)
    (excludes : ∀ audit, ¬ allowed SOnly38.targetLabel audit)
    (value : Nat) (numerical : SOnlyResultBits.readMachineBits (true :: suffix) = some value)
    (sampleIndex bridgeTicks : Nat)
    (before : SchedulerInvariant.Configuration SOnly38.program SOnly38.dispatcher)
    (beforeEq : (persistentSystem inputBits).contractionRun sampleIndex = before)
    (bridge : ZeroMutationRun (SchedulerControl.machine SOnly38.program SOnly38.dispatcher)
      bridgeTicks before
      (SchedulerResponse.responseStartConfiguration SOnly38.program SOnly38.dispatcher
        (scannedRegisters registers true suffix) true seedBits continuation
        (deletedCarrier true outerContext innerContext) parents)) :
    (∀ offset, offset < 56 → SOnlyObserver.event (SOnly38.trajectory inputBits (sampleIndex + offset)) = false) ∧
    SOnlyObserver.event (SOnly38.trajectory inputBits (sampleIndex + 56)) = true ∧
    (∀ address shell, (SOnly38.trajectory inputBits (sampleIndex + 56)).subterm? address = some shell →
      targetPattern.matchesBool shell = true →
      shell.subterm? auditAddress = some (deletedCarrier true outerContext innerContext) ∧
      SOnlyWitnessResult.readShell shell = some value) ∧
    SOnlyCurrentDecoder.read (SOnly38.trajectory inputBits (sampleIndex + 56)) = some value := by
  have scannedPhase : (scannedRegisters registers true suffix).phase = SOnly38.targetPhase := by
    rw [scannedRegisters, scanRegisters_phase]
    unfold Registers.observeLive
    split <;> exact phaseEq
  have deleted := SOnlyCanonicalOrigins.selectedResponse_deleted_licensed allowed response bc sourceLicensed
  exact target_response_all_witnesses inputBits allowed (scannedRegisters registers true suffix)
    scannedPhase seedBits continuation (deletedCarrier true outerContext innerContext) parents
    admissible response.targetHolds hb bc deleted outer excludes suffix response.targetDecode value numerical
    sampleIndex bridgeTicks before beforeEq bridge

end SOnlyFirstEventResponse
#print axioms SOnlyFirstEventResponse.responsePairs_licensed_split
#print axioms SOnlyFirstEventResponse.target_response_sharp
#print axioms SOnlyFirstEventResponse.target_response_all_witnesses

#print axioms SOnlyFirstEventResponse.selectedTarget_response_all_witnesses
