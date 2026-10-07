import SOnlyGlobalFirstEvent

/-!
# Global first acceptance independent of numeric decoding

A first source Event alone forces the exact first S acceptance. Every matching
shell contains the same literal frozen carrier and reconstructs the same source
prestate. No successful numeric decoding is required or inferred here.
-/
namespace SOnlyGlobalFirstStructure
open PureSFormal PureSFormal.PureS PureSFormal.Research
open SchedulerControl SchedulerInvariant SchedulerCycle SchedulerResponseInvariant
open SchedulerNestedResponse SchedulerCompletedContext SchedulerTraceAlgebra
open SOnlyProvenance SOnlyProvenanceRows SOnlyGeneratedOrigins SOnlySchedulerOrigins
open SOnlyGlobalAncestors SOnlyGlobalOrigins SOnlyGlobalFirstPrefix SOnlyGlobalFirstEvent
open SOnlyResponseLabels SOnlyStageEvents SOnlyEventPattern SOnlyEventTransfer
open SOnlyFirstEventOrigins SOnlyFirstEventResponse
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000
-- This naming linter unfolds the concrete trajectory recursively; kernel checking remains enabled.
set_option linter.constructorNameAsVariable false

theorem target_response_structure
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
      shell.subterm? auditAddress = some carrier ∧
      readPrestate SOnly38.program SOnly38.dispatcher.tree true shell = some (true :: suffix)) := by
  obtain ⟨silent, licensed, accepted⟩ := target_response_sharp inputBits allowed registers phaseEq
    seedBits continuation carrier parents admissible held hb bc hv outer excludes
    sampleIndex bridgeTicks before beforeEq bridge
  generalize treeEq : SOnly38.trajectory inputBits (sampleIndex + 56) = whole at licensed accepted ⊢
  have publicDecode := CheckpointRun.decodeCarrier?_of_decode SOnly38.program SOnly38.dispatcher.tree
    seedBits continuation admissible decoded
  refine ⟨silent, accepted, ?_⟩
  intro address shell located matched
  exact ⟨all_target_audits (allowed := allowed)
    (source := whole) (snapshot := carrier)
    licensed excludes located matched,
    all_target_prestates (allowed := allowed)
    (source := whole) (snapshot := carrier)
    (suffix := suffix) licensed excludes publicDecode located matched⟩

theorem selectedTarget_response_structure
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
      readPrestate SOnly38.program SOnly38.dispatcher.tree true shell = some (true :: suffix)) := by
  have scannedPhase : (scannedRegisters registers true suffix).phase = SOnly38.targetPhase := by
    rw [scannedRegisters, scanRegisters_phase]
    unfold Registers.observeLive
    split <;> exact phaseEq
  have deleted := SOnlyCanonicalOrigins.selectedResponse_deleted_licensed allowed response bc sourceLicensed
  exact target_response_structure inputBits allowed (scannedRegisters registers true suffix)
    scannedPhase seedBits continuation (deletedCarrier true outerContext innerContext) parents
    admissible response.targetHolds hb bc deleted outer excludes suffix response.targetDecode
    sampleIndex bridgeTicks before beforeEq bridge

/-- Structural first acceptance for an exact target source prestate. -/
theorem sourceTarget_first_structure (bits : List Bool) (r : Nat)
    (eventSuffix : List Bool)
    (allNonempty : ∀ k, k ≤ r →
      (CTS.iterate SOnly38.program k (CTS.initial SOnly38.program bits)).data ≠ [])
    (noEvent : ∀ k, k < r →
      ¬ SOnlySource.Event (CTS.iterate SOnly38.program k (CTS.initial SOnly38.program bits)))
    (event : CTS.iterate SOnly38.program r (CTS.initial SOnly38.program bits) =
      ⟨SOnly38.targetPhase, true :: eventSuffix⟩) :
    SOnlyObserver.event (SOnly38.trajectory bits (firstJobPreResponseTime bits r + 57)) = true ∧
    (∀ index, index < firstJobPreResponseTime bits r + 57 →
      SOnlyObserver.event (SOnly38.trajectory bits index) = false) ∧
    ∃ snapshot,
      CheckpointDecoder.decodeCarrier? SOnly38.program SOnly38.dispatcher.tree snapshot = some eventSuffix ∧
      ∀ address shell,
        (SOnly38.trajectory bits (firstJobPreResponseTime bits r + 57)).subterm? address = some shell →
        targetPattern.matchesBool shell = true →
        shell.subterm? auditAddress = some snapshot ∧
        readPrestate SOnly38.program SOnly38.dispatcher.tree true shell = some (true :: eventSuffix) := by
  cases bits with
  | nil => exact (allNonempty 0 (Nat.zero_le r) rfl).elim
  | cons bit suffix =>
      let bits := bit :: suffix
      let allowed : OriginSet SOnly38.program := fun label _ => label ≠ SOnly38.targetLabel
      have excludes : ∀ snapshot, ¬ allowed SOnly38.targetLabel snapshot := by
        intro snapshot origin
        exact origin rfl
      have sourceAllowed : SourceAllowed allowed (CTS.initial SOnly38.program bits) r := by
        intro index bound label snapshot labelEq same
        apply noEvent index bound
        apply (target_sourceLabel_iff _).mp
        simpa only [same] using labelEq
      let environment := environmentCode (compileActions SOnly38.program SOnly38.dispatcher.tree) bits
      let continuation := Dovetail.clockExit (r + 1) r environment
      obtain ⟨parents, registers, phase, responseBit, responseSuffix, source,
          outerContext, fullContext, innerContext, targetContext, ticks, prefixConfigurations,
          prefixChain, prefixCount, coherent, trace, sourceEq,
          prefixLicensed, outerLicensed, hb, sourceLicensed⟩ :=
        firstJob_response_prefix_licensed bit suffix r allNonempty allowed sourceAllowed
      have configurationEq := sourceEq.trans event
      have phaseEq : phase = SOnly38.targetPhase := congrArg CTS.Config.phase configurationEq
      have dataEq : responseBit :: responseSuffix = true :: eventSuffix := congrArg CTS.Config.data configurationEq
      have bitEq := (List.cons.inj dataEq).1
      have suffixEq := (List.cons.inj dataEq).2
      subst responseBit
      subst responseSuffix
      have registerPhase : registers.phase = SOnly38.targetPhase := coherent.phase_eq.trans phaseEq
      have notSeen : registers.seen = false := by simpa [scanSeen] using coherent.seen_eq
      let fullParents := .right
        (SchedulerResponse.pendingFunction SOnly38.program SOnly38.dispatcher bits continuation) :: parents
      let c4 := selectedC4Configuration SOnly38.program SOnly38.dispatcher registers true
        outerContext innerContext fullParents
      obtain ⟨bound, found⟩ := selected_seekC4 SOnly38.program SOnly38.dispatcher bits continuation source
        (Dovetail.clockExit_admissible (r + 1) r environment) registers true eventSuffix parents trace notSeen
      have c4Chain : ExactMutationChain (SchedulerControl.machine SOnly38.program SOnly38.dispatcher) c4
          (upConfiguration SOnly38.program SOnly38.dispatcher registers omega
            (ContextCursor.frames fullContext omega fullParents)) [c4] := by
        exact .next bound found (.done 0 ⟨rfl, rfl⟩)
      have throughC4 := SchedulerRecurrence.ExactMutationChain.append prefixChain c4Chain
      have c4Last : LastSample (prefixConfigurations ++ [c4]) c4 :=
        (LastSample.one c4).appendLeft prefixConfigurations
      have c4Eq : (persistentSystem bits).contractionRun (firstJobPreResponseTime bits r + 1) = c4 := by
        have sampled := SchedulerTraceAlgebra.ExactMutationChain.contractionRun_eq_last
          SOnly38.program SOnly38.dispatcher bits
          (SchedulerRecurrence.initialGood SOnly38.program SOnly38.dispatcher bits)
          throughC4 c4Last (sampleIndex := 0) rfl
        simpa only [Nat.zero_add, List.length_append, List.length_singleton, prefixCount] using sampled
      obtain ⟨frameTicks, toFrame⟩ := selectedC4_toFrame_zeroRunAt SOnly38.program SOnly38.dispatcher
        bits continuation source (Dovetail.clockExit_admissible (r + 1) r environment)
        registers true eventSuffix 0 parents trace notSeen
      have toFrame' : ZeroMutationRun (SchedulerControl.machine SOnly38.program SOnly38.dispatcher)
          frameTicks c4
          (SchedulerResponse.frameConfiguration SOnly38.program SOnly38.dispatcher
            (scannedRegisters registers true eventSuffix) bits continuation
            (deletedCarrier true outerContext innerContext) parents) := by
        simpa [c4, fullParents, PrimitiveFuel.pendingParents, selectedFrameConfiguration] using toFrame
      have entered := SchedulerResponse.enterResponse_zeroRun SOnly38.program SOnly38.dispatcher
        (scannedRegisters registers true eventSuffix) true bits continuation
        (deletedCarrier true outerContext innerContext) parents
        (scannedRegisters_bit registers true eventSuffix notSeen)
      obtain ⟨responseSilent, accepted, allWitnesses⟩ :=
        selectedTarget_response_structure bits bits allowed continuation source
          (Dovetail.clockExit_admissible (r + 1) r environment) registers registerPhase eventSuffix
          outerContext fullContext innerContext targetContext parents ticks trace hb.1 hb.2
          sourceLicensed outerLicensed excludes
          (firstJobPreResponseTime bits r + 1) _ c4 c4Eq (toFrame'.trans entered)
      have publicDecode := CheckpointRun.decodeCarrier?_of_decode SOnly38.program SOnly38.dispatcher.tree
        bits continuation (Dovetail.clockExit_admissible (r + 1) r environment) trace.targetDecode
      have finalTime : firstJobPreResponseTime bits r + 1 + 56 =
          firstJobPreResponseTime bits r + 57 := by omega
      rw [finalTime] at accepted allWitnesses
      refine ⟨accepted, ?_, deletedCarrier true outerContext innerContext, publicDecode, ?_⟩
      · intro index earlier
        change index < firstJobPreResponseTime bits r + 57 at earlier
        by_cases before : index ≤ firstJobPreResponseTime bits r
        · exact licensed_prefix_silent bits allowed prefixChain prefixLicensed excludes index
            (by simpa only [prefixCount] using before)
        · have offsetBound : index - (firstJobPreResponseTime bits r + 1) < 56 := by omega
          have offsetEq : firstJobPreResponseTime bits r + 1 +
              (index - (firstJobPreResponseTime bits r + 1)) = index := by omega
          simpa only [offsetEq] using responseSilent _ offsetBound
      · exact allWitnesses

/-- From only the first source event, derive the first S acceptance and a
single frozen audit shared by all accepted occurrences, even for source words
whose numerical decoding fails. Prior nonemptiness follows from absorption. -/
theorem firstSourceEvent_structure (bits : List Bool) (r : Nat)
    (noEvent : ∀ k, k < r →
      ¬ SOnlySource.Event (CTS.iterate SOnly38.program k (CTS.initial SOnly38.program bits)))
    (event : SOnlySource.Event
      (CTS.iterate SOnly38.program r (CTS.initial SOnly38.program bits))) :
    SOnlyObserver.event (SOnly38.trajectory bits (firstJobPreResponseTime bits r + 57)) = true ∧
    (∀ index, index < firstJobPreResponseTime bits r + 57 →
      SOnlyObserver.event (SOnly38.trajectory bits index) = false) ∧
    ∃ snapshot,
      CheckpointDecoder.decodeCarrier? SOnly38.program SOnly38.dispatcher.tree snapshot =
        some (CTS.iterate SOnly38.program r (CTS.initial SOnly38.program bits)).data.tail ∧
      ∀ address shell,
        (SOnly38.trajectory bits (firstJobPreResponseTime bits r + 57)).subterm? address = some shell →
        targetPattern.matchesBool shell = true →
        shell.subterm? auditAddress = some snapshot ∧
        readPrestate SOnly38.program SOnly38.dispatcher.tree true shell =
          some (CTS.iterate SOnly38.program r (CTS.initial SOnly38.program bits)).data := by
  let current := CTS.iterate SOnly38.program r (CTS.initial SOnly38.program bits)
  have phaseEq : current.phase = SOnly38.targetPhase := event.1
  have headEq : current.data.head? = some true := event.2
  obtain ⟨suffix, dataEq⟩ : ∃ suffix, current.data = true :: suffix := by
    cases h : current.data with
    | nil => simp [h] at headEq
    | cons bit suffix =>
        have bitEq : bit = true := by simpa [h] using headEq
        exact ⟨suffix, by rw [bitEq]⟩
  have nonempty : current.data ≠ [] := by simp [dataEq]
  have allNonempty := nonempty_prefix_of_nonempty_iterate SOnly38.program
    (CTS.initial SOnly38.program bits) r nonempty
  have stateEq : current = ⟨SOnly38.targetPhase, true :: suffix⟩ := by
    calc
      current = ⟨current.phase, current.data⟩ := by cases current; rfl
      _ = ⟨SOnly38.targetPhase, true :: suffix⟩ := by rw [phaseEq, dataEq]
  obtain ⟨accepted, silent, snapshot, decoded, witnesses⟩ :=
    sourceTarget_first_structure bits r suffix allNonempty noEvent stateEq
  refine ⟨accepted, silent, snapshot, ?_, ?_⟩
  · change CheckpointDecoder.decodeCarrier? SOnly38.program SOnly38.dispatcher.tree snapshot = some current.data.tail
    rw [dataEq]
    exact decoded
  · intro address shell located matched
    have conclusion := witnesses address shell located matched
    refine ⟨conclusion.1, ?_⟩
    change readPrestate SOnly38.program SOnly38.dispatcher.tree true shell = some current.data
    rw [dataEq]
    exact conclusion.2

/-- The earliest-acceptance statement has no parsing-success premise. -/
theorem firstSourceEvent_first_acceptance (bits : List Bool) (r : Nat)
    (noEvent : ∀ k, k < r →
      ¬ SOnlySource.Event (CTS.iterate SOnly38.program k (CTS.initial SOnly38.program bits)))
    (event : SOnlySource.Event
      (CTS.iterate SOnly38.program r (CTS.initial SOnly38.program bits))) :
    SOnlyObserver.event (SOnly38.trajectory bits (firstJobPreResponseTime bits r + 57)) = true ∧
    ∀ index, index < firstJobPreResponseTime bits r + 57 →
      SOnlyObserver.event (SOnly38.trajectory bits index) = false := by
  have result := firstSourceEvent_structure bits r noEvent event
  exact ⟨result.1, result.2.1⟩

end SOnlyGlobalFirstStructure
#print axioms SOnlyGlobalFirstStructure.sourceTarget_first_structure
#print axioms SOnlyGlobalFirstStructure.firstSourceEvent_structure
#print axioms SOnlyGlobalFirstStructure.firstSourceEvent_first_acceptance

#print axioms SOnlyGlobalFirstStructure.target_response_structure
#print axioms SOnlyGlobalFirstStructure.selectedTarget_response_structure
