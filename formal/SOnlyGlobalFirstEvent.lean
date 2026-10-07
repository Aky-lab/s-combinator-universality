import SOnlyGlobalFirstPrefix
import SOnlyFirstEventResponse

/-!
# Global first acceptance and current-tree numeric readout

The entire generated stage prefix is licensed away from the target action.
Its real next C4 contraction supplies the exact bridge to the sharp
56-contraction target response. Therefore the first observer acceptance is
at the fixed 57-contraction offset, and every accepted occurrence has the
same numerical public readout, including the fixed current-tree decoder.
-/
namespace SOnlyGlobalFirstEvent
open PureSFormal PureSFormal.PureS PureSFormal.Research
open SchedulerControl SchedulerInvariant SchedulerCycle SchedulerResponseInvariant
open SchedulerNestedResponse SchedulerCompletedContext SchedulerTraceAlgebra
open SOnlyProvenance SOnlyProvenanceRows SOnlyGeneratedOrigins SOnlySchedulerOrigins
open SOnlyGlobalAncestors SOnlyGlobalOrigins SOnlyGlobalFirstPrefix
open SOnlyResponseLabels SOnlyStageEvents SOnlyEventPattern SOnlyEventTransfer
open SOnlyFirstEventOrigins SOnlyFirstEventResponse
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

/-- An actual licensed generated sample list excludes the target at every
index through its last contraction, including the encoded initial tree. -/
theorem licensed_prefix_silent (bits : List Bool) (allowed : OriginSet SOnly38.program)
    {terminal : SchedulerInvariant.Configuration SOnly38.program SOnly38.dispatcher}
    {configurations : List (SchedulerInvariant.Configuration SOnly38.program SOnly38.dispatcher)}
    (chain : ExactMutationChain (SchedulerControl.machine SOnly38.program SOnly38.dispatcher)
      terminal (SchedulerControl.initialConfiguration SOnly38.program SOnly38.dispatcher bits)
      configurations)
    (licensed : SamplesLicensed (RootLicensed SOnly38.program SOnly38.dispatcher.tree allowed) configurations)
    (excludes : ∀ snapshot, ¬ allowed SOnly38.targetLabel snapshot) :
    ∀ index, index ≤ configurations.length →
      SOnlyObserver.event (SOnly38.trajectory bits index) = false := by
  intro index bounded
  cases index with
  | zero =>
      rw [trajectory_eq_contractionRun]
      exact event_false_of_excludes (initial_licensed _ SOnly38.program SOnly38.dispatcher bits) excludes
  | succ index =>
      have inRange : index < configurations.length := by omega
      let sample := configurations[index]
      have atIndex : configurations[index]? = some sample := by simp [sample, inRange]
      have tree := exactChain_rootReset_sample bits chain (sampleIndex := 0) rfl atIndex
      simp only [Nat.zero_add] at tree
      rw [tree]
      exact event_false_of_excludes (licensed sample (List.getElem_mem inRange)) excludes

/-- The exact first target source event yields the globally first accepted
S-tree. Every target-pattern witness and the deterministic first-preorder
current-tree reader return the supplied numerical value. -/
theorem sourceTarget_globally_first (bits : List Bool) (r : Nat)
    (eventSuffix : List Bool) (value : Nat)
    (allNonempty : ∀ k, k ≤ r →
      (CTS.iterate SOnly38.program k (CTS.initial SOnly38.program bits)).data ≠ [])
    (noEvent : ∀ k, k < r →
      ¬ SOnlySource.Event (CTS.iterate SOnly38.program k (CTS.initial SOnly38.program bits)))
    (event : CTS.iterate SOnly38.program r (CTS.initial SOnly38.program bits) =
      ⟨SOnly38.targetPhase, true :: eventSuffix⟩)
    (numerical : SOnlyResultBits.readMachineBits (true :: eventSuffix) = some value) :
    SOnlyObserver.event (SOnly38.trajectory bits (firstJobPreResponseTime bits r + 57)) = true ∧
    (∀ index, index < firstJobPreResponseTime bits r + 57 →
      SOnlyObserver.event (SOnly38.trajectory bits index) = false) ∧
    (∀ address shell,
      (SOnly38.trajectory bits (firstJobPreResponseTime bits r + 57)).subterm? address = some shell →
      targetPattern.matchesBool shell = true → SOnlyWitnessResult.readShell shell = some value) ∧
    SOnlyCurrentDecoder.read (SOnly38.trajectory bits (firstJobPreResponseTime bits r + 57)) = some value := by
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
      obtain ⟨responseSilent, accepted, allWitnesses, currentRead⟩ :=
        selectedTarget_response_all_witnesses bits bits allowed continuation source
          (Dovetail.clockExit_admissible (r + 1) r environment) registers registerPhase eventSuffix
          outerContext fullContext innerContext targetContext parents ticks trace hb.1 hb.2
          sourceLicensed outerLicensed excludes value numerical
          (firstJobPreResponseTime bits r + 1) _ c4 c4Eq (toFrame'.trans entered)
      have finalTime : firstJobPreResponseTime bits r + 1 + 56 =
          firstJobPreResponseTime bits r + 57 := by omega
      rw [finalTime] at accepted allWitnesses currentRead
      refine ⟨accepted, ?_, ?_, currentRead⟩
      · intro index earlier
        change index < firstJobPreResponseTime bits r + 57 at earlier
        by_cases before : index ≤ firstJobPreResponseTime bits r
        · exact licensed_prefix_silent bits allowed prefixChain prefixLicensed excludes index
            (by simpa only [prefixCount] using before)
        · have offsetBound : index - (firstJobPreResponseTime bits r + 1) < 56 := by omega
          have offsetEq : firstJobPreResponseTime bits r + 1 +
              (index - (firstJobPreResponseTime bits r + 1)) = index := by omega
          simpa only [offsetEq] using responseSilent _ offsetBound
      · intro address shell located matched
        exact (allWitnesses address shell located matched).2

/-- Event-form interface: nonemptiness of the entire required prefix follows
from the designated nonempty event itself. -/
theorem firstSourceEvent_current_read (bits : List Bool) (r value : Nat)
    (noEvent : ∀ k, k < r →
      ¬ SOnlySource.Event (CTS.iterate SOnly38.program k (CTS.initial SOnly38.program bits)))
    (event : SOnlySource.Event
      (CTS.iterate SOnly38.program r (CTS.initial SOnly38.program bits)))
    (numerical : SOnlyResultBits.readMachineBits
      (CTS.iterate SOnly38.program r (CTS.initial SOnly38.program bits)).data = some value) :
    SOnlyObserver.event (SOnly38.trajectory bits (firstJobPreResponseTime bits r + 57)) = true ∧
    (∀ index, index < firstJobPreResponseTime bits r + 57 →
      SOnlyObserver.event (SOnly38.trajectory bits index) = false) ∧
    (∀ address shell,
      (SOnly38.trajectory bits (firstJobPreResponseTime bits r + 57)).subterm? address = some shell →
      targetPattern.matchesBool shell = true → SOnlyWitnessResult.readShell shell = some value) ∧
    SOnlyCurrentDecoder.read (SOnly38.trajectory bits (firstJobPreResponseTime bits r + 57)) = some value := by
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
  have read : SOnlyResultBits.readMachineBits (true :: suffix) = some value := by
    rw [← dataEq]
    exact numerical
  exact sourceTarget_globally_first bits r suffix value allNonempty noEvent stateEq read

#print axioms licensed_prefix_silent
#print axioms sourceTarget_globally_first
#print axioms firstSourceEvent_current_read
end SOnlyGlobalFirstEvent
