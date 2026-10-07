import SOnlyEventResponse
import SOnlySource
import SOnlyObserver

/-!
# Generated stage witnesses for designated CTS events

The stage construction below uses the actual upstream PositiveStages,
clock/fuel, selected nonempty prefix, C4 and response-script constructors.
It does not assume a source-to-S event simulation or arbitrary descendant
provenance. Global exclusion of earlier accepted occurrences is separate.
-/
namespace SOnlyStageEvents

open PureSFormal PureSFormal.PureS PureSFormal.Research
open SchedulerControl SchedulerInvariant SchedulerCycle SchedulerResponseInvariant
open SchedulerNestedResponse SchedulerCompletedContext SchedulerTraceAlgebra
open SOnlyEventTransfer SOnlyEventPattern SOnlyEventResponse

set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

/-- The complete C4-plus-response list, retaining its literal final shell.
The construction works at an arbitrary outer zipper, without classifying the
final sample as a public checkpoint. -/
theorem selectedResponse_chain
    (program : CTS.Program) (dispatcher : ActionDispatcher program)
    (seedBits : List Bool) (continuation source : Term)
    (admissible : Carrier.Admissible continuation)
    (registers : Registers program) (bit : Bool) (suffix : List Bool)
    (outerContext fullContext innerContext targetContext : Context)
    (parents : List ParentFrame) (ticks : Nat)
    (trace : SelectedResponseTrace program dispatcher seedBits continuation source
      admissible registers bit suffix outerContext fullContext innerContext
      targetContext parents ticks)
    (notSeen : registers.seen = false) :
    ∃ configurations last,
      ExactMutationChain (SchedulerControl.machine program dispatcher)
        (selectedReturnConfiguration program dispatcher registers bit suffix seedBits continuation
          (deletedCarrier bit outerContext innerContext) parents)
        (upConfiguration program dispatcher registers omega
          (ContextCursor.frames fullContext omega
            (.right (SchedulerResponse.pendingFunction program dispatcher seedBits continuation) :: parents)))
        configurations ∧
      configurations.length = 1 + LocalResponse.completedCost program
        (dispatcher.route ((scannedRegisters registers bit suffix).phase, bit))
        ((scannedRegisters registers bit suffix).phase, bit) ∧
      LastSample configurations last ∧
      last.cursor.erase = Cursor.rebuild parents
        (LocalResponse.completed seedBits continuation (deletedCarrier bit outerContext innerContext)
          (SchedulerResponse.completedRoute program dispatcher
            (scannedRegisters registers bit suffix) bit
            (deletedCarrier bit outerContext innerContext))) := by
  let carrier := deletedCarrier bit outerContext innerContext
  let finalRegisters := scannedRegisters registers bit suffix
  let fullParents := .right
    (SchedulerResponse.pendingFunction program dispatcher seedBits continuation) :: parents
  let c4 := selectedC4Configuration program dispatcher registers bit
    outerContext innerContext fullParents
  obtain ⟨bound, found⟩ := selected_seekC4 program dispatcher seedBits continuation source
    admissible registers bit suffix parents trace notSeen
  have trace0 : SelectedResponseTrace program dispatcher seedBits continuation source
      admissible registers bit suffix outerContext fullContext innerContext targetContext
      (PrimitiveFuel.pendingParents
        (environmentCode (compileActions program dispatcher.tree) seedBits)
        continuation 0 parents) ticks := by
    simpa [PrimitiveFuel.pendingParents] using trace
  obtain ⟨frameTicks, toFrame⟩ := selectedC4_toFrame_zeroRunAt program dispatcher seedBits
    continuation source admissible registers bit suffix 0 parents trace0 notSeen
  have bitEq : finalRegisters.bit = some bit := scannedRegisters_bit registers bit suffix notSeen
  have entered := SchedulerResponse.enterResponse_zeroRun program dispatcher finalRegisters bit
    seedBits continuation carrier parents bitEq
  obtain ⟨responseConfigurations, responseChain, pairs⟩ :=
    normalResponse_exactPairedMutationChain program dispatcher finalRegisters bit
      seedBits continuation carrier parents
  have toFrame' : ZeroMutationRun (SchedulerControl.machine program dispatcher) frameTicks c4
      (SchedulerResponse.frameConfiguration program dispatcher finalRegisters seedBits
        continuation carrier parents) := by
    simpa [PrimitiveFuel.pendingParents, c4, fullParents, finalRegisters, carrier,
      selectedFrameConfiguration] using toFrame
  have postC4 := ExactMutationChain.prepend (toFrame'.trans entered) responseChain
  have completeChain : ExactMutationChain (SchedulerControl.machine program dispatcher)
      (selectedReturnConfiguration program dispatcher registers bit suffix seedBits continuation carrier parents)
      (upConfiguration program dispatcher registers omega
        (ContextCursor.frames fullContext omega fullParents)) (c4 :: responseConfigurations) := by
    exact .next bound (by simpa [c4, fullParents] using found) postC4
  have flags := responseEntries_finalFlags program
    (dispatcher.route_valid (finalRegisters.phase, bit)) seedBits continuation carrier
  obtain ⟨leading, last, decomposition, erased⟩ :=
    SchedulerNestedResponse.ResponseSamplePairs.terminalDecomposition program dispatcher
      finalRegisters bit seedBits continuation carrier parents pairs flags
  have final : LastSample responseConfigurations last := by
    rw [decomposition]
    exact (LastSample.one last).appendLeft leading
  refine ⟨c4 :: responseConfigurations, last, completeChain, ?_, .cons c4 final, erased⟩
  have count := pairs.length_eq.trans (responseEntries_length program
    (dispatcher.route_valid (finalRegisters.phase, bit)) seedBits continuation carrier)
  simp only [List.length_cons, count]
  exact Nat.add_comm _ _

/-- Contractions before the clock/fuel phase of stage r+1. Stage one begins
after the generator's staging contraction; later stages follow checkpoint r. -/
def stageStartTime (bits : List Bool) : Nat → Nat
  | 0 => 1
  | r + 1 => ExactCheckpointRun.checkpointTime SOnly38.program SOnly38.dispatcher bits (r + 1)

/-- The actual scheduler supplies a finite exact prefix and a generated
completed-parent zipper at every stage start, with no event premise. -/
theorem stageStart_prefix (bits : List Bool) (r : Nat) :
    ∃ parents configurations,
      ExactMutationChain (SchedulerControl.machine SOnly38.program SOnly38.dispatcher)
        (SchedulerRecurrence.stageSourceConfiguration SOnly38.program SOnly38.dispatcher
          bits (r + 1) parents)
        (SchedulerControl.initialConfiguration SOnly38.program SOnly38.dispatcher bits)
        configurations ∧
      configurations.length = stageStartTime bits r ∧
      CompletedParents SOnly38.program SOnly38.dispatcher parents
        (CheckpointRun.cumulativeLayers r) := by
  cases r with
  | zero =>
      exact ⟨[], SchedulerRecurrence.initialPreludeConfigurations SOnly38.program SOnly38.dispatcher bits,
        SchedulerRecurrence.initialPreludeChain SOnly38.program SOnly38.dispatcher bits,
        rfl, CompletedParents.root SOnly38.program SOnly38.dispatcher⟩
  | succ r =>
      obtain ⟨past⟩ := SchedulerRecurrence.positiveStages SOnly38.program SOnly38.dispatcher bits r
      exact ⟨past.nextParents, past.configurations, past.chain, past.count, past.nextOuter⟩

/-- Exact index just before the last response in the first job of stage r+1.
This counts all previous stages, current clock/fuel setup, and r source steps. -/
def firstJobPreResponseTime (bits : List Bool) (r : Nat) : Nat :=
  stageStartTime bits r + (3 * r + 10) +
    nonemptySweepCost SOnly38.program SOnly38.dispatcher r
      (CTS.initial SOnly38.program bits)

/-- Build, rather than assume, the first job's ordered source prefix through
its r-th selected response. The final trace has exactly the CTS prestate c_r.
Every preceding native contraction is retained in the returned exact list. -/
theorem firstJob_response_prefix (bit : Bool) (suffix : List Bool) (r : Nat)
    (allNonempty : ∀ k, k ≤ r →
      (CTS.iterate SOnly38.program k
        (CTS.initial SOnly38.program (bit :: suffix))).data ≠ []) :
    let bits := bit :: suffix
    let environment := environmentCode (compileActions SOnly38.program SOnly38.dispatcher.tree) bits
    let continuation := Dovetail.clockExit (r + 1) r environment
    ∃ parents registers phase responseBit responseSuffix source
        outerContext fullContext innerContext targetContext ticks configurations,
      ExactMutationChain (SchedulerControl.machine SOnly38.program SOnly38.dispatcher)
        (upConfiguration SOnly38.program SOnly38.dispatcher registers omega
          (ContextCursor.frames fullContext omega
            (.right (SchedulerResponse.pendingFunction SOnly38.program SOnly38.dispatcher
              bits continuation) :: parents)))
        (SchedulerControl.initialConfiguration SOnly38.program SOnly38.dispatcher bits)
        configurations ∧
      configurations.length = firstJobPreResponseTime bits r ∧
      RegistersCoherent registers phase [] false ∧
      SelectedResponseTrace SOnly38.program SOnly38.dispatcher bits continuation source
        (Dovetail.clockExit_admissible (r + 1) r environment)
        registers responseBit responseSuffix outerContext fullContext innerContext
        targetContext parents ticks ∧
      ⟨phase, responseBit :: responseSuffix⟩ =
        CTS.iterate SOnly38.program r (CTS.initial SOnly38.program bits) := by
  let bits := bit :: suffix
  let environment := environmentCode (compileActions SOnly38.program SOnly38.dispatcher.tree) bits
  let continuation := Dovetail.clockExit (r + 1) r environment
  obtain ⟨parents, prefixConfigurations, prefixChain, prefixCount, outer⟩ := stageStart_prefix bits r
  let phaseConfigurations := SchedulerNestedPhase.positiveStageConfigurationsAt
    SOnly38.program SOnly38.dispatcher bits (Registers.newJob SOnly38.program) parents r
  have phase := SchedulerNestedPhase.positiveStagePhaseInvariantAt
    SOnly38.program SOnly38.dispatcher bits (Registers.newJob SOnly38.program)
    (CTS.zeroPhase SOnly38.program) [] false (RegistersCoherent.initial SOnly38.program)
    parents (CheckpointRun.cumulativeLayers r) outer (stageStartTime bits r) r
  have phaseChain : ExactMutationChain
      (SchedulerControl.machine SOnly38.program SOnly38.dispatcher)
      (SchedulerNestedPhase.fuelTerminalConfigurationAt SOnly38.program SOnly38.dispatcher
        bits (Registers.newJob SOnly38.program) continuation parents (r + 1) 0)
      (SchedulerRecurrence.stageSourceConfiguration SOnly38.program SOnly38.dispatcher
        bits (r + 1) parents) phaseConfigurations := by
    simpa [phaseConfigurations, continuation, environment,
      SchedulerRecurrence.stageSourceConfiguration] using phase.chain
  obtain ⟨outerContext, fullContext, innerContext, targetContext, descentTicks,
      responseTicks, response, baseRun⟩ := nonemptyBase_toSelected_zeroRunAt
        SOnly38.program SOnly38.dispatcher bit suffix continuation
        (Dovetail.clockExit_admissible (r + 1) r environment) r parents
  have parentSplit : PrimitiveFuel.pendingParents environment continuation (r + 1) parents =
      .right (SchedulerResponse.pendingFunction SOnly38.program SOnly38.dispatcher bits continuation) ::
        PrimitiveFuel.pendingParents environment continuation r parents := by
    simpa [environment, SchedulerResponse.pendingFunction, PendingFrame.environmentCode_eq_envelope,
      PendingFrame.frameFunction] using
      (SchedulerCycle.pendingParents_succ_cons environment continuation r parents)
  have baseRun' : ZeroMutationRun
      (SchedulerControl.machine SOnly38.program SOnly38.dispatcher) descentTicks
      (SchedulerNestedPhase.fuelTerminalConfigurationAt SOnly38.program SOnly38.dispatcher
        bits (Registers.newJob SOnly38.program) continuation parents (r + 1) 0)
      (upConfiguration SOnly38.program SOnly38.dispatcher (Registers.newJob SOnly38.program).clearScan omega
        (ContextCursor.frames fullContext omega
          (.right (SchedulerResponse.pendingFunction SOnly38.program SOnly38.dispatcher bits continuation) ::
            PrimitiveFuel.pendingParents environment continuation r parents))) := by
    rw [← parentSplit]
    exact baseRun
  obtain ⟨finalRegisters, finalPhase, finalBit, finalSuffix, finalSource,
      finalOuterContext, finalFullContext, finalInnerContext, finalTargetContext,
      finalTicks, pendingConfigurations, pendingChain, pendingSampled,
      pendingCount, coherent, finalTrace, sourceEq⟩ :=
    selectedNonemptyPendingPrefixAt SOnly38.program SOnly38.dispatcher bits bits
      continuation (Dovetail.clockExit_admissible (r + 1) r environment)
      parents (CheckpointRun.cumulativeLayers r) outer r
      (stageStartTime bits r + phaseConfigurations.length)
      (Registers.newJob SOnly38.program).clearScan (CTS.zeroPhase SOnly38.program)
      bit suffix (baseCarrier environment continuation)
      outerContext fullContext innerContext targetContext responseTicks
      (RegistersCoherent.initial SOnly38.program).clearScan response allNonempty
  have restChain := ExactMutationChain.prepend baseRun' pendingChain
  have completeChain := SchedulerRecurrence.ExactMutationChain.append prefixChain
    (SchedulerRecurrence.ExactMutationChain.append phaseChain restChain)
  refine ⟨parents, finalRegisters, finalPhase, finalBit, finalSuffix, finalSource,
    finalOuterContext, finalFullContext, finalInnerContext, finalTargetContext,
    finalTicks, prefixConfigurations ++ (phaseConfigurations ++ pendingConfigurations),
    completeChain, ?_, coherent, finalTrace, sourceEq⟩
  simp only [List.length_append, prefixCount, pendingCount]
  rw [SchedulerNestedPhase.positiveStageConfigurationsAt_length]
  simp only [firstJobPreResponseTime, Nat.add_assoc]
  rfl

/-- A designated CTS prestate generates a real F17 witness, at an explicit
sample in the first job of stage r+1, with its exact public-audit readout.
Only source nonemptiness through r is assumed; no generated-stage or script
entry premise remains. This is event completeness, not global firstness. -/
theorem sourceTarget_witness_at (bits : List Bool) (r : Nat) (eventSuffix : List Bool)
    (allNonempty : ∀ k, k ≤ r →
      (CTS.iterate SOnly38.program k (CTS.initial SOnly38.program bits)).data ≠ [])
    (event : CTS.iterate SOnly38.program r (CTS.initial SOnly38.program bits) =
      ⟨SOnly38.targetPhase, true :: eventSuffix⟩) :
    ∃ address shell,
      (SOnly38.trajectory bits (firstJobPreResponseTime bits r + 57)).subterm? address = some shell ∧
      targetPattern.matchesBool shell = true ∧
      readPrestate SOnly38.program SOnly38.dispatcher.tree true shell = some (true :: eventSuffix) := by
  cases bits with
  | nil =>
      exact (allNonempty 0 (Nat.zero_le r) rfl).elim
  | cons bit suffix =>
      let bits := bit :: suffix
      let environment := environmentCode (compileActions SOnly38.program SOnly38.dispatcher.tree) bits
      let continuation := Dovetail.clockExit (r + 1) r environment
      obtain ⟨parents, registers, phase, responseBit, responseSuffix, source,
          outerContext, fullContext, innerContext, targetContext, ticks, prefixConfigurations,
          prefixChain, prefixCount, coherent, trace, sourceEq⟩ :=
        firstJob_response_prefix bit suffix r allNonempty
      have configurationEq := sourceEq.trans event
      have phaseEq : phase = SOnly38.targetPhase := congrArg CTS.Config.phase configurationEq
      have dataEq : responseBit :: responseSuffix = true :: eventSuffix := congrArg CTS.Config.data configurationEq
      have bitEq := (List.cons.inj dataEq).1
      have suffixEq := (List.cons.inj dataEq).2
      subst responseBit
      subst responseSuffix
      have notSeen : registers.seen = false := by simpa [scanSeen] using coherent.seen_eq
      obtain ⟨responseConfigurations, last, responseChain, responseCount, final, erased⟩ :=
        selectedResponse_chain SOnly38.program SOnly38.dispatcher bits continuation source
          (Dovetail.clockExit_admissible (r + 1) r environment) registers true eventSuffix
          outerContext fullContext innerContext targetContext parents ticks trace notSeen
      have scannedPhase : (scannedRegisters registers true eventSuffix).phase = SOnly38.targetPhase :=
        (scannedRegisters_coherentAt SOnly38.program registers phase coherent true eventSuffix).phase_eq.trans phaseEq
      have labelEq : ((scannedRegisters registers true eventSuffix).phase, true) = SOnly38.targetLabel := by
        rw [scannedPhase]
        rfl
      rw [labelEq, SOnly38.target_selected_route, target_response_cost] at responseCount
      have fullChain := SchedulerRecurrence.ExactMutationChain.append prefixChain responseChain
      have fullLast : LastSample (prefixConfigurations ++ responseConfigurations) last := final.appendLeft prefixConfigurations
      have fullCount : (prefixConfigurations ++ responseConfigurations).length =
          firstJobPreResponseTime bits r + 57 := by
        rw [List.length_append, prefixCount, responseCount]
      have sampled := SchedulerTraceAlgebra.ExactMutationChain.contractionRun_eq_last
        SOnly38.program SOnly38.dispatcher bits
        (SchedulerRecurrence.initialGood SOnly38.program SOnly38.dispatcher bits)
        fullChain fullLast (sampleIndex := 0) rfl
      have treeEq : SOnly38.trajectory bits (firstJobPreResponseTime bits r + 57) =
          Cursor.rebuild parents
            (LocalResponse.completed bits continuation (deletedCarrier true outerContext innerContext)
              (SchedulerResponse.completedRoute SOnly38.program SOnly38.dispatcher
                (scannedRegisters registers true eventSuffix) true
                (deletedCarrier true outerContext innerContext))) := by
        rw [trajectory_eq_contractionRun]
        rw [Nat.zero_add, fullCount] at sampled
        rw [sampled]
        exact erased
      let shell := LocalResponse.completed bits continuation
        (deletedCarrier true outerContext innerContext)
        (SchedulerResponse.completedRoute SOnly38.program SOnly38.dispatcher
          (scannedRegisters registers true eventSuffix) true
          (deletedCarrier true outerContext innerContext))
      let cursor : Cursor := ⟨shell, parents⟩
      refine ⟨RootResetSelectorContract.cursorAddress cursor, shell, ?_, ?_, ?_⟩
      · rw [treeEq]
        exact RootResetSelectorContract.subterm?_erase_cursorAddress cursor
      · exact completed_target_matches (scannedRegisters registers true eventSuffix)
          scannedPhase bits continuation (deletedCarrier true outerContext innerContext)
      · exact completed_readPrestate SOnly38.program SOnly38.dispatcher.tree bits continuation
          (deletedCarrier true outerContext innerContext) _
          (Dovetail.clockExit_admissible (r + 1) r environment) true eventSuffix trace.targetDecode

/-- CTS emptiness is absorbing in data. A later nonempty configuration proves
nonemptiness of every earlier prestate, without a source-compiler premise. -/
theorem nonempty_prefix_of_nonempty_iterate
    (program : CTS.Program) (initial : CTS.Config program) (r : Nat)
    (nonempty : (CTS.iterate program r initial).data ≠ []) :
    ∀ k, k ≤ r → (CTS.iterate program k initial).data ≠ [] := by
  intro k bound empty
  have stateEq : CTS.iterate program k initial =
      ⟨(CTS.iterate program k initial).phase, []⟩ := by
    cases state : CTS.iterate program k initial with
    | mk phase data =>
        have dataEq : data = [] := by simpa [state] using empty
        simp [dataEq]
  have later : (CTS.iterate program r initial).data = [] := by
    rw [← Nat.sub_add_cancel bound, CTS.iterate_add, stateEq]
    exact CTS.iterate_empty_data program (r - k) _
  exact nonempty later

/-- Global event completeness for the actual fixed finite observer. The sole
premise is a designated CTS event; all nonempty-prefix, stage-entry, and
response-occurrence facts are constructed. The selected witness's public
reader returns the exact CTS event prestate. -/
theorem sourceEvent_reaches_observer (bits : List Bool) (r : Nat)
    (event : SOnlySource.Event
      (CTS.iterate SOnly38.program r (CTS.initial SOnly38.program bits))) :
    ∃ n address shell,
      SOnlyObserver.event (SOnly38.trajectory bits n) = true ∧
      (SOnly38.trajectory bits n).subterm? address = some shell ∧
      targetPattern.matchesBool shell = true ∧
      readPrestate SOnly38.program SOnly38.dispatcher.tree true shell =
        some (CTS.iterate SOnly38.program r (CTS.initial SOnly38.program bits)).data := by
  let config := CTS.iterate SOnly38.program r (CTS.initial SOnly38.program bits)
  have phaseEq : config.phase = SOnly38.targetPhase := event.1
  have headEq : config.data.head? = some true := event.2
  have witness : ∃ suffix, config.data = true :: suffix := by
    cases dataEq : config.data with
    | nil => simp [dataEq] at headEq
    | cons bit suffix =>
        have bitEq : bit = true := by simpa [dataEq] using headEq
        exact ⟨suffix, by rw [bitEq]⟩
  obtain ⟨suffix, dataEq⟩ := witness
  have nonempty : config.data ≠ [] := by rw [dataEq]; simp
  have nonemptyPrefix := nonempty_prefix_of_nonempty_iterate SOnly38.program
    (CTS.initial SOnly38.program bits) r nonempty
  have eventEq : config = ⟨SOnly38.targetPhase, true :: suffix⟩ := by
    calc
      config = ⟨config.phase, config.data⟩ := by cases config; rfl
      _ = ⟨SOnly38.targetPhase, true :: suffix⟩ := by rw [phaseEq, dataEq]
  obtain ⟨address, shell, located, matched, decoded⟩ :=
    sourceTarget_witness_at bits r suffix nonemptyPrefix eventEq
  refine ⟨firstJobPreResponseTime bits r + 57, address, shell, ?_, located, matched, ?_⟩
  · exact (SOnlyObserver.event_iff_matches _).mpr ⟨address, shell, located, matched⟩
  · simpa only [← dataEq] using decoded

end SOnlyStageEvents

#print axioms SOnlyStageEvents.selectedResponse_chain
#print axioms SOnlyStageEvents.stageStart_prefix

#print axioms SOnlyStageEvents.firstJob_response_prefix

#print axioms SOnlyStageEvents.sourceTarget_witness_at

#print axioms SOnlyStageEvents.nonempty_prefix_of_nonempty_iterate
#print axioms SOnlyStageEvents.sourceEvent_reaches_observer
