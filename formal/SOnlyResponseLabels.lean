import SOnlyStageEvents

/-!
# Source-indexed labels in actual nonempty response lists

This module strengthens the generated selected-prefix constructor rather than
assuming that arbitrary public carrier grammar has a source history. Labels
here belong to actual normal-response script controls in the literal sample
list. Global descendant-origin preservation remains a distinct obligation.
-/
namespace SOnlyResponseLabels

open PureSFormal PureSFormal.PureS PureSFormal.Research
open SchedulerControl SchedulerInvariant SchedulerCycle SchedulerResponseInvariant
open SchedulerNestedResponse SchedulerCompletedContext SchedulerTraceAlgebra
open SOnlyStageEvents

set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

/-- Read a label only from an actual executing normal-response script. -/
def responseLabel? (program : CTS.Program) (dispatcher : ActionDispatcher program)
    (configuration : SchedulerInvariant.Configuration program dispatcher) : Option (ActionLabel program) :=
  match configuration.control with
  | some (.script (.normalResponse label) _ _) => some label
  | _ => none

/-- No other normal-response label occurs in this exact sample list. -/
def OnlyLabel (program : CTS.Program) (dispatcher : ActionDispatcher program)
    (label : ActionLabel program)
    (configurations : List (SchedulerInvariant.Configuration program dispatcher)) : Prop :=
  ∀ configuration, configuration ∈ configurations → ∀ observed,
    responseLabel? program dispatcher configuration = some observed → observed = label

/-- Deterministic executable searches make equal-length exact chains from the
same literal configuration have identical ordered lists, regardless of their
cursor-only terminal suffixes. -/
theorem exactChains_same_samples
    (program : CTS.Program) (dispatcher : ActionDispatcher program)
    {terminal before : SchedulerInvariant.Configuration program dispatcher}
    {configurations : List (SchedulerInvariant.Configuration program dispatcher)}
    (chain : ExactMutationChain (SchedulerControl.machine program dispatcher) terminal before configurations) :
    ∀ {otherTerminal otherConfigurations},
      ExactMutationChain (SchedulerControl.machine program dispatcher)
        otherTerminal before otherConfigurations →
      configurations.length = otherConfigurations.length → configurations = otherConfigurations := by
  induction chain with
  | done ticks suffix =>
      intro otherTerminal otherConfigurations other count
      have empty : otherConfigurations = [] := by simpa using count.symm
      exact empty.symm
  | @next before sample samples ticks found tail ih =>
      intro otherTerminal otherConfigurations other count
      cases other with
      | done otherTicks suffix => simp at count
      | @next _ otherSample otherSamples otherTicks otherFound otherTail =>
          have first := SchedulerBound.seekMutation_bound program dispatcher found
          have second := SchedulerBound.seekMutation_bound program dispatcher otherFound
          have same : sample = otherSample := Option.some.inj (first.symm.trans second)
          subst otherSample
          have tailCount : samples.length = otherSamples.length := Nat.succ.inj count
          exact congrArg (sample :: ·) (ih otherTail tailCount)

/-- The response-pair constructor carries the literal script label at every
sample, without inspecting any descendant carrier or audit. -/
theorem responsePairs_onlyLabel
    {program : CTS.Program} {dispatcher : ActionDispatcher program}
    {registers : Registers program} {bit : Bool} {seedBits : List Bool}
    {continuation carrier : Term} {parents : List ParentFrame}
    {configurations : List (SchedulerInvariant.Configuration program dispatcher)}
    {entries : List (Bool × Term)}
    (pairs : ResponseSamplePairs program dispatcher registers bit seedBits continuation
      carrier parents configurations entries) :
    OnlyLabel program dispatcher (registers.phase, bit) configurations := by
  induction pairs with
  | nil => intro configuration member; cases member
  | @cons pc cursor done term position eraseEq root configurationTail entryTail tail ih =>
      intro configuration member observed labelEq
      rcases List.mem_cons.mp member with same | later
      · subst configuration
        exact (Option.some.inj labelEq).symm
      · exact ih configuration later observed labelEq

/-- Construct the complete selected C4/response chain with its exact script
label invariant, at arbitrary outer parents. -/
theorem selectedResponse_labelledChain
    (program : CTS.Program) (dispatcher : ActionDispatcher program)
    (seedBits : List Bool) (continuation source : Term)
    (admissible : Carrier.Admissible continuation)
    (registers : Registers program) (bit : Bool) (suffix : List Bool)
    (outerContext fullContext innerContext targetContext : Context)
    (parents : List ParentFrame) (ticks : Nat)
    (trace : SelectedResponseTrace program dispatcher seedBits continuation source
      admissible registers bit suffix outerContext fullContext innerContext targetContext parents ticks)
    (notSeen : registers.seen = false) :
    ∃ configurations,
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
      OnlyLabel program dispatcher ((scannedRegisters registers bit suffix).phase, bit) configurations := by
  let carrier := deletedCarrier bit outerContext innerContext
  let finalRegisters := scannedRegisters registers bit suffix
  let fullParents := .right (SchedulerResponse.pendingFunction program dispatcher seedBits continuation) :: parents
  let c4 := selectedC4Configuration program dispatcher registers bit outerContext innerContext fullParents
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
  obtain ⟨responseConfigurations, responseChain, pairs⟩ := normalResponse_exactPairedMutationChain
    program dispatcher finalRegisters bit seedBits continuation carrier parents
  have toFrame' : ZeroMutationRun (SchedulerControl.machine program dispatcher) frameTicks c4
      (SchedulerResponse.frameConfiguration program dispatcher finalRegisters seedBits continuation carrier parents) := by
    simpa [PrimitiveFuel.pendingParents, c4, fullParents, finalRegisters, carrier,
      selectedFrameConfiguration] using toFrame
  have postC4 := ExactMutationChain.prepend (toFrame'.trans entered) responseChain
  refine ⟨c4 :: responseConfigurations, .next bound (by simpa [c4, fullParents] using found) postC4, ?_, ?_⟩
  · have count := pairs.length_eq.trans (responseEntries_length program
      (dispatcher.route_valid (finalRegisters.phase, bit)) seedBits continuation carrier)
    simp only [List.length_cons, count]
    exact Nat.add_comm _ _
  · intro configuration member observed labelEq
    rcases List.mem_cons.mp member with same | later
    · subst configuration
      simp [responseLabel?, c4, selectedC4Configuration, upConfiguration] at labelEq
    · exact responsePairs_onlyLabel pairs configuration later observed labelEq

/-- Recover the label invariant for any equal-length exact response segment
returned by another upstream constructor, via actual executable determinism. -/
theorem selectedResponse_onlyLabel
    (program : CTS.Program) (dispatcher : ActionDispatcher program)
    (seedBits : List Bool) (continuation source : Term)
    (admissible : Carrier.Admissible continuation)
    (registers : Registers program) (bit : Bool) (suffix : List Bool)
    (outerContext fullContext innerContext targetContext : Context)
    (parents : List ParentFrame) (ticks : Nat)
    (trace : SelectedResponseTrace program dispatcher seedBits continuation source
      admissible registers bit suffix outerContext fullContext innerContext targetContext parents ticks)
    (notSeen : registers.seen = false)
    {terminal : SchedulerInvariant.Configuration program dispatcher}
    {configurations : List (SchedulerInvariant.Configuration program dispatcher)}
    (chain : ExactMutationChain (SchedulerControl.machine program dispatcher) terminal
      (upConfiguration program dispatcher registers omega
        (ContextCursor.frames fullContext omega
          (.right (SchedulerResponse.pendingFunction program dispatcher seedBits continuation) :: parents))) configurations)
    (count : configurations.length = 1 + LocalResponse.completedCost program
      (dispatcher.route ((scannedRegisters registers bit suffix).phase, bit))
      ((scannedRegisters registers bit suffix).phase, bit)) :
    OnlyLabel program dispatcher ((scannedRegisters registers bit suffix).phase, bit) configurations := by
  obtain ⟨canonical, canonicalChain, canonicalCount, labelled⟩ :=
    selectedResponse_labelledChain program dispatcher seedBits continuation source admissible
      registers bit suffix outerContext fullContext innerContext targetContext parents ticks trace notSeen
  have same := exactChains_same_samples program dispatcher chain canonicalChain (count.trans canonicalCount.symm)
  exact same.symm ▸ labelled

/-- Semantic source label, absent exactly on an empty queue. -/
def sourceLabel? (program : CTS.Program) (current : CTS.Config program) : Option (ActionLabel program) :=
  match current.data with
  | [] => none
  | bit :: _ => some (current.phase, bit)

/-- Every normal-response control label belongs to an actual ordered source
prestate in the specified finite prefix. This is stronger than endpoint CTS
correctness and weaker than descendant event provenance. -/
def SourceLabels (program : CTS.Program) (dispatcher : ActionDispatcher program)
    (initial : CTS.Config program) (count : Nat)
    (configurations : List (SchedulerInvariant.Configuration program dispatcher)) : Prop :=
  ∀ configuration, configuration ∈ configurations → ∀ observed,
    responseLabel? program dispatcher configuration = some observed →
    ∃ index, index < count ∧ sourceLabel? program (CTS.iterate program index initial) = some observed

/-- Prepending the current response preserves the source order; tail indices
shift by one under the actual CTS iterate law. -/
theorem sourceLabels_prepend
    (program : CTS.Program) (dispatcher : ActionDispatcher program)
    (phase : CTS.Phase program) (bit : Bool) (suffix : List Bool) (count : Nat)
    {first tail : List (SchedulerInvariant.Configuration program dispatcher)}
    (firstLabels : OnlyLabel program dispatcher (phase, bit) first)
    (tailLabels : SourceLabels program dispatcher
      (CTS.absorbingStep program ⟨phase, bit :: suffix⟩) count tail) :
    SourceLabels program dispatcher ⟨phase, bit :: suffix⟩ (count + 1) (first ++ tail) := by
  intro configuration member observed labelEq
  rcases List.mem_append.mp member with firstMember | tailMember
  · have same := firstLabels configuration firstMember observed labelEq
    refine ⟨0, Nat.zero_lt_succ count, ?_⟩
    rw [same]
    rfl
  · obtain ⟨index, bound, sourceEq⟩ := tailLabels configuration tailMember observed labelEq
    refine ⟨index + 1, Nat.succ_lt_succ bound, ?_⟩
    rw [CTS.iterate_add]
    exact sourceEq

/-!
The following recursion strengthens the pinned selectedNonemptyPendingPrefixAt
construction. Its original exact chains, counts, sampled-state certificates,
and terminal source equation are preserved, with SourceLabels added. The
strengthening follows the real C4/response/zero-bridge concatenation.
-/
theorem selectedNonemptyPendingPrefix_labelled
    (program : CTS.Program) (dispatcher : ActionDispatcher program)
    (inputBits seedBits : List Bool) (continuation : Term)
    (hadmissible : Carrier.Admissible continuation)
    (outerParents : List ParentFrame) (layers : Nat)
    (outer : CompletedParents program dispatcher outerParents layers) :
    ∀ (remaining sampleIndex : Nat) (registers : Registers program)
      (phase : CTS.Phase program) (bit : Bool) (suffix : List Bool)
      (source : Term)
      (outerContext fullContext innerContext targetContext : Context)
      (ticks : Nat),
      RegistersCoherent registers phase [] false →
      SelectedResponseTrace program dispatcher seedBits continuation source
        hadmissible registers bit suffix outerContext fullContext innerContext
        targetContext
        (PrimitiveFuel.pendingParents
          (environmentCode (compileActions program dispatcher.tree) seedBits)
          continuation remaining outerParents) ticks →
      (∀ k, k ≤ remaining →
        (CTS.iterate program k ⟨phase, bit :: suffix⟩).data ≠ []) →
      ∃ finalRegisters finalPhase finalBit finalSuffix finalSource
          finalOuterContext finalFullContext finalInnerContext
          finalTargetContext finalTicks configurations,
        ExactMutationChain (SchedulerControl.machine program dispatcher)
          (upConfiguration program dispatcher finalRegisters omega
            (ContextCursor.frames finalFullContext omega
              (.right (SchedulerResponse.pendingFunction program dispatcher
                seedBits continuation) :: outerParents)))
          (upConfiguration program dispatcher registers omega
            (ContextCursor.frames fullContext omega
              (.right (SchedulerResponse.pendingFunction program dispatcher
                seedBits continuation) ::
                PrimitiveFuel.pendingParents
                  (environmentCode
                    (compileActions program dispatcher.tree) seedBits)
                  continuation remaining outerParents))) configurations ∧
        IndexedResponseSampledStates program dispatcher inputBits sampleIndex
          configurations ∧
        configurations.length =
          nonemptySweepCost program dispatcher remaining
            ⟨phase, bit :: suffix⟩ ∧
        RegistersCoherent finalRegisters finalPhase [] false ∧
        SelectedResponseTrace program dispatcher seedBits continuation
          finalSource hadmissible finalRegisters finalBit finalSuffix
          finalOuterContext finalFullContext finalInnerContext finalTargetContext
          outerParents finalTicks ∧
        ⟨finalPhase, finalBit :: finalSuffix⟩ =
          CTS.iterate program remaining ⟨phase, bit :: suffix⟩ ∧
        SourceLabels program dispatcher ⟨phase, bit :: suffix⟩ remaining configurations
  | 0, sampleIndex, registers, phase, bit, suffix, source, outerContext,
      fullContext, innerContext, targetContext, ticks, coherent, trace,
      allNonempty => by
      refine ⟨registers, phase, bit, suffix, source, outerContext, fullContext,
        innerContext, targetContext, ticks, [], ?_, .nil sampleIndex, rfl,
        coherent, ?_, rfl, ?_⟩
      · exact .done 0 ⟨rfl, rfl⟩
      · simpa [PrimitiveFuel.pendingParents] using trace
      · intro configuration member; cases member
  | remaining + 1, sampleIndex, registers, phase, bit, suffix, source,
      outerContext, fullContext, innerContext, targetContext, ticks, coherent,
      trace, allNonempty => by
      let encodedEnvironment :=
        environmentCode (compileActions program dispatcher.tree) seedBits
      let afterParents := PrimitiveFuel.pendingParents encodedEnvironment
        continuation (remaining + 1) outerParents
      let nextParents := PrimitiveFuel.pendingParents encodedEnvironment
        continuation remaining outerParents
      let finalRegisters := scannedRegisters registers bit suffix
      let carrier := deletedCarrier bit outerContext innerContext
      have firstNonempty :
          (CTS.absorbingStep program ⟨phase, bit :: suffix⟩).data ≠ [] := by
        have indexed := allNonempty 1
          (Nat.succ_le_succ (Nat.zero_le remaining))
        simpa [CTS.iterate] using indexed
      cases dataEq :
          (CTS.absorbingStep program ⟨phase, bit :: suffix⟩).data with
      | nil => exact (firstNonempty dataEq).elim
      | cons nextBit nextSuffix =>
          have dataEqRegisters :
              (CTS.absorbingStep program
                ⟨registers.phase, bit :: suffix⟩).data =
                  nextBit :: nextSuffix := by
            rw [coherent.phase_eq]
            exact dataEq
          have parentSplit : afterParents =
              .right (SchedulerResponse.pendingFunction program dispatcher
                seedBits continuation) :: nextParents := by
            simpa [afterParents, nextParents, encodedEnvironment,
              SchedulerResponse.pendingFunction,
              PendingFrame.environmentCode_eq_envelope,
              PendingFrame.frameFunction] using
              (SchedulerCycle.pendingParents_succ_cons encodedEnvironment
                continuation remaining outerParents)
          have cycleTrace : SelectedResponseTrace program dispatcher seedBits
              continuation source hadmissible registers bit suffix outerContext
              fullContext innerContext targetContext
              (.right (SchedulerResponse.pendingFunction program dispatcher
                seedBits continuation) :: nextParents) ticks := by
            rw [← parentSplit]
            simpa [afterParents, encodedEnvironment] using trace
          obtain ⟨firstConfigurations, firstChain, firstSampled, firstLength⟩ :=
            selectedPendingSegmentAt program dispatcher inputBits seedBits
              continuation source hadmissible registers phase coherent bit suffix
              (remaining + 1) sampleIndex (Nat.succ_ne_zero remaining)
              outerParents layers outer
              (by simpa [encodedEnvironment] using trace)
          have notSeen : registers.seen = false := by
            simpa using! coherent.seen_eq
          have noTail : registers.tail = false := by
            simpa using! coherent.tail_eq
          obtain ⟨nextContext, nextOuterContext, nextFullContext,
              nextInnerContext, nextTargetContext, returnTicks, downTicks,
              nextTicks, cycle⟩ :=
            pendingNonemptyCycleTrace program dispatcher seedBits continuation
              source hadmissible registers bit suffix nextParents ticks cycleTrace
              notSeen noTail nextBit nextSuffix dataEqRegisters
          have scannedCoherent : RegistersCoherent finalRegisters phase
              (bit :: suffix) false :=
            scannedRegisters_coherentAt program registers phase coherent bit
              suffix
          have firstLabels := selectedResponse_onlyLabel program dispatcher seedBits
            continuation source hadmissible registers bit suffix outerContext fullContext
            innerContext targetContext afterParents ticks
            (by simpa [afterParents, encodedEnvironment] using trace)
            notSeen firstChain firstLength
          have firstPhase : (scannedRegisters registers bit suffix).phase = phase :=
            scannedCoherent.phase_eq
          rw [firstPhase] at firstLabels
          have nextCoherent : RegistersCoherent finalRegisters.advance
              (CTS.nextPhase program phase) [] false := scannedCoherent.advance
          have stepEq :
              CTS.absorbingStep program ⟨phase, bit :: suffix⟩ =
                ⟨CTS.nextPhase program phase, nextBit :: nextSuffix⟩ := by
            cases step : CTS.absorbingStep program
                ⟨phase, bit :: suffix⟩ with
            | mk nextPhase output =>
                have phaseEq : nextPhase = CTS.nextPhase program phase := by
                  simpa [step] using
                    (CTS.absorbingStep_phase program
                      ⟨phase, bit :: suffix⟩)
                have outputEq : output = nextBit :: nextSuffix := by
                  simpa [step] using dataEq
                subst nextPhase
                subst output
                rfl
          have tailNonempty : ∀ k, k ≤ remaining →
              (CTS.iterate program k
                ⟨CTS.nextPhase program phase, nextBit :: nextSuffix⟩).data ≠
                  [] := by
            intro k bound
            have shiftedBound : k + 1 ≤ remaining + 1 :=
              Nat.succ_le_succ bound
            have shifted := allNonempty (k + 1) shiftedBound
            have iterateEq :
                CTS.iterate program (k + 1) ⟨phase, bit :: suffix⟩ =
                  CTS.iterate program k
                    ⟨CTS.nextPhase program phase,
                      nextBit :: nextSuffix⟩ := by
              rw [CTS.iterate_add]
              change CTS.iterate program k
                  (CTS.absorbingStep program ⟨phase, bit :: suffix⟩) = _
              rw [stepEq]
            rw [iterateEq] at shifted
            exact shifted
          obtain ⟨terminalRegisters, terminalPhase, terminalBit,
              terminalSuffix, terminalSource, terminalOuterContext,
              terminalFullContext, terminalInnerContext, terminalTargetContext,
              terminalTicks, tailConfigurations, tailChain, tailSampled,
              tailLength, terminalCoherent, terminalTrace, terminalEq, terminalLabels⟩ :=
            selectedNonemptyPendingPrefix_labelled program dispatcher inputBits seedBits
              continuation hadmissible outerParents layers outer remaining
              (sampleIndex + firstConfigurations.length) finalRegisters.advance
              (CTS.nextPhase program phase) nextBit nextSuffix
              (LocalResponse.completed seedBits continuation carrier
                (SchedulerResponse.completedRoute program dispatcher
                  finalRegisters bit carrier))
              nextOuterContext nextFullContext nextInnerContext nextTargetContext
              nextTicks nextCoherent (by
                simpa [nextParents, encodedEnvironment, finalRegisters, carrier]
                  using cycle.nextResponse)
              tailNonempty
          obtain ⟨bridgeDownTicks, bridgeDown⟩ := run_downDescent
            finalRegisters.advance cycle.nextResponse.sourceDescent
            (.right (SchedulerResponse.pendingFunction program dispatcher
              seedBits continuation) :: nextParents)
          have bridge : ZeroMutationRun
              (SchedulerControl.machine program dispatcher)
              (returnTicks + bridgeDownTicks)
              (selectedReturnConfiguration program dispatcher registers bit
                suffix seedBits continuation carrier afterParents)
              (upConfiguration program dispatcher finalRegisters.advance omega
                (ContextCursor.frames nextFullContext omega
                  (.right (SchedulerResponse.pendingFunction program dispatcher
                    seedBits continuation) :: nextParents))) := by
            have down' : ZeroMutationRun
                (SchedulerControl.machine program dispatcher) bridgeDownTicks
                (freshPendingDownConfiguration program dispatcher registers bit
                  suffix seedBits continuation carrier nextParents)
                (upConfiguration program dispatcher finalRegisters.advance omega
                  (ContextCursor.frames nextFullContext omega
                    (.right (SchedulerResponse.pendingFunction program dispatcher
                      seedBits continuation) :: nextParents))) := by
              simpa [freshPendingDownConfiguration,
                SchedulerResponse.freshNestedDownConfiguration,
                SchedulerResponse.normalPendingDownConfiguration,
                finalRegisters, carrier] using! bridgeDown
            have combined := cycle.returnToDown.trans down'
            rw [parentSplit]
            simpa [pendingReturnConfiguration, selectedReturnConfiguration,
              finalRegisters, carrier] using! combined
          have linkedTail := ExactMutationChain.prepend bridge tailChain
          have completeChain := SchedulerRecurrence.ExactMutationChain.append
            firstChain linkedTail
          have completeSampled :=
            SchedulerNestedPhase.IndexedResponseSampledStates.append program
              dispatcher inputBits firstSampled (by simpa using tailSampled)
          have sourceLabels : SourceLabels program dispatcher ⟨phase, bit :: suffix⟩
              (remaining + 1) (firstConfigurations ++ tailConfigurations) :=
            sourceLabels_prepend program dispatcher phase bit suffix remaining firstLabels
              (by simpa only [stepEq] using terminalLabels)
          refine ⟨terminalRegisters, terminalPhase, terminalBit,
            terminalSuffix, terminalSource, terminalOuterContext,
            terminalFullContext, terminalInnerContext, terminalTargetContext,
            terminalTicks, firstConfigurations ++ tailConfigurations, ?_,
            completeSampled, ?_, terminalCoherent, terminalTrace, ?_, sourceLabels⟩
          · simpa [encodedEnvironment, afterParents, nextParents,
              finalRegisters, carrier] using completeChain
          · simp only [List.length_append]
            rw [firstLength, tailLength]
            have finalPhaseEq : finalRegisters.phase = registers.phase :=
              scannedCoherent.phase_eq.trans coherent.phase_eq.symm
            calc
              (1 + LocalResponse.completedCost program
                    (dispatcher.route (finalRegisters.phase, bit))
                    (finalRegisters.phase, bit)) +
                  nonemptySweepCost program dispatcher remaining
                    ⟨CTS.nextPhase program phase,
                      nextBit :: nextSuffix⟩ =
                  CheckedTransition.totalCost program dispatcher phase
                      (bit :: suffix) +
                    nonemptySweepCost program dispatcher remaining
                      ⟨CTS.nextPhase program phase,
                        nextBit :: nextSuffix⟩ := by
                rw [finalPhaseEq, coherent.phase_eq,
                  CheckedTransition.totalCost_cons, dataEq,
                  CheckedTransition.markerCost_cons, Nat.add_zero]
              _ = CheckedTransition.totalCost program dispatcher phase
                      (bit :: suffix) +
                    nonemptySweepCost program dispatcher remaining
                      (CTS.absorbingStep program
                        ⟨phase, bit :: suffix⟩) := by
                rw [stepEq]
              _ = nonemptySweepCost program dispatcher (remaining + 1)
                    ⟨phase, bit :: suffix⟩ :=
                (nonemptySweepCost_succ program dispatcher remaining
                  ⟨phase, bit :: suffix⟩).symm
          · have iterateEq :
                CTS.iterate program (remaining + 1)
                    ⟨phase, bit :: suffix⟩ =
                  CTS.iterate program remaining
                    ⟨CTS.nextPhase program phase,
                      nextBit :: nextSuffix⟩ := by
              rw [CTS.iterate_add]
              change CTS.iterate program remaining
                  (CTS.absorbingStep program ⟨phase, bit :: suffix⟩) = _
              rw [stepEq]
            exact terminalEq.trans iterateEq.symm

/-- Appending the final response names source index count, preserving all
strictly earlier source indices of the pending prefix. -/
theorem sourceLabels_append_last
    (program : CTS.Program) (dispatcher : ActionDispatcher program)
    (initial : CTS.Config program) (count : Nat)
    (phase : CTS.Phase program) (bit : Bool) (suffix : List Bool)
    (sourceEq : ⟨phase, bit :: suffix⟩ = CTS.iterate program count initial)
    {first last : List (SchedulerInvariant.Configuration program dispatcher)}
    (firstLabels : SourceLabels program dispatcher initial count first)
    (lastLabels : OnlyLabel program dispatcher (phase, bit) last) :
    SourceLabels program dispatcher initial (count + 1) (first ++ last) := by
  intro configuration member observed labelEq
  rcases List.mem_append.mp member with firstMember | lastMember
  · obtain ⟨index, bound, source⟩ := firstLabels configuration firstMember observed labelEq
    exact ⟨index, Nat.lt_trans bound (Nat.lt_succ_self count), source⟩
  · have same := lastLabels configuration lastMember observed labelEq
    refine ⟨count, Nat.lt_succ_self count, ?_⟩
    rw [← sourceEq, same]
    rfl

/-- Every exact complete all-nonempty bounded job from its real Base-producing
fuel sample has only genuine source-prefix script labels. The endpoint may
include an arbitrary mutation-free return/continuation suffix: deterministic
same-length sample equality removes the need to reprove every return path. -/
theorem completeNonemptyJob_sourceLabels
    (program : CTS.Program) (dispatcher : ActionDispatcher program)
    (bit : Bool) (suffix : List Bool) (remaining : Nat)
    (continuation : Term) (admissible : Carrier.Admissible continuation)
    (parents : List ParentFrame) (layers : Nat)
    (outer : CompletedParents program dispatcher parents layers)
    (allNonempty : ∀ k, k ≤ remaining + 1 →
      (CTS.iterate program k (CTS.initial program (bit :: suffix))).data ≠ [])
    {terminal : SchedulerInvariant.Configuration program dispatcher}
    {configurations : List (SchedulerInvariant.Configuration program dispatcher)}
    (chain : ExactMutationChain (SchedulerControl.machine program dispatcher) terminal
      (SchedulerNestedPhase.fuelTerminalConfigurationAt program dispatcher (bit :: suffix)
        (Registers.newJob program) continuation parents (remaining + 1) 0) configurations)
    (count : configurations.length = ExactCheckpointRun.jobCost program dispatcher (bit :: suffix) (remaining + 1)) :
    SourceLabels program dispatcher (CTS.initial program (bit :: suffix)) (remaining + 1) configurations := by
  let bits := bit :: suffix
  let environment := environmentCode (compileActions program dispatcher.tree) bits
  obtain ⟨outerContext, fullContext, innerContext, targetContext, descentTicks,
      responseTicks, response, baseRun⟩ := nonemptyBase_toSelected_zeroRunAt
        program dispatcher bit suffix continuation admissible remaining parents
  have parentSplit : PrimitiveFuel.pendingParents environment continuation (remaining + 1) parents =
      .right (SchedulerResponse.pendingFunction program dispatcher bits continuation) ::
        PrimitiveFuel.pendingParents environment continuation remaining parents := by
    simpa [environment, SchedulerResponse.pendingFunction, PendingFrame.environmentCode_eq_envelope,
      PendingFrame.frameFunction] using
      (SchedulerCycle.pendingParents_succ_cons environment continuation remaining parents)
  have baseRun' : ZeroMutationRun (SchedulerControl.machine program dispatcher) descentTicks
      (SchedulerNestedPhase.fuelTerminalConfigurationAt program dispatcher bits
        (Registers.newJob program) continuation parents (remaining + 1) 0)
      (upConfiguration program dispatcher (Registers.newJob program).clearScan omega
        (ContextCursor.frames fullContext omega
          (.right (SchedulerResponse.pendingFunction program dispatcher bits continuation) ::
            PrimitiveFuel.pendingParents environment continuation remaining parents))) := by
    rw [← parentSplit]
    exact baseRun
  obtain ⟨finalRegisters, finalPhase, finalBit, finalSuffix, finalSource,
      finalOuterContext, finalFullContext, finalInnerContext, finalTargetContext,
      finalTicks, pendingConfigurations, pendingChain, _, pendingCount,
      coherent, finalTrace, sourceEq, pendingLabels⟩ :=
    selectedNonemptyPendingPrefix_labelled program dispatcher bits bits continuation admissible
      parents layers outer remaining 0 (Registers.newJob program).clearScan
      (CTS.zeroPhase program) bit suffix (baseCarrier environment continuation)
      outerContext fullContext innerContext targetContext responseTicks
      (RegistersCoherent.initial program).clearScan response
      (fun k bound => allNonempty k (Nat.le_trans bound (Nat.le_succ remaining)))
  have notSeen : finalRegisters.seen = false := by simpa [scanSeen] using coherent.seen_eq
  obtain ⟨lastConfigurations, lastChain, lastCount, lastLabels⟩ :=
    selectedResponse_labelledChain program dispatcher bits continuation finalSource admissible
      finalRegisters finalBit finalSuffix finalOuterContext finalFullContext finalInnerContext
      finalTargetContext parents finalTicks finalTrace notSeen
  have finalPhaseEq : (scannedRegisters finalRegisters finalBit finalSuffix).phase = finalPhase :=
    (scannedRegisters_coherentAt program finalRegisters finalPhase coherent finalBit finalSuffix).phase_eq
  rw [finalPhaseEq] at lastLabels lastCount
  have canonicalLabels := sourceLabels_append_last program dispatcher
    (CTS.initial program bits) remaining finalPhase finalBit finalSuffix sourceEq pendingLabels lastLabels
  have canonicalChain := ExactMutationChain.prepend baseRun'
    (SchedulerRecurrence.ExactMutationChain.append pendingChain lastChain)
  have lastNonempty : (CTS.absorbingStep program ⟨finalPhase, finalBit :: finalSuffix⟩).data ≠ [] := by
    rw [sourceEq]
    exact allNonempty (remaining + 1) (Nat.le_refl _)
  have markerZero : CheckedTransition.markerCost
      (CTS.absorbingStep program ⟨finalPhase, finalBit :: finalSuffix⟩).data = 0 := by
    cases dataEq : (CTS.absorbingStep program ⟨finalPhase, finalBit :: finalSuffix⟩).data with
    | nil => exact (lastNonempty dataEq).elim
    | cons nextBit nextSuffix => rfl
  have sourceEqInitial : ⟨finalPhase, finalBit :: finalSuffix⟩ =
      CTS.iterate program remaining (CTS.initial program bits) := sourceEq
  have canonicalCount : (pendingConfigurations ++ lastConfigurations).length =
      ExactCheckpointRun.jobCost program dispatcher bits (remaining + 1) := by
    rw [List.length_append, pendingCount, lastCount,
      ← nonemptySweepCost_initial_eq_jobCost, nonemptySweepCost_succ_last,
      ← sourceEqInitial, CheckedTransition.totalCost_cons, markerZero, Nat.add_zero]
    rfl
  have same := exactChains_same_samples program dispatcher chain canonicalChain
    (count.trans canonicalCount.symm)
  exact same.symm ▸ canonicalLabels

/-- The script-label test and designated CTS event use the same phase/head. -/
theorem target_sourceLabel_iff (config : CTS.Config SOnly38.program) :
    sourceLabel? SOnly38.program config = some SOnly38.targetLabel ↔ SOnlySource.Event config := by
  cases config with
  | mk phase data =>
      cases data with
      | nil => simp [sourceLabel?, SOnlySource.Event]
      | cons bit suffix => simp [sourceLabel?, SOnlySource.Event, SOnly38.targetLabel]

/-- No target normal-response script is executed in a labelled source prefix
before that prefix's first designated CTS event. This says nothing yet about
older or fabricated matching subtrees in the surrounding syntax. -/
theorem no_target_script_of_no_source_event
    (initial : CTS.Config SOnly38.program) (count : Nat)
    (configurations : List (SchedulerInvariant.Configuration SOnly38.program SOnly38.dispatcher))
    (labels : SourceLabels SOnly38.program SOnly38.dispatcher initial count configurations)
    (noEvent : ∀ index, index < count → ¬ SOnlySource.Event (CTS.iterate SOnly38.program index initial)) :
    ∀ configuration, configuration ∈ configurations →
      responseLabel? SOnly38.program SOnly38.dispatcher configuration ≠ some SOnly38.targetLabel := by
  intro configuration member target
  obtain ⟨index, bound, source⟩ := labels configuration member SOnly38.targetLabel target
  exact noEvent index bound ((target_sourceLabel_iff _).mp source)

/-- Structural setup phases never execute a normal-response script. -/
def NoResponseLabels (program : CTS.Program) (dispatcher : ActionDispatcher program)
    (configurations : List (SchedulerInvariant.Configuration program dispatcher)) : Prop :=
  ∀ configuration, configuration ∈ configurations → responseLabel? program dispatcher configuration = none

theorem noResponse_sourceLabels
    {program : CTS.Program} {dispatcher : ActionDispatcher program}
    {configurations : List (SchedulerInvariant.Configuration program dispatcher)}
    (none : NoResponseLabels program dispatcher configurations)
    (initial : CTS.Config program) (count : Nat) :
    SourceLabels program dispatcher initial count configurations := by
  intro configuration member observed labelEq
  rw [none configuration member] at labelEq
  cases labelEq

theorem sourceLabels_append
    {program : CTS.Program} {dispatcher : ActionDispatcher program}
    {initial : CTS.Config program} {count : Nat}
    {first tail : List (SchedulerInvariant.Configuration program dispatcher)}
    (firstLabels : SourceLabels program dispatcher initial count first)
    (tailLabels : SourceLabels program dispatcher initial count tail) :
    SourceLabels program dispatcher initial count (first ++ tail) := by
  intro configuration member observed labelEq
  rcases List.mem_append.mp member with before | after
  · exact firstLabels configuration before observed labelEq
  · exact tailLabels configuration after observed labelEq

theorem fuel_noResponse
    (program : CTS.Program) (dispatcher : ActionDispatcher program)
    (bits : List Bool) (registers : Registers program) (continuation : Term)
    (parents : List ParentFrame) (fuel depth : Nat) :
    NoResponseLabels program dispatcher
      (SchedulerNestedPhase.fuelConfigurationsAt program dispatcher bits registers continuation parents fuel depth) := by
  induction fuel generalizing depth with
  | zero =>
      intro configuration member
      simp only [SchedulerNestedPhase.fuelConfigurationsAt, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with same | same | same | same | same <;> subst configuration <;> rfl
  | succ fuel ih =>
      intro configuration member
      simp only [SchedulerNestedPhase.fuelConfigurationsAt, List.mem_cons] at member
      rcases member with same | same | later
      · subst configuration; rfl
      · subst configuration; rfl
      · exact ih (depth + 1) configuration later

theorem clockTail_noResponse
    (program : CTS.Program) (dispatcher : ActionDispatcher program)
    (bits : List Bool) (registers : Registers program) (stage : Nat)
    (parents : List ParentFrame) (wrappers remaining : Nat) :
    NoResponseLabels program dispatcher
      (SchedulerNestedPhase.clockTailConfigurationsAt program dispatcher bits registers stage parents wrappers remaining) := by
  induction remaining generalizing wrappers with
  | zero =>
      intro configuration member
      have same := List.mem_singleton.mp member
      subst configuration
      rfl
  | succ remaining ih =>
      intro configuration member
      rcases List.mem_cons.mp member with same | later
      · subst configuration; rfl
      · exact ih (wrappers + 1) configuration later

theorem phase_noResponse
    (program : CTS.Program) (dispatcher : ActionDispatcher program)
    (bits : List Bool) (registers : Registers program)
    (parents : List ParentFrame) (fuel : Nat) :
    NoResponseLabels program dispatcher
      (SchedulerNestedPhase.positiveStageConfigurationsAt program dispatcher bits registers parents fuel) := by
  intro configuration member
  simp only [SchedulerNestedPhase.positiveStageConfigurationsAt, List.mem_append, List.mem_cons,
    SchedulerNestedPhase.clockConfigurationsAt] at member
  rcases member with clock | launch | later
  · rcases clock with same | later
    · subst configuration; rfl
    · exact clockTail_noResponse program dispatcher bits registers (fuel + 1) parents 0 fuel configuration later
  · subst configuration; rfl
  · exact fuel_noResponse program dispatcher bits (Registers.newJob program) _ parents (fuel + 1) 0 configuration later

theorem handoff_noResponse
    (program : CTS.Program) (dispatcher : ActionDispatcher program)
    (bits : List Bool) (fuel remaining : Nat) (parents : List ParentFrame) :
    NoResponseLabels program dispatcher
      (SchedulerJobHandoff.handoffFuelConfigurationsAt program dispatcher bits fuel remaining parents) := by
  intro configuration member
  rcases List.mem_cons.mp member with same | later
  · subst configuration; rfl
  · exact fuel_noResponse program dispatcher bits (Registers.newJob program) _ parents (fuel + 1) 0 configuration later

/-! Exact labelled assembly of every nonfinal job and complete nonempty stage. -/
def LabelledNonfinalJobs
    (program : CTS.Program) (dispatcher : ActionDispatcher program)
    (bit : Bool) (suffix : List Bool) (fuel count sampleIndex : Nat)
    (outerParents : List ParentFrame) (layers : Nat)
    (_outer : CompletedParents program dispatcher outerParents layers) : Prop :=
  ∃ nextParents : List ParentFrame,
  ∃ configurations : List (SchedulerInvariant.Configuration program dispatcher),
    let bits := bit :: suffix
    let environment :=
      environmentCode (compileActions program dispatcher.tree) bits
    ExactMutationChain (SchedulerControl.machine program dispatcher)
      (SchedulerNestedPhase.fuelTerminalConfigurationAt program dispatcher bits
        (Registers.newJob program)
        (Dovetail.clockExit (fuel + 1) 0 environment) nextParents (fuel + 1) 0)
      (SchedulerNestedPhase.fuelTerminalConfigurationAt program dispatcher bits
        (Registers.newJob program)
        (Dovetail.clockExit (fuel + 1) count environment) outerParents
        (fuel + 1) 0)
      configurations ∧
    IndexedResponseSampledStates program dispatcher (bit :: suffix)
      sampleIndex configurations ∧
    configurations.length =
      ExactCheckpointRun.jobsCost program dispatcher (bit :: suffix) (fuel + 1)
        count ∧
    CompletedParents program dispatcher nextParents (layers + count) ∧
    SourceLabels program dispatcher (CTS.initial program (bit :: suffix)) (fuel + 1) configurations

/-- Construct all nonfinal jobs using the verified response and handoff phase
executors. -/
theorem nonfinalJobs_labelled
    (program : CTS.Program) (dispatcher : ActionDispatcher program)
    (bit : Bool) (suffix : List Bool) (fuel : Nat)
    (allNonempty : ∀ index, index ≤ fuel + 1 →
      (CTS.iterate program index
        (CTS.initial program (bit :: suffix))).data ≠ []) :
    ∀ (count sampleIndex : Nat) (outerParents : List ParentFrame)
      (layers : Nat)
      (outer : CompletedParents program dispatcher outerParents layers),
      LabelledNonfinalJobs program dispatcher bit suffix fuel count sampleIndex
        outerParents layers outer
  | 0, sampleIndex, outerParents, layers, outer => by
      exact ⟨outerParents, [], .done 0 ⟨rfl, rfl⟩, .nil sampleIndex, rfl,
        by simpa using outer, by intro configuration member; cases member⟩
  | count + 1, sampleIndex, outerParents, layers, outer => by
      let bits := bit :: suffix
      let environment :=
        environmentCode (compileActions program dispatcher.tree) bits
      let continuation := Dovetail.clockExit (fuel + 1) (count + 1) environment
      obtain ⟨responseParents, checkRegisters, responseConfigurations,
          responseChain, responseSampled, responseLength, responseOuter,
          responseErase, responseArity⟩ :=
        SchedulerNestedResponse.completeNonemptyJobAt program dispatcher bit
          suffix (fuel + 1) count (fuel + 1) sampleIndex environment outerParents
          layers outer (Nat.succ_ne_zero fuel) allNonempty
      have handoff := SchedulerJobHandoff.handoffFuelInvariantAt program
        dispatcher bits checkRegisters fuel count
        (sampleIndex + responseConfigurations.length) responseParents
        (layers + 1) responseOuter
      have tail := nonfinalJobs_labelled program dispatcher bit suffix fuel allNonempty count
        (sampleIndex + responseConfigurations.length +
          (SchedulerJobHandoff.handoffFuelConfigurationsAt program dispatcher
            bits fuel count responseParents).length)
        responseParents (layers + 1) responseOuter
      obtain ⟨terminalParents, tailConfigurations, tailChain, tailSampled,
          tailLength, terminalOuter, tailLabels⟩ := tail
      let handoffConfigurations :=
        SchedulerJobHandoff.handoffFuelConfigurationsAt program dispatcher bits
          fuel count responseParents
      let configurations := responseConfigurations ++
        handoffConfigurations ++ tailConfigurations
      have responseThenHandoff : ExactMutationChain
          (SchedulerControl.machine program dispatcher)
          (SchedulerNestedPhase.fuelTerminalConfigurationAt program dispatcher
            bits (Registers.newJob program)
            (Dovetail.clockExit (fuel + 1) count environment) responseParents
            (fuel + 1) 0)
          (SchedulerNestedPhase.fuelTerminalConfigurationAt program dispatcher
            bits (Registers.newJob program) continuation outerParents
            (fuel + 1) 0)
          (responseConfigurations ++ handoffConfigurations) := by
        exact SchedulerRecurrence.ExactMutationChain.append responseChain
          (by simpa [bits, environment, handoffConfigurations,
              SchedulerJobHandoff.continuationCursorAt] using handoff.chain)
      have completeChain := SchedulerRecurrence.ExactMutationChain.append
        responseThenHandoff tailChain
      have handoffSampled : IndexedResponseSampledStates program dispatcher bits
          (sampleIndex + responseConfigurations.length)
          handoffConfigurations := by
        simpa [handoffConfigurations] using handoff.sampled
      have responseAndHandoffSampled :=
        SchedulerNestedPhase.IndexedResponseSampledStates.append program
          dispatcher bits responseSampled handoffSampled
      have completeSampled :=
        SchedulerNestedPhase.IndexedResponseSampledStates.append program
          dispatcher bits responseAndHandoffSampled (by
            simpa [handoffConfigurations, Nat.add_assoc] using tailSampled)
      have responseLabels := completeNonemptyJob_sourceLabels program dispatcher bit suffix fuel
        continuation (Dovetail.clockExit_admissible (fuel + 1) (count + 1) environment)
        outerParents layers outer allNonempty responseChain responseLength
      have handoffLabels := noResponse_sourceLabels
        (handoff_noResponse program dispatcher bits fuel count responseParents)
        (CTS.initial program bits) (fuel + 1)
      have allLabels := sourceLabels_append (sourceLabels_append responseLabels handoffLabels) tailLabels
      refine ⟨terminalParents, configurations, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [bits, environment, continuation, configurations,
          handoffConfigurations] using completeChain
      · simpa [bits, configurations, handoffConfigurations] using
          completeSampled
      · simp only [configurations, List.length_append]
        rw [responseLength,
          SchedulerJobHandoff.handoffFuelConfigurationsAt_length, tailLength]
        rw [ExactCheckpointRun.jobsCost_succ]
        simp [Nat.add_assoc, Nat.add_comm]
      · have layerEq : (layers + 1) + count = layers + (count + 1) := by
          calc
            (layers + 1) + count = layers + (1 + count) :=
              Nat.add_assoc layers 1 count
            _ = layers + (count + 1) :=
              congrArg (Nat.add layers) (Nat.add_comm 1 count)
        rw [← layerEq]
        exact terminalOuter

      · simpa [configurations, handoffConfigurations, List.append_assoc] using allLabels

theorem allNonemptyRaw_labelled
    (program : CTS.Program) (dispatcher : ActionDispatcher program)
    (bit : Bool) (suffix : List Bool) (fuel sampleIndex : Nat)
    (parents : List ParentFrame)
    (outer : CompletedParents program dispatcher parents
      (CheckpointRun.cumulativeLayers fuel))
    (allNonempty : ∀ index, index ≤ fuel + 1 →
      (CTS.iterate program index
        (CTS.initial program (bit :: suffix))).data ≠ [])
    (indexEq : sampleIndex +
        ExactCheckpointRun.stageCost program dispatcher (bit :: suffix)
          (fuel + 1) =
      ExactCheckpointRun.checkpointTime program dispatcher (bit :: suffix)
        (fuel + 1)) :
    ∃ nextParents configurations checkpoint semantic,
      SchedulerStageAssembly.RawStageSegment program dispatcher (bit :: suffix) (fuel + 1) sampleIndex
        parents (CheckpointRun.cumulativeLayers fuel) nextParents configurations
        checkpoint semantic ∧
      SourceLabels program dispatcher (CTS.initial program (bit :: suffix)) (fuel + 1) configurations := by
  let bits := bit :: suffix
  let environment :=
    environmentCode (compileActions program dispatcher.tree) bits
  let stage := fuel + 1
  let phaseConfigurations :=
    SchedulerNestedPhase.positiveStageConfigurationsAt program dispatcher bits
      (Registers.newJob program) parents fuel
  have phase := SchedulerNestedPhase.positiveStagePhaseInvariantAt program
    dispatcher bits (Registers.newJob program) (CTS.zeroPhase program) [] false
    (RegistersCoherent.initial program) parents
    (CheckpointRun.cumulativeLayers fuel) outer sampleIndex fuel
  have phaseChain : ExactMutationChain
      (SchedulerControl.machine program dispatcher)
      (SchedulerNestedPhase.fuelTerminalConfigurationAt program dispatcher bits
        (Registers.newJob program) (Dovetail.clockExit stage fuel environment)
        parents stage 0)
      (SchedulerRecurrence.stageSourceConfiguration program dispatcher bits
        stage parents)
      phaseConfigurations := by
    simpa [phaseConfigurations, stage, environment, bits,
      SchedulerRecurrence.stageSourceConfiguration] using phase.chain
  have phaseSampled : IndexedResponseSampledStates program dispatcher bits
      sampleIndex phaseConfigurations := by
    simpa [phaseConfigurations, bits] using phase.sampled
  obtain ⟨terminalParents, nonfinalConfigurations, nonfinalChain,
      nonfinalSampled, nonfinalLength, nonfinalOuter, nonfinalLabels⟩ :=
    nonfinalJobs_labelled program dispatcher bit suffix fuel
      allNonempty fuel (sampleIndex + phaseConfigurations.length) parents
      (CheckpointRun.cumulativeLayers fuel) outer
  obtain ⟨nextParents, terminalLeading, checkpoint, terminalConfigurations,
      terminalChain, terminalEq, terminalLength, terminalData,
      classifyTerminal⟩ :=
    SchedulerNestedResponse.completeNonemptyTerminalJobRawAt program dispatcher
      bit suffix stage
      (sampleIndex + phaseConfigurations.length +
        nonfinalConfigurations.length)
      terminalParents
      (CheckpointRun.cumulativeLayers fuel + fuel) nonfinalOuter
      (Nat.succ_ne_zero fuel) allNonempty
  let configurations := phaseConfigurations ++ nonfinalConfigurations ++
    terminalConfigurations
  have phaseThenNonfinal := SchedulerRecurrence.ExactMutationChain.append phaseChain nonfinalChain
  have completeChain := SchedulerRecurrence.ExactMutationChain.append phaseThenNonfinal terminalChain
  have prefixSampled :=
    SchedulerNestedPhase.IndexedResponseSampledStates.append program dispatcher
      bits phaseSampled (by simpa using nonfinalSampled)
  have terminalLast : LastSample terminalConfigurations checkpoint := by
    rw [terminalEq]
    exact LastSample.appendLeft terminalLeading (.one checkpoint)
  have completeLast : LastSample configurations checkpoint := by
    exact LastSample.appendLeft
      (phaseConfigurations ++ nonfinalConfigurations) terminalLast
  obtain ⟨result, shape, shapeLayers, shapeTerminal, queue, completed⟩ :=
    terminalData
  have layerEq :
      (CheckpointRun.cumulativeLayers fuel + fuel) + 1 =
        CheckpointRun.cumulativeLayers (fuel + 1) := by
    rw [CheckpointRun.cumulativeLayers_succ]
    exact Nat.add_assoc (CheckpointRun.cumulativeLayers fuel) fuel 1
  have completed' : CompletedParents program dispatcher nextParents
      (CheckpointRun.cumulativeLayers (fuel + 1)) := by
    exact Eq.mp
      (congrArg
        (fun count => CompletedParents program dispatcher nextParents count)
        layerEq)
      completed
  have semantic : SchedulerRecurrence.PositiveCertificateData program dispatcher
      bits (fuel + 1) checkpoint nextParents := by
    exact SchedulerRecurrence.PositiveCertificateData.ofTerminalShape program
      dispatcher bits (fuel + 1) checkpoint nextParents completed' .fresh result
      shape (by simpa [layerEq] using shapeLayers) shapeTerminal queue
  have completeLength : configurations.length =
      ExactCheckpointRun.stageCost program dispatcher bits (fuel + 1) := by
    simp only [configurations, List.length_append]
    rw [SchedulerNestedPhase.positiveStageConfigurationsAt_length,
      nonfinalLength, terminalLength]
    simp [ExactCheckpointRun.stageCost, stage, Nat.succ_mul, Nat.mul_succ,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    rw [← Nat.add_assoc 2 8]
  have checkpointIndex : sampleIndex + configurations.length =
      ExactCheckpointRun.checkpointTime program dispatcher bits (fuel + 1) := by
    rw [completeLength]
    exact indexEq
  have phaseLabels := noResponse_sourceLabels
    (phase_noResponse program dispatcher bits (Registers.newJob program) parents fuel)
    (CTS.initial program bits) (fuel + 1)
  have terminalLabels := completeNonemptyJob_sourceLabels program dispatcher bit suffix fuel
    (Dovetail.clockExit stage 0 environment) (Dovetail.clockExit_admissible stage 0 environment)
    terminalParents (CheckpointRun.cumulativeLayers fuel + fuel) nonfinalOuter
    allNonempty terminalChain terminalLength
  have allLabels := sourceLabels_append (sourceLabels_append phaseLabels nonfinalLabels) terminalLabels
  have labels : SourceLabels program dispatcher (CTS.initial program (bit :: suffix))
      (fuel + 1) configurations := by
    simpa [configurations, phaseConfigurations, List.append_assoc] using allLabels
  refine ⟨nextParents, configurations, checkpoint, semantic, ?_, labels⟩
  refine
    { chain := ?_
      count := completeLength
      last := completeLast
      nextOuter := ?_
      checkpointIndex := checkpointIndex
      classify := ?_ }
  · simpa [configurations, stage, bits, environment,
      SchedulerRecurrence.stageSourceConfiguration,
      SchedulerRootContinuation.nextStageSourceConfiguration] using completeChain
  · exact completed'
  · intro activeContext checkpointChain certificate
    have terminalIndex :
        (sampleIndex + phaseConfigurations.length +
            nonfinalConfigurations.length) + terminalConfigurations.length =
          ExactCheckpointRun.checkpointTime program dispatcher bits
            (fuel + 1) := by
      simpa [configurations, List.length_append, Nat.add_assoc] using
        checkpointIndex
    have terminalSampled := classifyTerminal certificate terminalIndex
    have completeSampled :=
      SchedulerNestedPhase.IndexedResponseSampledStates.append program dispatcher
        bits prefixSampled (by
          simpa [Nat.add_assoc] using terminalSampled)
    simpa [configurations] using completeSampled

/-- Widening the source horizon preserves every established source label. -/
theorem sourceLabels_mono
    {program : CTS.Program} {dispatcher : ActionDispatcher program}
    {initial : CTS.Config program} {smaller larger : Nat}
    {configurations : List (SchedulerInvariant.Configuration program dispatcher)}
    (bound : smaller ≤ larger)
    (labels : SourceLabels program dispatcher initial smaller configurations) :
    SourceLabels program dispatcher initial larger configurations := by
  intro configuration member observed labelEq
  obtain ⟨index, before, source⟩ := labels configuration member observed labelEq
  exact ⟨index, Nat.lt_of_lt_of_le before bound, source⟩

theorem prelude_noResponse
    (program : CTS.Program) (dispatcher : ActionDispatcher program) (bits : List Bool) :
    NoResponseLabels program dispatcher
      (SchedulerRecurrence.initialPreludeConfigurations program dispatcher bits) := by
  intro configuration member
  have same := List.mem_singleton.mp member
  subst configuration
  rfl

/-- Finite generated prefixes through every nonempty stage retain source
labels for all their actual contraction samples. No labelled-prefix premise
is imposed on the caller. -/
theorem positiveStages_labelled
    (program : CTS.Program) (dispatcher : ActionDispatcher program)
    (bit : Bool) (suffix : List Bool) :
    ∀ offset,
      (∀ index, index ≤ offset + 1 →
        (CTS.iterate program index (CTS.initial program (bit :: suffix))).data ≠ []) →
      ∃ stages : SchedulerRecurrence.PositiveStages program dispatcher (bit :: suffix) (offset + 1),
        SourceLabels program dispatcher (CTS.initial program (bit :: suffix))
          (offset + 1) stages.configurations
  | 0, allNonempty => by
      have indexEq : 1 + ExactCheckpointRun.stageCost program dispatcher (bit :: suffix) 1 =
          ExactCheckpointRun.checkpointTime program dispatcher (bit :: suffix) 1 :=
        (ExactCheckpointRun.checkpointTime_one program dispatcher (bit :: suffix)).symm
      obtain ⟨nextParents, configurations, checkpoint, semantic, raw, labels⟩ :=
        allNonemptyRaw_labelled program dispatcher bit suffix 0 1 []
          (CompletedParents.root program dispatcher) allNonempty indexEq
      let stages := SchedulerStageAssembly.RawStageSegment.first program dispatcher
        (bit :: suffix) semantic raw
      refine ⟨stages, ?_⟩
      change SourceLabels program dispatcher (CTS.initial program (bit :: suffix)) 1
        (SchedulerRecurrence.initialPreludeConfigurations program dispatcher (bit :: suffix) ++ configurations)
      exact sourceLabels_append (noResponse_sourceLabels (prelude_noResponse program dispatcher (bit :: suffix)) _ _) labels
  | offset + 1, allNonempty => by
      obtain ⟨past, pastLabels⟩ := positiveStages_labelled program dispatcher bit suffix offset
        (fun index bound => allNonempty index (Nat.le_trans bound (Nat.le_succ _)))
      have indexEq : past.configurations.length +
          ExactCheckpointRun.stageCost program dispatcher (bit :: suffix) (offset + 2) =
          ExactCheckpointRun.checkpointTime program dispatcher (bit :: suffix) (offset + 2) := by
        rw [past.count]
        exact ExactCheckpointRun.checkpointTime_positive_succ program dispatcher (bit :: suffix) offset
      obtain ⟨nextParents, configurations, checkpoint, semantic, raw, labels⟩ :=
        allNonemptyRaw_labelled program dispatcher bit suffix (offset + 1)
          past.configurations.length past.nextParents past.nextOuter allNonempty indexEq
      let stages := SchedulerStageAssembly.RawStageSegment.extend past semantic raw
      refine ⟨stages, ?_⟩
      change SourceLabels program dispatcher (CTS.initial program (bit :: suffix)) (offset + 2)
        (past.configurations ++ configurations)
      exact sourceLabels_append (sourceLabels_mono (Nat.le_succ _) pastLabels) labels

/-- Labels at every actual noninitial persistent sample arise from source
prestates; the chosen finite horizon is supplied by the generated prefix. -/
theorem contractionRun_label_has_source (bits : List Bool) (index : Nat)
    (allNonempty : ∀ k, k ≤ index + 1 →
      (CTS.iterate SOnly38.program k (CTS.initial SOnly38.program bits)).data ≠ [])
    (label : ActionLabel SOnly38.program)
    (observed : responseLabel? SOnly38.program SOnly38.dispatcher
      ((SOnlyEventTransfer.persistentSystem bits).contractionRun (index + 1)) = some label) :
    ∃ sourceIndex, sourceIndex < index + 1 ∧
      sourceLabel? SOnly38.program
        (CTS.iterate SOnly38.program sourceIndex (CTS.initial SOnly38.program bits)) = some label := by
  cases bits with
  | nil => exact (allNonempty 0 (Nat.zero_le _) rfl).elim
  | cons bit suffix =>
      obtain ⟨stages, labels⟩ := positiveStages_labelled SOnly38.program SOnly38.dispatcher bit suffix index allNonempty
      have inRange : index < stages.configurations.length := Nat.lt_of_lt_of_le
        (Nat.lt_succ_self index) stages.horizonLower
      let configuration := stages.configurations[index]
      have atIndex : stages.configurations[index]? = some configuration := by simp [configuration, inRange]
      have sampled := SOnlyEventTransfer.exactChain_sample SOnly38.program SOnly38.dispatcher
        (bit :: suffix) (SchedulerRecurrence.initialGood SOnly38.program SOnly38.dispatcher (bit :: suffix))
        stages.chain (sampleIndex := 0) rfl atIndex
      have sampleEq : (SOnlyEventTransfer.persistentSystem (bit :: suffix)).contractionRun (index + 1) = configuration := by
        simpa using sampled
      have member : configuration ∈ stages.configurations := List.getElem_mem inRange
      exact labels configuration member label (sampleEq ▸ observed)

/-- A nonempty source computation with no designated event never executes
the target response script at any persistent sample. Descendant-event absence
still requires the independent generated-occurrence invariant. -/
theorem no_target_script_on_event_free_run (bits : List Bool)
    (nonempty : ∀ k, (CTS.iterate SOnly38.program k (CTS.initial SOnly38.program bits)).data ≠ [])
    (noEvent : ∀ k, ¬ SOnlySource.Event (CTS.iterate SOnly38.program k (CTS.initial SOnly38.program bits))) :
    ∀ index, responseLabel? SOnly38.program SOnly38.dispatcher
      ((SOnlyEventTransfer.persistentSystem bits).contractionRun index) ≠ some SOnly38.targetLabel := by
  intro index observed
  cases index with
  | zero => cases observed
  | succ index =>
      obtain ⟨sourceIndex, _, source⟩ := contractionRun_label_has_source bits index
        (fun k _ => nonempty k) SOnly38.targetLabel observed
      exact noEvent sourceIndex ((target_sourceLabel_iff _).mp source)

/-- The stage-start prefix retains every earlier stage's source-index bound. -/
theorem stageStart_labelled (bits : List Bool) (r : Nat)
    (allNonempty : ∀ k, k ≤ r → (CTS.iterate SOnly38.program k (CTS.initial SOnly38.program bits)).data ≠ []) :
    ∃ parents configurations,
      ExactMutationChain (SchedulerControl.machine SOnly38.program SOnly38.dispatcher)
        (SchedulerRecurrence.stageSourceConfiguration SOnly38.program SOnly38.dispatcher bits (r + 1) parents)
        (SchedulerControl.initialConfiguration SOnly38.program SOnly38.dispatcher bits) configurations ∧
      configurations.length = SOnlyStageEvents.stageStartTime bits r ∧
      CompletedParents SOnly38.program SOnly38.dispatcher parents (CheckpointRun.cumulativeLayers r) ∧
      SourceLabels SOnly38.program SOnly38.dispatcher (CTS.initial SOnly38.program bits) r configurations := by
  cases r with
  | zero =>
      exact ⟨[], SchedulerRecurrence.initialPreludeConfigurations SOnly38.program SOnly38.dispatcher bits,
        SchedulerRecurrence.initialPreludeChain SOnly38.program SOnly38.dispatcher bits,
        rfl, CompletedParents.root SOnly38.program SOnly38.dispatcher,
        noResponse_sourceLabels (prelude_noResponse SOnly38.program SOnly38.dispatcher bits) _ _⟩
  | succ r =>
      cases bits with
      | nil => exact (allNonempty 0 (Nat.zero_le _) rfl).elim
      | cons bit suffix =>
          obtain ⟨past, labels⟩ := positiveStages_labelled SOnly38.program SOnly38.dispatcher bit suffix r allNonempty
          exact ⟨past.nextParents, past.configurations, past.chain, past.count, past.nextOuter, labels⟩

/-- Strengthening of the exact first-job prefix: all response scripts before
the r-th selected response have source indices strictly less than r. -/
theorem firstJob_response_prefix_labelled (bit : Bool) (suffix : List Bool) (r : Nat)
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
        CTS.iterate SOnly38.program r (CTS.initial SOnly38.program bits) ∧
      SourceLabels SOnly38.program SOnly38.dispatcher (CTS.initial SOnly38.program bits) r configurations := by
  let bits := bit :: suffix
  let environment := environmentCode (compileActions SOnly38.program SOnly38.dispatcher.tree) bits
  let continuation := Dovetail.clockExit (r + 1) r environment
  obtain ⟨parents, prefixConfigurations, prefixChain, prefixCount, outer, prefixLabels⟩ := stageStart_labelled bits r allNonempty
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
      pendingCount, coherent, finalTrace, sourceEq, pendingLabels⟩ :=
    selectedNonemptyPendingPrefix_labelled SOnly38.program SOnly38.dispatcher bits bits
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
  have phaseLabels := noResponse_sourceLabels
    (phase_noResponse SOnly38.program SOnly38.dispatcher bits (Registers.newJob SOnly38.program) parents r)
    (CTS.initial SOnly38.program bits) r
  have labels := sourceLabels_append prefixLabels (sourceLabels_append phaseLabels pendingLabels)
  refine ⟨parents, finalRegisters, finalPhase, finalBit, finalSuffix, finalSource,
    finalOuterContext, finalFullContext, finalInnerContext, finalTargetContext,
    finalTicks, prefixConfigurations ++ (phaseConfigurations ++ pendingConfigurations),
    completeChain, ?_, coherent, finalTrace, sourceEq, labels⟩
  simp only [List.length_append, prefixCount, pendingCount]
  rw [SchedulerNestedPhase.positiveStageConfigurationsAt_length]
  simp only [firstJobPreResponseTime, Nat.add_assoc]
  rfl

/-- Before the designated first job reaches source index r, no target
response script occurs when all source indices below r are event-free. -/
theorem no_target_script_before_firstJob_response (bits : List Bool) (r : Nat)
    (allNonempty : ∀ k, k ≤ r → (CTS.iterate SOnly38.program k (CTS.initial SOnly38.program bits)).data ≠ [])
    (noEvent : ∀ k, k < r → ¬ SOnlySource.Event (CTS.iterate SOnly38.program k (CTS.initial SOnly38.program bits))) :
    ∀ index, index < SOnlyStageEvents.firstJobPreResponseTime bits r →
      responseLabel? SOnly38.program SOnly38.dispatcher
        ((SOnlyEventTransfer.persistentSystem bits).contractionRun (index + 1)) ≠ some SOnly38.targetLabel := by
  cases bits with
  | nil => exact (allNonempty 0 (Nat.zero_le _) rfl).elim
  | cons bit suffix =>
      obtain ⟨parents, registers, phase, responseBit, responseSuffix, source,
          outerContext, fullContext, innerContext, targetContext, ticks, configurations,
          chain, count, coherent, trace, sourceEq, labels⟩ :=
        firstJob_response_prefix_labelled bit suffix r allNonempty
      intro index bound observed
      have inRange : index < configurations.length := by rw [count]; exact bound
      let configuration := configurations[index]
      have atIndex : configurations[index]? = some configuration := by simp [configuration, inRange]
      have sampled := SOnlyEventTransfer.exactChain_sample SOnly38.program SOnly38.dispatcher
        (bit :: suffix) (SchedulerRecurrence.initialGood SOnly38.program SOnly38.dispatcher (bit :: suffix))
        chain (sampleIndex := 0) rfl atIndex
      have sampleEq : (SOnlyEventTransfer.persistentSystem (bit :: suffix)).contractionRun (index + 1) = configuration := by
        simpa using sampled
      exact no_target_script_of_no_source_event (CTS.initial SOnly38.program (bit :: suffix)) r
        configurations labels noEvent configuration (List.getElem_mem inRange) (sampleEq ▸ observed)

end SOnlyResponseLabels

#print axioms SOnlyResponseLabels.exactChains_same_samples
#print axioms SOnlyResponseLabels.selectedResponse_onlyLabel

#print axioms SOnlyResponseLabels.selectedNonemptyPendingPrefix_labelled

#print axioms SOnlyResponseLabels.completeNonemptyJob_sourceLabels
#print axioms SOnlyResponseLabels.no_target_script_of_no_source_event

#print axioms SOnlyResponseLabels.phase_noResponse
#print axioms SOnlyResponseLabels.handoff_noResponse

#print axioms SOnlyResponseLabels.nonfinalJobs_labelled
#print axioms SOnlyResponseLabels.allNonemptyRaw_labelled

#print axioms SOnlyResponseLabels.positiveStages_labelled
#print axioms SOnlyResponseLabels.contractionRun_label_has_source
#print axioms SOnlyResponseLabels.no_target_script_on_event_free_run

#print axioms SOnlyResponseLabels.firstJob_response_prefix_labelled
#print axioms SOnlyResponseLabels.no_target_script_before_firstJob_response
