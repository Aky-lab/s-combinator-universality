import SOnlyCanonicalOrigins
import SOnlySchedulerOrigins
import SOnlyResponseLabels
import SOnlyGlobalAncestors

/-! Licensed origins through the actual ordered nonempty scheduler response chains. -/
namespace SOnlyGlobalOrigins
open PureSFormal PureSFormal.PureS
open SchedulerControl SchedulerInvariant SchedulerCycle SchedulerResponseInvariant
open SchedulerNestedResponse SchedulerCompletedContext SchedulerTraceAlgebra
open SOnlyProvenance SOnlyProvenanceRows SOnlyGeneratedOrigins SOnlyCanonicalOrigins
open SOnlySchedulerOrigins SOnlyResponseLabels SOnlyGlobalAncestors
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

theorem samples_append {P : Term → Prop} {program : CTS.Program}
    {dispatcher : ActionDispatcher program} {left right : List (SchedulerInvariant.Configuration program dispatcher)}
    (hl : SamplesLicensed P left) (hr : SamplesLicensed P right) : SamplesLicensed P (left ++ right) := by
  intro sample member
  rcases List.mem_append.mp member with h | h
  · exact hl sample h
  · exact hr sample h

theorem responsePairs_licensed
    {program : CTS.Program} {dispatcher : ActionDispatcher program}
    (allowed : OriginSet program)
    {registers : Registers program} {bit : Bool} {seedBits : List Bool}
    {continuation carrier : Term} {parents : List ParentFrame}
    {configurations : List (SchedulerInvariant.Configuration program dispatcher)} {entries : List (Bool × Term)}
    (pairs : ResponseSamplePairs program dispatcher registers bit seedBits continuation
      carrier parents configurations entries)
    (admissible : Carrier.Admissible continuation)
    (held : ReachableAudit.Holds program dispatcher.tree seedBits continuation carrier)
    (hb : Ordinary (RootLicensed program dispatcher.tree allowed) continuation)
    (hv : Licensed program dispatcher.tree allowed carrier)
    (outer : Wraps (RootLicensed program dispatcher.tree allowed) parents)
    (origin : allowed (registers.phase, bit) carrier) :
    SamplesLicensed (RootLicensed program dispatcher.tree allowed) configurations := by
  induction pairs with
  | nil => intro sample member; cases member
  | @cons pc cursor done term position eraseEq row tail entries pairs ih =>
      intro sample member
      rcases List.mem_cons.mp member with eq | later
      · subst sample
        change AllH6 _ cursor.erase
        rw [eraseEq]
        exact outer _ (response_endpoint row)
          (response_licensed allowed row admissible held hb.1 hb.2 hv (holds_endpoint hb.2 held) origin)
      · exact ih sample later

theorem selectedResponse_licensedChain
    (program : CTS.Program) (dispatcher : ActionDispatcher program)
    (allowed : OriginSet program)
    (seedBits : List Bool) (continuation source : Term)
    (admissible : Carrier.Admissible continuation)
    (registers : Registers program) (bit : Bool) (suffix : List Bool)
    (outerContext fullContext innerContext targetContext : Context)
    (parents : List ParentFrame) (ticks : Nat)
    (trace : SelectedResponseTrace program dispatcher seedBits continuation source
      admissible registers bit suffix outerContext fullContext innerContext targetContext parents ticks)
    (notSeen : registers.seen = false)
    (hb : Ordinary (RootLicensed program dispatcher.tree allowed) continuation)
    (hs : Licensed program dispatcher.tree allowed source)
    (outer : Wraps (RootLicensed program dispatcher.tree allowed) parents)
    (origin : allowed ((scannedRegisters registers bit suffix).phase, bit)
      (deletedCarrier bit outerContext innerContext)) :
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
      SamplesLicensed (RootLicensed program dispatcher.tree allowed) configurations := by
  let carrier := deletedCarrier bit outerContext innerContext
  let finalRegisters := scannedRegisters registers bit suffix
  let fullParents := .right (SchedulerResponse.pendingFunction program dispatcher seedBits continuation) :: parents
  let c4 := selectedC4Configuration program dispatcher registers bit outerContext innerContext fullParents
  obtain ⟨bound, found⟩ := selected_seekC4 program dispatcher seedBits continuation source
    admissible registers bit suffix parents trace notSeen
  have trace0 : SelectedResponseTrace program dispatcher seedBits continuation source admissible
      registers bit suffix outerContext fullContext innerContext targetContext
      (PrimitiveFuel.pendingParents (environmentCode (compileActions program dispatcher.tree) seedBits)
        continuation 0 parents) ticks := by simpa [PrimitiveFuel.pendingParents] using trace
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
  have deleted := selectedResponse_deleted_licensed allowed trace hb.2 hs
  have pendingHead : Ordinary (RootLicensed program dispatcher.tree allowed)
      (SchedulerResponse.pendingFunction program dispatcher seedBits continuation) := by
    simpa [SchedulerResponse.pendingFunction, PendingFrame.environmentCode_eq_envelope,
      PendingFrame.frameFunction] using ordinary_app
      (environment_ordinary (RootLicensed program dispatcher.tree allowed) program dispatcher seedBits) hb.1
  have fullOuter := wraps_right outer pendingHead.1 pendingHead.2
  have c4Licensed : Licensed program dispatcher.tree allowed c4.cursor.erase := by
    change AllH6 _ (Cursor.rebuild (ContextCursor.frames outerContext (Carrier.tombstone bit (SchedulerAscent.frontPredecessor innerContext) (SchedulerAscent.frontPredecessor innerContext)) fullParents) (Carrier.tombstone bit (SchedulerAscent.frontPredecessor innerContext) (SchedulerAscent.frontPredecessor innerContext)))
    rw [rebuild_contextFrames]
    exact fullOuter carrier (holds_endpoint hb.2 trace.targetHolds) deleted
  have responseLicensed := responsePairs_licensed allowed pairs admissible trace.targetHolds hb deleted outer origin
  refine ⟨c4 :: responseConfigurations, .next bound (by simpa [c4, fullParents] using found) postC4, ?_, ?_⟩
  · have count := pairs.length_eq.trans (responseEntries_length program
      (dispatcher.route_valid (finalRegisters.phase, bit)) seedBits continuation carrier)
    simp only [List.length_cons, count]
    exact Nat.add_comm _ _
  · intro sample member
    rcases List.mem_cons.mp member with eq | later
    · subst sample; exact c4Licensed
    · exact responseLicensed sample later

theorem selectedResponse_licensed
    (program : CTS.Program) (dispatcher : ActionDispatcher program)
    (allowed : OriginSet program)
    (seedBits : List Bool) (continuation source : Term)
    (admissible : Carrier.Admissible continuation)
    (registers : Registers program) (bit : Bool) (suffix : List Bool)
    (outerContext fullContext innerContext targetContext : Context)
    (parents : List ParentFrame) (ticks : Nat)
    (trace : SelectedResponseTrace program dispatcher seedBits continuation source
      admissible registers bit suffix outerContext fullContext innerContext targetContext parents ticks)
    (notSeen : registers.seen = false)
    (hb : Ordinary (RootLicensed program dispatcher.tree allowed) continuation)
    (hs : Licensed program dispatcher.tree allowed source)
    (outer : Wraps (RootLicensed program dispatcher.tree allowed) parents)
    (origin : allowed ((scannedRegisters registers bit suffix).phase, bit)
      (deletedCarrier bit outerContext innerContext))
    {terminal : SchedulerInvariant.Configuration program dispatcher} {configurations : List (SchedulerInvariant.Configuration program dispatcher)}
    (chain : ExactMutationChain (SchedulerControl.machine program dispatcher) terminal
      (upConfiguration program dispatcher registers omega
        (ContextCursor.frames fullContext omega
          (.right (SchedulerResponse.pendingFunction program dispatcher seedBits continuation) :: parents))) configurations)
    (count : configurations.length = 1 + LocalResponse.completedCost program
      (dispatcher.route ((scannedRegisters registers bit suffix).phase, bit))
      ((scannedRegisters registers bit suffix).phase, bit)) :
    SamplesLicensed (RootLicensed program dispatcher.tree allowed) configurations := by
  obtain ⟨canonical, canonicalChain, canonicalCount, licensed⟩ :=
    selectedResponse_licensedChain program dispatcher allowed seedBits continuation source admissible
      registers bit suffix outerContext fullContext innerContext targetContext parents ticks trace notSeen hb hs outer origin
  have same := exactChains_same_samples program dispatcher chain canonicalChain (count.trans canonicalCount.symm)
  exact same.symm ▸ licensed

/-- The admitted labels come from actual source prestates in a bounded horizon. -/
def SourceAllowed {program : CTS.Program} (allowed : OriginSet program)
    (initial : CTS.Config program) (count : Nat) : Prop :=
  ∀ index, index < count → ∀ label snapshot,
    sourceLabel? program (CTS.iterate program index initial) = some label → allowed label snapshot

theorem sourceAllowed_mono {program : CTS.Program} {allowed : OriginSet program}
    {initial : CTS.Config program} {smaller larger : Nat}
    (h : SourceAllowed allowed initial larger) (bound : smaller ≤ larger) :
    SourceAllowed allowed initial smaller := by
  intro index before label snapshot source
  exact h index (Nat.lt_of_lt_of_le before bound) label snapshot source

theorem sourceAllowed_tail {program : CTS.Program} {allowed : OriginSet program}
    {initial : CTS.Config program} {count : Nat}
    (h : SourceAllowed allowed initial (count + 1)) :
    SourceAllowed allowed (CTS.absorbingStep program initial) count := by
  intro index before label snapshot source
  apply h (index + 1) (Nat.succ_lt_succ before) label snapshot
  rw [CTS.iterate_add]
  exact source


theorem selectedNonemptyPendingPrefix_licensed
    (program : CTS.Program) (dispatcher : ActionDispatcher program)
    (inputBits seedBits : List Bool) (continuation : Term)
    (hadmissible : Carrier.Admissible continuation)
    (outerParents : List ParentFrame) (layers : Nat)
    (outer : CompletedParents program dispatcher outerParents layers)
    (allowed : OriginSet program)
    (hb : Ordinary (RootLicensed program dispatcher.tree allowed) continuation)
    (outerLicensed : Wraps (RootLicensed program dispatcher.tree allowed) outerParents) :
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
      Licensed program dispatcher.tree allowed source →
      SourceAllowed allowed ⟨phase, bit :: suffix⟩ remaining →
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
        SamplesLicensed (RootLicensed program dispatcher.tree allowed) configurations ∧
        Licensed program dispatcher.tree allowed finalSource
  | 0, sampleIndex, registers, phase, bit, suffix, source, outerContext,
      fullContext, innerContext, targetContext, ticks, coherent, trace,
      allNonempty, hs, sourceAllowed => by
      refine ⟨registers, phase, bit, suffix, source, outerContext, fullContext,
        innerContext, targetContext, ticks, [], ?_, .nil sampleIndex, rfl,
        coherent, ?_, rfl, (by intro sample member; cases member), hs⟩
      · exact .done 0 ⟨rfl, rfl⟩
      · simpa [PrimitiveFuel.pendingParents] using trace
  | remaining + 1, sampleIndex, registers, phase, bit, suffix, source,
      outerContext, fullContext, innerContext, targetContext, ticks, coherent,
      trace, allNonempty, hs, sourceAllowed => by
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
          have currentOrigin : allowed (finalRegisters.phase, bit) carrier := by
            have phaseEq : finalRegisters.phase = phase := scannedCoherent.phase_eq
            rw [phaseEq]
            exact sourceAllowed 0 (Nat.zero_lt_succ remaining) (phase, bit) carrier rfl
          have firstLicensed := selectedResponse_licensed program dispatcher allowed seedBits
            continuation source hadmissible registers bit suffix outerContext fullContext innerContext
            targetContext afterParents ticks (by simpa [afterParents, encodedEnvironment] using trace)
            notSeen hb hs (pending_wraps program dispatcher seedBits hb.1 outerLicensed (remaining + 1))
            currentOrigin firstChain firstLength
          have deletedLicensed := selectedResponse_deleted_licensed allowed trace hb.2 hs
          have completedLicensed := completed_licensed program dispatcher allowed finalRegisters bit
            seedBits hb.1 (Or.inl hb.2) deletedLicensed (holds_endpoint hb.2 trace.targetHolds) currentOrigin
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
              tailLength, terminalCoherent, terminalTrace, terminalEq, tailLicensed, terminalLicensed⟩ :=
            selectedNonemptyPendingPrefix_licensed program dispatcher inputBits seedBits
              continuation hadmissible outerParents layers outer allowed hb outerLicensed remaining
              (sampleIndex + firstConfigurations.length) finalRegisters.advance
              (CTS.nextPhase program phase) nextBit nextSuffix
              (LocalResponse.completed seedBits continuation carrier
                (SchedulerResponse.completedRoute program dispatcher
                  finalRegisters bit carrier))
              nextOuterContext nextFullContext nextInnerContext nextTargetContext
              nextTicks nextCoherent (by
                simpa [nextParents, encodedEnvironment, finalRegisters, carrier]
                  using cycle.nextResponse)
              tailNonempty completedLicensed (by
                simpa only [stepEq] using sourceAllowed_tail sourceAllowed)
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
          refine ⟨terminalRegisters, terminalPhase, terminalBit,
            terminalSuffix, terminalSource, terminalOuterContext,
            terminalFullContext, terminalInnerContext, terminalTargetContext,
            terminalTicks, firstConfigurations ++ tailConfigurations, ?_,
            completeSampled, ?_, terminalCoherent, terminalTrace, ?_,
            samples_append firstLicensed tailLicensed, terminalLicensed⟩
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


theorem selectedNonemptySweepToFreshCheck_licensed
    (program : CTS.Program) (dispatcher : ActionDispatcher program)
    (inputBits seedBits : List Bool) (stage jobs : Nat) (environment : Term)
    (outerParents : List ParentFrame) (layers : Nat)
    (outer : CompletedParents program dispatcher outerParents layers)
    (allowed : OriginSet program)
    (he : Licensed program dispatcher.tree allowed environment)
    (outerLicensed : LicensedParents program dispatcher allowed outerParents) :
    ∀ (remaining sampleIndex : Nat) (registers : Registers program)
      (phase : CTS.Phase program) (bit : Bool) (suffix : List Bool)
      (source : Term)
      (outerContext fullContext innerContext targetContext : Context)
      (ticks : Nat),
      RegistersCoherent registers phase [] false →
      SelectedResponseTrace program dispatcher seedBits
        (Dovetail.clockExit stage (jobs + 1) environment) source
        (Dovetail.clockExit_admissible stage (jobs + 1) environment)
        registers bit suffix outerContext fullContext innerContext targetContext
        (PrimitiveFuel.pendingParents
          (environmentCode (compileActions program dispatcher.tree) seedBits)
          (Dovetail.clockExit stage (jobs + 1) environment) remaining
          outerParents) ticks →
      (∀ k, k ≤ remaining + 1 →
        (CTS.iterate program k ⟨phase, bit :: suffix⟩).data ≠ []) →
      Licensed program dispatcher.tree allowed source →
      SourceAllowed allowed ⟨phase, bit :: suffix⟩ (remaining + 1) →
      ∃ nextParents checkRegisters configurations,
        ExactMutationChain (SchedulerControl.machine program dispatcher)
          (SchedulerContinuation.checkConfiguration program dispatcher
            checkRegisters
            ⟨Dovetail.clockExit stage (jobs + 1) environment, nextParents⟩)
          (upConfiguration program dispatcher registers omega
            (ContextCursor.frames fullContext omega
              (.right (SchedulerResponse.pendingFunction program dispatcher
                seedBits (Dovetail.clockExit stage (jobs + 1) environment)) ::
                PrimitiveFuel.pendingParents
                  (environmentCode
                    (compileActions program dispatcher.tree) seedBits)
                  (Dovetail.clockExit stage (jobs + 1) environment) remaining
                  outerParents))) configurations ∧
        IndexedResponseSampledStates program dispatcher inputBits sampleIndex
          configurations ∧
        configurations.length =
          nonemptySweepCost program dispatcher (remaining + 1)
            ⟨phase, bit :: suffix⟩ ∧
        CompletedParents program dispatcher nextParents (layers + 1) ∧
        SamplesLicensed (RootLicensed program dispatcher.tree allowed) configurations ∧
        LicensedParents program dispatcher allowed nextParents
  | 0, sampleIndex, registers, phase, bit, suffix, source, outerContext,
      fullContext, innerContext, targetContext, ticks, coherent, trace,
      allNonempty, hs, sourceAllowed => by
      let continuation := Dovetail.clockExit stage (jobs + 1) environment
      have hb : Ordinary (RootLicensed program dispatcher.tree allowed) continuation := clockExit_ordinary stage (jobs + 1) he
      let carrier := deletedCarrier bit outerContext innerContext
      let finalRegisters := scannedRegisters registers bit suffix
      have trace' : SelectedResponseTrace program dispatcher seedBits
          continuation source
          (Dovetail.clockExit_admissible stage (jobs + 1) environment)
          registers bit suffix outerContext fullContext innerContext targetContext
          outerParents ticks := by
        simpa [continuation, PrimitiveFuel.pendingParents] using trace
      have firstNonempty :
          (CTS.absorbingStep program ⟨phase, bit :: suffix⟩).data ≠ [] := by
        have indexed := allNonempty 1 (by simp)
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
          obtain ⟨configurations, chain, sampled, lengthEq, nextOuter⟩ :=
            selectedFreshNonterminalJobAt program dispatcher inputBits seedBits
              stage jobs environment source registers phase coherent bit suffix
              sampleIndex outerParents layers outer trace' nextBit nextSuffix
              dataEqRegisters
          let nextParents :=
            SchedulerRootContinuation.freshContinuationParents program
              dispatcher finalRegisters bit seedBits carrier outerParents
          have notSeen : registers.seen = false := by simpa [scanSeen] using coherent.seen_eq
          have finalCoherent := scannedRegisters_coherentAt program registers phase coherent bit suffix
          have currentOrigin : allowed (finalRegisters.phase, bit) carrier := by
            have phaseEq : finalRegisters.phase = phase := finalCoherent.phase_eq
            rw [phaseEq]
            exact sourceAllowed 0 (Nat.zero_lt_succ 0) (phase, bit) carrier rfl
          have sampleCount : configurations.length = 1 + LocalResponse.completedCost program
              (dispatcher.route (finalRegisters.phase, bit)) (finalRegisters.phase, bit) := by
            rw [lengthEq, CheckedTransition.totalCost_cons, dataEqRegisters,
              CheckedTransition.markerCost_cons, Nat.add_zero]
            rw [show finalRegisters.phase = registers.phase from
              finalCoherent.phase_eq.trans coherent.phase_eq.symm]
          have licensed := selectedResponse_licensed program dispatcher allowed seedBits continuation source
            (Dovetail.clockExit_admissible stage (jobs + 1) environment) registers bit suffix
            outerContext fullContext innerContext targetContext outerParents ticks trace' notSeen hb hs
            outerLicensed.wraps currentOrigin chain sampleCount
          have deletedLicensed := selectedResponse_deleted_licensed allowed trace' hb.2 hs
          have nextLicensed := outerLicensed.fresh finalRegisters bit seedBits deletedLicensed
            (holds_endpoint hb.2 trace'.targetHolds) currentOrigin
          refine ⟨nextParents, finalRegisters.advance, configurations, ?_,
            sampled, ?_, ?_, licensed, nextLicensed⟩
          · simpa [nextParents, finalRegisters, carrier, continuation,
              SchedulerResponse.freshContinuationCursor,
              SchedulerResponse.literalContinuationCursor] using! chain
          · rw [lengthEq]
            simp [nonemptySweepCost, coherent.phase_eq]
          · simpa [nextParents, finalRegisters, carrier] using nextOuter
  | remaining + 1, sampleIndex, registers, phase, bit, suffix, source,
      outerContext, fullContext, innerContext, targetContext, ticks, coherent,
      trace, allNonempty, hs, sourceAllowed => by
      let continuation := Dovetail.clockExit stage (jobs + 1) environment
      have hb : Ordinary (RootLicensed program dispatcher.tree allowed) continuation := clockExit_ordinary stage (jobs + 1) he
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
          (Nat.succ_le_succ (Nat.zero_le (remaining + 1)))
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
              continuation, SchedulerResponse.pendingFunction,
              PendingFrame.environmentCode_eq_envelope,
              PendingFrame.frameFunction] using
              (SchedulerCycle.pendingParents_succ_cons encodedEnvironment
                continuation remaining outerParents)
          have cycleTrace : SelectedResponseTrace program dispatcher seedBits
              continuation source
              (Dovetail.clockExit_admissible stage (jobs + 1) environment)
              registers bit suffix outerContext fullContext innerContext
              targetContext
              (.right (SchedulerResponse.pendingFunction program dispatcher
                seedBits continuation) :: nextParents) ticks := by
            rw [← parentSplit]
            simpa [afterParents, continuation, encodedEnvironment] using trace
          obtain ⟨firstConfigurations, firstChain, firstSampled, firstLength⟩ :=
            selectedPendingSegmentAt program dispatcher inputBits seedBits
              continuation source
              (Dovetail.clockExit_admissible stage (jobs + 1) environment)
              registers phase coherent bit suffix (remaining + 1) sampleIndex
              (Nat.succ_ne_zero remaining) outerParents layers outer
              (by simpa [continuation, encodedEnvironment] using trace)
          have notSeen : registers.seen = false := by
            simpa using! coherent.seen_eq
          have noTail : registers.tail = false := by
            simpa using! coherent.tail_eq
          obtain ⟨nextContext, nextOuterContext, nextFullContext,
              nextInnerContext, nextTargetContext, returnTicks, downTicks,
              nextTicks, cycle⟩ :=
            pendingNonemptyCycleTrace program dispatcher seedBits continuation
              source (Dovetail.clockExit_admissible stage (jobs + 1) environment)
              registers bit suffix nextParents ticks cycleTrace notSeen noTail
              nextBit nextSuffix dataEqRegisters
          have finalCoherent : RegistersCoherent finalRegisters phase
              (bit :: suffix) false :=
            scannedRegisters_coherentAt program registers phase coherent bit suffix
          have currentOrigin : allowed (finalRegisters.phase, bit) carrier := by
            have phaseEq : finalRegisters.phase = phase := finalCoherent.phase_eq
            rw [phaseEq]
            exact sourceAllowed 0 (Nat.zero_lt_succ (remaining + 1)) (phase, bit) carrier rfl
          have firstLicensed := selectedResponse_licensed program dispatcher allowed seedBits
            continuation source (Dovetail.clockExit_admissible stage (jobs + 1) environment)
            registers bit suffix outerContext fullContext innerContext targetContext afterParents ticks
            (by simpa [afterParents, encodedEnvironment, continuation] using trace) notSeen hb hs
            (pending_wraps program dispatcher seedBits hb.1 outerLicensed.wraps (remaining + 1))
            currentOrigin firstChain firstLength
          have deletedLicensed := selectedResponse_deleted_licensed allowed trace hb.2 hs
          have completedLicensed := completed_licensed program dispatcher allowed finalRegisters bit
            seedBits hb.1 (Or.inl hb.2) deletedLicensed (holds_endpoint hb.2 trace.targetHolds) currentOrigin
          have nextCoherent : RegistersCoherent finalRegisters.advance
              (CTS.nextPhase program phase) [] false := finalCoherent.advance
          have stepEq :
              CTS.absorbingStep program ⟨phase, bit :: suffix⟩ =
                ⟨CTS.nextPhase program phase, nextBit :: nextSuffix⟩ := by
            cases step : CTS.absorbingStep program ⟨phase, bit :: suffix⟩ with
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
          have tailNonempty : ∀ k, k ≤ remaining + 1 →
              (CTS.iterate program k
                ⟨CTS.nextPhase program phase, nextBit :: nextSuffix⟩).data ≠
                  [] := by
            intro k bound
            have shiftedBound : k + 1 ≤ (remaining + 1) + 1 :=
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
          obtain ⟨terminalParents, checkRegisters, tailConfigurations,
              tailChain, tailSampled, tailLength, terminalOuter, tailLicensed, terminalLicensed⟩ :=
            selectedNonemptySweepToFreshCheck_licensed program dispatcher inputBits
              seedBits stage jobs environment outerParents layers outer allowed he outerLicensed remaining
              (sampleIndex + firstConfigurations.length) finalRegisters.advance
              (CTS.nextPhase program phase) nextBit nextSuffix
              (LocalResponse.completed seedBits continuation carrier
                (SchedulerResponse.completedRoute program dispatcher
                  finalRegisters bit carrier))
              nextOuterContext nextFullContext nextInnerContext nextTargetContext
              nextTicks nextCoherent (by
                simpa [nextParents, encodedEnvironment, continuation,
                  finalRegisters, carrier] using cycle.nextResponse)
              tailNonempty completedLicensed (by
                simpa only [stepEq] using sourceAllowed_tail sourceAllowed)
          obtain ⟨bridgeDownTicks, bridgeDown⟩ := run_downDescent
            finalRegisters.advance cycle.nextResponse.sourceDescent
            (.right (SchedulerResponse.pendingFunction program dispatcher
              seedBits continuation) :: nextParents)
          have bridge : ZeroMutationRun
              (SchedulerControl.machine program dispatcher)
              (returnTicks + bridgeDownTicks)
              (selectedReturnConfiguration program dispatcher registers bit suffix
                seedBits continuation carrier afterParents)
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
              dispatcher inputBits firstSampled (by
                simpa using tailSampled)
          refine ⟨terminalParents, checkRegisters,
            firstConfigurations ++ tailConfigurations, ?_, completeSampled,
            ?_, terminalOuter, samples_append firstLicensed tailLicensed, terminalLicensed⟩
          · simpa [continuation, encodedEnvironment, afterParents,
              nextParents, finalRegisters, carrier] using completeChain
          · simp only [List.length_append]
            rw [firstLength, tailLength]
            have finalPhase : finalRegisters.phase = registers.phase :=
              finalCoherent.phase_eq.trans coherent.phase_eq.symm
            calc
              (1 + LocalResponse.completedCost program
                    (dispatcher.route (finalRegisters.phase, bit))
                    (finalRegisters.phase, bit)) +
                  nonemptySweepCost program dispatcher (remaining + 1)
                    ⟨CTS.nextPhase program phase, nextBit :: nextSuffix⟩ =
                  CheckedTransition.totalCost program dispatcher phase
                      (bit :: suffix) +
                    nonemptySweepCost program dispatcher (remaining + 1)
                      ⟨CTS.nextPhase program phase,
                        nextBit :: nextSuffix⟩ := by
                rw [finalPhase, coherent.phase_eq,
                  CheckedTransition.totalCost_cons, dataEq,
                  CheckedTransition.markerCost_cons, Nat.add_zero]
                simp only [Nat.add_zero]
              _ = CheckedTransition.totalCost program dispatcher phase
                      (bit :: suffix) +
                    nonemptySweepCost program dispatcher (remaining + 1)
                      (CTS.absorbingStep program
                        ⟨phase, bit :: suffix⟩) := by
                rw [stepEq]
              _ = nonemptySweepCost program dispatcher
                    ((remaining + 1) + 1) ⟨phase, bit :: suffix⟩ :=
                (nonemptySweepCost_succ program dispatcher (remaining + 1)
                  ⟨phase, bit :: suffix⟩).symm


theorem completeNonemptyJob_licensed
    (program : CTS.Program) (dispatcher : ActionDispatcher program)
    (bit : Bool) (suffix : List Bool) (stage jobs fuel sampleIndex : Nat)
    (environment : Term) (outerParents : List ParentFrame) (layers : Nat)
    (outer : CompletedParents program dispatcher outerParents layers)
    (allowed : OriginSet program)
    (he : Licensed program dispatcher.tree allowed environment)
    (outerLicensed : LicensedParents program dispatcher allowed outerParents)
    (fuelPositive : fuel ≠ 0)
    (allNonempty : ∀ k, k ≤ fuel →
      (CTS.iterate program k
        (CTS.initial program (bit :: suffix))).data ≠ [])
    (sourceAllowed : SourceAllowed allowed (CTS.initial program (bit :: suffix)) fuel) :
    ∃ nextParents checkRegisters configurations,
      ExactMutationChain (SchedulerControl.machine program dispatcher)
        (SchedulerContinuation.checkConfiguration program dispatcher
          checkRegisters
          ⟨Dovetail.clockExit stage (jobs + 1) environment, nextParents⟩)
        (SchedulerNestedPhase.fuelTerminalConfigurationAt program dispatcher
          (bit :: suffix) (Registers.newJob program)
          (Dovetail.clockExit stage (jobs + 1) environment) outerParents fuel 0)
        configurations ∧
      IndexedResponseSampledStates program dispatcher (bit :: suffix)
        sampleIndex configurations ∧
      configurations.length =
        ExactCheckpointRun.jobCost program dispatcher (bit :: suffix) fuel ∧
      CompletedParents program dispatcher nextParents (layers + 1) ∧
      (SchedulerContinuation.checkConfiguration program dispatcher
        checkRegisters
        ⟨Dovetail.clockExit stage (jobs + 1) environment,
          nextParents⟩).cursor.erase =
        Cursor.rebuild nextParents
          (Dovetail.clockExit stage (jobs + 1) environment) ∧
      (Dovetail.clockExit stage (jobs + 1) environment).headArity = 3 ∧
      SamplesLicensed (RootLicensed program dispatcher.tree allowed) configurations ∧
      LicensedParents program dispatcher allowed nextParents := by
  cases fuel with
  | zero => exact (fuelPositive rfl).elim
  | succ remaining =>
      let bits := bit :: suffix
      let continuation := Dovetail.clockExit stage (jobs + 1) environment
      have hb : Ordinary (RootLicensed program dispatcher.tree allowed) continuation := clockExit_ordinary stage (jobs + 1) he
      let encodedEnvironment :=
        environmentCode (compileActions program dispatcher.tree) bits
      let afterParents := PrimitiveFuel.pendingParents encodedEnvironment
        continuation remaining outerParents
      let fullParents := PrimitiveFuel.pendingParents encodedEnvironment
        continuation (remaining + 1) outerParents
      obtain ⟨outerContext, fullContext, innerContext, targetContext,
          descentTicks, responseTicks, response, baseRun⟩ :=
        nonemptyBase_toSelected_zeroRunAt program dispatcher bit suffix
          continuation (Dovetail.clockExit_admissible stage (jobs + 1)
            environment) remaining outerParents
      have parentSplit : fullParents =
          .right (SchedulerResponse.pendingFunction program dispatcher bits
            continuation) :: afterParents := by
        simpa [fullParents, afterParents, encodedEnvironment, continuation,
          SchedulerResponse.pendingFunction,
          PendingFrame.environmentCode_eq_envelope,
          PendingFrame.frameFunction] using
          (SchedulerCycle.pendingParents_succ_cons encodedEnvironment continuation
            remaining outerParents)
      have baseRun' : ZeroMutationRun
          (SchedulerControl.machine program dispatcher) descentTicks
          (SchedulerNestedPhase.fuelTerminalConfigurationAt program dispatcher
            bits (Registers.newJob program) continuation outerParents
            (remaining + 1) 0)
          (upConfiguration program dispatcher
            (Registers.newJob program).clearScan omega
            (ContextCursor.frames fullContext omega
              (.right (SchedulerResponse.pendingFunction program dispatcher bits
                continuation) :: afterParents))) := by
        rw [← parentSplit]
        simpa [bits, continuation, encodedEnvironment, fullParents] using baseRun
      have response' : SelectedResponseTrace program dispatcher bits continuation
          (baseCarrier encodedEnvironment continuation)
          (Dovetail.clockExit_admissible stage (jobs + 1) environment)
          (Registers.newJob program).clearScan bit suffix outerContext fullContext
          innerContext targetContext afterParents responseTicks := by
        simpa [bits, continuation, encodedEnvironment, afterParents] using response
      have sweepNonempty : ∀ k, k ≤ remaining + 1 →
          (CTS.iterate program k
            ⟨CTS.zeroPhase program, bit :: suffix⟩).data ≠ [] := by
        intro k bound
        simpa [bits, CTS.initial] using allNonempty k bound
      obtain ⟨nextParents, checkRegisters, configurations, sweepChain,
          sampled, lengthEq, nextOuter, licensed, nextLicensed⟩ :=
        selectedNonemptySweepToFreshCheck_licensed program dispatcher bits bits stage
          jobs environment outerParents layers outer allowed he outerLicensed remaining sampleIndex
          (Registers.newJob program).clearScan (CTS.zeroPhase program) bit suffix
          (baseCarrier encodedEnvironment continuation) outerContext fullContext
          innerContext targetContext responseTicks
          (RegistersCoherent.initial program).clearScan response' sweepNonempty
          (base_ordinary (environment_ordinary _ program dispatcher bits) hb).1 sourceAllowed
      have completeChain := ExactMutationChain.prepend baseRun' sweepChain
      refine ⟨nextParents, checkRegisters, configurations, ?_, sampled, ?_,
        nextOuter, rfl, Dovetail.headArity_clockExit_succ stage jobs environment, licensed, nextLicensed⟩
      · simpa [bits, continuation, encodedEnvironment] using completeChain
      · rw [lengthEq]
        simpa [bits, CTS.initial] using
          (nonemptySweepCost_initial_eq_jobCost program dispatcher bits
            (remaining + 1))


end SOnlyGlobalOrigins

#print axioms SOnlyGlobalOrigins.responsePairs_licensed
#print axioms SOnlyGlobalOrigins.selectedResponse_licensed
#print axioms SOnlyGlobalOrigins.selectedNonemptyPendingPrefix_licensed
#print axioms SOnlyGlobalOrigins.selectedNonemptySweepToFreshCheck_licensed
#print axioms SOnlyGlobalOrigins.completeNonemptyJob_licensed
