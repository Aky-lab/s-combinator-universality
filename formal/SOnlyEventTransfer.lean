import SOnly38
import PureSFormal.PureS.SchedulerTraceAlgebra

/-!
# Exact-sample chronology and current-tree event-audit bridges

This module mechanizes two new bridges in docs/cts-event-transfer.md: every
indexed element of an exact mutation chain is its corresponding contraction
sample, and an actual normal response's creation audit reconstructs its CTS
prestate through the public, seed-free decoder. These theorems do not assume
that the public checkpoint grammar excludes fabricated descendant events.

The remaining generated-occurrence invariant and ordered labelled stage lift
are not proved here. In particular no theorem here claims that every F17
occurrence in every scheduler sample is an actual selected response.
-/

namespace SOnlyEventTransfer

open PureSFormal PureSFormal.PureS PureSFormal.Research
open SchedulerInvariant

set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

/-- Indexed chronology, strengthening the imported last-sample theorem.
The zero-mutation suffix contributes no sample or hidden index increment. -/
theorem exactChain_sample
    (program : CTS.Program) (dispatcher : ActionDispatcher program)
    (bits : List Bool)
    (initialGood : SampledGood program dispatcher bits 0
      (SchedulerBound.bound program dispatcher)
      (SchedulerControl.initialConfiguration program dispatcher bits)) :
    let system := SampledGood.productiveSystem program dispatcher bits
      (SchedulerBound.bound program dispatcher)
      (SchedulerControl.initialConfiguration program dispatcher bits)
      initialGood
    ∀ {terminal before configurations sampleIndex index sample},
      SchedulerResponseInvariant.ExactMutationChain
        (SchedulerControl.machine program dispatcher) terminal before configurations →
      system.contractionRun sampleIndex = before →
      configurations[index]? = some sample →
      system.contractionRun (sampleIndex + index + 1) = sample := by
  dsimp only
  intro terminal before configurations sampleIndex index sample chain beforeEq atIndex
  revert sampleIndex index sample
  induction chain with
  | done ticks suffix =>
      intro sampleIndex index sample beforeEq atIndex
      simp at atIndex
  | @next before head tail searchTicks found rest ih =>
      intro sampleIndex index sample beforeEq atIndex
      have boundedFound := SchedulerBound.seekMutation_bound program dispatcher found
      have nextEq :
          (SampledGood.productiveSystem program dispatcher bits
            (SchedulerBound.bound program dispatcher)
            (SchedulerControl.initialConfiguration program dispatcher bits)
            initialGood).next before = head :=
        FiniteController.advance_eq_of_seekMutation
          (SchedulerControl.machine program dispatcher)
          (SchedulerBound.bound program dispatcher) boundedFound
      have runNext :
          (SampledGood.productiveSystem program dispatcher bits
            (SchedulerBound.bound program dispatcher)
            (SchedulerControl.initialConfiguration program dispatcher bits)
            initialGood).contractionRun (sampleIndex + 1) = head := by
        rw [show sampleIndex + 1 = Nat.succ sampleIndex by rfl,
          FiniteController.ProductiveSystem.contractionRun_succ, beforeEq, nextEq]
      cases index with
      | zero =>
          have headEq : head = sample := by simpa using atIndex
          simpa [headEq] using runNext
      | succ index =>
          have tailIndex : tail[index]? = some sample := by simpa using atIndex
          have result := ih runNext tailIndex
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using result

/-- The concrete persistent configuration sequence, with proved initial goodness. -/
abbrev persistentSystem (bits : List Bool) :=
  SampledGood.productiveSystem SOnly38.program SOnly38.dispatcher bits
    (SchedulerBound.bound SOnly38.program SOnly38.dispatcher)
    (SchedulerControl.initialConfiguration SOnly38.program SOnly38.dispatcher bits)
    (SchedulerRecurrence.initialGood SOnly38.program SOnly38.dispatcher bits)

/-- Whole-term equality specialized to the actual persistent configurations. -/
theorem trajectory_eq_contractionRun (bits : List Bool) (index : Nat) :
    SOnly38.trajectory bits index =
      ((persistentSystem bits).contractionRun index).cursor.erase := by
  rw [SOnly38.trajectory_eq_persistent]
  rfl

/-- Every exact-chain list element is the corresponding root-reset current tree. -/
theorem exactChain_rootReset_sample (bits : List Bool)
    {terminal before : SchedulerInvariant.Configuration SOnly38.program SOnly38.dispatcher}
    {configurations : List
      (SchedulerInvariant.Configuration SOnly38.program SOnly38.dispatcher)}
    {sampleIndex index : Nat}
    {sample : SchedulerInvariant.Configuration SOnly38.program SOnly38.dispatcher}
    (chain : SchedulerResponseInvariant.ExactMutationChain
      (SchedulerControl.machine SOnly38.program SOnly38.dispatcher)
      terminal before configurations)
    (beforeEq : (persistentSystem bits).contractionRun sampleIndex = before)
    (atIndex : configurations[index]? = some sample) :
    SOnly38.trajectory bits (sampleIndex + index + 1) = sample.cursor.erase := by
  rw [trajectory_eq_contractionRun]
  exact congrArg (fun configuration => configuration.cursor.erase)
    (exactChain_sample SOnly38.program SOnly38.dispatcher bits
      (SchedulerRecurrence.initialGood SOnly38.program SOnly38.dispatcher bits)
      chain beforeEq atIndex)

/-- The frozen halt audit is the literal LLLR field of a fresh Local. -/
def auditAddress : Address := [.left, .left, .left, .right]

/-- Seed-free readout from one candidate shell, with no hidden source parameter. -/
def readAudit (program : CTS.Program) (tree : Dispatcher.Tree (ActionLabel program))
    (term : Term) : Option (List Bool) := do
  let snapshot ← term.subterm? auditAddress
  CheckpointDecoder.decodeCarrier? program tree snapshot

/-- Restore the selected head bit after reading the post-deletion snapshot. -/
def readPrestate (program : CTS.Program)
    (tree : Dispatcher.Tree (ActionLabel program)) (bit : Bool)
    (term : Term) : Option (List Bool) :=
  (readAudit program tree term).map (bit :: ·)

/-- The audit address ignores the accumulator, dispatcher and continuation. -/
theorem freshShell_audit (bits : List Bool)
    (continuation snapshot dispatcher seedAudit continuationAudit : Term) :
    (Carrier.activeShell bits continuation (freshHField snapshot)
      dispatcher seedAudit continuationAudit).subterm? auditAddress = some snapshot := by
  simp [auditAddress, Carrier.activeShell, Carrier.shell, freshHField, Term.subterm?]

theorem completed_audit (bits : List Bool)
    (continuation snapshot completedRoute : Term) :
    (LocalResponse.completed bits continuation snapshot completedRoute).subterm?
      auditAddress = some snapshot := by
  simp [LocalResponse.completed, auditAddress, Carrier.activeShell, Carrier.shell,
    freshHField, Term.subterm?]

/-- An exact fresh layer retains its creation snapshot even when its current
accumulator is different. This is a statement of literal syntax, not safety
under arbitrary S reduction. -/
theorem freshLayer_audit
    {program : CTS.Program} {tree : Dispatcher.Tree (ActionLabel program)}
    {bits : List Bool} {continuation snapshot accumulator result : Term}
    {route : Dispatcher.Route} {label : ActionLabel program} {dispatcher : Term}
    (layer : ReachableAudit.Layer program tree bits continuation snapshot
      accumulator result .fresh route label dispatcher) :
    result.subterm? auditAddress = some snapshot := by
  rw [layer.result_eq]
  simp [auditAddress, Carrier.activeShell, Carrier.shell, ReachableAudit.haltField,
    freshHField, Term.subterm?]

/-- Completion plus the existing source-sensitive decode yields a public
current-tree readout. Only the proof uses the seed and admissible continuation. -/
theorem completed_readPrestate
    (program : CTS.Program) (tree : Dispatcher.Tree (ActionLabel program))
    (bits : List Bool) (continuation snapshot completedRoute : Term)
    (admissible : Carrier.Admissible continuation) (bit : Bool) (suffix : List Bool)
    (decoded : CarrierDecoder.decode? program tree bits continuation admissible snapshot =
      some suffix) :
    readPrestate program tree bit
      (LocalResponse.completed bits continuation snapshot completedRoute) =
        some (bit :: suffix) := by
  have publicDecode := CheckpointRun.decodeCarrier?_of_decode program tree bits
    continuation admissible decoded
  simp [readPrestate, readAudit, completed_audit, publicDecode]

/-- The actual selected-response trace supplies the premise; no extra audit
correctness hypothesis is introduced. -/
theorem selectedResponse_readPrestate
    (program : CTS.Program) (dispatcher : ActionDispatcher program)
    (seedBits : List Bool) (continuation source : Term)
    (admissible : Carrier.Admissible continuation)
    (registers : SchedulerControl.Registers program) (bit : Bool) (suffix : List Bool)
    (outerContext fullContext innerContext targetContext : Context)
    (parents : List ParentFrame) (ticks : Nat)
    (response : SchedulerCycle.SelectedResponseTrace program dispatcher seedBits
      continuation source admissible registers bit suffix outerContext fullContext
      innerContext targetContext parents ticks) :
    readPrestate program dispatcher.tree bit
      (LocalResponse.completed seedBits continuation
        (SchedulerCycle.deletedCarrier bit outerContext innerContext)
        (SchedulerResponse.completedRoute program dispatcher
          (SchedulerCycle.scannedRegisters registers bit suffix) bit
          (SchedulerCycle.deletedCarrier bit outerContext innerContext))) =
      some (bit :: suffix) := by
  exact completed_readPrestate program dispatcher.tree seedBits continuation _ _
    admissible bit suffix response.targetDecode

end SOnlyEventTransfer

#print axioms SOnlyEventTransfer.exactChain_sample
#print axioms SOnlyEventTransfer.trajectory_eq_contractionRun
#print axioms SOnlyEventTransfer.exactChain_rootReset_sample
#print axioms SOnlyEventTransfer.freshShell_audit
#print axioms SOnlyEventTransfer.freshLayer_audit
#print axioms SOnlyEventTransfer.completed_readPrestate
#print axioms SOnlyEventTransfer.selectedResponse_readPrestate
