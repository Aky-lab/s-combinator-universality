import SOnlyStageEvents
import SOnlyResultBits

/-!
# A numerical result in an actual accepted S sample

A selected source configuration with the required first-counter form yields
an actual root-reset S sample, a literal target witness, and the correct
natural-number result read only from that witness's frozen current-tree audit.
The source event and numerical form are hypotheses. No firstness or universal
agreement among all matching witnesses is asserted in this module.
-/
namespace SOnlyWitnessResult

open PureSFormal PureSFormal.PureS
open SOnlySource

/-- Fixed, seed-free numerical projection from one candidate event shell. -/
def readShell (shell : Term) : Option Nat :=
  (SOnlyEventTransfer.readPrestate SOnly38.program SOnly38.dispatcher.tree true shell).bind
    SOnlyResultBits.readMachineBits

/-- Explicitly join source-word simulation, global native event completeness,
bitword restoration and first-counter arithmetic. -/
theorem numerical_witness
    (input tail : List Symbol) (sourceTime value : Nat) (front rest : List Nat)
    (sourceAt : iterate sourceTime ⟨input, true⟩ =
      ⟨(⟨17, by decide⟩ : Symbol) :: tail, true⟩)
    (wordEq : 18 :: SOnlyResultBits.published tail =
      front ++ List.replicate (4 ^ (2 * value + 4)) 16 ++ rest)
    (no16 : ∀ symbol ∈ front, symbol ≠ 16) (notHead : rest.head? ≠ some 16) :
    ∃ sampleIndex address shell,
      SOnlyObserver.event (SOnly38.trajectory (encodeWord input) sampleIndex) = true ∧
      (SOnly38.trajectory (encodeWord input) sampleIndex).subterm? address = some shell ∧
      SOnlyEventPattern.targetPattern.matchesBool shell = true ∧
      readShell shell = some value := by
  have selected : Selected (iterate sourceTime ⟨input, true⟩) := by
    rw [sourceAt]
    exact ⟨rfl, rfl⟩
  have sourceEvent := (event_at_time sourceTime ⟨input, true⟩ ⟨17, by decide⟩).mpr ⟨selected, rfl⟩
  have initialEq : encode ⟨input, true⟩ = CTS.initial SOnly38.program (encodeWord input) := rfl
  rw [initialEq] at sourceEvent
  obtain ⟨index, address, shell, accepted, located, matched, decoded⟩ :=
    SOnlyStageEvents.sourceEvent_reaches_observer (encodeWord input) (19 * sourceTime + 17) sourceEvent
  refine ⟨index, address, shell, accepted, located, matched, ?_⟩
  unfold readShell
  rw [decoded]
  simp only [Option.bind_some]
  rw [← initialEq, Nat.add_comm (19 * sourceTime) 17, CTS.iterate_add,
    trajectory_simulation, sourceAt]
  exact SOnlyResultBits.source_event_result tail front rest value wordEq no16 notHead

end SOnlyWitnessResult

#print axioms SOnlyWitnessResult.numerical_witness
