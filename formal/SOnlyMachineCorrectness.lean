import SOnlyMachineBounds

/-!
# Output-specific correctness of the complete finite-input compiler

This is the padded five-helper-per-label, V+5 formal variant documented in
`docs/formal-register-machine-frontend.md`. The proof below identifies every
result, not merely the existence of some halting result.
-/
namespace SOnlyMachineCorrectness

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

/-- Source iteration composes literally, including its absorbing halt state. -/
theorem sourceRun_add (M : SOnlyMachine.Machine d n) (m k : Nat) (s : SOnlyMachine.SourceState d n) :
    SOnlyMachine.sourceRun M (m + k) s =
      SOnlyMachine.sourceRun M k (SOnlyMachine.sourceRun M m s) := by
  induction m generalizing s with
  | zero => simp [SOnlyMachine.sourceRun]
  | succ m ih => simpa [Nat.succ_add, SOnlyMachine.sourceRun] using ih (SOnlyMachine.sourceStep M s)

theorem source_halt_stable (M : SOnlyMachine.Machine d n) (k : Nat) (s : SOnlyMachine.SourceState d n)
    (h : M.instruction s.label = .halt) : SOnlyMachine.sourceRun M k s = s := by
  induction k with
  | zero => rfl
  | succ k ih => simpa [SOnlyMachine.sourceRun, SOnlyMachine.sourceStep, h] using ih

/-- Deterministic source halting has one final vector, independent of how long
the absorbing total semantics has subsequently been run. -/
theorem source_halted_unique (M : SOnlyMachine.Machine d n) (s : SOnlyMachine.SourceState d n)
    (k t : Nat) (hk : M.instruction (SOnlyMachine.sourceRun M k s).label = .halt)
    (ht : M.instruction (SOnlyMachine.sourceRun M t s).label = .halt) :
    SOnlyMachine.sourceRun M k s = SOnlyMachine.sourceRun M t s := by
  have h₁ : SOnlyMachine.sourceRun M (k + t) s = SOnlyMachine.sourceRun M k s := by
    rw [sourceRun_add, source_halt_stable M t _ hk]
  have h₂ : SOnlyMachine.sourceRun M (t + k) s = SOnlyMachine.sourceRun M t s := by
    rw [sourceRun_add, source_halt_stable M k _ ht]
  rw [Nat.add_comm k t] at h₁
  exact h₁.symm.trans h₂

/-- The exact result theorem for the actual all-zero dense Nat-label program:
it halts with first counter 2v+3 iff the given machine halts with result v. -/
theorem output_iff (M : SOnlyMachine.Machine d n) (input : Fin (d + 1) → Nat) (v : Nat) :
    (∃ time, SOnlyMachineBP2.Halted (SOnlyMachineNat.compile M input)
        (SOnlyMachineBP2.run (SOnlyMachineNat.compile M input) time SOnlyMachineNat.initialState) ∧
      (SOnlyMachineBP2.run (SOnlyMachineNat.compile M input) time SOnlyMachineNat.initialState).value 0 = 2 * v + 3) ↔
    (∃ steps, M.instruction (SOnlyMachine.sourceRun M steps (SOnlyMachine.initial M input)).label = .halt ∧
      (SOnlyMachine.sourceRun M steps (SOnlyMachine.initial M input)).value 0 = v) := by
  constructor
  · rintro ⟨time, ht, hv⟩
    obtain ⟨hs, ho⟩ := SOnlyMachineNat.halt_output M input time ht
    refine ⟨time, hs, ?_⟩
    omega
  · rintro ⟨steps, hs, hv⟩
    obtain ⟨time, ht⟩ := (SOnlyMachineNat.halt_iff M input).mpr ⟨steps, hs⟩
    obtain ⟨hs', ho⟩ := SOnlyMachineNat.halt_output M input time ht
    have he := source_halted_unique M (SOnlyMachine.initial M input) steps time hs hs'
    refine ⟨time, ht, ?_⟩
    rw [← he, hv] at ho
    exact ho

/-- Reading the first counter with the fixed arithmetic reader recovers any
specified halting source result at every actual target halt. -/
theorem every_halt_reads_result (M : SOnlyMachine.Machine d n) (input : Fin (d + 1) → Nat)
    (steps : Nat) (hs : M.instruction (SOnlyMachine.sourceRun M steps (SOnlyMachine.initial M input)).label = .halt)
    (time : Nat) (ht : SOnlyMachineBP2.Halted (SOnlyMachineNat.compile M input)
      (SOnlyMachineBP2.run (SOnlyMachineNat.compile M input) time SOnlyMachineNat.initialState)) :
    SOnlyMachineWaterfallBP2.readOutput
      ((SOnlyMachineBP2.run (SOnlyMachineNat.compile M input) time SOnlyMachineNat.initialState).value 0) =
      (SOnlyMachine.sourceRun M steps (SOnlyMachine.initial M input)).value 0 := by
  have hs' := (SOnlyMachineNat.halt_output M input time ht).1
  have he := source_halted_unique M (SOnlyMachine.initial M input) steps time hs hs'
  rw [SOnlyMachineNat.readout_correct M input time ht, ← he]

end SOnlyMachineCorrectness

#print axioms SOnlyMachineCorrectness.output_iff
#print axioms SOnlyMachineCorrectness.every_halt_reads_result
