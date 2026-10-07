import SOnlyMachineFinite

/-!
# Natural-label interface to the UT19 source compiler

The finite compiler uses zero-based dense labels. This module forgets their
bounds into `Nat`, proves exact projection of every actual run, and exports
the all-zero halting/output theorems in the UT19 source interface.
-/
namespace SOnlyMachineNat

open SOnlyMachineBP2 (Command Program State)
open SOnlyMachine (put)

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

/-- Forget the finite label proof without changing an instruction. -/
def liftProgram {count : Nat} (P : Program (Fin count)) : Program Nat :=
  SOnlyMachineFinite.renameProgram Fin.val P

def project (count : Nat) (s : State Nat) : State (Fin count) :=
  ⟨s.pc, fun i => s.value i.val⟩

theorem project_put (count : Nat) (v : Nat → Nat) (i : Fin count) (n : Nat) :
    (fun j : Fin count => put v i.val n j.val) = put (fun j : Fin count => v j.val) i n := by
  funext j
  simp [put, Fin.ext_iff]

theorem execute_project {count : Nat} (command : Command (Fin count)) (s : State Nat) :
    project count (SOnlyMachineBP2.execute (SOnlyMachineFinite.renameCommand Fin.val command) s) =
      SOnlyMachineBP2.execute command (project count s) := by
  cases command with
  | inc i => simp [SOnlyMachineBP2.execute, SOnlyMachineFinite.renameCommand, project, project_put]
  | dec i =>
    by_cases h : s.value i.val = 0 <;>
      simp [SOnlyMachineBP2.execute, SOnlyMachineFinite.renameCommand, project, project_put, h]

theorem advance_project {count : Nat} (P : Program (Fin count)) (s : State Nat) :
    project count (SOnlyMachineBP2.advance (liftProgram P) s) =
      SOnlyMachineBP2.advance P (project count s) := by
  cases h : P[s.pc]? with
  | none => simp [SOnlyMachineBP2.advance, SOnlyMachineBP2.step?, liftProgram,
      SOnlyMachineFinite.renameProgram, project, h]
  | some command =>
    simp only [SOnlyMachineBP2.advance, SOnlyMachineBP2.step?, liftProgram,
      SOnlyMachineFinite.renameProgram, project, List.getElem?_map, h, Option.map_some, Option.getD_some]
    exact execute_project command s

/-- The dense finite trajectory is exactly the restriction of the Nat-label
trajectory, including all restarts and the final retained counter vector. -/
theorem run_project {count : Nat} (P : Program (Fin count)) (k : Nat) (s : State Nat) :
    project count (SOnlyMachineBP2.run (liftProgram P) k s) =
      SOnlyMachineBP2.run P k (project count s) := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    rw [SOnlyMachineBP2.run_succ, ih, advance_project]
    rfl

theorem halted_project {count : Nat} (P : Program (Fin count)) (s : State Nat) :
    SOnlyMachineBP2.Halted (liftProgram P) s ↔ SOnlyMachineBP2.Halted P (project count s) := by
  simp [SOnlyMachineBP2.Halted, project, liftProgram, SOnlyMachineFinite.renameProgram]

theorem bounded {count : Nat} (P : Program (Fin count)) :
    ∀ command ∈ liftProgram P, match command with | .inc target | .dec target => target < count := by
  intro command hc
  rcases List.mem_map.mp hc with ⟨original, ho, he⟩
  subst command
  cases original with
  | inc i => exact i.isLt
  | dec i => exact i.isLt

def counterCount (d n : Nat) : Nat := (SOnlyMachineFinite.targetCells d n).order.length

def compile (M : SOnlyMachine.Machine d n) (input : Fin (d + 1) → Nat) : Program Nat :=
  liftProgram (SOnlyMachineFinite.compile M input)

theorem compile_bounded (M : SOnlyMachine.Machine d n) (input : Fin (d + 1) → Nat) :
    ∀ command ∈ compile M input,
      match command with | .inc target | .dec target => target < counterCount d n :=
  bounded (SOnlyMachineFinite.compile M input)

theorem counterCount_pos (d n : Nat) : 0 < counterCount d n := SOnlyMachineFinite.counter_count_pos d n

theorem compile_nonempty (M : SOnlyMachine.Machine d n) (input : Fin (d + 1) → Nat) :
    0 < (compile M input).length := by
  simpa only [compile, liftProgram, SOnlyMachineFinite.renameProgram, List.length_map] using
    SOnlyMachineFinite.compile_nonempty M input

/-- Every index below counterCount occurs; adding one yields exactly the
published positive labels 1,...,counterCount. -/
theorem compile_dense (M : SOnlyMachine.Machine d n) (input : Fin (d + 1) → Nat)
    (i : Nat) (hi : i < counterCount d n) :
    Command.inc i ∈ compile M input ∨ Command.dec i ∈ compile M input := by
  rcases SOnlyMachineFinite.compile_dense M input ⟨i, hi⟩ with h | h
  · left
    exact List.mem_map_of_mem (f := SOnlyMachineFinite.renameCommand Fin.val) h
  · right
    exact List.mem_map_of_mem (f := SOnlyMachineFinite.renameCommand Fin.val) h

def initialState : State Nat := ⟨0, fun _ => 0⟩

/-- Full frontend theorem in the exact unbounded Nat-label source interface. -/
theorem halt_iff (M : SOnlyMachine.Machine d n) (input : Fin (d + 1) → Nat) :
    (∃ k, SOnlyMachineBP2.Halted (compile M input)
      (SOnlyMachineBP2.run (compile M input) k initialState)) ↔
    (∃ k, M.instruction (SOnlyMachine.sourceRun M k (SOnlyMachine.initial M input)).label = .halt) := by
  have hiff : (∃ k, SOnlyMachineBP2.Halted (compile M input)
      (SOnlyMachineBP2.run (compile M input) k initialState)) ↔
      (∃ k, SOnlyMachineBP2.Halted (SOnlyMachineFinite.compile M input)
      (SOnlyMachineBP2.run (SOnlyMachineFinite.compile M input) k ⟨0, fun _ => 0⟩)) := by
    apply exists_congr
    intro k
    simp only [compile, halted_project, run_project]
    rfl
  exact hiff.trans (SOnlyMachineFinite.halt_iff M input)

theorem halt_output (M : SOnlyMachine.Machine d n) (input : Fin (d + 1) → Nat) (k : Nat)
    (hk : SOnlyMachineBP2.Halted (compile M input)
      (SOnlyMachineBP2.run (compile M input) k initialState)) :
    M.instruction (SOnlyMachine.sourceRun M k (SOnlyMachine.initial M input)).label = .halt ∧
    (SOnlyMachineBP2.run (compile M input) k initialState).value 0 =
      2 * (SOnlyMachine.sourceRun M k (SOnlyMachine.initial M input)).value 0 + 3 := by
  have hf : SOnlyMachineBP2.Halted (SOnlyMachineFinite.compile M input)
      (SOnlyMachineBP2.run (SOnlyMachineFinite.compile M input) k ⟨0, fun _ => 0⟩) := by
    simp only [compile, halted_project, run_project] at hk
    exact hk
  obtain ⟨hh, ho⟩ := SOnlyMachineFinite.halt_output M input k hf
  refine ⟨hh, ?_⟩
  have hr := run_project (SOnlyMachineFinite.compile M input) k initialState
  change project (counterCount d n) (SOnlyMachineBP2.run (compile M input) k initialState) =
    SOnlyMachineBP2.run (SOnlyMachineFinite.compile M input) k ⟨0, fun _ => 0⟩ at hr
  rw [← hr] at ho
  exact ho

theorem readout_correct (M : SOnlyMachine.Machine d n) (input : Fin (d + 1) → Nat) (k : Nat)
    (hk : SOnlyMachineBP2.Halted (compile M input)
      (SOnlyMachineBP2.run (compile M input) k initialState)) :
    SOnlyMachineWaterfallBP2.readOutput
      ((SOnlyMachineBP2.run (compile M input) k initialState).value 0) =
      (SOnlyMachine.sourceRun M k (SOnlyMachine.initial M input)).value 0 := by
  rw [(halt_output M input k hk).2]
  exact SOnlyMachineWaterfallBP2.readOutput_correct _

end SOnlyMachineNat

#print axioms SOnlyMachineNat.halt_iff
#print axioms SOnlyMachineNat.halt_output
#print axioms SOnlyMachineNat.readout_correct
