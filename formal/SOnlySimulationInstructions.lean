import SOnlySimulationSchedule

namespace SOnlySimulation

open SOnlySource SOnlyCounter SOnlyMemory SOnlyTemporalMemory
open SOnlyMachine (put)

set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

/-- An ordinary source tuple, including an auxiliary halt value zero. -/
def valueWords (value : Nat → Nat) (counter : Nat) : List Symbol := C (2 * value counter + 1)

def boundary (depth count : Nat) (program : BPProgram) (pc : Nat) (value : Nat → Nat) : Config :=
  ⟨programWord depth count program (2 * pc + 2) (valueWords value), true⟩

/-- The dummy preserves every ordinary source value, uniformly in its size. -/
theorem dummy_run (depth count : Nat) (program : BPProgram) (value : Nat → Nat)
    (capacity : 1 < 2 ^ depth) :
    SafeRun ⟨programWord depth count program 0 (valueWords value), false⟩
      (boundary depth count program 0 value) := by
  have h1 := scheduled_normal_run depth count program 0 (fun b => NormalAction.dec (2 * value b))
    (by omega) (by intro b hb; simp [NormalAction.take])
    (scheduledParity_normal program 0 (by omega))
  have h2 := scheduled_normal_run depth count program 1 (fun b => NormalAction.inc (2 * value b))
    capacity (by intro b hb; simp [NormalAction.take])
    (scheduledParity_normal program 1 (by omega))
  simp only [NormalAction.input, NormalAction.output, Piece.word, decide_false, decide_true,
    Nat.zero_add] at h1 h2
  exact h1.trans h2

def protectedWords (value : Nat → Nat) (target counter : Nat) : List Symbol :=
  if counter = target then D else valueWords value counter

/-- A restart's one protected target is normalized through the real dummy;
all other source values are preserved, and the target becomes source value one. -/
theorem protected_dummy_run (depth count : Nat) (program : BPProgram) (value : Nat → Nat)
    (target : Nat) (capacity : 1 < 2 ^ depth) :
    SafeRun ⟨programWord depth count program 0 (protectedWords value target), false⟩
      (boundary depth count program 0 (put value target 1)) := by
  let first : Nat → NormalAction := fun b => if b = target then .shield 1 false else .dec (2 * value b)
  let second : Nat → NormalAction := fun b => .inc (if b = target then 2 else 2 * value b)
  have h1 := scheduled_normal_run depth count program 0 first
    (by omega) (by intro b hb; simp only [first]; split <;> simp [NormalAction.take])
    (scheduledParity_normal program 0 (by omega))
  have h2 := scheduled_normal_run depth count program 1 second
    capacity (by intro b hb; simp [second, NormalAction.take])
    (scheduledParity_normal program 1 (by omega))
  have hinput : (fun b => (first b).input.word) = protectedWords value target := by
    funext b; simp only [first, protectedWords]; split <;> rfl
  have hmiddle : (fun b => (first b).output.word) = (fun b => (second b).input.word) := by
    funext b; simp only [first, second]; split <;> rfl
  have houtput : (fun b => (second b).output.word) = valueWords (put value target 1) := by
    funext b; simp only [second, valueWords, put, NormalAction.output, Piece.word]
    split <;> rfl
  rw [hinput, hmiddle] at h1
  rw [houtput] at h2
  exact h1.trans h2

/-- Every legal source increment is two safe global halfcommands. -/
theorem source_increment_run (depth count : Nat) (program : BPProgram) (pc target : Nat)
    (value : Nat → Nat) (fetch : program[pc]? = some (.inc target))
    (capacity : 2 * pc + 3 < 2 ^ depth) :
    SafeRun (boundary depth count program pc value)
      (boundary depth count program (pc + 1) (put value target (value target + 1))) := by
  have hpc : pc < program.length := by
    obtain ⟨h, _⟩ := List.getElem?_eq_some_iff.mp fetch; exact h
  let first : Nat → NormalAction := fun b => .inc (2 * value b + 1)
  let second : Nat → NormalAction := fun b =>
    if b = target then .inc (2 * value b + 2) else .dec (2 * value b + 1)
  have h1 := scheduled_normal_run depth count program (2 * pc + 2) first (by omega)
    (by intro b hb; rw [scheduledAction_source_first count program pc b _ fetch]; rfl)
    (scheduledParity_normal program _ (by omega))
  have h2 := scheduled_normal_run depth count program (2 * pc + 3) second capacity
    (by intro b hb; rw [scheduledAction_source_second count program pc b _ fetch]
        simp only [second]; split <;> simp_all [NormalAction.take])
    (scheduledParity_normal program _ (by omega))
  have hinput : (fun b => (first b).input.word) = valueWords value := rfl
  have hmiddle : (fun b => (first b).output.word) = (fun b => (second b).input.word) := by
    funext b; simp only [first, second]; split <;> rfl
  have houtput : (fun b => (second b).output.word) = valueWords (put value target (value target + 1)) := by
    funext b; simp only [second, valueWords, put]
    split
    · next h => subst b; congr 1 <;> omega
    · rfl
  rw [hinput, hmiddle] at h1
  rw [houtput] at h2
  have hp1 : decide (2 * pc + 2 ≠ 0) = true := by simp
  have hp2 : decide (2 * pc + 3 ≠ 0) = true := by simp
  rw [hp1] at h1
  rw [hp2] at h2
  have he : 2 * pc + 2 + 1 = 2 * pc + 3 := by omega
  rw [he] at h1
  have hout : 2 * pc + 3 + 1 = 2 * (pc + 1) + 2 := by omega
  rw [hout] at h2
  exact h1.trans h2

/-- Every successful source decrement has the same exact boundary simulation. -/
theorem source_positive_decrement_run (depth count : Nat) (program : BPProgram) (pc target : Nat)
    (value : Nat → Nat) (fetch : program[pc]? = some (.dec target))
    (positive : 0 < value target) (capacity : 2 * pc + 3 < 2 ^ depth) :
    SafeRun (boundary depth count program pc value)
      (boundary depth count program (pc + 1) (put value target (value target - 1))) := by
  have hpc : pc < program.length := by
    obtain ⟨h, _⟩ := List.getElem?_eq_some_iff.mp fetch; exact h
  let first : Nat → NormalAction := fun b => .dec (2 * value b)
  let second : Nat → NormalAction := fun b =>
    if b = target then .dec (2 * value b - 1) else .inc (2 * value b)
  have h1 := scheduled_normal_run depth count program (2 * pc + 2) first (by omega)
    (by intro b hb; rw [scheduledAction_source_first count program pc b _ fetch]; rfl)
    (scheduledParity_normal program _ (by omega))
  have h2 := scheduled_normal_run depth count program (2 * pc + 3) second capacity
    (by intro b hb; rw [scheduledAction_source_second count program pc b _ fetch]
        simp only [second]; split <;> simp_all [NormalAction.take])
    (scheduledParity_normal program _ (by omega))
  have hinput : (fun b => (first b).input.word) = valueWords value := rfl
  have hmiddle : (fun b => (first b).output.word) = (fun b => (second b).input.word) := by
    funext b; simp only [first, second]
    split
    · next h => subst b; simp only [NormalAction.input, NormalAction.output, Piece.word]; congr 1; omega
    · rfl
  have houtput : (fun b => (second b).output.word) = valueWords (put value target (value target - 1)) := by
    funext b; simp only [second, valueWords, put]
    split
    · next h => subst b; simp only [NormalAction.output, Piece.word]; congr 1; omega
    · rfl
  rw [hinput, hmiddle] at h1
  rw [houtput] at h2
  have hp1 : decide (2 * pc + 2 ≠ 0) = true := by simp
  have hp2 : decide (2 * pc + 3 ≠ 0) = true := by simp
  rw [hp1] at h1
  rw [hp2] at h2
  have he : 2 * pc + 2 + 1 = 2 * pc + 3 := by omega
  rw [he] at h1
  have hout : 2 * pc + 3 + 1 = 2 * (pc + 1) + 2 := by omega
  rw [hout] at h2
  exact h1.trans h2

end SOnlySimulation

#print axioms SOnlySimulation.dummy_run
#print axioms SOnlySimulation.protected_dummy_run
#print axioms SOnlySimulation.source_increment_run
#print axioms SOnlySimulation.source_positive_decrement_run
