import SOnlySimulationEpoch
import SOnlyMachineBP2

namespace SOnlySimulation

open SOnlySource SOnlyCounter SOnlyMemory SOnlyTemporalMemory

set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

abbrev BPProgram := SOnlyMachineBP2.Program Nat
abbrev BPCommand := SOnlyMachineBP2.Command Nat

inductive Macro where
  | dummy | inc (target : Nat) | dec (target : Nat) | haltA | haltB | pad

def expandedAt (program : BPProgram) (slot : Nat) : Macro :=
  if slot = 0 then .dummy else
  match program[slot - 1]? with
  | some (.inc target) => .inc target
  | some (.dec target) => .dec target
  | none => if slot = program.length + 1 then .haltA
            else if slot = program.length + 2 then .haltB else .pad

/-- The action schedule is indexed by zero-based source labels, with the
additional halt counter at `count`. True means increment/take. -/
def macroAction (count : Nat) (instruction : Macro) (second : Bool) (counter : Nat) : Bool :=
  match instruction with
  | .dummy | .pad => second
  | .inc target => if second then decide (counter = target) else true
  | .dec target => if second then decide (counter ≠ target) else false
  | .haltA => if second then decide (counter ≠ count) else false
  | .haltB => true

def scheduledAction (count : Nat) (program : BPProgram) (time counter : Nat) : Bool :=
  macroAction count (expandedAt program (time / 2)) (decide (time % 2 = 1)) counter

def scheduledParity (program : BPProgram) (time : Nat) : Bool :=
  decide (time ≠ 2 * program.length + 3)

/-- Memory input alignment: the initial leading 19 or a previous odd Reset
supplies skip at time zero; subsequent normal Command phases are take. -/
def scheduledEntry (count : Nat) (program : BPProgram) (time block : Nat) : Bool :=
  if block = 0 then decide (time ≠ 0)
  else scheduledAction count program time (block - 1)

def scheduledExit (count : Nat) (program : BPProgram) (time block : Nat) : Bool :=
  if block < count + 1 then scheduledAction count program time block
  else scheduledParity program time

/-- Adjacent action differences specify exactly every emitted memory width. -/
def scheduledWidth (count : Nat) (program : BPProgram) (time block : Nat) : Bool :=
  Bool.xor (scheduledEntry count program time block) (scheduledExit count program time block)

def programMemory (depth count : Nat) (program : BPProgram) (time block : Nat) : List Cell :=
  epochMemory depth (scheduledWidth count program) (scheduledEntry count program) time block

def programWord (depth count : Nat) (program : BPProgram) (time : Nat)
    (counter : Nat → List Symbol) : List Symbol :=
  indexedWord (programMemory depth count program time) counter (count + 1) 0

@[simp] theorem scheduledEntry_next (count : Nat) (program : BPProgram) (time block : Nat) :
    scheduledEntry count program time (block + 1) = scheduledAction count program time block := by
  simp [scheduledEntry]

@[simp] theorem scheduledEntry_first (count : Nat) (program : BPProgram) (time : Nat) :
    scheduledEntry count program time 0 = decide (time ≠ 0) := rfl

/-- Kernel-checked construction-to-global-run interface: no memory alignment
premises remain, only the actual requested counter action schedule. -/
theorem scheduled_normal_run (depth count : Nat) (program : BPProgram) (time : Nat)
    (action : Nat → NormalAction) (horizon : time < 2 ^ depth)
    (agrees : ∀ b, b < count + 1 → (action b).take = scheduledAction count program time b)
    (parity : scheduledParity program time = true) :
    SafeRun ⟨programWord depth count program time (fun b => (action b).input.word), decide (time ≠ 0)⟩
      ⟨programWord depth count program (time + 1) (fun b => (action b).output.word), true⟩ := by
  have hr := epoch_normal_run depth (scheduledWidth count program) (scheduledEntry count program)
    time (count+1) action (by omega) horizon
    (fun b hb => by rw [scheduledEntry_next, agrees b hb])
    (fun b hb => by simp only [scheduledWidth, scheduledExit, if_pos hb, agrees b hb])
    (by simp [scheduledWidth, scheduledExit, parity])
  exact hr

@[simp] theorem expandedAt_zero (program : BPProgram) : expandedAt program 0 = .dummy := by
  simp [expandedAt]

theorem expandedAt_source (program : BPProgram) (index : Nat) (command : BPCommand)
    (fetch : program[index]? = some command) :
    expandedAt program (index + 1) = match command with | .inc t => .inc t | .dec t => .dec t := by
  simp [expandedAt, fetch]
  cases command <;> rfl

theorem expandedAt_halt (program : BPProgram) : expandedAt program (program.length + 1) = .haltA := by
  simp [expandedAt]

@[simp] theorem scheduledAction_zero (count : Nat) (program : BPProgram) (b : Nat) :
    scheduledAction count program 0 b = false := by simp [scheduledAction, macroAction]

@[simp] theorem scheduledAction_one (count : Nat) (program : BPProgram) (b : Nat) :
    scheduledAction count program 1 b = true := by simp [scheduledAction, macroAction]

theorem scheduledAction_source_first (count : Nat) (program : BPProgram) (i b : Nat)
    (command : BPCommand) (fetch : program[i]? = some command) :
    scheduledAction count program (2 * i + 2) b =
      match command with | .inc _ => true | .dec _ => false := by
  have hd : (2 * i + 2) / 2 = i + 1 := by omega
  have hm : (2 * i + 2) % 2 = 0 := by omega
  rw [scheduledAction, hd, hm, expandedAt_source program i command fetch]
  cases command <;> rfl

theorem scheduledAction_source_second (count : Nat) (program : BPProgram) (i b : Nat)
    (command : BPCommand) (fetch : program[i]? = some command) :
    scheduledAction count program (2 * i + 3) b =
      match command with | .inc t => decide (b = t) | .dec t => decide (b ≠ t) := by
  have hd : (2 * i + 3) / 2 = i + 1 := by omega
  have hm : (2 * i + 3) % 2 = 1 := by omega
  rw [scheduledAction, hd, hm, expandedAt_source program i command fetch]
  cases command <;> rfl

theorem scheduledAction_halt_first (count : Nat) (program : BPProgram) (b : Nat) :
    scheduledAction count program (2 * program.length + 2) b = false := by
  have hd : (2 * program.length + 2) / 2 = program.length + 1 := by omega
  have hm : (2 * program.length + 2) % 2 = 0 := by omega
  rw [scheduledAction, hd, hm, expandedAt_halt]
  rfl

theorem scheduledAction_halt_second (count : Nat) (program : BPProgram) (b : Nat) :
    scheduledAction count program (2 * program.length + 3) b = decide (b ≠ count) := by
  have hd : (2 * program.length + 3) / 2 = program.length + 1 := by omega
  have hm : (2 * program.length + 3) % 2 = 1 := by omega
  rw [scheduledAction, hd, hm, expandedAt_halt]
  rfl

theorem scheduledParity_normal (program : BPProgram) (time : Nat)
    (before : time < 2 * program.length + 3) : scheduledParity program time = true := by
  simp [scheduledParity, show time ≠ 2 * program.length + 3 from by omega]

@[simp] theorem scheduledParity_halt (program : BPProgram) :
    scheduledParity program (2 * program.length + 3) = false := by simp [scheduledParity]

/-- The canonical initial finite word, including the single leading label 19. -/
def seed (depth count : Nat) (program : BPProgram) : List Symbol :=
  (18 : Symbol) :: programWord depth count program 0 (fun _ => C 1)

/-- The leading 19 is consumed without output and supplies the first odd
Command alignment. It is not an event or an empty-queue transition. -/
theorem seed_prefix_run (depth count : Nat) (program : BPProgram) :
    SafeRun ⟨seed depth count program, true⟩
      ⟨programWord depth count program 0 (fun _ => C 1), false⟩ := by
  refine ⟨1, by omega, ?_, ?_⟩
  · have hp : production (18 : Symbol) = [] := by decide +kernel
    simp [iterate, step, seed, hp]
  · intro time ht
    have hz : time = 0 := by omega
    subst time
    simp [iterate, Selected, seed]

end SOnlySimulation

#print axioms SOnlySimulation.scheduled_normal_run
#print axioms SOnlySimulation.seed_prefix_run
