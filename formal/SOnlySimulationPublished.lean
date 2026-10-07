import SOnlySimulationSchedule

/-!
# Literal published width table

Independent transcription of the compact encoder's width recipes. The theorem
compares every slot (including the otherwise unreachable haltB and padding)
with the action-difference schedule used by the simulation proof.
-/
namespace SOnlySimulation

set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

/-- Direct zero-based transcription of `s_only.ut19._widths`.
`block=0` is its first memory, and `block=count+1` its last memory. -/
def publishedWidth (count : Nat) (instruction : Macro) (second : Bool) (block : Nat) : Bool :=
  let first := decide (block = 0)
  let last := decide (block = count+1)
  let adjacent := fun target => decide (block = target ∨ block = target+1)
  match instruction with
  | .dummy => if second then false else last
  | .inc target => if second then Bool.xor (Bool.xor (adjacent target) first) last else false
  | .dec target => if second then adjacent target else first || last
  | .haltA => if second then decide (block = count) else first || last
  | .haltB => false
  | .pad => if second then false else first || last

def publishedEntry : Macro → Bool → Bool
  | .dummy, second => second
  | _, _ => true

def publishedParity : Macro → Bool → Bool
  | .haltA, second => !second
  | _, _ => true

def Macro.Bounded (count : Nat) : Macro → Prop
  | .inc target | .dec target => target < count
  | _ => True

/-- The direct literal width table is the required adjacent action difference. -/
theorem published_width_difference (count : Nat) (instruction : Macro) (second : Bool) (block : Nat)
    (hb : block ≤ count+1) (valid : instruction.Bounded count) :
    publishedWidth count instruction second block =
      Bool.xor (if block = 0 then publishedEntry instruction second
          else macroAction count instruction second (block-1))
        (if block < count+1 then macroAction count instruction second block
          else publishedParity instruction second) := by
  cases instruction with
  | dummy =>
    cases second <;> by_cases h0 : block=0 <;> by_cases hl : block=count+1 <;>
      simp_all [publishedWidth, publishedEntry, publishedParity, macroAction] <;> omega
  | haltB =>
    cases second <;> by_cases h0 : block=0 <;> by_cases hl : block=count+1 <;>
      simp_all [publishedWidth, publishedEntry, publishedParity, macroAction] <;> omega
  | pad =>
    cases second <;> by_cases h0 : block=0 <;> by_cases hl : block=count+1 <;>
      simp_all [publishedWidth, publishedEntry, publishedParity, macroAction] <;> omega
  | haltA =>
    cases second <;> by_cases h0 : block=0 <;> by_cases hl : block=count+1 <;>
      by_cases ht : block=count <;>
      simp_all [publishedWidth, publishedEntry, publishedParity, macroAction] <;> omega
  | inc target =>
    change target < count at valid
    cases second <;> by_cases h0 : block=0 <;> by_cases hl : block=count+1 <;>
      by_cases ht : block=target <;> by_cases hn : block=target+1 <;>
      simp_all [publishedWidth, publishedEntry, publishedParity, macroAction] <;> omega
  | dec target =>
    change target < count at valid
    cases second <;> by_cases h0 : block=0 <;> by_cases hl : block=count+1 <;>
      by_cases ht : block=target <;> by_cases hn : block=target+1 <;>
      simp_all [publishedWidth, publishedEntry, publishedParity, macroAction] <;> omega

/-- Only the initial dummy's first half enters with skip alignment. -/
theorem published_entry_scheduled (program : BPProgram) (time : Nat) :
    publishedEntry (expandedAt program (time/2)) (decide (time%2=1)) = decide (time ≠ 0) := by
  by_cases hz : time/2=0
  · have ht : time=0 ∨ time=1 := by omega
    rcases ht with rfl | rfl <;> simp [expandedAt, publishedEntry]
  · have ht : time ≠ 0 := by omega
    simp only [expandedAt, if_neg hz]
    cases hg : program[time/2-1]? with
    | some command => cases command <;> simp [publishedEntry, ht]
    | none =>
      by_cases hh : time/2=program.length+1
      · simp [hh, publishedEntry, ht]
      · by_cases hh' : time/2=program.length+2 <;> simp [hh, hh', publishedEntry, ht]

/-- The only odd global Parity is the second half of haltA. -/
theorem published_parity_scheduled (program : BPProgram) (time : Nat) :
    publishedParity (expandedAt program (time/2)) (decide (time%2=1)) = scheduledParity program time := by
  by_cases hz : time/2=0
  · have ht : time=0 ∨ time=1 := by omega
    rcases ht with rfl | rfl <;> simp [expandedAt, publishedParity, scheduledParity]
  · simp only [expandedAt, if_neg hz]
    cases hg : program[time/2-1]? with
    | some command =>
      have hi : time/2-1 < program.length := by
        obtain ⟨hi, _⟩ := List.getElem?_eq_some_iff.mp hg
        exact hi
      have ht : time ≠ 2*program.length+3 := by omega
      cases command <;> simp [publishedParity, scheduledParity, ht]
    | none =>
      by_cases hh : time/2=program.length+1
      · rw [if_pos hh]
        simp only [publishedParity, scheduledParity]
        by_cases hm : time%2=1
        · have ht : time=2*program.length+3 := by omega
          simp [ht]
        · have ht : time ≠ 2*program.length+3 := by omega
          simp [hm, ht]
      · have ht : time ≠ 2*program.length+3 := by omega
        simp only [if_neg hh]
        split <;> simp [publishedParity, scheduledParity, ht]

theorem expandedAt_bounded (count : Nat) (program : BPProgram)
    (valid : ∀ command ∈ program, match command with | .inc target | .dec target => target < count)
    (slot : Nat) : (expandedAt program slot).Bounded count := by
  unfold expandedAt
  split
  · trivial
  · cases hg : program[slot-1]? with
    | some command =>
      obtain ⟨hi, he⟩ := List.getElem?_eq_some_iff.mp hg
      have hc : command ∈ program := he ▸ List.getElem_mem hi
      have hv := valid command hc
      cases command <;> exact hv
    | none =>
      by_cases hh : slot=program.length+1
      · simp [hh, Macro.Bounded]
      · by_cases hh' : slot=program.length+2 <;> simp [hh, hh', Macro.Bounded]

/-- All-time equality with the published literal recipes, including both halt
halves and every padding slot. No source run or observation history is used. -/
theorem scheduledWidth_eq_published (count : Nat) (program : BPProgram)
    (valid : ∀ command ∈ program, match command with | .inc target | .dec target => target < count)
    (time block : Nat) (hb : block ≤ count+1) :
    scheduledWidth count program time block =
      publishedWidth count (expandedAt program (time/2)) (decide (time%2=1)) block := by
  rw [published_width_difference count _ _ block hb (expandedAt_bounded count program valid _),
    published_entry_scheduled, published_parity_scheduled]
  rfl

/-- Initial memory generated directly from the published width table. -/
def publishedMemory (depth count : Nat) (program : BPProgram) (block : Nat) : List SOnlyMemory.Cell :=
  SOnlyTemporalMemory.initialCells (SOnlyTemporalMemory.initializer depth
    (fun time => publishedWidth count (expandedAt program (time/2)) (decide (time%2=1)) block))

/-- The simulation's initial memories agree cell-for-cell with the literal
published recipe; equality covers full vectors, not merely their parity. -/
theorem programMemory_zero_eq_published (depth count : Nat) (program : BPProgram)
    (valid : ∀ command ∈ program, match command with | .inc target | .dec target => target < count)
    (block : Nat) (hb : block ≤ count+1) :
    programMemory depth count program 0 block = publishedMemory depth count program block := by
  unfold programMemory epochMemory publishedMemory
  simp only [SOnlyTemporalMemory.memoryRun]
  congr 2
  funext time
  exact scheduledWidth_eq_published count program valid time block hb

end SOnlySimulation

#print axioms SOnlySimulation.scheduledWidth_eq_published
#print axioms SOnlySimulation.programMemory_zero_eq_published
