import SOnlySimulationInstructions

namespace SOnlySimulation

open SOnlySource SOnlyCounter SOnlyMemory SOnlyTemporalMemory
open SOnlyMachine (put)

set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

def indexedIncrementRows (mem : Nat → List Cell) (exponent : Nat → Nat) : Nat → Nat → List IncrementRow
  | 0, _ => []
  | n + 1, base => (mem base, exponent base) :: indexedIncrementRows mem exponent n (base + 1)

def indexedPrefix (mem : Nat → List Cell) (counter : Nat → List Symbol) : Nat → Nat → List Symbol → List Symbol
  | 0, _, tail => tail
  | n + 1, base, tail => memory (mem base) ++ (counter base ++ indexedPrefix mem counter n (base + 1) tail)

theorem indexedWord_prefix (mem : Nat → List Cell) (counter : Nat → List Symbol) (n base : Nat) :
    indexedWord mem counter n base = indexedPrefix mem counter n base (memory (mem (base + n))) := by
  induction n generalizing base with
  | zero => simp [indexedWord, indexedPrefix]
  | succ n ih =>
    simp only [indexedWord, indexedPrefix, ih]
    rw [show base + 1 + n = base + (n+1) from by omega]

theorem indexedWord_split (mem : Nat → List Cell) (counter : Nat → List Symbol) (left right base : Nat) :
    indexedWord mem counter (left + right) base =
      indexedPrefix mem counter left base (indexedWord mem counter right (base + left)) := by
  induction left generalizing base with
  | zero => simp [indexedPrefix]
  | succ left ih =>
    rw [Nat.succ_add]
    simp only [indexedWord, indexedPrefix, ih]
    rw [show base + 1 + left = base + (left+1) from by omega]

theorem indexedPrefix_increments (mem : Nat → List Cell) (counter : Nat → List Symbol)
    (exponent : Nat → Nat) (n base : Nat) (tail : List Symbol)
    (hc : ∀ b, base ≤ b → b < base + n → counter b = C (exponent b)) :
    indexedPrefix mem counter n base tail =
      incrementPrefix (indexedIncrementRows mem exponent n base) tail := by
  induction n generalizing base with
  | zero => rfl
  | succ n ih =>
    simp only [indexedPrefix, indexedIncrementRows, incrementPrefix]
    rw [hc base (by omega) (by omega), ih (base+1)]
    intro b hb hb'; exact hc b (by omega) (by omega)

/-- Cut the actual interleaved word at an arbitrary selected counter. -/
theorem indexed_exceptional_word (mem : Nat → List Cell) (counter : Nat → List Symbol)
    (exponent : Nat → Nat) (count target : Nat) (ht : target < count + 1)
    (hc : ∀ b, b < count + 1 → b ≠ target → counter b = C (exponent b)) :
    indexedWord mem counter (count + 1) 0 =
      incrementPrefix (indexedIncrementRows mem exponent target 0)
        (memory (mem target) ++ (counter target ++
          incrementPrefix (indexedIncrementRows mem exponent (count - target) (target + 1))
            (memory (mem (count + 1))))) := by
  have hn : count + 1 = target + (count - target + 1) := by omega
  conv => lhs; rw [hn]
  rw [indexedWord_split, Nat.zero_add, indexedWord]
  rw [indexedWord_prefix]
  rw [show target + 1 + (count - target) = count + 1 from by omega]
  rw [indexedPrefix_increments mem counter exponent target 0]
  · congr 2
    rw [indexedPrefix_increments mem counter exponent (count-target) (target+1)]
    intro b hb hb'; exact hc b (by omega) (by omega)
  · intro b hb hb'; exact hc b (by omega) (by omega)

theorem indexedIncrement_map (mem : Nat → List Cell) (exponent : Nat → Nat) (n base : Nat) :
    (indexedIncrementRows mem exponent n base).map (fun row => (reset row.1, row.2 + 1)) =
      indexedIncrementRows (fun b => reset (mem b)) (fun b => exponent b + 1) n base := by
  induction n generalizing base with
  | zero => rfl
  | succ n ih => simp only [indexedIncrementRows, List.map_cons, ih]

theorem indexedIncrement_nonempty (mem : Nat → List Cell) (exponent : Nat → Nat) (n base : Nat)
    (hn : ∀ b, mem b ≠ []) : ∀ row ∈ indexedIncrementRows mem exponent n base, row.1 ≠ [] := by
  induction n generalizing base with
  | zero => simp [indexedIncrementRows]
  | succ n ih =>
    intro row hrow
    simp only [indexedIncrementRows, List.mem_cons] at hrow
    rcases hrow with rfl | hrow
    · exact hn base
    · exact ih (base+1) row hrow

theorem indexedIncrement_fits (mem : Nat → List Cell) (exponent : Nat → Nat)
    (entry : Nat → Bool) (n base : Nat)
    (next : ∀ b, base ≤ b → b < base + n → entry (b+1) = true)
    (width : ∀ b, base ≤ b → b < base + n → widthParity (mem b) = Bool.xor (entry b) true) :
    IncrementFits (entry base) (indexedIncrementRows mem exponent n base) ∧
      incrementEnd (entry base) (indexedIncrementRows mem exponent n base) = entry (base+n) := by
  induction n generalizing base with
  | zero => simp [indexedIncrementRows, IncrementFits, incrementEnd]
  | succ n ih =>
    have hi := ih (base+1) (fun b hb hb' => next b (by omega) (by omega))
      (fun b hb hb' => width b (by omega) (by omega))
    rw [next base (by omega) (by omega)] at hi
    refine ⟨⟨width base (by omega) (by omega), hi.1⟩, ?_⟩
    change incrementEnd true (indexedIncrementRows mem exponent n (base+1)) = _
    rw [hi.2]
    congr 1; omega

/-- All actual memory widths in an exceptional halfcommand are supplied by
one epoch observation, including the suffix after the flipped Parity phase. -/
theorem scheduled_exceptional_fits (depth count : Nat) (program : BPProgram)
    (time target : Nat) (exponent : Nat → Nat) (ht : target < count+1)
    (horizon : time < 2 ^ depth)
    (actions : ∀ b, b < count+1 → scheduledAction count program time b = decide (b ≠ target)) :
    ExceptionalFits (scheduledEntry count program time 0) (scheduledParity program time)
      (indexedIncrementRows (programMemory depth count program time) exponent target 0)
      (indexedIncrementRows (programMemory depth count program time) exponent (count-target) (target+1))
      (programMemory depth count program time target) (programMemory depth count program time (count+1)) := by
  let mem := programMemory depth count program time
  let entry := scheduledEntry count program time
  have width : ∀ b, b < count+1 → widthParity (mem b) = Bool.xor (entry b) (decide (b ≠ target)) := by
    intro b hb
    rw [show mem b = epochMemory depth (scheduledWidth count program) (scheduledEntry count program) time b from rfl,
      epoch_width _ _ _ _ _ horizon]
    simp only [scheduledWidth, scheduledExit, if_pos hb, actions b hb, entry]
  have next : ∀ b, entry (b+1) = scheduledAction count program time b := fun b => scheduledEntry_next _ _ _ _
  have htphase : entry (target+1) = false := by rw [next, actions target ht]; simp
  have hp := indexedIncrement_fits mem exponent entry target 0
    (fun b _ hb => by rw [next, actions b (by omega)]; simp [show b ≠ target from by omega])
    (fun b _ hb => by rw [width b (by omega)]; simp [show b ≠ target from by omega])
  have ha := indexedIncrement_fits mem exponent entry (count-target) (target+1)
    (fun b hb hb' => by rw [next, actions b (by omega)]; simp [show b ≠ target from by omega])
    (fun b hb hb' => by rw [width b (by omega)]; simp [show b ≠ target from by omega])
  rw [htphase] at ha
  refine ⟨hp.1, ?_, ha.1, ?_⟩
  · rw [hp.2, Nat.zero_add, width target ht]; simp
  · rw [ha.2, show target + 1 + (count-target) = count+1 from by omega]
    change widthParity (epochMemory depth (scheduledWidth count program) (scheduledEntry count program) time (count+1)) = _
    rw [epoch_width _ _ _ _ _ horizon]
    simp [scheduledWidth, scheduledExit, entry]

/-- Actual zero-decrement second half: exact reset to the initial memory epoch,
with only the chosen counter protected. -/
theorem scheduled_zero_reset_run (depth count : Nat) (program : BPProgram)
    (time target : Nat) (value : Nat → Nat) (ht : target < count+1)
    (zero : value target = 0) (horizon : time < 2 ^ depth)
    (actions : ∀ b, b < count+1 → scheduledAction count program time b = decide (b ≠ target))
    (parity : scheduledParity program time = true) :
    SafeRun ⟨programWord depth count program time (fun b => C (2 * value b)), scheduledEntry count program time 0⟩
      ⟨programWord depth count program 0 (protectedWords value target), false⟩ := by
  let mem := programMemory depth count program time
  let before := indexedIncrementRows mem (fun b => 2 * value b) target 0
  let after := indexedIncrementRows mem (fun b => 2 * value b) (count-target) (target+1)
  have fits := scheduled_exceptional_fits depth count program time target (fun b => 2*value b) ht horizon actions
  rw [parity] at fits
  have hne : ∀ b, mem b ≠ [] := fun b => epoch_nonempty depth _ _ time b
  have hr := exceptional_reset_run before after (mem target) (mem (count+1))
    (scheduledEntry count program time 0) fits (hne target)
    (indexedIncrement_nonempty mem _ target 0 hne)
  rw [exceptional_reset before after _ _ _ fits] at hr
  have hi : programWord depth count program time (fun b => C (2*value b)) =
      exceptionalWord before after (mem target) (mem (count+1)) := by
    unfold programWord
    rw [indexed_exceptional_word _ _ (fun b => 2*value b) count target ht (by intro b hb hbt; rfl)]
    simp only [zero, Nat.mul_zero]
    rfl
  have resetmem : (fun b => reset (mem b)) = programMemory depth count program 0 := by
    funext b; exact epoch_reset depth _ _ time b
  have hout : programWord depth count program 0 (protectedWords value target) =
      incrementPrefix (before.map (fun row => (reset row.1, row.2+1)))
        (memory (reset (mem target)) ++ (D ++
          incrementPrefix (after.map (fun row => (reset row.1, row.2+1))) (memory (reset (mem (count+1)))))) := by
    unfold programWord
    rw [indexed_exceptional_word _ _ (fun b => 2*value b+1) count target ht]
    · simp only [protectedWords, ite_true]
      simp only [before, after, indexedIncrement_map]
      rw [resetmem, congrFun resetmem target, congrFun resetmem (count+1)]
    · intro b hb hbt; simp [protectedWords, hbt, valueWords]
  rw [← hi, ← hout] at hr
  exact hr

/-- A failed BP2 decrement includes the restarted dummy before reestablishing
the ordinary source boundary, so arbitrary many restarts can be composed. -/
theorem source_zero_decrement_run (depth count : Nat) (program : BPProgram) (pc target : Nat)
    (value : Nat → Nat) (fetch : program[pc]? = some (.dec target)) (ht : target < count+1)
    (zero : value target = 0) (capacity : 2 * pc + 3 < 2 ^ depth) :
    SafeRun (boundary depth count program pc value)
      (boundary depth count program 0 (put value target 1)) := by
  have hpc : pc < program.length := by obtain ⟨h, _⟩ := List.getElem?_eq_some_iff.mp fetch; exact h
  have h1 := scheduled_normal_run depth count program (2*pc+2) (fun b => NormalAction.dec (2*value b))
    (by omega)
    (by intro b hb; rw [scheduledAction_source_first count program pc b _ fetch]; rfl)
    (scheduledParity_normal program _ (by omega))
  have h2 := scheduled_zero_reset_run depth count program (2*pc+3) target value ht zero capacity
    (fun b _ => scheduledAction_source_second count program pc b _ fetch)
    (scheduledParity_normal program _ (by omega))
  have h3 := protected_dummy_run depth count program value target (by omega)
  have hp1 : decide (2*pc+2 ≠ 0) = true := by simp
  have hp2 : scheduledEntry count program (2*pc+3) 0 = true := by simp
  simp only [NormalAction.input, NormalAction.output, Piece.word, hp1] at h1
  rw [hp2] at h2
  rw [show 2*pc+2+1 = 2*pc+3 from by omega] at h1
  exact h1.trans (h2.trans h3)

end SOnlySimulation

#print axioms SOnlySimulation.scheduled_zero_reset_run
#print axioms SOnlySimulation.source_zero_decrement_run
