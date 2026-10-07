import SOnlySimulationHalt

namespace SOnlySimulation

open SOnlySource SOnlyCounter SOnlyMemory SOnlyTemporalMemory

set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

/-- Finite interleaving of n memory/counter pairs followed by a last memory. -/
def indexedWord (mem : Nat → List Cell) (counter : Nat → List Symbol) : Nat → Nat → List Symbol
  | 0, base => memory (mem base)
  | n + 1, base => memory (mem base) ++ (counter base ++ indexedWord mem counter n (base + 1))

def indexedRows (mem : Nat → List Cell) (action : Nat → NormalAction) : Nat → Nat → List NormalRow
  | 0, _ => []
  | n + 1, base => (mem base, action base) :: indexedRows mem action n (base + 1)

theorem indexed_input (mem : Nat → List Cell) (action : Nat → NormalAction) (n base : Nat) :
    rowsWord (indexedRows mem action n base) (mem (base + n)) =
      indexedWord mem (fun b => (action b).input.word) n base := by
  induction n generalizing base with
  | zero => simp [indexedRows, indexedWord]
  | succ n ih =>
    simp only [indexedRows, rowsWord_cons, indexedWord]
    rw [show base + (n + 1) = base + 1 + n from by omega, ih]

theorem indexed_output (mem : Nat → List Cell) (action : Nat → NormalAction)
    (entry : Nat → Bool) (n base : Nat)
    (next : ∀ b, base ≤ b → b < base + n → entry (b + 1) = (action b).take) :
    assemble (normalOutput (entry base) (indexedRows mem action n base) (mem (base + n))) =
      indexedWord (fun b => normalUpdate (entry b) (mem b))
        (fun b => (action b).output.word) n base := by
  induction n generalizing base with
  | zero => simp [indexedRows, normalOutput, indexedWord, assemble, Piece.word]
  | succ n ih =>
    have hnext := next base (by omega) (by omega)
    simp only [indexedRows, normalOutput, assemble, List.flatMap_cons, Piece.word, indexedWord]
    congr 2
    rw [← hnext, show base + (n + 1) = base + 1 + n from by omega]
    exact ih (base + 1) (fun b hb hb' => next b (by omega) (by omega))

/-- Telescoping all adjacent prescribed action differences into the actual
whole-queue phase specification. -/
theorem indexed_fits (mem : Nat → List Cell) (action : Nat → NormalAction)
    (entry : Nat → Bool) (n base : Nat) (p : Bool)
    (next : ∀ b, base ≤ b → b < base + n → entry (b + 1) = (action b).take)
    (width : ∀ b, base ≤ b → b < base + n →
      widthParity (mem b) = Bool.xor (entry b) (action b).take)
    (last : widthParity (mem (base + n)) = Bool.xor (entry (base + n)) p) :
    Fits (entry base) p (indexedRows mem action n base) (mem (base + n)) := by
  induction n generalizing base with
  | zero => simpa [indexedRows, Fits] using last
  | succ n ih =>
    refine ⟨width base (by omega) (by omega), ?_⟩
    rw [← next base (by omega) (by omega)]
    rw [show base + (n + 1) = base + 1 + n from by omega] at last ⊢
    apply ih (base + 1)
    · intro b hb hb'; exact next b (by omega) (by omega)
    · intro b hb hb'; exact width b (by omega) (by omega)
    · exact last

/-- General finite-width global normal simulation stated directly in indexed
memory and counter functions rather than local components. -/
theorem indexed_normal_run (mem : Nat → List Cell) (action : Nat → NormalAction)
    (entry : Nat → Bool) (n : Nat) (positive : 0 < n)
    (hne : mem 0 ≠ [])
    (next : ∀ b, b < n → entry (b + 1) = (action b).take)
    (width : ∀ b, b < n → widthParity (mem b) = Bool.xor (entry b) (action b).take)
    (last : widthParity (mem n) = Bool.xor (entry n) true) :
    SafeRun ⟨indexedWord mem (fun b => (action b).input.word) n 0, entry 0⟩
      ⟨indexedWord (fun b => normalUpdate (entry b) (mem b))
        (fun b => (action b).output.word) n 0, true⟩ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hf := indexed_fits mem action entry (k+1) 0 true
    (fun b _ hb => next b (by omega)) (fun b _ hb => width b (by omega)) (by simpa using last)
  have hr := normal_run (mem 0) (action 0) (indexedRows mem action k 1)
    (mem (k+1)) (entry 0) hne (by simpa [indexedRows] using hf)
  have hi := indexed_input mem action (k+1) 0
  have ho := indexed_output mem action entry (k+1) 0 (fun b _ hb => next b (by omega))
  simp only [Nat.zero_add, indexedRows] at hi ho
  rw [hi, ho] at hr
  exact hr

/-- Epoch memories are specified using the exact constructive initializer and
its arbitrary-forcing update, before any global correctness is assumed. -/
def epochMemory (depth : Nat) (desired entry : Nat → Nat → Bool) (time block : Nat) : List Cell :=
  memoryRun (fun t => !(entry t block)) time (initialCells (initializer depth (fun t => desired t block)))

@[simp] theorem epoch_width (depth : Nat) (desired entry : Nat → Nat → Bool) (time block : Nat)
    (horizon : time < 2 ^ depth) :
    widthParity (epochMemory depth desired entry time block) = desired time block := by
  exact source_programmed_width depth _ _ time horizon

@[simp] theorem epoch_next (depth : Nat) (desired entry : Nat → Nat → Bool) (time block : Nat) :
    epochMemory depth desired entry (time + 1) block =
      normalUpdate (entry time block) (epochMemory depth desired entry time block) := by
  simp only [epochMemory, memoryRun, Bool.not_not]

theorem normalUpdate_length (cells : List Cell) (q : Bool) :
    (normalUpdate q cells).length = cells.length := by
  induction cells generalizing q with
  | nil => rfl
  | cons cell cells ih => cases cell; simp only [normalUpdate, List.length_cons, ih]

theorem memoryRun_length (forcing : Nat → Bool) (time : Nat) (cells : List Cell) :
    (memoryRun forcing time cells).length = cells.length := by
  induction time with
  | zero => rfl
  | succ time ih => rw [memoryRun, normalUpdate_length, ih]

@[simp] theorem epoch_length (depth : Nat) (desired entry : Nat → Nat → Bool) (time block : Nat) :
    (epochMemory depth desired entry time block).length = 2 ^ depth := by
  simp [epochMemory, memoryRun_length, initialCells, initializer_length]

theorem epoch_nonempty (depth : Nat) (desired entry : Nat → Nat → Bool) (time block : Nat) :
    epochMemory depth desired entry time block ≠ [] := by
  intro h
  have hl := epoch_length depth desired entry time block
  rw [h] at hl
  have hp := Nat.pow_pos (n := depth) (by decide : 0 < 2)
  simp only [List.length_nil] at hl
  omega

theorem memoryRun_fixed (forcing : Nat → Bool) (time : Nat) (cells : List Cell) :
    (memoryRun forcing time cells).map Prod.snd = cells.map Prod.snd := by
  induction time with
  | zero => rfl
  | succ time ih => rw [memoryRun, normal_fixed, ih]

/-- Restart really discards the entire preceding forcing history and returns
to the exact original tag initializer, rather than merely matching its parity. -/
theorem epoch_reset (depth : Nat) (desired entry : Nat → Nat → Bool) (time block : Nat) :
    reset (epochMemory depth desired entry time block) = epochMemory depth desired entry 0 block := by
  unfold epochMemory
  change reset (memoryRun _ time _) = initialCells _
  have hf := memoryRun_fixed (fun t => !(entry t block)) time
    (initialCells (initializer depth (fun t => desired t block)))
  have hr : ∀ cells : List Cell, reset cells = initialCells (cells.map Prod.snd) := by
    intro cells; simp [reset, initialCells, List.map_map, Function.comp_def]
  rw [hr, hf]
  simp [initialCells, List.map_map, Function.comp_def]

/-- The programmed-width theorem discharges every global alignment premise of
a normal halfcommand, under only the current horizon bound and literal schedule. -/
theorem epoch_normal_run (depth : Nat) (desired entry : Nat → Nat → Bool)
    (time n : Nat) (action : Nat → NormalAction) (positive : 0 < n)
    (horizon : time < 2 ^ depth)
    (next : ∀ b, b < n → entry time (b + 1) = (action b).take)
    (width : ∀ b, b < n → desired time b = Bool.xor (entry time b) (action b).take)
    (last : desired time n = Bool.xor (entry time n) true) :
    SafeRun ⟨indexedWord (epochMemory depth desired entry time)
        (fun b => (action b).input.word) n 0, entry time 0⟩
      ⟨indexedWord (epochMemory depth desired entry (time + 1))
        (fun b => (action b).output.word) n 0, true⟩ := by
  have hr := indexed_normal_run (epochMemory depth desired entry time) action (entry time) n positive
    (epoch_nonempty depth desired entry time 0) next
    (fun b hb => by rw [epoch_width depth desired entry time b horizon]; exact width b hb)
    (by rw [epoch_width depth desired entry time n horizon]; exact last)
  have he : (fun b => normalUpdate (entry time b) (epochMemory depth desired entry time b)) =
      epochMemory depth desired entry (time + 1) := by
    funext b; exact (epoch_next depth desired entry time b).symm
  rw [he] at hr
  exact hr

/-- All observations required by any epoch are strictly before the first
possible forcing disturbance; no periodic extension is needed. -/
theorem epoch_horizon (length N time : Nat) (capacity : length + 3 ≤ N)
    (needed : time ≤ 2 * length + 3) : time < 2 * N := by omega

end SOnlySimulation

#print axioms SOnlySimulation.indexed_normal_run
#print axioms SOnlySimulation.epoch_normal_run
#print axioms SOnlySimulation.epoch_reset
#print axioms SOnlySimulation.epoch_horizon
