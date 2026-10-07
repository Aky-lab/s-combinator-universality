import SOnlyMachineWaterfallBP2

/-!
# Amnesiac-counter to tie-free Waterfall arithmetic

The finite rows are the explicit signed rows plus their common positive
offset, represented in natural arithmetic. Coincident action terms add and
cancel, so self-successors are covered without a separate assumption.
-/
namespace SOnlyMachineClock

open SOnlyMachine
open SOnlyMachineBP2 (Enumeration)

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

variable {α : Type} [DecidableEq α]

inductive Clock (α : Type) where
  | data : α → Clock α
  | action : Action α → Clock α
  | recovery : α → Clock α
  deriving DecidableEq, Repr

def normalized (s : SOnlyMachine.State α) : Clock α → Nat
  | .data i => 2 * (s.value i + 1)
  | .action a => if a = s.action then 0 else 4
  | .recovery _ => 4

/-- Literal nonnegative trigger rows, with common offset five. -/
def row (P : Table α) : Clock α → Clock α → Nat
  | .action .halt, _ => 0
  | .action (.inc i), c =>
    5 + (if c = .data i then 2 else 0) + (if c = .action (.inc i) then 4 else 0) -
      (if c = .action (P i).inc then 4 else 0)
  | .action (.dec i), c =>
    5 + (if c = .action (.dec i) then 4 else 0) - (if c = .data i then 2 else 0) -
      (if c = .recovery i then 3 else 0)
  | .data i, c =>
    5 + (if c = .data i then 2 else 0) + (if c = .recovery i then 3 else 0) -
      (if c = .action (P i).failure then 4 else 0)
  | .recovery i, c =>
    6 + (if c = .recovery i then 3 else 0) - (if c = .action (P i).success then 4 else 0)

/-- The intended action is the unique zero, including the halt action. -/
theorem normalized_zero (s : SOnlyMachine.State α) : normalized s (.action s.action) = 0 := by
  simp [normalized]

theorem normalized_other (s : SOnlyMachine.State α) (c : Clock α) (h : c ≠ .action s.action) :
    0 < normalized s c := by
  cases c with
  | data i => simp [normalized] <;> omega
  | action a => simp [normalized, show a ≠ s.action from by intro he; exact h (by rw [he])]
  | recovery i => simp [normalized]

/-- Every nonhalt row entry is positive; in particular no nonhalt diagonal
can fail to reset its triggering clock. -/
theorem row_positive (P : Table α) (i c : Clock α) (hi : i ≠ .action .halt) : 0 < row P i c := by
  cases i with
  | data i => simp only [row]; split <;> split <;> split <;> omega
  | recovery i => simp only [row]; split <;> split <;> omega
  | action a =>
    cases a with
    | halt => exact False.elim (hi rfl)
    | inc i => simp only [row]; split <;> split <;> split <;> omega
    | dec i =>
      cases c <;> simp only [row, reduceCtorEq, if_false]
      all_goals split <;> omega

/-- An increment trigger lands at the next normalized action plus five. -/
theorem increment_row (P : Table α) (v : α → Nat) (i : α) :
    (fun c => normalized ⟨v, .inc i⟩ c + row P (.action (.inc i)) c) =
      (fun c => normalized ⟨put v i (v i + 1), (P i).inc⟩ c + 5) := by
  funext c
  cases c with
  | data j =>
    by_cases h : j = i
    · subst j; simp [normalized, row, put]; omega
    · simp [normalized, row, put, h]
  | recovery j => simp [normalized, row]
  | action a =>
    by_cases h₁ : a = .inc i <;> by_cases h₂ : a = (P i).inc <;>
      simp_all [normalized, row]

/-- The first decrement event leaves all action clocks four, with a recovery
clock one and the decremented data clock deciding the branch. -/
def branch (v : α → Nat) (i : α) : Clock α → Nat
  | .data j => if j = i then 2 * v i else 2 * (v j + 1)
  | .action _ => 4
  | .recovery j => if j = i then 1 else 4

theorem decrement_row (P : Table α) (v : α → Nat) (i : α) :
    (fun c => normalized ⟨v, .dec i⟩ c + row P (.action (.dec i)) c) =
      (fun c => branch v i c + 5) := by
  funext c
  cases c with
  | data j =>
    by_cases h : j = i
    · subst j; simp [normalized, row, branch]; omega
    · simp [normalized, row, branch, h]
  | action a => by_cases h : a = .dec i <;> simp [normalized, row, branch, h]
  | recovery j => by_cases h : j = i <;> simp [normalized, row, branch, h]

theorem branch_zero (v : α → Nat) (i : α) (h : v i = 0) : branch v i (.data i) = 0 := by
  simp [branch, h]

theorem branch_zero_other (v : α → Nat) (i : α) (h : v i = 0)
    (c : Clock α) (hc : c ≠ .data i) : 0 < branch v i c := by
  cases c with
  | data j =>
    have hj : j ≠ i := by intro he; subst j; exact hc rfl
    simp [branch, hj] <;> omega
  | action a => simp [branch]
  | recovery j => by_cases hj : j = i <;> simp [branch, hj]

/-- The failed-decrement data row restores the unchanged counter and selects
its failure action, again at common positive offset five. -/
theorem failure_row (P : Table α) (v : α → Nat) (i : α) (h : v i = 0) :
    (fun c => branch v i c + row P (.data i) c) =
      (fun c => normalized ⟨v, (P i).failure⟩ c + 5) := by
  funext c
  cases c with
  | data j => by_cases hj : j = i <;> simp [branch, row, normalized, hj, h]
  | action a => by_cases ha : a = (P i).failure <;> simp [branch, row, normalized, ha]
  | recovery j => by_cases hj : j = i <;> simp [branch, row, normalized, hj]

/-- Positive-decrement recovery event vector, after one common unit of time. -/
def recovery (v : α → Nat) (i : α) : Clock α → Nat := fun c => branch v i c - 1

theorem recovery_zero (v : α → Nat) (i : α) : recovery v i (.recovery i) = 0 := by
  simp [recovery, branch]

theorem recovery_other (v : α → Nat) (i : α) (h : 0 < v i)
    (c : Clock α) (hc : c ≠ .recovery i) : 0 < recovery v i c := by
  cases c with
  | data j => by_cases hj : j = i <;> simp [recovery, branch, hj] <;> omega
  | action a => simp [recovery, branch]
  | recovery j =>
    have hj : j ≠ i := by intro he; subst j; exact hc rfl
    simp [recovery, branch, hj]

theorem recovery_delay (v : α → Nat) (i : α) (h : 0 < v i) :
    (fun c => branch v i c + 5) = (fun c => recovery v i c + 6) := by
  funext c
  cases c with
  | data j => by_cases hj : j = i <;> simp [recovery, branch, hj] <;> omega
  | action a => simp [recovery, branch]
  | recovery j => by_cases hj : j = i <;> simp [recovery, branch, hj]

/-- The recovery row restores even data values and chooses the successful
continuation, including self-successor cases. -/
theorem success_row (P : Table α) (v : α → Nat) (i : α) (h : 0 < v i) :
    (fun c => recovery v i c + row P (.recovery i) c) =
      (fun c => normalized ⟨put v i (v i - 1), (P i).success⟩ c + 5) := by
  funext c
  cases c with
  | data j => by_cases hj : j = i <;> simp [recovery, branch, row, normalized, put, hj] <;> omega
  | action a => by_cases ha : a = (P i).success <;> simp [recovery, branch, row, normalized, ha]
  | recovery j => by_cases hj : j = i <;> simp [recovery, branch, row, normalized, hj]

/-- An explicit fixed list of the 4k+1 clocks, with a distinguished halt clock. -/
def clockList : List α → List (Clock α)
  | [] => [.action .halt]
  | i :: tail => .data i :: .action (.inc i) :: .action (.dec i) :: .recovery i :: clockList tail

theorem mem_clockList (items : List α) (c : Clock α) :
    c ∈ clockList items ↔ match c with
      | .data i => i ∈ items
      | .recovery i => i ∈ items
      | .action (.inc i) => i ∈ items
      | .action (.dec i) => i ∈ items
      | .action .halt => True := by
  induction items with
  | nil => cases c with
    | data i => simp [clockList]
    | recovery i => simp [clockList]
    | action a => cases a <;> simp [clockList]
  | cons i tail ih => cases c with
    | data j => simp [clockList, ih]
    | recovery j => simp [clockList, ih]
    | action a => cases a <;> simp [clockList, ih]

theorem clockList_nodup (items : List α) (h : items.Nodup) : (clockList items).Nodup := by
  induction items with
  | nil => simp [clockList]
  | cons i tail ih =>
    have hi := (List.nodup_cons.mp h).1
    have ht := ih (List.nodup_cons.mp h).2
    simp [clockList, List.nodup_cons, mem_clockList, hi, ht]

def clocks (e : Enumeration α) : Enumeration (Clock α) where
  order := clockList e.order
  nodup := clockList_nodup e.order e.nodup
  complete := by
    intro c
    rw [mem_clockList]
    cases c with
    | data i => exact e.complete i
    | recovery i => exact e.complete i
    | action a => cases a with
      | inc i => exact e.complete i
      | dec i => exact e.complete i
      | halt => trivial

abbrev BPCell (α : Type) := SOnlyMachineWaterfallBP2.Cell (Clock α)

def program (P : Table α) (e : Enumeration α) (initial : SOnlyMachine.State α) :
    SOnlyMachineBP2.Program (BPCell α) :=
  SOnlyMachineWaterfallBP2.compile (clocks e) (fun c => normalized initial c + 5) (row P) (.action .halt)

/-- A raw action boundary just before the next Waterfall event. -/
def raw (s : SOnlyMachine.State α) : SOnlyMachineBP2.State (BPCell α) :=
  ⟨0, SOnlyMachineWaterfallBP2.ready (fun c => normalized s c + 5) 1⟩

/-- Halting boundaries are the real final BP2 state; nonhalting boundaries
are raw action boundaries. This makes the composed simulation cofinal. -/
def encode (P : Table α) (e : Enumeration α) (initial s : SOnlyMachine.State α) :
    SOnlyMachineBP2.State (BPCell α) :=
  if s.action = .halt then
    ⟨(program P e initial).length, SOnlyMachineWaterfallBP2.ready (fun c => normalized s c + 1) 0⟩
  else raw s

/-- Normalizing a halt boundary executes the complete finite halt exit; other
action boundaries require zero additional target instructions. -/
theorem normalize (P : Table α) (e : Enumeration α) (initial s : SOnlyMachine.State α) :
    ∃ t, SOnlyMachineBP2.run (program P e initial) t (raw s) = encode P e initial s := by
  by_cases h : s.action = .halt
  · have hs : normalized s (.action .halt) = 0 := by simpa [h] using normalized_zero s
    have ho : ∀ c, c ≠ Clock.action Action.halt → 0 < normalized s c := by
      intro c hc
      apply normalized_other s c
      simpa [h] using hc
    obtain ⟨t, ht, he⟩ := SOnlyMachineWaterfallBP2.delayed_halt_event (clocks e)
      (fun c => normalized initial c + 5) (row P) (.action .halt) (normalized s) 5 (by decide) hs ho
    exact ⟨t, by simpa only [program, raw, encode, if_pos h] using he⟩
  · exact ⟨0, by simp [encode, h]⟩

/-- Concatenate a nonempty execution with optional normalization. -/
theorem finish_macro (P : Table α) (e : Enumeration α) (initial s t : SOnlyMachine.State α)
    (h : SOnlyMachineBP2.Reaches (program P e initial) (encode P e initial s) (raw t)) :
    SOnlyMachineBP2.Reaches (program P e initial) (encode P e initial s) (encode P e initial t) := by
  obtain ⟨m, hm, he⟩ := h
  obtain ⟨n, hn⟩ := normalize P e initial t
  exact ⟨m + n, by omega, SOnlyMachineBP2.run_join _ he hn⟩

/-- Every amnesiac action is realized by a nonempty finite execution of the
literal, input-compiled BP2 program, without any interpreter or event oracle. -/
theorem step_simulation (P : Table α) (e : Enumeration α) (initial s : SOnlyMachine.State α) :
    SOnlyMachineBP2.Reaches (program P e initial) (encode P e initial s) (encode P e initial (step P s)) := by
  cases s with
  | mk v a =>
    cases a with
    | halt =>
      refine ⟨1, by decide, ?_⟩
      simp only [step, encode, if_pos rfl]
      exact SOnlyMachineBP2.run_halted _ 1 _ (by exact Nat.le_refl _)
    | inc i =>
      apply finish_macro P e initial ⟨v, .inc i⟩ (step P ⟨v, .inc i⟩)
      have hi : Clock.action (Action.inc i) ≠ Clock.action Action.halt := by simp
      have h := SOnlyMachineWaterfallBP2.delayed_nonhalt_event (clocks e)
        (fun c => normalized initial c + 5) (row P) (.action .halt) (.action (.inc i))
        (normalized ⟨v, .inc i⟩) 5 (by decide) (normalized_zero _) (normalized_other ⟨v, .inc i⟩) hi
        (row_positive P _ _ hi)
      rw [increment_row] at h
      simpa only [program, encode, raw, step, reduceCtorEq, if_false] using h
    | dec i =>
      apply finish_macro P e initial ⟨v, .dec i⟩ (step P ⟨v, .dec i⟩)
      have hi : Clock.action (Action.dec i) ≠ Clock.action Action.halt := by simp
      have hfirst := SOnlyMachineWaterfallBP2.delayed_nonhalt_event (clocks e)
        (fun c => normalized initial c + 5) (row P) (.action .halt) (.action (.dec i))
        (normalized ⟨v, .dec i⟩) 5 (by decide) (normalized_zero _) (normalized_other ⟨v, .dec i⟩) hi
        (row_positive P _ _ hi)
      rw [decrement_row] at hfirst
      by_cases hz : v i = 0
      · have hn : Clock.data i ≠ Clock.action (Action.halt : Action α) := by simp
        have hnext := SOnlyMachineWaterfallBP2.delayed_nonhalt_event (clocks e)
          (fun c => normalized initial c + 5) (row P) (.action .halt) (.data i)
          (branch v i) 5 (by decide) (branch_zero v i hz) (branch_zero_other v i hz) hn
          (row_positive P _ _ hn)
        rw [failure_row P v i hz] at hnext
        have h := SOnlyMachineBP2.reaches_trans _ hfirst hnext
        simpa only [program, encode, raw, step, hz, reduceCtorEq, if_false, if_pos] using h
      · have hp : 0 < v i := by omega
        have hn : Clock.recovery i ≠ Clock.action (Action.halt : Action α) := by simp
        rw [recovery_delay v i hp] at hfirst
        have hnext := SOnlyMachineWaterfallBP2.delayed_nonhalt_event (clocks e)
          (fun c => normalized initial c + 5) (row P) (.action .halt) (.recovery i)
          (recovery v i) 6 (by decide) (recovery_zero v i) (recovery_other v i hp) hn
          (row_positive P _ _ hn)
        rw [success_row P v i hp] at hnext
        have h := SOnlyMachineBP2.reaches_trans _ hfirst hnext
        simpa only [program, encode, raw, step, hz, reduceCtorEq, if_false] using h

/-- The actual all-zero entry executes initialization and, if needed, the halt
exit; every natural input tuple is admitted without a run-length parameter. -/
theorem initial_simulation (P : Table α) (e : Enumeration α) (initial : SOnlyMachine.State α) :
    SOnlyMachineBP2.Reaches (program P e initial) ⟨0, fun _ => 0⟩ (encode P e initial initial) := by
  obtain ⟨m, hm, hi⟩ := SOnlyMachineWaterfallBP2.initialization (clocks e)
    (fun c => normalized initial c + 5) (row P) (.action .halt)
  obtain ⟨n, hn⟩ := normalize P e initial initial
  exact ⟨m + n, by omega, SOnlyMachineBP2.run_join _ hi hn⟩

/-- Arbitrarily long amnesiac runs have cofinal exact BP2 boundary runs. -/
theorem run_simulation (P : Table α) (e : Enumeration α) (initial : SOnlyMachine.State α)
    (k : Nat) (s : SOnlyMachine.State α) :
    ∃ t, k ≤ t ∧ SOnlyMachineBP2.run (program P e initial) t (encode P e initial s) =
      encode P e initial (SOnlyMachine.run P k s) := by
  induction k generalizing s with
  | zero => exact ⟨0, by omega, rfl⟩
  | succ k ih =>
    obtain ⟨m, hm, he⟩ := step_simulation P e initial s
    obtain ⟨n, hn, hf⟩ := ih (step P s)
    exact ⟨m + n, by omega, SOnlyMachineBP2.run_join _ he hf⟩

/-- Include the actual all-zero boot in the cofinal boundary theorem. -/
theorem initialized_run (P : Table α) (e : Enumeration α) (initial : SOnlyMachine.State α) (k : Nat) :
    ∃ t, k ≤ t ∧ SOnlyMachineBP2.run (program P e initial) t ⟨0, fun _ => 0⟩ =
      encode P e initial (SOnlyMachine.run P k initial) := by
  obtain ⟨m, hm, hi⟩ := initial_simulation P e initial
  obtain ⟨n, hn, hh⟩ := run_simulation P e initial k initial
  exact ⟨m + n, by omega, SOnlyMachineBP2.run_join _ hi hh⟩

@[simp] theorem encode_halted_iff (P : Table α) (e : Enumeration α)
    (initial s : SOnlyMachine.State α) :
    SOnlyMachineBP2.Halted (program P e initial) (encode P e initial s) ↔ s.action = .halt := by
  have hp := SOnlyMachineWaterfallBP2.compile_nonempty (clocks e)
    (fun c => normalized initial c + 5) (row P) (.action .halt)
  by_cases h : s.action = .halt
  · simp [encode, h, SOnlyMachineBP2.Halted]
  · simp only [encode, if_neg h, raw, SOnlyMachineBP2.Halted, SOnlyMachineBP2.State.pc, h, iff_false]
    change ¬ (program P e initial).length ≤ 0
    change 0 < (program P e initial).length at hp
    omega

/-- Target halt absorption plus cofinality rules out every premature halt
inside initialization, chain scans, or trigger blocks. -/
theorem halt_boundary (P : Table α) (e : Enumeration α) (initial : SOnlyMachine.State α)
    (k : Nat) (hk : SOnlyMachineBP2.Halted (program P e initial)
      (SOnlyMachineBP2.run (program P e initial) k ⟨0, fun _ => 0⟩)) :
    SOnlyMachineBP2.run (program P e initial) k ⟨0, fun _ => 0⟩ =
      encode P e initial (SOnlyMachine.run P k initial) := by
  obtain ⟨t, ht, he⟩ := initialized_run P e initial k
  have ht' : t = k + (t - k) := by omega
  rw [ht', SOnlyMachineBP2.run_add,
    SOnlyMachineBP2.run_halted _ _ _ hk] at he
  exact he

/-- Exact halting equivalence for arbitrary finite amnesiac programs and inputs. -/
theorem halt_iff (P : Table α) (e : Enumeration α) (initial : SOnlyMachine.State α) :
    (∃ k, SOnlyMachineBP2.Halted (program P e initial)
      (SOnlyMachineBP2.run (program P e initial) k ⟨0, fun _ => 0⟩)) ↔
    (∃ k, (SOnlyMachine.run P k initial).action = .halt) := by
  constructor
  · rintro ⟨k, hk⟩
    have he := halt_boundary P e initial k hk
    rw [he] at hk
    exact ⟨k, (encode_halted_iff P e initial _).mp hk⟩
  · rintro ⟨k, hk⟩
    obtain ⟨t, ht, he⟩ := initialized_run P e initial k
    exact ⟨t, by rw [he]; exact (encode_halted_iff P e initial _).mpr hk⟩

/-- Every actual halted target state carries the same final source data,
through the fixed affine code 2v+3 in every data output coordinate. -/
theorem halt_output (P : Table α) (e : Enumeration α) (initial : SOnlyMachine.State α)
    (k : Nat) (hk : SOnlyMachineBP2.Halted (program P e initial)
      (SOnlyMachineBP2.run (program P e initial) k ⟨0, fun _ => 0⟩)) (output : α) :
    (SOnlyMachine.run P k initial).action = .halt ∧
    (SOnlyMachineBP2.run (program P e initial) k ⟨0, fun _ => 0⟩).value (.value (.data output)) =
      2 * (SOnlyMachine.run P k initial).value output + 3 := by
  have he := halt_boundary P e initial k hk
  have hh : (SOnlyMachine.run P k initial).action = .halt := by
    rw [he] at hk
    exact (encode_halted_iff P e initial _).mp hk
  refine ⟨hh, ?_⟩
  rw [he]
  simp only [encode, if_pos hh, SOnlyMachineBP2.State.value, SOnlyMachineWaterfallBP2.ready,
    SOnlyMachineWaterfallBP2.store, normalized]
  omega

end SOnlyMachineClock
