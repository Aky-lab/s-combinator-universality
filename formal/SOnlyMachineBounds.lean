import SOnlyMachineNat

/-!
# Effective size bounds for the formal frontend variant

This formal compiler allocates all five I/S/F/U/V helpers at every label and
starts Waterfall at V+5, unlike the selective helper allocation and V+1 in the
Python reference. For D=d+1 registers, Q=n+1 labels, s=sum(input), put k=D+5Q.
It has N=4k+1 clocks and C=8k+3 BP2 counters. The theorem below proves a safe
polynomial command bound 2C(2s+9)+N(18C+2)+C+4N+4. The input values occur only
in the finite unary initializer; construction never runs the source machine.
-/
namespace SOnlyMachineBounds

open SOnlyMachineBP2 (Enumeration)

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

variable {α β : Type}

theorem sum_le (items : List α) (f : α → Nat) (bound : Nat)
    (h : ∀ i ∈ items, f i ≤ bound) : (items.map f).sum ≤ items.length * bound := by
  induction items with
  | nil => simp
  | cons i tail ih =>
    have hi := h i (by simp)
    have ht := ih (by intro j hj; exact h j (by simp [hj]))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

theorem member_le_sum (items : List α) (f : α → Nat) (i : α) (hi : i ∈ items) :
    f i ≤ (items.map f).sum := by
  induction items with
  | nil => simp at hi
  | cons j tail ih =>
    simp only [List.mem_cons] at hi
    simp only [List.map_cons, List.sum_cons]
    rcases hi with h | h
    · subst i; omega
    · have := ih h; omega

theorem flatMap_length_le (items : List α) (f : α → List β) (bound : Nat)
    (h : ∀ i ∈ items, (f i).length ≤ bound) : (items.flatMap f).length ≤ items.length * bound := by
  rw [List.length_flatMap]
  exact sum_le items _ bound h

theorem unary_length_le [DecidableEq α] (e : Enumeration α) (weight : α → Nat) (bound : Nat)
    (h : ∀ i, weight i ≤ bound) :
    (SOnlyMachineBP2.unary e.order weight).length ≤ e.order.length * bound := by
  exact flatMap_length_le e.order _ bound (by intro i hi; simpa using h i)

theorem guarded_length [DecidableEq α] (word : List α) (guard : α) :
    (SOnlyMachineBP2.guarded word guard).length = 2 * word.length + 2 := by
  simp [SOnlyMachineBP2.guarded, SOnlyMachineBP2.addMany, SOnlyMachineBP2.subMany]
  omega

theorem guarded_length_le [DecidableEq α] (e : Enumeration α) (weight : α → Nat) (guard : α)
    (bound : Nat) (h : ∀ i, weight i ≤ bound) :
    (SOnlyMachineBP2.guarded (SOnlyMachineBP2.unary e.order weight) guard).length ≤
      2 * (e.order.length * bound) + 2 := by
  rw [guarded_length]
  have := unary_length_le e weight bound h
  omega

theorem auxList_length {d n : Nat} (items : List (Fin (n + 1))) :
    (SOnlyMachineFinite.auxList (d := d) items).length = 5 * items.length := by
  induction items with
  | nil => rfl
  | cons i tail ih => simp [SOnlyMachineFinite.auxList, ih]; omega

def helperCount (d n : Nat) : Nat := (d + 1) + 5 * (n + 1)

@[simp] theorem machineCells_length (d n : Nat) :
    (SOnlyMachineFinite.machineCells d n).order.length = helperCount d n := by
  simp [SOnlyMachineFinite.machineCells, auxList_length, helperCount]

theorem clockList_length (items : List α) :
    (SOnlyMachineClock.clockList items).length = 4 * items.length + 1 := by
  induction items with
  | nil => rfl
  | cons i tail ih => simp [SOnlyMachineClock.clockList, ih]; omega

@[simp] theorem clocks_length [DecidableEq α] (e : Enumeration α) :
    (SOnlyMachineClock.clocks e).order.length = 4 * e.order.length + 1 := clockList_length _

@[simp] theorem cells_length [DecidableEq α] (e : Enumeration α) :
    (SOnlyMachineWaterfallBP2.cells e).order.length = 2 * e.order.length + 1 := by
  simp [SOnlyMachineWaterfallBP2.cells]; omega

@[simp] theorem counterCount_exact (d n : Nat) :
    SOnlyMachineNat.counterCount d n = 8 * helperCount d n + 3 := by
  simp [SOnlyMachineNat.counterCount, SOnlyMachineFinite.targetCells]
  omega

/-- All actual rows have uniformly bounded entries, independent of input. -/
theorem row_le_nine [DecidableEq α] (P : SOnlyMachine.Table α) (i c : SOnlyMachineClock.Clock α) :
    SOnlyMachineClock.row P i c ≤ 9 := by
  cases i with
  | data i => cases c <;> simp [SOnlyMachineClock.row] <;> (repeat (first | split | omega))
  | recovery i => cases c <;> simp [SOnlyMachineClock.row] <;> (repeat (first | split | omega))
  | action a => cases a <;> cases c <;> simp [SOnlyMachineClock.row] <;> (repeat (first | split | omega))

/-- A conservative syntax-size bound for any bounded-row Waterfall instance. -/
theorem waterfall_length_bound [DecidableEq α] (e : Enumeration α) (w : α → Nat)
    (A : α → α → Nat) (halt : α) (bound : Nat) (hb : 1 ≤ bound)
    (hw : ∀ i, w i ≤ bound) (hA : ∀ i j, A i j ≤ 9) :
    (SOnlyMachineWaterfallBP2.compile e w A halt).length ≤
      2 * ((2 * e.order.length + 1) * bound) + 2 +
      e.order.length * (18 * (2 * e.order.length + 1) + 2) +
      (2 * e.order.length + 1) + e.order.length * 4 + 2 := by
  let C := (SOnlyMachineWaterfallBP2.cells e).order.length
  have hi : (SOnlyMachineWaterfallBP2.initCode e w).length ≤ 2 * (C * bound) + 2 := by
    apply guarded_length_le
    intro c
    cases c with
    | value i => exact hw i
    | zero i => exact hb
    | marker => exact Nat.zero_le _
  have ht : (e.order.flatMap (SOnlyMachineWaterfallBP2.triggerCode e A halt)).length ≤
      e.order.length * (18 * C + 2) := by
    apply flatMap_length_le
    intro i hi
    have hg := guarded_length_le (SOnlyMachineWaterfallBP2.cells e)
      (SOnlyMachineWaterfallBP2.triggerWeight A halt i) (.zero i) 9 (by
        intro c
        cases c with
        | value j =>
          have ha := hA i j
          simp only [SOnlyMachineWaterfallBP2.triggerWeight]
          split <;> split <;> omega
        | zero j => simp [SOnlyMachineWaterfallBP2.triggerWeight]
        | marker => simp [SOnlyMachineWaterfallBP2.triggerWeight]; split <;> omega)
    have he : 2 * (C * 9) + 2 = 18 * C + 2 := by omega
    simpa only [SOnlyMachineWaterfallBP2.triggerCode, C, he] using hg
  have hs : (SOnlyMachineWaterfallBP2.sweep e).length ≤ C := by
    have h := unary_length_le (SOnlyMachineWaterfallBP2.cells e) SOnlyMachineWaterfallBP2.sweepWeight 1
      (by intro c; cases c <;> simp [SOnlyMachineWaterfallBP2.sweepWeight])
    simpa [SOnlyMachineWaterfallBP2.sweep, SOnlyMachineBP2.subMany, C] using h
  have hz : (e.order.flatMap SOnlyMachineWaterfallBP2.test).length ≤ e.order.length * 4 := by
    exact flatMap_length_le _ _ 4 (by intro i hi; simp [SOnlyMachineWaterfallBP2.test])
  have hc : C = 2 * e.order.length + 1 := cells_length e
  rw [hc] at hi ht hs
  simp only [SOnlyMachineWaterfallBP2.compile, SOnlyMachineWaterfallBP2.prologue,
    List.length_append, List.length_cons, List.length_nil]
  omega

def inputSum (input : Fin (d + 1) → Nat) : Nat := ((List.finRange (d + 1)).map input).sum

theorem input_le_sum (input : Fin (d + 1) → Nat) (i : Fin (d + 1)) : input i ≤ inputSum input :=
  member_le_sum _ input i (List.mem_finRange i)

def polynomialBound (d n sum : Nat) : Nat :=
  let k := helperCount d n
  let N := 4 * k + 1
  let C := 8 * k + 3
  2 * (C * (2 * sum + 9)) + 2 + N * (18 * C + 2) + C + N * 4 + 2

/-- Kernel-checked effective polynomial bound for the actual formal compiler,
with no source execution, halting premise, or finite testing assumption. -/
theorem compile_length_bound (M : SOnlyMachine.Machine d n) (input : Fin (d + 1) → Nat) :
    (SOnlyMachineNat.compile M input).length ≤ polynomialBound d n (inputSum input) := by
  have hn : ∀ c : SOnlyMachine.Cell d n,
      (SOnlyMachine.normal input : SOnlyMachine.Cell d n → Nat) c ≤ inputSum input := by
    intro c
    cases c with
    | data i => exact input_le_sum input i
    | I q => exact Nat.zero_le _
    | S q => exact Nat.zero_le _
    | F q => exact Nat.zero_le _
    | U q => exact Nat.zero_le _
    | V q => exact Nat.zero_le _
  have hw : ∀ c, SOnlyMachineClock.normalized (SOnlyMachine.encode M (SOnlyMachine.initial M input)) c + 5 ≤
      2 * inputSum input + 9 := by
    intro c
    cases c with
    | data i =>
      have := hn i
      simp only [SOnlyMachineClock.normalized, SOnlyMachine.encode, SOnlyMachine.initial]
      omega
    | recovery i => simp [SOnlyMachineClock.normalized] <;> omega
    | action a => simp only [SOnlyMachineClock.normalized]; split <;> omega
  have h := waterfall_length_bound (SOnlyMachineClock.clocks (SOnlyMachineFinite.machineCells d n))
    (fun c => SOnlyMachineClock.normalized (SOnlyMachine.encode M (SOnlyMachine.initial M input)) c + 5)
    (SOnlyMachineClock.row (SOnlyMachine.compile M)) (.action .halt) (2 * inputSum input + 9)
    (by omega) hw (row_le_nine _)
  have hc : 2 * (4 * helperCount d n + 1) + 1 = 8 * helperCount d n + 3 := by omega
  simpa only [SOnlyMachineNat.compile, SOnlyMachineNat.liftProgram, SOnlyMachineFinite.compile,
    SOnlyMachineFinite.renameProgram, List.length_map, SOnlyMachineFinite.typedProgram,
    SOnlyMachineClock.program, clocks_length, machineCells_length, polynomialBound, hc] using h

end SOnlyMachineBounds

#print axioms SOnlyMachineBounds.compile_length_bound
