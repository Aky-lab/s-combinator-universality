import SOnlyCounter

/-!
# Arbitrary-length UT19 memory blocks

This proves the local literal-production layer of the running-XOR memory
argument uniformly in the list of cells. True alignment means take (the
written proof's alignment 0); false means skip (alignment 1). Exterior Parity
and Reset alignments remain explicit hypotheses.

The normal update, reset, width observation and halt-marker word are proved
from the actual UT19 table. The temporal power-of-two observation/inversion
and disturbance-delay theorem is a separate algebraic obligation.
-/

namespace SOnlyMemory

open SOnlySource SOnlyCounter

set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

/-- A cell consists of its dynamic bit and fixed post-cell inverter bit. -/
abbrev Cell := Bool × Bool

def cellWord (h : Bool) : List Symbol := if h then [5, 4, 18] else [4, 5]

def inverter : List Symbol := [0, 0, 18]

def component (h a : Bool) : List Symbol :=
  cellWord h ++ if a then inverter else []

def memory (cells : List Cell) : List Symbol :=
  cells.flatMap (fun c => component c.1 c.2)

/-- Incoming take alignment after this original component has been consumed. -/
def nextAlignment (q h a : Bool) : Bool := Bool.xor q (Bool.xor h a)

def updatedDynamic (q h : Bool) : Bool := Bool.xor h (!q)

/-- Only dynamic state changes; the original widths determine each next alignment. -/
def normalUpdate (q : Bool) : List Cell → List Cell
  | [] => []
  | (h, a) :: tail => (updatedDynamic q h, a) :: normalUpdate (nextAlignment q h a) tail

def reset (cells : List Cell) : List Cell := cells.map (fun c => (false, c.2))

/-- The Reset word of a cell and optional inverter under odd Parity. -/
def markerComponent (a : Bool) : List Symbol :=
  [17, 9] ++ if a then [17, 3] else []

def markerWord (cells : List Cell) : List Symbol :=
  cells.flatMap (fun c => markerComponent c.2)

@[simp] theorem memory_nil : memory [] = [] := rfl
@[simp] theorem memory_cons (h a : Bool) (tail : List Cell) :
    memory ((h, a) :: tail) = component h a ++ memory tail := rfl

/-- Eight finite parity cases, separate from the arbitrary-length induction. -/
theorem component_phase : ∀ h a q : Bool,
    phaseAfter (component h a).length q = nextAlignment q h a := by decide +kernel

theorem command_phase_stable : ∀ h a q p : Bool,
    phaseAfter (pass q (component h a)).length p = p := by decide +kernel

theorem parity_phase_stable : ∀ h a q p r : Bool,
    phaseAfter (pass p (pass q (component h a))).length r = r := by decide +kernel

theorem component_normal : ∀ h a q : Bool,
    halfcommand q true true (component h a) = component (updatedDynamic q h) a := by decide +kernel

theorem component_reset : ∀ h a q p : Bool,
    halfcommand q p false (component h a) = component false a := by decide +kernel

theorem component_marker : ∀ h a q : Bool,
    pass false (pass q (component h a)) = markerComponent a := by decide +kernel

/-- Component concatenation retains the supplied Parity/Reset alignment because
both intervening component lengths are even. -/
theorem halfcommand_component (h a q p r : Bool) (tail : List Symbol) :
    halfcommand q p r (component h a ++ tail) =
      halfcommand q p r (component h a) ++
        halfcommand (nextAlignment q h a) p r tail := by
  simp only [halfcommand, pass_append, component_phase,
    command_phase_stable, parity_phase_stable]

/-- Exact normal-continuation semantics for every finite block and forcing bit. -/
theorem memory_normal (cells : List Cell) (q : Bool) :
    halfcommand q true true (memory cells) = memory (normalUpdate q cells) := by
  induction cells generalizing q with
  | nil => simp [halfcommand, normalUpdate, pass]
  | cons c tail ih =>
    obtain ⟨h, a⟩ := c
    rw [memory_cons, halfcommand_component, component_normal, ih]
    rfl

/-- Odd Reset restores every dynamic bit to zero; Parity may have either alignment. -/
theorem memory_reset (cells : List Cell) (q p : Bool) :
    halfcommand q p false (memory cells) = memory (reset cells) := by
  induction cells generalizing q with
  | nil => simp [halfcommand, reset, pass]
  | cons c tail ih =>
    obtain ⟨h, a⟩ := c
    rw [memory_cons, halfcommand_component, component_reset, ih]
    rfl

/-- Under odd Parity, every cell's Reset pair begins with published symbol 18. -/
theorem memory_marker (cells : List Cell) (q : Bool) :
    pass false (pass q (memory cells)) = markerWord cells := by
  induction cells generalizing q with
  | nil => simp [pass, markerWord]
  | cons c tail ih =>
    obtain ⟨h, a⟩ := c
    rw [memory_cons, pass_append, pass_append, component_phase,
      command_phase_stable, component_marker, ih]
    rfl

/-- With even Reset a nonempty odd-Parity block signals immediately, before its
first Reset transition. With odd Reset the identical leading 18 is skipped. -/
theorem marker_event (cells : List Cell) (hne : cells ≠ []) (take : Bool) :
    Selected ⟨markerWord cells, take⟩ ↔ take = true := by
  cases cells with
  | nil => exact False.elim (hne rfl)
  | cons c tail => simp [Selected, markerWord, markerComponent]

/-- Fixed inverter placement is unchanged by normal continuation. -/
theorem normal_fixed (cells : List Cell) (q : Bool) :
    (normalUpdate q cells).map Prod.snd = cells.map Prod.snd := by
  induction cells generalizing q with
  | nil => rfl
  | cons c tail ih =>
    obtain ⟨h, a⟩ := c
    simp only [normalUpdate, List.map_cons, ih]

/-- Combined cell width parities. -/
def combined (cells : List Cell) : List Bool :=
  cells.map (fun c => Bool.xor c.1 c.2)

/-- Inclusive prefix XOR, forced by the incoming skip-alignment bit. -/
def runningXor (g : Bool) : List Bool → List Bool
  | [] => []
  | c :: tail => let next := Bool.xor g c; next :: runningXor next tail

private theorem update_combined : ∀ q h a : Bool,
    Bool.xor (updatedDynamic q h) a = Bool.xor (!q) (Bool.xor h a) := by decide

private theorem next_skip : ∀ q h a : Bool,
    (!nextAlignment q h a) = Bool.xor (!q) (Bool.xor h a) := by decide

/-- The actual tag block realizes c'_i = g XOR XOR_(j≤i) c_j, at any width. -/
theorem memory_running_xor (cells : List Cell) (q : Bool) :
    combined (normalUpdate q cells) = runningXor (!q) (combined cells) := by
  induction cells generalizing q with
  | nil => rfl
  | cons c tail ih =>
    obtain ⟨h, a⟩ := c
    simp only [combined, normalUpdate, List.map_cons, updatedDynamic, runningXor]
    change Bool.xor (updatedDynamic q h) a :: combined (normalUpdate (nextAlignment q h a) tail) = _
    rw [update_combined, ih, next_skip]
    rfl

/-- Reset restores precisely the fixed initializer vector, independent of forcing. -/
theorem memory_reset_vector (cells : List Cell) :
    combined (reset cells) = cells.map Prod.snd := by
  induction cells with
  | nil => rfl
  | cons c tail ih =>
    obtain ⟨h, a⟩ := c
    simp [combined, reset]

/-- Current output parity, before the next memory update. -/
def widthParity (cells : List Cell) : Bool := (combined cells).foldr Bool.xor false

theorem component_width : ∀ h a : Bool,
    (component h a).length % 2 = if Bool.xor h a then 1 else 0 := by decide +kernel

/-- The output consumed by surrounding counters is XOR of current combined bits. -/
theorem memory_width (cells : List Cell) :
    (memory cells).length % 2 = if widthParity cells then 1 else 0 := by
  induction cells with
  | nil => rfl
  | cons c tail ih =>
    obtain ⟨h, a⟩ := c
    rw [memory_cons, List.length_append, Nat.add_mod, component_width, ih]
    change ((if Bool.xor h a then 1 else 0) + (if widthParity tail then 1 else 0)) % 2 =
      if Bool.xor (Bool.xor h a) (widthParity tail) then 1 else 0
    cases Bool.xor h a <;> cases widthParity tail <;> rfl

/-- Scan only selected original positions for the halt marker. -/
def safePass (take : Bool) : List Symbol → Bool
  | [] => true
  | symbol :: tail => ((!take) || decide (symbol ≠ (⟨17, by decide⟩ : Symbol))) && safePass (!take) tail

theorem safePass_cons (symbol : Symbol) (tail : List Symbol) (q : Bool) :
    safePass q (symbol :: tail) = true ↔
      (q = true → symbol ≠ (⟨17, by decide⟩ : Symbol)) ∧ safePass (!q) tail = true := by
  cases q <;> simp [safePass]

theorem safePass_append (front tail : List Symbol) (q : Bool) :
    safePass q (front ++ tail) =
      (safePass q front && safePass (phaseAfter front.length q) tail) := by
  induction front generalizing q with
  | nil => simp [safePass, phaseAfter]
  | cons a as ih => simp [safePass, phaseAfter, ih, Bool.and_assoc]

/-- Structural pass safety excludes an event at every actual source prestate
while the original word is consumed, even with arbitrary trailing/generated data. -/
theorem safe_prefix_no_event (front suffix : List Symbol) (q : Bool) (time : Nat)
    (hsafe : safePass q front = true) (htime : time < front.length) :
    ¬Selected (iterate time ⟨front ++ suffix, q⟩) := by
  induction front generalizing suffix q time with
  | nil => simp at htime
  | cons a as ih =>
    obtain ⟨ha, hrest⟩ := (safePass_cons a as q).mp hsafe
    cases time with
    | zero =>
      rintro ⟨hq, hhead⟩
      exact ha hq (Option.some.inj hhead)
    | succ time =>
      have htime' : time < as.length := by simpa using htime
      have h := ih (suffix ++ if q then production a else []) (!q) time hrest htime'
      rw [show time + 1 = time + 1 from rfl, SOnlyCounter.iterate_add]
      change ¬Selected (iterate time ⟨(as ++ suffix) ++ (if q then production a else []), !q⟩)
      rw [List.append_assoc]
      exact h

theorem component_command_safe : ∀ h a q : Bool,
    safePass q (component h a) = true := by decide +kernel

theorem component_parity_safe : ∀ h a q p : Bool,
    safePass p (pass q (component h a)) = true := by decide +kernel

theorem component_reset_safe : ∀ h a q p r : Bool,
    (p = true ∨ r = false) → safePass r (pass p (pass q (component h a))) = true := by decide +kernel

/-- Every Command position of any memory block is free of selected 18. -/
theorem memory_command_safe (cells : List Cell) (q : Bool) :
    safePass q (memory cells) = true := by
  induction cells generalizing q with
  | nil => rfl
  | cons c tail ih =>
    obtain ⟨h, a⟩ := c
    rw [memory_cons, safePass_append, component_phase, component_command_safe, ih]
    rfl

/-- Every Parity position is free of selected 18, under either exterior phase. -/
theorem memory_parity_safe (cells : List Cell) (q p : Bool) :
    safePass p (pass q (memory cells)) = true := by
  induction cells generalizing q with
  | nil => rfl
  | cons c tail ih =>
    obtain ⟨h, a⟩ := c
    rw [memory_cons, pass_append, safePass_append, component_phase,
      command_phase_stable, component_parity_safe, ih]
    rfl

/-- Normal Reset and either legal odd Reset are event-free at every position. -/
theorem memory_reset_safe (cells : List Cell) (q p r : Bool) (legal : p = true ∨ r = false) :
    safePass r (pass p (pass q (memory cells))) = true := by
  induction cells generalizing q with
  | nil => rfl
  | cons c tail ih =>
    obtain ⟨h, a⟩ := c
    rw [memory_cons, pass_append, pass_append, safePass_append, component_phase,
      command_phase_stable, parity_phase_stable, component_reset_safe h a q p r legal, ih]
    rfl

/-- Count cells plus their optional fixed inverters. -/
def componentCount (cells : List Cell) : Nat :=
  (cells.map (fun c => 1 + if c.2 then 1 else 0)).sum

theorem command_component_length : ∀ h a q : Bool,
    (pass q (component h a)).length = 2 * (1 + if a then 1 else 0) := by decide +kernel

theorem parity_component_length : ∀ h a q p : Bool,
    (pass p (pass q (component h a))).length = 2 * (1 + if a then 1 else 0) := by decide +kernel

/-- Every cell and inverter produces exactly a two-symbol Parity component. -/
theorem memory_command_length (cells : List Cell) (q : Bool) :
    (pass q (memory cells)).length = 2 * componentCount cells := by
  induction cells generalizing q with
  | nil => rfl
  | cons c tail ih =>
    obtain ⟨h, a⟩ := c
    rw [memory_cons, pass_append, component_phase, List.length_append,
      command_component_length, ih]
    simp only [componentCount, List.map_cons, List.sum_cons, Nat.mul_add]

/-- Every cell and inverter also produces exactly a two-symbol Reset component. -/
theorem memory_parity_length (cells : List Cell) (q p : Bool) :
    (pass p (pass q (memory cells))).length = 2 * componentCount cells := by
  induction cells generalizing q with
  | nil => rfl
  | cons c tail ih =>
    obtain ⟨h, a⟩ := c
    rw [memory_cons, pass_append, pass_append, component_phase, command_phase_stable,
      List.length_append, parity_component_length, ih]
    simp only [componentCount, List.map_cons, List.sum_cons, Nat.mul_add]

/-- Nonempty blocks have at least one cell, regardless of inverter placement. -/
theorem componentCount_positive (cells : List Cell) (hne : cells ≠ []) :
    0 < componentCount cells := by
  cases cells with
  | nil => exact False.elim (hne rfl)
  | cons c tail =>
    simp only [componentCount, List.map_cons, List.sum_cons]
    omega

theorem intermediate_words_nonempty (cells : List Cell) (q p : Bool) (hne : cells ≠ []) :
    pass q (memory cells) ≠ [] ∧ pass p (pass q (memory cells)) ≠ [] := by
  have hpositive := componentCount_positive cells hne
  constructor
  · intro h
    have hlen := congrArg List.length h
    rw [memory_command_length] at hlen
    simp only [List.length_nil] at hlen
    omega
  · intro h
    have hlen := congrArg List.length h
    rw [memory_parity_length] at hlen
    simp only [List.length_nil] at hlen
    omega

end SOnlyMemory

#print axioms SOnlyMemory.memory_normal
#print axioms SOnlyMemory.memory_reset
#print axioms SOnlyMemory.memory_marker
#print axioms SOnlyMemory.marker_event
#print axioms SOnlyMemory.normal_fixed
#print axioms SOnlyMemory.memory_running_xor
#print axioms SOnlyMemory.memory_reset_vector
#print axioms SOnlyMemory.memory_width

#print axioms SOnlyMemory.safe_prefix_no_event
#print axioms SOnlyMemory.memory_command_safe
#print axioms SOnlyMemory.memory_parity_safe
#print axioms SOnlyMemory.memory_reset_safe
#print axioms SOnlyMemory.memory_command_length
#print axioms SOnlyMemory.memory_parity_length
#print axioms SOnlyMemory.intermediate_words_nonempty
