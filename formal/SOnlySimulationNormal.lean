import SOnlySimulation

namespace SOnlySimulation

open SOnlySource SOnlyCounter SOnlyMemory SOnlyTemporalMemory

set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

/-- Exactly the counter operations whose Parity word is even. Positive
ordinary decrements are deliberately distinguished from exponent-zero ones. -/
inductive NormalAction where
  | inc (n : Nat)
  | dec (n : Nat)
  | shield (n : Nat) (take : Bool)

def NormalAction.take : NormalAction → Bool
  | .inc _ => true
  | .dec _ => false
  | .shield _ q => q

def NormalAction.input : NormalAction → Piece
  | .inc n => .count n
  | .dec n => .count (n + 1)
  | .shield n _ => .protect n

def NormalAction.output : NormalAction → Piece
  | .inc n => .count (n + 1)
  | .dec n => .count n
  | .shield n _ => .count (n + 1)

@[simp] theorem NormalAction.input_even (a : NormalAction) (q : Bool) :
    phaseAfter a.input.word.length q = q := by
  cases a <;> simp only [NormalAction.input, Piece.word, ordinary_phase, protected_phase]

@[simp] theorem NormalAction.command_even (a : NormalAction) (p : Bool) :
    phaseAfter (pass a.take a.input.word).length p = p := by
  cases a <;> simp [NormalAction.take, NormalAction.input, Piece.word,
    increment_command, decrement_command, protected_command]

@[simp] theorem NormalAction.parity_even (a : NormalAction) (p r : Bool) :
    phaseAfter (pass p (pass a.take a.input.word)).length r = r := by
  cases a with
  | inc n => exact phaseAfter_of_even _ (reset_word_even n true p) r
  | dec n => exact phaseAfter_of_even _ (reset_word_even (n+1) false p) r
  | shield n q => exact phaseAfter_of_even _ (protected_reset_even n q p) r

@[simp] theorem NormalAction.update (a : NormalAction) :
    halfcommand a.take true true a.input.word = a.output.word := by
  cases a with
  | inc n => exact increment n true true
  | dec n => exact decrement_even_reset n true
  | shield n q => exact protected_increment n q true true

/-- A memory block is followed by one counter, retaining actual FIFO order. -/
abbrev NormalRow := List Cell × NormalAction

def rowsPieces : List NormalRow → List Cell → List Piece
  | [], last => [.mem last]
  | (cells, action) :: rows, last => .mem cells :: action.input :: rowsPieces rows last

def rowsWord (rows : List NormalRow) (last : List Cell) : List Symbol :=
  assemble (rowsPieces rows last)

@[simp] theorem rowsWord_nil (last : List Cell) : rowsWord [] last = memory last := by
  simp [rowsWord, rowsPieces, assemble, Piece.word]

@[simp] theorem rowsWord_cons (cells : List Cell) (a : NormalAction)
    (rows : List NormalRow) (last : List Cell) :
    rowsWord ((cells, a) :: rows) last = memory cells ++ (a.input.word ++ rowsWord rows last) := by
  simp [rowsWord, rowsPieces, assemble, Piece.word]

/-- The width differences telescope from current Command phase to every desired
counter action and finally to the chosen global Parity phase. -/
def Fits : Bool → Bool → List NormalRow → List Cell → Prop
  | q, p, [], last => widthParity last = Bool.xor q p
  | q, p, (cells, a) :: rows, last =>
      widthParity cells = Bool.xor q a.take ∧ Fits a.take p rows last

private theorem xor_cancel_left (q a : Bool) : Bool.xor q (Bool.xor q a) = a := by
  cases q <;> cases a <;> rfl

/-- Width specifications determine the actual counter alignment, not just a
separate abstract schedule. -/
theorem fits_counter_phase (cells : List Cell) (q a : Bool)
    (h : widthParity cells = Bool.xor q a) :
    phaseAfter (memory cells).length q = a := by
  rw [memory_next_phase, h, xor_cancel_left]

/-- Global phase uses lengths of consumed words, as required by the FIFO machine. -/
theorem fits_global_phase (rows : List NormalRow) (last : List Cell) (q p : Bool)
    (fits : Fits q p rows last) : phaseAfter (rowsWord rows last).length q = p := by
  induction rows generalizing q with
  | nil => simpa using fits_counter_phase last q p fits
  | cons row rows ih =>
    obtain ⟨cells, a⟩ := row
    obtain ⟨hfirst, hrest⟩ := fits
    rw [rowsWord_cons, List.length_append, phaseAfter_add,
      List.length_append, phaseAfter_add, fits_counter_phase cells q a.take hfirst,
      NormalAction.input_even]
    exact ih a.take hrest

/-- All normal-action Parity words are even, so no intermediate component can
change the Parity alignment. -/
theorem normal_command_phase (rows : List NormalRow) (last : List Cell) (q p r : Bool)
    (fits : Fits q p rows last) :
    phaseAfter (pass q (rowsWord rows last)).length r = r := by
  induction rows generalizing q with
  | nil => simp
  | cons row rows ih =>
    obtain ⟨cells, a⟩ := row
    obtain ⟨hfirst, hrest⟩ := fits
    rw [rowsWord_cons, pass_append, fits_counter_phase cells q a.take hfirst,
      pass_append, NormalAction.input_even, List.length_append, phaseAfter_add,
      memory_command_phase, List.length_append, phaseAfter_add, NormalAction.command_even]
    exact ih a.take hrest

/-- Exact following Command word after every cell and counter has updated. -/
def normalOutput : Bool → List NormalRow → List Cell → List Piece
  | q, [], last => [.mem (normalUpdate q last)]
  | q, (cells, a) :: rows, last =>
      .mem (normalUpdate q cells) :: a.output :: normalOutput a.take rows last

/-- The three-pass update is proved on the fully assembled literal word. -/
theorem normal_halfcommand (rows : List NormalRow) (last : List Cell) (q : Bool)
    (fits : Fits q true rows last) :
    halfcommand q true true (rowsWord rows last) = assemble (normalOutput q rows last) := by
  induction rows generalizing q with
  | nil => simpa [normalOutput, assemble, Piece.word] using memory_normal last q
  | cons row rows ih =>
    obtain ⟨cells, a⟩ := row
    obtain ⟨hfirst, hrest⟩ := fits
    rw [rowsWord_cons]
    simp only [halfcommand, pass_append, memory_command_phase, memory_parity_phase,
      fits_counter_phase cells q a.take hfirst, NormalAction.input_even,
      NormalAction.command_even, NormalAction.parity_even]
    change halfcommand q true true (memory cells) ++
      (halfcommand a.take true true a.input.word ++
        halfcommand a.take true true (rowsWord rows last)) = _
    rw [memory_normal, NormalAction.update, ih a.take hrest]
    rfl

/-- Every Reset position of a normal halfcommand is event-free. -/
theorem normal_reset_safe (rows : List NormalRow) (last : List Cell) (q : Bool)
    (fits : Fits q true rows last) :
    safePass true (pass true (pass q (rowsWord rows last))) = true := by
  induction rows generalizing q with
  | nil => simpa using memory_reset_safe last q true true (Or.inl rfl)
  | cons row rows ih =>
    obtain ⟨cells, a⟩ := row
    obtain ⟨hfirst, hrest⟩ := fits
    rw [rowsWord_cons]
    simp only [pass_append, memory_command_phase,
      fits_counter_phase cells q a.take hfirst, NormalAction.input_even]
    rw [NormalAction.command_even, safePass_append, memory_parity_phase,
      safePass_append, NormalAction.parity_even, ih a.take hrest,
      memory_reset_safe cells q true true (Or.inl rfl), Bool.true_and, Bool.and_true]
    apply counter_safe
    apply pass_counter_word
    apply pass_counter_word
    cases a <;> first | exact ordinary_counter_word _ | exact protected_counter_word _

/-- Nonempty first memory guarantees all three whole-queue pass entrances. -/
theorem memory_prefix_nonempty (cells : List Cell) (tail : List Symbol) (q p : Bool)
    (hne : cells ≠ []) :
    memory cells ++ tail ≠ [] ∧ pass q (memory cells ++ tail) ≠ [] ∧
      pass p (pass q (memory cells ++ tail)) ≠ [] := by
  have hm : memory cells ≠ [] := by
    cases cells with
    | nil => contradiction
    | cons c cs => cases c with | mk h a => cases h <;> simp [memory, component, cellWord]
  have hi := intermediate_words_nonempty cells q p hne
  rw [pass_append, pass_append]
  exact ⟨List.append_ne_nil_of_left_ne_nil hm _, List.append_ne_nil_of_left_ne_nil hi.1 _,
    List.append_ne_nil_of_left_ne_nil hi.2 _⟩

/-- Actual safe finite execution of a normal global halfcommand. This includes
arbitrary positive decrements and protected-counter normalization. -/
theorem normal_run (cells : List Cell) (a : NormalAction) (rows : List NormalRow)
    (last : List Cell) (q : Bool) (hne : cells ≠ [])
    (fits : Fits q true ((cells, a) :: rows) last) :
    SafeRun ⟨rowsWord ((cells, a) :: rows) last, q⟩
      ⟨assemble (normalOutput q ((cells, a) :: rows) last), true⟩ := by
  let word := rowsWord ((cells, a) :: rows) last
  have hne' : word ≠ [] ∧ pass q word ≠ [] ∧ pass true (pass q word) ≠ [] := by
    simpa only [word, rowsWord_cons, List.append_assoc] using
      memory_prefix_nonempty cells (a.input.word ++ rowsWord rows last) q true hne
  have h1 := safe_pass_run word q hne'.1 (assembled_command_safe (rowsPieces _ last) q)
  rw [fits_global_phase _ _ q true fits] at h1
  have h2 := safe_pass_run (pass q word) true hne'.2.1
    (assembled_parity_safe (rowsPieces _ last) q true)
  rw [normal_command_phase _ _ q true true fits] at h2
  have h3 := safe_pass_run (pass true (pass q word)) true hne'.2.2
    (normal_reset_safe _ _ q fits)
  have heven : (pass true (pass q word)).length % 2 = 0 :=
    assembled_reset_even (rowsPieces ((cells, a) :: rows) last) q true
  rw [phaseAfter_of_even _ heven true] at h3
  have h := h1.trans (h2.trans h3)
  change SafeRun _ ⟨halfcommand q true true word, true⟩ at h
  simpa only [word, normal_halfcommand _ _ q fits] using h

end SOnlySimulation

#print axioms SOnlySimulation.fits_global_phase
#print axioms SOnlySimulation.normal_halfcommand
#print axioms SOnlySimulation.normal_run
