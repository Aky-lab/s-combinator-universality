import Std

/-!
A direct, exact bridge from deterministic two-way tapes to two finite stacks.
The source tape is an arbitrary function `Int → Fin symbols`, with a separate
integer head position. The target stores only the finite state and scanned
symbol in control, plus two finite lists, nearest cell first. No bound on a
computation or visited tape interval is assumed.
-/
namespace SOnlyTapeStacks

inductive Direction where
  | left | stay | right
  deriving DecidableEq, Repr

structure Action (states symbols : Nat) where
  next : Fin states
  write : Fin symbols
  move : Direction
  deriving DecidableEq, Repr

structure Machine (states symbols : Nat) where
  start : Fin states
  blank : Fin symbols
  transition : Fin states → Fin symbols → Option (Action states symbols)

structure TapeConfig (states symbols : Nat) where
  state : Fin states
  position : Int
  cells : Int → Fin symbols

structure StackConfig (states symbols : Nat) where
  state : Fin states
  scanned : Fin symbols
  left : List (Fin symbols)
  right : List (Fin symbols)
  deriving DecidableEq, Repr

/-- Infinite blank extension of a finite, nearest-cell-first stack. -/
def ray (blank : α) : List α → Nat → α
  | [], _ => blank
  | x :: _, 0 => x
  | _ :: xs, n + 1 => ray blank xs n

@[simp] theorem ray_nil (blank : α) (n : Nat) : ray blank [] n = blank := rfl
@[simp] theorem ray_cons_zero (blank x : α) (xs : List α) :
    ray blank (x :: xs) 0 = x := rfl
@[simp] theorem ray_cons_succ (blank x : α) (xs : List α) (n : Nat) :
    ray blank (x :: xs) (n + 1) = ray blank xs n := rfl
@[simp] theorem ray_tail (blank : α) (xs : List α) (n : Nat) :
    ray blank xs.tail n = ray blank xs (n + 1) := by
  cases xs <;> rfl

/-- Ordinary functional update of one cell of a bi-infinite tape. -/
def writeAt (cells : Int → α) (position : Int) (value : α) : Int → α :=
  fun i => if i = position then value else cells i

@[simp] theorem writeAt_same (cells : Int → α) (p : Int) (v : α) :
    writeAt cells p v p = v := by simp [writeAt]

theorem writeAt_other (cells : Int → α) (p i : Int) (v : α) (h : i ≠ p) :
    writeAt cells p v i = cells i := by simp [writeAt, h]

def displacement : Direction → Int
  | .left => -1
  | .stay => 0
  | .right => 1

/-- Write the current tape cell, change state, and move the absolute head. -/
def applyTape (a : Action states symbols) (c : TapeConfig states symbols) :
    TapeConfig states symbols :=
  ⟨a.next, c.position + displacement a.move, writeAt c.cells c.position a.write⟩

/-- Write the head symbol, then push that symbol and pop the opposite stack. -/
def applyStacks (blank : Fin symbols) (a : Action states symbols)
    (s : StackConfig states symbols) : StackConfig states symbols :=
  match a.move with
  | .left => ⟨a.next, ray blank s.left 0, s.left.tail, a.write :: s.right⟩
  | .stay => ⟨a.next, a.write, s.left, s.right⟩
  | .right => ⟨a.next, ray blank s.right 0, a.write :: s.left, s.right.tail⟩

/-- Equality of every observable cell, not just of the visited tape window. -/
structure Represents (blank : Fin symbols) (c : TapeConfig states symbols)
    (s : StackConfig states symbols) : Prop where
  state : c.state = s.state
  scanned : c.cells c.position = s.scanned
  left : ∀ n : Nat, c.cells (c.position - ((n : Int) + 1)) = ray blank s.left n
  right : ∀ n : Nat, c.cells (c.position + ((n : Int) + 1)) = ray blank s.right n

/-- Read a relative integer tape coordinate from the finite stack representation. -/
def readStacks (blank : Fin symbols) (s : StackConfig states symbols) :
    Int → Fin symbols
  | .ofNat 0 => s.scanned
  | .ofNat (n + 1) => ray blank s.right n
  | .negSucc n => ray blank s.left n

/-- The representation determines every cell of the entire bi-infinite tape. -/
theorem represents_read (blank : Fin symbols)
    (c : TapeConfig states symbols) (s : StackConfig states symbols)
    (h : Represents blank c s) (i : Int) :
    c.cells i = readStacks blank s (i - c.position) := by
  cases he : i - c.position with
  | ofNat n =>
    cases n with
    | zero =>
      have hi : i = c.position := by
        simp only [Int.ofNat_eq_natCast] at he
        omega
      change c.cells i = s.scanned
      rw [hi]
      exact h.scanned
    | succ n =>
      have hi : i = c.position + ((n : Int) + 1) := by
        simp only [Int.ofNat_eq_natCast] at he
        omega
      change c.cells i = ray blank s.right n
      rw [hi]
      exact h.right n
  | negSucc n =>
    have hi : i = c.position - ((n : Int) + 1) := by omega
    change c.cells i = ray blank s.left n
    rw [hi]
    exact h.left n

/-- The exact single-transition theorem, including empty stacks. -/
theorem apply_represents (blank : Fin symbols) (a : Action states symbols)
    (c : TapeConfig states symbols) (s : StackConfig states symbols)
    (h : Represents blank c s) :
    Represents blank (applyTape a c) (applyStacks blank a s) := by
  cases hm : a.move with
  | stay =>
    constructor
    · simp [applyTape, applyStacks, hm]
    · simp [applyTape, applyStacks, hm, displacement]
    · intro n
      simp only [applyTape, applyStacks, hm, displacement, Int.add_zero]
      rw [writeAt_other _ _ _ _ (by omega)]
      exact h.left n
    · intro n
      simp only [applyTape, applyStacks, hm, displacement, Int.add_zero]
      rw [writeAt_other _ _ _ _ (by omega)]
      exact h.right n
  | left =>
    constructor
    · simp [applyTape, applyStacks, hm]
    · simp only [applyTape, applyStacks, hm, displacement]
      rw [writeAt_other _ _ _ _ (by omega)]
      have he : c.position + -1 = c.position - ((0 : Int) + 1) := by omega
      rw [he]
      exact h.left 0
    · intro n
      simp only [applyTape, applyStacks, hm, displacement, ray_tail]
      rw [writeAt_other _ _ _ _ (by omega)]
      have he : c.position + -1 - ((n : Int) + 1) =
          c.position - (((n + 1 : Nat) : Int) + 1) := by omega
      rw [he]
      exact h.left (n + 1)
    · intro n
      cases n with
      | zero =>
        have he : c.position + -1 + 1 = c.position := by omega
        simp [applyTape, applyStacks, hm, displacement, writeAt, he]
      | succ n =>
        simp only [applyTape, applyStacks, hm, displacement, ray_cons_succ]
        rw [writeAt_other _ _ _ _ (by omega)]
        have he : c.position + -1 + (((n + 1 : Nat) : Int) + 1) =
            c.position + ((n : Int) + 1) := by omega
        rw [he]
        exact h.right n
  | right =>
    constructor
    · simp [applyTape, applyStacks, hm]
    · simp only [applyTape, applyStacks, hm, displacement]
      rw [writeAt_other _ _ _ _ (by omega)]
      simpa using h.right 0
    · intro n
      cases n with
      | zero => simp [applyTape, applyStacks, hm, displacement, writeAt]
      | succ n =>
        simp only [applyTape, applyStacks, hm, displacement, ray_cons_succ]
        rw [writeAt_other _ _ _ _ (by omega)]
        have he : c.position + 1 - (((n + 1 : Nat) : Int) + 1) =
            c.position - ((n : Int) + 1) := by omega
        rw [he]
        exact h.left n
    · intro n
      simp only [applyTape, applyStacks, hm, displacement, ray_tail]
      rw [writeAt_other _ _ _ _ (by omega)]
      have he : c.position + 1 + ((n : Int) + 1) =
          c.position + (((n + 1 : Nat) : Int) + 1) := by omega
      rw [he]
      exact h.right (n + 1)

def tapeStep (m : Machine states symbols) (c : TapeConfig states symbols) :
    Option (TapeConfig states symbols) :=
  (m.transition c.state (c.cells c.position)).map (fun a => applyTape a c)

def stackStep (m : Machine states symbols) (s : StackConfig states symbols) :
    Option (StackConfig states symbols) :=
  (m.transition s.state s.scanned).map (fun a => applyStacks m.blank a s)

/-- Lifting a relation also requires that failure/termination agrees exactly. -/
def OptionRelated (R : α → β → Prop) : Option α → Option β → Prop
  | none, none => True
  | some a, some b => R a b
  | _, _ => False

/-- One stack transition exists exactly when one tape transition exists. -/
theorem step_represents (m : Machine states symbols)
    (c : TapeConfig states symbols) (s : StackConfig states symbols)
    (h : Represents m.blank c s) :
    OptionRelated (Represents m.blank) (tapeStep m c) (stackStep m s) := by
  simp only [tapeStep, stackStep, h.state, h.scanned]
  cases m.transition s.state s.scanned with
  | none => trivial
  | some a => exact apply_represents m.blank a c s h

/-- Run exactly n actual transitions; none means termination occurred earlier. -/
def run (step : α → Option α) : Nat → α → Option α
  | 0, c => some c
  | n + 1, c => (step c).bind (run step n)

/-- Every finite run is represented, without a time or tape-space bound. -/
theorem run_represents (m : Machine states symbols) (n : Nat)
    (c : TapeConfig states symbols) (s : StackConfig states symbols)
    (h : Represents m.blank c s) :
    OptionRelated (Represents m.blank) (run (tapeStep m) n c)
      (run (stackStep m) n s) := by
  induction n generalizing c s with
  | zero => exact h
  | succ n ih =>
    have hs := step_represents m c s h
    cases hc : tapeStep m c <;> cases ht : stackStep m s <;>
      simp_all only [run, Option.bind_none, Option.bind_some, OptionRelated]

/-- A finite input word starts at absolute tape coordinate zero. -/
def inputCells (blank : Fin symbols) (input : List (Fin symbols)) :
    Int → Fin symbols
  | .ofNat n => ray blank input n
  | .negSucc _ => blank

def tapeInput (m : Machine states symbols) (input : List (Fin symbols)) :
    TapeConfig states symbols := ⟨m.start, 0, inputCells m.blank input⟩

def stackInput (m : Machine states symbols) (input : List (Fin symbols)) :
    StackConfig states symbols :=
  ⟨m.start, ray m.blank input 0, [], input.tail⟩

/-- All finite words, including the empty word, have the required representation. -/
theorem input_represents (m : Machine states symbols) (input : List (Fin symbols)) :
    Represents m.blank (tapeInput m input) (stackInput m input) := by
  constructor
  · rfl
  · rfl
  · intro n
    change inputCells m.blank input (0 - ((n : Int) + 1)) = m.blank
    have he : 0 - ((n : Int) + 1) = Int.negSucc n := by omega
    rw [he]
    rfl
  · intro n
    change inputCells m.blank input (0 + ((n : Int) + 1)) = ray m.blank input.tail n
    have he : 0 + ((n : Int) + 1) = Int.ofNat (n + 1) := by
      simp only [Int.ofNat_eq_natCast]
      omega
    rw [he]
    simp [inputCells]

/-- End-to-end arbitrary-input, arbitrary-finite-time tape-to-stack simulation. -/
theorem input_run_represents (m : Machine states symbols)
    (input : List (Fin symbols)) (n : Nat) :
    OptionRelated (Represents m.blank)
      (run (tapeStep m) n (tapeInput m input))
      (run (stackStep m) n (stackInput m input)) :=
  run_represents m n _ _ (input_represents m input)

/-- Termination is preserved and reflected at a represented boundary. -/
theorem optionRelated_none_iff {R : α → β → Prop} {x : Option α} {y : Option β}
    (h : OptionRelated R x y) : x = none ↔ y = none := by
  cases x <;> cases y <;> simp_all [OptionRelated]

theorem step_none_iff (m : Machine states symbols)
    (c : TapeConfig states symbols) (s : StackConfig states symbols)
    (h : Represents m.blank c s) :
    tapeStep m c = none ↔ stackStep m s = none :=
  optionRelated_none_iff (step_represents m c s h)

theorem run_none_iff (m : Machine states symbols) (n : Nat)
    (c : TapeConfig states symbols) (s : StackConfig states symbols)
    (h : Represents m.blank c s) :
    run (tapeStep m) n c = none ↔ run (stackStep m) n s = none :=
  optionRelated_none_iff (run_represents m n c s h)

/-- The source/target halts after exactly n transitions, including n = 0. -/
def HaltsAfter (step : α → Option α) (n : Nat) (c : α) : Prop :=
  ∃ d, run step n c = some d ∧ step d = none

theorem haltsAfter_iff (m : Machine states symbols) (n : Nat)
    (c : TapeConfig states symbols) (s : StackConfig states symbols)
    (h : Represents m.blank c s) :
    HaltsAfter (tapeStep m) n c ↔ HaltsAfter (stackStep m) n s := by
  have hr := run_represents m n c s h
  cases hc : run (tapeStep m) n c <;> cases hs : run (stackStep m) n s <;>
    simp only [hc, hs, OptionRelated] at hr
  · simp [HaltsAfter, hc, hs]
  · simp only [HaltsAfter, hc, hs, Option.some.injEq, exists_eq_left']
    exact step_none_iff m _ _ hr

theorem input_haltsAfter_iff (m : Machine states symbols)
    (input : List (Fin symbols)) (n : Nat) :
    HaltsAfter (tapeStep m) n (tapeInput m input) ↔
    HaltsAfter (stackStep m) n (stackInput m input) :=
  haltsAfter_iff m n _ _ (input_represents m input)

/-- Exact halting equivalence for the whole computation from any finite word. -/
theorem input_halts_iff (m : Machine states symbols) (input : List (Fin symbols)) :
    (∃ n, HaltsAfter (tapeStep m) n (tapeInput m input)) ↔
    (∃ n, HaltsAfter (stackStep m) n (stackInput m input)) := by
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, (haltsAfter_iff m n _ _ (input_represents m input)).mp hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, (haltsAfter_iff m n _ _ (input_represents m input)).mpr hn⟩

/-- Every finite prefix exists on one side exactly when it exists on the other. -/
theorem input_diverges_iff (m : Machine states symbols) (input : List (Fin symbols)) :
    (∀ n, run (tapeStep m) n (tapeInput m input) ≠ none) ↔
    (∀ n, run (stackStep m) n (stackInput m input) ≠ none) := by
  constructor
  · intro h n hn
    exact h n ((run_none_iff m n _ _ (input_represents m input)).mpr hn)
  · intro h n hn
    exact h n ((run_none_iff m n _ _ (input_represents m input)).mp hn)

/-- Positive symbol digits ensure that no nonempty stack has code zero. -/
def digit (a : Fin symbols) : Nat := a.val + 1

/-- Least significant digit is the top; base is alphabet size plus one. -/
def stackCode (symbols : Nat) : List (Fin symbols) → Nat
  | [] => 0
  | a :: rest => digit a + (symbols + 1) * stackCode symbols rest

@[simp] theorem stackCode_nil (symbols : Nat) : stackCode symbols [] = 0 := rfl
@[simp] theorem stackCode_cons (a : Fin symbols) (rest : List (Fin symbols)) :
    stackCode symbols (a :: rest) = digit a + (symbols + 1) * stackCode symbols rest := rfl

theorem digit_positive (a : Fin symbols) : 0 < digit a := by simp [digit]

theorem digit_lt_base (a : Fin symbols) : digit a < symbols + 1 := by
  have := a.isLt
  simp only [digit]
  omega

theorem stackCode_cons_positive (a : Fin symbols) (rest : List (Fin symbols)) :
    0 < stackCode symbols (a :: rest) := by
  simp only [stackCode, digit]
  omega

@[simp] theorem stackCode_eq_zero_iff (xs : List (Fin symbols)) :
    stackCode symbols xs = 0 ↔ xs = [] := by
  cases xs with
  | nil => simp
  | cons a rest =>
    have := stackCode_cons_positive a rest
    simp only [reduceCtorEq, iff_false]
    omega

/-- This is the quotient required by the literal counter pop block. -/
theorem stackCode_div (a : Fin symbols) (rest : List (Fin symbols)) :
    stackCode symbols (a :: rest) / (symbols + 1) = stackCode symbols rest := by
  simp only [stackCode]
  rw [Nat.add_mul_div_left _ _ (by omega)]
  rw [Nat.div_eq_of_lt (digit_lt_base a)]
  simp

/-- This is the residue required by the finite-control symbol decoder. -/
theorem stackCode_mod (a : Fin symbols) (rest : List (Fin symbols)) :
    stackCode symbols (a :: rest) % (symbols + 1) = digit a := by
  simp only [stackCode, Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt (digit_lt_base a)

/-- Decode positive digit d as symbol d-1; residue zero denotes empty/blank. -/
def decodeDigit (blank : Fin symbols) (d : Nat) : Fin symbols :=
  if h : 0 < d ∧ d < symbols + 1 then ⟨d - 1, by omega⟩ else blank

@[simp] theorem decodeDigit_zero (blank : Fin symbols) : decodeDigit blank 0 = blank := by
  simp [decodeDigit]

@[simp] theorem decodeDigit_digit (blank a : Fin symbols) :
    decodeDigit blank (digit a) = a := by
  unfold decodeDigit
  rw [dif_pos ⟨digit_positive a, digit_lt_base a⟩]
  apply Fin.ext
  simp [digit]

/-- Numeric pop is exact even when the list is empty. -/
theorem code_pop (blank : Fin symbols) (xs : List (Fin symbols)) :
    (decodeDigit blank (stackCode symbols xs % (symbols + 1)),
      stackCode symbols xs / (symbols + 1)) =
    (ray blank xs 0, stackCode symbols xs.tail) := by
  cases xs with
  | nil => simp
  | cons a rest =>
    simp only [stackCode_mod, stackCode_div, decodeDigit_digit, ray_cons_zero, List.tail_cons]

theorem code_pop_symbol (blank : Fin symbols) (xs : List (Fin symbols)) :
    decodeDigit blank (stackCode symbols xs % (symbols + 1)) = ray blank xs 0 :=
  congrArg Prod.fst (code_pop blank xs)

theorem code_pop_rest (xs : List (Fin symbols)) :
    stackCode symbols xs / (symbols + 1) = stackCode symbols xs.tail := by
  cases xs with
  | nil => simp
  | cons a rest => exact stackCode_div a rest

/-- The stack encoding loses no finite word, including leading/trailing blanks. -/
theorem stackCode_injective : Function.Injective (stackCode symbols) := by
  intro xs
  induction xs with
  | nil =>
    intro ys h
    have hz : stackCode symbols ys = 0 := h.symm
    simpa using ((stackCode_eq_zero_iff ys).mp hz).symm
  | cons a xs ih =>
    intro ys h
    cases ys with
    | nil =>
      have hp := stackCode_cons_positive a xs
      simp only [stackCode_nil] at h
      omega
    | cons b ys =>
      have ht := congrArg (fun n => n / (symbols + 1)) h
      simp only [stackCode_div] at ht
      have hh := congrArg (fun n => n % (symbols + 1)) h
      simp only [stackCode_mod, digit] at hh
      have hab : a = b := Fin.ext (by omega)
      rw [hab, ih ht]

/-- Only two unbounded naturals remain; state and head symbol are finite control. -/
structure EncodedConfig (states symbols : Nat) where
  state : Fin states
  scanned : Fin symbols
  left : Nat
  right : Nat
  deriving DecidableEq, Repr

def encodeStacks (s : StackConfig states symbols) : EncodedConfig states symbols :=
  ⟨s.state, s.scanned, stackCode symbols s.left, stackCode symbols s.right⟩

/-- Pure arithmetic target. Literal INC/DECJZ expansion is a separate layer. -/
def applyEncoded (blank : Fin symbols) (a : Action states symbols)
    (c : EncodedConfig states symbols) : EncodedConfig states symbols :=
  match a.move with
  | .left => ⟨a.next, decodeDigit blank (c.left % (symbols + 1)),
      c.left / (symbols + 1), digit a.write + (symbols + 1) * c.right⟩
  | .stay => ⟨a.next, a.write, c.left, c.right⟩
  | .right => ⟨a.next, decodeDigit blank (c.right % (symbols + 1)),
      digit a.write + (symbols + 1) * c.left, c.right / (symbols + 1)⟩

theorem applyEncoded_encodeStacks (blank : Fin symbols) (a : Action states symbols)
    (s : StackConfig states symbols) :
    applyEncoded blank a (encodeStacks s) = encodeStacks (applyStacks blank a s) := by
  cases hm : a.move <;>
    simp [applyEncoded, applyStacks, hm, encodeStacks, code_pop_symbol, code_pop_rest]

def encodedStep (m : Machine states symbols) (c : EncodedConfig states symbols) :
    Option (EncodedConfig states symbols) :=
  (m.transition c.state c.scanned).map (fun a => applyEncoded m.blank a c)

theorem encodedStep_encodeStacks (m : Machine states symbols)
    (s : StackConfig states symbols) :
    encodedStep m (encodeStacks s) = (stackStep m s).map encodeStacks := by
  change (m.transition s.state s.scanned).map
      (fun a => applyEncoded m.blank a (encodeStacks s)) =
    ((m.transition s.state s.scanned).map (fun a => applyStacks m.blank a s)).map
      encodeStacks
  cases m.transition s.state s.scanned <;>
    simp only [Option.map_none, Option.map_some, applyEncoded_encodeStacks]

/-- General exact functional simulation, with termination reflected by Option. -/
theorem run_map {stepA : α → Option α} {stepB : β → Option β} {f : α → β}
    (h : ∀ a, stepB (f a) = (stepA a).map f) (n : Nat) (a : α) :
    run stepB n (f a) = (run stepA n a).map f := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    simp only [run, h]
    cases hs : stepA a with
    | none => rfl
    | some a' => exact ih a'

theorem encodedRun_encodeStacks (m : Machine states symbols)
    (n : Nat) (s : StackConfig states symbols) :
    run (encodedStep m) n (encodeStacks s) =
      (run (stackStep m) n s).map encodeStacks :=
  run_map (encodedStep_encodeStacks m) n s

/-- Halting is reflected as well as preserved by arithmetic stack encoding. -/
theorem encoded_haltsAfter_iff (m : Machine states symbols)
    (n : Nat) (s : StackConfig states symbols) :
    HaltsAfter (encodedStep m) n (encodeStacks s) ↔
      HaltsAfter (stackStep m) n s := by
  simp only [HaltsAfter, encodedRun_encodeStacks]
  cases hr : run (stackStep m) n s with
  | none => simp
  | some s' =>
    simp only [Option.map_some, Option.some.injEq, exists_eq_left']
    rw [encodedStep_encodeStacks]
    cases stackStep m s' <;> simp

/-- Conventional tapes and two natural stack codes have the same exact halt time. -/
theorem input_encoded_haltsAfter_iff (m : Machine states symbols)
    (input : List (Fin symbols)) (n : Nat) :
    HaltsAfter (tapeStep m) n (tapeInput m input) ↔
    HaltsAfter (encodedStep m) n (encodeStacks (stackInput m input)) :=
  (input_haltsAfter_iff m input n).trans (encoded_haltsAfter_iff m n _).symm

end SOnlyTapeStacks
