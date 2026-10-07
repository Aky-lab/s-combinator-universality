import SOnlySource

/-!
# Uniform three-pass UT19 counter kernel

All source symbols are zero-based `SOnlySource.Symbol` values, so the numeral
11 denotes published symbol 12. Each `pass` consumes exactly its original
word, and the FIFO theorem connects it to source microsteps. Halfcommand
alignments are explicit exterior inputs: they are not inferred by running
an isolated counter queue. Counter exponents and copy counts are arbitrary
natural numbers throughout the proofs.
-/

namespace SOnlyCounter

open SOnlySource

set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

/-- Alternating production selection over one original queue. -/
def pass (take : Bool) : List Symbol → List Symbol
  | [] => []
  | symbol :: tail => (if take then production symbol else []) ++ pass (!take) tail

/-- The alignment after consuming exactly `n` original symbols. -/
def phaseAfter : Nat → Bool → Bool
  | 0, take => take
  | n + 1, take => phaseAfter n (!take)

theorem iterate_add (m n : Nat) (config : Config) :
    iterate (m + n) config = iterate m (iterate n config) := by
  induction m with
  | zero => simp only [Nat.zero_add, iterate]
  | succ m ih => simp only [Nat.succ_add, iterate, ih]

/-- A pass is the actual source trajectory over the original word, with any
suffix left in front of its output. No nonempty-output premise is needed. -/
theorem consume_source_prefix (front suffix : List Symbol) (take : Bool) :
    iterate front.length ⟨front ++ suffix, take⟩ =
      ⟨suffix ++ pass take front, phaseAfter front.length take⟩ := by
  induction front generalizing suffix take with
  | nil => simp [iterate, pass, phaseAfter]
  | cons a as ih =>
    rw [List.length_cons, iterate_add]
    cases take
    · simpa [iterate, step, pass, phaseAfter] using ih suffix true
    · simpa [iterate, step, pass, phaseAfter, List.append_assoc] using
        ih (suffix ++ production a) false

/-- Finite-word concatenation tracks consumed-length parity, not output length. -/
theorem pass_append (front tail : List Symbol) (take : Bool) :
    pass take (front ++ tail) =
      pass take front ++ pass (phaseAfter front.length take) tail := by
  induction front generalizing take with
  | nil => simp [pass, phaseAfter]
  | cons a as ih => simp [pass, phaseAfter, ih, List.append_assoc]

/-- Repeat a finite word, using an arbitrary natural copy count. -/
def copies (word : List Symbol) : Nat → List Symbol
  | 0 => []
  | n + 1 => word ++ copies word n

@[simp] theorem copies_zero (word : List Symbol) : copies word 0 = [] := rfl
@[simp] theorem copies_succ (word : List Symbol) (n : Nat) :
    copies word (n + 1) = word ++ copies word n := rfl
@[simp] theorem copies_one (word : List Symbol) : copies word 1 = word := by simp [copies]
@[simp] theorem copies_nil (n : Nat) : copies [] n = [] := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [copies] using ih

theorem copies_add (word : List Symbol) (m n : Nat) :
    copies word (m + n) = copies word m ++ copies word n := by
  induction m with
  | zero => simp
  | succ m ih => simp [Nat.succ_add, ih, List.append_assoc]

theorem copies_copies (word : List Symbol) (m n : Nat) :
    copies (copies word m) n = copies word (m * n) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [copies_succ, ih, Nat.mul_succ]
                 rw [Nat.add_comm, copies_add]

@[simp] theorem copies_length (word : List Symbol) (n : Nat) :
    (copies word n).length = word.length * n := by
  induction n with
  | zero => simp
  | succ n ih => simp [ih, Nat.mul_succ, Nat.add_comm]

/-- Both input symbols in a pair are consumed, so the next pair keeps alignment. -/
theorem pass_pairs (a b : Symbol) (n : Nat) (take : Bool) :
    pass take (copies [a, b] n) =
      copies (if take then production a else production b) n := by
  induction n with
  | zero => simp [pass]
  | succ n ih =>
    rw [copies_succ, pass_append]
    cases take <;> simp [pass, phaseAfter, ih]


/-- Equal-symbol pairs select the same production under either alignment. -/
theorem pass_constant_pairs (a : Symbol) (n : Nat) (take : Bool) :
    pass take (copies [a, a] n) = copies (production a) n := by
  rw [pass_pairs]
  cases take <;> rfl

/-- Checked equations for exactly the six counter productions. -/
@[simp] theorem production_12 : production (11 : Symbol) = [13, 13, 13, 13] := by decide +kernel
@[simp] theorem production_13 : production (12 : Symbol) = [14] := by decide +kernel
@[simp] theorem production_14 : production (13 : Symbol) = [15, 15] := by decide +kernel
@[simp] theorem production_15 : production (14 : Symbol) = [15, 16] := by decide +kernel
@[simp] theorem production_16 : production (15 : Symbol) = [11, 12] := by decide +kernel
@[simp] theorem production_17 : production (16 : Symbol) = [11, 11, 11, 11] := by decide +kernel

/-- Ordinary internal exponent n, published [12,13]^(2^n). -/
def C (n : Nat) : List Symbol := copies [11, 12] (2 ^ n)

/-- Protected exponent n, written as pairs: published [12]^(2^(n+1)). -/
def T (n : Nat) : List Symbol := copies [11, 11] (2 ^ n)

def D : List Symbol := T 1

def halfcommand (q p r : Bool) (word : List Symbol) : List Symbol :=
  pass r (pass p (pass q word))

theorem twice_pow (n : Nat) : 2 * 2 ^ n = 2 ^ (n + 1) := by
  rw [Nat.pow_succ, Nat.mul_comm]

/-- Changing between singleton and paired repetition does not bound the count. -/
theorem two_copies (a : Symbol) (n : Nat) :
    copies [a, a] n = copies [a] (2 * n) := by
  change copies (copies [a] 2) n = copies [a] (2 * n)
  exact copies_copies [a] 2 n

theorem four_copies (a : Symbol) (n : Nat) :
    copies [a, a, a, a] n = copies [a, a] (2 * n) := by
  change copies (copies [a, a] 2) n = copies [a, a] (2 * n)
  exact copies_copies [a, a] 2 n

/-- The pair notation for a protected counter is exactly the published word. -/
theorem protected_word (n : Nat) : T n = copies [11] (2 ^ (n + 1)) := by
  rw [T, two_copies, twice_pow]

@[simp] theorem C_length (n : Nat) : (C n).length = 2 ^ (n + 1) := by
  simp only [C, copies_length, List.length_cons, List.length_nil]
  exact twice_pow n

@[simp] theorem T_length (n : Nat) : (T n).length = 2 ^ (n + 1) := by
  simp only [T, copies_length, List.length_cons, List.length_nil]
  exact twice_pow n

/-- Ordinary increment: the Command output is [14]^(2^(n+2)). -/
theorem increment_command (n : Nat) :
    pass true (C n) = copies [13, 13] (2 ^ (n + 1)) := by
  simp only [C, pass_pairs, ↓reduceIte, production_12, four_copies, twice_pow]

/-- Both Parity and Reset exterior alignments are allowed. -/
theorem increment (n : Nat) (p r : Bool) :
    halfcommand true p r (C n) = C (n + 1) := by
  unfold halfcommand
  rw [increment_command, pass_constant_pairs, production_14,
    pass_constant_pairs, production_16]
  rfl

/-- Protected counters request either operation but always take the increment path. -/
theorem protected_command (n : Nat) (q : Bool) :
    pass q (T n) = copies [13, 13] (2 ^ (n + 1)) := by
  simp only [T, pass_constant_pairs, production_12, four_copies, twice_pow]

theorem protected_increment (n : Nat) (q p r : Bool) :
    halfcommand q p r (T n) = C (n + 1) := by
  simp only [halfcommand, protected_command, pass_constant_pairs,
    production_14, production_16, C]

/-- Positive exponent decrement, with `n+1` expressing all positive exponents. -/
theorem decrement_command (n : Nat) :
    pass false (C (n + 1)) = copies [14, 14] (2 ^ n) := by
  simp only [C, pass_pairs, Bool.false_eq_true, ↓reduceIte, production_13]
  simpa only [twice_pow] using (two_copies (14 : Symbol) (2 ^ n)).symm

/-- The middle pass is independent of the exterior Parity alignment. -/
theorem decrement_parity (n : Nat) (p : Bool) :
    pass p (pass false (C (n + 1))) = copies [15, 16] (2 ^ n) := by
  rw [decrement_command, pass_constant_pairs, production_15]

/-- Even Reset preserves the ordinary representation and subtracts one exponent. -/
theorem decrement_even_reset (n : Nat) (p : Bool) :
    halfcommand false p true (C (n + 1)) = C n := by
  unfold halfcommand
  rw [decrement_parity, pass_pairs]
  simp only [↓reduceIte, production_16, C]

/-- Odd Reset on a nonzero decrement produces protection, not an ordinary decrement. -/
theorem decrement_odd_reset (n : Nat) (p : Bool) :
    halfcommand false p false (C (n + 1)) = T (n + 1) := by
  unfold halfcommand
  rw [decrement_parity, pass_pairs]
  simp only [Bool.false_eq_true, ↓reduceIte, production_17, four_copies, twice_pow, T]

/-- At exponent zero the first pass produces the exceptional singleton 15. -/
theorem zero_decrement_command : pass false (C 0) = [14] := by
  simp [C, copies, pass]

/-- Taken singleton 15 produces [16,17], before the exterior Reset is known. -/
theorem zero_decrement_parity_even : pass true (pass false (C 0)) = [15, 16] := by
  simp [zero_decrement_command, pass]

/-- A skipped singleton 15 vanishes, implementing the halt-counter branch. -/
theorem zero_decrement_parity_odd : pass false (pass false (C 0)) = [] := by
  simp [zero_decrement_command, pass]

/-- The saturated zero case is explicitly distinct from a negative exponent. -/
theorem zero_decrement_saturates : halfcommand false true true (C 0) = C 0 := by
  unfold halfcommand
  rw [zero_decrement_parity_even]
  simp [pass, C, copies]

/-- An ordinary zero decrement under odd Reset produces D = [12,12,12,12]. -/
theorem zero_decrement_protects : halfcommand false true false (C 0) = D := by
  simp [halfcommand, zero_decrement_parity_even, pass, D, T, copies]

/-- Odd Parity deletes the halt counter, regardless of subsequent alignment. -/
theorem zero_decrement_deletes (r : Bool) :
    halfcommand false false r (C 0) = [] := by
  simp only [halfcommand, zero_decrement_parity_odd, pass]

/-- The protected restart has exactly one protected halfcommand. -/
theorem protected_restart_first (q p r : Bool) :
    halfcommand q p r D = C 2 := protected_increment 1 q p r

theorem protected_restart_complete (q p r p' r' : Bool) :
    halfcommand true p' r' (halfcommand q p r D) = C 3 := by
  rw [protected_restart_first]
  exact increment 2 p' r'

/-- All ordinary and protected Command counter words have even length. -/
theorem command_words_even (n : Nat) : (C n).length % 2 = 0 ∧ (T n).length % 2 = 0 := by
  rw [C_length, T_length, ← twice_pow]
  simp

/-- The only odd Parity counter word is the zero-exponent decrement singleton. -/
theorem parity_word_parity (n : Nat) (q : Bool) :
    (pass q (C n)).length % 2 = if q then 0 else if n = 0 then 1 else 0 := by
  cases q with
  | true =>
    rw [increment_command]
    simp
  | false =>
    cases n with
    | zero => rw [zero_decrement_command]; rfl
    | succ n => rw [decrement_command]; simp

theorem protected_parity_even (n : Nat) (q : Bool) :
    (pass q (T n)).length % 2 = 0 := by
  rw [protected_command]
  simp

/-- Every Reset counter word is even, including the empty exceptional word. -/
theorem reset_word_even (n : Nat) (q p : Bool) :
    (pass p (pass q (C n))).length % 2 = 0 := by
  cases q with
  | true =>
    rw [increment_command, pass_constant_pairs, production_14]
    simp
  | false =>
    cases n with
    | zero =>
      cases p
      · rw [zero_decrement_parity_odd]; rfl
      · rw [zero_decrement_parity_even]; rfl
    | succ n => rw [decrement_parity]; simp

theorem protected_reset_even (n : Nat) (q p : Bool) :
    (pass p (pass q (T n))).length % 2 = 0 := by
  rw [protected_command, pass_constant_pairs, production_14]
  simp

/-- The counter subalphabet consists of published symbols 12 through 17. -/
def CounterWord (word : List Symbol) : Prop :=
  ∀ symbol, symbol ∈ word → 11 ≤ symbol.val ∧ symbol.val ≤ 16

/-- Kernel-checked closure of the six literal counter productions. -/
theorem counter_productions_closed : ∀ symbol : Symbol,
    (11 ≤ symbol.val ∧ symbol.val ≤ 16) → CounterWord (production symbol) := by
  unfold CounterWord
  decide +kernel

theorem counterWord_append (front tail : List Symbol)
    (hfront : CounterWord front) (htail : CounterWord tail) : CounterWord (front ++ tail) := by
  intro symbol h
  rcases List.mem_append.mp h with h | h
  · exact hfront symbol h
  · exact htail symbol h

theorem counterWord_copies (word : List Symbol) (n : Nat) (hword : CounterWord word) :
    CounterWord (copies word n) := by
  induction n with
  | zero => simp [CounterWord]
  | succ n ih => exact counterWord_append word (copies word n) hword ih

theorem ordinary_counter_word (n : Nat) : CounterWord (C n) := by
  apply counterWord_copies
  unfold CounterWord
  decide +kernel

theorem protected_counter_word (n : Nat) : CounterWord (T n) := by
  apply counterWord_copies
  unfold CounterWord
  decide +kernel

/-- No pass over counter symbols can emit a memory/halt marker. -/
theorem pass_counter_word (word : List Symbol) (take : Bool) (hword : CounterWord word) :
    CounterWord (pass take word) := by
  induction word generalizing take with
  | nil => simpa [pass] using hword
  | cons a as ih =>
    have ha : 11 ≤ a.val ∧ a.val ≤ 16 := hword a (by simp)
    have has : CounterWord as := fun symbol h => hword symbol (by simp [h])
    cases take with
    | false => simpa [pass] using ih true has
    | true =>
      simpa [pass] using counterWord_append (production a) (pass false as)
        (counter_productions_closed a ha) (ih false has)

theorem counter_word_no_selected (word : List Symbol) (take : Bool)
    (hword : CounterWord word) : ¬Selected ⟨word, take⟩ := by
  rintro ⟨_, hhead⟩
  obtain ⟨tail, htail⟩ := List.head?_eq_some_iff.mp hhead
  change word = _ at htail
  have hbound := hword (⟨17, by decide⟩ : Symbol) (by rw [htail]; simp)
  have : (17 : Nat) ≤ 16 := hbound.2
  omega

/-- At every stage of any counter halfcommand, the counter itself cannot signal 18. -/
theorem counter_stages_no_selected (word : List Symbol) (q p r observed : Bool)
    (hword : CounterWord word) :
    ¬Selected ⟨word, observed⟩ ∧
    ¬Selected ⟨pass q word, observed⟩ ∧
    ¬Selected ⟨pass p (pass q word), observed⟩ ∧
    ¬Selected ⟨halfcommand q p r word, observed⟩ := by
  have h1 := pass_counter_word word q hword
  have h2 := pass_counter_word (pass q word) p h1
  have h3 := pass_counter_word (pass p (pass q word)) r h2
  exact ⟨counter_word_no_selected word observed hword,
    counter_word_no_selected _ observed h1,
    counter_word_no_selected _ observed h2,
    counter_word_no_selected _ observed h3⟩

end SOnlyCounter

#print axioms SOnlyCounter.consume_source_prefix
#print axioms SOnlyCounter.pass_append
#print axioms SOnlyCounter.pass_pairs
#print axioms SOnlyCounter.copies_copies

#print axioms SOnlyCounter.protected_word
#print axioms SOnlyCounter.increment
#print axioms SOnlyCounter.protected_increment
#print axioms SOnlyCounter.decrement_even_reset
#print axioms SOnlyCounter.decrement_odd_reset
#print axioms SOnlyCounter.zero_decrement_saturates
#print axioms SOnlyCounter.zero_decrement_protects
#print axioms SOnlyCounter.zero_decrement_deletes
#print axioms SOnlyCounter.protected_restart_complete

#print axioms SOnlyCounter.command_words_even
#print axioms SOnlyCounter.parity_word_parity
#print axioms SOnlyCounter.reset_word_even
#print axioms SOnlyCounter.counter_productions_closed
#print axioms SOnlyCounter.pass_counter_word
#print axioms SOnlyCounter.counter_stages_no_selected
