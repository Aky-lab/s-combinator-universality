import SOnlySource
import Init.Data.Nat.Power2.Lemmas

/-!
# Current-word counter-run arithmetic

The reader scans only a supplied finite symbol word. It extracts its first
maximal run of published symbol 16 and uses integer bit tests/logarithms.
The theorem identifies its result for every word in the first-counter form,
with arbitrary surrounding memories that do not merge with that run.
-/
namespace SOnlyResult

/-- Count the leading run of published symbol 16. -/
def leadingRun : List Nat → Nat
  | [] => 0
  | symbol :: rest => if symbol = 16 then leadingRun rest + 1 else 0

/-- Locate the first run structurally; no source program or trace is supplied. -/
def firstRun : List Nat → Nat
  | [] => 0
  | symbol :: rest => if symbol = 16 then leadingRun rest + 1 else firstRun rest

/-- The same integer power-of-four test and exponent arithmetic as the
structural result interface. The integer tested is an input run length. -/
def decodeLength (n : Nat) : Option Nat :=
  if 4 ≤ n ∧ (n &&& (n - 1)) = 0 ∧ n.log2 % 2 = 0
  then some (n.log2 / 2 - 1) else none

def readCounter (word : List Nat) : Option Nat := decodeLength (firstRun word)

/-- Undo the compiler's positive odd first-counter result convention. -/
def decodeMachineValue (counter : Nat) : Option Nat :=
  if 3 ≤ counter ∧ counter % 2 = 1 then some ((counter - 3) / 2) else none

def readMachineValue (word : List Nat) : Option Nat :=
  (readCounter word).bind decodeMachineValue

theorem leadingRun_non16 (tail : List Nat) (notHead : tail.head? ≠ some 16) :
    leadingRun tail = 0 := by
  cases tail with
  | nil => rfl
  | cons symbol rest =>
      have different : symbol ≠ 16 := by intro h; subst symbol; exact notHead rfl
      simp [leadingRun, different]

theorem leadingRun_replicate (n : Nat) (tail : List Nat) :
    leadingRun (List.replicate n 16 ++ tail) = n + leadingRun tail := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, leadingRun, ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem firstRun_prefix (front tail : List Nat)
    (no16 : ∀ symbol ∈ front, symbol ≠ 16) : firstRun (front ++ tail) = firstRun tail := by
  induction front with
  | nil => rfl
  | cons symbol rest ih =>
      have different := no16 symbol (by simp)
      simp only [List.cons_append, firstRun, if_neg different]
      exact ih (fun x h => no16 x (by simp [h]))

/-- A nonempty run between non-16 boundaries is exactly the first run found. -/
theorem firstRun_counter (front tail : List Nat) (n : Nat) (positive : 0 < n)
    (no16 : ∀ symbol ∈ front, symbol ≠ 16) (notHead : tail.head? ≠ some 16) :
    firstRun (front ++ List.replicate n 16 ++ tail) = n := by
  rw [List.append_assoc, firstRun_prefix front _ no16]
  cases n with
  | zero => omega
  | succ n =>
      simp only [List.replicate_succ, List.cons_append, firstRun, ↓reduceIte]
      rw [leadingRun_replicate, leadingRun_non16 tail notHead]

theorem pow_four (n : Nat) : 4 ^ n = 2 ^ (2 * n) := by
  rw [Nat.pow_mul]

theorem decodeLength_counter (value : Nat) :
    decodeLength (4 ^ (value + 1)) = some value := by
  have nonzero : 4 ^ (value + 1) ≠ 0 := Nat.ne_of_gt (Nat.pow_pos (by decide))
  have power2 : (4 ^ (value + 1)).isPowerOfTwo := ⟨2 * (value + 1), pow_four _⟩
  have bitTest := (Nat.and_sub_one_eq_zero_iff_isPowerOfTwo nonzero).mpr power2
  have logEq : (4 ^ (value + 1)).log2 = 2 * (value + 1) := by
    rw [pow_four, Nat.log2_two_pow]
  have lower : 4 ≤ 4 ^ (value + 1) := by
    have h := Nat.one_le_pow value 4 (by decide)
    rw [Nat.pow_succ]
    omega
  simp only [decodeLength, lower, bitTest, logEq]
  have parity : 2 * (value + 1) % 2 = 0 := by omega
  simp [parity]

/-- Uniform readout of a first counter K(value)=16^(4^(value+1)). -/
theorem readCounter_correct (front tail : List Nat) (value : Nat)
    (no16 : ∀ symbol ∈ front, symbol ≠ 16) (notHead : tail.head? ≠ some 16) :
    readCounter (front ++ List.replicate (4 ^ (value + 1)) 16 ++ tail) = some value := by
  unfold readCounter
  rw [firstRun_counter front tail _ (Nat.pow_pos (by decide)) no16 notHead,
    decodeLength_counter]

theorem decodeMachineValue_correct (value : Nat) :
    decodeMachineValue (2 * value + 3) = some value := by
  unfold decodeMachineValue
  have lower : 3 ≤ 2 * value + 3 := by omega
  have parity : (2 * value + 3) % 2 = 1 := by omega
  simp [lower, parity]

/-- The complete fixed numerical map on the event grammar's first-counter form. -/
theorem readMachineValue_correct (front tail : List Nat) (value : Nat)
    (no16 : ∀ symbol ∈ front, symbol ≠ 16) (notHead : tail.head? ≠ some 16) :
    readMachineValue (front ++ List.replicate (4 ^ (2 * value + 4)) 16 ++ tail) = some value := by
  unfold readMachineValue
  have exponent : 2 * value + 4 = (2 * value + 3) + 1 := by omega
  rw [exponent, readCounter_correct front tail _ no16 notHead]
  exact decodeMachineValue_correct value

end SOnlyResult

#print axioms SOnlyResult.firstRun_counter
#print axioms SOnlyResult.decodeLength_counter
#print axioms SOnlyResult.readCounter_correct
#print axioms SOnlyResult.readMachineValue_correct
