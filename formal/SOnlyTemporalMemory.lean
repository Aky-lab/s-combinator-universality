import SOnlyMemory

/-!
# Constructive power-of-two memory initialization and disturbance delay

The proof uses even/odd index decomposition, rather than a binomial parity
library. Two inclusive prefix-XOR updates split into one update on each
subsequence. This gives the same upper-into-lower superset butterfly as the
published initializer. All vector depths, observation times and forcing
histories remain arbitrary.
-/

namespace SOnlyTemporalMemory

open SOnlyMemory

set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

private theorem xor_shuffle : ∀ a b c d : Bool,
    Bool.xor (Bool.xor a b) (Bool.xor c d) =
      Bool.xor (Bool.xor a c) (Bool.xor b d) := by decide

private theorem xor_cancel : ∀ a b : Bool, Bool.xor (Bool.xor a b) b = a := by decide

private theorem xor_pair : ∀ g h x y : Bool,
    Bool.xor (Bool.xor g (Bool.xor h x)) (Bool.xor (Bool.xor h x) y) = Bool.xor g y := by decide

private theorem xor_carry : ∀ g h x y : Bool,
    Bool.xor (Bool.xor g y) (Bool.xor (Bool.xor h x) y) =
      Bool.xor (Bool.xor g h) x := by decide

private theorem xor_assoc : ∀ a b c : Bool,
    Bool.xor a (Bool.xor b c) = Bool.xor (Bool.xor a b) c := by decide

private theorem xor_group : ∀ x y a b : Bool,
    Bool.xor x (Bool.xor y (Bool.xor a b)) =
      Bool.xor (Bool.xor x a) (Bool.xor y b) := by decide

private theorem xor_elim : ∀ a y z : Bool,
    Bool.xor a (Bool.xor (Bool.xor a y) z) = Bool.xor y z := by decide

/-- Interleave the even-index and odd-index subsequences. -/
def weave {α : Type} : List α → List α → List α
  | x :: xs, y :: ys => x :: y :: weave xs ys
  | _, _ => []

@[simp] theorem weave_length {α : Type} (xs ys : List α) (h : xs.length = ys.length) :
    (weave xs ys).length = 2 * xs.length := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all [weave]
  | cons x xs ih =>
    cases ys with
    | nil => simp at h
    | cons y ys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      simp only [weave, List.length_cons, ih ys h]
      omega

@[simp] theorem runningXor_length (g : Bool) (xs : List Bool) :
    (runningXor g xs).length = xs.length := by
  induction xs generalizing g with
  | nil => rfl
  | cons x xs ih => simp [runningXor, ih]

/-- The key characteristic-two identity, including arbitrary incoming carries. -/
theorem double_prefix_weave (xs ys : List Bool) (g h : Bool) :
    runningXor g (runningXor h (weave xs ys)) =
      weave (runningXor (Bool.xor g h) xs) (runningXor g ys) := by
  induction xs generalizing ys g h with
  | nil => cases ys <;> rfl
  | cons x xs ih =>
    cases ys with
    | nil => rfl
    | cons y ys =>
      simp only [weave, runningXor]
      rw [xor_pair, ih, xor_carry]
      rw [xor_assoc]

/-- Unforced prefix-XOR dynamics. -/
def run : Nat → List Bool → List Bool
  | 0, xs => xs
  | n + 1, xs => runningXor false (run n xs)

@[simp] theorem run_length (n : Nat) (xs : List Bool) : (run n xs).length = xs.length := by
  induction n with
  | zero => rfl
  | succ n ih => simp [run, ih]

theorem run_add (m n : Nat) (xs : List Bool) : run (m + n) xs = run m (run n xs) := by
  induction m with
  | zero => simp [run]
  | succ m ih => simp only [Nat.succ_add, run, ih]

/-- Two updates at full width equal one update on each half-width subsequence. -/
theorem run_even_weave (n : Nat) (xs ys : List Bool) :
    run (2 * n) (weave xs ys) = weave (run n xs) (run n ys) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega]
    simp only [run]
    rw [ih, double_prefix_weave]
    rfl

def observe (xs : List Bool) : Bool := xs.foldr Bool.xor false

theorem observe_weave (xs ys : List Bool) (h : xs.length = ys.length) :
    observe (weave xs ys) = Bool.xor (observe xs) (observe ys) := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all [weave, observe]
  | cons x xs ih =>
    cases ys with
    | nil => simp at h
    | cons y ys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      simp only [weave, observe, List.foldr_cons]
      change Bool.xor x (Bool.xor y (observe (weave xs ys))) = _
      rw [ih ys h]
      exact xor_group x y (observe xs) (observe ys)

/-- At every paired position, adjacent inclusive prefixes cancel to the odd input. -/
theorem observe_prefix_weave (xs ys : List Bool) (g : Bool) (h : xs.length = ys.length) :
    observe (runningXor g (weave xs ys)) = observe ys := by
  induction xs generalizing ys g with
  | nil => cases ys <;> simp_all [weave, observe, runningXor]
  | cons x xs ih =>
    cases ys with
    | nil => simp at h
    | cons y ys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      simp only [weave, runningXor, observe, List.foldr_cons]
      change Bool.xor (Bool.xor g x)
        (Bool.xor (Bool.xor (Bool.xor g x) y)
          (observe (runningXor (Bool.xor (Bool.xor g x) y) (weave xs ys)))) = _
      rw [ih ys _ h]
      exact xor_elim (Bool.xor g x) y (observe ys)

theorem observe_even (n : Nat) (xs ys : List Bool) (h : xs.length = ys.length) :
    observe (run (2 * n) (weave xs ys)) =
      Bool.xor (observe (run n xs)) (observe (run n ys)) := by
  rw [run_even_weave, observe_weave _ _ (by simpa using h)]

theorem observe_odd (n : Nat) (xs ys : List Bool) (h : xs.length = ys.length) :
    observe (run (2 * n + 1) (weave xs ys)) = observe (run n ys) := by
  rw [run, run_even_weave, observe_prefix_weave _ _ _ (by simpa using h)]

/-- A power-of-two vector, recursively separated into even and odd indices. -/
inductive Vector : Nat → Type where
  | single : Bool → Vector 0
  | branch {depth : Nat} : Vector depth → Vector depth → Vector (depth + 1)

def toList : {depth : Nat} → Vector depth → List Bool
  | 0, .single b => [b]
  | _ + 1, .branch even odd => weave (toList even) (toList odd)

def vxor : {depth : Nat} → Vector depth → Vector depth → Vector depth
  | 0, .single a, .single b => .single (Bool.xor a b)
  | _ + 1, .branch ae ao, .branch be bo => .branch (vxor ae be) (vxor ao bo)

/-- Upper-into-lower butterfly, in least-significant-index-bit order. -/
def transform : {depth : Nat} → Vector depth → Vector depth
  | 0, .single b => .single b
  | _ + 1, .branch even odd =>
      .branch (vxor (transform even) (transform odd)) (transform odd)

/-- Index lookup repeats with the vector's power-of-two period. -/
def lookup : {depth : Nat} → Vector depth → Nat → Bool
  | 0, .single b, _ => b
  | _ + 1, .branch even odd, time =>
      if time % 2 = 0 then lookup even (time / 2) else lookup odd (time / 2)

/-- Construct a vector from any desired finite sequence, read at indices below 2^depth. -/
def tabulate : (depth : Nat) → (Nat → Bool) → Vector depth
  | 0, f => .single (f 0)
  | depth + 1, f => .branch
      (tabulate depth (fun i => f (2 * i)))
      (tabulate depth (fun i => f (2 * i + 1)))

@[simp] theorem toList_length {depth : Nat} (v : Vector depth) : (toList v).length = 2 ^ depth := by
  induction v with
  | single b => rfl
  | @branch depth even odd he ho =>
    simp only [toList, weave_length _ _ (he.trans ho.symm), he]
    rw [Nat.pow_succ, Nat.mul_comm]

theorem vxor_shuffle {depth : Nat} (a b c d : Vector depth) :
    vxor (vxor a b) (vxor c d) = vxor (vxor a c) (vxor b d) := by
  induction a with
  | single a => cases b; cases c; cases d; simp only [vxor, xor_shuffle]
  | branch ae ao he ho =>
    cases b; cases c; cases d
    simp only [vxor, he, ho]

theorem vxor_cancel {depth : Nat} (a b : Vector depth) : vxor (vxor a b) b = a := by
  induction a with
  | single a => cases b; simp only [vxor, xor_cancel]
  | branch ae ao he ho => cases b; simp only [vxor, he, ho]

theorem lookup_xor {depth : Nat} (a b : Vector depth) (time : Nat) :
    lookup (vxor a b) time = Bool.xor (lookup a time) (lookup b time) := by
  induction a generalizing time with
  | single a => cases b; rfl
  | branch ae ao he ho =>
    cases b
    simp only [vxor, lookup]
    split <;> simp_all

/-- The butterfly is a linear map over XOR. -/
theorem transform_xor {depth : Nat} (a b : Vector depth) :
    transform (vxor a b) = vxor (transform a) (transform b) := by
  induction a with
  | single a => cases b; rfl
  | branch ae ao he ho =>
    cases b with
    | branch be bo =>
      simp only [vxor, transform, he, ho]
      rw [vxor_shuffle]

/-- The prescribed superset butterfly is its own constructive inverse. -/
theorem transform_involution {depth : Nat} (v : Vector depth) :
    transform (transform v) = v := by
  induction v with
  | single b => rfl
  | branch even odd he ho =>
    simp only [transform, transform_xor, he, ho, vxor_cancel]

theorem lookup_tabulate (depth : Nat) (f : Nat → Bool) (time : Nat) (htime : time < 2 ^ depth) :
    lookup (tabulate depth f) time = f time := by
  induction depth generalizing f time with
  | zero =>
    have : time = 0 := by simpa using htime
    subst time
    rfl
  | succ depth ih =>
    have hdiv := Nat.div_add_mod time 2
    have hmod := Nat.mod_lt time (by decide : 0 < 2)
    have hbound : time / 2 < 2 ^ depth := by
      rw [Nat.pow_succ] at htime
      omega
    simp only [tabulate, lookup]
    split
    · rw [ih _ _ hbound]
      congr 1
      omega
    · rw [ih _ _ hbound]
      congr 1
      omega

theorem run_single (time : Nat) (b : Bool) : run time [b] = [b] := by
  induction time with
  | zero => rfl
  | succ time ih => simp [run, ih, runningXor]

/-- Every unforced observation is exactly the corresponding butterfly coordinate. -/
theorem observation_transform {depth : Nat} (v : Vector depth) (time : Nat) :
    observe (run time (toList v)) = lookup (transform v) time := by
  induction v generalizing time with
  | single b => simp [toList, run_single, observe, transform, lookup]
  | branch even odd he ho =>
    have hlength : (toList even).length = (toList odd).length := by simp
    have hdiv := Nat.div_add_mod time 2
    have hmod := Nat.mod_lt time (by decide : 0 < 2)
    by_cases ht : time % 2 = 0
    · have ht' : time = 2 * (time / 2) := by omega
      calc
        observe (run time (toList (.branch even odd))) =
            Bool.xor (observe (run (time / 2) (toList even)))
              (observe (run (time / 2) (toList odd))) := by
          change observe (run time (weave (toList even) (toList odd))) = _
          conv => lhs; rw [ht']
          exact observe_even _ _ _ hlength
        _ = lookup (transform (.branch even odd)) time := by
          simp only [transform, lookup, ht, ↓reduceIte, lookup_xor, he, ho]
    · have ht' : time = 2 * (time / 2) + 1 := by omega
      calc
        observe (run time (toList (.branch even odd))) =
            observe (run (time / 2) (toList odd)) := by
          change observe (run time (weave (toList even) (toList odd))) = _
          conv => lhs; rw [ht']
          exact observe_odd _ _ _ hlength
        _ = lookup (transform (.branch even odd)) time := by
          simp only [transform, lookup, ht, ↓reduceIte, ho]

/-- Applying the same butterfly initializes an arbitrary desired observation vector. -/
theorem initialized_observation {depth : Nat} (desired : Vector depth) (time : Nat) :
    observe (run time (toList (transform desired))) = lookup desired time := by
  rw [observation_transform, transform_involution]

/-- A finite, explicit initializer with exactly 2^depth bits. -/
def initializer (depth : Nat) (desired : Nat → Bool) : List Bool :=
  toList (transform (tabulate depth desired))

@[simp] theorem initializer_length (depth : Nat) (desired : Nat → Bool) :
    (initializer depth desired).length = 2 ^ depth := by simp [initializer]

/-- Uniform all-input initializer correctness over the entire finite observation window. -/
theorem initializer_correct (depth : Nat) (desired : Nat → Bool) (time : Nat)
    (htime : time < 2 ^ depth) : observe (run time (initializer depth desired)) = desired time := by
  rw [initializer, initialized_observation, lookup_tabulate depth desired time htime]

theorem weave_replicate (n : Nat) (b : Bool) :
    weave (List.replicate n b) (List.replicate n b) = List.replicate (2 * n) b := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega]
    simp only [List.replicate_succ, weave, ih]

theorem doubled_replicate (depth : Nat) (b : Bool) :
    List.replicate (2 ^ (depth + 1)) b =
      weave (List.replicate (2 ^ depth) b) (List.replicate (2 ^ depth) b) := by
  rw [weave_replicate, Nat.pow_succ, Nat.mul_comm]

/-- Output produced after `time` unforced updates of an all-ones disturbance. -/
def impulse (depth time : Nat) : Bool :=
  observe (run time (List.replicate (2 ^ depth) true))

theorem impulse_even (depth time : Nat) : impulse (depth + 1) (2 * time) = false := by
  unfold impulse
  rw [doubled_replicate, observe_even _ _ _ rfl]
  simp

theorem impulse_odd (depth time : Nat) : impulse (depth + 1) (2 * time + 1) = impulse depth time := by
  unfold impulse
  rw [doubled_replicate, observe_odd _ _ _ rfl]

/-- An update disturbance is invisible for the next width-minus-one observations. -/
theorem impulse_before (depth time : Nat) (h : time + 1 < 2 ^ depth) :
    impulse depth time = false := by
  induction depth generalizing time with
  | zero => simp at h
  | succ depth ih =>
    have hdiv := Nat.div_add_mod time 2
    have hmod := Nat.mod_lt time (by decide : 0 < 2)
    rw [Nat.pow_succ] at h
    by_cases ht : time % 2 = 0
    · have ht' : time = 2 * (time / 2) := by omega
      rw [ht', impulse_even]
    · have ht' : time = 2 * (time / 2) + 1 := by omega
      rw [ht', impulse_odd]
      apply ih
      omega

/-- The first impulse output is precisely at exponent width-minus-one. -/
theorem impulse_boundary (depth : Nat) : impulse depth (2 ^ depth - 1) = true := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
    have hpos : 0 < 2 ^ depth := Nat.pow_pos (by decide)
    have hindex : 2 ^ (depth + 1) - 1 = 2 * (2 ^ depth - 1) + 1 := by
      rw [Nat.pow_succ]
      omega
    rw [hindex, impulse_odd, ih]

def xorList (xs ys : List Bool) : List Bool := List.zipWith Bool.xor xs ys

theorem prefix_xor (xs ys : List Bool) (g h : Bool) :
    runningXor (Bool.xor g h) (xorList xs ys) =
      xorList (runningXor g xs) (runningXor h ys) := by
  induction xs generalizing ys g h with
  | nil => cases ys <;> rfl
  | cons x xs ih =>
    cases ys with
    | nil => rfl
    | cons y ys =>
      simp only [xorList, List.zipWith_cons_cons, runningXor]
      rw [xor_shuffle]
      exact congrArg (List.cons (Bool.xor (Bool.xor g x) (Bool.xor h y))) (ih ys _ _)

theorem run_xor (time : Nat) (xs ys : List Bool) :
    run time (xorList xs ys) = xorList (run time xs) (run time ys) := by
  induction time with
  | zero => rfl
  | succ time ih =>
    simpa only [run, ih, Bool.false_xor] using prefix_xor (run time xs) (run time ys) false false

theorem observe_xor (xs ys : List Bool) (h : xs.length = ys.length) :
    observe (xorList xs ys) = Bool.xor (observe xs) (observe ys) := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all [xorList, observe]
  | cons x xs ih =>
    cases ys with
    | nil => simp at h
    | cons y ys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      change Bool.xor (Bool.xor x y) (observe (xorList xs ys)) = _
      rw [ih ys h]
      exact xor_shuffle x y (observe xs) (observe ys)

@[simp] theorem xorList_zeros (xs : List Bool) :
    xorList xs (List.replicate xs.length false) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [xorList, List.length_cons, List.replicate_succ, List.zipWith_cons_cons,
      Bool.xor_false]
    exact congrArg (List.cons x) ih

@[simp] theorem prefix_zeros (n : Nat) (g : Bool) :
    runningXor g (List.replicate n false) = List.replicate n g := by
  induction n generalizing g with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, runningXor, ih]

/-- A forcing bit adds the all-ones column, exactly as in the written recurrence. -/
theorem prefix_forcing (xs : List Bool) (g : Bool) :
    runningXor g xs = xorList (runningXor false xs) (List.replicate xs.length g) := by
  simpa only [Bool.false_xor, xorList_zeros, prefix_zeros] using
    prefix_xor xs (List.replicate xs.length false) false g

@[simp] theorem run_zeros (time n : Nat) :
    run time (List.replicate n false) = List.replicate n false := by
  induction time with
  | zero => rfl
  | succ time ih => simp [run, ih]

@[simp] theorem observe_zeros (n : Nat) : observe (List.replicate n false) = false := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [observe, List.replicate_succ] using ih

theorem observe_constant_forcing (depth time : Nat) (g : Bool) :
    observe (run time (List.replicate (2 ^ depth) g)) = (g && impulse depth time) := by
  cases g
  · simp
  · rfl

/-- One arbitrary forcing update, observed after any further unforced horizon. -/
theorem one_forcing_effect (depth time : Nat) (xs : List Bool) (g : Bool)
    (hlen : xs.length = 2 ^ depth) :
    observe (run time (runningXor g xs)) =
      Bool.xor (observe (run (time + 1) xs)) (g && impulse depth time) := by
  rw [prefix_forcing, run_xor,
    observe_xor _ _ (by simp), hlen, observe_constant_forcing]
  have hshift : run time (runningXor false xs) = run (time + 1) xs :=
    (run_add time 1 xs).symm
  rw [hshift]

/-- An arbitrary realized forcing history; no independence/nonadaptivity premise. -/
def forcedRun (forcing : Nat → Bool) : Nat → List Bool → List Bool
  | 0, xs => xs
  | time + 1, xs => runningXor (forcing time) (forcedRun forcing time xs)

@[simp] theorem forcedRun_length (forcing : Nat → Bool) (time : Nat) (xs : List Bool) :
    (forcedRun forcing time xs).length = xs.length := by
  induction time with
  | zero => rfl
  | succ time ih => simp [forcedRun, ih]

/-- Finite impulse convolution, read backwards from the last forcing update. -/
def response (depth : Nat) (forcing : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => false
  | time + 1, shift => Bool.xor (response depth forcing time (shift + 1))
      (forcing time && impulse depth shift)

/-- Exact linear response identity for all histories, times and observation shifts. -/
theorem forcing_response (depth : Nat) (forcing : Nat → Bool) (time shift : Nat)
    (xs : List Bool) (hlen : xs.length = 2 ^ depth) :
    observe (run shift (forcedRun forcing time xs)) =
      Bool.xor (observe (run (shift + time) xs)) (response depth forcing time shift) := by
  induction time generalizing shift with
  | zero => simp [forcedRun, response]
  | succ time ih =>
    rw [forcedRun, one_forcing_effect depth shift _ _ (by simpa using hlen), ih]
    rw [show (shift + 1) + time = shift + (time + 1) by omega]
    exact (xor_assoc _ _ _).symm

/-- Every forcing contribution vanishes strictly before the width boundary. -/
theorem response_before (depth : Nat) (forcing : Nat → Bool) (time shift : Nat)
    (h : shift + time < 2 ^ depth) : response depth forcing time shift = false := by
  induction time generalizing shift with
  | zero => rfl
  | succ time ih =>
    rw [response, ih (shift + 1) (by omega), impulse_before depth shift (by omega)]
    cases forcing time <;> rfl

/-- Forced and unforced observations agree over the complete protected window. -/
theorem forcing_invisible (depth : Nat) (forcing : Nat → Bool) (time : Nat)
    (xs : List Bool) (hlen : xs.length = 2 ^ depth) (htime : time < 2 ^ depth) :
    observe (forcedRun forcing time xs) = observe (run time xs) := by
  have h := forcing_response depth forcing time 0 xs hlen
  rw [response_before depth forcing time 0 (by simpa using htime)] at h
  simpa only [run, Nat.zero_add, Bool.xor_false] using h

/-- Constructive prescribed observations survive every possible forcing history. -/
theorem forced_initializer_correct (depth : Nat) (desired forcing : Nat → Bool) (time : Nat)
    (htime : time < 2 ^ depth) :
    observe (forcedRun forcing time (initializer depth desired)) = desired time := by
  rw [forcing_invisible depth forcing time _ (initializer_length depth desired) htime,
    initializer_correct depth desired time htime]

/-- A single disturbance in update zero. -/
def unitPulse (time : Nat) : Bool := decide (time = 0)

theorem unitPulse_run (depth time : Nat) :
    forcedRun unitPulse (time + 1) (List.replicate (2 ^ depth) false) =
      run time (List.replicate (2 ^ depth) true) := by
  induction time with
  | zero => simp [forcedRun, run, unitPulse]
  | succ time ih =>
    rw [forcedRun, ih]
    simp only [unitPulse, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, decide_false]
    rfl

/-- The protection window is sharp: the update-zero disturbance first appears
at output 2^depth, including the one-cell case. -/
theorem first_disturbed_output (depth : Nat) :
    (∀ time, time < 2 ^ depth →
      observe (forcedRun unitPulse time (List.replicate (2 ^ depth) false)) = false) ∧
    observe (forcedRun unitPulse (2 ^ depth) (List.replicate (2 ^ depth) false)) = true := by
  constructor
  · intro time htime
    rw [forcing_invisible depth unitPulse time _ (by simp) htime]
    simp
  · have hpos : 0 < 2 ^ depth := Nat.pow_pos (by decide)
    have hwidth : 2 ^ depth = (2 ^ depth - 1) + 1 := by omega
    conv => lhs; arg 1; arg 2; rw [hwidth]
    rw [unitPulse_run]
    exact impulse_boundary depth

/-- One literal butterfly stride: at bit zero, XOR odd into even; higher
strides apply independently to the two index-parity subsequences. -/
def stage : Nat → {depth : Nat} → Vector depth → Vector depth
  | _, 0, .single b => .single b
  | 0, _ + 1, .branch even odd => .branch (vxor even odd) odd
  | bit + 1, _ + 1, .branch even odd => .branch (stage bit even) (stage bit odd)

/-- Execute consecutive stride bits, in precisely increasing order. -/
def stages {depth : Nat} : Nat → Nat → Vector depth → Vector depth
  | _, 0, v => v
  | first, count + 1, v => stages (first + 1) count (stage first v)

theorem stages_branch (first count : Nat) {depth : Nat} (even odd : Vector depth) :
    stages (first + 1) count (.branch even odd) =
      .branch (stages first count even) (stages first count odd) := by
  induction count generalizing first even odd with
  | zero => rfl
  | succ count ih =>
    simp only [stages, stage]
    rw [ih]

/-- The recursive initializer is exactly the increasing-stride butterfly. -/
theorem increasing_strides_eq_transform {depth : Nat} (v : Vector depth) :
    stages 0 depth v = transform v := by
  induction depth with
  | zero => cases v; rfl
  | succ depth ih =>
    cases v with
    | branch even odd =>
      rw [stages, stage, stages_branch, ih, ih]
      simp only [transform, transform_xor]

/-- Exact indexed semantics of a stride: leave a set bit unchanged; otherwise
XOR the entry offset by 2^bit into it. This is the published compiler loop. -/
theorem lookup_stage (bit : Nat) {depth : Nat} (v : Vector depth) (index : Nat)
    (hbit : bit < depth) :
    lookup (stage bit v) index =
      if index.testBit bit then lookup v index
      else Bool.xor (lookup v index) (lookup v (index + 2 ^ bit)) := by
  induction bit generalizing depth index with
  | zero =>
    cases depth with
    | zero => omega
    | succ depth =>
      cases v with
      | branch even odd =>
        have hdiv := Nat.div_add_mod index 2
        have hmod := Nat.mod_lt index (by decide : 0 < 2)
        by_cases hzero : index % 2 = 0
        · have hone : (index + 1) % 2 = 1 := by omega
          have hquot : (index + 1) / 2 = index / 2 := by omega
          simp [stage, lookup, lookup_xor, Nat.testBit_zero, hzero, hone, hquot]
        · have hone : index % 2 = 1 := by omega
          simp [stage, lookup, Nat.testBit_zero, hone]
  | succ bit ih =>
    cases depth with
    | zero => omega
    | succ depth =>
      cases v with
      | branch even odd =>
        have hsmall : bit < depth := by omega
        have hmod : (index + 2 ^ (bit + 1)) % 2 = index % 2 := by
          rw [Nat.pow_succ]
          omega
        have hquot : (index + 2 ^ (bit + 1)) / 2 = index / 2 + 2 ^ bit := by
          rw [Nat.pow_succ]
          omega
        simp only [stage, lookup, Nat.testBit_succ, hmod, hquot]
        split <;> exact ih _ _ hsmall

/-- Instantiate the source memory with zero dynamic bits and the computed fixed bits. -/
def initialCells (bits : List Bool) : List Cell := bits.map (fun a => (false, a))

@[simp] theorem initialCells_combined (bits : List Bool) : combined (initialCells bits) = bits := by
  induction bits with
  | nil => rfl
  | cons b bits ih => simpa [combined, initialCells] using congrArg (List.cons b) ih

/-- Actual normal memory updates, parameterized by incoming skip-alignment bits. -/
def memoryRun (forcing : Nat → Bool) : Nat → List Cell → List Cell
  | 0, cells => cells
  | time + 1, cells => normalUpdate (!(forcing time)) (memoryRun forcing time cells)

/-- Connect the list algebra to the literal three-pass tag memory. -/
theorem memoryRun_combined (forcing : Nat → Bool) (time : Nat) (cells : List Cell) :
    combined (memoryRun forcing time cells) = forcedRun forcing time (combined cells) := by
  induction time with
  | zero => rfl
  | succ time ih => simp only [memoryRun, memory_running_xor, Bool.not_not, ih, forcedRun]

/-- A uniform programmed-width theorem for the actual source block. Exterior
Parity and Reset must be normal; forcing may depend on surrounding execution. -/
theorem source_programmed_width (depth : Nat) (desired forcing : Nat → Bool) (time : Nat)
    (htime : time < 2 ^ depth) :
    widthParity (memoryRun forcing time (initialCells (initializer depth desired))) = desired time := by
  unfold widthParity
  change observe (combined (memoryRun forcing time (initialCells (initializer depth desired)))) = _
  rw [memoryRun_combined, initialCells_combined, forced_initializer_correct depth desired forcing time htime]

/-- Exact emitted-symbol accounting for the initializer: two per cell plus
three per fixed inverter. -/
theorem initial_memory_length (bits : List Bool) :
    (memory (initialCells bits)).length = 2 * bits.length + 3 * (bits.filter id).length := by
  induction bits with
  | nil => rfl
  | cons b bits ih =>
    change (component false b ++ memory (initialCells bits)).length = _
    rw [List.length_append, ih]
    cases b <;> simp [component, cellWord, inverter] <;> omega

/-- The constructive memory initializer occupies between 2W and 5W tag symbols. -/
theorem initializer_memory_bounds (depth : Nat) (desired : Nat → Bool) :
    2 * 2 ^ depth ≤ (memory (initialCells (initializer depth desired))).length ∧
      (memory (initialCells (initializer depth desired))).length ≤ 5 * 2 ^ depth := by
  rw [initial_memory_length, initializer_length]
  have hfilter := List.length_filter_le (p := id) (l := initializer depth desired)
  rw [initializer_length] at hfilter
  omega

theorem weave_get_even {α : Type} (xs ys : List α) (index : Nat)
    (h : xs.length = ys.length) : (weave xs ys)[2 * index]? = xs[index]? := by
  induction xs generalizing ys index with
  | nil => cases ys <;> simp_all [weave]
  | cons x xs ih =>
    cases ys with
    | nil => simp at h
    | cons y ys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      cases index with
      | zero => rfl
      | succ index =>
        rw [show 2 * (index + 1) = (2 * index + 1) + 1 by omega]
        simpa only [weave, List.getElem?_cons_succ] using ih ys index h

theorem weave_get_odd {α : Type} (xs ys : List α) (index : Nat)
    (h : xs.length = ys.length) : (weave xs ys)[2 * index + 1]? = ys[index]? := by
  induction xs generalizing ys index with
  | nil => cases ys <;> simp_all [weave]
  | cons x xs ih =>
    cases ys with
    | nil => simp at h
    | cons y ys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      cases index with
      | zero => rfl
      | succ index =>
        rw [show 2 * (index + 1) + 1 = ((2 * index + 1) + 1) + 1 by omega]
        simpa only [weave, List.getElem?_cons_succ] using ih ys index h

/-- The butterfly's index interpretation is the literal order of emitted bits. -/
theorem toList_lookup {depth : Nat} (v : Vector depth) (index : Nat)
    (hindex : index < 2 ^ depth) : (toList v)[index]? = some (lookup v index) := by
  induction v generalizing index with
  | single b =>
    have : index = 0 := by simpa using hindex
    subst index
    rfl
  | @branch depth even odd he ho =>
    have hlength : (toList even).length = (toList odd).length := by simp
    have hdiv := Nat.div_add_mod index 2
    have hmod := Nat.mod_lt index (by decide : 0 < 2)
    have hsmall : index / 2 < 2 ^ depth := by
      rw [Nat.pow_succ] at hindex
      omega
    by_cases ht : index % 2 = 0
    · have ht' : index = 2 * (index / 2) := by omega
      calc
        (toList (.branch even odd))[index]? = (toList even)[index / 2]? := by
          change (weave (toList even) (toList odd))[index]? = _
          conv => lhs; arg 2; rw [ht']
          exact weave_get_even _ _ _ hlength
        _ = some (lookup (.branch even odd) index) := by
          rw [he _ hsmall]
          simp only [lookup, ht, ↓reduceIte]
    · have ht' : index = 2 * (index / 2) + 1 := by omega
      calc
        (toList (.branch even odd))[index]? = (toList odd)[index / 2]? := by
          change (weave (toList even) (toList odd))[index]? = _
          conv => lhs; arg 2; rw [ht']
          exact weave_get_odd _ _ _ hlength
        _ = some (lookup (.branch even odd) index) := by
          rw [ho _ hsmall]
          simp only [lookup, ht, ↓reduceIte]

/-- Exact equality to the finite increasing-stride implementation, in ordinary
list order; this is a checked link, not a replacement initializer convention. -/
theorem initializer_eq_increasing_strides (depth : Nat) (desired : Nat → Bool) :
    initializer depth desired = toList (stages 0 depth (tabulate depth desired)) := by
  rw [increasing_strides_eq_transform]
  rfl

end SOnlyTemporalMemory

#print axioms SOnlyTemporalMemory.double_prefix_weave
#print axioms SOnlyTemporalMemory.run_even_weave
#print axioms SOnlyTemporalMemory.observe_even
#print axioms SOnlyTemporalMemory.observe_odd

#print axioms SOnlyTemporalMemory.transform_involution
#print axioms SOnlyTemporalMemory.observation_transform
#print axioms SOnlyTemporalMemory.initializer_correct

#print axioms SOnlyTemporalMemory.impulse_before
#print axioms SOnlyTemporalMemory.impulse_boundary
#print axioms SOnlyTemporalMemory.forcing_response
#print axioms SOnlyTemporalMemory.forcing_invisible
#print axioms SOnlyTemporalMemory.forced_initializer_correct
#print axioms SOnlyTemporalMemory.first_disturbed_output

#print axioms SOnlyTemporalMemory.increasing_strides_eq_transform
#print axioms SOnlyTemporalMemory.lookup_stage
#print axioms SOnlyTemporalMemory.memoryRun_combined
#print axioms SOnlyTemporalMemory.source_programmed_width
#print axioms SOnlyTemporalMemory.initializer_memory_bounds

#print axioms SOnlyTemporalMemory.toList_lookup
#print axioms SOnlyTemporalMemory.initializer_eq_increasing_strides
