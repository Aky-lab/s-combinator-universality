import Std

/-!
# Uniform register-machine to positive-counter compilation

The source has arbitrary finite nonempty register and label types. The target
uses the amnesiac semantics of the written BP2 front end. Stored natural `v`
represents the positive counter `v + 1`: a failed decrement at stored zero
therefore leaves the actual positive counter at one.

This is a deliberately padded variant of the written compiler: it allocates
I/S/F/U/V for every label, scans all labels in order, and assigns unreachable
successors `halt`. The padding changes the syntax-size formula, not the
simulation. No execution bound, source halting premise, or finite test set is
used to construct the table.
-/

namespace SOnlyMachine

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

variable {α : Type} [DecidableEq α]

def put (v : α → Nat) (i : α) (n : Nat) : α → Nat := fun j => if j = i then n else v j

@[simp] theorem put_same (v : α → Nat) (i : α) (n : Nat) : put v i n i = n := by simp [put]
@[simp] theorem put_other (v : α → Nat) (i j : α) (n : Nat) (h : j ≠ i) :
    put v i n j = v j := by simp [put, h]
@[simp] theorem put_put (v : α → Nat) (i : α) (m n : Nat) :
    put (put v i m) i n = put v i n := by funext j; simp [put]; split <;> rfl
@[simp] theorem put_self (v : α → Nat) (i : α) : put v i (v i) = v := by
  funext j; by_cases h : j = i <;> simp_all [put]

theorem put_comm (v : α → Nat) (i j : α) (m n : Nat) (h : i ≠ j) :
    put (put v i m) j n = put (put v j n) i m := by
  funext k
  by_cases hi : k = i <;> by_cases hj : k = j <;> simp_all [put]

inductive Action (α : Type) where
  | inc : α → Action α
  | dec : α → Action α
  | halt : Action α
  deriving DecidableEq, Repr

structure Row (α : Type) where
  inc : Action α
  success : Action α
  failure : Action α

structure State (α : Type) where
  value : α → Nat
  action : Action α

/-- The finite table is a total function on the finite counter type. -/
abbrev Table (α : Type) := α → Row α

def step (P : Table α) (s : State α) : State α :=
  match s.action with
  | .halt => s
  | .inc i => ⟨put s.value i (s.value i + 1), (P i).inc⟩
  | .dec i => if s.value i = 0 then ⟨s.value, (P i).failure⟩
    else ⟨put s.value i (s.value i - 1), (P i).success⟩

def run (P : Table α) : Nat → State α → State α
  | 0, s => s
  | n + 1, s => run P n (step P s)

@[simp] theorem run_zero (P : Table α) (s : State α) : run P 0 s = s := rfl
@[simp] theorem run_succ (P : Table α) (n : Nat) (s : State α) :
    run P (n + 1) s = run P n (step P s) := rfl

theorem run_add (P : Table α) (m n : Nat) (s : State α) :
    run P (m + n) s = run P n (run P m s) := by
  induction m generalizing s with
  | zero => simp [run]
  | succ m ih => simpa [Nat.succ_add, run] using ih (step P s)

@[simp] theorem run_halt (P : Table α) (n : Nat) (v : α → Nat) :
    run P n ⟨v, .halt⟩ = ⟨v, .halt⟩ := by
  induction n <;> simp_all [run, step]

/-- Successor in a bounded chain. Only the unselected, unreachable tail halts. -/
def next {n : Nat} (f : Fin (n + 1) → α) (q : Fin (n + 1)) : Action α :=
  if h : q.val + 1 < n + 1 then .dec (f ⟨q.val + 1, h⟩) else .halt

/-- Every scan is a finite actual execution: one marked counter is consumed,
all earlier unmarked counters fail, and the configured successful edge wins. -/
theorem scan_from {n : Nat} (P : Table α) (f : Fin (n + 1) → α)
    (hf : Function.Injective f)
    (hrow : ∀ q, (P (f q)).failure = next f q)
    (v : α → Nat) (hv : ∀ q, v (f q) = 0) (q : Fin (n + 1))
    (distance : Nat) (j : Fin (n + 1)) (hj : j.val + distance = q.val) :
    run P (distance + 1) ⟨put v (f q) 1, .dec (f j)⟩ =
      ⟨v, (P (f q)).success⟩ := by
  induction distance generalizing j with
  | zero =>
    have heq : j = q := Fin.ext (by omega)
    subst j
    simp only [run_succ, run_zero, step, put_same, show (1 : Nat) ≠ 0 by decide,
      ↓reduceIte, Nat.sub_self, put_put]
    have he : put v (f q) 0 = v := by simpa only [hv q] using put_self v (f q)
    rw [he]
  | succ d ih =>
    have hlt : j.val + 1 < n + 1 := by have := q.isLt; omega
    have hne : f j ≠ f q := by intro h; have := congrArg Fin.val (hf h); omega
    have hzero : put v (f q) 1 (f j) = 0 := by simp [put, hne, hv]
    rw [run_succ]
    simp only [step, hzero, ↓reduceIte, hrow, next, dif_pos hlt]
    exact ih ⟨j.val + 1, hlt⟩ (by simp only; omega)

theorem scan {n : Nat} (P : Table α) (f : Fin (n + 1) → α)
    (hf : Function.Injective f)
    (hrow : ∀ q, (P (f q)).failure = next f q)
    (v : α → Nat) (hv : ∀ q, v (f q) = 0) (q : Fin (n + 1)) :
    run P (q.val + 1) ⟨put v (f q) 1, .dec (f 0)⟩ =
      ⟨v, (P (f q)).success⟩ :=
  scan_from P f hf hrow v hv q q.val 0 (by simp)

inductive Instruction (d n : Nat) where
  | inc : Fin (d + 1) → Fin (n + 1) → Instruction d n
  | dec : Fin (d + 1) → Fin (n + 1) → Fin (n + 1) → Instruction d n
  | halt : Instruction d n
  deriving DecidableEq, Repr

structure Machine (d n : Nat) where
  instruction : Fin (n + 1) → Instruction d n
  entry : Fin (n + 1)

structure SourceState (d n : Nat) where
  value : Fin (d + 1) → Nat
  label : Fin (n + 1)

def sourceStep (M : Machine d n) (s : SourceState d n) : SourceState d n :=
  match M.instruction s.label with
  | .inc i t => ⟨put s.value i (s.value i + 1), t⟩
  | .dec i yes no => if s.value i = 0 then ⟨s.value, no⟩
    else ⟨put s.value i (s.value i - 1), yes⟩
  | .halt => s

inductive Cell (d n : Nat) where
  | data : Fin (d + 1) → Cell d n
  | I : Fin (n + 1) → Cell d n
  | S : Fin (n + 1) → Cell d n
  | F : Fin (n + 1) → Cell d n
  | U : Fin (n + 1) → Cell d n
  | V : Fin (n + 1) → Cell d n
  deriving DecidableEq, Repr

def entry (M : Machine d n) (q : Fin (n + 1)) : Action (Cell d n) :=
  match M.instruction q with
  | .inc _ _ => .inc (.I q)
  | .dec _ _ _ => .inc (.S q)
  | .halt => .halt

/-- A literal compiler table, including total values for unused row entries. -/
def compile (M : Machine d n) : Table (Cell d n)
  | .data _ => ⟨.dec (.I 0), .dec (.S 0), .dec (.F 0)⟩
  | .I q => ⟨match M.instruction q with | .inc i _ => .inc (.data i) | _ => .halt,
      match M.instruction q with | .inc _ t => entry M t | _ => .halt,
      next Cell.I q⟩
  | .S q => ⟨.inc (.F q), .dec (.V q), next Cell.S q⟩
  | .F q => ⟨match M.instruction q with | .dec i _ _ => .dec (.data i) | _ => .halt,
      .dec (.U q), next Cell.F q⟩
  | .U q => ⟨.dec (.F 0),
      match M.instruction q with | .dec _ yes _ => entry M yes | _ => .halt,
      .inc (.V q)⟩
  | .V q => ⟨.dec (.S 0),
      match M.instruction q with | .dec _ _ no => entry M no | _ => .halt,
      .inc (.U q)⟩

/-- Instruction boundaries have exactly zero residual auxiliary counts. -/
def normal (r : Fin (d + 1) → Nat) : Cell d n → Nat
  | .data i => r i
  | _ => 0

def encode (M : Machine d n) (s : SourceState d n) : State (Cell d n) :=
  ⟨normal s.value, entry M s.label⟩

@[simp] theorem normal_data (r : Fin (d + 1) → Nat) (i : Fin (d + 1)) :
    (normal r : Cell d n → Nat) (.data i) = r i := rfl

@[simp] theorem normal_I (r : Fin (d + 1) → Nat) (q : Fin (n + 1)) : normal r (.I q) = 0 := rfl
@[simp] theorem normal_S (r : Fin (d + 1) → Nat) (q : Fin (n + 1)) : normal r (.S q) = 0 := rfl
@[simp] theorem normal_F (r : Fin (d + 1) → Nat) (q : Fin (n + 1)) : normal r (.F q) = 0 := rfl
@[simp] theorem normal_U (r : Fin (d + 1) → Nat) (q : Fin (n + 1)) : normal r (.U q) = 0 := rfl
@[simp] theorem normal_V (r : Fin (d + 1) → Nat) (q : Fin (n + 1)) : normal r (.V q) = 0 := rfl

@[simp] theorem normal_put (r : Fin (d + 1) → Nat) (i : Fin (d + 1)) (v : Nat) :
    (normal (put r i v) : Cell d n → Nat) = put (normal r) (.data i) v := by
  funext c
  cases c <;> simp [normal, put]

/-- An increment macro takes the marker and data increments, then q+1 scans. -/
theorem inc_macro (M : Machine d n) (r : Fin (d + 1) → Nat)
    (q : Fin (n + 1)) (i : Fin (d + 1)) (t : Fin (n + 1))
    (hq : M.instruction q = .inc i t) :
    run (compile M) (q.val + 3) ⟨normal r, entry M q⟩ =
      ⟨normal (put r i (r i + 1)), entry M t⟩ := by
  have hscan := scan (compile M) Cell.I (by intro a b h; cases h; rfl)
    (by intro a; rfl) (normal (put r i (r i + 1))) (by intro a; rfl) q
  change run (compile M) ((q.val + 1) + 1 + 1) _ = _
  rw [run_succ, run_succ]
  have hs : step (compile M) (step (compile M) ⟨normal r, entry M q⟩) =
      ⟨put (normal (put r i (r i + 1))) (.I q) 1, .dec (.I 0)⟩ := by
    simp only [step, entry, hq, compile, normal_I, Nat.zero_add]
    simp only [put, Cell.data.injEq, reduceCtorEq, ↓reduceIte, normal_data]
    rw [normal_put]
    congr 1
    funext c
    cases c <;> simp [put, normal]
  rw [hs]
  simpa only [compile, hq] using hscan

/-- Concatenate two checked finite executions. -/
theorem run_join (P : Table α) {m n : Nat} {a b c : State α}
    (h₁ : run P m a = b) (h₂ : run P n b = c) : run P (m + n) a = c := by
  rw [run_add, h₁, h₂]

/-- The successful decrement restores both call-site chains and its control
counter, including when many source instructions share the same data register. -/
theorem dec_success_macro (M : Machine d n) (r : Fin (d + 1) → Nat)
    (q : Fin (n + 1)) (i : Fin (d + 1)) (yes no : Fin (n + 1))
    (hq : M.instruction q = .dec i yes no) (hr : r i ≠ 0) :
    run (compile M) (2 * q.val + 8) ⟨normal r, entry M q⟩ =
      ⟨normal (put r i (r i - 1)), entry M yes⟩ := by
  let r' := put r i (r i - 1)
  let v : Cell d n → Nat := normal r'
  have hfirst : run (compile M) 3 ⟨normal r, entry M q⟩ =
      ⟨put (put v (.F q) 1) (.S q) 1, .dec (.S 0)⟩ := by
    simp [run, step, entry, hq, compile, put, normal, hr]
    funext c
    cases c <;> simp [v, r', put, normal]
  have hs := scan (compile M) Cell.S (by intro a b h; cases h; rfl)
    (by intro a; rfl) (put v (.F q) 1) (by intro a; simp [v, put, normal]) q
  have hmiddle : run (compile M) 2
      ⟨put v (.F q) 1, (compile M (.S q)).success⟩ =
      ⟨put (put v (.U q) 1) (.F q) 1, .dec (.F 0)⟩ := by
    simp [run, step, compile, put, v, normal]
    funext c
    cases c <;> simp [put, normal]
  have hf := scan (compile M) Cell.F (by intro a b h; cases h; rfl)
    (by intro a; rfl) (put v (.U q) 1) (by intro a; simp [v, put, normal]) q
  have hlast : run (compile M) 1
      ⟨put v (.U q) 1, (compile M (.F q)).success⟩ =
      ⟨v, entry M yes⟩ := by
    simp [run, step, compile, hq]
    simpa [v, normal] using put_self v (.U q)
  have h := run_join (compile M) hfirst
    (run_join (compile M) hs (run_join (compile M) hmiddle (run_join (compile M) hf hlast)))
  have hcost : 3 + (q.val + 1 + (2 + (q.val + 1 + 1))) = 2 * q.val + 8 := by omega
  rw [hcost] at h
  exact h

/-- The zero branch is symmetric: its failed data decrement leaves the source
zero intact, and the V counter remembers which failure continuation to enter. -/
theorem dec_zero_macro (M : Machine d n) (r : Fin (d + 1) → Nat)
    (q : Fin (n + 1)) (i : Fin (d + 1)) (yes no : Fin (n + 1))
    (hq : M.instruction q = .dec i yes no) (hr : r i = 0) :
    run (compile M) (2 * q.val + 8) ⟨normal r, entry M q⟩ =
      ⟨normal r, entry M no⟩ := by
  let v : Cell d n → Nat := normal r
  have hfirst : run (compile M) 3 ⟨normal r, entry M q⟩ =
      ⟨put (put v (.S q) 1) (.F q) 1, .dec (.F 0)⟩ := by
    simp [run, step, entry, hq, compile, put, normal, hr, v]
  have hf := scan (compile M) Cell.F (by intro a b h; cases h; rfl)
    (by intro a; rfl) (put v (.S q) 1) (by intro a; simp [v, put, normal]) q
  have hmiddle : run (compile M) 2
      ⟨put v (.S q) 1, (compile M (.F q)).success⟩ =
      ⟨put (put v (.V q) 1) (.S q) 1, .dec (.S 0)⟩ := by
    simp [run, step, compile, put, v, normal]
    funext c
    cases c <;> simp [put, normal]
  have hs := scan (compile M) Cell.S (by intro a b h; cases h; rfl)
    (by intro a; rfl) (put v (.V q) 1) (by intro a; simp [v, put, normal]) q
  have hlast : run (compile M) 1
      ⟨put v (.V q) 1, (compile M (.S q)).success⟩ =
      ⟨v, entry M no⟩ := by
    simp [run, step, compile, hq]
    simpa [v, normal] using put_self v (.V q)
  have h := run_join (compile M) hfirst
    (run_join (compile M) hf (run_join (compile M) hmiddle (run_join (compile M) hs hlast)))
  have hcost : 3 + (q.val + 1 + (2 + (q.val + 1 + 1))) = 2 * q.val + 8 := by omega
  rw [hcost] at h
  exact h

/-- Every instruction is simulated by a strictly positive, syntax-bounded block. -/
def macroCost (M : Machine d n) (s : SourceState d n) : Nat :=
  match M.instruction s.label with
  | .inc _ _ => s.label.val + 3
  | .dec _ _ _ => 2 * s.label.val + 8
  | .halt => 1

theorem macroCost_pos (M : Machine d n) (s : SourceState d n) :
    0 < macroCost M s := by
  unfold macroCost
  cases M.instruction s.label <;> simp_all <;> omega

theorem macro_simulation (M : Machine d n) (s : SourceState d n) :
    run (compile M) (macroCost M s) (encode M s) = encode M (sourceStep M s) := by
  cases s with
  | mk r q =>
    cases hq : M.instruction q with
    | inc i t => simpa [macroCost, encode, sourceStep, hq] using inc_macro M r q i t hq
    | dec i yes no =>
      by_cases hr : r i = 0
      · simpa [macroCost, encode, sourceStep, hq, hr] using dec_zero_macro M r q i yes no hq hr
      · simpa [macroCost, encode, sourceStep, hq, hr] using dec_success_macro M r q i yes no hq hr
    | halt => simp [macroCost, encode, sourceStep, entry, hq, step]

def sourceRun (M : Machine d n) : Nat → SourceState d n → SourceState d n
  | 0, s => s
  | k + 1, s => sourceRun M k (sourceStep M s)

/-- Runtime-dependent time change, used only to prove simulation, never to compile. -/
def elapsed (M : Machine d n) : Nat → SourceState d n → Nat
  | 0, _ => 0
  | k + 1, s => macroCost M s + elapsed M k (sourceStep M s)

theorem elapsed_ge (M : Machine d n) (k : Nat) (s : SourceState d n) :
    k ≤ elapsed M k s := by
  induction k generalizing s with
  | zero => simp [elapsed]
  | succ k ih =>
    have := ih (sourceStep M s)
    have := macroCost_pos M s
    simp only [elapsed]
    omega

/-- Arbitrarily long finite source runs agree exactly at instruction boundaries. -/
theorem run_simulation (M : Machine d n) (k : Nat) (s : SourceState d n) :
    run (compile M) (elapsed M k s) (encode M s) = encode M (sourceRun M k s) := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    simp only [elapsed, sourceRun, run_add, macro_simulation, ih]

@[simp] theorem entry_halt_iff (M : Machine d n) (q : Fin (n + 1)) :
    entry M q = .halt ↔ M.instruction q = .halt := by
  unfold entry
  cases M.instruction q <;> simp

/-- A halted target stays at precisely the same counter vector. -/
theorem run_after_halt (P : Table α) (s : State α) (k l : Nat)
    (h : (run P k s).action = .halt) : run P (k + l) s = run P k s := by
  rw [run_add]
  generalize he : run P k s = t at *
  cases t with
  | mk value action =>
    simp only [State.action] at h
    subst action
    exact run_halt P l value

/-- Halting in the middle of any macro cannot invent a source halt: the
strictly positive block lengths are cofinal, and halt is absorbing. -/
theorem halt_iff (M : Machine d n) (s : SourceState d n) :
    (∃ k, (run (compile M) k (encode M s)).action = .halt) ↔
    (∃ k, M.instruction (sourceRun M k s).label = .halt) := by
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have hge := elapsed_ge M k s
    have he : k + (elapsed M k s - k) = elapsed M k s := by omega
    have hstay := run_after_halt (compile M) (encode M s) k (elapsed M k s - k) hk
    rw [he, run_simulation] at hstay
    have ha := congrArg State.action hstay
    rw [hk] at ha
    exact (entry_halt_iff M _).mp ha
  · rintro ⟨k, hk⟩
    refine ⟨elapsed M k s, ?_⟩
    rw [run_simulation]
    exact (entry_halt_iff M _).mpr hk

/-- The same reverse argument preserves every register, not just the halt bit. -/
theorem halt_output (M : Machine d n) (s : SourceState d n) (k : Nat)
    (hk : (run (compile M) k (encode M s)).action = .halt) :
    (run (compile M) k (encode M s)).value = normal (sourceRun M k s).value ∧
    M.instruction (sourceRun M k s).label = .halt := by
  have hge := elapsed_ge M k s
  have he : k + (elapsed M k s - k) = elapsed M k s := by omega
  have hstay := run_after_halt (compile M) (encode M s) k (elapsed M k s - k) hk
  rw [he, run_simulation] at hstay
  constructor
  · exact (congrArg State.value hstay).symm
  · have ha := congrArg State.action hstay
    rw [hk] at ha
    exact (entry_halt_iff M _).mp ha

/-- The effective finite-input entry state is explicit and accepts every tuple. -/
def initial (M : Machine d n) (input : Fin (d + 1) → Nat) : SourceState d n :=
  ⟨input, M.entry⟩

theorem arbitrary_input_halt_iff (M : Machine d n) (input : Fin (d + 1) → Nat) :
    (∃ k, (run (compile M) k (encode M (initial M input))).action = .halt) ↔
    (∃ k, M.instruction (sourceRun M k (initial M input)).label = .halt) :=
  halt_iff M (initial M input)

end SOnlyMachine
