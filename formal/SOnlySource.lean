import SOnly38

/-!
# Exact source-word simulation for the fixed 38-phase CTS

The general FIFO lemma below consumes an arbitrary original front, keeping its
suffix in front of all appended words. The specialization uses the literal
UT19 production table from `SOnly38`, and proves statements uniformly in the
source queue, rather than enumerating bounded source configurations.

Symbols are represented by `Fin 19`; zero-based index `i` denotes published
label `i + 1`. Empty source states use the phase-toggling total extension,
matching the upstream CTS extension, which advances its phase on empty input.
Neither total extension generates a selected-head event on an empty word.
-/

namespace SOnlySource

open PureSFormal

set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

/-- Output appended while consuming a given original bit front. -/
def scan (P : CTS.Program) (q : CTS.Phase P) : List Bool → List Bool
  | [] => []
  | b :: bs => (if b then P.appendant q else []) ++ scan P (CTS.nextPhase P q) bs

theorem iteratePhase_next (P : CTS.Program) (n : Nat) (q : CTS.Phase P) :
    CTS.iteratePhase P n (CTS.nextPhase P q) =
      CTS.nextPhase P (CTS.iteratePhase P n q) := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [CTS.iteratePhase_succ] using congrArg (CTS.nextPhase P) ih

/-- The suffix may be arbitrary and empty: every original front bit is consumed
before any newly appended bit. -/
theorem consume_prefix (P : CTS.Program) (front suffix : List Bool)
    (q : CTS.Phase P) :
    CTS.iterate P front.length ⟨q, front ++ suffix⟩ =
      ⟨CTS.iteratePhase P front.length q, suffix ++ scan P q front⟩ := by
  induction front generalizing q suffix with
  | nil => simp [scan]
  | cons b bs ih =>
      rw [List.length_cons, CTS.iterate_add]
      cases b
      · simpa [scan, CTS.iterate, CTS.advance, iteratePhase_next] using
          ih suffix (CTS.nextPhase P q)
      · simpa [scan, CTS.iterate, CTS.advance, iteratePhase_next, List.append_assoc] using
          ih (suffix ++ P.appendant q) (CTS.nextPhase P q)

/-- At an interior offset, unconsumed original bits still precede the suffix
and every generated appendant. -/
theorem consume_partial (P : CTS.Program) (front suffix : List Bool)
    (q : CTS.Phase P) (n : Nat) (hn : n ≤ front.length) :
    CTS.iterate P n ⟨q, front ++ suffix⟩ =
      ⟨CTS.iteratePhase P n q, front.drop n ++ suffix ++ scan P q (front.take n)⟩ := by
  have h := consume_prefix P (front.take n) (front.drop n ++ suffix) q
  simpa only [List.length_take, Nat.min_eq_left hn, ← List.append_assoc,
    List.take_append_drop] using h

/-- An original prefix of length greater than `n` guarantees an ordinary step
at offset `n`, independently of the suffix and appendants. -/
theorem ordinary_exists_in_prefix (P : CTS.Program) (front suffix : List Bool)
    (q : CTS.Phase P) (n : Nat) (hn : n < front.length) :
    (CTS.ordinaryStep P (CTS.iterate P n ⟨q, front ++ suffix⟩)).isSome = true := by
  rw [consume_partial P front suffix q n (Nat.le_of_lt hn)]
  rw [List.drop_eq_getElem_cons hn]
  cases front[n] <;> simp [CTS.ordinaryStep]

abbrev Symbol := Fin 19

/-- A zero-based source symbol is encoded by the literal published one-hot code. -/
def code (symbol : Symbol) : List Bool := SOnly38.oneHot (symbol.val + 1)

def encodeWord (word : List Symbol) : List Bool := word.flatMap code

/-- Read the fixed literal table; the theorem below checks the index conversion. -/
def production (symbol : Symbol) : List Symbol :=
  ((SOnly38.productions[symbol.val]?).getD []).map
    (fun label => ⟨(label - 1) % 19, by omega⟩)

theorem production_matches_published : ∀ symbol : Symbol,
    (production symbol).map (fun x => x.val + 1) =
      (SOnly38.productions[symbol.val]?).getD [] := by decide

structure Config where
  word : List Symbol
  take : Bool
  deriving DecidableEq, Repr

/-- Alternating one-symbol deletion, with take=false denoting skip.
An empty word remains empty while its phase toggles, solely for total iteration. -/
def step (config : Config) : Config :=
  match config.word with
  | [] => ⟨[], !config.take⟩
  | symbol :: tail => ⟨tail ++ (if config.take then production symbol else []), !config.take⟩

def iterate : Nat → Config → Config
  | 0, c => c
  | n + 1, c => step (iterate n c)

def boundaryPhase (take : Bool) : CTS.Phase SOnly38.program :=
  if take then ⟨0, by decide⟩ else ⟨19, by decide⟩

def encode (config : Config) : CTS.Config SOnly38.program :=
  ⟨boundaryPhase config.take, encodeWord config.word⟩

@[simp] theorem code_length (symbol : Symbol) : (code symbol).length = 19 := by
  simp [code, SOnly38.oneHot]

@[simp] theorem encodeWord_nil : encodeWord [] = [] := rfl

@[simp] theorem encodeWord_cons (symbol : Symbol) (tail : List Symbol) :
    encodeWord (symbol :: tail) = code symbol ++ encodeWord tail := rfl

@[simp] theorem encodeWord_append (left right : List Symbol) :
    encodeWord (left ++ right) = encodeWord left ++ encodeWord right := by
  simp [encodeWord]

/-- The only finite table computation in the block proof: both phases and
all 19 heads, with no bound on the following queue. -/
theorem scan_code : ∀ (take : Bool) (symbol : Symbol),
    scan SOnly38.program (boundaryPhase take) (code symbol) =
      encodeWord (if take then production symbol else []) := by decide +kernel

theorem phase_block : ∀ take : Bool,
    CTS.iteratePhase SOnly38.program 19 (boundaryPhase take) = boundaryPhase (!take) := by decide +kernel

/-- Every source microstep is exactly 19 CTS steps. This includes empty input
under the two explicitly matched phase-advancing total extensions. -/
theorem step_simulation (config : Config) :
    CTS.iterate SOnly38.program 19 (encode config) = encode (step config) := by
  cases config with
  | mk word take =>
    cases word with
    | nil =>
      change CTS.iterate SOnly38.program 19 ⟨boundaryPhase take, []⟩ =
        ⟨boundaryPhase (!take), []⟩
      rw [CTS.iterate_empty, phase_block]
    | cons symbol tail =>
      have h := consume_prefix SOnly38.program (code symbol) (encodeWord tail) (boundaryPhase take)
      simpa only [encode, step, encodeWord_cons, encodeWord_append, code_length,
        scan_code, phase_block] using h

/-- Exact uniform trajectory agreement at all source boundaries. -/
theorem trajectory_simulation (n : Nat) (config : Config) :
    CTS.iterate SOnly38.program (19 * n) (encode config) = encode (iterate n config) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.mul_add, Nat.mul_one, Nat.add_comm (19 * n) 19, CTS.iterate_add, ih]
    exact step_simulation (iterate n config)

/-- The original 19-bit head block prevents premature CTS exhaustion. -/
theorem ordinary_at_offset (symbol : Symbol) (tail : List Symbol) (take : Bool)
    (offset : Nat) (hoffset : offset < 19) :
    (CTS.ordinaryStep SOnly38.program
      (CTS.iterate SOnly38.program offset (encode ⟨symbol :: tail, take⟩))).isSome = true := by
  exact ordinary_exists_in_prefix SOnly38.program (code symbol) (encodeWord tail)
    (boundaryPhase take) offset (by simpa using hoffset)

/-- A source selected-production event is about the head and the take phase. -/
def Selected (config : Config) : Prop :=
  config.take = true ∧ config.word.head? = some (⟨17, by decide⟩ : Symbol)

/-- The exact CTS pre-transition observation used for published symbol 18. -/
def Event (config : CTS.Config SOnly38.program) : Prop :=
  config.phase = SOnly38.targetPhase ∧ config.data.head? = some true

private theorem head_append_nonempty {α : Type} (front tail : List α)
    (h : front ≠ []) : (front ++ tail).head? = front.head? := by
  cases front with
  | nil => exact False.elim (h rfl)
  | cons a as => rfl

/-- Interior phases have no wrap until the final skip bit is consumed. -/
theorem phase_at_offset (take : Bool) (offset : Fin 19) :
    (CTS.iteratePhase SOnly38.program offset.val (boundaryPhase take)).val =
      if take then offset.val else 19 + offset.val := by
  rw [CTS.iteratePhase_val]
  have hoffset := offset.isLt
  cases take with
  | false =>
    change (19 + offset.val) % 38 = 19 + offset.val
    exact Nat.mod_eq_of_lt (by omega)
  | true =>
    change (0 + offset.val) % 38 = offset.val
    rw [Nat.zero_add]
    exact Nat.mod_eq_of_lt (by omega)

/-- An original one-hot block has its leading one precisely at its symbol index. -/
theorem code_head_at_offset (symbol offset : Fin 19) :
    ((code symbol).drop offset.val).head? = some (decide (offset.val = symbol.val)) := by
  rw [List.drop_eq_getElem_cons (by simp)]
  simp [code, SOnly38.oneHot]

/-- Every event inside a block occurs exactly at offset 17 and comes from a
selected source symbol 18; skipped 18s cannot signal. -/
theorem event_in_block (config : Config) (offset : Fin 19) :
    Event (CTS.iterate SOnly38.program offset.val (encode config)) ↔
      Selected config ∧ offset.val = 17 := by
  cases config with
  | mk word take =>
    cases word with
    | nil => simp [encode, CTS.iterate_empty, Event, Selected]
    | cons symbol tail =>
      rw [show encode ⟨symbol :: tail, take⟩ =
        ⟨boundaryPhase take, code symbol ++ encodeWord tail⟩ from rfl]
      rw [consume_partial SOnly38.program (code symbol) (encodeWord tail)
        (boundaryPhase take) offset.val (by simp)]
      have hdrop : (code symbol).drop offset.val ≠ [] := by
        intro h
        have hlen := congrArg List.length h
        simp only [List.length_drop, code_length, List.length_nil] at hlen
        have := offset.isLt
        omega
      simp only [Event]
      rw [List.append_assoc, head_append_nonempty _ _ hdrop, code_head_at_offset]
      rw [Fin.ext_iff, phase_at_offset]
      simp only [SOnly38.targetPhase, Option.some.injEq, decide_eq_true_eq,
        Selected, List.head?_cons]
      cases take <;> simp only [Bool.false_eq_true, false_and, ↓reduceIte,
        true_and, Fin.ext_iff]
      · constructor
        · intro h
          omega
        · intro h
          exact h.elim
      · omega

/-- Exact event transfer at arbitrary source microstep and arbitrary block offset. -/
theorem event_at_time (n : Nat) (config : Config) (offset : Fin 19) :
    Event (CTS.iterate SOnly38.program (19 * n + offset.val) (encode config)) ↔
      Selected (iterate n config) ∧ offset.val = 17 := by
  rw [Nat.add_comm, CTS.iterate_add, trajectory_simulation]
  exact event_in_block (iterate n config) offset

/-- No event is missed by inspecting source blocks: this quantifies over every
CTS prestate index, not just an index already known to have a block form. -/
theorem event_at_arbitrary_time (time : Nat) (config : Config) :
    Event (CTS.iterate SOnly38.program time (encode config)) ↔
      Selected (iterate (time / 19) config) ∧ time % 19 = 17 := by
  have h := event_at_time (time / 19) config ⟨time % 19, Nat.mod_lt _ (by decide)⟩
  simpa only [Nat.div_add_mod] using h

/-- Existence of the designated source event is exactly existence of the CTS event. -/
theorem event_exists_iff (config : Config) :
    (∃ time, Event (CTS.iterate SOnly38.program time (encode config))) ↔
      ∃ n, Selected (iterate n config) := by
  constructor
  · rintro ⟨time, h⟩
    exact ⟨time / 19, ((event_at_arbitrary_time time config).mp h).1⟩
  · rintro ⟨n, h⟩
    exact ⟨19 * n + 17, (event_at_time n config ⟨17, by decide⟩).mpr ⟨h, rfl⟩⟩

/-- A first source event at `n` yields the first CTS event at exactly `19*n+17`. -/
theorem first_event_exact (config : Config) (n : Nat)
    (selected : Selected (iterate n config))
    (earlier : ∀ j, j < n → ¬Selected (iterate j config)) :
    Event (CTS.iterate SOnly38.program (19 * n + 17) (encode config)) ∧
      ∀ time, time < 19 * n + 17 →
        ¬Event (CTS.iterate SOnly38.program time (encode config)) := by
  constructor
  · exact (event_at_time n config ⟨17, by decide⟩).mpr ⟨selected, rfl⟩
  · intro time htime hevent
    obtain ⟨hselected, hmod⟩ := (event_at_arbitrary_time time config).mp hevent
    have hdiv := Nat.div_add_mod time 19
    exact earlier (time / 19) (by omega) hselected

end SOnlySource

#print axioms SOnlySource.consume_prefix
#print axioms SOnlySource.consume_partial
#print axioms SOnlySource.ordinary_exists_in_prefix
#print axioms SOnlySource.production_matches_published
#print axioms SOnlySource.scan_code
#print axioms SOnlySource.step_simulation
#print axioms SOnlySource.trajectory_simulation

#print axioms SOnlySource.ordinary_at_offset
#print axioms SOnlySource.phase_at_offset
#print axioms SOnlySource.code_head_at_offset
#print axioms SOnlySource.event_in_block
#print axioms SOnlySource.event_at_time

#print axioms SOnlySource.event_at_arbitrary_time
#print axioms SOnlySource.event_exists_iff
#print axioms SOnlySource.first_event_exact
