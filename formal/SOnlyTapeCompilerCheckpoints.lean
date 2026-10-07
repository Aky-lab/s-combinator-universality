import SOnlyMachine
import StackMacros
import SOnlyTapeStacks

/-!
Exact halting reflection for a partial source semantics compiled to a literal
register machine. Only positive-time single-step simulation and agreement of
halt instructions at encoded boundaries are assumed. A finite source prefix
either terminates or supplies a checkpoint at least as late as its length.
Consequently an internal register-machine halt cannot escape observation.
-/
namespace SOnlyTapeCompilerCheckpoints

open SOnlyMachine SOnlyStack

universe u
variable {α : Type u} {d n : Nat}

/-- A halt instruction fixes the entire register-machine configuration. -/
theorem sourceStep_halt (M : Machine d n) (s : SourceState d n)
    (halted : M.instruction s.label = .halt) : sourceStep M s = s := by
  simp [sourceStep, halted]

/-- Halting configurations remain fixed for every finite number of microsteps. -/
theorem sourceRun_halt (M : Machine d n) (s : SourceState d n)
    (halted : M.instruction s.label = .halt) (k : Nat) : sourceRun M k s = s := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [sourceRun, sourceStep_halt M s halted] using ih

/-- Once a run halts, every later microstep has exactly the same configuration. -/
theorem sourceRun_after_halt (M : Machine d n) (s : SourceState d n)
    (t : Nat) (halted : M.instruction (sourceRun M t s).label = .halt)
    (elapsed : Nat) (later : t ≤ elapsed) :
    sourceRun M elapsed s = sourceRun M t s := by
  have split : elapsed = t + (elapsed - t) := by omega
  rw [split, sourceRun_add]
  exact sourceRun_halt M _ halted _

/-- Any two halting observations on one deterministic run are the same full
configuration, irrespective of which halting time is earlier. -/
theorem sourceRun_halts_equal (M : Machine d n) (s : SourceState d n)
    (t u : Nat)
    (halt_t : M.instruction (sourceRun M t s).label = .halt)
    (halt_u : M.instruction (sourceRun M u s).label = .halt) :
    sourceRun M t s = sourceRun M u s := by
  by_cases h : t ≤ u
  · exact (sourceRun_after_halt M s t halt_t u h).symm
  · exact sourceRun_after_halt M s u halt_u t (by omega)

/-- Constructive finite-prefix dichotomy: termination before the requested
length, or a configuration reached after exactly that many source steps. -/
theorem partial_run_cases (f : α → Option α) (k : Nat) (a : α) :
    (∃ j, j < k ∧ SOnlyTapeStacks.HaltsAfter f j a) ∨
    ∃ b, SOnlyTapeStacks.run f k a = some b := by
  induction k generalizing a with
  | zero => exact Or.inr ⟨a, rfl⟩
  | succ k ih =>
    cases hstep : f a with
    | none =>
      exact Or.inl ⟨0, by omega, a, rfl, hstep⟩
    | some b =>
      rcases ih b with ⟨j, hj, c, hc, halted⟩ | ⟨c, hc⟩
      · exact Or.inl ⟨j + 1, by omega, c,
          by simpa only [SOnlyTapeStacks.run, hstep, Option.bind_some] using hc,
          halted⟩
      · exact Or.inr ⟨c,
          by simpa only [SOnlyTapeStacks.run, hstep, Option.bind_some] using hc⟩

/-- Every finite successful source run has an actual register-machine
checkpoint, with cumulative microstep count at least the source-step count. -/
theorem simulate_run (f : α → Option α) (E : α → SourceState d n)
    (M : Machine d n)
    (implements : ∀ a b, f a = some b →
      ∃ duration, 0 < duration ∧ sourceRun M duration (E a) = E b)
    (k : Nat) (a b : α) (runs : SOnlyTapeStacks.run f k a = some b) :
    ∃ elapsed, k ≤ elapsed ∧ sourceRun M elapsed (E a) = E b := by
  induction k generalizing a with
  | zero =>
    have hab : a = b := Option.some.inj runs
    exact ⟨0, Nat.le_refl 0, congrArg E hab⟩
  | succ k ih =>
    cases hstep : f a with
    | none => simp [SOnlyTapeStacks.run, hstep] at runs
    | some c =>
      have rest : SOnlyTapeStacks.run f k c = some b := by
        simpa only [SOnlyTapeStacks.run, hstep, Option.bind_some] using runs
      obtain ⟨duration, positive, executes⟩ := implements a c hstep
      obtain ⟨elapsed, lower, simulates⟩ := ih c rest
      refine ⟨duration + elapsed, by omega, ?_⟩
      rw [sourceRun_add, executes, simulates]

/-- If a target halt is reached after `t` microsteps, a source halt occurs
after at most `t` source transitions. This excludes premature internal halts. -/
theorem reflects_halt_bounded (f : α → Option α) (E : α → SourceState d n)
    (M : Machine d n)
    (implements : ∀ a b, f a = some b →
      ∃ duration, 0 < duration ∧ sourceRun M duration (E a) = E b)
    (boundary_halt : ∀ a, M.instruction (E a).label = .halt ↔ f a = none)
    (a : α) (t : Nat)
    (halted : M.instruction (sourceRun M t (E a)).label = .halt) :
    ∃ k, k ≤ t ∧ SOnlyTapeStacks.HaltsAfter f k a := by
  rcases partial_run_cases f t a with ⟨k, hk, hhalts⟩ | ⟨b, hruns⟩
  · exact ⟨k, by omega, hhalts⟩
  · obtain ⟨elapsed, lower, executes⟩ := simulate_run f E M implements t a b hruns
    have same : E b = sourceRun M t (E a) :=
      executes.symm.trans (sourceRun_after_halt M (E a) t halted elapsed lower)
    refine ⟨t, Nat.le_refl t, b, hruns, (boundary_halt b).mp ?_⟩
    rw [same]
    exact halted

/-- Exact cofinal-checkpoint halting equivalence, from local premises alone. -/
theorem halting_iff (f : α → Option α) (E : α → SourceState d n)
    (M : Machine d n)
    (implements : ∀ a b, f a = some b →
      ∃ duration, 0 < duration ∧ sourceRun M duration (E a) = E b)
    (boundary_halt : ∀ a, M.instruction (E a).label = .halt ↔ f a = none)
    (a : α) :
    (∃ t, M.instruction (sourceRun M t (E a)).label = .halt) ↔
    ∃ k, SOnlyTapeStacks.HaltsAfter f k a := by
  constructor
  · rintro ⟨t, halted⟩
    obtain ⟨k, _, hhalts⟩ := reflects_halt_bounded f E M implements boundary_halt a t halted
    exact ⟨k, hhalts⟩
  · rintro ⟨k, b, hruns, halted⟩
    obtain ⟨elapsed, _, executes⟩ := simulate_run f E M implements k a b hruns
    refine ⟨elapsed, ?_⟩
    rw [executes]
    exact (boundary_halt b).mpr halted

/-- Reflection recovers the exact final encoded state, not merely the
existence of some source halt. The reflected source time is bounded by the
observed microstep time. -/
theorem reflects_halt_state (f : α → Option α) (E : α → SourceState d n)
    (M : Machine d n)
    (implements : ∀ a b, f a = some b →
      ∃ duration, 0 < duration ∧ sourceRun M duration (E a) = E b)
    (boundary_halt : ∀ a, M.instruction (E a).label = .halt ↔ f a = none)
    (a : α) (t : Nat)
    (halted : M.instruction (sourceRun M t (E a)).label = .halt) :
    ∃ k b, k ≤ t ∧ SOnlyTapeStacks.run f k a = some b ∧ f b = none ∧
      E b = sourceRun M t (E a) := by
  obtain ⟨k, lower, b, hruns, hb⟩ :=
    reflects_halt_bounded f E M implements boundary_halt a t halted
  obtain ⟨elapsed, _, executes⟩ := simulate_run f E M implements k a b hruns
  have boundary : M.instruction (sourceRun M elapsed (E a)).label = .halt := by
    rw [executes]
    exact (boundary_halt b).mpr hb
  exact ⟨k, b, lower, hruns, hb,
    executes.symm.trans (sourceRun_halts_equal M (E a) elapsed t boundary halted)⟩

/-- Every boundary-aligned numerical observable is preserved and reflected
at termination, including target observations between source checkpoints. -/
theorem result_iff (f : α → Option α) (E : α → SourceState d n)
    (M : Machine d n)
    (implements : ∀ a b, f a = some b →
      ∃ duration, 0 < duration ∧ sourceRun M duration (E a) = E b)
    (boundary_halt : ∀ a, M.instruction (E a).label = .halt ↔ f a = none)
    (outA : α → Nat) (outB : SourceState d n → Nat)
    (boundary_result : ∀ a, outB (E a) = outA a)
    (a : α) (r : Nat) :
    (∃ t, M.instruction (sourceRun M t (E a)).label = .halt ∧
      outB (sourceRun M t (E a)) = r) ↔
    ∃ k b, SOnlyTapeStacks.run f k a = some b ∧ f b = none ∧ outA b = r := by
  constructor
  · rintro ⟨t, halted, result⟩
    obtain ⟨k, b, _, hruns, hb, same⟩ :=
      reflects_halt_state f E M implements boundary_halt a t halted
    refine ⟨k, b, hruns, hb, ?_⟩
    rw [← boundary_result b, same]
    exact result
  · rintro ⟨k, b, hruns, halted, result⟩
    obtain ⟨elapsed, _, executes⟩ := simulate_run f E M implements k a b hruns
    refine ⟨elapsed, ?_, ?_⟩
    · rw [executes]
      exact (boundary_halt b).mpr halted
    · rw [executes, boundary_result b, result]

end SOnlyTapeCompilerCheckpoints

#print axioms SOnlyTapeCompilerCheckpoints.partial_run_cases
#print axioms SOnlyTapeCompilerCheckpoints.simulate_run
#print axioms SOnlyTapeCompilerCheckpoints.reflects_halt_bounded
#print axioms SOnlyTapeCompilerCheckpoints.halting_iff
#print axioms SOnlyTapeCompilerCheckpoints.reflects_halt_state
#print axioms SOnlyTapeCompilerCheckpoints.result_iff
