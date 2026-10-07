import SOnlyGeneratedOrigins
import PureSFormal.PureS.SchedulerNestedPhase
import PureSFormal.PureS.SchedulerJobHandoff
import PureSFormal.PureS.SchedulerAllStages

/-! Generated CLOCK/FUEL and outer-parent license preservation.
The literal sample lists are checked against their actual pinned definitions.
This file does not assume that an arbitrary CompletedParents certificate
contains only previously generated event origins. -/
namespace SOnlySchedulerOrigins
open PureSFormal PureSFormal.PureS SOnlyProvenance SOnlyProvenanceRows SOnlyGeneratedOrigins
open SchedulerControl SchedulerInvariant SchedulerNestedPhase
set_option maxHeartbeats 3000000

theorem allH6_mono {P Q : Term → Prop} (mono : ∀ term, P term → Q term)
    {term : Term} (licensed : AllH6 P term) : AllH6 Q term := by
  induction term with
  | s => trivial
  | app left right ihl ihr =>
      exact ⟨ihl licensed.1, ihr licensed.2.1, fun root => mono _ (licensed.2.2 root)⟩

/-- A generated outer zipper can wrap every certified whole endpoint. -/
def Wraps (P : Term → Prop) (parents : List ParentFrame) : Prop :=
  ∀ endpoint, Endpoint endpoint → AllH6 P endpoint → AllH6 P (Cursor.rebuild parents endpoint)

theorem wraps_nil (P : Term → Prop) : Wraps P [] := by
  intro t _ h
  exact h

theorem wraps_left {P : Term → Prop} {parents : List ParentFrame} {audit : Term}
    (outer : Wraps P parents) (ha : AllH6 P audit) : Wraps P (.left audit :: parents) := by
  intro t endpoint ht
  have extended := endpoint_extension ht ha endpoint
  exact outer _ (Or.inl extended.2) extended.1

theorem wraps_right {P : Term → Prop} {parents : List ParentFrame} {head : Term}
    (outer : Wraps P parents) (hh : AllH6 P head) (hc : classify head = .other) :
    Wraps P (.right head :: parents) := by
  intro t _ ht
  exact outer _ (Or.inl (other_app_class hc)) (other_app_carries hh ht hc)

abbrev Ordinary (P : Term → Prop) (term : Term) := AllH6 P term ∧ classify term = .other

theorem ordinary_app {P : Term → Prop} {head arg : Term}
    (hh : Ordinary P head) (ha : AllH6 P arg) : Ordinary P (.app head arg) :=
  ⟨other_app_carries hh.1 ha hh.2, other_app_class hh.2⟩

theorem ordinary_s_pair {P : Term → Prop} {first second : Term}
    (hf : Ordinary P first) (hs : AllH6 P second) : Ordinary P (.app (.app .s first) second) :=
  ⟨s_pair_carries hf.1 hs, by simp [classify, hf.2, delta]⟩

theorem ordinary_b_app {P : Term → Prop} {arg : Term} (h : Ordinary P arg) :
    Ordinary P (.app b arg) :=
  ⟨app_no_new (b_carries P) h.1 (by decide), by simp [b, classify, h.2, delta]⟩

theorem C_ordinary (P : Term → Prop) (n : Nat) : Ordinary P (C n) := by
  induction n with
  | zero => exact ⟨by simp [C, b, AllH6, classify, delta], classify_C 0⟩
  | succ n ih => exact ordinary_b_app ih

theorem environment_ordinary (P : Term → Prop) (program : CTS.Program)
    (dispatcher : ActionDispatcher program) (bits : List Bool) :
    Ordinary P (environmentCode (compileActions program dispatcher.tree) bits) :=
  ⟨environment_carries P program dispatcher.tree bits, classify_environment _ _⟩

theorem clockWrappers_ordinary (P : Term → Prop) (n r : Nat) : Ordinary P (clockWrappers n r) := by
  induction r with
  | zero => exact ordinary_app (C_ordinary P _) (C_ordinary P _).1
  | succ r ih => exact ordinary_s_pair (C_ordinary P n) ih.1

theorem clockExit_ordinary {P : Term → Prop} (n r : Nat) {environment : Term}
    (he : AllH6 P environment) : Ordinary P (Dovetail.clockExit n r environment) :=
  ordinary_app (clockWrappers_ordinary P n r) he

theorem base_ordinary {P : Term → Prop} {environment continuation : Term}
    (he : Ordinary P environment) (hb : Ordinary P continuation) :
    Ordinary P (baseCarrier environment continuation) := by
  have be := ordinary_b_app he
  have alpha := ordinary_app (ordinary_app he be.1) hb.1
  have beta := ordinary_app (ordinary_app he hb.1) alpha.1
  exact ordinary_app (ordinary_app hb alpha.1) beta.1

theorem pending_wraps {P : Term → Prop} (program : CTS.Program)
    (dispatcher : ActionDispatcher program) (bits : List Bool) {continuation : Term}
    (hb : AllH6 P continuation) {parents : List ParentFrame} (outer : Wraps P parents)
    (depth : Nat) :
    Wraps P (PrimitiveFuel.pendingParents
      (environmentCode (compileActions program dispatcher.tree) bits) continuation depth parents) := by
  induction depth generalizing parents with
  | zero => exact outer
  | succ depth ih =>
      apply ih
      exact wraps_right outer
        (other_app_carries (environment_carries P program dispatcher.tree bits) hb (classify_environment _ _))
        (other_app_class (classify_environment _ _))

theorem clock_wrappers_wraps {P : Term → Prop} {parents : List ParentFrame}
    (outer : Wraps P parents) (stage wrappers : Nat) :
    Wraps P (PrimitiveClock.wrapperParents stage wrappers parents) := by
  induction wrappers generalizing parents with
  | zero => exact outer
  | succ wrappers ih =>
      apply ih
      exact wraps_right outer (s_one_carries (C_ordinary P stage).1)
        (by simp [classify, delta])

/-- Every positive CLOCK contraction, below its actual environment boundary. -/
theorem positive_clock_licensed {P : Term → Prop} (program : CTS.Program)
    (dispatcher : ActionDispatcher program) (bits : List Bool) (registers : Registers program)
    (stage wrappers remaining : Nat) {parents : List ParentFrame} (outer : Wraps P parents) :
    AllH6 P (positiveClockMutationConfiguration program dispatcher registers stage wrappers remaining
      (.left (environmentCode (compileActions program dispatcher.tree) bits) :: parents)).cursor.erase := by
  have endpoint := ordinary_s_pair (C_ordinary P stage)
    (ordinary_app (C_ordinary P remaining) (C_ordinary P stage).1).1
  exact clock_wrappers_wraps (wraps_left outer (environment_carries P program dispatcher.tree bits))
    stage wrappers _ (Or.inl endpoint.2) endpoint.1

/-- The closing zero-CLOCK sample uses the same literal wrapper stack. -/
theorem zero_clock_licensed {P : Term → Prop} (program : CTS.Program)
    (dispatcher : ActionDispatcher program) (bits : List Bool) (registers : Registers program)
    (stage wrappers : Nat) {parents : List ParentFrame} (outer : Wraps P parents) :
    AllH6 P (zeroClockMutationConfiguration program dispatcher registers stage wrappers
      (.left (environmentCode (compileActions program dispatcher.tree) bits) :: parents)).cursor.erase := by
  have endpoint := ordinary_app (C_ordinary P (stage + 1)) (C_ordinary P (stage + 1)).1
  exact clock_wrappers_wraps (wraps_left outer (environment_carries P program dispatcher.tree bits))
    stage wrappers _ (Or.inl endpoint.2) endpoint.1

/-- All seven actual native FUEL residual forms, uniformly in their old holes. -/
theorem fuel_rows_licensed {P : Term → Prop} (program : CTS.Program)
    (dispatcher : ActionDispatcher program) (registers : Registers program)
    (fuel : Nat) {environment continuation : Term} {parents : List ParentFrame}
    (he : Ordinary P environment) (hb : Ordinary P continuation) (outer : Wraps P parents) :
    AllH6 P (fuelPositiveFirstMutationConfiguration program dispatcher registers fuel environment continuation parents).cursor.erase ∧
    AllH6 P (fuelPositiveSecondMutationConfiguration program dispatcher registers fuel environment continuation parents).cursor.erase ∧
    AllH6 P (fuelZeroFirstMutationConfiguration program dispatcher registers environment continuation parents).cursor.erase ∧
    AllH6 P (fuelZeroSecondMutationConfiguration program dispatcher registers environment continuation parents).cursor.erase ∧
    AllH6 P (fuelZeroThirdMutationConfiguration program dispatcher registers environment continuation parents).cursor.erase ∧
    AllH6 P (fuelZeroFourthMutationConfiguration program dispatcher registers environment continuation parents).cursor.erase ∧
    AllH6 P (fuelZeroFifthMutationConfiguration program dispatcher registers environment continuation parents).cursor.erase := by
  have ce := ordinary_app (C_ordinary P fuel) he.1
  have ceb := ordinary_app ce hb.1
  have eb := ordinary_app he hb.1
  have be := ordinary_b_app he
  have ebe := ordinary_app he be.1
  have alpha := ordinary_app ebe hb.1
  have r1 := ordinary_s_pair he ce.1
  have r2 := ordinary_app eb ceb.1
  have z1 := ordinary_app be be.1
  have z2 := ordinary_s_pair be ebe.1
  have z3 := ordinary_app (ordinary_app be hb.1) alpha.1
  have z4 := ordinary_s_pair hb eb.1
  have z5 := base_ordinary he hb
  exact ⟨wraps_left outer hb.1 _ (Or.inl r1.2) r1.1,
    outer _ (Or.inl r2.2) r2.1,
    wraps_left outer hb.1 _ (Or.inl z1.2) z1.1,
    wraps_left outer hb.1 _ (Or.inl z2.2) z2.1,
    outer _ (Or.inl z3.2) z3.1,
    wraps_left outer alpha.1 _ (Or.inl z4.2) z4.1,
    outer _ (Or.inl z5.2) z5.1⟩

/-- Pointwise property of the actual ordered contraction sample lists. -/
def SamplesLicensed (P : Term → Prop) {program : CTS.Program}
    {dispatcher : ActionDispatcher program}
    (samples : List (SchedulerInvariant.Configuration program dispatcher)) : Prop :=
  ∀ sample ∈ samples, AllH6 P sample.cursor.erase

theorem fuel_list_licensed {P : Term → Prop} (program : CTS.Program)
    (dispatcher : ActionDispatcher program) (bits : List Bool) (registers : Registers program)
    (continuation : Term) (hb : Ordinary P continuation)
    (parents : List ParentFrame) (outer : Wraps P parents) (fuel depth : Nat) :
    SamplesLicensed P (fuelConfigurationsAt program dispatcher bits registers continuation parents fuel depth) := by
  induction fuel generalizing depth with
  | zero =>
      have rows := fuel_rows_licensed program dispatcher registers 0
        (environment_ordinary P program dispatcher bits) hb
        (pending_wraps program dispatcher bits hb.1 outer depth)
      intro sample member
      simp only [fuelConfigurationsAt, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with h | h | h | h | h <;> subst sample
      · exact rows.2.2.1
      · exact rows.2.2.2.1
      · exact rows.2.2.2.2.1
      · exact rows.2.2.2.2.2.1
      · exact rows.2.2.2.2.2.2
  | succ fuel ih =>
      have rows := fuel_rows_licensed program dispatcher registers fuel
        (environment_ordinary P program dispatcher bits) hb
        (pending_wraps program dispatcher bits hb.1 outer depth)
      intro sample member
      simp only [fuelConfigurationsAt, List.mem_cons] at member
      rcases member with h | h | later
      · subst sample; exact rows.1
      · subst sample; exact rows.2.1
      · exact ih (depth + 1) sample later

theorem clock_tail_licensed {P : Term → Prop} (program : CTS.Program)
    (dispatcher : ActionDispatcher program) (bits : List Bool) (registers : Registers program)
    (stage : Nat) (parents : List ParentFrame) (outer : Wraps P parents) (wrappers remaining : Nat) :
    SamplesLicensed P (clockTailConfigurationsAt program dispatcher bits registers stage parents wrappers remaining) := by
  induction remaining generalizing wrappers with
  | zero =>
      intro sample member
      simp only [clockTailConfigurationsAt, List.mem_singleton] at member
      subst sample
      exact zero_clock_licensed program dispatcher bits registers stage (wrappers + 1) outer
  | succ remaining ih =>
      intro sample member
      simp only [clockTailConfigurationsAt, List.mem_cons] at member
      rcases member with eq | later
      · subst sample
        exact positive_clock_licensed program dispatcher bits registers stage (wrappers + 1) remaining outer
      · exact ih (wrappers + 1) sample later

theorem clock_list_licensed {P : Term → Prop} (program : CTS.Program)
    (dispatcher : ActionDispatcher program) (bits : List Bool) (registers : Registers program)
    (parents : List ParentFrame) (outer : Wraps P parents) (stage : Nat) :
    SamplesLicensed P (clockConfigurationsAt program dispatcher bits registers parents stage) := by
  intro sample member
  simp only [clockConfigurationsAt, List.mem_cons] at member
  rcases member with eq | later
  · subst sample
    exact positive_clock_licensed program dispatcher bits registers (stage + 1) 0 stage outer
  · exact clock_tail_licensed program dispatcher bits registers (stage + 1) parents outer 0 stage sample later

/-- Actual clock-launch-fuel block of a positive stage. -/
theorem phase_list_licensed {P : Term → Prop} (program : CTS.Program)
    (dispatcher : ActionDispatcher program) (bits : List Bool) (registers : Registers program)
    (parents : List ParentFrame) (outer : Wraps P parents) (fuel : Nat) :
    SamplesLicensed P (positiveStageConfigurationsAt program dispatcher bits registers parents fuel) := by
  let environment := environmentCode (compileActions program dispatcher.tree) bits
  have he : Ordinary P environment := environment_ordinary P program dispatcher bits
  have hb := clockExit_ordinary (fuel + 1) fuel he.1
  have launch := ordinary_app (ordinary_app (C_ordinary P (fuel + 1)) he.1) hb.1
  intro sample member
  rcases List.mem_append.mp member with clock | rest
  · exact clock_list_licensed program dispatcher bits registers parents outer fuel sample clock
  · rcases List.mem_cons.mp rest with same | later
    · subst sample
      exact outer _ (Or.inl launch.2) launch.1
    · exact fuel_list_licensed program dispatcher bits (Registers.newJob program) _ hb parents outer
        (fuel + 1) 0 sample later

/-- Actual inter-job launch plus complete fuel sample list. -/
theorem handoff_list_licensed {P : Term → Prop} (program : CTS.Program)
    (dispatcher : ActionDispatcher program) (bits : List Bool) (fuel count : Nat)
    (parents : List ParentFrame) (outer : Wraps P parents) :
    SamplesLicensed P (SchedulerJobHandoff.handoffFuelConfigurationsAt program dispatcher bits fuel count parents) := by
  let environment := environmentCode (compileActions program dispatcher.tree) bits
  have he : Ordinary P environment := environment_ordinary P program dispatcher bits
  have hb := clockExit_ordinary (fuel + 1) count he.1
  have launch := ordinary_app (ordinary_app (C_ordinary P (fuel + 1)) he.1) hb.1
  intro sample member
  rcases List.mem_cons.mp member with same | later
  · subst sample
    exact outer _ (Or.inl launch.2) launch.1
  · exact fuel_list_licensed program dispatcher bits (Registers.newJob program) _ hb parents outer
      (fuel + 1) 0 sample later

/-- The literal initial tree is licensed for every origin predicate. -/
theorem initial_licensed (P : Term → Prop) (program : CTS.Program)
    (dispatcher : ActionDispatcher program) (bits : List Bool) :
    AllH6 P (SchedulerControl.initialConfiguration program dispatcher bits).cursor.erase :=
  (ordinary_app (ordinary_app (C_ordinary P 0) (C_ordinary P 0).1)
    (environment_carries P program dispatcher.tree bits)).1

/-- The unique generator staging contraction creates no completed Local. -/
theorem prelude_list_licensed (P : Term → Prop) (program : CTS.Program)
    (dispatcher : ActionDispatcher program) (bits : List Bool) :
    SamplesLicensed P (SchedulerRecurrence.initialPreludeConfigurations program dispatcher bits) := by
  intro sample member
  have same := List.mem_singleton.mp member
  subst sample
  exact (ordinary_app (ordinary_app (C_ordinary P 1) (C_ordinary P 1).1)
    (environment_carries P program dispatcher.tree bits)).1

end SOnlySchedulerOrigins


#print axioms SOnlySchedulerOrigins.positive_clock_licensed
#print axioms SOnlySchedulerOrigins.fuel_rows_licensed
#print axioms SOnlySchedulerOrigins.phase_list_licensed
#print axioms SOnlySchedulerOrigins.handoff_list_licensed
#print axioms SOnlySchedulerOrigins.initial_licensed
#print axioms SOnlySchedulerOrigins.prelude_list_licensed
