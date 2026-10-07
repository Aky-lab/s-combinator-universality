import SOnlyTapeCompiler
import SOnlyUniversality

/-!
Every conventional finite-alphabet deterministic Turing machine and finite
input compiles to a finite closed S term. The already fixed finite controller
and fixed regular observer recognize precisely source halting. No tape-space,
source-time, generated-origin or eventual-event premise is supplied.
-/
namespace SOnlyTuringUniversality

open PureSFormal PureSFormal.PureS

abbrev controller := SOnlyUniversality.controller
abbrev selector := SOnlyUniversality.selector
abbrev event := SOnlyUniversality.event
abbrev decode := SOnlyUniversality.decode

abbrev TapeMachine := SOnlyTapeStacks.Machine

def Halts (machine : TapeMachine states symbols) (input : List (Fin symbols)) : Prop :=
  ∃ steps, SOnlyTapeStacks.HaltsAfter (SOnlyTapeStacks.tapeStep machine) steps
    (SOnlyTapeStacks.tapeInput machine input)

/-- All source-dependent data is compiled into the initial closed tree. -/
def encode (machine : TapeMachine states symbols) (input : List (Fin symbols)) : Term :=
  SOnlyUniversality.encode (SOnlyTapeCompiler.inputMachine machine input)
    (SOnlyTapeCompiler.inputValues symbols input)

def trajectory (machine : TapeMachine states symbols)
    (input : List (Fin symbols)) (index : Nat) : Term :=
  SOnlyUniversality.trajectory (SOnlyTapeCompiler.inputMachine machine input)
    (SOnlyTapeCompiler.inputValues symbols input) index

def FirstEvent (machine : TapeMachine states symbols)
    (input : List (Fin symbols)) (index : Nat) : Prop :=
  event (trajectory machine input index) = true ∧
    ∀ earlier, earlier < index → event (trajectory machine input earlier) = false

theorem starts_at_encoder (machine : TapeMachine states symbols)
    (input : List (Fin symbols)) : trajectory machine input 0 = encode machine input := rfl

theorem root_reset (term : Term) :
    controller.initial term = ⟨some controller.start, Cursor.atRoot term⟩ :=
  SOnlyUniversality.root_reset term

theorem no_interinvocation_state : controller.InterInvocationState = Unit := rfl

theorem all_input_linear (term : Term) :
    controller.stoppingTime term ≤ controller.coefficient * (term.size + 1) :=
  SOnlyUniversality.all_input_linear term

/-- Exactly one native contextual S contraction occurs at every encoded step. -/
theorem every_step_native (machine : TapeMachine states symbols)
    (input : List (Fin symbols)) (index : Nat) :
    Step (trajectory machine input index) (trajectory machine input (index + 1)) :=
  SOnlyUniversality.every_step_native _ _ index

/-- The prescribed fixed selector produces the actual sample sequence. -/
theorem selector_executes (machine : TapeMachine states symbols)
    (input : List (Fin symbols)) (index : Nat) :
    selector (trajectory machine input index) = some (trajectory machine input (index+1)) :=
  SOnly38.trajectory_selects _ index

/-- Full conventional-Turing-machine halting equivalence. -/
theorem halting_iff_event (machine : TapeMachine states symbols)
    (input : List (Fin symbols)) :
    Halts machine input ↔ ∃ index, event (trajectory machine input index) = true := by
  exact (SOnlyTapeCompiler.input_halting_iff machine input).trans
    (SOnlyUniversality.halting_iff_event _ _)

/-- Every halting source reaches a first accepted sample with a numerical
readout from that sample alone. The number is the compiled register result. -/
theorem halting_first_result (machine : TapeMachine states symbols)
    (input : List (Fin symbols)) (halts : Halts machine input) :
    ∃ index value, FirstEvent machine input index ∧
      decode (trajectory machine input index) = some value := by
  have sourceHalt := (SOnlyTapeCompiler.input_halting_iff machine input).mp halts
  obtain ⟨index, _, _, first, decoded⟩ := SOnlyUniversality.halting_first_result _ _ sourceHalt
  exact ⟨index, _, first, decoded⟩

theorem halting_iff_first_event (machine : TapeMachine states symbols)
    (input : List (Fin symbols)) :
    Halts machine input ↔ ∃ index, FirstEvent machine input index := by
  constructor
  · intro halts
    obtain ⟨index, _, first, _⟩ := halting_first_result machine input halts
    exact ⟨index, first⟩
  · rintro ⟨index, first⟩
    exact (halting_iff_event machine input).mpr ⟨index, first.1⟩

theorem nonhalting_no_event (machine : TapeMachine states symbols)
    (input : List (Fin symbols)) (nonhalt : ¬Halts machine input) :
    ∀ index, event (trajectory machine input index) = false := by
  intro index
  cases observed : event (trajectory machine input index) with
  | false => rfl
  | true => exact False.elim (nonhalt ((halting_iff_event machine input).mpr ⟨index, observed⟩))

/-- Exact result convention: the natural code of the finite left stack in the
specified two-stack simulation. Retained blanks and the visited extent are part
of this representation; this is not a normalized arbitrary tape-output word. -/
def LeftStackResult (machine : TapeMachine states symbols)
    (input : List (Fin symbols)) (value : Nat) : Prop :=
  ∃ steps stacks,
    SOnlyTapeStacks.run (SOnlyTapeStacks.stackStep machine) steps
      (SOnlyTapeStacks.stackInput machine input) = some stacks ∧
    SOnlyTapeStacks.stackStep machine stacks = none ∧
    SOnlyTapeStacks.stackCode symbols stacks.left = value

/-- Exact value-specific first-current-tree result for the stated convention. -/
theorem left_stack_result_iff_first_event (machine : TapeMachine states symbols)
    (input : List (Fin symbols)) (value : Nat) :
    LeftStackResult machine input value ↔
    ∃ index, FirstEvent machine input index ∧
      decode (trajectory machine input index) = some value := by
  exact (SOnlyTapeCompiler.input_left_stack_result_iff machine input value).symm.trans
    (SOnlyUniversality.result_iff_first_event _ _ value)

end SOnlyTuringUniversality

#print axioms SOnlyTuringUniversality.encode
#print axioms SOnlyTuringUniversality.halting_iff_event
#print axioms SOnlyTuringUniversality.halting_iff_first_event
#print axioms SOnlyTuringUniversality.halting_first_result
#print axioms SOnlyTuringUniversality.selector_executes
#print axioms SOnlyTuringUniversality.every_step_native
#print axioms SOnlyTuringUniversality.nonhalting_no_event

#print axioms SOnlyTuringUniversality.left_stack_result_iff_first_event
