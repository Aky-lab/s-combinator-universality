import PureSFormal.Research.RootResetFiniteAllInputsTraceAgreement
import PureSFormal.Research.RootResetContractProjection

/-!
# The fixed UT19 one-hot, 38-phase CTS instance

This file specializes Cinematic Strawberry's construction at upstream commit
85a867988442fc423279341200f81634a1e65582. Its proved layers are the concrete
UT19 one-hot program, the fixed root-reset controller, every-sample trajectory
agreement, and exact public-checkpoint decoding. Static facts use the
kernel-checked `decide` tactic.

The complete project composition and proof boundary are described in
../docs/formal-cts-instance.md. The complementary written proofs are
../docs/universal-bp2-front-end.md, ../docs/ut19-simulation-invariants.md,
../docs/cts-event-transfer.md, and ../docs/s-event-readout.md.
-/

namespace SOnly38

open PureSFormal PureSFormal.PureS PureSFormal.Research

set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

/-- UT19's published one-based production labels, identical to s_only/ut19.py. -/
def productions : List (List Nat) :=
  [[2, 3], [4, 4], [18, 4], [1, 1, 19],
   [7, 9], [8, 9], [10, 10], [11, 10], [18, 10],
   [5, 6], [6, 5, 19], [14, 14, 14, 14], [15],
   [16, 16], [16, 17], [12, 13], [12, 12, 12, 12], [18], []]

/-- A published symbol k becomes 0^(k-1), 1, 0^(19-k). -/
def oneHot (symbol : Nat) : List Bool :=
  (List.range 19).map (fun index => decide (index + 1 = symbol))

/-- Nineteen encoded TAKE productions followed by nineteen empty SKIP phases. -/
def appendants : List (List Bool) :=
  productions.map (fun word => word.flatMap oneHot) ++ List.replicate 19 []

/-- A literal positive-period CTS in the upstream type. -/
def program : CTS.Program where
  period := 38
  period_pos := by decide
  appendant phase := (appendants[phase.val]?).getD []

theorem production_count : productions.length = 19 := by decide

theorem production_symbols_valid :
    productions.all (fun word => word.all (fun symbol =>
      decide (1 ≤ symbol ∧ symbol ≤ 19))) = true := by decide

theorem period_eq : program.period = 38 := rfl

theorem appendant_count : appendants.length = 38 := by decide

/-- Connect all finite program indices to the displayed appendant table. -/
theorem enumerated_appendants :
    (List.finRange program.period).map program.appendant = appendants := by decide

theorem appendant_bit_count :
    (appendants.map List.length).sum = 760 := by decide

theorem appendant_one_count :
    (appendants.map (fun word => (word.filter id).length)).sum = 40 := by decide

theorem skip_appendants :
    appendants.drop 19 = List.replicate 19 [] := by decide

/-- The event's phase is zero-based 17, corresponding to published symbol 18. -/
def targetPhase : CTS.Phase program := ⟨17, by decide⟩

def targetLabel : ActionLabel program := (targetPhase, true)

def targetAppendant : List Bool := List.replicate 17 false ++ [true, false]

theorem target_appendant : program.appendant targetPhase = targetAppendant := by decide

theorem target_appendant_length : (program.appendant targetPhase).length = 19 := by decide

theorem target_appendant_one_count :
    ((program.appendant targetPhase).filter id).length = 1 := by decide

/-- The designated response cannot empty its output, even with empty suffix. -/
theorem target_response_nonempty (suffix : List Bool) :
    (CTS.absorbingStep program ⟨targetPhase, true :: suffix⟩).data ≠ [] := by
  change suffix ++ program.appendant targetPhase ≠ []
  rw [target_appendant]
  cases suffix <;> simp [targetAppendant]

/-- Use the exact canonical balanced dispatcher, rather than a replica. -/
abbrev dispatcher : ActionDispatcher program :=
  WeakPathUniversality.canonicalDispatcher program

/-- Left=0 and right=1, so this is literally the route 0100011. -/
def targetRoute : Dispatcher.Route :=
  [.left, .right, .left, .left, .left, .right, .right]

theorem dispatcher_leaf_count : dispatcher.tree.leafCount = 76 := by
  exact BalancedActionTree.tree_leafCount program

theorem dispatcher_depth : dispatcher.tree.depth = 7 := by decide

theorem target_selected_route : dispatcher.route targetLabel = targetRoute := by decide

theorem target_route_lookup :
    dispatcher.tree.lookup? targetRoute = some targetLabel := by decide

theorem target_has_route : Dispatcher.HasRoute dispatcher.tree targetRoute targetLabel :=
  Dispatcher.hasRoute_of_lookup? target_route_lookup

/-- The exact upstream S-syntax encoder for arbitrary finite input bitwords. -/
def encode (bits : List Bool) : Term :=
  generator (compileActions program dispatcher.tree) bits

abbrev selector : Term → Option Term :=
  RootResetFiniteAllInputsTraceAgreement.selector program

abbrev controller : RootResetSelectorContract.Contract :=
  RootResetFinitePrioritySelector.selectorContract program dispatcher

def trajectory (bits : List Bool) (index : Nat) : Term :=
  RootResetTermOnlyTransfer.run selector index (encode bits)

theorem encode_eq_upstream (bits : List Bool) :
    encode bits = (WeakPathUniversality.finiteCTSWeakPathUniversality program).encode bits := rfl

private theorem readonly_eq_projected {α : Type}
    (spec : RootResetReadonlySelector.ProbeSpec α) :
    RootResetReadonlySelector.selectStep? spec =
      RootResetContractProjection.projectedStep? (RootResetReadonlySelector.selectorContract spec) := by
  unfold RootResetReadonlySelector.selectStep? RootResetContractProjection.projectedStep?
  rfl

private theorem generic_selector_eq_projected
    (p : CTS.Program) (layout : ActionDispatcher p) :
    RootResetFinitePrioritySelector.selectStep? p layout =
      RootResetContractProjection.projectedStep?
        (RootResetFinitePrioritySelector.selectorContract p layout) :=
  readonly_eq_projected (RootResetFinitePrioritySelector.selectionSpec p layout)

/-- This equality links the actual root-reset invocation and bare-term selector. -/
theorem selector_eq_projected (term : Term) :
    selector term = RootResetContractProjection.projectedStep? controller term :=
  congrFun (generic_selector_eq_projected program dispatcher) term

theorem same_root_start (term : Term) :
    controller.initial term = ⟨some controller.start, Cursor.atRoot term⟩ :=
  RootResetFinitePrioritySelector.same_root_start program dispatcher term

theorem boundary_state_is_unit : controller.InterInvocationState = Unit := rfl

theorem coefficient_positive : 0 < controller.coefficient := controller.coefficient_pos

/-- The fixed coefficient depends on the CTS/dispatcher, not on the input tree. -/
theorem every_input_linear (term : Term) :
    controller.stoppingTime term ≤ controller.coefficient * (term.size + 1) :=
  RootResetFinitePrioritySelector.all_input_linear program dispatcher term

theorem every_input_terminal (term : Term) :
    (RootResetSelectorContract.runtimeHaltKind controller.haltKind
      (FiniteController.run controller.machine (controller.stoppingTime term)
        (controller.initial term)).control).isSome = true :=
  RootResetFinitePrioritySelector.all_input_terminal program dispatcher term

/-- Successful answers are exactly one native occurrence contraction. -/
theorem selected_one_contraction (source target : Term)
    (selected : selector source = some target) :
    let final := controller.invokeRun () source
    RootResetSelectorContract.runtimeHaltKind controller.haltKind final.control = some .redex ∧
      final.cursor.erase = target ∧
      FiniteController.runMutationCount controller.machine
        (controller.stoppingTime source) (controller.initial source) = 1 ∧
      source.contractAt? (RootResetSelectorContract.cursorAddress final.cursor) = some target := by
  have projected : RootResetContractProjection.projectedStep? controller source = some target :=
    (selector_eq_projected source).symm.trans selected
  exact RootResetContractProjection.some_result controller () source target projected

/-- Failed answers are normal, unchanged, and perform zero contractions. -/
theorem rejected_zero_contractions (source : Term) (selected : selector source = none) :
    let final := controller.invokeRun () source
    RootResetSelectorContract.runtimeHaltKind controller.haltKind final.control = some .nf ∧
      RootResetSelectorContract.AddressNormal source ∧ final.cursor.erase = source ∧
      FiniteController.runMutationCount controller.machine
        (controller.stoppingTime source) (controller.initial source) = 0 := by
  have projected : RootResetContractProjection.projectedStep? controller source = none :=
    (selector_eq_projected source).symm.trans selected
  exact RootResetContractProjection.none_result controller () source projected

/-- No input/stage/provenance premise is required for the every-sample equality. -/
theorem trajectory_eq_persistent (bits : List Bool) (index : Nat) :
    trajectory bits index =
      ((WeakPathUniversality.finiteCTSWeakPathUniversality program).path bits).term index :=
  RootResetFiniteAllInputsTraceAgreement.termOnlyPath_eq_persistentPath program bits index

theorem trajectory_selects (bits : List Bool) (index : Nat) :
    selector (trajectory bits index) = some (trajectory bits (index + 1)) := by
  rw [trajectory_eq_persistent, trajectory_eq_persistent]
  exact RootResetFiniteAllInputsTraceAgreement.agreesOnEverySample program bits index

theorem trajectory_contracts (bits : List Bool) (index : Nat) :
    Step (trajectory bits index) (trajectory bits (index + 1)) := by
  rw [trajectory_eq_persistent, trajectory_eq_persistent]
  exact ((WeakPathUniversality.finiteCTSWeakPathUniversality program).path bits).contracts index

/-- The generic checkpoint simulation is instantiated, not assumed. -/
def checkpointRealization :
    WeakPath.UniformRealizes program (RootResetTermOnlyTransfer.Projects selector) selector
      (PublicDecoder.decode program dispatcher.tree) :=
  RootResetFiniteAllInputsTraceAgreement.finiteCTSUniversality program

abbrev checkpointTime (bits : List Bool) (horizon : Nat) : Nat :=
  (WeakPathUniversality.finiteCTSWeakPathUniversality program).checkpointTime bits horizon

/-- This is the upstream public-checkpoint decoder, not the F17 event observer. -/
theorem exact_checkpoint (bits : List Bool) (horizon : Nat) :
    PublicDecoder.decode program dispatcher.tree (trajectory bits (checkpointTime bits horizon)) =
      some (horizon, CTS.iterate program horizon (CTS.initial program bits)) := by
  rw [trajectory_eq_persistent]
  exact ((WeakPathUniversality.finiteCTSWeakPathUniversality program).realizes bits).exactCheckpoint horizon

theorem checkpoint_accepts_only (bits : List Bool) (index horizon : Nat)
    (config : CTS.Config program)
    (decoded : PublicDecoder.decode program dispatcher.tree (trajectory bits index) =
      some (horizon, config)) :
    index = checkpointTime bits horizon ∧
      config = CTS.iterate program horizon (CTS.initial program bits) := by
  rw [trajectory_eq_persistent] at decoded
  exact ((WeakPathUniversality.finiteCTSWeakPathUniversality program).realizes bits).acceptsOnly
    index horizon config decoded

end SOnly38

#print axioms SOnly38.enumerated_appendants
#print axioms SOnly38.appendant_bit_count
#print axioms SOnly38.appendant_one_count
#print axioms SOnly38.target_selected_route
#print axioms SOnly38.every_input_linear
#print axioms SOnly38.every_input_terminal
#print axioms SOnly38.selected_one_contraction
#print axioms SOnly38.rejected_zero_contractions
#print axioms SOnly38.trajectory_eq_persistent
#print axioms SOnly38.trajectory_selects
#print axioms SOnly38.trajectory_contracts
#print axioms SOnly38.exact_checkpoint
#print axioms SOnly38.checkpoint_accepts_only
