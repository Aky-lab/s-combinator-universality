import PureSFormal.PureS.CheckpointDecoder

/-!
# Input-size bounds for the exact public carrier decoder

These statements concern ordinary occurrence-tree size, not the size of a
shared DAG. The executable fuel simulation agrees with the existing decoder
on every finite input. The recursion charge counts one classifier iteration,
and reserves at most `queue.size` cell-spine iterations at a Base. Thus the
charge is not a claim that the imported classifier runs in constant time.
The accompanying source audit bounds each classifier by a fixed multiple of
`(input.size + 1)^2`, including its non-linear `spineArgs` implementation.
-/

namespace SOnlyDecoderBound

open PureSFormal PureSFormal.PureS
open CheckpointDecoder

theorem parseBase_queue_size_lt {actions term : Term} {view : BaseView}
    (parsed : parseBase? actions term = some view) : view.queue.size < term.size := by
  rw [parseBase?_sound parsed]
  simp only [openBase, openEnvironment, Term.size]
  omega

theorem cellSpine_output_length {term : Term} {bits : List Bool}
    (parsed : CellSpine.decode? term = some bits) : bits.length ≤ term.size := by
  have decoded := CellSpine.decode?_sound parsed
  clear parsed
  induction decoded with
  | omega => simp [PureSFormal.PureS.omega]
  | live bit inner ih =>
      simp only [List.length_append, List.length_singleton, Term.size]
      omega
  | tombstone bit audit inner ih =>
      simp only [Carrier.tombstone, Term.size]
      omega

theorem carrier_output_length {program : CTS.Program}
    {tree : Dispatcher.Tree (ActionLabel program)} {term : Term} {bits : List Bool}
    (parsed : decodeCarrier? program tree term = some bits) : bits.length ≤ term.size := by
  have decoded := decodeCarrier?_sound program tree parsed
  clear parsed
  induction decoded with
  | base view boundary queue =>
      have lengthBound := cellSpine_output_length (CellSpine.decode?_complete queue)
      have sizeBound := parseBase_queue_size_lt boundary
      omega
  | «local» view notBase boundary inner ih =>
      have sizeBound := parseLocal?_accumulator_size_lt boundary
      omega
  | live bit notBase notLocal boundary inner ih =>
      have sizeBound := parsedCell_size_lt boundary rfl
      simp only [List.length_append, List.length_singleton]
      omega
  | tombstone bit notBase notLocal boundary inner ih =>
      have sizeBound := parsedCell_size_lt boundary rfl
      omega

/-- A fuelled copy of the actual ordered classifier, with identical rejection
and output behavior. The only new argument is a syntactic recursion budget. -/
def carrierFuel (program : CTS.Program) (tree : Dispatcher.Tree (ActionLabel program)) :
    Nat → Term → Option (List Bool)
  | 0, _ => none
  | fuel + 1, term =>
      match parseBase? (compileActions program tree) term with
      | some view => CellSpine.decode? view.queue
      | none =>
          match parseLocal? program tree term with
          | some view => carrierFuel program tree fuel view.accumulator
          | none =>
              match CanonicalStep.parseCell? term with
              | some (.live bit predecessor) =>
                  (carrierFuel program tree fuel predecessor).map (fun bits => bits ++ [bit])
              | some (.tombstone _ predecessor) => carrierFuel program tree fuel predecessor
              | none => none

/-- Tree size is sufficient fuel on arbitrary inputs, including malformed ones. -/
theorem carrierFuel_eq (program : CTS.Program) (tree : Dispatcher.Tree (ActionLabel program))
    (fuel : Nat) (term : Term) (enough : term.size ≤ fuel) :
    carrierFuel program tree fuel term = decodeCarrier? program tree term := by
  induction fuel generalizing term with
  | zero => have positive := term.size_pos; omega
  | succ fuel ih =>
      rw [carrierFuel, decodeCarrier?]
      cases hb : parseBase? (compileActions program tree) term with
      | some view => rfl
      | none =>
          simp only
          cases hl : parseLocal? program tree term with
          | some view =>
              exact ih view.accumulator (by
                have := parseLocal?_accumulator_size_lt hl
                omega)
          | none =>
              simp only
              cases hc : CanonicalStep.parseCell? term with
              | none => rfl
              | some cell =>
                  cases cell with
                  | live bit predecessor =>
                      simp only
                      rw [ih predecessor (by have := parsedCell_size_lt hc rfl; omega)]
                  | tombstone bit predecessor =>
                      exact ih predecessor (by have := parsedCell_size_lt hc rfl; omega)

/-- One unit per carrier classifier, with an upper allowance for every
cell-spine frame at its unique terminal Base. No history or source execution
is supplied to this function. -/
def carrierCharge (program : CTS.Program) (tree : Dispatcher.Tree (ActionLabel program))
    (term : Term) : Nat :=
  match hb : parseBase? (compileActions program tree) term with
  | some view => view.queue.size + 1
  | none =>
      match hl : parseLocal? program tree term with
      | some view => carrierCharge program tree view.accumulator + 1
      | none =>
          match hc : CanonicalStep.parseCell? term with
          | some (.live _ predecessor) => carrierCharge program tree predecessor + 1
          | some (.tombstone _ predecessor) => carrierCharge program tree predecessor + 1
          | none => 1
termination_by term.size
decreasing_by
  · exact parseLocal?_accumulator_size_lt hl
  · exact parsedCell_size_lt hc rfl
  · exact parsedCell_size_lt hc rfl

theorem carrierCharge_le (program : CTS.Program) (tree : Dispatcher.Tree (ActionLabel program))
    (term : Term) : carrierCharge program tree term ≤ term.size := by
  induction term using (measure Term.size).wf.induction with
  | h term ih =>
      rw [carrierCharge]
      cases hb : parseBase? (compileActions program tree) term with
      | some view =>
          have := parseBase_queue_size_lt hb
          simp only
          omega
      | none =>
          simp only
          cases hl : parseLocal? program tree term with
          | some view =>
              have smaller := parseLocal?_accumulator_size_lt hl
              have bound := ih view.accumulator smaller
              simp only
              omega
          | none =>
              simp only
              cases hc : CanonicalStep.parseCell? term with
              | none => exact term.size_pos
              | some cell =>
                  cases cell with
                  | live bit predecessor =>
                      have smaller := parsedCell_size_lt hc rfl
                      have bound := ih predecessor smaller
                      simp only
                      omega
                  | tombstone bit predecessor =>
                      have smaller := parsedCell_size_lt hc rfl
                      have bound := ih predecessor smaller
                      simp only
                      omega

/-- Once a classifier is charged a quadratic input allowance, the total is
cubic. The static constant multiplying this meter is justified by inspecting
the imported parser implementations, not assumed constant-time in this lemma. -/
theorem carrier_cubic_charge (program : CTS.Program)
    (tree : Dispatcher.Tree (ActionLabel program)) (term : Term) :
    carrierCharge program tree term * (term.size + 1) * (term.size + 1) ≤
      term.size * (term.size + 1) * (term.size + 1) := by
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (carrierCharge_le program tree term))

/-- Number of list cells visited by literal `spineArgs`, counting one frame
and the existing list traversed by every append. -/
def spineVisits : Term → Nat
  | .s => 1
  | .app fn _ => spineVisits fn + fn.spineArgs.length + 1

theorem spine_length_lt (term : Term) : term.spineArgs.length < term.size := by
  induction term with
  | s => simp
  | app fn arg ih => simp only [Term.spineArgs, List.length_append, List.length_singleton, Term.size];
                     have := arg.size_pos; omega

theorem spineVisits_le (term : Term) :
    spineVisits term ≤ (term.spineArgs.length + 1) * (term.spineArgs.length + 1) := by
  induction term with
  | s => simp [spineVisits]
  | app fn arg ih =>
      simp only [spineVisits, Term.spineArgs, List.length_append, List.length_singleton]
      simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul] at *
      omega

theorem spineVisits_quadratic (term : Term) : spineVisits term ≤ term.size * term.size := by
  exact Nat.le_trans (spineVisits_le term)
    (Nat.mul_le_mul (spine_length_lt term) (spine_length_lt term))

end SOnlyDecoderBound

#print axioms SOnlyDecoderBound.carrier_output_length
#print axioms SOnlyDecoderBound.carrierFuel_eq
#print axioms SOnlyDecoderBound.carrierCharge_le
#print axioms SOnlyDecoderBound.carrier_cubic_charge
#print axioms SOnlyDecoderBound.spineVisits_quadratic
