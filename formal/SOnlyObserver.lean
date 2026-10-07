import SOnlyEventPattern

/-!
# A finite bottom-up observer for the literal phase-17 event

The observer stores one Boolean per pattern occurrence and one descendant bit.
All transitions are functions of child states and fixed pattern code. A finite
cover is given constructively. The accepted language is descendant occurrence
of the upstream independent-hole completed-Local pattern, with its exact label.
-/
namespace SOnlyObserver

open PureSFormal PureSFormal.PureS PureSFormal.Research

/-- One match bit for every node of a fixed pattern, with no input tree stored. -/
def Bits : Pattern → Type
  | .hole => Bool
  | .s => Bool
  | .app left right => Bool × Bits left × Bits right

def rootBit : (pattern : Pattern) → Bits pattern → Bool
  | .hole, value => value
  | .s, value => value
  | .app _ _, value => value.1

/-- The complete finite Boolean cube, including unreachable states. -/
def cover : (pattern : Pattern) → List (Bits pattern)
  | .hole => [false, true]
  | .s => [false, true]
  | .app left right => [false, true].flatMap (fun bit =>
      (cover left).flatMap (fun l => (cover right).map (fun r => (bit, l, r))))

theorem cover_complete (pattern : Pattern) (value : Bits pattern) : value ∈ cover pattern := by
  induction pattern with
  | hole => cases value <;> change _ ∈ [false, true] <;> simp only [List.mem_cons] <;> decide
  | s => cases value <;> change _ ∈ [false, true] <;> simp only [List.mem_cons] <;> decide
  | app left right ihL ihR =>
      rcases value with ⟨bit, l, r⟩
      change (bit, l, r) ∈ [false, true].flatMap (fun bit =>
        (cover left).flatMap (fun l => (cover right).map (fun r => (bit, l, r))))
      apply List.mem_flatMap.mpr
      refine ⟨bit, ?_, List.mem_flatMap.mpr ⟨l, ihL l, List.mem_map.mpr ⟨r, ihR r, rfl⟩⟩⟩
      cases bit <;> simp

private theorem flatMap_length_uniform {α β : Type} (xs : List α) (f : α → List β)
    (n : Nat) (uniform : ∀ x ∈ xs, (f x).length = n) :
    (xs.flatMap f).length = xs.length * n := by
  induction xs with
  | nil => simp
  | cons head tail ih =>
      rw [List.flatMap_cons, List.length_append, uniform head (by simp),
        ih (fun x member => uniform x (by simp [member]))]
      simp [Nat.add_mul, Nat.add_comm]

/-- The uncompressed cube has exactly one bit per pattern occurrence. -/
theorem cover_length (pattern : Pattern) : (cover pattern).length = 2 ^ pattern.size := by
  induction pattern with
  | hole => rfl
  | s => rfl
  | app left right ihL ihR =>
      change ([false, true].flatMap (fun bit =>
        (cover left).flatMap (fun l => (cover right).map (fun r => (bit, l, r))))).length = _
      rw [flatMap_length_uniform _ _ ((cover left).length * (cover right).length)]
      · simp only [List.length_cons, List.length_nil, ihL, ihR, Pattern.size,
          Nat.pow_succ, Nat.pow_add]
        omega
      · intro bit member
        exact flatMap_length_uniform _ _ _ (fun l h => List.length_map _)

/-- State at an S leaf; this uses no input beyond the node constructor. -/
def leafBits : (pattern : Pattern) → Bits pattern
  | .hole => true
  | .s => true
  | .app left right => (false, leafBits left, leafBits right)

/-- One application transition on bounded child-state cubes. -/
def joinBits : (pattern : Pattern) → Bits pattern → Bits pattern → Bits pattern
  | .hole, _, _ => true
  | .s, _, _ => false
  | .app left right, l, r =>
      (rootBit left l.2.1 && rootBit right r.2.2,
       joinBits left l.2.1 r.2.1, joinBits right l.2.2 r.2.2)

/-- The semantic specification of all subpattern bits at one tree root. -/
def specification : (pattern : Pattern) → Term → Bits pattern
  | .hole, _ => true
  | .s, term => Pattern.matchesBool .s term
  | .app left right, term =>
      (Pattern.matchesBool (.app left right) term,
       specification left term, specification right term)

@[simp] theorem root_specification (pattern : Pattern) (term : Term) :
    rootBit pattern (specification pattern term) = Pattern.matchesBool pattern term := by
  cases pattern <;> rfl

theorem leaf_specification (pattern : Pattern) : leafBits pattern = specification pattern .s := by
  induction pattern with
  | hole => rfl
  | s => rfl
  | app left right ihL ihR => simp only [leafBits, specification, Pattern.matchesBool, ihL, ihR]; rfl

theorem join_specification (pattern : Pattern) (left right : Term) :
    joinBits pattern (specification pattern left) (specification pattern right) =
      specification pattern (.app left right) := by
  induction pattern with
  | hole => rfl
  | s => rfl
  | app l r ihL ihR =>
      simp only [joinBits, specification, root_specification, Pattern.matchesBool, ihL, ihR]; rfl

abbrev State (pattern : Pattern) := Bits pattern × Bool

def stateCover (pattern : Pattern) : List (State pattern) :=
  (cover pattern).flatMap (fun bits => [false, true].map (fun found => (bits, found)))

theorem stateCover_complete (pattern : Pattern) (state : State pattern) :
    state ∈ stateCover pattern := by
  rcases state with ⟨bits, found⟩
  simp only [stateCover, List.mem_flatMap, List.mem_map]
  refine ⟨bits, cover_complete pattern bits, found, ?_, rfl⟩
  cases found <;> simp

theorem stateCover_length (pattern : Pattern) :
    (stateCover pattern).length = 2 ^ (pattern.size + 1) := by
  unfold stateCover
  rw [flatMap_length_uniform _ _ 2]
  · rw [cover_length, Nat.pow_succ]
  · intro bits member; rfl

def leafState (pattern : Pattern) : State pattern :=
  (leafBits pattern, rootBit pattern (leafBits pattern))

def joinState (pattern : Pattern) (left right : State pattern) : State pattern :=
  let bits := joinBits pattern left.1 right.1
  (bits, rootBit pattern bits || left.2 || right.2)

def run (pattern : Pattern) : Term → State pattern
  | .s => leafState pattern
  | .app left right => joinState pattern (run pattern left) (run pattern right)

/-- A mathematical descendant predicate, with independent holes at the root. -/
def Occurs (pattern : Pattern) : Term → Prop
  | .s => Pattern.Matches pattern .s
  | .app left right => Pattern.Matches pattern (.app left right) ∨
      Occurs pattern left ∨ Occurs pattern right

theorem run_bits (pattern : Pattern) (term : Term) :
    (run pattern term).1 = specification pattern term := by
  induction term with
  | s => exact leaf_specification pattern
  | app left right ihL ihR =>
      change joinBits pattern (run pattern left).1 (run pattern right).1 = _
      rw [ihL, ihR, join_specification]

theorem accepts_iff_occurs (pattern : Pattern) (term : Term) :
    (run pattern term).2 = true ↔ Occurs pattern term := by
  induction term with
  | s =>
      change rootBit pattern (leafBits pattern) = true ↔ Pattern.Matches pattern .s
      rw [leaf_specification, root_specification, Pattern.matchesBool_eq_true_iff]
  | app left right ihL ihR =>
      change (rootBit pattern (joinBits pattern (run pattern left).1 (run pattern right).1) ||
        (run pattern left).2 || (run pattern right).2) = true ↔ _
      rw [run_bits, run_bits, join_specification, root_specification]
      simp only [Bool.or_eq_true, Pattern.matchesBool_eq_true_iff, ihL, ihR, Occurs]
      exact or_assoc

theorem occurs_iff_subterm (pattern : Pattern) (term : Term) :
    Occurs pattern term ↔ ∃ address subtree,
      term.subterm? address = some subtree ∧ Pattern.Matches pattern subtree := by
  induction term with
  | s =>
      constructor
      · intro h; exact ⟨[], .s, rfl, h⟩
      · rintro ⟨address, subtree, located, matched⟩
        cases address with
        | nil => cases located; exact matched
        | cons dir rest => cases dir <;> cases located
  | app left right ihL ihR =>
      constructor
      · intro h
        rcases h with h | h | h
        · exact ⟨[], .app left right, rfl, h⟩
        · obtain ⟨a, t, located, matched⟩ := ihL.mp h
          exact ⟨.left :: a, t, located, matched⟩
        · obtain ⟨a, t, located, matched⟩ := ihR.mp h
          exact ⟨.right :: a, t, located, matched⟩
      · rintro ⟨address, subtree, located, matched⟩
        cases address with
        | nil => cases located; exact Or.inl matched
        | cons dir rest =>
            cases dir with
            | left => exact Or.inr (Or.inl (ihL.mpr ⟨rest, subtree, located, matched⟩))
            | right => exact Or.inr (Or.inr (ihR.mpr ⟨rest, subtree, located, matched⟩))

/-- Every fixed pattern has an explicit finite bottom-up state cover. -/
theorem finite_observer_correct (pattern : Pattern) (term : Term) :
    run pattern term ∈ stateCover pattern ∧
      ((run pattern term).2 = true ↔ ∃ address subtree,
        term.subterm? address = some subtree ∧ Pattern.Matches pattern subtree) := by
  exact ⟨stateCover_complete pattern _, (accepts_iff_occurs pattern term).trans
    (occurs_iff_subterm pattern term)⟩

/-- The fixed regular event language used by the 38-phase construction. -/
def event (term : Term) : Bool := (run SOnlyEventPattern.targetPattern term).2

theorem event_iff_matches (term : Term) : event term = true ↔
    ∃ address subtree, term.subterm? address = some subtree ∧
      SOnlyEventPattern.targetPattern.matchesBool subtree = true := by
  rw [event, accepts_iff_occurs, occurs_iff_subterm]
  simp only [Pattern.matchesBool_eq_true_iff]

/-- The recognized occurrence is exactly a fresh Local with the pinned
phase-17 route and label, independently of its arbitrary wildcard payloads. -/
theorem event_iff (term : Term) : event term = true ↔
    ∃ address subtree, term.subterm? address = some subtree ∧
      ∃ view : CheckpointDecoder.LocalView SOnly38.program,
        view.status = .fresh ∧ view.route = SOnly38.targetRoute ∧
        view.label = SOnly38.targetLabel ∧
        CheckpointDecoder.LocalShape SOnly38.program SOnly38.dispatcher.tree view subtree := by
  rw [event, accepts_iff_occurs, occurs_iff_subterm]
  constructor
  · rintro ⟨address, subtree, located, matched⟩
    exact ⟨address, subtree, located,
      (SOnlyEventPattern.targetPattern_iff subtree).mp (Pattern.matchesBool_complete matched)⟩
  · rintro ⟨address, subtree, located, view⟩
    exact ⟨address, subtree, located,
      Pattern.matchesBool_sound ((SOnlyEventPattern.targetPattern_iff subtree).mpr view)⟩

/-- A constructive finite state cover for this single, source-independent event. -/
theorem event_finite_cover (term : Term) :
    run SOnlyEventPattern.targetPattern term ∈ stateCover SOnlyEventPattern.targetPattern ∧
      (stateCover SOnlyEventPattern.targetPattern).length =
        2 ^ (SOnlyEventPattern.targetPattern.size + 1) :=
  ⟨stateCover_complete _ _, stateCover_length _⟩

end SOnlyObserver

#print axioms SOnlyObserver.finite_observer_correct

#print axioms SOnlyObserver.event_iff
#print axioms SOnlyObserver.event_finite_cover

#print axioms SOnlyObserver.event_iff_matches
