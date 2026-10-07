import SOnlyWitnessResult

/-!
# Fixed first-preorder current-tree decoder

The search tests the current root, then left subtree, then right subtree.
A selected malformed witness is rejected by readShell; it is not skipped in
favor of a later convenient witness. Correctness at first acceptance reduces
to a uniform certificate for every matching occurrence in that current tree.
-/
namespace SOnlyCurrentDecoder

open PureSFormal.PureS
open SOnlyEventPattern

def findShell : Term → Option Term
  | .s => if targetPattern.matchesBool .s then some .s else none
  | .app left right =>
      if targetPattern.matchesBool (.app left right) then some (.app left right)
      else match findShell left with
        | some shell => some shell
        | none => findShell right

def read (term : Term) : Option Nat := (findShell term).bind SOnlyWitnessResult.readShell

theorem findShell_sound (term shell : Term) (found : findShell term = some shell) :
    ∃ address, term.subterm? address = some shell ∧ targetPattern.matchesBool shell = true := by
  induction term generalizing shell with
  | s =>
      simp only [findShell] at found
      split at found
      · rename_i matched
        cases found
        exact ⟨[], rfl, matched⟩
      · cases found
  | app left right ihL ihR =>
      simp only [findShell] at found
      split at found
      · rename_i matched
        cases found
        exact ⟨[], rfl, matched⟩
      · cases leftFound : findShell left with
        | some result =>
            simp only [leftFound] at found
            cases found
            obtain ⟨address, located, matched⟩ := ihL shell leftFound
            exact ⟨.left :: address, located, matched⟩
        | none =>
            simp only [leftFound] at found
            obtain ⟨address, located, matched⟩ := ihR shell found
            exact ⟨.right :: address, located, matched⟩

theorem findShell_none_iff (term : Term) : findShell term = none ↔
    ¬ SOnlyObserver.Occurs targetPattern term := by
  induction term with
  | s =>
      simp only [findShell, SOnlyObserver.Occurs]
      cases matched : targetPattern.matchesBool .s <;>
        simp [matched, ← Pattern.matchesBool_eq_true_iff]
  | app left right ihL ihR =>
      simp only [findShell, SOnlyObserver.Occurs]
      cases matched : targetPattern.matchesBool (.app left right) with
      | true => simp [matched, ← Pattern.matchesBool_eq_true_iff]
      | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          have noRoot : ¬Pattern.Matches targetPattern (.app left right) := by
            rw [← Pattern.matchesBool_eq_true_iff, matched]; decide
          cases leftFound : findShell left with
          | none =>
              have noLeft := ihL.mp leftFound
              simp [noRoot, noLeft, ihR]
          | some shell =>
              have yesLeft : ¬¬SOnlyObserver.Occurs targetPattern left := by
                intro noLeft
                have impossible := ihL.mpr noLeft
                rw [leftFound] at impossible
                cases impossible
              simp [noRoot, yesLeft]

/-- The search finds a shell exactly when the finite event observer accepts. -/
theorem event_iff_found (term : Term) : SOnlyObserver.event term = true ↔
    ∃ shell, findShell term = some shell := by
  rw [SOnlyObserver.event, SOnlyObserver.accepts_iff_occurs]
  cases found : findShell term with
  | none =>
      have absent := (findShell_none_iff term).mp found
      simp [absent]
  | some shell =>
      have present : SOnlyObserver.Occurs targetPattern term := by
        obtain ⟨address, located, matched⟩ := findShell_sound term shell found
        exact (SOnlyObserver.occurs_iff_subterm _ _).mpr
          ⟨address, shell, located, Pattern.matchesBool_sound matched⟩
      simp [present]

/-- The first selected shell is read even when its decoder returns none. -/
theorem read_of_found (term shell : Term) (found : findShell term = some shell) :
    read term = SOnlyWitnessResult.readShell shell := by
  simp [read, found]

/-- A uniform current-tree witness certificate suffices for the fixed decoder.
The theorem does not choose a convenient witness or require a history parameter. -/
theorem read_of_all_witnesses (term : Term) (value : Nat)
    (accepted : SOnlyObserver.event term = true)
    (valid : ∀ address shell, term.subterm? address = some shell →
      targetPattern.matchesBool shell = true → SOnlyWitnessResult.readShell shell = some value) :
    read term = some value := by
  obtain ⟨shell, found⟩ := (event_iff_found term).mp accepted
  obtain ⟨address, located, matched⟩ := findShell_sound term shell found
  rw [read_of_found term shell found]
  exact valid address shell located matched

end SOnlyCurrentDecoder

#print axioms SOnlyCurrentDecoder.findShell_sound
#print axioms SOnlyCurrentDecoder.event_iff_found
#print axioms SOnlyCurrentDecoder.read_of_all_witnesses
