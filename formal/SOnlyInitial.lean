import SOnlyObserver

/-!
# Event absence in every encoded initial term

The result is uniform in the entire finite input bitword. It checks every
descendant, including the static dispatcher and word encoding. No source
execution bound or finite list of tested seeds is involved.
-/
namespace SOnlyInitial

open PureSFormal PureSFormal.PureS PureSFormal.Research

/-- Every subtree has at most four arguments on its left spine. -/
def Low : Term → Prop
  | .s => True
  | .app fn arg => fn.headArity < 4 ∧ Low fn ∧ Low arg

theorem Low.arity {term : Term} (bounded : Low term) : term.headArity ≤ 4 := by
  cases term with
  | s => decide
  | app fn arg => exact bounded.1

theorem Low.subterm {term subtree : Term} (bounded : Low term)
    {address : Address} (located : term.subterm? address = some subtree) : Low subtree := by
  induction address generalizing term with
  | nil =>
      have equal := Option.some.inj ((Term.subterm?_root _).symm.trans located)
      subst subtree
      exact bounded
  | cons dir rest ih =>
      cases term with
      | s => cases dir <;> cases located
      | app fn arg =>
          cases dir with
          | left => exact ih bounded.2.1 located
          | right => exact ih bounded.2.2 located

theorem low_live (bit : Bool) : Low (live bit) := by
  cases bit <;> simp [Low, live, valueTag, v0, v1, C, b]

theorem live_arity (bit : Bool) : (live bit).headArity = 2 := rfl

theorem low_word (bits : List Bool) : Low (word bits) := by
  have general : ∀ (tail : List Bool) (start : Term), Low start →
      Low (tail.foldl (fun acc bit => Term.app (live bit) acc) start) := by
    intro tail
    induction tail with
    | nil => intro start low; exact low
    | cons bit tail ih =>
        intro start low
        apply ih (.app (live bit) start)
        exact ⟨by rw [live_arity]; decide, low_live bit, low⟩
  exact general bits omega trivial

theorem low_appender (bits : List Bool) : Low (appender bits) := by
  induction bits with
  | nil => simp [appender, p, b, Low]
  | cons bit bits ih =>
      simp only [appender_cons, push, Low, Term.headArity]
      exact ⟨by decide, ⟨by decide, trivial, by decide, trivial, ih⟩, low_live bit⟩

theorem low_action (program : CTS.Program) (label : ActionLabel program) :
    Low (selectedAction program label) := by
  rcases label with ⟨phase, bit⟩
  cases bit with
  | false => simp [selectedAction, p, b, Low]
  | true => exact low_appender _

theorem low_compile (program : CTS.Program) (tree : Dispatcher.Tree (ActionLabel program)) :
    Low (compileActions program tree) := by
  induction tree with
  | leaf label =>
      change Low (.app b (selectedAction program label))
      exact ⟨by decide, by simp [Low, b], low_action program label⟩
  | node left right ihL ihR =>
      change Low (.app b (.app (.app .s (compileActions program left)) (compileActions program right)))
      exact ⟨by decide, by simp [Low, b], by simp, ⟨by decide, trivial, ihL⟩, ihR⟩

theorem low_generator (actions : Term) (bits : List Bool) (low : Low actions) :
    Low (generator actions bits) := by
  simp [generator, environmentCode, dispatcherCode, actCode, seedCode,
    Low, Term.headArity, C, b, haltCode, haltTag, low, low_word bits]

theorem initial_low (bits : List Bool) : Low (SOnly38.encode bits) :=
  low_generator _ bits (low_compile _ _)

/-- A completed Local cannot occur among trees with the initial arity bound. -/
theorem low_not_local {term : Term} (bounded : Low term)
    (view : CheckpointDecoder.LocalView SOnly38.program) :
    ¬ CheckpointDecoder.LocalShape SOnly38.program SOnly38.dispatcher.tree view term := by
  intro shape
  have parsed := CheckpointDecoder.parseLocal?_complete shape
  have arity := CheckpointDecoder.parseLocal?_headArity parsed
  have low := bounded.arity
  omega

/-- The fixed event observer rejects every literal initial encoding. -/
theorem initial_event_false (bits : List Bool) :
    SOnlyObserver.event (SOnly38.encode bits) = false := by
  cases found : SOnlyObserver.event (SOnly38.encode bits) with
  | false => rfl
  | true =>
      obtain ⟨address, subtree, located, view, _, _, _, shape⟩ :=
        (SOnlyObserver.event_iff _).mp found
      exact False.elim (low_not_local ((initial_low bits).subterm located) view shape)

end SOnlyInitial

#print axioms SOnlyInitial.initial_low
#print axioms SOnlyInitial.initial_event_false
