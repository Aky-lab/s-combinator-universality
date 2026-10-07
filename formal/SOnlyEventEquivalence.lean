import SOnlyGlobalStages

/-!
# Source-event and S-event equivalence

The source interface permits termination after an event, but excludes empty
CTS data before all designated source events. Under this source invariant,
existence of an event on the fixed finite-observer S trajectory is equivalent
to existence of the designated CTS prestate.
-/
namespace SOnlyEventEquivalence
open PureSFormal

/-- The source may become empty only after a designated pre-transition event. -/
def NoPrematureEmpty (bits : List Bool) : Prop :=
  ∀ time, (CTS.iterate SOnly38.program time (CTS.initial SOnly38.program bits)).data = [] →
    ∃ eventTime, eventTime ≤ time ∧ SOnlySource.Event
      (CTS.iterate SOnly38.program eventTime (CTS.initial SOnly38.program bits))

/-- The nonhalting branch needs nonemptiness only when no source event exists. -/
theorem nonempty_of_event_free (bits : List Bool)
    (safe : NoPrematureEmpty bits)
    (noEvent : ∀ k, ¬SOnlySource.Event
      (CTS.iterate SOnly38.program k (CTS.initial SOnly38.program bits))) :
    ∀ time, (CTS.iterate SOnly38.program time (CTS.initial SOnly38.program bits)).data ≠ [] := by
  intro time empty
  obtain ⟨eventTime, _, occurred⟩ := safe time empty
  exact noEvent eventTime occurred

/-- No source event means no accepted S tree; an actual source event creates
an accepted tree. The source is allowed to exhaust after that event. -/
theorem event_exists_iff (bits : List Bool) (safe : NoPrematureEmpty bits) :
    (∃ sample, SOnlyObserver.event (SOnly38.trajectory bits sample) = true) ↔
      ∃ time, SOnlySource.Event
        (CTS.iterate SOnly38.program time (CTS.initial SOnly38.program bits)) := by
  constructor
  · rintro ⟨sample, accepted⟩
    apply Classical.byContradiction
    intro missing
    have noEvent : ∀ k, ¬SOnlySource.Event
        (CTS.iterate SOnly38.program k (CTS.initial SOnly38.program bits)) := by
      intro k event
      exact missing ⟨k, event⟩
    have rejected := SOnlyGlobalStages.no_event_on_nonempty_event_free_run bits
      (nonempty_of_event_free bits safe noEvent) noEvent sample
    rw [accepted] at rejected
    cases rejected
  · rintro ⟨time, occurred⟩
    obtain ⟨sample, _, _, accepted, _, _, _⟩ :=
      SOnlyStageEvents.sourceEvent_reaches_observer bits time occurred
    exact ⟨sample, accepted⟩

end SOnlyEventEquivalence

#print axioms SOnlyEventEquivalence.event_exists_iff
