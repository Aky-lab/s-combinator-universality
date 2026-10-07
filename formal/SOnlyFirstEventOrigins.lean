import SOnlyCanonicalOrigins
import SOnlyCurrentDecoder

/-!
# Sharp creation-time origin licenses

Incomplete actual response rows preserve the old origin set. Completion adds
only the selected label and the literal post-deletion carrier. Consequently,
when the old origins exclude the target label, every accepted descendant at
completion has the same frozen audit, including the first-preorder witness.
These are local preservation and elimination results, not a global scheduler
closure assumption or an address-indexed causal identity claim.
-/
namespace SOnlyFirstEventOrigins
open PureSFormal PureSFormal.PureS
open SOnlyProvenance SOnlyProvenanceRows SOnlyGeneratedOrigins
open SOnlyEventPattern SOnlyEventTransfer
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

/-- Extension by exactly one label and one literal frozen carrier value. -/
def AddOrigin {program : CTS.Program} (allowed : OriginSet program)
    (label : ActionLabel program) (snapshot : Term) : OriginSet program :=
  fun observed audit => allowed observed audit ∨ (observed = label ∧ audit = snapshot)

theorem rootLicensed_mono
    {program : CTS.Program} {tree : Dispatcher.Tree (ActionLabel program)}
    {old new : OriginSet program} {term : Term}
    (mono : ∀ label snapshot, old label snapshot → new label snapshot)
    (licensed : RootLicensed program tree old term) : RootLicensed program tree new term := by
  intro view shape fresh
  obtain ⟨snapshot, audit, origin⟩ := licensed view shape fresh
  exact ⟨snapshot, audit, mono _ _ origin⟩

theorem licensed_mono
    {program : CTS.Program} {tree : Dispatcher.Tree (ActionLabel program)}
    {old new : OriginSet program} {term : Term}
    (mono : ∀ label snapshot, old label snapshot → new label snapshot)
    (licensed : Licensed program tree old term) : Licensed program tree new term := by
  exact allH6_of_descendants term (fun _ occurs h6 =>
    rootLicensed_mono mono (allH6_descendant licensed occurs h6))

theorem licensed_add
    {program : CTS.Program} {tree : Dispatcher.Tree (ActionLabel program)}
    {allowed : OriginSet program} {term : Term}
    (label : ActionLabel program) (snapshot : Term)
    (licensed : Licensed program tree allowed term) :
    Licensed program tree (AddOrigin allowed label snapshot) term :=
  licensed_mono (fun _ _ h => Or.inl h) licensed

/-- Crucially, a proper response row does not need the new origin at all. -/
theorem incomplete_response_licensed
    {program : CTS.Program} {tree : Dispatcher.Tree (ActionLabel program)}
    (allowed : OriginSet program) {route : Dispatcher.Route} {label : ActionLabel program}
    {path : Dispatcher.HasRoute tree route label}
    {bits : List Bool} {continuation carrier term : Term}
    (row : SchedulerResponseInvariant.ResponseRootMutation program tree path bits continuation carrier false term)
    (admissible : Carrier.Admissible continuation)
    (snapshotInv : ReachableAudit.Holds program tree bits continuation carrier)
    (hb : Licensed program tree allowed continuation) (bc : classify continuation = .other)
    (hv : Licensed program tree allowed carrier) : Licensed program tree allowed term := by
  apply response_row_carries row hb bc hv (holds_endpoint bc snapshotInv)
  intro _
  exact rejected_root_licensed allowed (row.failure admissible snapshotInv rfl).localBoundary

/-- At the final contraction the only additional license is the exact pair. -/
theorem response_licensed_add
    {program : CTS.Program} {tree : Dispatcher.Tree (ActionLabel program)}
    (allowed : OriginSet program) {route : Dispatcher.Route} {label : ActionLabel program}
    {path : Dispatcher.HasRoute tree route label}
    {bits : List Bool} {continuation carrier term : Term} {done : Bool}
    (row : SchedulerResponseInvariant.ResponseRootMutation program tree path bits continuation carrier done term)
    (admissible : Carrier.Admissible continuation)
    (snapshotInv : ReachableAudit.Holds program tree bits continuation carrier)
    (hb : Licensed program tree allowed continuation) (bc : classify continuation = .other)
    (hv : Licensed program tree allowed carrier) :
    Licensed program tree (AddOrigin allowed label carrier) term :=
  response_licensed _ row admissible snapshotInv (licensed_add label carrier hb) bc
    (licensed_add label carrier hv) (holds_endpoint bc snapshotInv) (Or.inr ⟨rfl, rfl⟩)

/-- Every literal address occurrence is a descendant value. -/
theorem descendant_of_subterm {source found : Term} {address : Address}
    (located : source.subterm? address = some found) : Descendant source found := by
  induction address generalizing source with
  | nil => simp only [Term.subterm?] at located; cases located; exact .root _
  | cons direction address ih =>
      cases source with
      | s => cases direction <;> simp [Term.subterm?] at located
      | app left right =>
          cases direction with
          | left => exact .left (ih located)
          | right => exact .right (ih located)

theorem fresh_shape_h6
    {program : CTS.Program} {tree : Dispatcher.Tree (ActionLabel program)}
    {view : CheckpointDecoder.LocalView program} {term : Term}
    (shape : CheckpointDecoder.LocalShape program tree view term)
    (fresh : view.status = .fresh) : classify term = .h4 := by
  obtain ⟨halt, dispatcher, seedAudit, continuationAudit, haltShape, _, eq⟩ := shape
  rw [fresh] at haltShape
  cases haltShape
  rw [eq]
  rfl

/-- Eliminate the actual license of an arbitrary accepted descendant. -/
theorem target_witness_origin
    {allowed : OriginSet SOnly38.program} {source shell : Term} {address : Address}
    (licensed : Licensed SOnly38.program SOnly38.dispatcher.tree allowed source)
    (located : source.subterm? address = some shell)
    (matched : targetPattern.matchesBool shell = true) :
    ∃ snapshot, shell.subterm? auditAddress = some snapshot ∧ allowed SOnly38.targetLabel snapshot := by
  obtain ⟨view, fresh, _, label, shape⟩ := (targetPattern_iff shell).mp matched
  have root := allH6_descendant licensed (descendant_of_subterm located) (fresh_shape_h6 shape fresh)
  obtain ⟨snapshot, audit, origin⟩ := root view shape fresh
  exact ⟨snapshot, audit, label ▸ origin⟩

/-- Target-free licenses exclude the finite observer at every occurrence. -/
theorem event_false_of_excludes
    {allowed : OriginSet SOnly38.program} {source : Term}
    (licensed : Licensed SOnly38.program SOnly38.dispatcher.tree allowed source)
    (excludes : ∀ snapshot, ¬ allowed SOnly38.targetLabel snapshot) :
    SOnlyObserver.event source = false := by
  cases accepted : SOnlyObserver.event source with
  | false => rfl
  | true =>
      obtain ⟨shell, found⟩ := (SOnlyCurrentDecoder.event_iff_found source).mp accepted
      obtain ⟨address, located, matched⟩ := SOnlyCurrentDecoder.findShell_sound source shell found
      obtain ⟨snapshot, _, origin⟩ := target_witness_origin licensed located matched
      exact (excludes snapshot origin).elim

/-- No accepted occurrence can pick an older, different frozen audit. -/
theorem all_target_audits
    {allowed : OriginSet SOnly38.program} {source snapshot : Term}
    (licensed : Licensed SOnly38.program SOnly38.dispatcher.tree
      (AddOrigin allowed SOnly38.targetLabel snapshot) source)
    (excludes : ∀ audit, ¬ allowed SOnly38.targetLabel audit)
    {address : Address} {shell : Term}
    (located : source.subterm? address = some shell)
    (matched : targetPattern.matchesBool shell = true) :
    shell.subterm? auditAddress = some snapshot := by
  obtain ⟨audit, read, origin⟩ := target_witness_origin licensed located matched
  rcases origin with old | ⟨_, eq⟩
  · exact (excludes audit old).elim
  · exact eq ▸ read

/-- The public, seed-free reader agrees on every target witness. -/
theorem all_target_prestates
    {allowed : OriginSet SOnly38.program} {source snapshot : Term} {suffix : List Bool}
    (licensed : Licensed SOnly38.program SOnly38.dispatcher.tree
      (AddOrigin allowed SOnly38.targetLabel snapshot) source)
    (excludes : ∀ audit, ¬ allowed SOnly38.targetLabel audit)
    (decoded : CheckpointDecoder.decodeCarrier? SOnly38.program SOnly38.dispatcher.tree snapshot = some suffix)
    {address : Address} {shell : Term}
    (located : source.subterm? address = some shell)
    (matched : targetPattern.matchesBool shell = true) :
    readPrestate SOnly38.program SOnly38.dispatcher.tree true shell = some (true :: suffix) := by
  have audit := all_target_audits licensed excludes located matched
  unfold readPrestate readAudit
  rw [audit]
  change (CheckpointDecoder.decodeCarrier? SOnly38.program SOnly38.dispatcher.tree snapshot).map (true :: ·) = _
  rw [decoded]
  rfl

/-- In particular the fixed first-preorder decoder reads the unique source
result; there is no history input and no selection of a convenient witness. -/
theorem current_read_of_added_origin
    {allowed : OriginSet SOnly38.program} {source snapshot : Term}
    {suffix : List Bool} {value : Nat}
    (licensed : Licensed SOnly38.program SOnly38.dispatcher.tree
      (AddOrigin allowed SOnly38.targetLabel snapshot) source)
    (excludes : ∀ audit, ¬ allowed SOnly38.targetLabel audit)
    (accepted : SOnlyObserver.event source = true)
    (decoded : CheckpointDecoder.decodeCarrier? SOnly38.program SOnly38.dispatcher.tree snapshot = some suffix)
    (numerical : SOnlyResultBits.readMachineBits (true :: suffix) = some value) :
    SOnlyCurrentDecoder.read source = some value := by
  apply SOnlyCurrentDecoder.read_of_all_witnesses source value accepted
  intro address shell located matched
  unfold SOnlyWitnessResult.readShell
  rw [all_target_prestates licensed excludes decoded located matched]
  exact numerical

end SOnlyFirstEventOrigins
#print axioms SOnlyFirstEventOrigins.incomplete_response_licensed
#print axioms SOnlyFirstEventOrigins.response_licensed_add
#print axioms SOnlyFirstEventOrigins.event_false_of_excludes
#print axioms SOnlyFirstEventOrigins.all_target_audits
#print axioms SOnlyFirstEventOrigins.current_read_of_added_origin
