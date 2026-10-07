# Mechanized source and event interfaces

The nine modules in this checkpoint formalize the one-hot source translation,
target event language, initial event absence, native response samples, global
event completeness, and local provenance/counter kernels over the pinned CTS-to-S construction. The results are uniform in
finite input words and current S trees.

## Exact one-hot simulation

`SOnlySource.trajectory_simulation` proves, for either alternating phase and
every source configuration `c`,

    CTS.iterate program (19*n) (encode c) = encode (iterate n c).

The FIFO-prefix lemma quantifies over arbitrary suffixes. The 38 cases in the
literal table check are only the two phases and nineteen possible head symbols;
they impose no bound on queue length or number of steps. Each interior offset
of a nonempty block has an ordinary CTS step.

`event_at_arbitrary_time` identifies every CTS target prestate:

    Event(CTS.iterate program t (encode c))
      iff Selected(iterate (t/19) c) and t mod 19 = 17.

Consequently a first selected source event at n becomes the first CTS event at
exactly 19*n+17. Empty states use a phase-advancing total extension in both
models and never create a head event.

## Literal event and finite observer

`SOnlyEventPattern.targetPattern` uses the pinned dispatcher's literal route
0100011 and its label (17,true), with exactly nineteen completed history
arguments. `targetPattern_iff` characterizes matching on every finite tree as
a fresh Local with that route and label. Equal action code at another leaf
cannot change its label.

`SOnlyObserver` constructs a deterministic bottom-up automaton for every
upstream independent-hole Pattern. The leaf transition and application
transition receive only the node constructor, fixed pattern code, and bounded
child states. The proof gives an explicit finite cover and exact descendant
occurrence semantics. The event instance uses the same targetPattern, not a
second separately justified grammar.

The mechanized cover has one bit per pattern occurrence and one descendant
bit, hence finite-cover length 2^(pattern.size+1). Its existence proof enumerates the
mathematical cube; evaluating a term calls only the leaf/join transitions.
The Python implementation's 1,751-bit shared-subpattern cover is a separate
compression of this language.

`SOnlyInitial.initial_event_false` proves the event absent from every encoded
initial term. Its inductive argument covers arbitrary words, appendants and
dispatch trees: every initial subtree has head arity at most four, while a
completed Local has arity five or six.

## Exact samples and frozen output audits

`SOnlyEventTransfer.exactChain_sample` assigns every element of an imported
exact mutation chain its precise persistent contraction index. Its root-reset
corollary uses whole-term equality at that same index.

The audit lemmas identify the literal LLLR snapshot of a fresh Local. The
public seed-free decoder recovers the deleted carrier word; restoring the
fixed head bit recovers the selected trace’s pre-transition word. `SelectedResponseTrace.targetDecode`
discharges the decoder premise for an actual selected response.

`SOnlyEventResponse.target_final_sample` places a target response completion
exactly 56 contractions after response entry. The count includes FRAME,
dispatcher route and nineteen appender bits; it excludes the preceding C4
contraction. The result holds under arbitrary outer zipper parents, including
jobs without a public checkpoint.

The event/readout theorem starts from an actual persistent sample and a proved
cursor-only bridge into its response script. It concludes that the specified
root-reset sample contains the literal target shell and its public audit
returns true::suffix. These entry premises are visible in the statement.

## Global event completeness

`SOnlyStageEvents.sourceEvent_reaches_observer` supplies the actual entry
premises from the initial encoder. Its only hypothesis is a designated event
at CTS prestate index r. Empty data is absorbing, so this hypothesis already
implies nonemptiness at every earlier index.

The construction traverses the previous scheduler stages, enters the first
job of stage r+1, and executes its first r responses. The imported coherent
phase chain identifies the next response with exactly the phase/head of c_r.
One selected C4 and the 56 response contractions yield the witnessed sample
at `firstJobPreResponseTime bits r + 57`.

The conclusion gives an actual root-reset sample accepted by the finite
observer, a located F17 shell, and public readout equal to the exact data word
of c_r. It establishes one-way global event completeness without a supplied
script-entry bridge, an assumed generated-trajectory predicate, or a public
checkpoint at the observation time.

## Local provenance and raw counter kernels

`SOnlyProvenance` gives an exact nine-state congruence for the reserved H6
prefix. It proves the dangerous continuation boundary is precisely an
H-headed arity-five endpoint; the actual normal-response root constructors
have safe endpoint classes. Generic appender, dispatcher, numeral and clock
code satisfy the required static classifier conditions.

Its template theorem decomposes every H6 subtree of a substituted template
into a scaffold node or a descendant of an input hole. Repeated and arbitrary
holes are permitted. Local inheritance lemmas cover the fresh-shell birth,
right-hand histories, rebuilt completed ancestors and the frozen LLLR field.
The scaffold and inherited-hole certificates remain explicit premises. These
are extensional subtree-value invariants, not a completed address-indexed
causal history for the entire scheduler.

`SOnlyCounter` proves the UT19 raw counter equations by induction on arbitrary
natural exponents. It includes increment, protected increment, the distinct
even/odd Reset outcomes of a positive decrement, all exponent-zero cases,
and the protected restart C(2)→C(3). FIFO pass correctness, parity equations,
counter-alphabet closure and absence of selected 18 in counter stages are
also proved. Exterior alignments remain parameters until the global schedule
is supplied.

## Verification

All nine modules passed a combined official Lean 4.33.1 fresh-kernel replay
in 117.619 seconds. The import-only wrapper used the pinned upstream closure,
the checked SOnly38 instance and frozen read-only project outputs. Queries of
242 public types, definitions and theorem declarations reported only
`propext`, `Quot.sound` and `Classical.choice`.

Post-replay rehashing found no changes in 426 pinned source/config files,
424 original outputs, 17,505 toolchain files or 21 new source/output/helper
files. The [result manifest](../results/formal_event_interfaces.json) links
each source identity and final build log. [Execution evidence](../artifacts/formal-interfaces-2026-10-07/)
preserves the wrapper, audit, manifests and resource-guard receipts.

An independent [semantic review](formal-event-interfaces-review.md) checked
the source models, quantified assumptions, literal labels, finite states,
phase coherence, contraction counts and numerical boundaries.

## Composition frontier

The remaining global direction is event soundness and firstness: every
accepted descendant must be licensed by a real target-response origin, with
no such origin preceding the first source target response. The audit proof
must then cover every witness at the first accepting sample, including the
first-preorder witness selected by the bounded reader.

The register-machine/BP2 compiler, global UT19 memory/scheduling/restart
invariants, and final numeric decoder composition are distinct source/output
layers. The local counter kernel and event-completeness theorem provide
interfaces for these inductions.
