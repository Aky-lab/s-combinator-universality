# Scheduler labels, memory kernels and current-tree results

This checkpoint adds seven modules to the [source/event interfaces](formal-event-interfaces.md).
The combined sixteen-module project closure passed official Lean 4.33.1
fresh-kernel replay in 123.335 seconds. The additional 160 declaration queries,
combined with the earlier 242, reported only `propext`, `Quot.sound` and
`Classical.choice`. All frozen proof, pinned source, original output and
toolchain hashes were unchanged afterward.

[Result manifest](../results/formal_extended_kernels.json) ·
[Execution evidence](../artifacts/formal-extensions-2026-10-07/)

## Actual scheduler labels

`SOnlyResponseLabels` strengthens the actual selected-response, job and stage
constructors with source-indexed labels. Each observed normal-response control
has the label of a genuine CTS prestate within the relevant source prefix.
Exact-chain uniqueness transfers the property to other certified chains of
the same length and endpoint.

`no_target_script_on_event_free_run` excludes target normal-response controls
at every persistent contraction sample when all CTS prestates are nonempty
and no source target event occurs. `no_target_script_before_firstJob_response`
excludes them through the exact earlier-stage and first-job prefix preceding
the first source target response.

The label property supplies a source-index witness and bound. It is not a
monotone index map of every response or a statement about every controller
microtick. Turning control-label exclusion into absence of target-shaped
subtrees requires the generated-origin invariant.

## Response and context inheritance

`SOnlyProvenanceRows` attaches the nine-state H6 analysis to the actual upstream
route, appender and response constructors. Every H6 subtree of a response
residual is inherited from its original carrier or continuation, or is the
current response root. The latter has the literal original carrier at LLLR.

Further lemmas cover C4 and tombstones, mutable Base syntax, actual action
history contexts, pending frames and arbitrary-depth certified outer contexts.
Inherited-hole certificates, endpoint classes and old root registrations are
explicit. An unrestricted public Local grammar is not used as a substitute
for generated-parent evidence.

## Uniform local memory algebra

`SOnlyMemory` proves three-pass behavior for arbitrary finite cell lists:
normal update, either odd-Reset restoration, fixed inverter preservation,
inclusive prefix-XOR evolution and current width parity. It identifies the
odd-Parity marker word and its immediate selected event.

Its safety theorem connects an ordinary component prefix to actual source
microsteps, with arbitrary following suffix. Earlier legal component passes
have no selected 18; nonempty memory components have nonempty Parity and Reset
intermediates. The global alignment and epoch schedule remain the conditions
that choose those legal component cases.

## Current-bitword numerical interface

`SOnlyResult` locates the first maximal run of published symbol 16. If the
preceding word contains no 16 and the following word is empty or does not
start with 16, it reads a run of length `4^(x+1)` as x. Integer bit tests and
`log2` implement the power-of-four check. The final fixed inverse maps
`2*v+3` to v.

`SOnlyResultBits` decodes fixed 19-bit one-hot blocks to published one-based
labels. It proves this for every finite encoded source word with sufficient
structural fuel. The supplied fuel is the current bit length, while each
recursive iteration consumes an entire block; it does not bound a simulated
computation.

At an ordinary phase-17 event, the current word is exactly `10` followed by
the encoded remainder of the source queue. The reader restores the known head
18 and decodes the remaining whole blocks. The proof includes the seventeen
zero-deletion offset and the zero-based/source versus one-based/published
label conversion.

This numerical projection is deliberately narrower than a full Reset grammar
verification theorem: it extracts a correct first counter under the displayed
counter-form hypotheses. It may accept structurally malformed surrounding
memories. The complete Python parser has additional syntax checks; no general
implementation-equivalence claim is made here.

## An actual numerical witness and a fixed preorder decoder

`SOnlyWitnessResult.numerical_witness` joins source-word simulation, global
native event completeness, bit restoration and counter arithmetic. Given an
actual selected source configuration with the stated first-counter form, it
constructs a real accepted S sample and a located target shell whose seed-free
current-tree audit reads the correct natural number.

`SOnlyCurrentDecoder` fixes the selection order: current root, then left
subtree, then right subtree. The first matching shell is decoded even if its
payload is malformed; a later convenient witness is not substituted. Search
succeeds exactly when the finite event observer accepts.

`read_of_all_witnesses` isolates the remaining output condition: if every
matching occurrence in the accepted current tree decodes to v, this fixed
preorder decoder returns v. The numerical-witness theorem supplies one good
occurrence. Global first-event provenance must establish the all-witness
certificate.

## Remaining global composition

The two active inductions are generated S-tree origin preservation across
whole jobs/stages, and global BP2-to-UT19 scheduling/restart correctness.
Sharp first acceptance and universal audit agreement then connect the fixed
observer and preorder result reader. The register-machine front end and
operational bounds complete the outer interfaces.
