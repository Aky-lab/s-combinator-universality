# Review of the source and event proof interfaces

7 October 2026. Independent source-level review of the nine modules in
[the formal interface checkpoint](formal-event-interfaces.md), against the
pinned upstream definitions. Compilation and fresh replay are recorded
separately in the [execution evidence](../artifacts/formal-interfaces-2026-10-07/).

## Finding

The stated interfaces are semantically consistent with the intended models.
They prove uniform source-to-CTS simulation, exact event-language recognition,
and one-way global CTS-event-to-S-event completeness. No semantic defect was
found in the reviewed statements or their composition at this scope.

The principal remaining obligation is the converse and its first-event
refinement: accepted descendants must be justified by generated target
responses, and every witness at the first accepted sample must give the
correct frozen output.

## Source model and event indices

The source uses continuous alternating one-symbol deletion. Its empty state
keeps empty data and toggles phase; the upstream CTS total extension keeps
empty data and advances phase. Nineteen CTS advances exchange boundary phases
0 and 19. Empty states therefore agree exactly under the total simulation and
never generate a head event. Ordinary-step existence is proved separately
inside each nonempty block.

The FIFO and trajectory theorems quantify over arbitrary finite queues,
suffixes and natural iteration counts. The finite table proof covers only the
two phases and nineteen head symbols. `production_matches_published` verifies
the zero/one-based conversion for every source symbol, including the
implementation's default/modulo representation of the fixed table.

The quotient/remainder theorem covers every CTS index, not just known block
boundaries. It identifies the designated event exactly with a selected
published symbol 18 at source index `t/19` and offset `t % 19 = 17`. The
first-event theorem transfers the least source event to CTS index `19*n+17`.

## Labels, states and initial absence

The literal target pattern retains the route's `HasRoute` proof. Its label is
therefore fixed structurally even when another leaf has equal appender code.
The completed Local equivalence uses independent wildcard payloads and makes
no reachability inference from their syntax.

The finite observer state is a fixed product of Booleans. Its transitions
receive fixed pattern code and bounded child states. The proof-only semantic
specification is not called by the executable run. No source execution,
source-dependent register, term comparison or retained history is hidden in
a transition.

Its checked finite-cover length is `2^(pattern.size+1)`, using pattern
occurrences. This differs from the separately implemented canonical-subpattern
compression with 1,751 bits. Cover membership and length are formalized;
minimality, a separate NoDup theorem and Python implementation correspondence
are not part of this result. The executable run does not enumerate the cover.

The initial-absence argument includes arbitrary word length and all static
code. It bounds every descendant's head arity by four, whereas a completed
Local has arity five or six.

## Chronology, phase coherence and the actual witnessed sample

Exact-chain entries are post-contraction samples, so the indexed theorem's
`sampleIndex + index + 1` is the correct convention. Cursor-only bridges add
no contraction offset.

The target response costs

    3 + (2*7 + 1 + 2*19) = 56

contractions: FRAME, route and appender. The selected deletion adds one C4,
yielding the stage theorem's `+57`.

The global construction starts a new job at the original CTS configuration,
executes exactly r prior responses and returns c_r with coherent registers.
The selected-response scan preserves that phase. The stage prefix and
zero-mutation bridges are constructed from actual upstream recursion, rather
than supplied as new trajectory assumptions.

`sourceEvent_reaches_observer` derives earlier nonemptiness from the target
configuration's nonempty data. Its sole hypothesis is the target CTS event.
The conclusion locates a real F17 shell in an accepted root-reset sample and
identifies the public audit with exactly c_r's data word. It does not require
a public checkpoint at that sample.

## Audit, provenance and counter boundaries

The public audit reader takes the literal LLLR subterm and invokes the
seed-free carrier parser. Restoring the fixed true bit is sufficient for the
proved response witness. The theorem constructs one good witness; it does
not yet justify every match or select the first-preorder match.

The nine-state H6 abstraction is exact for all finite terms. Template
substitution covers arbitrary and repeated holes. Root Endpoint classification
alone does not classify descendant origins. The template transfer theorem
retains explicit scaffold-origin and inherited-hole premises, and rebuilt
completed ancestors retain an explicit root-registration premise.

These are extensional subtree-value certificates. They can support a global
absence/readout invariant, but do not themselves provide an address-indexed
birth history or whole-scheduler closure.

The counter kernel is uniform in natural exponents and copy counts. Its
exterior Command/Parity/Reset alignments remain independent parameters.
Positive decrement includes the essential odd-Reset protected branch;
exponent zero separately covers saturation, protection and deletion. FIFO
passes use consumed-length parity. These are the intended local equations,
not an implicit claim that independently chosen component alignments form a
whole source execution.

## Outstanding composition work

- Preserve generated-origin and label certificates across every mutation,
  copied subtree and rebuilt outer context.
- Exclude target descendants before the first target response and establish
  audit agreement for every witness at first acceptance.
- Complete global UT19 memory/alignment/restart invariants and the machine/BP2
  front end.
- Join the fixed numerical decoder and its operational bounds to that first
  accepted current tree.

The result manifest preserves exact source fingerprints for the replayed
checkpoint. Later local kernel extensions are separate proof increments.
