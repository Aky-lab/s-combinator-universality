# Independent review of the bounded current-S event reader

6 October 2026. Reviewed `s_only/s_event_readout.py`, its public carrier
reference in `s_only/cts_reader.py`, the downstream `ut19_readout.py`, and the
conditional theorem in `s-event-readout.md`. This review makes no production
edits and executes no native UT19 reduction, downloaded code, or installer.

## Verdict

Scoped signoff on the structural decoder, its sufficient **charged-work**
bound, and the explicitly conditional numerical interface. No production
correctness defect was found in the reviewed runtime paths. The one requested
complexity qualification is resolved in the reviewed documentation:
unrestricted caller-supplied cap integers contribute their own bit-length to
real bit cost and working memory.

This is a proof/implementation audit supported by adversarial finite tests,
not a replacement for the imported source simulation, scheduler coverage,
all-sample transfer, or universal Python-port correspondence.

## Resolved clarification: integer cap sizes

`_Budget.take` evaluates `limit - used` on every charged operation. The exact
plain-integer validation accepts an arbitrarily large nonnegative `max_work`.
Consequently a fixed one-node S input with `max_work = 1 << K` already performs
arithmetic on a K-bit integer. `max_word_bits - 1` and the downstream
`19 * max_queue_symbols` provide other examples. Charged work is unchanged,
but real bit cost is not bounded solely by the graph node count N and fixed
code size C for arbitrary caller caps.

The corrected documentation now makes the following distinctions:

- `W(N,C) = 4096 (N+1)^3 (C+1)^2` remains the charged-work bound.
- The N+C-only bit-cost theorem applies to fixed/default caps, or caps whose
  bit-length is appropriately bounded by N+C. In particular, choosing the
  actual N for the derived-limit helper meets this condition.
- The fully parameterized API includes the sum K of the six cap fields'
  bit-lengths as an input-size parameter. A conservative polynomial bound in
  N+C+K follows by the same argument. Space must include cap integers and
  their temporary arithmetic as well, now explicitly stated as O(K) extra bits.
- If the helper is given only an upper bound n, the direct derived statement
  is in n+C. An arbitrarily loose n cannot silently be replaced by actual N
  in an N+C-only cost assertion.

The final revised paragraph was re-inspected. This is a qualification of the
complexity model, not a halting/readout counterexample or a request to cap
otherwise legal integer arguments.

## Structural validation and equality

Exact class checks precede reads of application children. Input equality,
hashing, cached occurrence counts, and user-defined methods are not used.
The iterative snapshot holds node and captured-child references, so identity
keys remain live. On a fixed immutable input, active identities are exactly
DFS ancestors: revisiting an active identity detects a directed cycle, while
a completed shared child is reused. All input syntax is validated, including
unused audits and siblings after an already visible event.

For A distinct applications, snapshot traversal has `1 + 3A` pops. A nonempty
valid finite DAG has at least one atom, so this is at most `3N`. The captured
postorder edges strictly decrease, and subsequent matching/parsing never
returns to the mutable Python object graph. Malformed objects may cause an
earlier budget refusal; neither refusal nor rejection is a source-halting
answer. Concurrent mutation remains outside the immutable-input contract.

Structural comparison is exact equality of unfolded S/App trees, without
unfolding those trees. Every newly visited ordered index pair pushes at most
two pairs. Thus at most `2NM+1` pair pops occur between arenas of sizes N,M,
including duplicate pops. The same-arena identity shortcut is explicitly
disabled for fixed-code comparisons: equal integers from separate arenas do
not mean equal nodes. Different sharing patterns and independently allocated
atoms/copies do not affect the result. Repeated Base continuations use this
full equality test; opaque audits do not.

## Carrier correspondence and termination

The bounded recognizers reproduce the ordered reference grammar:

1. Base with an active fixed-program environment, primitive b, equal actual
   continuations, and a dormant fixed-program environment. Its queue is then
   required to be a cell spine ending at S; a malformed spine cannot fall
   through to Local parsing.
2. Fresh/marked Local with the same finite halt, seed, continuation, route,
   dormant-code, PI, and label-determined history-count checks.
3. Live cell or tombstone with its canonical strict predecessor.

The route follows a trusted factory-produced finite dispatch tree. Every
successful outer carrier iteration selects a strict input descendant,
including transition into a Base. There are at most N+1 iterations, even
when many distinct paths in the input share subgraphs. Every returned bit
comes from a different node on that decreasing path, so the carrier word
has length at most N. Reversing the collected outside-in live labels is
ordinary string assembly, not undoing an action or replaying history.

Malformed finite syntax is covered by the same work bounds as successful
syntax: failed Base/Local alternatives can perform comparisons, but cannot
restart at an ancestor or create a new recursive search. Static grammar
mutation or direct hostile construction of `CompiledCarrierReader` is outside
the factory-only trusted-code contract and was not treated as an input attack.

## Work accounting

The following conservative envelope covers the reviewed loops:

- `3N` validation pops;
- `(N+1)(2N^2+1)` for repeated Base-continuation equality attempts;
- `(N+1)(C+10)(2NC+1)` for fixed-code comparisons;
- `(40C+80)(N+1)` for constructor, arity, route, and history inspections;
- `N(C+1)+2N+6` for pattern evaluation, witness extraction, and LLLR lookup;
- at most `2N+1` for retained bits and carrier string assembly;
- `1024(N+2)` reserved before constructing and scanning the restored word.

The ten non-route fixed comparisons cover two Base environment checks and b,
two halt alternatives, PI, two live alternatives, and two tombstone
alternatives. Selected route length and completed history count are each
bounded by C. Arbitrary continuation equality occurs at most once per Base
attempt. Failed alternatives are therefore included.

For N >= 1 and C >= 32, each displayed term is dominated by a constant times
`P=(N+1)^3(C+1)^2`; even loose constants sum to less than 2,150P, below 4,096P.
The generic reader omits the event-specific work, so its advertised bound
also suffices. The bound is deliberately loose, not a performance estimate.

The reservation is sufficient for the concrete downstream reader: it scans
binary input, consumes fixed 19-character blocks with a constant number of
string operations, advances its Reset cursor monotonically, counts supplied
runs, checks powers of four with integer bit operations, and emits at most
one tuple entry per counter run. It never constructs an exponential-size
number or allocates according to a cap. Restored word length is at most N+1;
logical symbol count, counter count, and total output bit count are likewise
at most N+1. The derived non-work caps consequently cannot refuse an otherwise
valid output within the stated node bound.

This envelope counts charged structural/string units. Hash-table operations,
bitvectors, integer arithmetic, and actual Python execution require the
separate bit-cost qualification above.

## Witness and semantic interface

The bottom-up pattern matcher evaluates each fixed descriptor at each input
DAG node. Independent wildcard matches introduce no accidental equality
constraints. Its descendant bit is extensional even for shared children.
Stopping at a root match, otherwise descending left whenever the left child
contains any match, selects exactly the first preorder occurrence.

The numerical reader commits to that witness. A malformed first payload
rejects; it does not search for a later payload that happens to decode. The
LLLR path is structurally guaranteed by the accepted F17 root. It reads that
fresh halt audit, restores the known deleted 1, and invokes the phase-17 CTS
result grammar. The current action accumulator is irrelevant to the answer.

The source theorem remains conditional on reaching the first accepting S
sample under the documented generated scheduler and correspondence premises.
A fabricated shell can pass both syntax and numeric decoding; an arbitrary
later sample can retain an old event. Neither case establishes firstness or
source identity. The documentation correctly keeps those semantic obligations
outside the runtime decoder. Runtime paths contain no source evaluator,
reducer, compiler, clock, file read, trace lookup, or private reference parser.

## Independent verification

`tests/test_s_event_readout_review.py` adds tests for:

- precise snapshot alias indices, distinct S identities, and captured edges;
- every public entry's missing-slot, hidden-cycle, and invalid-sibling cases;
- malformed first-witness priority and events inside opaque halt audits;
- every UT19 phase/bit label, including repeated appender codes;
- cross-arena numerical index collisions;
- 800 deterministic DAG-equality comparisons against canonical shapes;
- equal trees with different highly shared representations;
- irregular-dispatch carrier/mutation differential cases with derived caps;
- the exact work-reservation boundary and legal huge-integer cap semantics.

All 9 independent tests passed in 27.272 seconds under a hard 180-second
process timeout and a 1-GiB address-space limit. The differential test includes
246 carrier/mutation cases; the equality test includes 800 comparisons.

```sh
timeout 180s sh -c 'ulimit -v 1048576; python -B -m unittest discover -s tests -p test_s_event_readout_review.py -v'
```

The combined rerun of the event, independent-review, carrier, and UT19 reader
suites passed all 69 tests in 84.532 seconds under the same hard
180-second/1-GiB guard:

```sh
timeout 180s sh -c 'ulimit -v 1048576; PYTHONPATH=tests python -B -m unittest test_s_event_readout test_s_event_readout_review test_cts_reader test_ut19_readout -v'
```

The integer-cap time and storage qualifications above were resolved and
re-inspected before this final signoff. No production code changes were needed.
