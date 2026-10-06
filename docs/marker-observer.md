# Finite read-only marker observer

`s_only.marker_observer` independently reconstructs a finite tree-walking
observer for a **prospective, priority-selected fresh halt-field contraction**.
It reads the current bare S tree, starts at the root each time, and preserves
every occurrence while deciding this specific selected event.

## Mathematical source and exact attachment

The source specification is Cinematic Strawberry's
`cstrawberry/predictive-universe`, commit
`85a867988442fc423279341200f81634a1e65582`:

- [RootResetFiniteMarkerObserver.lean](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/Research/RootResetFiniteMarkerObserver.lean):
  `markerPattern`, `markerPattern_iff`, `observer`, `SelectedMarker`,
  `observer_all_input`, and `accepted_actual_root_event`.
- [RootResetFinitePrioritySelector.lean](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/Research/RootResetFinitePrioritySelector.lean):
  `selectionSpec` orders fresh response, marked handoff, and active endpoint,
  with root resets between declined passes.
- [RootResetRegisteredMarkerOccurrence.lean](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/Research/RootResetRegisteredMarkerOccurrence.lean):
  `commit_follow`, `commit_rdx`, and `contract_performs` identify the actual
  occurrence selected for COMMIT, including its parent context.

These sources were inspected only. No upstream code, Lean toolchain, or
package was installed or executed for this reconstruction. The existing
[MIT attribution](../third_party/cinematic-strawberry-MIT.txt) applies.

Write `B = S S`, `HALT_TAG = B S`, and `HALT = B HALT_TAG`. The literal test is

```text
App(literal(HALT), hole)
```

It runs **at the successful priority-selection cursor**, not at the root of
the response. A completed fresh Local has the left-associated shape

```text
(((HALT payload) dispatch) seedAudit) continuationAudit
```

so its LLL occurrence is exactly `HALT payload`. The existing COMMIT rows
select that LLL occurrence. The local restoring probe reads only its fixed
left-hand code and treats `payload` as an independent wildcard. In particular,
it neither decodes nor compares payload copies. One ordinary S contraction
at that occurrence yields

```text
HALT payload -> S payload (HALT_TAG payload)
```

which is the marked field and no longer matches the fresh-field pattern.
The synthetic tests independently construct both shapes and verify the
selected address, including the extra R under a registered pending parent.

Every successful priority pass is routed to the same literal test, including
successes that are not COMMIT events. A declined last priority pass answers
false immediately. **There is no Euler fallback.** For example, a tree whose
root is `HALT S` has a fresh-field shape and an ordinary root redex, but the
observer rejects it when priority selection declines. Applying the predicate
to the general reduction selector's final cursor would wrongly accept this
example because that selector additionally performs an Euler search.

## Static compilation and runtime boundary

```python
from s_only.cts import Program
from s_only.encoding import encode
from s_only.marker_observer import observer_table, accepts

table = observer_table(Program(('1', '')))
answer = accepts(encode(Program(('1', '')), '101'), table)
```

Compilation is explicit and sees only the fixed program and construction
budgets. Any positive number of binary appendants is supported within those
budgets; the original two-phase program `('1', '')` emits **257,308 states**.
The table retains only immutable `states` and `start`, with six observations
per state: S/application crossed with root/L/R incoming side. No program,
input seed, pattern, schedule, source state, or callable remains in the table.

Allowed runtime commands are `stay`, `L`, `R`, and `U`, with uniform absorbing
Boolean terminals. `Rdx` is rejected by the table validator. Each invocation
has precisely one finite control and one occurrence zipper; the zipper is
the only unbounded cursor context. The interpreter has no extra stack,
runtime compiler, tree hash, full structural parser, checkpoint reader,
source evaluator, tick budget, or previous-invocation memory. Both outcomes
preserve the entire ambient tree. The final cursor need not be at the root;
only each invocation's initial cursor is reset there.

The observer reuses the independently reconstructed program-static priority
fragments. Its extra literal probe is restoring on success and failure.
Thus, if `P(t)` denotes the priority worker's Boolean result and endpoint,
the composition computes exactly

```text
P(t).ready and literal_fresh_halt_field(P(t).endpoint.focus)
```

Root ascent between priority passes preserves the ambient tree and is
strictly depth-decreasing. Priority-fragment termination follows the same
carrier, scope, and strict-edge arguments documented for the
[root selector](root-selector.md). The added shape probe has fixed size and
is acyclic. This gives the intended compositional all-input termination
argument; the Python reconstruction's correspondence and termination have
not been independently machine-checked in Lean. A hand-built `ObserverTable`
can contain loops: its validator proves interface finiteness and read-only
commands, not termination of arbitrary supplied graphs.

For a terminating run on an N-occurrence tree with Q control states, there
are only NQ possible read-only configurations. Repeating one would repeat
the future forever, so a terminating deterministic run takes fewer than NQ
nonterminal ticks. `linear_coefficient` exposes Q for external test bounds;
it is a counting consequence conditional on termination, not an independent
termination certificate or an input-time counter.

The construction options are `max_states`, `max_appendant_bits` (default
128), and `max_phases` (default 16). `None` disables the corresponding cap.
State caps constrain emitted rows, not all temporary compiler memory. A tiny
state cap rejects before program-dependent pattern expansion. Syntax-cap
violations and host recursion exhaustion raise `CompilationLimit`. The
tests cover invalid and Boolean-valued caps, early rejection, and the exact
state-count success/failure boundary.

## Event timing is separate from checkpoint timing

Samples below are numbered from zero before any contraction. At sample n,
the observer reports whether the **next priority-selected contraction** has
the marker shape. The next sample contains the contracted, marked field.

For `('1', '')`, bounded native runs independently selected each next
rewrite from the current tree. Results are:

| Seed | Last tested sample | True marker samples | Decodable checkpoint samples and data |
| --- | ---: | --- | --- |
| empty | 20 | 19 | 0: empty; 20: empty |
| `0` | 21 | 20 | 0: `0`; 21: empty |
| `1` | 87 | 55, 86 | 0: `1`; 22: `1`; 87: empty |
| `00` | 81 | 51, 80 | 0: `00`; 20: `0`; 81: empty |
| `10` | 85 | none | 0: `10`; 22: `01`; 85: `1` |
| `11` | 85 | none | 0: `11`; 22: `11`; 85: `1` |

All **86** samples of the original published `101` path reject. This is
bounded evidence only; it is not a nonhalting conclusion for that seed.
The `1` case is especially useful: a marker is already selected at sample
55, while the first decoded empty checkpoint is at sample 87. Markers can
also recur in later native work. They are not pointwise equal to checkpoint
emptiness, and false at one sample does not establish nonhalting.

For arbitrary malformed trees, acceptance is the specified syntactic
selection property, not a certificate that a tree came from an encoded CTS
run. The upstream source relates existence of such an event on its selected
encoded trajectory to eventual ordinary CTS emptiness. The tests here do
not independently prove that full trajectory theorem for the Python port.

The compact **482-phase Neary fixture** uses a different source predicate:
phase 170 with head 1 on a **nonempty** word. That target requires a dedicated
finite observer and the larger program's controller construction.

## Finite tree walker versus bottom-up tree automaton

This module's output is a finite **tree-walking** graph. An explicit bottom-up
automaton and an agreement witness are separate artifacts.

The pinned source's
[RootResetMarkerTreeAutomaton.lean](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/Research/RootResetMarkerTreeAutomaton.lean)
defines an explicit bottom-up automaton via
`FiniteWorkerTreeAutomaton.automaton (observer program layout)` and proves
`automaton_accepts_eq_observer` on every S tree. The precise
[FiniteWorkerTreeAutomaton interface](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/Research/FiniteWorkerTreeAutomaton.lean)
requires a finite worker with decidable control equality, terminal behavior,
read-only behavior, and a reached configuration fixed by one more step.
It reindexes finite controls and invokes the closed-set/powerset compiler.
The marker source supplies the fixed configuration from its all-input
observer bound. Porting the bottom-up state space and its agreement witness
would extend the present walking implementation.

## Reproducible checks

```sh
python -m unittest discover -s tests -p test_marker_observer.py -v
```

The test-only structural predicate spells out `HALT` directly and never
uses the generated marker pattern. A separately assembled priority worker
ends before the shape probe; the tests compare the observer to that worker
plus the independent structural predicate. This isolates composition and
local-shape checking and reuses the previously tested priority fragments.

Coverage includes all original samples; native empty/nonempty seeds;
synthetic fresh/marked fields and all dispatcher labels; bare marker-shaped
redex rejection without fallback; 626 exhaustive small trees; pattern-shaped
malformed trees with unrelated holes and ambient contexts; terminal
absorption; root reset; immutable graph/configuration shape; mutation and
dynamic-target rejection; compile-time budgets; and periods 1, 3, and 5 with
unbalanced routes. Runtime isolation disables compilers, structural readers,
source stepping, tree equality/hashing/serialization, and reduction helpers
while repeatedly observing reordered positive and negative trees.

### Native event report

```sh
timeout 600s bash -c 'ulimit -v 2097152; python -m tools.marker_observer_report --deterministic --output /tmp/marker-observer.json'
cmp results/marker_observer.json /tmp/marker-observer.json
```

[The deterministic report](../results/marker_observer.json) follows seeds
`101`, `1`, `0`, and the empty word for 100 contractions each. It records
all 404 Boolean samples, 400 independently audited contractions, 12 marker
signals, and 12 structural checkpoints. Exact prefix tokens and occurrence
frame identities check read-only traversal; every native result is compared
with a separately applied single-occurrence rewrite.

The observer uses 5,276,638 microticks in total, and native selection uses
5,180,062. The largest observed tree has 341,519 nodes. The original `101`
seed produces false on all 101 samples in this bounded extension. Marker
indices through sample 100 are:

| Seed | True samples |
| --- | --- |
| `101` | none |
| `1` | 55, 86 |
| `0` | 20, 43, 52, 72, 81 |
| empty | 19, 41, 50, 69, 78 |

Only the fixed graph and current term enter either machine. Reader calls,
source comparisons, exact-token audits, counters, budgets and digests belong
to the report driver. Its internal deadline is soft; the command above adds
an external process timeout and a 2 GiB address-space limit.
