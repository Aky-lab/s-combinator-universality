# Exact finite-selector control minimization

`s_only/control_minimization.py` is an optional **post-compilation** experiment.
It quotients an immutable `root_selector.SelectorTable` without changing the
primitive interpreter, compiler, observation alphabet, or invocation protocol.
All original states are included, even states unreachable from the start.
The graph is minimized for arbitrary strings of all six observations, a
stronger requirement than equality only on the encoded sample trajectory.

The first bounded legacy measurement reduced **257,299 to 218,111 controls**:
39,188 fewer states (15.23%). Every one of the original 1,543,794 observation
entries passed the independent finite quotient-witness check. This does not
remove `stay` instructions, shorten traces, or assert a construction-memory
improvement. The original graph must exist before this pass starts.
The generic two-phase program `("0", "10")` independently reduced **342,539
to 289,582 controls**, removing 52,957 (15.46%).

## Interface and runtime boundary

```python
from s_only.control_minimization import minimize, verify_quotient
from s_only.root_selector import selector_table, execute

original = selector_table()
result = minimize(original, max_states=1_000_000)
verify_quotient(original, result)
runtime_table = result.table
# execute(term, runtime_table) uses the existing interpreter unchanged.
```

`MinimizationResult` is an immutable pair:

- `table`: another validated `SelectorTable`, containing only `states` and
  `start`, suitable for the existing runtime;
- `state_map`: a compile-time tuple mapping **every** original control to its
  quotient control. It is the finite witness and is unnecessary at runtime.

Only the table needs to survive into execution. Keeping `result`, the original
table, or an existing compiler cache can retain extra storage; callers seeking
storage savings must release those separately. The input-state cap is checked
before minimization indexes are allocated. It is not a time bound and cannot
undo or bound the preceding compilation. The CLI passes its state cap into the
generic compiler; legacy compilation has no state-budget parameter.

## Exact equivalence theorem

Let `A` be the fixed six-element observation alphabet
`(S/application) × (root/L/R)`. For a control `q` and observation `a`, let
`out(q,a)` be its command and `next(q,a)` its next control. For the two
absorbing commands `normal` and `contracted`, temporarily define `next(q,a)=q`.
These conceptual self-edges are used only by refinement; output terminal
instructions still have `next_state=None`.

A relation `~` is an exact-output bisimulation when, whenever `p ~ q`, every
`a` in `A` satisfies:

1. `out(p,a) = out(q,a)`; and
2. `next(p,a) ~ next(q,a)`.

In particular, `stay`, L, R, U, Rdx, `normal`, and `contracted` are seven
different outputs. A stay is a full microtick, never an epsilon transition.

**Finite quotient theorem.** The partition produced by `minimize` is the
coarsest exact-output bisimulation on the entire supplied graph. Its quotient
and mapped start produce exactly the same command sequence for every finite
observation word, from every original state and its mapped state. Infinite
observation streams have equal commands at every finite position as well.

**Partition argument.** Initially two states share a block exactly when their
six-output vectors agree. Given a splitter block `B` and observation `a`,
each block is split by membership in `Pre_a(B)`. No bisimulation class can be
split: its related successors must agree on membership in any union of current
bisimulation classes. All initial blocks are scheduled as splitters for each
observation. When a block splits, its larger half retains its identifier and
its smaller half is scheduled for all six observations. If the old block is
still pending for an observation, its pending entry now processes the larger
half and the new entry processes the smaller. If already processed, processing
the smaller half suffices: the larger is the old block minus the smaller, and
every source state has exactly one successor for that observation. This is
the standard complement invariant of smaller-half partition refinement.
The worklist eventually empties because each proper split adds a block and
there are at most as many blocks as original states. The resulting partition
is stable under every predecessor operation, hence is a bisimulation. Since
no bisimulation class was separated, it is the coarsest one.

The quotient chooses a representative for each block and maps its successors
to blocks; stability makes this independent of the representative. Command
trace equality follows by induction on observation-word length. Conversely,
states with equal traces for every finite observation word have equal outputs
and trace-equivalent successors, so are bisimilar. Thus this is a minimal
Mealy quotient over the unrestricted six-observation alphabet, **not** a claim
of minimum controller size under realizable-tree observations, epsilon-step
equivalence, or reachability pruning.

### Transfer to actual S-tree execution

Start the original and quotient machines on the same occurrence zipper, in
controls related by `state_map`. Equal zippers have the same next observation.
The witness gives equal next primitives and related successor controls:

- a stay leaves both cursors unchanged;
- L, R, or U makes the same occurrence move in both machines;
- Rdx sees the same focus and context, passes or fails the same native-redex
  guard, and, if legal, produces equal replacement terms and contexts;
- `normal` and `contracted` remain separately absorbing; an Rdx state remains
  an Rdx state and its successor remains contracted.

Induction gives identical cursors and command traces through every microtick.
This includes the exact selected occurrence, contraction legality, the single
contraction and resulting erasure, terminal status, and finite tick counts.
An illegal primitive in an arbitrary hand-written original table fails at the
same point in the quotient; minimization does not repair unsafe inputs or
prove an arbitrary input controller terminates. For valid compiled tables,
existing all-input safety and termination arguments transfer unchanged.
Divergent behavior is preserved too, by equality of every finite prefix.

The quotient start is exactly `state_map[original.start]`. Each invocation
still supplies a fresh root zipper and that same start control. No prior
cursor, tree size, source-machine state, runtime counter, pattern, or witness
is consulted. Root-reset behavior therefore survives for all finite input
trees, including malformed encodings and repeated invocations.

### Independently checkable certificate

`verify_quotient` does not run partition refinement. It checks map size,
immutable integer targets, surjectivity, mapped start, and, for every original
state and every observation, equality of outputs and mapped successors.
These local checks alone establish the trace-preservation theorem by the
induction above. They do **not** independently certify minimality. Small-graph
tests check minimality against a separate all-pairs greatest-fixed-point
oracle rather than a second copy of the refinement algorithm.

## Refinement cost

Write `N` for controls and `E=6N` for the totalized edges. Six inverse-edge
indexes use compact integer linked lists, rather than Python lists per edge
target. A partition is stored as contiguous blocks in a state array, with
inverse positions and a state-to-block map. Gathering predecessors swaps each
marked state into its block's marked suffix; splitting touches only the
marked states and the new smaller half. The splitter is snapshotted before
swaps so that moving its own predecessor states cannot corrupt its traversal.

Only smaller halves receive new worklist entries. Any state can enter such a
new half at most `floor(log2 N)` times. Inverse-edge visits, splitter snapshots,
and relabelings are therefore **O(E log N)** in the usual constant-time-index
model, with **O(E+N)** auxiliary storage. For the fixed six-letter alphabet,
these simplify to O(N log N) work and O(N) storage. There is no repeated
whole-graph scan per distinguishing depth. A 12,000-state distinguishable
chain exercises this case in the tests. Python allocation and dictionary
costs affect wall-clock measurements; no numeric speed or memory bound is
inferred solely from these asymptotic statements.

## Reproduction and measurements

The following commands run only this project's independently reconstructed
Python code; no pinned upstream code is executed or installed. External
timeouts and address-space limits are part of the experiment driver, not
finite controller state. Run the large cases sequentially:

```sh
timeout 180s bash -c 'ulimit -v 1200000; python -m unittest discover -s tests -p test_control_minimization.py -v'
timeout 120s bash -c 'ulimit -v 1200000; python -m s_only.control_minimization --output /tmp/legacy-quotient.json'
timeout 120s bash -c 'ulimit -v 1200000; python -m s_only.control_minimization --program 0 10 --output /tmp/generic-quotient.json'
```

The deterministic JSON report includes original and quotient graph digests,
the complete state-map digest, state counts, the checked observation-entry
count, and successful witness verification. It contains no timing fields.
Repeated invocation on an unchanged compiler therefore supports a byte-for-byte
report comparison. The witness itself is reproducible from `minimize`; a hash
is a reproducibility label, not a substitute for the exhaustive witness check.

Recorded reports (2026-10-06):

| Controller | Original states | Quotient states | Entries verified |
| --- | ---: | ---: | ---: |
| [Legacy fixture](../results/control_quotient_legacy.json) | 257,299 | 218,111 | 1,543,794 |
| [Program `(0, 10)`](../results/control_quotient_generic.json) | 342,539 | 289,582 | 2,055,234 |

```sh
cmp results/control_quotient_legacy.json /tmp/legacy-quotient.json
cmp results/control_quotient_generic.json /tmp/generic-quotient.json
```

The reports use the binary digest encoding below, distinct from the text-row
encoding in the earlier selector reports.

Digest encoding version 1 is explicit:

- graph: ASCII `selector-table-v1` followed by a zero byte; unsigned 64-bit
  big-endian state count and start; then each row in state order and each
  observation in `OBSERVATIONS` order, encoded as a one-byte command number
  and an unsigned 64-bit big-endian next state;
- command numbers: normal=0, contracted=1, stay=2, L=3, R=4, U=5, Rdx=6;
- absent next state: `2**64-1`;
- witness: ASCII `selector-state-map-v1` followed by a zero byte; unsigned
  64-bit big-endian length, then each mapped state in that same integer format.

The first legacy run on 2026-10-06, Python 3.12.14, compiled in 2.86 seconds,
minimized in 6.57 seconds, and verified the witness in 0.18 seconds. Peak RSS
for the **combined compile/minimize/verify process** was 275,244 KiB. These are
single-run measurements, not a comparison against isolated original-runtime
RSS, and not evidence of lower compilation peak memory. Only the state-count
reduction and exact behavior preservation are claimed here.
The later complete CLI runs, including compilation, digesting, minimization,
and verification, took 11.54 seconds for legacy and 14.93 seconds for the
generic case; they were sequential and subject to one enclosing 120-second
timeout and the same 1,200,000-KiB address-space limit.

## Tests and limitations

`tests/test_control_minimization.py` checks:

- all primitive output distinctions and separately absorbing terminals;
- cyclic and unreachable equivalent states, retained stay ticks, and delayed
  distinctions on every observation including the sixth;
- 100 seeded generated graphs against an independent all-pairs bisimulation
  fixed point, plus cyclic clones with different successor ids;
- exhaustive three-observation traces of a small cyclic table;
- quotient idempotence, deterministic numbering, invalid witnesses and caps;
- a 12,000-state chain and independently encoded digest/report checks;
- exhaustive source-to-quotient witness checks on legacy and generic tables;
- complete lockstep microtick traces on all 65 S trees with one through six
  leaves, then 85 legacy and 40 generic encoded contractions, each invocation
  starting fresh at root and checking final erasure and terminal absorption.

All nine focused tests passed together in 38.963 seconds under explicit
process bounds. Seven independent review tests cover 1,528 uneven cyclic
copies with 257 known equivalence classes, illegal operations, contextual
contraction, divergence, unreachable-edge witness corruption, all command
encodings, hash-seed independence, and CLI validation. Both recorded reports
were independently regenerated byte-for-byte from the frozen compiler sources.

The bounded tree runs are regression evidence. All-input equivalence follows
from the finite witness and induction. The existing selector and source-to-S
proof obligations remain unchanged. Production integration is optional and
remains a separate decision after review.
