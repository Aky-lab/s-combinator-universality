# Exact succinct restoring probes

`s_only.succinct_probes` is a standalone alternative representation of the
single-pattern table emitted by `s_only.probes.compile_pattern`. It addresses
up-front graph materialization: a shared pattern DAG can describe an enormous
finite table without allocating one Python row per control. Exact control
indices and primitive traces are preserved. This standalone entry point
compiles one pattern; prioritized rows and full controllers require further
composition.

The code retains fixed immutable pattern metadata. This is a distinct
**succinct-code representation**, unlike the original materialized table which
discards its pattern after compilation. Calling it a finite transition
function does not mean its implementation has no static pattern information.

## Interface and retained code

```python
from s_only.probes import Cursor, execute
from s_only.succinct_probes import compile_pattern
from s_only.terms import App, S

pattern = ("S", "_")
table = compile_pattern(pattern)
assert table.state_count == 9
assert table.start == 8
assert execute(table, Cursor.at(App(S, S))).answer
```

The existing `probes.step` and `probes.execute` work unchanged by their ordinary
`start`, `transition`, and `answer` method contract. Their Python annotations
still name `ProbeTable`; this experiment neither edits those annotations nor
subclasses the materialized row container. There is deliberately no `states`
property, implicit materialization, runtime switch, or new executor.

A `SuccinctProbeTable` has two frozen fields:

- `nodes`: an immutable tuple of frozen descriptors
- `root`: the final descriptor's index

Each descriptor contains its kind, child descriptor indices if any, an exact
emitted-state width, the exact standalone microtick bound, and its height.
Children strictly precede their parent. The constructor validates all types,
child bounds, counts, and heights before the table can be used. Empty and
mutable metadata, Boolean indices/counts, forward references, and inconsistent
counts are rejected. Compilation accepts only the original syntax's exact
plain strings `"_"`/`"S"` and exact length-two tuples.

No original pattern tuple is retained. The descriptors retain its needed
static structure. Identity maps, DFS stacks, and cycle-detection sets are
compile-time temporaries and are discarded. In particular there is no mutable
hash cache attached to a table or invocation.

## State counts and independent layout check

Let `W(P)` count the states emitted by a matcher, excluding the two terminals:

```text
W(_)     = 0
W(S)     = 1
W((A,B)) = 6 + W(A) + W(B)
```

The full control set is exactly the integers `0 <= q < 2 + W(P)`, including
conceptual occurrence states which happen to be unreachable. State 0 is false;
state 1 is true. If a fragment at origin `o` has continuations `y,n`, define
its entry by

```text
E(P,o,y) = y                   if W(P) = 0
           o + W(P) - 1       otherwise.
```

A hole emits no rows and enters `y`. An S literal emits one node-kind test at
`o`, with `stay y` on S and `stay n` on an application.

For a pair `(A,B)` starting at `o`, write

```text
r = o + 2 + W(B)
l = r + 2 + W(A).
```

The original `_Builder.match` allocates precisely the following rows, in this
order:

| State or interval | Materialized instruction or fragment |
| --- | --- |
| `o` | `U y` |
| `o+1` | `U n` |
| `[o+2, r)` | `Match(B, y=o, n=o+1)` |
| `r` | `R E(B,o+2,o)` |
| `r+1` | `U r` |
| `[r+2, l)` | `Match(A, y=r+1, n=o+1)` |
| `l` | `L E(A,r+2,r+1)` |
| `l+1` | `stay n` on S; `stay l` on an application |

These are half-open intervals. An empty child interval allocates no row, and
its entry is the corresponding yes continuation. The final row is
`l+1 = o+W((A,B))-1`.

This order was checked directly against the existing compiler rather than
inferred from the matching equation alone. In particular, Python evaluates
the nested `self.move("R", right_test)` before its outer `self.move("U", ...)`,
and evaluates the final left move before its enclosing node-kind test. The
nine-state `("S","_")` layout is also checked against a literal independently
written list of Instructions in the tests.

For the complete table the initial fragment has `(o,y,n)=(2,1,0)`. Thus
`start = state_count-1` also covers a hole, whose start is terminal 1.

## Pointwise equality proof

Consider any fragment `Match(P,y,n)` appended to a builder whose next state is
`o`, with both continuation indices below `o`. Its emitted interval is
`[o,o+W(P))`. The decoder is called with a control in that interval and carries
only the local values `(descriptor, origin, yes, no)`.

Induct on the finite unfolded pattern, or equivalently on descriptor height.

1. A hole's interval is empty, so the equality claim over it is vacuous; both
   compilers return entry `y` without emitting a row.
2. An S literal's interval contains only `o`. Both implementations produce
   `Instruction("stay", y)` for each S observation and
   `Instruction("stay", n)` for each application observation. Both enter `o`.
3. For a pair, the eight portions of the layout above partition its emitted
   interval. On each of the six singleton structural rows the decoder uses
   exactly the command and target displayed in the layout. On either child
   interval it descends to that child's descriptor and the displayed origin
   and continuations, so the induction hypothesis gives the exact row there.
   Both compilers enter the final node-kind test. Empty child intervals are
   skipped, and the explicit `E` rule handles their continuation targets.

The incoming-side observation is ignored by both generated programs; all
three entries for a node kind are equal. The two global terminal rows are
likewise identical. Consequently, for every valid control `q` and all six
observations, the succinct lookup returns an `Instruction` equal to the entry
at **that same state index** in the materialized table. It also has the same
state count, start, and answer map. This is pointwise equality, not merely an
input/output simulation or a relabeling.

Every nonterminal target remains below its source. In a recursive descent the
new continuations precede the new origin, and the six structural rows visibly
have smaller targets. So the implicit graph has the same acyclic ordering
certificate as the materialized graph.

For the same initial `Configuration`, each `probes.step` sees the same control,
node kind and incoming side, hence issues the same primitive command and next
control. Induction on ticks gives identical control and occurrence-cursor
traces, including terminal absorption. Both execute paths therefore return
the same Boolean at the same restored cursor. No theorem requires a positive
match to be fast.

The finite mathematical observation domain consists of the declared plain
strings. The succinct API explicitly rejects non-string/subclass observations;
it does not reproduce accidental custom-equality acceptance by the original
Python tuple lookup outside that domain. Controls must be plain integers in
the declared range, as in `ProbeTable`.

## Shared DAGs preserve occurrence indices

Compilation performs an explicit iterative DFS. Each exact tuple is recorded
by its object identity, with one descriptor constructed after its two children.
Only identity integers are used as keys for tuple nodes: no recursive tuple
hashing, recursive structural equality, recursion on the Python call stack,
or traversal of the unfolded occurrence tree is needed. A discovered active
node would be rejected as a cycle; malformed mutable or subclass nodes are
rejected before they can provide children. (Ordinary immutable tuple
construction cannot itself create a tuple-only cycle.)

Widths add each child contribution even when both child indices are equal.
For example, `shared=("S","_")` followed by `(shared,shared)` uses four
descriptors but describes 22 controls. Its two copies of `shared` occupy
different state intervals and have different continuation targets. A lookup
carries the selected occurrence's origin and continuations; it does not
identify those controls just because their descriptor index is shared.

For the doubled literal family

```text
D_0 = "S"
D_(k+1) = (D_k,D_k)   # both edges point to the same tuple object
```

there are `k+1` descriptors and exactly

```text
W(D_k) = 7*2^k - 6
state_count = 7*2^k - 4
```

virtual controls. This is `O(k)` descriptors, **not** `O(k)` bits: the exact
counts have `O(k)`-bit values, and these descriptors occupy `O(k^2)` bits in
this representation. No structural deduplication of separately allocated but
equal tuple nodes is promised or needed.

## Why this is finite control, and what it costs

For each fixed compiled table the metadata is fixed and finite. The transition
function's entire input is `(control, kind, incoming)`, ranging over a finite
set of `6 * state_count` possibilities. It can be expanded into the original
finite table by enumerating that set. Its result is independent of the source
machine, any S term, cursor, invocation, file, earlier lookup, or recorded
trajectory.

Each decoding-loop iteration either returns an instruction or descends one
DAG edge. Child indices decrease strictly, and descriptor height decreases.
At most `lookup_depth_bound` decoder-loop iterations occur; this bound depends
only on compiled code. Each iteration selects one descriptor and reads a
constant number of metadata fields, including child widths for a pair. Total
metadata accesses therefore have a constant-multiple height bound, rather
than the height being an exact bound on every descriptor access. No descent
depends on input-tree depth or size. A constant number of temporary integer
variables carries the interval and continuations; there is no decoder stack
and no auxiliary persistent runtime register.

Interval origins, continuations and calculated state offsets are bounded by
the virtual control range (or its one-past size), hence have at most
`M = state_count.bit_length()` bits. The descriptor-index register separately
needs `O(log D)` bits, where `D` is the stored descriptor count. Public
construction can include unused descriptors, so its index need not fit within
the virtual control range of the root. The compiler itself emits only
reachable descriptors with `D <= state_count`, but the general lookup-space
bound does not rely on that stronger property. Temporary instruction objects
have the existing validated `probes.Instruction` type and use plain-string
commands.

For compiler outputs, compilation takes `O(D)` DAG visits and `O(D)`
exact-integer additions/comparisons, with `O(D*M)` bit work/storage as a
conservative bound. If `H` is the root descriptor height, lookup takes at most
`H` decoder iterations and `O(H)` total metadata accesses. A conservative
general bit-work bound is `O(H*(M + log D))`, with `O(M + log D)` auxiliary
bits, in addition to immutable code and the returned instruction. For compiler
outputs this simplifies to `O(H*M)` bit work. These bounds are all functions of
the fixed code alone. In particular, the decoder is not an unbounded
interpreter concealed inside one transition. It is a uniform algorithm for
representing a family of finite functions with a code-specific finite bound,
and could be unrolled into a finite lookup circuit for each code object.

The runtime configuration remains exactly the existing finite `control` and
one occurrence `cursor`. The cursor zipper can naturally grow with input-tree
depth, as in the original model; the decoder neither reads it nor adds another
zipper, stack, counter, or register to that configuration.

There is an important cost distinction: one original controller microtick
still invokes exactly one primitive command. Python now pays bounded decoding
work for its transition lookup instead of directly indexing an allocated row.
That cost is not asserted to be one constant-time machine instruction, and the
unchanged immutable zipper also has depth-dependent Python allocation costs.

## Runtime length is unchanged

The exact standalone microtick bound is

```text
C(_) = 0
C(S) = 1
C((A,B)) = 5 + C(A) + C(B).
```

Descriptors count both child occurrences here too. This equals the original
materialized table's `tick_bound`, and successful inputs attain it. In the
doubled literal family it is `6*2^k - 5`. Thus a succinct code object can still
take exponentially many microticks to match successfully. The example and
large-DAG tests use tiny mismatching inputs with a strict external budget;
they make no fast-positive-match claim.

## Verification

Run only this component's tests with an external process timeout if desired:

```sh
timeout 30s python -m unittest discover -s tests -p test_succinct_probes.py -v
```

The tests cover:

- Pointwise equality of every state, all six transitions, answers, starts,
  counts and exact tick bounds for all 550 patterns with at most five leaves
- Another 100 seeded mixed shared DAGs, preserving occurrence controls
- Complete microtick trace equality in 17,850 invocations: all 102 patterns
  with at most four leaves at every occurrence of all 23 S trees with at most
  five leaves
- Instrumented decoder-iteration bounds across all controls and observations of
  the 102-pattern corpus
- Positive matches attaining the exact bound and direct use of the unchanged
  `probes.execute`, including shared input subterms at different occurrences
- Frozen metadata; repeated independent invocations; runtime with term
  equality, serialization and compilers disabled
- Plain-string commands, invalid controls/observations, malformed metadata,
  malicious subclasses, and malformed patterns below depth 6,000
- A valid depth-6,000 pattern without recursive validation or hashing
- A depth-4,096 doubled literal DAG with 4,097 descriptors and exactly
  `7*2^4096-4` virtual states, including a lookup traversing all 4,097 descriptor
  levels; tiny S and application inputs must fail within respectively one and
  four externally counted microticks, regardless of the enormous static bound

These tests complement the structural proof. They remove neither the need for
future composition proofs nor the measured full-controller compilation
bottleneck in components not yet implemented in this representation.
