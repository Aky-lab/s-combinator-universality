# Exact interval-coded selector prototype

`s_only.succinct_selector` composes the independently checked succinct
[pattern](succinct-probes.md), [prioritized-row](succinct-rows.md), and
[walker](succinct-walkers.md) tables into the **same indexed finite graph** as
the existing fixed-program compiler. This is a separate opt-in prototype;
production selector APIs and their runtime have not changed.

It preserves the full graph, including unreachable states, original start,
all six entries at every original index, movement ticks, uniform terminals,
and immediate absorption after one native contraction. It does not minimize
states, skip matching, or replace the primitive interpreter with a source
machine. Virtual control counts need not fit Python's `len`/`sys.maxsize`.

The initial whole-program API accepts periods 1 and 2 and at most eight total
appendant bits. Scaling toward the compact 482-phase fixture requires further
work on repeated pattern construction and cross-fragment metadata duplication.

## Interface and scope

```python
from s_only.cts import Program
from s_only.root_selector import execute, erase
from s_only.succinct_selector import compile_table
from s_only.terms import S, App

table = compile_table(Program(('1', '')))
assert table.state_count == 257_299
assert table.start == 227_379
term = App(App(App(S, S), S), S)
result = execute(term, table)             # unchanged primitive interpreter
assert table.status(result.control) == 'contracted'
assert erase(result.cursor) == App(App(S, S), App(S, S))
```

`SuccinctSelectorTable` exposes `start`, `state_count`, `transition`, `status`,
`linear_coefficient`, `lookup_depth_bound`, and `metadata_records`. It has no
virtual `states` sequence. Only explicit `materialize(max_states=...)` creates
a materialized `root_selector.SelectorTable`; it rejects a count above the
specified positive cap before enumerating anything.

`root_selector.step`, `select_cursor`, `select_path`, `execute`, and
`reduce_once` use an explicit table structurally and need no edits. Their
existing type annotations still name the materialized type. The existing
`program_selector` and `periodic_selector` compiler entry points continue
to produce materialized tables; `succinct_selector.compile_table` selects
the new representation explicitly.

Compilation reuses `program_selector_parts.active`, `priority`, `clock`, and
`root_selector._euler` unchanged. It follows the original order:

1. normal, contracted, and selected/Rdx direct states;
2. root-reset Euler fallback;
3. active worker;
4. marked worker, with a root reset before the active continuation;
5. fresh worker, with a root reset before the marked continuation.

The same fixed `PatternFamily` definitions construct each source fragment.
Only fragment representation and graph storage differ.

## Immutable interval representation

A frozen table has exactly two fields: `blocks` and `start`. `blocks` is an
immutable tuple partitioning `[0, state_count)` in ascending order. There are
two exact frozen record kinds:

- `_DirectRow(origin, row)`: one original state and its six immutable `Command`
  entries; its exclusive stop is `origin+1`.
- `_Fragment(origin, table, yes, no)`: a validated exact succinct component,
  its original terminal continuations, and an affine placement of every
  retained component state. Its stop is derived from that component's explicit
  `state_count` and the number of removed terminals.

The compiler facade `SuccinctGraphBuilder` inherits the original finite direct
row helpers. It replaces reservation and embedding, so the existing helpers
can still use `reserve`, `jump`, and `builder.states[index] = row` at precisely
the same emission points. Its compile-only `states` facade supports indexed
assignment to reserved direct controls. It is deliberately not iterable or
sized; no virtual list is allocated. Reserved forward references are filled
before finalization, and unresolved or twice-filled reservations are rejected.

Compilation has mutable dictionaries, temporary pattern objects, a wall clock,
and lists. None survive in the finished table. Its referenced objects are only
exact frozen blocks, Commands, component tables, pattern descriptors, strings,
integers, and tuples. Addresses retained inside row code are fixed compiled
instruction data, never input-tree addresses or saved invocation cursors.

## Embedding equivalence by index

The original `GraphBuilder.embed(T, yes, no)` enumerates old indices in ascending
order, removes every Boolean-answer state, and allocates one new state for
every other old state. It then copies each retained primitive entry while
replacing its target through that mapping. Let `o` be the outer builder's next
index before the embedding.

### Ordinary pattern and row probes

Their only Boolean states are false 0 and true 1. Every old `q >= 2` is retained,
so exactly `T.state_count-2` states are emitted, and the original embedding map is

```text
M(0) = no
M(1) = yes
M(q) = o + q - 2   for q >= 2.
```

The succinct block has exactly interval `[o, o+T.state_count-2)`. For an outer
control `c` in it, decoding `q=c-o+2` returns the exact original component entry
`(command, t)`. The outer instruction is `(command, M(t))`, exactly the old
copying rule. This applies equally to reachable and unreachable controls.
The returned entry is `M(T.start)`.

A wildcard-only matcher or empty rows emit no retained controls. There is no
zero-length interval: compilation still returns `M(T.start)`. This preserves
true/false starts and wildcard priority resets, including unreachable suffix
rows inside a nonempty row fragment.

### Closed descent and ascent walkers

A closed walker changes old state 1 into a nonterminal feedback instruction
`stay -> T.start`. Its only Boolean state is false 0. Thus the original builder
retains **old 1 as well as every larger state**, and its exact map is

```text
M(0) = no
M(q) = o + q - 1   for q >= 1.
```

The interval is `[o, o+T.state_count-1)`. Decode `q=c-o+1`, preserve its command,
and map its target with this same `M`. The supplied `yes` field is validated
but never used for a walker; builder descent/ascent pass the same continuation
as both arguments, matching the original constructors.

An empty walker still has two old controls, start 0, and the unreachable
feedback row at old 1. Therefore embedding emits **one** outer state whose
instruction is `stay -> no`, while returning entry `no`. Removing that
unreachable feedback state would shift every later control and is incorrect.

### Composition induction

Induct on operations performed by the original graph constructors. Maintain:

1. Both builders have emitted the same number of virtual controls.
2. Every filled direct row or embedded component entry agrees at the same
   control and every observation, after applying the same continuation map.
3. Every outstanding direct reservation has the same index.
4. Each helper returns the same continuation index.

A reservation adds one outstanding state to both. Direct row assignment fills
identical Commands at that index. The two embedding cases above add equal
widths and exact entries and return equal starts, including the zero-width
case. The other builder helpers are unchanged compositions of these operations.
Therefore running the same fixed-program constructors in the same order gives
identical full indexed tables and the same final start.

This argument depends on the proved exact component decoders, not on a claim
that finite tests cover arbitrary programs. The restricted implemented compiler
is the concrete composition to which the proof applies.

## Structural validation

Construction does not enumerate virtual controls. It checks:

- Exact frozen record types, an immutable nonempty outer tuple, plain integer
  origins, positive intervals, complete contiguous coverage, and valid start.
- Every direct row has six exact Commands and plain string primitives drawn
  from `stay`, `L`, `R`, `U`, `Rdx`, `normal`, and `contracted`.
- Every direct target and each embedded `yes`/`no` field is a plain integer in
  the full outer control range, including unused continuations.
- `normal` and `contracted` rows are uniform, target-free, and absorbing.
- Every Rdx row is uniform and targets an actual direct `contracted` row. That
  target is itself fully checked, so contraction cannot continue selection.
- Every nested component is an exact accepted immutable type, with its own
  complete constructor validation rerun. This includes unused descriptor/code
  metadata, child-before-parent links, counts, row scopes, row targets, starts,
  loop feedback, and tick profiles.

Type whitelists use identity checks. Every primitive command and target is
preflighted before uniformity or cross-row comparisons, so custom equality
methods cannot substitute mutable objects for the declared code types.

The component invariants establish that each retained decoded command is a
movement/stay with a valid local target. The affine maps then establish every
virtual outer target lies in its fragment interval or one of the checked
continuations. No unbounded virtual-entry validation scan is needed.

## Runtime and resource accounting

A transition lookup receives only one finite control, node kind, and incoming
side. It binary-searches the fixed outer intervals, then either reads a direct
row or invokes the appropriate immutable component decoder and rebases one
target. It has no term/cursor argument, source evaluator, structural reader,
file/hash operation, compiler invocation, saved history, or persistent mutable
cache. Repeated and out-of-order queries return the same entry without changing
code.

If there are `I` outer intervals and maximum component decoder-loop bound `D`,
outer plus component lookup uses at most `bit_length(I)+D` search/decoder loop
iterations. Fixed wrapper calls add constant work. The number of local scalar
registers and the fixed Python call depth do not depend on the S input tree.
No runtime recursive traversal of a pattern is used.

These are code-size bounds, not unit-cost arbitrary-precision arithmetic
claims. Let `B` bound the bit lengths of every nonnegative integer stored or
derived from the fixed representation: virtual state count, interval endpoints,
continuation targets, all nested widths/profiles, descriptor and block indices,
container lengths, and address lengths. Include unused code as well. Runtime
integer temporaries have `B+O(1)` bits. Search, addition, subtraction, and division
by two cost at most `O(B)` bit operations per decoder iteration in a conventional
model. Thus one primitive-table lookup has a fixed-code bound
`O((bit_length(I)+D) * B)` up to constant wrapper work. For a fixed compiled
program all these quantities are constants independent of input-tree size.

The unchanged occurrence zipper is the native runtime's tree location, not
extra selector memory. Lookup does not inspect it; the interpreter supplies
only its two local observations. Each invocation resets to the same start and
the current tree's root. After Rdx the same interpreter performs one native
S contraction and reaches an absorbing terminal.

The inherited `linear_coefficient = state_count+1` has the original conditional
meaning: a deterministic **terminating read-only** invocation on an N-occurrence
tree cannot repeat a configuration among at most `N*state_count` possibilities;
contraction adds one tick. This is not by itself a termination proof. Exact
same-index transitions transfer every materialized run and its primitive tick
count, and any separately justified termination or simulation theorem under
its original premises. They do not manufacture an all-input simulation or
termination theorem from the finite tests here.

### Physical metadata and current duplication

`metadata_records` is a reproducible count of referenced representation slots:
seven for each direct block plus its six command entries; one for each fragment
block; and one for each nested table header, pattern-code wrapper, descriptor,
row block, and address direction. It counts shared code again when referenced
by separate fragments. It is not a measurement of Python resident bytes or
integer bits, and the same-object repeated-embedding API can overcount physical
sharing. The ordinary compiler currently recompiles code per fragment, so
cross-fragment duplication is real.

Measured locally on the prototype:

| Program appendants | Virtual states | Start | Intervals | Direct states | Fragments | Pattern descriptors | Metadata slots |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `('',)` | 82,116 | 71,512 | 313 | 120 | 193 | 9,304 | 13,460 |
| `('', '')` | 210,962 | 186,666 | 369 | 128 | 241 | 21,924 | 28,973 |
| `('1', '')` | 257,299 | 227,379 | 370 | 128 | 242 | 25,888 | 33,040 |
| `('01', '001')` | 432,812 | 381,908 | 370 | 128 | 242 | 34,423 | 41,987 |

The legacy program's 242 fragments contain 804 separately referenced pattern
codes, 676 row blocks, and 3,676 address directions. All 804 pattern-code tables
are distinct objects, but only 57 are distinct by full descriptor equality in
an external measurement. This is substantial actual duplication, not merely a
counting artifact. The corresponding identity-distinct/equality-distinct counts
are 516/43 for `('',)`, 802/55 for `('', '')`, and 812/65 for `('01', '001')`.
Equality/hashing for this comparison is external measurement only, never part
of lookup. No cross-fragment interning is implemented.

An external recursive `sys.getsizeof` traversal, visiting each reachable object
identity once and following dataclass fields/tuples, counted 2,736,002 bytes for
the legacy immutable table in the local Python build. It counted 1,036,338,
2,280,878, and 3,606,394 bytes for the other three listed programs respectively.
These are platform-specific reachable-object shallow-size sums, including
integer/tuple objects and shared objects once; they exclude allocator overhead,
compiler temporaries, interpreter code, and process RSS. They are not a portable
memory bound. The virtual-to-slot ratio must not be reported as a RAM compression
factor: the two representations' records have different sizes, and
arbitrary-precision integer storage matters.

Default whole-program limits are eight appendant bits, 100,000 retained metadata
slots, and a 10-second **cooperative** compile deadline. The appendant cap cannot
be raised above eight in this prototype; period cannot exceed two. Metadata
and positive finite time limits are mandatory and configurable. Checks occur
before/after component compilation and at graph operations/finalization. They
can reject retained metadata and detect elapsed time, but do not interrupt an
individual component compiler or bound its transient allocation. Use an
external process time/memory limit when a hard resource bound is required.

## Independent bounded checks

`tests/test_succinct_selector.py` checks:

- All six same-index entries and statuses for the full 257,299-state legacy
  program; exact original start and archived graph digest.
- Exact capped materialization of the 82,116-state period-one empty program.
- Ordinary/closed/empty fragments; unreachable wildcard suffixes; retained
  empty-walker feedback; mixed direct rows, forward reservations and assignment.
- A shared depth-128 pattern embedded into a controller whose virtual count
  exceeds `sys.maxsize`, with sparse independently rebased checks and a direct
  state placed after the enormous interval.
- Invalid intervals, commands, targets, observations, terminal rows, Rdx
  continuations, mutable metadata, corrupt nested descriptors, budgets, and
  explicit materialization caps.
- The first twelve native contractions from the archived 85-step queue trace:
  lockstep control and cursor agreement at every primitive tick, exact selected
  addresses and result hashes, and immediate one-contraction absorption.
- The unchanged `execute` runtime on normal forms and a bare S redex.
- Transition lookup with compiler, source-step, pattern-family, cursor, file,
  hashing, identity, and clock operations patched to fail.

The frozen legacy graph digest is
`bb4c1f981a8dba4fb14d7f93f55d6f6927c460ebc8263037643903ddec291924`.
The digest checks external materialized/indexed graph inspection, never runtime
hashing. Native trace counters and deadlines also live only in the external
test driver.

Run the focused suite from the repository root:

```sh
python -m unittest discover -s tests -p 'test_succinct_selector.py' -v
```

## Full graph and trajectory report

```sh
timeout 180s sh -c 'ulimit -v 1048576; exec python -m tools.succinct_selector_report --deterministic --output /tmp/succinct-selector.json'
cmp results/succinct_selector.json /tmp/succinct-selector.json
```

[The deterministic report](../results/succinct_selector.json) compares all
1,543,794 transition entries and 257,299 statuses, then runs the reference
and succinct controllers separately over all 85 archived contractions.
Every per-invocation microtick-trace digest, selected address, output size
and prefix hash agrees. Each run uses 1,315,234 selection microticks, with
a maximum of 41,917 for one selection and a peak of 339,285 tree nodes.

The reported representation has 370 intervals and 33,040 referenced metadata
records. The checking process retains both representations; its memory use
therefore describes the combined verifier. Its internal deadlines are soft,
with the command above enforcing the hard timeout and 1 GiB address-space cap.

Independent review additionally checks arbitrary forward/self-target graph
compositions, repeated embedded fragments, all native samples, immutable
retained code, and rejection of custom-comparison/metaclass metadata.
