# Exact succinct prioritized rows

`s_only.succinct_rows` is a standalone succinct representation of the exact
finite table emitted by `s_only.probes.compile_rows`. It preserves every
original control index, observation entry, start, answer, and primitive tick,
including controls made unreachable by an earlier wildcard or priority.
Matching work is unchanged. These row tables feed the
[spine walkers](succinct-walkers.md) and [interval-coded selector](succinct-selector.md).

Like [succinct single-pattern probes](succinct-probes.md), this implementation
retains fixed immutable pattern-DAG **code**. It does not claim to discard all
static pattern information. Its lookup function reads only that code, the
finite control, and one of the existing six observations. Input terms, cursors,
source machines, files, history, compilation, and mutable lookup caches are
absent from that function.

## Interface

```python
from s_only.probes import Cursor, execute
from s_only.succinct_rows import compile_rows
from s_only.terms import App, S

rows = ((("S", "_"), (1,)), ("S", ()))
table = compile_rows(rows)
assert (table.state_count, table.start, table.tick_bound) == (11, 10, 7)
term = App(S, App(S, S))
result = execute(table, Cursor.at(term))
assert result.answer is True
assert result.cursor.focus is term.right
assert result.cursor.path == (1,)
```

The unmodified `probes.step` and `probes.execute` use the existing structural
method contract (`start`, `answer`, `transition`). Their Python annotations
still name the materialized `ProbeTable`; no new executor or implicit
materialization is introduced. `state_count` is the virtual finite control-set
size. There is intentionally no allocated `states` tuple.

The frozen `SuccinctRowsTable` has four fields:

- `patterns`: a tuple of frozen pattern-code records. Each contains an exact
  `SuccinctProbeTable` and its failure-path profile, described below.
- `blocks`: a tuple of frozen, positive-width intervals in the original
  reverse-row emission order. A block contains `origin`, exclusive `stop`, a
  pattern-code index, an immutable selected address, and its failure target.
- `start`: the original table's start control, including terminal starts.
- `ticks`: the exact original graph-DP bound, exposed by `tick_bound`.

Constructor checks cover every descriptor, including unused code; exact plain
field types; child-before-parent DAG links; integer widths and heights;
failure profiles; row-address scope; contiguous positive intervals; legal
prior-row continuations; start; and the exact tick count. Mutable containers,
subclasses, Boolean indices/counts, bad intervals, unscoped addresses,
inconsistent profiles and invalid targets are rejected. Public construction
may include unused valid immutable pattern code. That code does not add
controls or affect answers.

Compilation accepts the original finite row iterable and exact tuple/string
pattern syntax. It holds the original rows only while compiling. Identical
root objects can reuse one immutable standalone code object, cached by object
identity. Their row occurrences still receive separate intervals and
continuations. Separately allocated but equal pattern roots need not share
code. Shared subgraphs are compact inside each standalone code object; no
cross-root structural interning is promised. Compilation never recursively
hashes or compares source pattern tuples. Caches, source tuples, and temporary
stacks are discarded; selected addresses remain immutable static code.

## Exact interval layout

Let the matcher state width be

```text
W(_)     = 0
W(S)     = 1
W((A,B)) = 6 + W(A) + W(B).
```

Controls 0 and 1 are the original false and true terminals. Suppose a row
`(P,a)` is processed during reverse-row compilation, the next available control
is `o`, and the already compiled suffix has entry `n`. Write `d=len(a)` and
`p=o+d`. The original compiler first emits the movement chain for the selected
address in reverse, then emits the pattern matcher.

For `0 <= j < d`, the movement control `o+j` has instruction

```text
command = L if a[d-1-j] == 0 else R
target  = 1 if j == 0 else o+j-1.
```

Thus entering its final control executes the address in forward order and
ends at true. Define that successful-selection entry as

```text
y = 1       if d == 0
    p - 1   otherwise.
```

The matcher occupies `[p,p+W(P))`. A standalone succinct probe has its same
matcher at local controls `[2,2+W(P))`, with success/failure continuations 1/0.
For global control `q` in the matcher interval, decode local control `q-p+2`
and transform its nonterminal target `t` by

```text
rebase(t) = n          if t == 0
            y         if t == 1
            p+t-2     if t >= 2.
```

The command is unchanged. This affine map on internal controls, together with
the two explicit continuation substitutions, is valid throughout the nested
matcher layout. Its internal structural rows and child intervals use only
relative offsets and these continuations, as proved for the standalone
probe. In particular, it also applies to emitted rows that no real invocation
can reach.

For a positive-width row, its block is `[o,p+W(P))` and its entry is its final
control `p+W(P)-1`. Scope validation makes a wildcard's address empty, so every
positive-width row has a nonempty matcher interval. The intervals strictly
increase and partition exactly `[2,state_count)`. All address targets and
rebased matcher targets are strictly below their source; no new control
numbering convention is introduced.

### Zero-width rows

A wildcard at an empty address emits no states and sets the next entry to
true. Keeping a zero-length interval would introduce duplicate boundaries
and potentially ambiguous lookup. Instead, it is omitted from `blocks`, while
the subsequent row's failure target (or the complete table's start) records
the reset to 1.

Examples:

- Empty row list: two terminal states, `start=0`, `tick_bound=0`.
- Any nonempty list of wildcard-only rows: two states, `start=1`, bound zero.
- A leading wildcard followed by a literal: three states, `start=1`; the
  literal's unreachable state is still present and has its exact original row.
- Rows `S`, `_`, `(S,S)`, all at empty addresses: eleven states, `start=10`,
  bound one. The first literal's failure target is 1, not adjacent state 9.

In each nonzero block, a legal failure continuation is the previous nonzero
block's entry, the initial false terminal if there is no previous block, or
true if an intervening zero-state wildcard reset the continuation. The
constructor checks exactly these possibilities. The final start is the last
block's entry or true, with false also possible when there are no blocks.

## Pointwise equivalence proof

Induct on the number of source rows processed in **reverse compilation order**.
Keep as the induction invariant:

1. The same set of control indices has been emitted, with equal Instructions
   at each index and each of the six observations.
2. The current suffix entry agrees.
3. The nonzero blocks partition all emitted nonterminal controls.

Initially both tables contain only terminal controls 0 and 1 and have suffix
entry 0. For the next row, scoped address validation agrees: walking a proper
address prefix must encounter a pair, never a hole or S. The DAG walk visits
the same fixed pattern path without unfolding unrelated occurrences.

If the row is a wildcard, scope forces an empty address. Both compilers emit
nothing and change the suffix entry to 1, preserving the invariant.

Otherwise, both emit the reversed-address chain given above, followed by a
matcher. The standalone probe's same-index layout theorem, with the explicit
rebasing substitution, gives equality for every state of this matcher and
every observation. The no continuation is the equal prior suffix entry; the
yes continuation is the equal selected-address entry. Both enter the final
matcher control. The new positive interval starts where the prior interval
ended, establishing all three invariants.

After every row, therefore, sizes and starts are equal and transition
Instructions agree **at the same original index**, not just up to a
relabeling. The answer maps are identical: false at 0, true at 1, and pending
elsewhere. Equality is over the declared mathematical observation domain
(`S`/`application` and `root`/`L`/`R`, as exact strings); accidental
custom-equality acceptance outside that domain is not reproduced.

For equal initial configurations, one `probes.step` observes the same finite
control, node kind and incoming side in both representations. Pointwise
Instruction equality gives the same primitive command and target. Induction
on ticks gives identical control and full occurrence-cursor traces, including
terminal absorption. First-match priority, failure restoration, selected
success addresses, and preservation of the ambient term all transfer from
the original row table. Shared input objects at different occurrence paths
remain distinct cursor occurrences. No extra runtime state is introduced.

## Exact graph bounds need separate success and failure profiles

Let `Y(P)` and `F(P)` be the longest control-graph paths through a matcher
before entering respectively its designated success and failure
continuations. `F` can be absent. These profiles count primitive transitions,
not lookup work.

```text
Y(_) = 0                         F(_) = absent
Y(S) = 1                         F(S) = 1
Y((A,B)) = 5 + Y(A) + Y(B)
F((A,B)) = max(1,
               3 + F(A)          when F(A) exists,
               5 + Y(A) + F(B)   when F(B) exists).
```

These formulas follow independently from the emitted graph:

- A hole enters success immediately and has no failure path.
- An S test takes one transition to either continuation.
- Pair success takes the initial test, L, a successful left match, U, R, a
  successful right match, and U: five structural transitions.
- Pair failure either fails the initial test (one transition), fails the left
  match after test/L and returns by U (three plus `F(A)`), or succeeds on the
  left and fails on the right (five plus `Y(A)+F(B)`).

These exhaust the graph branches. Thus arbitrary continuation bounds `y,n`
give exactly `max(Y(P)+y, F(P)+n)`, omitting the absent failure branch. The
existing standalone probe's `tick_bound` stores `Y(P)`. A single bottom-up DAG
pass supplies `F(P)` without expanding occurrences.

A row's success continuation has bound `len(a)`, and its failure continuation
has the already computed suffix bound `R`. Therefore

```text
row_bound = max(Y(P) + len(a), F(P) + R),
```

again omitting absent failure. A wildcard resets the bound to zero. In
particular, treating `F(_)` as zero rather than absent would incorrectly make
an unreachable suffix contribute. This reverse-row recurrence is the exact
`ProbeTable.tick_bound` graph dynamic program; the constructor recomputes it
and validates the stored result.

Graph exactness does **not** imply that a real tree attains the bound. For rows
`((_,_),())` followed by `((S,S),())`, graph DP reports 8. Every application
matches the first row in 5 ticks, and S fails both rows in 2 ticks. The graph
path of length 8 combines observations that a fixed term cannot realize
across the two restoring probes. The original table has this same distinction.

## Lookup work and arbitrary-precision costs

For fixed code, `transition` has exactly the finite inputs `(control, kind,
incoming)`. It first binary-searches the nonempty row blocks. This takes at
most `block_lookup_bound = B.bit_length()` iterations for `B` blocks. A
movement-chain state is decoded directly. Otherwise one standalone pattern
lookup is called, followed by the constant-size target rebasing calculation.

If `H` is the maximum stored probe height, at most `H` pattern-decoder
iterations occur. Thus the exposed

```text
lookup_depth_bound = B.bit_length() + H
```

bounds the sum of search and pattern-decoder iterations. It is conservative
when high or unused pattern code is present. Every iteration uses only a
constant number of immutable metadata accesses. Incoming side is validated
but ignored by these particular emitted instructions, as in the original
table. Bounds depend only on fixed code, never input-tree depth, size, or a
previous invocation.

No pattern-recursion stack, return stack, term equality/hash, file lookup,
compiler call, source-machine state, or persistent auxiliary register occurs
in transition lookup. Binary-search indices and the selected interval/
continuations are a constant number of temporary integers. The retained
runtime configuration remains exactly `Configuration(control, cursor)`.
The existing cursor zipper may grow with the input-tree depth; the lookup
neither sees it nor adds another zipper.

Integer arithmetic is not assumed to be unit cost. Let

- `N` be the virtual control count and `M=N.bit_length()`;
- `D` be the sum of stored standalone descriptor counts;
- `P` be the stored pattern-code count;
- `B` be the positive block count;
- `A` be the sum of stored address lengths, counted with multiplicity;
- `K = M + bit_length(D+P+B+2)`.

Active interval origins, local/global controls and continuation targets fit
in `O(M)` bits. Descriptor and pattern indices may require additional bits,
especially for publicly constructed code with unused metadata; they are
covered by `K`. Lookup has conservative bit-work bound
`O((1+log(B+1)+H)*K)` and `O(K)` auxiliary bits, apart from immutable code and
the returned Instruction. Tuple metadata access uses the usual RAM indexing
model; the bound explicitly accounts for the arbitrary-precision offsets,
comparisons and index arithmetic. A per-code circuit or expanded finite table
could implement the same total finite function; this is a bounded decoder,
not an unbounded interpreter hidden inside one primitive tick.

For compiler outputs, all nonempty standalone roots occur in row blocks,
so their widths and tick profiles are bounded by the resulting virtual size.
With `R` supplied rows, compilation takes `O(D+A+R)` DAG/address/row visits and
exact-integer operations, plus compile-time identity-map operations. A
conservative bit-work bound is
`O((D+A+R)*(M+bit_length(D+R+2)))`, with expected constant-time identity-table
operations on ordinary object identities. Zero-width rows still contribute
to `R`, even when no states are emitted. Static metadata has conservative
size `O((D+P+B)*K+A)` bits for compiler outputs. A general public constructor
can retain unused descriptors with larger counters; its stored bit cost must
also include those actual counter widths, which do not increase active
lookup offsets. Retaining repeated immutable addresses by reference can
reduce physical storage, but no such reduction is needed for the bound.

For the shared doubled-literal family `D_0=S`, `D_(k+1)=(D_k,D_k)`, two rows
using that same root, one selecting address `R^k` and one selecting the root,
use one `(k+1)`-descriptor code object and two blocks, but preserve exactly

```text
state_count = 14*2^k + k - 10
tick_bound  = 2*(6*2^k - 5).
```

This has `O(k)` descriptor/address entries and `O(k^2)` stored bits, not
`O(k)` bits. Compilation and lookup avoid occurrence expansion. Successful
matching can still require exponentially many original ticks. The large test
uses only tiny mismatching trees under separate fixed tick caps; it makes no
fast-positive-match claim.

## Verification

```sh
timeout 30s python -m unittest discover -s tests -p test_succinct_rows.py -v
```

The 16 component tests cover:

- An independently written eleven-state layout, plus the reversed allocation
  order of a two-edge selected address
- Empty rows, all-wildcard zero-state rows, leading/internal wildcard resets,
  unreachable controls, and duplicate interval-boundary avoidance
- Every control and all six observations for all 2,955 row lists of length
  zero through three over 14 small scoped rows, plus 180 seeded larger lists
  involving shared pattern DAGs and deeper scoped addresses
- Independent graph-DP success/failure profiles for all 102 patterns with up
  to four leaves, and a graph bound that no real input attains
- Complete primitive trace equality in 10,339 invocations: all 211 row lists
  of length zero through two over those small rows, at every occurrence of all
  S trees with up to four leaves; direct use of the unchanged `execute`
- First-match priority, nonroot selected addresses, shared input occurrences,
  and exact cursor restoration after every row fails
- Duplicate object reuse, equal distinct objects, separate occurrence
  intervals, frozen metadata, repeated invocations, and runtime with source
  compilation, files and term equality disabled
- Instrumented binary-search and pattern-decoder iteration bounds, including
  a 4,097-block table
- A depth-4,096 doubled DAG retaining 4,097 descriptors for the virtual table
  above; a lookup through all descriptor levels; S and `(S S)` mismatches in
  exactly 2 and 8 externally capped ticks
- A valid depth-6,000 pattern and selected address without recursive
  compilation, malformed patterns at the same depth, malicious subclasses,
  invalid controls/observations and malformed public metadata/targets

These checks support the structural proof without claiming the subsequent
walker/controller composition or a full compact-fixture execution.
