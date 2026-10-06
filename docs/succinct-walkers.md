# Exact succinct inverse rows and spine walkers

`s_only.succinct_walkers` extends the exact succinct pattern and prioritized-row
representations with three standalone compilers:

- `compile_inverse_rows(rows)` returns `SuccinctInverseRowsTable`.
- `compile_descent(rows)` returns `SuccinctWalkerTable` over succinct forward rows.
- `compile_ascent(rows)` returns `SuccinctWalkerTable` over succinct inverse rows.

For every valid row family these preserve the corresponding `s_only.walkers`
compiler's **original state indices**, state count, start, answers, every
instruction under all six observations, and exact static graph bounds. This
includes unreachable controls and semantically shadowed rows. There is no
renumbering, behavioral quotient, tree-size-dependent compilation, or change
to the cursor representation. `walkers.step` and `walkers.execute` run these
objects unchanged; their existing Python type annotations have not been edited.

These are the spine fragments used by the [interval-coded selector](succinct-selector.md).
Their matching and loop lengths remain equal to the originals.

## Inputs and immutable code

Rows retain the original exact tuple syntax: `(pattern, address)`. Patterns
are exact `_`/`S` strings or exact length-two tuples; addresses are exact tuples
of plain integer 0/1 directions. The path must be structurally guaranteed by
its pattern. All three compilers reject every empty address, including a
shadowed one. The empty *list of rows* remains valid: it has two controls,
starts at false state 0, and immediately returns false without moving.

The original `walkers._prepare` materializes a forward table for validation,
even when only an inverse table is requested. Here inverse compilation instead
uses the already checked succinct pattern compiler and the same DAG-based
scope validator as succinct forward rows. It never constructs either
materialized table. Descent builds only its succinct forward representation.

One frozen `_PatternCode` stores a standalone succinct matcher plus its exact
failure profile. Identity-based sharing occurs only during compilation and
only for identical pattern root objects. Source tuples remain alive until
compilation finishes, preventing reused identity keys. No recursive tuple
hashing or structural comparison is used. Distinct equal roots may have
separate descriptors; child sharing within each root is preserved.

Each frozen `_InverseRowBlock` stores the original interval `[origin, stop)`,
a pattern-code index, an immutable address, and the next-row failure target.
Blocks appear in reverse source-row emission order and partition every
nonterminal control. Every inverse row has positive width. Constructor checks
validate all nested descriptors and failure profiles, even unused metadata;
plain integer counts and indices; exact frozen types; scoped nonempty
addresses; interval adjacency and widths; finite continuations; start; and the
exact bound. A forged nested object is revalidated, rather than trusted just
because the outer class is frozen. As with the earlier representations,
Python's explicit `object.__setattr__` is outside the immutable-object contract.

## Original inverse-row allocation, derived from the builder

Let `a=(a_0,...,a_(d-1))` be a scoped nonempty address, `P` its pattern, `o` the
next unused control, and `n` the next row's entry (or false state 0). Write
`W(P)` for the original matcher's nonterminal width, with

```text
W(_) = 0
W(S) = 1
W((A,B)) = 6 + W(A) + W(B).
```

Set `m=o+d` and `t=m+W(P)`. The row has exactly `W(P)+3d` controls and enters
`t+2d-1`. The original `_InverseBuilder.inverse` allocates in this order:

1. Restoration states `o,...,o+d-1`. State `o+j` moves in direction
   `a_(d-j-1)` and targets `n` for `j=0`, or `o+j-1` otherwise. Thus entering
   `o+j-1` restores exactly the last `j` address edges, in their original
   downward order.
2. The matcher interval `[m,t)`. Its yes continuation is global state 1; its
   no continuation is `m-1`, the full restoration chain. Every standalone
   matcher nonterminal `q` is translated to `m+q-2`; terminal target 0 becomes
   `m-1`, terminal target 1 remains 1, and other targets use the same shift.
3. For each address index `i=0,...,d-1`, append a `U` move at `t+2i` and an
   incoming-side test at `t+2i+1`. The move targets the immediately preceding
   control, which is the matcher entry when `i=0`, or the prior test otherwise.
   The test stays to its move when incoming side equals `a_i`; otherwise it
   stays to `n` when `d-i-1=0`, or `o+d-i-2` otherwise.

The nested `self.move("U", entry)` is evaluated before its enclosing
`incoming_test`, explaining the within-pair allocation order. Although the
pairs are emitted in *forward* address order, execution enters the final pair
and tests incoming sides in *reverse* address order.

Scope plus `d>0` implies that `P` has a pair root, so `W(P)>0`. Consequently
the first upward move really does target `t-1`, a nonempty matcher entry. A
lookup never needs a special zero-width-root case for inverse rows. Zero-width
hole children inside the matcher still work by the earlier decoder proof.

### Pointwise equality and restoration

A binary search identifies the unique block containing the control. The three
interval cases above either emit the displayed instruction directly or invoke
the exact standalone matcher decoder with shifted control and continuations.
That decoder already preserves every occurrence control, even where DAG
children share descriptors. Each interval case therefore agrees at the same
index with the original builder. The global terminal rows also agree.

Induction over reverse row emission gives equal state counts, entry indices,
continuation targets, answer maps, and all six entries of every state for the
whole inverse table. Every nonterminal target is smaller than its source:
restoration targets precede restoration states, matcher continuations precede
its interval, upward moves target their predecessor, and failed side tests
target restoration states or an earlier row.

When an incoming-side mismatch occurs after `j` completed upward moves, only
those `j` known address edges are restored. If every side test succeeds,
matching happens at the intended candidate ancestor. Matcher failure first
restores that ancestor's cursor, then the full `d`-edge chain restores the
invocation occurrence before the next row starts. Matcher success leaves the
cursor at the ancestor and answers true. These are occurrence identities,
including parent objects and incoming sides, rather than just equal subtrees.

Since each transition is identical, induction on ticks gives identical
`Configuration(control, cursor)` traces for the original and succinct probes.
Terminal absorption and final cursor/answer follow immediately. The same
argument works on unrelated trees as well as encoded-looking inputs; the
transition function never observes which class of input it is traversing.

## Exact inverse graph bounds

Let `Y(P)` be the matcher success profile and `F(P)` its failure profile,
measured before the relevant continuation. `F(_)` is absent; scoped nonempty
rows always have a pair root and hence a present failure profile. The profiles
are derived from the six-observation control graph, not by asserting one input
can realize every longest-path branch:

```text
Y(_) = 0                 F(_) = absent
Y(S) = 1                 F(S) = 1
Y((A,B)) = 5 + Y(A) + Y(B)
F((A,B)) = max(1,
                 3 + F(A)          when F(A) is present,
                 5 + Y(A) + F(B)   when F(B) is present).
```

For a single inverse row, success costs `2d+Y(P)` before true: one incoming
stay and one `U` per address edge, followed by the matcher. An incoming miss
after `j` successful upward moves costs `2j+1+j=3j+1` before the row's no
continuation. The maximum over `0<=j<d` is `3d-2`. A matcher miss adds `2d`
climbing ticks, `F(P)` matcher ticks, and `d` restoration ticks. Hence

```text
inverse_success = 2d + Y(P)
inverse_failure = max(3d-2, 3d+F(P))
B(empty suffix) = 0
B(row :: suffix) = max(inverse_success, inverse_failure + B(suffix)).
```

These are exact graph-DP quantities. Each path must either leave through yes
or no; each exit's longest path can be concatenated with any graph path from
its fixed continuation. Inverse row failure is present because its side tests
can fail, independently of matcher success. For scoped rows `3d+F(P)` dominates
`3d-2`, but the implementation keeps the full derivation explicit. Constructor
validation recomputes these quantities from immutable code and rejects an
incorrect cached bound.

**A graph bound need not be attainable by a tree.** Two identical `(_,_) -> L`
inverse rows have success profile 11, failure profile 8, and graph bound 11.
On a real L occurrence the first row's parent is necessarily an application,
so that row succeeds in 7 ticks. At a root or R occurrence, both incoming tests
fail in 2 ticks. The graph can pretend the parent is S after climbing from a
child, and can use inconsistent observations between repeated rows. Tests
check the exact bound of 11 and the real-input maximum of 7 separately.

## Closing descent and ascent feedback

`SuccinctWalkerTable` retains one exact immutable succinct row probe. Its
`start` and state count are unchanged; feedback is the unique true terminal,
state 1. The wrapper replaces only that state's six instructions with
`Instruction("stay", start)` and changes its answer from true to nonterminal.
State 0 remains absorbing false. Every other instruction and answer remains
unchanged. It rejects `start=feedback`, just like `WalkerTable`; an empty-row
probe with `start=0` is accepted, and its unreachable feedback points to 0.

Cutting feedback gives the original acyclic probe graph, so exactly

```text
pass_bound = underlying_probe.tick_bound
coefficient = pass_bound + 1.
```

Thus the wrapper is pointwise equal to `_close_feedback`, and the same
per-tick trace proof applies. It adds no runtime state or execution algorithm.
The compiler guarantees transfer unchanged:

- Descent follows a strict descendant on each successful pass and returns
  false at the first miss. Its bound is
  `coefficient * nodes(initial_focus)` original microticks.
- Ascent follows a strict ancestor on each successful pass and returns false
  at the first family miss. Its bound is
  `coefficient * (initial_depth + 1)` original microticks.

A manually wrapped forward probe may contain nonprogressing empty addresses.
The wrapper's structural validation alone does not establish cursor progress;
the termination statements concern the strict-address compiler outputs, just
as the original `WalkerTable` theorem concerns its compiler outputs.

### Inverse candidates are not automatically forward predecessors

Inverse rows recognize candidate ancestors in their own priority order. They
do not retrospectively verify which row prioritized descent selected. A row
shadowed by an earlier forward row can still recognize an inverse candidate.
Overlapping ancestor candidates can stop ascent at a different boundary or
let ascent cross a nested starting point. Prefix overlap by itself supplies
no reconstruction theorem, and the relevant suffix/boundary conditions must
not be replaced by a prefix-free assertion.

The original coherence, uniqueness, and starting-boundary requirements in
[the spine-walker documentation](spine-walkers.md) still apply. Succinctness
changes the representation, so it cannot repair this semantic limitation.
Tests retain concrete priority, nearer-ancestor, prefix-overlap, and nested
boundary counterexamples.

## Finite control and code-bounded lookup resources

The only transition inputs are a plain integer `control` in `[0,N)` and one
of six plain-string `(kind,incoming)` observations. The original Python tuple
lookup accidentally admits some custom equality objects; this API deliberately
rejects subclasses and out-of-domain values, as the earlier succinct APIs do.

The fixed result depends only on immutable compiled code and those finite
inputs. It has no term, cursor, source-machine state, history, compiler, file,
hash/equality hook, dynamic call-return stack, or persistent cache access.
The decoder has a constant number of temporary integer variables. Binary
search takes at most `B.bit_length()` iterations for `B` row blocks. Matcher
lookup takes at most the chosen root's descriptor height; let `H` be the
maximum stored root height (including unused pattern codes). Thus the exposed
`lookup_depth_bound` is `B.bit_length()+H`. Restoration and incoming-test
arithmetic take constant additional work. The wrapper adds constant work and
no loops. These bounds are code-only and independent of input depth or size.

The bound properties may scan immutable pattern metadata when explicitly
requested; runtime transition lookup does not call them. A count of decoder
iterations is not a count of every metadata field access: each iteration uses
a constant number of such accesses. Tests instrument search and matcher
iterations separately and include a 4,097-block table.

To account for arbitrary-precision arithmetic, let

- `N` be the virtual control count and `M=N.bit_length()`;
- `D` be the sum of stored pattern-descriptor counts;
- `P` be the number of stored pattern code objects;
- `B` be the number of inverse-row blocks, and `A` total address length;
- `K = M + bit_length(D+P+B+2)`.

Active origins, stops, matcher offsets, restoration offsets, and continuations
have `O(M)` bits. Pattern and descriptor indices need their own index budget:
a public code object can retain unused metadata with index values much larger
than `N`. The tests use both a pattern index and an active descriptor index
over 1,000 for a twelve-control inverse table. This is why a blanket `O(M)`
auxiliary-space claim would be incorrect for public construction.

Using the usual RAM model for immutable tuple access, lookup takes
`O((1+log(B+1)+H)*K)` conservative bit work and `O(K)` auxiliary bits, apart
from code and the returned Instruction. In particular, the temporary
variables range over a fixed finite space for each fixed table, even when
integer counts have thousands of bits. A finite circuit or the expanded
original table can implement the same finite function. This is a bounded
local decoder, not an unbounded interpreter hidden in a primitive tick.

For compiler outputs, with `R` supplied rows, construction takes
`O(D+A+R)` DAG/address/row visits and exact-integer operations, plus temporary
identity-map operations. A conservative bit-work bound is
`O((D+A+R)*(M+bit_length(D+R+2)))`, using ordinary expected-cost identity-map
operations. Stored metadata has conservative size `O((D+P+B)*K+A)` bits for
compiler outputs. General public constructors may retain unused descriptors
with much larger counts; their stored size and validation work must also
include the actual widths of those counts. Such unused counters are not read
by an active transition and do not enlarge its active arithmetic registers.

Runtime configuration remains exactly one finite control plus one occurrence
zipper. The zipper can grow with input depth and its immutable Python updates
retain their existing costs. One original microtick still executes exactly
one primitive command. The bounded Python decode overhead is not asserted to
be one constant-time machine instruction.

### Exponentially many controls, unchanged positive running time

For the shared doubled literal family `D_0=S`, `D_(k+1)=(D_k,D_k)`,

```text
W(D_k) = 7*2^k - 6
Y(D_k) = F(D_k) = 6*2^k - 5.
```

For `k>=1`, the two rows `(D_k,L)` and `(D_k,R)` use one `(k+1)`-descriptor
pattern code, two blocks and two address entries. Their inverse/ascent graph
has

```text
state_count = 14*2^k - 4
inverse.tick_bound = ascent.pass_bound = 12*2^k - 4.
```

Their descent graph has `14*2^k-8` controls and pass bound `12*2^k-9`:
failure of the first matcher followed by success and one selected edge of the
second is one tick longer than failure of both matchers. Storage has `O(k)`
descriptor entries but `O(k^2)` bits in this representation. Positive matcher
execution remains exponential in `k`.

The depth-4,096 tests compile these three objects without a materialized
compiler. They perform an isolated lookup traversing all 4,097 descriptor
levels, then run only tiny mismatches with independent caps of 2 or 8 ticks.
They explicitly reject a cap of 7 where 8 ticks are required. There is no
giant positive execution or implicit budget based on the enormous bound.

## Verification

```sh
timeout 30s python -m unittest discover -s tests -p test_succinct_walkers.py -v
```

The component suite covers:

- Independently written twelve-state inverse instructions and a two-edge
  restoration/incoming-test layout
- All states and six observations of 585 strict small-row lists, 64 deeper
  single rows, and 100 seeded shared-DAG families, for all three compilers
- Independent success/failure graph DP across every scoped strict row with
  patterns of two through four leaves, including an unattainable graph bound
- Complete control/cursor trace equality in 10,731 small-tree invocations,
  plus every occurrence of shared appender, word, marker and value encodings
- Exact restoration at every failed reversed-address prefix and late matcher
  failure before trying another ancestor candidate
- Shared input occurrences, direct unchanged-runtime execution, feedback,
  priority/coherence limitations, and absorbing false exits
- Frozen metadata, repeated independent invocations, compiler/file/tree
  equality/hash hooks disabled during execution, and code-bounded loops
- A 4,097-block search, depth-4,096 doubled DAG, and depth-6,000 scoped pattern
  and address, all without recursive validation or occurrence expansion
- Empty families, shadowed empty-address rejection, malformed input/metadata,
  strict type checks, finite targets, unused metadata indices, and explicit
  external execution-budget failure

These tests supplement the same-index structural proof and preserve the
limits of the underlying ancestor-candidate semantics.
