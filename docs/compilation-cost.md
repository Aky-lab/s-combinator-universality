# Static cost of literal-inlining compilation

The compact 482-phase source fixture cannot be treated as merely a larger
instance of the small compiled controller experiments. For the current Python
compiler, **one selected-action component alone has an exact symbolic allocation
of 571,594,401,546 states before quotienting**. Of these, 568,498,572,096 states
come solely from repeated restoring matchers for dormant dispatcher siblings.
No large pattern family or controller graph was constructed to obtain this
result. These are counts of six-observation control states, not bytes or ticks.

The bound concerns this repository's concrete literal-inlining compiler.
A different construction can share control before materialization, so this
count describes the present allocation strategy rather than the intrinsic
complexity of the selection behavior.

The [succinct probe prototype](succinct-probes.md) already represents a
single restoring matcher through exactly indexed transition lookup, without
enumerating its controls. Extending that representation to row composition
and complete controllers is the next construction step.

## Scope and attribution

The mathematical restoring matcher and selected-appender row construction remain
attributed to Cinematic Strawberry's construction, pinned at
[`85a867988442fc423279341200f81634a1e65582`](https://github.com/cstrawberry/predictive-universe/tree/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality).
See the existing [probe compiler](probe-compiler.md),
[appender gadget](appender-gadget.md), and
[positive-period controller](periodic-controllers.md) descriptions. The static
allocation derivation below is independent work for this repository's Python
implementation, checked against its concrete small-table allocations.

The relevant local implementation is:

- [`probes._Builder.match` and `compile_rows`](../s_only/probes.py)
- [`GraphBuilder.embed` and `rows`](../s_only/selector_parts/graph.py)
- [`PatternFamily.route_pattern`, `appender_rows`, and `selected_action_rows`](../s_only/program_selector_parts/patterns.py)
- [`compile_endpoint`](../s_only/program_selector_parts/active.py)
- [`compile_program` and `encoding_stats`](../s_only/encoding.py)

A successful unquotiented whole-controller construction includes the
selected-action row component once. Other endpoint, dispatcher, frontend,
priority, fallback, and terminal controls are additional allocations. Explicit
syntax limits, state budgets, recursion exhaustion, or other resource failures
may stop an attempted compilation before these counts are allocated. This
analysis predicts the component required by successful materialization; it does
not assert that the current implementation can finish that materialization.
The default 16-phase and 128-appendant-bit guards already reject this fixture.

## 1. Exact restoring-matcher allocation

Let W(P) count newly allocated nonterminal states for a matcher of pattern P,
with its two continuations already supplied. Inspection of `_Builder.match`
gives:

```text
W(_)       = 0
W(S)       = 1
W((A, B))  = 6 + W(A) + W(B)
```

The application case allocates `U yes`, shared `U no`, `R`, `U`, `L`, and the
node-kind test. Its two recursive child matchers allocate the remaining states.
This recurrence counts allocation, including any states a subsequent reachability
or equivalence pass might remove. It differs from the conservative pattern
microtick budget in `pattern_budget`.

A closed S tree with n unfolded nodes has (n−1)/2 application nodes and (n+1)/2
S leaves. Therefore its literal matcher has exactly:

```text
W(literal(t)) = (7n − 5) / 2
```

Term or pattern object sharing does not change this count: `_Builder.match`
recurses for every occurrence and does not memoize matchers. `compile_rows`
separately allocates each row's matcher and one movement state per address edge.
It also creates two absorbing answer states. `GraphBuilder.embed` redirects those
two answers to existing continuations and allocates all other states once, with
no merging even when rows or continuations are identical. Thus:

```text
states added by builder.rows(rows, yes, no)
    = sum over rows (W(pattern) + length(address))
```

## 2. Dispatcher literals and dormant sibling costs

Let p be the positive number of phases, M the total appendant length, and O the
total number of appendant ones, counted with phase multiplicity. The encoded
dispatcher has 2p labelled leaves in phase-major order `(0,0), (0,1), (1,0), ...`.
A bit-zero leaf always contains PI; a bit-one leaf contains its phase's appender.
Even identical action code retains separate labelled occurrences.

For an appendant with m bits and o ones:

```text
routine nodes                     = 5 + 20m + 2o
leaf nodes, including outer B     = 9 + 20m + 2o
W(leaf)                           = 29 + 70m + 7o
```

A branch code is `B (S left right)`, where B is `S S`. Its matcher cost is
`27 + W(left) + W(right)`. The whole dispatcher consequently has:

```text
dispatcher nodes = 32p − 7 + 20M + 2O
W(dispatcher)   = 112p − 27 + 70M + 7O
```

For a leaf j at route depth d_j, expanding the recurrence along that route
partitions the dispatcher cost into its selected leaf, its d_j branch overheads,
and the literal sibling subtrees left dormant at each fork. The exact sum of
those sibling literal matcher costs is:

```text
C_j = W(dispatcher) − W(leaf_j) − 27d_j
```

`route_pattern` includes every one of these dormant sibling literals once in
every row for the selected leaf. Their `call_pattern` wrappers add further
states, deliberately excluded from C_j. Distinct phases are counted separately,
even for identical appendants, because the current compiler emits independent
rows and has no control-state interning.

### Independent route depths

The encoder pairs adjacent subtrees at each round and carries an odd final
subtree unchanged, without padding. Equivalently, a subtree with n > 1 leaves
splits after the largest power of two strictly below n. To see this, after k
rounds each full block of 2^k consecutive leaves is a complete subtree; a final
short block follows the same construction recursively. The last merge joins
the leading largest complete block to the remaining suffix. This also covers a
power-of-two n, whose split is n/2.

`dispatcher_leaf_depths(2*p)` uses this largest-power split, independently of the
encoder's pairing loop and route metadata. An iterative traversal visits 4p−1
intervals and retains all 2p occurrence depths. Tests compare those depths with
actual labelled encoder routes, including odd periods and duplicate code.

## 3. Dormant-literal lower bound

An empty appendant contributes no selected-action rows. A nonempty m-bit
appendant contributes one initial row, m Push-stage rows, and m−1 next-call rows:
exactly 2m rows. All are associated with that phase's bit-one leaf. Therefore:

```text
L_dormant = sum over phases j with m_j > 0 (2m_j C_j)
```

This is a lower bound even for the selected-action component alone: it omits
Local wrappers, chosen-route scaffolding, live appender-response patterns, and
all fixed output-address movements. It requires only lengths, ones, and route
depths, with no pattern expansion.

## 4. Exact selected-action component

A slightly stronger linear-time analysis also counts the omitted work. For a
phase's word, let T be the sum of its one-bit positions, numbered starting at 1.
Positions matter because appender-stage rows repeatedly contain suffix literals.

A fresh Local wrapper adds 72 matcher states. A selected leaf's chosen wrapper
adds 13. Each selected ancestor's wrappers add 25 states plus its dormant
sibling literal. Thus every row has:

```text
W(row) = 85 + 25d + C + W(live response)
```

For the row at zero-based appender position i, write r = m−i−1 for the remaining
suffix length, q for its number of ones, and b for the current bit. The live
responses have the following exact costs:

```text
initial call:               21 + 70m + 7o
Push stage i:               90 + 70r + 7(q+b) + 6i
next-call stage i, r > 0:   27 + 70r + 7q     + 6i
```

Summing these one initial, m Push, and m−1 next-call responses gives
`76m² + 105m + 14T`. The common selected address has length `4 + 2d`; history
adds i edges for each Push row and i+1 for each next-call row. Total output
address allocation is `m² + 7m + 4md`. Consequently:

```text
selected matchers = 2mC + 76m² + 275m + 50md + 14T
selected addresses = m² + 7m + 4md
exact embedded selected-action states
                  = 2mC + 77m² + 282m + 54md + 14T
```

These formulas also return zero for m = 0. Their sum across all phases is an
exact count for this component and a stronger lower bound on the entire
unquotiented graph. Formula evaluation uses O(p+M) source inspections and
arithmetic operations. Counting distinct appendants adds expected O(p+M)
hashing work. O(p) integer summaries are retained, with arbitrary-precision
bit costs additional. The calculation creates no terms, patterns, giant
prefix strings, or controller states.

## 5. Small actual-allocation checks

The focused tests compare the formulas against the actual `compile_pattern`,
`compile_rows`, and `GraphBuilder.rows` allocation paths. Coverage includes
all binary one-phase appendants through length four, empty and all-zero words,
identical appendants, unequal one positions, and periods 1 through 5. Route
metadata is separately checked for periods 1–17, 31, 32, and 33.

The following comparison uses the exact selected component and previously
recorded whole-controller counts. The focused test also actually recompiles the
129,268-state one-phase whole graph, checking that value afresh. It does not
recompile the larger recorded whole graphs.

| Appendants | Selected rows | Dormant bound | Exact selected component | Whole graph |
|---|---:|---:|---:|---:|
| `("01",)` | 4 | 116 | 1,124 | 129,268 |
| `("1", "")` | 2 | 228 | 709 | 257,299 |
| `("", "")` | 0 | 0 | 0 | 210,962 |
| `("01", "", "01")` | 8 | 2,876 | 5,216 | 694,400 |
| `("10", "1", "", "10")` | 10 | 5,490 | 8,445 | 1,201,863 |
| `("01", "", "1", "01", "001")` | 16 | 13,436 | 18,594 | 2,134,486 |

Whole-graph records: [two-phase](../results/two_phase_programs.json) and
[positive-period](../results/positive_period_programs.json). A zero bound for all
empty appendants correctly leaves the cost of all other controller components
unaccounted for.

## 6. Compact source fixture

The deterministic report reads
[`artifacts/neary-left-toggle/program.json`](../artifacts/neary-left-toggle/program.json)
and records the input file's SHA-256 in its output. Source statistics are:

- 482 phases, 63,644 appendant bits, 140 ones
- 41 unique appendants; 126 nonempty appendants; maximum length 1,998
- 1,288,577 unfolded dispatcher nodes; 4,510,017 literal-matcher states
- 960 dispatcher leaves at depth 10; the final four at depth 6
- 127,288 selected-action rows

The resulting allocation counts are:

| Quantity | States |
|---|---:|
| Dormant sibling literals alone | 568,498,572,096 |
| All selected-action matchers | 571,551,887,060 |
| Selected output-address movements | 42,514,486 |
| Exact embedded selected-action component | **571,594,401,546** |

The small number of shared immutable encoding objects or unique appendants does
not limit these allocations: matching unfolds literal occurrences and repeats
them across rows. This identifies a concrete construction bottleneck before any
attempt to build the compact fixture's current whole controller.

A post-compilation quotient cannot avoid the pre-quotient allocation already
required to build its input graph. A redesigned compiler that shares or factors
controls before allocation could change this result and would need its own
correctness and cost analysis. No minimal-controller bound, peak memory-byte
estimate, time-to-compile estimate, or compression guarantee is inferred here.

## Reproduce

Python 3.10 or later, standard library only, from the repository root:

```sh
python -m unittest discover -s tests -p test_compilation_cost.py -v
python -m tools.compilation_cost_report \
  --program artifacts/neary-left-toggle/program.json \
  --output /tmp/neary_compilation_cost.json
cmp /tmp/neary_compilation_cost.json results/neary_compilation_cost.json
```

Add `--include-phases` for each phase's contribution. The CLI bounds the input
file, source bits, and phase count before analysis. Its output has no timestamp
or nondeterministic timing measurements. The fixture test makes calls to term,
pattern, and table construction fail if invoked during the static calculation.

Implementation: [`s_only/compilation_cost.py`](../s_only/compilation_cost.py).
Stored report: [`results/neary_compilation_cost.json`](../results/neary_compilation_cost.json).
