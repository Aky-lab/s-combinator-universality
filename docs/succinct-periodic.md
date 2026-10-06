# Bounded positive-period succinct controllers

`s_only.succinct_periodic.compile_table` is an opt-in extension of the
[exact interval-coded selector](succinct-selector.md). It admits fixed binary
CTS programs with **one through five phases and at most eight total appendant
bits**. The existing `succinct_selector.compile_table` remains restricted to
periods one/two, with its original defaults, graph indices, and contract.
Neither materialized selector API is changed.

```python
from s_only.cts import Program
from s_only.succinct_periodic import compile_table
from s_only.root_selector import execute, erase
from s_only.terms import App, S

table = compile_table(Program(('01', '', '01')))
assert (table.state_count, table.start) == (694_400, 621_444)
assert table.metadata_records == 70_326
assert not hasattr(table, 'states')
term = App(App(App(S, S), S), S)
result = execute(term, table)  # The original primitive interpreter.
assert erase(result.cursor) == App(App(S, S), App(S, S))
```

## Limits and exact scope

The new entry point accepts these keyword-only limits:

| Limit | Default | Admitted values |
| --- | ---: | --- |
| `max_phases` | 5 | Plain integers 1 through 5 |
| `max_appendant_bits` | 8 | Plain integers 0 through 8 |
| `max_metadata_records` | 250,000 | Positive plain integers |
| `max_compile_seconds` | 10 | Positive plain integers/floats fitting a finite clock value |

The syntax caps cannot be disabled with `None` or raised beyond these ceilings.
The phase cap applies even when every appendant is empty. A valid program may
still exhaust an explicit metadata/time budget. A budget exhaustion is
`CompilationLimit`; malformed syntax or budgets are rejected before the
relevant construction. Only an exact `cts.Program` with a nonempty plain tuple
of plain binary strings is accepted. Subclasses, Boolean numeric budgets, and
objects with spoofed metaclass equality cannot enter the immutable code.

The metadata budget bounds referenced retained representation slots. The time
budget is **cooperative**, checked at graph operations and around fragment
compilation/finalization. Neither bounds transient allocation inside a fragment
compiler, preempts that compiler, or promises process-level memory safety.
Experiments require an external hard timeout and address-space cap. Exhaustion
is an incomplete experiment, not evidence for or against simulation.

The finite ceilings are intentional. This API does not attempt the 482-phase
fixture, remove input caps, solve all-program compilation scaling, or prove
all-input termination/universality from finite tests.

## Shared graph construction and runtime

Both succinct entry points call a single compile-only `_assemble_program`
helper, after checking their separate public limits. This helper is a minimal
extraction of the old period-one/two compiler body. It creates the same
`SuccinctGraphBuilder` and calls the unchanged `program_selector_parts`
constructors in their original order:

1. Normal, contracted and selected/Rdx states.
2. Root-reset Euler fallback.
3. Active worker.
4. Marked worker, continuing through a root reset to active.
5. Fresh worker, continuing through a root reset to marked.

`PatternFamily(program, required_period=None)` is fixed compile-time data.
Identical constructor operations and exact fragment embedding give the same
control count, start, six same-index transition entries, and unreachable states
as the materialized compiler. The [component/composition argument](succinct-selector.md#embedding-equivalence-by-index)
applies without an additional decoding mechanism: expanding the admitted
periods changes the fixed patterns, not the embedding proof or runtime.

The output remains the exact frozen `SuccinctSelectorTable(blocks, start)`.
Lookup receives only a finite control and the six combinations of node kind
and incoming side. It searches immutable intervals, decodes an immutable
fragment and rebases one target. It receives no input term, source state,
selection history, evaluator, compiler or mutable cache. The source `Program`,
pattern family, builder dictionaries and compile clock are not retained.

All type whitelists use identity, and direct-row primitive data is preflighted
before equality/uniformity checks. Nested fragment validators are unchanged.
The conditional finite-configuration bound remains
`linear_coefficient = state_count + 1`; it does not assert termination. Lookup
cost still depends on fixed-code size and integer bit lengths, not just the
number of logical interpreter ticks. Native runs use the unchanged
`root_selector.step`, fresh fixed control/root per invocation, one S contraction,
and immediate absorption.

## Physical representation measurements

The following measurements use the fixed programs already archived in
[`positive_period_programs.json`](../results/positive_period_programs.json).
Compile times are single local observations, not performance guarantees.

| Appendants | States | Start | Intervals | Direct rows | Metadata slots | Compile seconds |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `('01',)` | 129,268 | 111,742 | 314 | 120 | 16,431 | 0.104 |
| `('01', '', '01')` | 694,400 | 621,444 | 426 | 136 | 70,326 | 0.433 |
| `('10', '1', '', '10')` | 1,201,863 | 1,086,283 | 482 | 144 | 113,584 | 0.857 |
| `('01', '', '1', '01', '001')` | 2,134,486 | 1,945,270 | 538 | 152 | 182,697 | 1.223 |

The metadata definition is inherited: seven slots for a direct block and its
six Commands, one per fragment block, and one per referenced nested table
header, pattern-code wrapper, descriptor, row block and address direction.
Separate embeddings count their referenced code separately. This is neither
Python bytes nor integer storage, and the states-to-slots ratio is not a RAM
compression factor.

| Period | Pattern descriptors | Pattern-table references / identity-distinct tables | Equality-distinct tables | Reachable-object bytes | Lookup-depth bound |
| --- | ---: | ---: | ---: | ---: | ---: |
| 1 | 12,093 | 520 / 520 | 47 | 1,326,962 | 36 |
| 3 | 59,072 | 1,136 / 1,136 | 75 | 6,036,918 | 43 |
| 4 | 97,890 | 1,500 / 1,500 | 89 | 9,910,414 | 42 |
| 5 | 160,811 | 1,912 / 1,912 | 107 | 16,243,546 | 47 |

The byte figure is an external `sys.getsizeof` sum, visiting every object
identity reachable through dataclass fields and tuples once. It includes
integers and tuples; it excludes allocator overhead, compiler temporaries,
code and process RSS. It is platform-dependent, not a memory bound. Equality
and identity measurements are external instrumentation only.

Every referenced pattern table in this default compiler is a distinct object,
while many have equal descriptor contents. **Cross-fragment metadata duplication
remains real; no cross-fragment interning is implemented.** These measurements
establish modest-period feasibility only. The proof for huge virtual component
counts does not imply a scalable whole-controller compiler for large periods.

## Verification

`tests/test_succinct_periodic.py` covers:

- Fixed counts/starts/metadata and boundary entries for periods three/four/five.
- Original-order constructor composition with synthetic workers and root resets.
- Exact identity-based type checks, mutable and hostile-metaclass impostors,
  plain binary syntax, mandatory budgets and exact metadata thresholds.
- Empty-word five-phase programs, tightened phase/bit budgets, and soft deadline
  exhaustion before source-pattern construction.
- Equality of the old/new tables for admitted small programs, unchanged old
  defaults, and continued old-API rejection of period three and nine-bit syntax.
- A complete traversal of retained objects to exclude source programs, mutable
  containers and caches; repeated/out-of-order lookup with compilation, source
  evaluation, file and clock access patched to fail.
- Unchanged native execution and absorption, plus the first twelve seed-`11`
  selections per larger period, compared with archived paths only after selection.

Run the focused suite from the repository root:

```sh
timeout 180s sh -c 'ulimit -v 1048576; exec python -m unittest discover -s tests -p test_succinct_periodic.py -v'
```

The separate large comparison serially retains one materialized reference,
checks all six entries and every status, verifies the original start and
archived text-row digest, releases that reference, and executes the succinct
controller from seed `11` through horizon two. The external checkpoint reader
and source semantics check the results; they never supply runtime choices.
Every selected address, checkpoint, aggregate selection microtick count and
other field of the bounded run is compared with the archived output.

The checking process is bounded by a 1,200-second hard timeout and 2 GiB
address-space limit, with a 1,000-second cooperative total deadline. Per-program
compilation has 15 seconds and 250,000 metadata slots; reference construction
has 3,000,000 states. Native execution is externally capped at 120 contractions,
200,000 selection ticks per invocation and 2,000,000 expanded nodes. The
contraction/tick caps also imply a finite cumulative tick ceiling. Hard limits
belong to the external shell launcher, not the library function.

All four exhaustive graph comparisons passed: **24,960,102 entries and
4,160,017 statuses**, including all unreachable states. Original starts agree
with independently materialized construction. The archived text-row digests
are reproduced exactly:

| Period | Entries checked | Graph SHA-256 |
| --- | ---: | --- |
| 1 | 775,608 | `01d339bb54065f6d0d9ca99a106fa21b59deb994c6a8bf09bddac74eee4b0ce5` |
| 3 | 4,166,400 | `38277ee9c55e38ced8ef2c18c4ca54a7e028a1290df1ca063a093624fe4307c1` |
| 4 | 7,211,178 | `3bbceb900808d754490988a9d5738749e06abf15fdb8c686325c625e2491cef1` |
| 5 | 12,806,916 | `4d9401bb322822819001dc866bc3e9123e59824aa6d5d689787a1dcddd2f34b4` |

All seed-`11` runs for periods three/four/five match the complete archived
records through horizon two:

| Period | Contractions at horizons 1 / 2 | Selection ticks | Maximum selection ticks | Peak expanded nodes | Horizon-two phase / data |
| --- | ---: | ---: | ---: | ---: | --- |
| 3 | 26 / 101 | 2,712,642 | 82,562 | 803,851 | 2 / `01` |
| 4 | 26 / 105 | 3,363,500 | 106,270 | 1,143,761 | 2 / `101` |
| 5 | 28 / 111 | 5,102,530 | 164,434 | 1,687,063 | 2 / `01` |

That is 317 independently executed native contractions and 11,178,672 selection
ticks. The full serial experiment took approximately 405.8 seconds locally.
The focused new suite passed 13 tests, and the existing `test_succinct_selector`
suite passed all 16 tests after the shared-helper extraction. No whole-repository
suite is claimed for this change.

The deterministic [project report](../results/succinct_periodic.json) includes
all graph/start/metadata results, all three full seed-`11` run records,
aggregate coverage, and the frozen source archive checksum. Timing and
platform-dependent byte measurements are excluded from the deterministic
artifact. No archived path or source transition is passed to runtime lookup.

Reproduce it with the bounded project tool and compare bytes:

```sh
timeout 1200s sh -c 'ulimit -v 2097152; exec python -m tools.succinct_periodic_report --deterministic --output /tmp/succinct-periodic.json'
cmp results/succinct_periodic.json /tmp/succinct-periodic.json
```

The tool validates options and the frozen archive structure/checksum before
compilation. It rejects budgets too small to complete the fixed coverage,
and releases each materialized reference before the native run and next
compilation. `--deterministic` removes measured elapsed time only; configured
soft/hard bounds remain disclosed. The Python function does not itself enforce
the external hard process envelope. The 15-second compile deadline applies to
succinct construction; materialized references have the state cap and the
overall external deadlines.

The focused report tests use synthetic compilers and runners to check option
validation, corrupted archives, exact fixed metadata, serial reference release,
native equality, deadline exhaustion, aggregates, and deterministic output:

```sh
timeout 120s sh -c 'ulimit -v 524288; exec python -m unittest discover -s tests -p test_succinct_periodic_report.py -v'
```

This verifier deliberately materializes a reference graph and does not
demonstrate low peak process RSS. The separate succinct representation-size
measurements do not change that limitation.
