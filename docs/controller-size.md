# Whole-controller count and start preflight

`s_only.controller_size.controller_size` counts the **entire original,
unquotiented finite controller**, with its original start index and assembly
stage allocation totals. It constructs no matcher descriptors, probe tables,
row-block tables, interval tables, or materialized controller graph. Its output
is an accounting record, not executable control code.

This closes a different question from `compilation_cost`: that module derives
the selected-action component directly from source-word arithmetic. The new
preflight still invokes the existing fixed-program pattern factories and the
active/marked/fresh graph constructors. Its cost depends on their finite pattern
DAG construction and on traversing those DAGs. It must not be described as a
linear-time source-only formula or a prediction of physical code size.

## Counting rules

Let `W` be the number of nonterminal controls emitted by a standalone matcher:

- `W(_) = 0`
- `W(S) = 1`
- `W((a,b)) = 6 + W(a) + W(b)`

The application matcher always emits six direct controls, plus both child
occurrence widths. Shared pattern objects save counting work, but never merge
the original control occurrences. Every nonempty matcher starts at its last
emitted control. The zero-width wildcard starts at true, state 1.

A forward row with pattern `p` and fixed address `a` emits `W(p) + len(a)`
nonterminals. An inverse row emits `W(p) + 3*len(a)`. Rows are emitted in reverse
priority order. The count keeps unreachable suffix controls. In particular,
`(_, ())` emits no controls but resets the family entry to true, even if later
rows already allocated a nonempty suffix. An empty row family starts at false,
state 0. Inverse rows and walkers require nonempty, pattern-scoped addresses.

Ordinary embedding removes false 0 and true 1 and redirects them to the supplied
continuations. A closed descent/ascent walker removes only false 0: state 1 has
become feedback and remains allocated. This includes one unreachable feedback
control for an empty walker family. The remapping of a retained standalone
control `q` is `origin + q - dropped`, where `dropped` is two for an ordinary
fragment and one for a walker. A direct reservation adds exactly one state.

These rules determine both allocation counts and entry indices without decoding
any of the six transition entries. They are an allocation/index derivation;
they do not prove the correctness of the controller's transition semantics,
termination, source simulation, S-only universality, or eventual halt event.

## Assembly and retained data

The top-level count follows `_assemble_program`'s exact evaluation order:

1. Normal, contracted, and contraction controls
2. Euler fallback and its root reset
3. Active pass
4. Root reset before marked, then marked pass
5. Root reset before fresh, then fresh pass

The active, marked, and fresh constructors and `PatternFamily` are reused
unchanged. The top-level order is independently transcribed, and tests also
run the shared `_assemble_program` with the counting facade to detect drift.
Stage records give the first allocated index, number of allocated states, and
returned entry. Their state counts partition the whole graph. Fragment-kind
totals independently partition it together with the direct-reservation count.

`CountingGraphBuilder.states` is a sparse reservation-assignment facade, not a
virtual list. Its integer-keyed dictionary retains only filled/unfilled flags
for directly reserved controls. Six-entry rows supplied by existing direct-row
constructors are transient and discarded on assignment. Pattern widths are
computed with iterative postorder traversal and integer identity keys. A cache
is local to one matcher or one prepared row family, whose roots remain alive
throughout that cache's lifetime. It does not recursively hash tuples, unfold
shared occurrences, retain all past patterns, or risk identity reuse between
fragments. There is no allocation proportional to the virtual state count.

`pattern_work` counts traversal-stack pops, processed rows, and checked address
directions. `pattern_nodes` counts newly evaluated DAG nodes across those local
caches. Neither includes work performed inside the shape factories. Integer
arithmetic uses arbitrary precision; bit costs are additional.

## Bounds and reproduction

Defaults admit up to 64 phases and 1,024 total appendant bits, with at most
100,000,000 pattern-work units and a 120-second cooperative wall-clock budget.
Syntax caps can be explicitly changed, but none of these bounds can be disabled
with `None`. The clock is checked at fragment/direct-state boundaries and every
1,024 work units. Factory construction can occur between checks. The library
does **not** claim a hard time or memory guarantee: use a separately bounded
process for larger preflights. Exceeding a bound means no exact whole result was
obtained; a partial count must never be presented as the final graph size.

The standard-library-only focused verification includes materialized and
succinct references through period five. It is intentionally more expensive
than the count-only operation:

```sh
timeout 180s sh -c 'ulimit -v 1048576; exec python -m unittest discover -s tests -p test_controller_size.py -v'
```

The fixed 38-phase, 760-bit UT19 program can be measured without compiling a
runtime table:

```sh
timeout 180s sh -c 'ulimit -v 1048576; exec python -m s_only.controller_size --ut19 --max-pattern-work 250000000 --max-compile-seconds 150' > /tmp/ut19-controller-size.json
```

`ulimit -v` is in KiB on the documented Linux shell; 1,048,576 KiB is 1 GiB.
The JSON output is deterministic on successful completion. A cooperative
resource failure prints `complete: false` and returns failure. An external
timeout or process kill may leave no result, so check the process exit status.

The initial UT19 attempt used the defaults and stopped at the 100,000,000-work
cap after 53.97 seconds, at 633,612 KiB peak RSS. It did not establish the whole
count. The reproduction above raises only the pattern-work and cooperative-time
budgets; the external 180-second/1-GiB envelope is unchanged. The successful
initial 13-test suite ran in 70.98 seconds under that same hard envelope. After
adding the independent selected-action formula comparison, the final 14-test
suite passed in 77.24 seconds, again within the unchanged hard envelope.

## Fixed UT19 result

The second bounded attempt completed in 122.84 seconds at 633,648 KiB peak RSS,
using 229,204,100 pattern-work units and evaluating 76,092,787 local-cache DAG
nodes. The deterministic result is saved in
[`results/ut19_controller_size.json`](../results/ut19_controller_size.json).

- Whole original graph: **2,122,868,774 states**
- Original start index: **2,064,502,462**
- Active pass: 1,843,629,910 states
- Marked pass: 62,765,845 states
- Fresh pass: 216,472,989 states
- Initial terminals/contraction, Euler fallback, and inter-pass root resets: 30 states

The independently compiled pooled table has the same whole state count and
start. The preflight does not use those figures as input. It preserves all
unreachable states, so the six-observation graph contains 12,737,212,644 primitive
entries before any physical representation sharing. The source-only
selected-action formula gives 85,600,964 states, approximately 4.03% of the whole
graph. That component's size was a lower bound, not a whole-controller estimate.

Allocation by fragment kind is also recorded: 83,251,537 match states;
422,823,536 forward-row states; 79,310,739 inverse-row states; 435,835,147 descent
states; and 1,101,647,399 ascent states. Another 416 directly reserved controls,
including direct controls inside the three passes, complete the total. These
fragment totals and the assembly stage totals are different partitions of the
same graph and must not be added together.

## Verification scope

Tests compare count/start against original materialized and succinct compilers
for the existing periods 1–5; also check archived program counts, the shared
assembly order, exhaustive small pattern/address combinations, priority rows,
zero-width resets, empty-family feedback, sparse direct reservations, and a
depth-4,096 doubly shared DAG whose occurrence count exceeds machine integers.
They reject invalid pattern/address inputs and exercise syntax, time and
pattern-work limits. A patched-compiler test ensures preflight never invokes a
probe/table compiler. This is differential verification of counts and starts,
not another full transition comparison or native S execution experiment.

Physical storage, compilation time, lookup time, reachable-state count,
minimization, and the runtime microtick cost cannot be inferred from the virtual
state total alone. Pooling may share code without removing a single state.
