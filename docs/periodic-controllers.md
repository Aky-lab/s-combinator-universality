# Program-static controllers for positive CTS periods

`s_only.periodic_selector.selector_table` extends the independently reconstructed
root-reset S controller to any positive CTS period, within explicit compile-time
resource limits. This is a separate entry point: `s_only.program_selector` still
accepts exactly two phases, and its five recorded graphs retain their original
start states and byte-serialization digests.

The executed evidence for this finite-graph reconstruction covers periods
1, 3, 4 and 5.
Native trajectories reach two CTS horizons; independent synthetic witnesses
exercise routes and phase recovery across every phase, including successor
wraparound. Larger periods and longer native trajectories remain separate work.

## Interface and budgets

```python
from s_only.cts import Program
from s_only.encoding import encode
from s_only.periodic_selector import selector_table, reduce_once

program = Program(("01", "", "01"))
table = selector_table(program, max_states=3_000_000)
term = encode(program, "11")
term = reduce_once(term, table)  # one native S contraction, or None if normal
```

Compilation takes a fixed program, never an input word, current S tree, desired
horizon, source state, or selected-address schedule. Its typed cache holds at
most one table. The syntax budgets are 128 total appendant bits and 16 phases
by default; `None` disables either budget explicitly. The phase budget also
bounds dispatcher syntax when every appendant is empty. It is a resource
policy, not a semantic restriction to 16 phases or evidence that every such
program fits available memory.

`max_states` optionally caps emitted controls. It does not bound temporary
probe fragments or total host memory. Syntax/state exhaustion and caught host
`RecursionError` become `CompilationLimit`; operating-system memory and process
time limits remain the caller's responsibility. No compile-time budget becomes
a runtime register. The legacy API retains its original default 128-bit budget
and validation, including rejection of Boolean or floating-point budget values.

The shared compile core in `program_selector_parts/compiler.py` emits both
APIs' graphs. `PatternFamily` retains its two-phase compatibility default;
`required_period=None` is the explicit general-period compile-time mode.

## Static generalization

Four parameterized changes extend the existing row families:

1. Dispatcher construction pairs adjacent trees, carries an odd final tree
   unchanged, and repeats until one tree remains, exactly as the initial
   encoder does. It emits neither padding leaves nor fictitious phases.
2. A frozen, phase-major tuple maps `(phase, bit)` to the actual root-to-leaf
   route. Rows use this route instead of interpreting the label pair as two
   directions. Duplicate appender or subtree code never identifies a label.
3. Completed-Local phase labels use `(phase + 1) % program_period`.
4. The dispatcher probe emits a finite target for each program phase and each
   front-bit branch. All such choices are graph controls fixed at compilation.

For example, the six labels of period three have routes `000`, `001`, `010`,
`011`, `10`, `11`; the final two leaves are shallower. Period five also has
unequal-depth leaves. Repeated empty or nonempty appendants retain distinct
phase labels despite identical literal code.

Deletion/handoff chronology remains Boolean. In particular, a Local or
tombstone toggles chronology parity even when the program period is odd.
Clock parity also retains its original numeral-stage meaning. Neither query
becomes a modulo-program-period counter. `priority.py` and `clock.py` are
unchanged by this extension.

## Runtime boundary

The result is the existing frozen `SelectorTable(states, start)`. Each state
has exactly six local-observation entries: S/application node kind combined
with root/left/right incoming side. Instructions contain only a primitive
command and a finite target index. The configuration remains finite control
plus one occurrence zipper.

Every invocation starts at the current tree's root and the same table start
state. Selection changes no bare syntax. `Rdx` performs exactly one native
`S x y z → x z (y z)` contraction and enters an absorbing terminal. There is
no source evaluator, structural reader, program object, runtime route array,
input-dependent compiler, global phase counter, prior invocation cursor,
schedule, or supplementary unbounded control stack. The zipper is the
permitted occurrence context.

The fresh-response, marked-handoff, active-endpoint and root-reset fallback
priority order is unchanged. Existing explicit-table runtime wrappers are
reused, including `reduce_once` returning `None` on normal form.

## Independent bounded checks

```sh
# Bash; cap virtual address space at 6 GiB and total process time at 420 s.
ulimit -v 6291456
timeout 420s python -m unittest discover -s tests -p test_periodic_selector.py -v
python -m unittest discover -s tests -p test_program_selector.py -v
```

The new tests use a largest-power-of-two split formula to derive expected
routes independently of the production adjacent-pairing loop and stored route
map. Concrete S terms, not instantiated production patterns, witness every
intermediate dispatcher stage and every nonempty appender stage in each phase.
Dispatcher witnesses independently encode the prior phase and deleted bit in
the designated carrier; the actual finite phase/front-bit probe must recover
them and select the expected redex. Both fresh and marked completed Local
witnesses check the accumulator address and appendant-dependent history depth.
Repeated-code and all-empty period-three and period-five programs are included.

A separate parity witness checks zero through three completed-Local layers in
every phase of odd periods 1, 3 and 5, verifying restoration and Boolean parity.
The runtime-isolation check disables compiler, source-transition and structural
reader entry points after construction, then checks 30 root-reset selections,
the exact one-contraction result, immutable table shape, and absorption.

Compatibility tests compare all five legacy state counts, start controls, and
SHA-256 digests of every `(state, observation, command, target)` row against the
frozen two-phase report. They also compare the two public APIs' entire returned
tables for `("01", "001")`.

### Native trajectories

The focused matrix uses seeds `11`, `1`, and the empty word for each program:

| Period | Appendant tuple | States | Start | Contractions for `11` / `1` / empty |
| ---: | --- | ---: | ---: | --- |
| 1 | `("01",)` | 129,268 | 111,742 | 89 / 81 / 69 |
| 3 | `("01", "", "01")` | 694,400 | 621,444 | 101 / 101 / 89 |
| 4 | `("10", "1", "", "10")` | 1,201,863 | 1,086,283 | 105 / 105 / 89 |
| 5 | `("01", "", "1", "01", "001")` | 2,134,486 | 1,945,270 | 111 / 111 / 99 |

All twelve runs check their initial state and horizons one and two. The driver
compares every structural sample with a separately computed CTS trajectory and
never feeds the answer back into selection. There are 1,150 native contractions,
1,162 samples and 36 accepted checkpoints. For seed `11`, data sequences are:

- Period 1: `11 → 101 → 0101`, phases `0 → 0 → 0`
- Period 3: `11 → 101 → 01`, phases `0 → 1 → 2`
- Period 4: `11 → 110 → 101`, phases `0 → 1 → 2`
- Period 5: `11 → 101 → 01`, phases `0 → 1 → 2`

The largest observed tree has 1,701,241 unfolded nodes and the longest
selection takes 164,434 primitive microticks. Each seed has explicit limits of
180 native contractions, 2,000,000 microticks per selection, 5,000,000 unfolded
nodes, and a soft 90-second deadline. The next contraction's exact growth is
checked before performing it. The final test process additionally uses the
hard timeout and address-space cap above. Compilation is capped at 3,000,000
states in this matrix.

The initial period-five attempt with a 2,000,000-state cap raised
`CompilationLimit: controller exceeds 2000000 states`. It did not produce a
controller or a successful run. Only the explicitly raised 3,000,000-state
retry produced the 2,134,486-state graph shown above. Both outcomes are retained
because final graph size alone obscures the cost of construction.

The structural reader uses the existing totalized empty-word convention:
horizon and phase continue advancing while data remains empty. Ordinary CTS
semantics stop on an empty queue. The test's oracle extends that terminal case
only for readout comparison; an empty word is not an S normal-form claim.
Native horizon two exercises phases zero and one for periods greater than two;
later-phase and wraparound coverage there is synthetic, not a claim of a
complete native cycle.

### Deterministic experiment report

[The report](../results/positive_period_programs.json) records all selected
addresses, checkpoint prefix hashes, graph digests, rejected-sample counts,
and the period-five compilation attempts. Reproduce it with:

```sh
timeout 620s bash -c 'ulimit -v 6291456; python -m tools.periodic_selector_report --deterministic --output /tmp/positive-period-programs.json'
cmp results/positive_period_programs.json /tmp/positive-period-programs.json
```

The report reuses the two-phase experiment's external bounded driver. Its
global soft deadline is 600 seconds; the shell command adds a hard timeout
and a 6 GiB address-space cap. Compile-time caches are released between
programs. All 1,162 current-tree readout decisions are checked, including
1,126 rejected samples, while selection receives only its static table and
the current tree. The file's SHA-256 is
`e54cede3399a9902a66777a33ce63c7b87b3c6a46a51b1ef968112d4073cc017`.

Large-program construction needs additional scaling work before the compact
482-phase source fixture can be run. The [static cost derivation](compilation-cost.md)
counts 571,594,401,546 states in one currently inlined component alone.
A quotient of a finished graph does not remove the cost of constructing that
graph. The all-program simulation
argument and the independent formal-source check remain separate obligations.

## Pinned mathematical definitions

The construction follows source inspected at
`cstrawberry/predictive-universe`, commit
`85a867988442fc423279341200f81634a1e65582`:

- [Carrier phase recovery](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/Research/RootResetCarrierPhaseProbe.lean): `labelledLocal` uses `CTS.nextPhase`; `labels` includes Base and both Local statuses.
- [Carrier chronology parity](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/Research/RootResetCarrierParityProbe.lean): controls carry a Boolean for arbitrary programs; restored tagged edges toggle it.
- [Local dispatcher probe](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/Research/RootResetLocalDispatcherProbe.lean): finite phase/front-bit controls and route-specific rows.
- [Dispatcher stage rows](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/Research/RootResetDispatcherStageRows.lean): fixed-route exposed/forked stages and recursive context lifting.

See [the two-phase construction](two-phase-programs.md) for the unchanged
completed-Local, selected-appender, carrier, priority, and clock dependencies,
the [general appender lemma](appender-gadget.md) for a direct occurrence-level
proof of every finite append routine, and [the structural reader](cts-reader.md)
for the separate checkpoint grammar.
