# Program-static two-phase controllers

`s_only.program_selector` compiles a finite root-reset controller from any fixed
`Program((first_appendant, second_appendant))`. The mathematical row definitions
apply to finite binary appendants. The Python implementation accepts empty,
multi-bit, identical, and two-empty appendants subject to exposed construction
budgets and host resources. Other phase counts are rejected explicitly.

This extends the independent fixed-fixture reconstruction without replacing
`s_only.root_selector`, its pattern families, or the published queue fixture.
The generic initial encoder, controller, and structural reader are distinct
components. Only the controller performs native S contractions.

## Interface

```python
from s_only.cts import Program
from s_only.encoding import compile_program
from s_only.program_selector import selector_table, reduce_once
from s_only.cts_reader import compile_reader

program = Program(("01", "001"))
table = selector_table(program, max_states=1_000_000)
encoder = compile_program(program)
reader = compile_reader(program)
term = encoder.encode("11")

# Repeat under external experiment budgets.
term = reduce_once(term, table)
checkpoint = reader.decode(term)
```

For externally bounded execution, initialize
`Configuration(table.start, Cursor.at(term))`, then call `step(table, state)`
one primitive tick at a time. `table.status` reports `Rdx` before the one
contraction, and `contracted` afterward. `erase(state.cursor)` materializes the
result. Each invocation starts afresh at the root; no earlier cursor or control
is passed to the next invocation.

`selector_table` has no word or runtime-tree parameter. Its cache holds at most
one table and is keyed only by the immutable program and construction budgets.
`max_states` limits emitted controls; it is not a controller register and does
not bound temporary compilation memory. `max_appendant_bits` defaults to 128
total bits across both appendants; passing `None` disables that syntax budget.
A syntax-budget or state-budget overrun raises `CompilationLimit` before the
excess construction is accepted. Static literal expansion is iterative. The
shared restoring-probe compiler still uses compile-time recursion; exhausting
that host limit is also reported as `CompilationLimit`, with the cause named.
Practical compilation is additionally limited by host memory and recursion.

## Static specialization

A frozen `PatternFamily` carries the program's generic compiled dispatcher and
its four phase-major labels `(0,0), (0,1), (1,0), (1,1)`. The adjacent-pairing
layout is the generic encoder's layout for four leaves. Code for dormant
branches is a fixed literal; mutable fields and audits are independent holes.
This object is used only during graph construction and is absent from the
returned table.

Program specialization affects:

- literal ACT/environment code and fuel admission patterns;
- completed action arity, with one retained history per emitted bit;
- accumulator addresses and their inverse carrier patterns;
- the initial nonempty-action row and all intermediate appender rows;
- dormant dispatcher code and completed-route labels.

For an emitted word of length `m > 0`, selected-action rows comprise its initial
call plus `2m-1` appender-stage rows. At history depth `h`, the first Push row
selects `L^h`. When a nonempty suffix remains, the next-call row selects
`L^(h+1)`. Thus the whole selected action uses `2m` native contractions. An
empty appendant contributes no selected-action row. Both-empty programs still
have dispatch, carrier, clock, fuel, response, and fallback controllers.

The carrier chronology query retains its two finite parity controls. Phase
recovery reads the static route label of the nearest completed Local, or phase
zero at Base, then restores its entry cursor. There is no dynamically stored
phase counter, queue, route, origin address, or procedure stack.

## Runtime boundary

The returned value is the existing `SelectorTable`, containing exactly
`states` and `start`. Each state has six entries indexed by S/application node
kind and root/left/right incoming side. Entries contain a primitive command and
finite target index. The runtime configuration contains exactly a finite
control and one occurrence zipper.

Primitive commands are one-edge `L`, `R`, `U`, `stay`, one native `Rdx`, and
absorbing terminals. Fixed paths, pattern recursion, row lists, and continuation
composition are erased into the finite graph at compile time. Runtime selection
uses no source CTS evaluator, structural checkpoint reader, term hash,
serialization, recorded selection, or unbounded auxiliary stack. The shared
native contraction primitive inspects the selected redex's bounded S shape.
The zipper's parent frames are the single permitted occurrence context.

The priority is fresh response, marked handoff, active endpoint, then complete
root-reset preorder fallback. The fallback guarantees a place to search when
specialized patterns decline; passing bounded tests is not a new general
termination or simulation proof for this Python implementation.

## Checks and limits

Run:

```sh
python -m unittest discover -s tests -p test_program_selector.py -v
```

The regression suite checks all legacy static families and all 85 published
selection addresses and output hashes. The legacy program still produces
257,299 states. Other measured state counts are:

| Appendant pair | States |
| --- | ---: |
| `("0", "10")` | 342,539 |
| `("10", "1")` | 346,648 |
| `("", "")` | 210,962 |
| `("01", "001")` | 432,812 |

Independent concrete S constructors test every appender stage, including
appendant lengths four and five, as well as completed accumulator addresses.
Unrelated audit/hole values test that row guards still select native redexes.
A runtime isolation test disables the source-step function and compiler entry
points after construction.

The integration test uses each new program with seeds `11`, `1`, and the empty
word. It drives selections from current trees and independently compares all
accepted structural samples until horizon two with ordinary CTS steps. The
controller never receives the source state or the reader's result. The test
budgets are 1,000,000 emitted controls, 2,000,000 primitive ticks per invocation,
15 seconds per invocation, 5,000,000 expanded nodes, 45 seconds per seed, and
150 native contractions. Checks fail explicitly on exhausted budgets.

The structural readout convention continues advancing the horizon and phase
on an empty queue. The ordinary CTS interpreter stops on empty; the test
oracle extends that terminal state with empty data and cyclic phase only for
this readout comparison. Empty source data does not mean that the bare S term
is in normal form.

## Reproducible matrix

```sh
timeout 310s python -m tools.program_selector_report --deterministic \
  --output /tmp/two-phase-programs.json
cmp results/two_phase_programs.json /tmp/two-phase-programs.json
```

[The recorded report](../results/two_phase_programs.json) covers all five
programs above, including the original `("1", "")`, with seeds `101`, `11`,
`1`, and the empty word. Across 20 runs it checks 1,725 native contractions
and all 1,745 structural samples. Exactly 60 samples are accepted: the
initial state and horizons one and two in each run. Every accepted phase
and word matches the separately evaluated totalized CTS convention.

For `("01", "001")` on `11`, the checkpoints are `11 → 101 → 01001` at
native contractions 0, 24, and 103. For `("0", "10")` on `101`, they are
`101 → 010 → 10` at 0, 22, and 85. The largest observed tree has 897,715
expanded nodes, and the longest selection uses 66,971 primitive microticks.

The report records each graph's digest, every selected occurrence address,
checkpoint prefix hashes, and rejected-sample counts. Source evaluation,
readout and recording remain outside the selector. The expanded-node cap is
checked before contraction using the exact increase `nodes(z) - 1` for an
`S x y z` redex. Compilation has explicit syntax/state caps; wall-clock
checks are soft, so the command above adds an independent process timeout.
The experiment's horizon is two CTS steps; arbitrary-period controller
construction and all-input trajectory equivalence are separate next steps.

## Remaining positive-period extension points

The current implementation deliberately rejects periods other than two. A
future generic-period compiler would need these changes before relaxing that
check:

1. Replace the four-leaf `patterns._dispatch` construction with the encoder's
   adjacent-pairing forest, carrying an unpaired final tree unchanged. Keep a
   compile-time map from each `(phase, bit)` label to its actual route.
2. Change `PatternFamily.dispatcher_rows` to use that route map. The label pair
   currently doubles as a two-edge route; this is false for other periods.
3. Use program-period successor labels in `PatternFamily.phase_labels`, and
   emit all finite phase targets in `active.compile_dispatcher`.
4. Replace or explicitly manage compilation costs before scaling to the
   482-phase source fixture: repeated suffix-code construction in
   `appender_rows`, repeated dormant-code patterns across selected rows, and
   repeated fragment embedding all precede any final graph compression.

The restored chronology bit in `priority.compile_parity` should remain Boolean:
[the pinned carrier parity machine](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/Research/RootResetCarrierParityProbe.lean)
uses a Boolean for arbitrary programs. It controls deletion versus handoff,
whereas
[carrier phase recovery](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/Research/RootResetCarrierPhaseProbe.lean)
uses `CTS.nextPhase`. The existing clock parity concerns numeral stages and
also does not become a modulo-program-period counter. No generic-period
implementation or large-program integration is included in this extension.

## Pinned definitions

The mathematical source is Cinematic Strawberry's
`cstrawberry/predictive-universe`, commit
`85a867988442fc423279341200f81634a1e65582`. Relevant definitions were inspected
as read-only source; no upstream executable or package was installed or run.

- [Completed Local patterns](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/Research/RootResetCompletedLocalPatterns.lean): `actionPattern`, fixed route patterns, and Local shells.
- [Appender finite rows](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/Research/RootResetAppenderFiniteRows.lean): `Spec.basePattern`, `Spec.address`, and `specsFrom`.
- [Appender route rows](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/Research/RootResetAppenderRouteRows.lean): fixed route lifting and shell addresses.
- [Selected action rows](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/Research/RootResetSelectedActionRows.lean): nonempty initial calls followed by appender rows.
- [Dispatcher stage rows](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/Research/RootResetDispatcherStageRows.lean): fixed recovered-route stages.
- [Local dispatcher probe](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/Research/RootResetLocalDispatcherProbe.lean): restoring phase/front-bit queries and finite route dispatch.

The priority, clock, restoring-probe, and spine composition follows the same
pinned dependencies documented in [the fixed controller](root-selector.md).
This is an independent Python reconstruction and empirical extension, not a
replay of the upstream Lean proof.
