# S-combinator universality

Exact S-only rewriting, replicated encoded computations, and finite-controller tools.

```text
term ::= S | (term term)
S x y z -> x z (y z)
```

Application associates to the left. A native step contracts one occurrence in a finite application tree.

## Reproduced computations

- [S-only queue computation](docs/queue-replication.md): `101 → 011 → 11` across 85 native contractions, with all 86 structural readout decisions checked independently
- [Independent root-reset controller](docs/root-selector.md): all 85 addresses selected from current trees by a fixed 257,299-state graph
- [Interval-coded controller](docs/succinct-selector.md): the identical graph represented by 370 intervals, with every transition and the full 85-step microtick trace checked
- [Program-static two-phase controllers](docs/two-phase-programs.md): 20 runs across five programs and four seeds, with 1,725 native contractions and 60 checked checkpoints
- [Positive-period controllers](docs/periodic-controllers.md): periods 1, 3, 4 and 5, with 1,150 native contractions and 36 checked checkpoints across 12 runs
- [Succinct positive-period controllers](docs/succinct-periodic.md): the same indexed graphs through period five, with 24,960,102 entries and 317 native contractions independently compared
- [Structural CTS reader](docs/cts-reader.md): program-parameterized decoding of current S trees, including unbalanced dispatchers and multi-bit actions
- [Read-only marker observer](docs/marker-observer.md): 404 native samples checked, with 12 prospective halt-field signals and separately recorded checkpoint times
- [Compact binary-machine fixture](docs/neary-fixture.md): two write-and-halt cases compiled to a 482-phase cyclic tag system, starting from 3,374 bits and peaking at 5,187 queued bits
- [Compact UT19 source compiler](docs/ut19-fixtures.md): a fixed 38-phase CTS, checked halting and nonhalting fixtures, and structural result recovery from 1,710–2,736-bit seeds
- [Generic initial S encoding](docs/cts-encoding.md): the compact fixture produces 1,342,619-node initial trees, represented by 27,547 shared immutable objects with reproducible prefix hashes

Native S trajectories and ordinary CTS source-machine runs have separate
execution records. The larger compact-source fixture currently records its
ordinary CTS computation and corresponding initial S encoding.

## Run

Python 3.10 or later; standard library only. From the repository root:

```sh
python -m unittest discover -s tests -v
python -m s_only reduce 'S (S S) S S' --certificate trace.json
python -m s_only verify trace.json
python -m tools.replicate_queue
python -m tools.root_selector_report --deterministic --output /tmp/root-selector.json
python -m tools.succinct_selector_report --deterministic --output /tmp/succinct-selector.json
python -m tools.succinct_periodic_report --deterministic --output /tmp/succinct-periodic.json
python -m tools.program_selector_report --deterministic --output /tmp/two-phase-programs.json
python -m tools.periodic_selector_report --deterministic --output /tmp/positive-period-programs.json
python -m tools.marker_observer_report --deterministic --output /tmp/marker-observer.json
python -m tools.ut19_source_report --output /tmp/ut19-source.json
python -m tools.neary_fixture --output-dir /tmp/neary-left-toggle
python -m tools.inspect_cts_encoding --program artifacts/neary-left-toggle/program.json --word-file artifacts/neary-left-toggle/seed-b.txt --sha256
```

The positive-period tests construct a 2.1-million-state graph. The
[reproduction commands](docs/periodic-controllers.md#independent-bounded-checks)
include explicit process and memory limits.

## Reducer and controller tools

- [Executable semantics](docs/semantics.md): immutable occurrence trees, normal/applicative/head strategies, resource bounds and independent trace verification
- [Baseline experiments](docs/baseline.md): exhaustive small terms and checked gadgets
- [General appender lemma](docs/appender-gadget.md): an exact `2m`-contraction derivation with arbitrary closed parameters and retained-history order
- [Restoring probes](docs/probe-compiler.md): finite six-observation transition tables with a general restoring proof
- [Succinct probe tables](docs/succinct-probes.md): exact indexed transition lookup from compact immutable code, including 4,097 descriptors for `7·2^4096−4` virtual states
- [Succinct prioritized rows](docs/succinct-rows.md) and [spine walkers](docs/succinct-walkers.md): index-preserving composition, restoration and feedback
- [Compile-only code sharing](docs/pooled-selector.md): equal immutable controller values share storage while preserving every indexed primitive transition
- [Spine walkers](docs/spine-walkers.md): bounded descent, restoring ancestor tests and explicit reconstruction conditions
- [Fuel endpoints](docs/fuel-probe.md): seven concrete rows recovering 25 local selections in the recorded queue path
- [Exact control minimization](docs/control-minimization.md): finite quotient witnesses reduce the legacy controller to 218,111 states while preserving every primitive tick
- [Strategy comparison](docs/strategy-comparison.md): where standard selectors depart from the encoded trajectory

## Research

- [Research map](docs/research-map.md): primary literature, exact interfaces and pinned constructions
- [Controller audit](docs/controller-audit.md): finite control, root reset, readout and proof dependencies
- [Compact encoding route](docs/compact-encoding.md): direct source compilation and its size model
- [Static compiler cost](docs/compilation-cost.md): an exact 571,594,401,546-state component count identifies the compact fixture's literal-inlining bottleneck
- [Event-composition lemma](docs/event-composition.md): transferring a distinguished CTS halt event through exact S readout
- [Compact source simulation proof](docs/ut19-simulation-invariants.md): running-XOR memory, counter restarts, first-event equivalence, and preserved output tuples
- [Structural UT19 result reader](docs/ut19-readout.md): current-state Reset grammar and the exact 17-bit CTS event offset
- [Generated source artifacts](artifacts/neary-left-toggle/) and [experiment reports](results/)

Current work focuses on compact representations of the finite controller,
the source-to-S readout bridge, and independent checking of the pinned formal theorem.
