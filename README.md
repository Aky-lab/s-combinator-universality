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
- [Program-static two-phase controllers](docs/two-phase-programs.md): 20 runs across five programs and four seeds, with 1,725 native contractions and 60 checked checkpoints
- [Structural CTS reader](docs/cts-reader.md): program-parameterized decoding of current S trees, including unbalanced dispatchers and multi-bit actions
- [Compact binary-machine fixture](docs/neary-fixture.md): two write-and-halt cases compiled to a 482-phase cyclic tag system, starting from 3,374 bits and peaking at 5,187 queued bits
- [Generic initial S encoding](docs/cts-encoding.md): the compact fixture produces 1,342,619-node initial trees, represented by 27,547 shared immutable objects with reproducible prefix hashes

The native S queue run and the ordinary CTS source-machine runs have separate execution records. The generic encoder constructs the corresponding initial S syntax; the two-phase controller and the larger compact-source controller have separate integration scopes.

## Run

Python 3.10 or later; standard library only. From the repository root:

```sh
python -m unittest discover -s tests -v
python -m s_only reduce 'S (S S) S S' --certificate trace.json
python -m s_only verify trace.json
python -m tools.replicate_queue
python -m tools.root_selector_report --deterministic --output /tmp/root-selector.json
python -m tools.program_selector_report --deterministic --output /tmp/two-phase-programs.json
python -m tools.neary_fixture --output-dir /tmp/neary-left-toggle
python -m tools.inspect_cts_encoding --program artifacts/neary-left-toggle/program.json --word-file artifacts/neary-left-toggle/seed-b.txt --sha256
```

## Reducer and controller tools

- [Executable semantics](docs/semantics.md): immutable occurrence trees, normal/applicative/head strategies, resource bounds and independent trace verification
- [Baseline experiments](docs/baseline.md): exhaustive small terms and checked gadgets
- [Restoring probes](docs/probe-compiler.md): finite six-observation transition tables with a general restoring proof
- [Spine walkers](docs/spine-walkers.md): bounded descent, restoring ancestor tests and explicit reconstruction conditions
- [Fuel endpoints](docs/fuel-probe.md): seven concrete rows recovering 25 local selections in the recorded queue path
- [Exact control minimization](docs/control-minimization.md): finite quotient witnesses reduce the legacy controller to 218,111 states while preserving every primitive tick
- [Strategy comparison](docs/strategy-comparison.md): where standard selectors depart from the encoded trajectory

## Research

- [Research map](docs/research-map.md): primary literature, exact interfaces and pinned constructions
- [Controller audit](docs/controller-audit.md): finite control, root reset, readout and proof dependencies
- [Compact encoding route](docs/compact-encoding.md): direct source compilation and its size model
- [Event-composition lemma](docs/event-composition.md): transferring a distinguished CTS halt event through exact S readout
- [Generated source artifacts](artifacts/neary-left-toggle/) and [experiment reports](results/)

Current work focuses on extending the reconstructed controller to the compact source program, strengthening the source-to-S readout bridge, and independently checking the pinned formal theorem.
