# S-combinator universality

Research on computation in the S-only combinator calculus, with an exact reducer, independently checked traces, and reproducible experiments.

```text
term ::= S | (term term)
S x y z -> x z (y z)
```

Application associates to the left. Each reduction contracts one occurrence in a finite application tree.

## Run

Python 3.10 or later; standard library only. From the repository root:

```sh
python -m unittest discover -s tests -v
python -m s_only reduce 'S (S S) S S' --certificate trace.json
python -m s_only verify trace.json
python -m tools.baseline
python -m tools.replicate_queue
python -m tools.compare_strategies
python -m tools.fuel_probe_report
```

The reducer provides leftmost-outermost (`normal`), leftmost-innermost (`applicative`) and left-spine (`head`) selection. Every run has explicit step and expanded-tree-size limits. Certificates record the selected occurrence, size and SHA-256 of each resulting tree; a separate prefix-string verifier replays the native rewrites and checks the strategy and stopping condition.

## Results and research

- [Research map](docs/research-map.md): primary literature through October 2026, precise simulation interfaces and the current replication target
- [Semantics](docs/semantics.md): syntax, occurrence identity, resource accounting and certificate format
- [Baseline experiments](docs/baseline.md): closed gadgets and exhaustive bounded census
- [Two-phase queue replication](docs/queue-replication.md): 85 native contractions and all 86 checkpoint decisions independently reproduced
- [Controller interface audit](docs/controller-audit.md)
- [Restoring finite-state probes](docs/probe-compiler.md) and [fuel endpoints](docs/fuel-probe.md)
- [Selector comparison](docs/strategy-comparison.md): where standard strategies leave the encoded trajectory
- [Machine-readable census](results/baseline.json)
- [Checked example traces](examples/)

The current source audit targets the September 2026 root-restarted finite-controller construction, with its small cyclic-tag queue example reproduced and selector recovery next. The research map records the exact upstream commit, attribution and verification plan.
