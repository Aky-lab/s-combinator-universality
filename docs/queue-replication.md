# Two-phase queue replication

The two-phase cyclic-tag fixture from Cinematic Strawberry's *Pure S Is Computationally Universal Under a Fixed Root-Restarted Finite Controller* has been reproduced through all 85 native contractions with independent reducers and a structural checkpoint reader.

```sh
python -m tools.replicate_queue
```

The result is [machine-readable](../results/queue_101_replication.json). The portable [native-path certificate](../fixtures/queue_101_path.json) contains the initial 171-node tree, 85 occurrence addresses, and each resulting tree's node count and SHA-256.

## Observations

The source program has appendants `[1]` and `[]`, starting with word `101` at phase zero.

| Native contractions | CTS horizon | Phase | Queue | Expanded nodes |
|---:|---:|---:|:---|---:|
| 0 | 0 | 0 | 101 | 171 |
| 22 | 1 | 1 | 011 | 17,057 |
| 85 | 2 | 0 | 11 | 339,285 |

The structural reader rejects all 83 intermediate samples. In particular, contraction 55 has already completed a job whose queue is `11`, but its continuation still contains another job. The terminal-continuation test rejects that sample and accepts the second completion at contraction 85.

The reader receives only the current bare S tree. It follows the active queue and completed response fields, validates the fixed dispatcher branches, parses the terminal clock, and checks phase and fresh/marked status. It never invokes the source cyclic-tag transition. The experiment separately computes source configurations and compares each successful readout.

## Native occurrence checks

The input term is reconstructed directly from the mathematical abbreviations in Appendix E.1. Its prefix serialization agrees byte-for-byte with the published initial record.

Every recorded occurrence is replayed through two different native kernels:

1. Immutable application nodes with context rebuilding.
2. Flat prefix strings with independently computed subtree spans and string-range replacement.

Both kernels agree with all 85 literal target strings in the pinned upstream trace. The checked-in compact fixture preserves their digests and sizes. Reproduction checks both kernels again and compares their complete final trees.

The native-path format has no implicit reduction strategy: its address sequence is explicit input. The [independent root-reset selector](root-selector.md) now computes all those addresses from fresh roots.

## Provenance

- Upstream commit: [`85a867988442fc423279341200f81634a1e65582`](https://github.com/cstrawberry/predictive-universe/tree/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality)
- Construction and grammar: [`paper.md`, Sections 3, 4.2–4.3 and Appendix E](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/paper.md)
- Source execution record: [`067-worked-trace.log.gz`](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/evidence/formal/headline-complete/067-worked-trace.log.gz)
- [Data derivation and source hashes](../fixtures/queue_101_provenance.json)
- [Upstream MIT notice](../third_party/cinematic-strawberry-MIT.txt)

The source trace was read as data; the published upstream runtime and Lean checker were not executed for this replication. The independent implementation is in `s_only/queue_fixture.py`; native reduction remains entirely in the small S kernel.

## Scale of the full compiler

The [paper's Section 7.4](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/paper.md#section-7-4) derives a lower bound of `2^57207` literal seed bits for its padded universal encoder. The bound passes through at least 3,813 restricted-tag productions, a program-tape length at least 19,068, and a radix-eight unary block. This explains why the small queue fixture is the practical executable target.

The next engineering goals are independent selector recovery on this manageable fixture and a more compact source encoding. A fresh formal-package replay remains a separate verification task.
