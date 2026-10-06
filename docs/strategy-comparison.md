# Selector comparison on the queue fixture

Run `python -m tools.compare_strategies` to reproduce [these measurements](../results/strategy_comparison.json).

## Choices on the same recorded trajectory

At each of the 85 pre-contraction trees in the certified queue trace, apply each standard selector to that same tree and compare its address with the recorded address.

| Selector | Matching choices | First different contraction | Recorded address | Standard choice |
|---|---:|---:|---|---|
| Normal | 8 / 85 | 3 | LR | root |
| Applicative | 3 / 85 | 4 | root | LR |
| Head | 8 / 85 | 3 | LR | root |

These counts concern choices on a common sequence of input trees. Once a different contraction is chosen, an independently run trajectory has different later trees.

## Separate bounded trajectories

Starting from the same 171-node encoding, run each standard selector for up to 100 contractions and 100,001 expanded nodes. All three runs reach the step bound:

| Selector | Contractions | Final nodes | Accepted source observations |
|---|---:|---:|---|
| Normal | 100 | 26,101 | Initial `101` only |
| Applicative | 100 | 4,351 | Initial `101` only |
| Head | 100 | 26,101 | Initial `101` only |

Every native step and strategy choice in these separate runs is replayed by the independent certificate checker. The fixture's structural checkpoint reader is applied to every sampled tree.

The custom controller's address choices are therefore material to reproducing this encoding. Reconstructing its finite tests and priority passes is the next implementation target. These bounded observations leave later behavior beyond the recorded horizon unclassified.
