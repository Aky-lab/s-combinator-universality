# Baseline experiments

Reproduce with `python -m tools.baseline`; results are stored in `results/baseline.json` and six trace certificates in `examples/`.

## Closed constructions

Let `F = S S S`. For every closed payload `z`, one root step gives:

```text
F z -> S z (S z)
```

The third argument is copied into two distinct occurrences. Instantiating `z = S` gives a size-preserving step; instantiating `z = S S` grows from 9 to 11 total tree nodes. A second small construction is:

```text
S (S S) S S
  -> (S S) S (S S)
  -> S (S S) (S (S S))
```

These identities exercise application associativity, contextual contraction and copying. The tests also contract only one of two equal payload occurrences and check that its sibling is unchanged.

`S (S S S S)` illustrates observation scope: head selection performs zero steps, while normal selection contracts its argument once. Both outcomes have separate certificates.

The growing example `S S S (S S S) (S S S)` takes 12 checked normal-order steps, increasing from 17 to 231 expanded nodes. Its certificate records a step-limit observation.

## Bounded census

The census includes every ordered binary tree with 1–8 S leaves: 626 terms, each run under all three strategies. Each run permits 100 native steps and 10,001 expanded nodes.

| Leaves | Terms | Normal-order full normal forms | Applicative-order full normal forms | Head full normal forms | Head-only normal forms |
|---:|---:|---:|---:|---:|---:|
| 7 | 132 | 130 | 130 | 75 | 57 |
| 8 | 429 | 388 | 388 | 162 | 252 |

At seven leaves, both full-reduction strategies hit the node bound on two terms. At eight leaves, normal order has 12 node-limited and 29 step-limited runs; applicative order has 22 node-limited and 19 step-limited runs. Head reduction has six node-limited and nine step-limited runs at eight leaves.

The complete counts at every size and strategy are in the JSON result. Outcomes depend on the stated resource bounds. In particular, equal normal-form counts between the two full strategies in this census are a measured finite result.

## Verification

The independent tuple oracle checks every one-step contraction and every valid subtree occurrence through eight leaves, including rejected non-redex positions. It also compares all three selectors and bounded execution. The prefix-string checker verifies all six published trace certificates, including their stopping conditions.

The test suite additionally covers invalid syntax and paths, node-growth identities, payload occurrence isolation, deep input parsing, and certificate tampering. Run the suite against a checkout with `python -m unittest discover -s tests -v`.
