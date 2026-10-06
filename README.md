# S-combinator universality

Research on computation in the S-only combinator calculus: reduction dynamics, explicit encodings, and computational universality.

## Calculus

Terms are finite binary application trees built from a single constant:

```text
term ::= S | (term term)
```

Application associates to the left. The reduction rule is:

```text
S x y z -> x z (y z)
```

A redex may occur at any position in a term. Experiments specify the reduction strategy and resource bounds so that their results can be reproduced.

## Research directions

- Implement a native S-only reducer with exact term representations and traceable reduction steps.
- Compare reduction strategies, normal forms, and term-growth behavior.
- Develop explicit encodings of data and computational processes.
- Investigate candidate constructions through small, independently checked examples.
- Record proofs, counterexamples, search procedures, and reproducible experimental results.

## Method

Constructions should state their input encoding, reduction strategy, and output interpretation. Computational searches should record their search space, pruning rules, and bounds. Tests should cover the reduction rule, substitution structure, and representative traces.

The central goal is a precise account of the computational power of the S-only calculus, supported by checkable constructions and reproducible implementations.
