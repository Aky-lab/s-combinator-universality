# Independent review of the auxiliary interface bounds

6 October 2026. **Scoped signoff:** no wrong allocation bound, hidden source
evaluation, or compressed-source representation loophole was found in
[`auxiliary-interface-bounds.md`](auxiliary-interface-bounds.md). This review
checks that document and its implementation dependencies. It does not discharge
the separate generated-controller, first-event provenance transfer, or formal
proof-replay obligations.

## Exact allocation identities

The [front-end](universal-bp2-front-end.md#55-exact-syntax-only-compiler-bounds)
counts are exact, including decrement branches, repeated successor labels,
unused registers, and a source that starts at halt:

- The initial Waterfall tuple sums to `2s+18k+1`; adding the `4k+1`
  initialization indicators gives initializer length `4s+44k+6`.
- The four nonhalt row sums for each amnesiac counter total `21N+1`.
  After diagonal compensation and guards, all nonhalt blocks therefore
  contribute `42kN+2k = 168k^2+44k` commands.
- The halt block contributes `16k+6`, and the sweep/tests/final markers
  contribute `20k+7`. Thus `L=168k^2+124k+19+4s`, with `C=8k+3` labels.

For compact UT19 encoding, `1 << (L+2).bit_length()` is the least power of two
at least `L+3`, including equality at a power-of-two boundary. There are
`2P(C+2)` transformed bits. Each zero emits two symbols and each one emits
five, followed by exactly `C+1` four-symbol separators and one leading symbol.
This independently gives

```text
q = 1 + 4(C+1) + 4P(C+2) + 3a.
```

The bound `a <= 2P(C+2)` and strict bound `P < 2(L+3)` consequently give the
document's inequalities. Each of the `log2(2P)` butterfly levels has `P`
assignments. The desired-column builder and butterfly inspect only finite
command syntax; no source transition is evaluated.

The fixed table has 40 production symbols. Its one-hot translation has
38 phases, 760 appendant bits, and 40 appendant ones. Each input symbol
contributes 19 bits and one one. Substitution into the literal occurrence-tree
formula gives `33+1216+15200+80+304q+2q = 16,529+306q`.
This is an occurrence count, not a distinct-object count.

## Representation-sensitive claim

The binary-size assertion is valid with the stated **explicit** register,
instruction, and binary-value lists. In particular, `I+J <= b` implies
`k=d+I+4J <= 5b`, and `s <= b*2^b`. A direct arithmetic check is

```text
L <= 4200b^2 + 620b + 19 + 4b*2^b
  <= (4200b^2 + 624b + 19)*2^b
  <= 8192(b+1)^2*2^b,                 b >= 1.
```

Hence `q` and the initial occurrence count are `O(b^3*2^b)`. The butterfly
adds `log P = O(b+log b)` levels, and finite indices add polynomial bit costs.
A literal, unshared implementation therefore admits the stated
`O(poly(b)*2^b)` bit-time bound. It need not rely on hash-consing or assume
constant-time arbitrary-size arithmetic.

This claim would not extend unchanged to run-length encoded register lists,
exponentiation notation for initial values, or a succinct generator for the
source program. Those representations are excluded by the document's explicit
description convention. The bound also does not assert polynomial cost in
binary source size, or any bound on simulated running time.

## Current-tree observation

The canonical target pattern count was independently recomputed as 1,750;
the extra descendant bit gives the stated `2^1751` finite state cover.
The numerical reader separately uses a fixed code allowance of 5,165, which
includes unused literal descriptors. These are different counts and are not
interchanged in the budget argument.

In the reader, every retained carrier bit comes from a node on a strictly
descending current-input path. Sharing cannot multiply output through an
unfolding: output length is at most the number `N` of distinct input nodes.
Arbitrary continuation comparisons memoize ordered node pairs, giving at most
`2N^2+1` charged pops per comparison. Repeating that comparison at most `N+1`
times explains the cubic term in `4096(N+1)^3(c+1)^2`; fixed-code comparisons,
pattern scans, complete syntax validation, and output reservation fit its
remaining factors. Arbitrary caller cap integers are covered separately by
their bit lengths, as the linked reader proof requires.

No reader step queries the source, an old sample, or an execution counter.
Identifying the decoded payload with a source output still requires the
first-event and scheduler premises already stated in the reviewed document.

## Independent executable checks

The new
[`test_auxiliary_interface_bounds_review.py`](../tests/test_auxiliary_interface_bounds_review.py)
adds five methods:

- 48 source syntax cases, including decrements and unused registers;
- ten compact UT19 lengths straddling power-of-two padding boundaries, checked
  against the quadratic subset-XOR definition rather than another butterfly;
- three constructed S trees whose occurrence counts are recomputed from edges,
  without trusting cached sizes or `encoding_stats`;
- the binary-size envelope for 67 tested bit lengths, up to 1,024;
- a fabricated, decodable event with more than `2^80` unfolded nodes but fewer
  than 10,000 distinct nodes, decoded using its current-DAG-derived budget.

All source/tag/CTS/S evaluator entry points are patched to fail during the new
compilation checks. The fabricated readout fixture is likewise decoded with
evaluators disabled; it makes no native reachability assertion.

The original two methods and these five methods passed together: **7 tests in
2.674 seconds**, using only repository code and Python's standard library:

```sh
timeout --signal=KILL 180s sh -c 'ulimit -v 1048576; python -B -m unittest discover -s tests -p "test_auxiliary_interface_bounds*.py" -v'
```

This is a focused review run, not the complete repository suite. The new review
files were created after the separately frozen 208-file checkpoint and are not
part of that checkpoint's test claim. No existing file was edited and nothing
was published by this review.
