# Bounds for the fixed encoding and observation interfaces

The encoder constructs finite syntax from a machine description and its input.
Its allocation and loop bounds are determined before the simulated machine
runs. The event detector and result decoder inspect only the current S tree.
This section makes those bounds explicit for the fixed 38-phase route.

## 1. Source syntax to the initial S tree

Use the finite register-machine interface in
[the front-end theorem](universal-bp2-front-end.md). Write `d` for its register
count, `I,J` for its increment/decrement instruction counts, and `s` for the sum
of its initial register values. Let

```text
k = d + I + 4J
C = 8k+3
L = 168k^2 + 124k + 19 + 4s.
```

The compiled BP2 program has exactly `C` labels and `L` commands. Its
construction consists of finite transition tables and guarded literal blocks;
all loops are bounded by these syntax and input quantities.

Let `P` be the least power of two at least `L+3`. Thus
`L+3 <= P < 2(L+3)`. The compact UT19 encoder constructs `C+2` memory vectors,
each of width `2P`. If `a` is the number of 1s in their transformed vectors,
the initial tag queue has exactly

```text
q = 1 + 4(C+1) + 4P(C+2) + 3a
0 <= a <= 2P(C+2).
```

Consequently

```text
q <= 1 + 4(C+1) + 10P(C+2)
  <  1 + 4(C+1) + 20(L+3)(C+2).
```

Each vector is computed by the fixed subset-XOR butterfly: for width `2P`,
there are exactly `P log2(2P)` XOR assignments. Vector construction, queue
materialization, and the 19-bit one-hot translation are linear in their
respective output lengths. The butterfly never evaluates BP2 instructions.
This gives `O((C+2)P log(P+1))` Boolean/index operations, plus source compilation
and the ordinary bit costs of finite indices.

Every one-hot symbol has 19 bits and exactly one 1. The fixed CTS program has
38 appendants, 760 total appendant bits, and 40 appendant ones. Substituting
`n=19q,u=q` into the [literal S-size formula](cts-encoding.md#exact-unfolded-size)
gives the exact **unfolded** initial occurrence-tree size

```text
|T0| = 33 + 32*38 + 20*760 + 2*40 + 16*(19q) + 2q
     = 16,529 + 306q.
```

Thus the initial tree size is polynomial in the unary input values and machine
syntax. A literal unshared encoder can write this many nodes directly; the
implementation's immutable sharing is an optional storage optimization.
It does not alter the mathematical tree or reduction rule.

### Binary input length

For an explicit bit-size estimate, choose a conventional complete description
length `b >= 1` that dominates the number of registers, number of instructions,
and total binary input length. Lists of register values and instructions are
explicit; numeric register identifiers may be renumbered densely from that
finite list before compilation. Then

```text
k <= 5b,     C <= 40b+3,     s <= b*2^b,
L <= 8192(b+1)^2*2^b.
```

The displayed constant is conservative. In particular `P`, `q`, and `|T0|`
are all `O(poly(b) * 2^b)`, and the specified compiler admits a singly
exponential bit-time bound of the same form. Unary expansion of binary input
values explains the exponential factor. All bounds depend on the finite input
representation, never on whether the source halts or how long it runs.

## 2. Fixed regular event detector

The target event is descendant occurrence of the completed fresh Local pattern
with label `(17,1)` and route `0100011`. Its linear holes are independent. The
[bottom-up automaton](pattern-automaton.md) uses one bit for each of its 1,750
canonical subpatterns and one descendant-acceptance bit. Its finite state cover
therefore has `2^1751` states, with fixed Boolean leaf/application transitions.

For an occurrence tree of `m` nodes, bottom-up evaluation takes `O(m)` fixed-size
state transitions. For an acyclic shared representation with `N` distinct nodes,
`N <= m`, the same value can be computed once per node. Syntax validation and
first-preorder witness selection are bounded graph traversals. Neither
acceptance nor witness choice uses a source program, a time counter, or a
previous observation.

## 3. Current-tree output decoding

At the first accepting sample, the [frozen-audit theorem](local-event-provenance.md)
identifies the creation-time post-deletion carrier at address `LLLR` inside the
selected event occurrence. The [bounded reader](s-event-readout.md) checks that
carrier grammar, restores the deleted 1, and reads the phase-17 UT19 result.
Its sufficient charged-work budget is

```text
W(N,c) = 4096(N+1)^3(c+1)^2,
```

where `c` is a fixed code allowance. All reachable S syntax is validated,
including ignored audit fields. Arbitrary continuation equality is checked by
memoized pairs of current-input nodes. The parser's successful recursive
premises become strict-descendant iterations, bounding output length by `N`.

Taking the actual node count, or a polynomial upper bound, for the derived
limits gives polynomial bit-time and storage in current input size. For the
parameterized API, arbitrary cap integers add their own bit-length to that
bound, as detailed in the reader proof. Refusal under a smaller practical cap
has no source-halting interpretation.

The source-machine output is the fixed arithmetic map `(x_1-3)/2` applied to
the first decoded BP2 counter. At a compiled halt this is a natural integer;
the front-end theorem gives `x_1=2n+3`. This final map is linear in the number
of output bits, and its coordinate and formula are independent of the source.

## 4. The remaining controller obligation

These encoder/observer bounds do not depend on a source simulation theorem.
Their **semantic composition** does: the fixed controller must follow the
registered generated stages, cover source steps in the required order, and
preserve the first event's frozen audit at all native intermediate samples.
Its every-input root-reset termination theorem is a separate fixed-interface
obligation, recorded in [the proof roadmap](proof-dependencies.md).

For the mathematical theorem one may use the exact pinned generic CTS encoder
and finite controller definitions. A correspondence theorem for a separately
written Python port is then a reproduction obligation rather than part of the
mathematical universality statement. The chosen formal construction and the
new event/readout lemmas still require their own exact proof checks.
