# Finite descending and ascending spine walkers

`s_only.walkers` closes a finite restoring edge probe into a read-only loop. It supplies three compilers:

- `compile_descent(rows)` repeatedly selects the first matching row and follows its strict-child address. It stops at the first occurrence where no row matches.
- `compile_inverse_rows(rows)` performs one prioritized ancestor-candidate test. A success ends at the candidate ancestor; a failure restores its exact starting occurrence.
- `compile_ascent(rows)` repeats those ancestor-candidate tests until all candidates fail.

These are finite-controller components for root-reset carrier queries. They do not themselves select native S reductions, establish a universal machine simulation, or reconstruct an arbitrary descent path without additional hypotheses.

## Mathematical source and implementation scope

The source specification is the work in `cstrawberry/predictive-universe`, pinned at commit `85a867988442fc423279341200f81634a1e65582`:

- [RootResetEdgeSpine.lean](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/Research/RootResetEdgeSpine.lean): feedback after a successful edge fragment, strict-subterm termination, and a linear microtick bound.
- [RootResetInverseEdgeFragment.lean](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/Research/RootResetInverseEdgeFragment.lean): incoming-side tests, ascent to a matching ancestor, and exact failure return.
- [RootResetInverseEdgeSpine.lean](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/Research/RootResetInverseEdgeSpine.lean): prioritized ancestor families and termination by decreasing parent depth.

This is an independent standard-library Python implementation, built on the project's [restoring probe compiler](probe-compiler.md). The linked source was read as mathematical specification; no upstream code was executed or installed. These tests do not constitute a checked Lean proof of the Python implementation.

There are two deliberate implementation differences. First, all three public compilers require each child address to be guaranteed by its pattern, as in the existing forward compiler. The backward fragment could safely support arbitrary fixed addresses because it observes actual incoming sides, but this API keeps the common scoped-row contract. Second, upstream inverse feedback passes through a marker and a restart, costing two microticks. This table has a single explicit feedback transition and therefore uses one microtick. The table-derived coefficient below accounts for the actual implementation.

## Rows and endpoints

A row is `(pattern, address)`, with the same wildcard/S/application pattern syntax as `s_only.probes`. Addresses are immutable tuples of `0` and `1`, for left and right. Every proper prefix of the address must identify an application in the pattern. All addresses must also be nonempty, including unreachable or shadowed rows. Empty-address feedback is rejected at compilation: a successful test at the same occurrence would provide no decreasing measure.

An empty family is valid and immediately answers false at its invocation cursor. Both looping walkers always finish at a false terminal. Here false means that the next edge/candidate search missed; it does not mean that the entire walk made no progress. The result's cursor is the endpoint. The single-step inverse returns true on success and false on failure.

An invocation can start at any existing occurrence in an ambient finite S tree. The tree is never changed. Shared Python subtree objects still represent distinct occurrences when their zipper parent paths differ.

## Tables and runtime boundary

`WalkerTable` is separate from `ProbeTable`. The latter retains its existing immutable, acyclic, strictly backward-numbered contract.

A `WalkerTable` has exactly three fields:

```text
states    immutable tuple of immutable six-instruction rows
start     a finite control index
feedback  a finite control index
```

Its six observations are exactly the existing `(node kind, incoming side)` combinations: S or application, paired with root, L or R. Commands are the existing stay, L, R, U and absorbing Boolean terminals. Every state except `feedback` has only backward-numbered nonterminal targets. The feedback row must contain six copies of `stay start`. Entry cannot equal feedback. Cutting this one feedback edge therefore leaves an acyclic finite fragment, and the table can compute its longest pass independently of the input tree.

The validator checks table immutability, reference validity, terminal uniformity and the designated-feedback structure. It does not prove that a hand-written table makes cursor progress or that its moves are legal. Those properties are established below for the compiled tables from their designated start states. In particular, allowing one feedback edge is not a claim that every hand-written loop of that shape terminates.

Runtime `Configuration` remains exactly `(control, cursor)`. The occurrence zipper remains exactly `(focus, parents)`. `transition` receives only finite control, node kind and incoming side. `step` executes one command. `execute` repeatedly steps until an absorbing answer is reached. It performs no pattern recursion, source matching, address traversal loop, arithmetic countdown, whole-term equality, serialization, or tree-size/depth query. Fixed paths and failure continuations are compiled into finite states. There is no second zipper, saved invocation cursor, dynamic procedure stack, or walk-history register.

Cursor movement uses the existing immutable term objects. `cursor.path` and `cursor.root` are result-inspection helpers, not observations supplied to the controller. Compiled terms and tables contain no runtime pattern values.

## Descending walk theorem

Let `F(c)` be undefined when no row pattern matches the subtree at occurrence `c`. Otherwise, choose the first matching row `(Q, a)` and let `F(c)` be the occurrence obtained by following `a` from `c`.

For each invocation, the restoring prioritized probe either:

1. misses at its exact invocation occurrence and enters the false terminal; or
2. reaches the selected strict descendant and then takes the one-tick feedback transition to the same finite entry state.

The first case follows from the restoring matcher theorem. In the second case, the pattern scope check guarantees that the address exists, and its nonemptiness makes its endpoint a proper subterm. Thus each successful whole pass strictly decreases the focused occurrence-tree node count. Intermediate matching movements need not decrease it; the measure is asserted at complete-pass boundaries.

Strong induction on focused node count proves termination for every finite input, including trees that do not represent a well-formed carrier. The resulting endpoint is exactly the first miss in the unique sequence `c, F(c), F(F(c)), ...`. Every microtick preserves the ambient term.

## A single inverse step and exact restoration

For row `(Q, a)` and invocation occurrence `c`, a candidate exists exactly when:

- the invocation path ends in the full fixed address `a`; and
- the subtree at the ancestor obtained by removing that suffix matches `Q`.

This definition uses paths only in the mathematical specification and independent test oracle. Execution instead checks the directions of `a` in reverse order using incoming-side observations. A matching side triggers U. A mismatching side, including root, follows a compiled restoration continuation. After all sides match, the already compiled restoring Q probe tests the candidate ancestor. Its success exits there; its failure follows the fixed downward path back to the original occurrence.

After `j` successful upward movements, the compiler has a finite failure continuation that descends through the last `j` directions of `a` in forward order. It contains exactly `j` downward commands. Each such edge is known to exist because the read-only machine just crossed it upward. Induction on the number of checked directions shows:

- a side mismatch restores all earlier upward movements;
- a pattern mismatch first restores the candidate cursor, then restores all upward movements;
- a success ends at the matching ancestor, whose forward address `a` returns to the original occurrence.

Restoration means the identical focused term object, ambient term object, occurrence path and ordered parent-object/side pairs. It does not promise the Python object identity of each small `_Frame` wrapper: U removes wrappers and a subsequent descent recreates them. No subtree is rebuilt, and no extra record of removed frames is retained. This is exact equality of the represented occurrence zipper, rather than an implementation-level allocation promise.

`compile_inverse_rows` tries these row fragments in order. Every failure returns before the next row begins; the first success wins. Thus failure of the whole family restores the invocation, including after late pattern mismatches.

## Ascending walk theorem and limits of inversion

Let `B(c)` be the ancestor chosen by the first successful inverse row, or undefined when all rows fail. Each successful row removes exactly `len(address)` parent frames. Nonempty addresses therefore imply strict depth decrease at whole-pass boundaries. Induction on the initial parent depth proves that `compile_ascent` terminates at the first undefined B, preserving the ambient term throughout.

This theorem needs no uniqueness premise: B is a deterministic, terminating ancestor-candidate function for every accepted family. Calling it an inverse of prioritized F would require more.

For a specific descent trajectory

```text
c0 -> c1 -> ... -> ck
```

a sufficient reconstruction premise is:

1. For each `j > 0`, every matching inverse row candidate at `cj` names the same ancestor `c(j-1)`. At least one exists, namely the forward row used at `c(j-1)`.
2. No inverse row candidate exists at `c0`.

Under these premises, inverse ascent follows precisely `ck, ..., c1, c0` and stops. A weaker exact premise is simply that the first matching inverse candidate at each `cj` is `c(j-1)`, together with the same boundary condition. These are properties of the rows and trajectory, not runtime checks or silently inferred invariants. Root-started descent automatically satisfies the second premise.

A useful static sufficient condition for candidate uniqueness is that the distinct addresses are suffix-free: no address is a proper suffix of another. Addresses of one common positive length are a special case. If two addresses both end the same occurrence path, one is a suffix of the other. Under this condition they must be equal and identify the same ancestor. Consequently, a root-started descent with a suffix-free address family round-trips through ascent. Duplicate rows with the same address do not affect this argument. A nested start still needs its own inverse boundary.

Three small tested counterexamples make the restrictions concrete:

- With rows `((_, _), L)` then `((_, _), R)`, inverse recognition at the right child of `(S S)` returns the root, although forward priority at that root selects the left child. A successful inverse candidate is not necessarily a selected forward edge.
- With rows `((S, _), R)` then `(((_, _), _), LR)`, descent from `((S S) S)` uses the second row and reaches LR. Inverse priority recognizes `(S S)` at L using the first row and stops there. The root-to-endpoint descent does not round-trip.
- With the single row `((_, _), R)`, starting descent at R inside `(S (S S))` reaches RR. Inverse ascent reaches the ambient root, passing the original nested start. The zipper carries no invocation-boundary marker.

To prove that B is a genuine inverse on an entire claimed carrier domain, one must additionally establish forward coherence: for every accepted candidate pair `(ancestor, origin)` in that domain, the first forward row selected at the ancestor points to that origin. Candidate uniqueness, forward coherence, and the intended top boundary are separate obligations.

## State counts and fixed microtick bounds

Let `A(Q)` and `S(Q)` count the application and literal S nodes in a pattern. The existing restoring compiler's exact worst-case pattern cost is

```text
C(Q) = 5 A(Q) + S(Q).
```

For rows `(Qi, ai)`, the emitted state-cover sizes, including two exit slots and any unreachable states, are:

```text
descent:       2 + sum_i (6 A(Qi) + S(Qi) + len(ai))
inverse/ascent: 2 + sum_i (6 A(Qi) + S(Qi) + 3 len(ai))
```

Each inverse address direction contributes an incoming test, an upward move, and a possible downward restoration move. A single inverse row costs at most `C(Q) + 3 len(a)` microticks. Success uses two ticks per ascended edge plus matching; failure may also restore each edge. A partial side mismatch after `j < len(a)` successful ascents costs `3j + 1`, which is within the same bound. Hence a complete family pass is bounded by

```text
P_down <= sum_i (C(Qi) + len(ai))
P_up   <= sum_i (C(Qi) + 3 len(ai)).
```

`WalkerTable.pass_bound` computes a possibly tighter bound directly from the immutable table: terminals and the cut feedback state get zero, and every other state gets one plus the maximum bound among its six targets. `coefficient = pass_bound + 1` includes the feedback transition. These calculations occur outside the interpreter; no bound becomes a runtime register.

For `N` nodes in the initial focused tree, descending execution takes at most

```text
coefficient * N
```

microticks. A strictly decreasing positive size permits at most `N - 1` successful passes, followed by one miss; each successful pass costs at most the coefficient and the miss costs no more. Strong induction gives the same bound without storing the number of passes.

For initial cursor depth `d`, ascending execution takes at most

```text
coefficient * (d + 1)
```

microticks. There are at most `d` successful strictly ascending passes, followed by one miss. Since `d + 1` is at most the ambient occurrence-tree node count, this is also a fixed coefficient times ambient tree size. The focused subtree size alone cannot bound ascent from a deeply nested leaf.

These are abstract controller microticks. Python tuple creation and slicing in the immutable zipper can take time proportional to cursor depth. The bounds do not assert constant wall-clock cost per Python step.

## API example

```python
from s_only.probes import HOLE, Configuration, Cursor
from s_only.terms import parse
from s_only.walkers import compile_descent, compile_ascent, execute, step

rows = (((HOLE, HOLE), (1,)),)
root = Cursor.at(parse("S (S (S S))"))
descending = compile_descent(rows)
ascending = compile_ascent(rows)

bottom = execute(descending, root)
assert bottom.answer is False
assert bottom.cursor.path == (1, 1, 1)
restored = execute(ascending, bottom.cursor)
assert restored.cursor.path == ()
assert restored.cursor.focus is root.focus

configuration = Configuration(descending.start, root)
configuration = step(descending, configuration)  # exactly one microtick
```

The example's single fixed-length address family and root start satisfy the reconstruction premises. `compile_inverse_rows` provides a separate acyclic one-pass table when only one ancestor step is wanted.

## Independent tests

```sh
python -m unittest discover -s tests -p test_walkers.py -v
```

The independent oracle uses built-in tuples, recursive structural pattern matching, and explicit occurrence paths. It does not use production matchers, cursor movement, compilers, parser or reduction logic to determine expected outcomes.

The exhaustive corpus comprises all 626 ordered closed S trees with one through eight leaves and all 8,788 occurrence starts. Six row families are checked for descent, one inverse step and repeated ascent at every start: 158,184 instrumented invocations. Every invocation checks its independent endpoint and a static-coefficient microtick bound. Further tests cover:

- Failed incoming tests after each available reversed-address prefix, root boundaries, and late ancestor-pattern failures with exact restoration before fallback.
- Single-row forward/inverse correspondence and root-started reconstruction for common-length and unequal-length suffix-free address families.
- All three reconstruction counterexamples above.
- Immutable tables, all six observation entries, finite references, the one designated feedback state, absorbing terminals, invalid inputs and rejection of empty feedback addresses.
- Exact emitted state counts and conservative symbolic bounds.
- Shared subtree objects at distinct occurrences and term preservation through every microtick of representative loops.
- A 2,000-edge spine, with runtime term equality, pattern compilation, serialization and path/root inspection disabled. The single right-edge family takes exactly 14,001 descending and 16,001 ascending microticks.

The dedicated suite contains 16 tests. The induction arguments give the unbounded finite-input specifications; the exhaustive and stress cases independently check this implementation and its resource accounting.
