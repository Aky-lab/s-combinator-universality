# Restoring pattern compiler

`s_only.probes` compiles finite S-tree patterns into immutable, read-only transition tables. A matcher returns a Boolean at exactly its initial occurrence, on both success and failure. An ordered row table tries restoring matchers in order, then follows the first matching row's fixed relative address.

The mathematical specification is the restoring compiler in [§5.1 of *Pure S Is Computationally Universal Under a Fixed Root-Restarted Finite Controller*](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/paper.md#section-5-1), pinned at `85a867988442fc423279341200f81634a1e65582`. The conservative pattern costs below are from its [Appendix G.1](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/paper.md#root-cost-patterns). This module is an independent standard-library implementation of those equations.

## Pattern and row syntax

```text
Pattern ::= "_" | "S" | (Pattern, Pattern)
Address ::= a finite tuple of 0 and 1
Row     ::= (Pattern, Address)
```

`HOLE = "_"` matches any subtree. `LITERAL_S = "S"` matches exactly an S leaf. A pair matches an application whose two children match its components. Wildcards are independent: repeated holes impose no equality or binding constraint.

The empty address selects the starting occurrence. A `0` descends left and a `1` descends right. Row addresses must be guaranteed by their patterns: every proper prefix of the address must identify an application node in the pattern. The selected endpoint can itself be a hole or literal S. For example, `(("_", "S"), (0,))` is valid, while `(("_", "S"), (0, 0))` is rejected because the hole need not have a child. This check ensures that the selected path exists on every tree matching the row.

Selection is relative to any invocation cursor, including an occurrence nested inside an arbitrary larger term. All mismatches restore that exact cursor before the next row starts. If all rows fail, the final answer is false there. If row `i` is the first match, the final answer is true at its address relative to that cursor. Row order therefore matters even when patterns overlap. A row establishes the existence of its selected occurrence; concrete endpoint rows must separately establish that the occurrence has the intended shape, such as a native S redex.

## Table and machine syntax

A `ProbeTable` contains only `states` and `start`. `states[q]` is an immutable six-entry tuple in this exact observation order:

```text
(S, root), (S, L), (S, R),
(application, root), (application, L), (application, R)
```

An `Instruction` is one of:

```text
Instruction("stay", q)      keep the cursor; enter q
Instruction("L", q)         descend one left edge; enter q
Instruction("R", q)         descend one right edge; enter q
Instruction("U", q)         ascend one parent edge; enter q
Instruction("true")         absorbing true answer
Instruction("false")        absorbing false answer
```

Terminal states have the same answer in all six entries. Stepping a terminal returns the same configuration unchanged. `answer(q)` returns `None` for an unfinished control and the corresponding Boolean for a terminal. Reaching a terminal takes no additional microtick: only the preceding transitions are counted.

The transition method receives only finite control, node kind and incoming side. Compilation duplicates each kind-dependent instruction across the three incoming-side entries; this still gives a total table over all six observations. The step interpreter observes node kind using the term constructor, never structural equality.

A runtime `Configuration` has exactly two fields: `control` and `cursor`. The cursor has an immutable focused term and a tuple of parent frames. Each frame contains the original immutable parent and the incoming side. These frames represent the single current occurrence. Ascending recovers the same parent object without rebuilding or modifying a term node. There is no procedure-return stack, source pattern, bound, matching counter or source-machine data in a configuration.

`Cursor.at(term, path)` prepares the starting occurrence before execution. It does not retain the supplied address as a separate register. `cursor.path` and `cursor.root` are inspection helpers for results and tests; the transition function never receives them. Only cursor movement uses parent frames. An absent edge raises `InvalidMove`, making invalid hand-written programs visible. The compiled matchers and scoped row tables never attempt an absent edge from their designated start.

Every nonterminal target is numbered below its source state. `ProbeTable` validates the six-entry shape, immutable storage, terminal uniformity, valid references and this strict ordering. Thus these tables cover finite acyclic probe fragments, with absorbing terminals. Later controllers that require loops need an appropriate separate control representation.

### Small table example

For `compile_pattern(("S", "_"))`, the complete state cover has nine states and starts at state 8. Each entry below applies to all three incoming sides for its node kind.

| State | On S | On application |
|---|---|---|
| 0 | false | false |
| 1 | true | true |
| 2 | U 1 | U 1 |
| 3 | U 0 | U 0 |
| 4 | R 2 | R 2 |
| 5 | U 4 | U 4 |
| 6 | stay 5 | stay 3 |
| 7 | L 6 | L 6 |
| 8 | stay 0 | stay 7 |

On an application with a left S leaf, the control sequence is `8, 7, 6, 5, 4, 2, 1`. The cursor walks left, up, right, up and finishes at its initial occurrence after six transitions. If the left child is an application, state 6 enters state 3, which restores the parent and answers false.

## Compilation equations

Write `N(s, a)` for a one-tick node-kind test that stays in place and enters `s` on S or `a` on an application. Write `L q`, `R q`, `U q` for one movement followed by control `q`. Let `y` and `n` be already compiled continuations.

```text
Match_[](y, n)  = y
Match_S(y, n)   = N(y, n)
Match_(A B)(y, n)
                = N(n, L Match_A(U R Match_B(U y, U n), U n))

G([])           = answer(false)
G((Q, a) :: rs)  = Match_Q(a answer(true), G(rs))
```

Here `[]` in a pattern denotes the wildcard, and `a q` is the fixed address expanded into successive L/R controls. The implementation creates continuation states first, compiles the right subpattern, then the left subpattern and enclosing test. Both child-failure exits of an application share its `U n` state. All targets therefore precede the newly emitted state.

The recursive compiler operates on the finite pattern before execution. It emits integers and immutable instructions, then discards its pattern and continuation-building data. Runtime execution calls only the table and cursor primitives.

## Restoring theorem

For every finite pattern `Q`, every finite S term, and every existing invocation cursor `c`, the fragment `Match_Q(y, n)` reaches `y` precisely when the subtree at `c` matches `Q`, and reaches `n` otherwise. In either case it reaches that continuation at exactly `c`, with the entire term unchanged. No illegal move occurs before that continuation. The continuations themselves are not executed when asserting this fragment property.

Proof by structural induction on `Q`:

1. A wildcard enters `y` immediately without moving. Every subtree matches it.
2. Literal S performs one node-kind test. It enters `y` exactly for a leaf and `n` exactly for an application, without moving.
3. For an application pattern `A B`, an S focus fails immediately at `c`. At an application focus, the test and left move reach its left child. By the induction hypothesis, the A fragment tests that child and restores its child cursor.
   - If A fails, the compiled `U n` returns one edge to `c` and enters `n`.
   - If A succeeds, `U R` returns to `c` and reaches its right child. The B fragment restores that right-child cursor by induction. Its `U y` or `U n` exit returns to `c`, with the answer determined by B.

Each downward move follows an observed application. Every upward move in this argument cancels a preceding downward move from the same parent; it does not depend on whether `c` was at the root, a left child or a right child. The parent objects and child references are immutable, so these inverse movements recover exactly the original occurrence and ambient term, including when distinct occurrences share the same subtree object.

For rows, induction over the ordered list now applies. A mismatch reaches the next row at `c`. A success reaches its address continuation at `c`; the static address check guarantees all its downward moves. No later row runs. The empty row list is the false terminal at `c`.

## Finite state and microtick bounds

Let `a(Q)`, `s(Q)` and `h(Q)` count application, literal S and wildcard nodes in a pattern. Without state deduplication, compiling one matcher emits exactly

```text
2 + 6 a(Q) + s(Q)
```

states, including its two Boolean terminals. Each application contributes five movement states and one node-kind state; each literal S contributes one node-kind state; holes contribute none. This is the size of the emitted state cover, including any unreachable states, rather than a claim about minimal or reachable-state counts.

The exact worst-case number of transitions before a standalone matcher first answers is

```text
C(_)     = 0
C(S)     = 1
C(A B)   = 5 + C(A) + C(B)
C(Q)     = 5 a(Q) + s(Q)
```

A mismatch at the application root costs one transition. A failed left test costs `3 + c_A`; a successful left test followed by either right outcome costs `5 + c_A + c_B`. Induction bounds these by `C(Q)`. Filling every hole with S gives a matching tree attaining `C(Q)`, so the bound is exact. It is independent of the sizes of wildcard subtrees and of the initial cursor depth.

The paper's conservative function, exposed by `pattern_budget`, is

```text
B(_)     = 1
B(S)     = 2
B(A B)   = 6 + B(A) + B(B)
B(Q)     = 6 a(Q) + 2 s(Q) + h(Q)
```

Every standalone pattern test takes strictly fewer than `B(Q)` transitions. In fact `B(Q) - C(Q) = a(Q) + s(Q) + h(Q) > 0`.

A finite row list `R = [(Q_i, address_i)]` emits exactly

```text
2 + sum_i (6 a(Q_i) + s(Q_i) + length(address_i))
```

states. Its execution takes at most `sum_i (C(Q_i) + length(address_i))` transitions, and hence at most the paper's forward cost `sum_i (B(Q_i) + length(address_i))`. Only one successful address is followed, so these sums are conservative. An empty row list answers immediately in zero transitions.

`table.tick_bound` computes a second, independently inspectable bound directly from the emitted acyclic table. Terminal states have bound zero. Each other state has bound one plus the largest bound among its six targets. Strictly decreasing state references make this a finite calculation in state order. For standalone matchers it equals `C(Q)`; for rows it can improve on the summed bound. Neither this calculation nor a countdown appears in `execute` or a runtime configuration. The test harness alone counts microticks to check the bound.

These counts are controller microticks. Python tuple operations used by the immutable zipper can take time proportional to cursor depth; the microtick claim is not a depth-independent Python wall-clock claim.

## API example

```python
from s_only.probes import HOLE, LITERAL_S, Cursor, compile_pattern, compile_rows, execute
from s_only.terms import parse

term = parse("S (S S)")
matcher = compile_pattern((LITERAL_S, HOLE))
result = execute(matcher, Cursor.at(term))
assert result.answer and result.cursor.path == ()

rows = compile_rows((
    ((LITERAL_S, LITERAL_S), (0,)),
    ((LITERAL_S, HOLE), (1,)),
))
selected = execute(rows, Cursor.at(term))
assert selected.answer and selected.cursor.path == (1,)
assert selected.cursor.root is term
```

For one-tick inspection, initialize `Configuration(table.start, cursor)`, call `step(table, configuration)`, and inspect `table.answer(configuration.control)`. `execute` performs this loop without counters or source-pattern access.

## Independent finite checks

Run the dedicated suite from the repository root:

```sh
python -m unittest discover -s tests -p test_probes.py -v
```

The expected answers come from a separate recursive matcher over built-in tuples, with `None` as its wildcard. It does not call the production compiler, table interpreter, parser or reduction helpers to calculate an expected answer.

The exhaustive corpus contains all 626 closed ordered S trees with one through eight leaves, comprising 8,788 occurrences. Tests cover:

- All 102 wildcard/S patterns with at most four leaves against all 626 tree roots: 63,852 matcher invocations.
- All 22 patterns with at most three leaves at every occurrence of all 626 trees: 193,336 matcher invocations, checking exact restoration of the original focus and parent frames.
- Four ordered row lists at every occurrence: 35,152 selection invocations, including no-match, priority overlap and fallback cases.
- Attainment of each standalone exact bound on a matching tree; static state counts, backward references, all six local observations, total tables and absorbing terminals.
- Late right-child failures, shared-subtree occurrence identity, invalid pattern/address/table rejection and immutable terms, tables and cursors.
- Execution at depth 2,000 while term equality, source-pattern compilation and term formatting are disabled.

The dedicated suite has 18 passing tests. Its exhaustive cases check 292,340 probe invocations, in addition to the focused boundary and stress cases. The induction above establishes the restoring property for arbitrary finite inputs; the finite corpus independently checks the implementation and its accounting.
