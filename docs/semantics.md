# Executable semantics

## Terms and native steps

A term is either `S` or `App(left, right)`. The command-line parser accepts juxtaposition, parentheses and whitespace; `S S S S` means `(((S S) S) S)`.

A redex is exactly `(((S x) y) z)`, contracted to `((x z) (y z))`. A path is a finite sequence of `0` (left) and `1` (right), starting at the root. The empty path selects the root. Paths distinguish occurrences even when the implementation shares immutable subtrees in memory.

For example, `S S S z` contracts to `S z (S z)`. The two occurrences of `z` can subsequently evolve separately. Rewriting one occurrence never mutates the other.

## Strategies

- `normal`: first redex in root-left-right preorder
- `applicative`: first redex in left-right-root postorder
- `head`: first redex along the left spine, starting at the root

The selectors are stateless functions of the current term. Their definitions are visible in `s_only/reduction.py`. The strategy interface will support additional explicit controllers as their specifications are implemented.

A head-normal term may contain reducible arguments. The run reports `normal_form` when no redex exists anywhere, and `head_normal_form` when head selection stops while an internal redex remains.

## Resource accounting

`leaves(t)` counts S occurrences in the expanded tree; `nodes(t) = 2*leaves(t)-1` includes applications. Counts are cached in immutable nodes and include every duplicated occurrence. Shared object count is a different storage measure.

For one native contraction with third argument `z`:

```text
leaves(after) - leaves(before) = leaves(z) - 1
nodes(after)  - nodes(before)  = nodes(z)  - 1
```

The runner checks the next exact node count before constructing that term. A limit is inclusive. An already oversized initial term produces `node_limit` with zero steps. After each accepted step, absence of a selected redex is checked before the step budget, so a term normalized on the last allowed step is reported accurately. If both step and next-growth limits apply, `step_limit` has precedence.

`step_limit` and `node_limit` describe finite observations. They carry no nontermination conclusion.

## Trace certificates

`schema: s-only-trace-v1` has these fields:

- `initial_prefix`, `final_prefix`: preorder strings with `A` for binary application and `S` for a leaf
- `strategy`: one of the three selector names
- `max_steps`, `max_nodes`: resource limits
- `steps`: records containing a binary path string, resulting expanded node count and SHA-256 of the resulting prefix string
- `status`: the verified reason execution stopped

Example: `S S S S` is `AAASSSS` in prefix form. Its root contraction gives `AASSASS`.

The verifier reads prefix spans and performs string-range replacements. It uses separate code for syntax validation, redex recognition, strategy selection, contraction and terminal checks. Hashes are checked after replay; they are not accepted in place of the actual rewrite.

The finite test oracle adds a third representation: nested Python tuples and the string `S`. It exhaustively constructs all 626 closed trees through eight leaves and examines every existing subtree occurrence.

A separate `s-only-path-v1` certificate contains `initial_prefix` and the same step-record format, without a selector or stopping claim. `verify_path_certificate` checks each prescribed native rewrite. It is used for reproducing a published address sequence.

## Cost model

The implementation favors transparent semantics. It retains immutable subtree sharing but traverses expanded occurrences for formatting and certificate hashing. Node limits bound a single expanded term; they do not bound cumulative trace memory or total CPU work. Path tuples may have length proportional to tree depth. The implementation is intended for bounded experiments and exact small-case replication.
