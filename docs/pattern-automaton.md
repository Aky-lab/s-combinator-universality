# A finite bottom-up automaton for descendant pattern occurrence

This module independently implements and proves a regular **syntax language**.
It is not yet a UT19 trajectory halt observer. In particular, accepting a
fabricated tree is intentional: the language has no source computation,
reachability, clock comparison, carrier validity, or history premise.

Implementation: [`s_only/pattern_automaton.py`](../s_only/pattern_automaton.py).
The separate Python evaluator is input-bounded and uses a stack and identity
memo. It is **not** the single-zipper native reduction controller. No existing
reduction controller or observer is changed.

## Syntax and immutable compiled code

An input term is a finite closed tree over `S` and binary `App`. Patterns are
`probes.HOLE` (`"_"`), `probes.LITERAL_S` (`"S"`), or exact two-element tuples
of patterns. Every hole occurrence is an independent wildcard. Reusing the
same hole string or pair object imposes no equality between matched payloads.
Nonlinear patterns with repeated named variables are outside this syntax.

For a fixed pattern `P`, let `K` be its distinct structural subpatterns. The
compiler assigns `K` consecutive IDs in child-before-parent order. Leaves are
interned by their two plain-string kinds; pairs are interned by the shallow
key `("pair", left_id, right_id)`. The input tuples themselves are never
hashed, compared recursively, copied into occurrence trees, or retained in
the finished automaton. Identity maps traverse the input DAG, so shared
subtrees are compiled once. Equal but separately allocated tuples receive the
same structural ID.

Canonicalization correctness follows by induction on descriptor height.
Equal atoms have equal IDs. At a pair, equal child patterns have equal IDs by
induction, so equal pairs have equal shallow keys and equal IDs. Conversely,
an equal pair ID has the same two child IDs, which describe equal patterns by
induction. Atom and pair keys are disjoint. Thus the final descriptors name
exactly `K`, and `k = len(automaton.nodes) = |K|`.

The frozen descriptor tuple contains only kinds and bounded child indices;
the root is its last descriptor. Construction validates exact field types,
strictly preceding child indices, uniqueness and root reachability. Every
descriptor is therefore genuinely a subpattern, with no cycles or unused
extra code. No claim of state minimization is made.

## States and transitions

The state space is the full finite cube `Q = {0, ..., 2^(k+1)-1}`. Bit `i < k`
states that descriptor `i` matches the current subtree root. Bit `k` is
`found`, saying that the full pattern occurs at some descendant, including
the root. Some cube states need not be reachable; the transition is defined
on all of them. The cover is not materialized. `state_count_bound` constructs
only the integer `2^(k+1)`, not that many objects or table entries.

At an `S` node:

- Set exactly the existing hole and literal-S match bits.
- Set `found` if the full-pattern bit is set.

At an application with child states `l` and `r`:

- Set an existing hole bit, and clear a literal-S bit.
- For descriptor `(a,b)`, set its match bit exactly when bit `a` is set in
  `l` and bit `b` is set in `r`.
- Set `found` exactly when the full-pattern match bit, `l.found`, or
  `r.found` is set.

Accept exactly the states with `found` set. `matches_root` separately reads
the full-pattern bit, so a positive descendant and a positive root are not
confused.

`transition(kind, left=None, right=None)` receives only the local node kind,
zero or two bounded integer states, and the fixed immutable code. It has no
term, occurrence address, source program, history, external input, persistent
cache, or input-sized control register. Its loop over the fixed `k` descriptors
is program-static. It does not call the compiler, evaluator, clock, filesystem,
term methods, or a reduction routine.

## Semantic proof

Define matching in the usual way: a hole matches every tree; literal S
matches only S; `(p,q)` matches `App(x,y)` exactly when `p` matches `x` and
`q` matches `y`. Let `W_P(T)` mean that `P` matches some subtree occurrence
of `T`, including its root.

For every finite closed S tree `T`, the state computed bottom-up satisfies:

1. For every `i < k`, bit `i` is set iff subpattern `i` matches `T` at its root.
2. Bit `k` is set iff `W_P(T)`.

Proof by structural induction on `T`:

- **Base `T = S`.** Precisely the hole and literal-S subpatterns match the
  root, as set by the leaf transition. Its sole subtree occurrence is itself,
  so setting `found` from the full-pattern bit proves both assertions.
- **Step `T = App(x,y)`.** By induction the children's bits correctly identify
  every subpattern root match. Holes match, literals do not, and each pair
  matches exactly when its two child bits are set. This is the application
  transition, proving assertion 1. Every subtree occurrence is either the
  root, a descendant in `x`, or a descendant in `y`. The disjunction of those
  three witnesses is exactly the computed `found` bit, proving assertion 2.

Consequently `automaton.accepts(evaluate(automaton, T))` agrees with `W_P(T)`
whenever evaluation completes. Every finite tree has this mathematical
bottom-up run irrespective of whether chosen implementation budgets suffice.
Exhausting a budget raises `ResourceLimit`; it is never language rejection.

For a shared acyclic term DAG, unfold it conceptually to its occurrence tree.
Every occurrence of one DAG object has identical subtree structure and hence
the same bottom-up state by the theorem. Computing that state once and reusing
it at several parent edges is therefore sound. The existential descendant bit
needs no multiplicity count. No actual unfolding is required. An identity
memo would not be sound for an occurrence-dependent or history-dependent
predicate; this construction has neither dependency.

## Exact structural bounds and resource discipline

Let `p` be the number of distinct input pair objects, `a <= 2` the number of
atom kinds present, and `k` the number of canonical descriptors.

- Compilation checks at most `p+a` distinct pattern nodes and emits exactly
  `k <= p+a` descriptors. Each pair is expanded once and schedules exactly
  three stack entries (its exit and two children). The traversal therefore
  processes exactly `1+3p` stack entries on valid input. This count is about
  the shared representation, not the unfolded occurrence count.
- The compiler's explicit stack has at most `1+2p` entries. Identity maps,
  active set, canonical interning map and output are bounded by `p+a` entries
  each. Validation scans `k` descriptors; its root-reachability traversal has
  exactly `1+2b` pops, where `b` is the number of canonical pair descriptors.
- Each transition scans exactly `k` descriptors, tests at most two child bits
  for each pair, sets at most `k` match bits, then computes one descendant bit.
  It terminates independently of the input tree. State values and intermediate
  bit vectors have at most `k+1` bits; child indices are less than `k`. The
  cover-count integer alone has `k+2` bits.
- Python big-integer operations are not claimed to be unit cost. A safe
  bit-operation upper bound is `O(k^2)` per transition, with `O(k)` temporary
  bits. The descriptor code has `O(k log(k+1))` bits plus representation
  overhead. Hash-map bounds use ordinary expected dictionary costs rather
  than asserting worst-case constant-time hashing.
- Let an accepted term DAG have `d` distinct nodes and `t` distinct App nodes.
  Evaluation performs exactly `d` transitions and exactly `1+3t` stack pops.
  Its stack has at most `1+2t` entries, with at most `d` memo states and `t`
  active IDs. The memo holds at most `d(k+1)` state bits, in addition to input
  references, IDs, Python container overhead and the fixed code. Evaluation
  is thus input-bounded rather than finite-working-memory Python execution.

`compile_pattern` has inclusive `max_descriptors` (default 100,000) and
`max_pattern_nodes` (200,000) caps. `evaluate` has an inclusive
`max_term_nodes` cap (1,000,000 distinct objects). Both have `max_seconds`
(default 10), checked cooperatively at traversal boundaries and before
return. Compilation also checks before and after metadata validation.
One transition or metadata validation can run past the soft time cap before
the next check. These are not asynchronous CPU/memory guards; the commands
below impose an additional 180-second/1-GiB process boundary. No exponential
occurrence-size integer is used by the generic evaluator.

Malformed syntax and states raise `ValueError`. Exact built-in types are
checked **before** equality, hashing, arithmetic, indexing, or ordering can
invoke user-supplied hooks: subclasses of int/str/tuple/App are rejected.
Checks use identity against type objects, avoiding hostile metaclass equality.
Boolean states are rejected despite Python's bool/int relationship. S requires
no child states; application requires two in-range states. Inconsistent but
well-typed cube vectors are legal states, as required for a total transition.
Every reachable term node is checked even after a positive match; malformed
descendants cannot be hidden by short-circuit acceptance. Cyclic term objects
are rejected. As with the repository's immutable-term model, concurrent
out-of-band mutation via `object.__setattr__` is not an admissible input model.

## Bounded UT19 instance: what was checked

[`tools/ut19_event_language_report.py`](../tools/ut19_event_language_report.py)
reconstructs precisely the candidate in
[`ut19-s-event-audit.md`](ut19-s-event-audit.md):

- fixed 38-phase UT19 CTS, `required_period=None`;
- the **label** `(17,1)` at structural route `0100011`;
- `PI _` followed by exactly 19 independent history holes;
- seven chosen-route wrappers with literal dormant sibling calls;
- the fresh Local shell `(((HALT _) D17) ((S _) _)) (_ _)`.

An independent iterative pattern comparison checks this reconstruction
against the unique chosen `dispatch_records()` entry and `local_pattern`.
It does not identify labels by equality of appender code. The result has
**1,750 canonical subpatterns**, **1,751 state bits**, and the finite cover
bound **`2^1751`**. The state space is never enumerated or minimized.

A fabricated tree made by replacing every wildcard with S is accepted. The
single atom S is rejected. The encoded `+1` seed has 1,710 source bits, 44,069
expanded S-tree nodes and 3,491 distinct immutable nodes. It is rejected; an
independent DAG head-arity calculation also finds maximum arity four, below
the fresh Local's head arity six.

Optional replay reads the bounded report for the already verified first eight
native contractions at addresses `0, 0, 01, root, 0, root, 10, 10`. Each rewrite
is compared with an independently spelled one-occurrence S contraction and
the saved occurrence-node count. All nine samples, including the initial
tree, are negative. The final tree has 264,381 expanded nodes and 3,501 distinct
nodes. The native selector is **not rerun** by this report. Its separately
reported 2,122,868,774-state count is not an automaton-state count.

None of these finite checks proves generated-occurrence provenance, semantic
labels, source-event coverage, first-event timing, or the protected numerical
readout obligations. Those remain as listed in the audit. In particular, a
negative bounded prefix does not establish source nonhalting, and a positive
fabricated tree does not establish a real source event.

## Reproduce

Standard library only, from the repository root:

```sh
(ulimit -v 1048576; timeout 180s python -m unittest discover -s tests \
    -p 'test_pattern_automaton.py' -v)
(ulimit -v 1048576; timeout 180s python -m unittest discover -s tests \
    -p 'test_ut19_event_language_report.py' -v)
(ulimit -v 1048576; timeout 180s python -m tools.ut19_event_language_report \
    --output /tmp/ut19-event-language.json)
# Optional: the separately produced first-native-attempt record must exist.
(ulimit -v 1048576; timeout 180s python -m tools.ut19_event_language_report \
    --replay /tmp/ut19-native-attempt-first.json \
    --output /tmp/ut19-event-language-replay.json)
```

The generic suite independently checks all 550 patterns with at most five
leaves against all 65 S trees with at most six leaves (35,750 pairs), including
every subpattern match bit. It also covers independent repeated holes,
descendant-only matches, all cube states of a small automaton, depth-1,200
shared and distinct-equal pattern DAGs, deep terms, malformed/hostile inputs,
cycles, frozen metadata, cap boundaries and deterministic deadline expiry.
The instance tests reproduce all eight contractions from their own small
fixture, without relying on an ephemeral file or executing the selector.

On 6 October 2026, the two new suites and the existing `test_probes.py` and
`test_encoding.py` suites passed together: 52 tests in 20.184 seconds, under
the 180-second/1-GiB guard, with 36,620 KiB maximum resident memory. This was
a focused related-test run, not the entire repository suite.

The generic automaton and its proof are independent implementations of the
elementary subpattern construction. UT19's table is the
[CC0 wiki construction](https://esolangs.org/w/index.php?title=UT19&oldid=154545).
The reused S encoding/pattern constructors derive from Cinematic Strawberry's
mathematical construction at pinned commit
`85a867988442fc423279341200f81634a1e65582`; its
[MIT copyright and permission notice](../third_party/cinematic-strawberry-MIT.txt)
is preserved. No upstream formal proof was kernel-replayed by this work.
