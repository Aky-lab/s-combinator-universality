# Independent finite root-reset selector

The fixed two-phase selector now chooses all **85 published native addresses**
from the current bare S tree alone. Its contractions reproduce every recorded
node count and SHA-256 digest. Each invocation starts with the same finite
control and a fresh root cursor; no previous address, source-machine state,
expected path, term hash, or saved sample enters selection.

The implementation covers the fixed two-phase program and its finite
controller construction. Generic initial encoding and compact binary-machine
execution are separate components, linked in the project overview.

## Specification and provenance

The mathematical specification is Cinematic Strawberry's
`cstrawberry/predictive-universe`, pinned at commit
`85a867988442fc423279341200f81634a1e65582`:

- [Paper, Sections 5.1–5.2](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/paper.md#section-5-1): finite pass composition, carrier rows, scope guards, response decisions, historical-copy exclusion, and termination.
- [RootResetFinitePrioritySelector.lean](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/Research/RootResetFinitePrioritySelector.lean): fresh-response, marked-handoff, active-endpoint priority.
- [RootResetFreshResponsePass.lean](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/Research/RootResetFreshResponsePass.lean), [RootResetMarkedHandoffPass.lean](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/Research/RootResetMarkedHandoffPass.lean): candidate recovery and response selection.
- [RootResetActiveEndpointProbe.lean](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/Research/RootResetActiveEndpointProbe.lean): frontend and endpoint ordering.
- [RootResetNestedClockProbe.lean](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/Research/RootResetNestedClockProbe.lean): two numeral-parity passes, guarded rejection, and growth selection.
- [RootResetReadonlySelector.lean](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/Research/RootResetReadonlySelector.lean) and [RootResetEulerWalker.lean](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/Research/RootResetEulerWalker.lean): one-contraction finish, root ascent, and complete preorder fallback.

These sources were read, not executed or installed. The independent Python
implementation uses the existing [probe compiler](probe-compiler.md),
[spine walkers](spine-walkers.md), and [fuel rows](fuel-probe.md). The existing
[upstream MIT notice](../third_party/cinematic-strawberry-MIT.txt) is retained.

## What runs

`s_only/selector_parts/` contains compile-time constructors:

- `patterns.py`: fixed code literals, carrier and scope patterns, FRAME,
  dispatcher and selected-action rows
- `graph.py`: finite graph assembly, inlining restoring tables and walkers
- `priority.py`: fresh/marked searches, scoped response decisions,
  nonemptiness, parity, oldest-live, EMPTY-origin, COMMIT and handoff
- `active.py`: active-history frontend and ordered endpoint probes
- `clock.py`: nested CLOCK and fixed-control parity

`s_only/root_selector.py` executes the graph. `SelectorTable` has only
`states` and `start`. The generated table has **257,299 controls**, each with
six immutable entries: S/application crossed with root/L/R incoming side.
This is the emitted finite cover, not a minimal or reachable-state count and
not a numerical claim about the upstream controller.

The configuration has exactly `control` and `cursor`. The cursor is the
occurrence zipper already used by restoring probes. Runtime commands are
stay, L, R, U and Rdx, plus two absorbing result interpretations. Rdx performs
one ordinary `S x y z -> x z (y z)` contraction and immediately enters the
contracted terminal. No later movement is allowed after that mutation.

Patterns, row addresses, tagged procedure calls, recursion over the dispatcher,
and continuation wiring disappear into finite states before input processing.
The interpreter performs no pattern recursion, whole-tree equality,
serialization, tree-size inspection, data-dependent arithmetic, source
transition, dynamic call stack, or saved invocation cursor. Parity is encoded
by two copies of finite control, never by an integer counter.

`Cursor.path` is inspected only to report the selected occurrence. Following
Rdx, the cursor retains the original context with a replacement focus;
`erase(cursor)` materializes that represented result. The read-only
`Cursor.root` helper must not be used on a contracted cursor. This terminal
zipper erasure is output reconstruction, not a selector observation.

Shared immutable subtrees remain distinct occurrences through their different
parent paths. Selection never substitutes structural equality for occurrence
identity.

## Exact pass assembly

1. Run the active frontend; **both** its answers feed nearest completed-fresh
   ancestor recovery. If found, run the scoped completed-response query.
2. On decline, explicitly ascend by U to the root. Run the frontend again,
   locate the nearest completed marked Local, and search for its nearest
   registered pending parent.
3. On decline, reset to root again. Run the active frontend, then scoped
   Base, pending-to-Base, dispatcher, selected action/Push, seven FUEL rows,
   and nested CLOCK, in that order.
4. On decline, reset to root and run complete root-left-right Euler search.
   A verified redex enters Rdx; exhaustion enters the normal terminal.

The frontend admits a marked Local's RL continuation before testing FRAME.
A fresh Local admits RL only after a successful nonemptiness query. Registered
pending shells admit R only for the listed structural child cases. FRAME is
rechecked at the root or after Local RL, not indiscriminately after every
pending descent. Its failed descent restores the segment boundary.

The dispatcher reconstructs phase and the deleted front bit from designated
carrier fields, restores its Local, and selects a static route-stage row.
It does not evaluate a CTS step or inspect its source input. CLOCK rejects a
saturated head with a malformed numeral immediately; a rejected numeral is
not permission to try growth.

Composition inlines continuations and elides upstream component-handoff stays.
The Euler probe is compiled from the restoring redex pattern rather than
copying the upstream 15-state table. These changes preserve choices but change
literal microtick costs. All counts below describe this Python graph only.

## Scope and inverse restoration

An inverse row recognizes an ancestor candidate; it is not automatically the
inverse of prioritized descent. This implementation depends on the specific
carrier-family coherence and boundary conditions in paper Section 5.2.2:

- The final forward edge enters the argument of one of the pairwise distinct
  fixed functions S, PI, LIVE[0], LIVE[1].
- Base and tombstone reverse side words differ at their second side.
- Local reverse words identify the appender history, route pairs, and the
  prefix-free Local delimiter; overlapping Local patterns therefore identify
  the same ancestor occurrence.
- Consequently, every successful inverse carrier candidate at a descent
  endpoint identifies the actual preceding carrier occurrence.
- Root and left-child starts cannot have an inverse carrier predecessor.
  A right-child start is admitted only after its immediate parent matches
  the fixed program's pending pattern. That parent's function differs from
  all four carrier anchor functions, establishing the stopping boundary.

The scoped query restores its right-child cursor after checking that parent.
An unrelated right parent declines **before** beginning the carrier scan.
The inverse walk therefore stops at the intended start, without a marker,
saved depth, secondary cursor, or extra stack. The nonemptiness and EMPTY
subfamilies preserve the same boundary. FRAME and CLOCK have their own
left/root boundary or fixed-head exclusion arguments.

The response decision preserves the source's distinctions:

- Nonpending fresh/nonempty declines; nonpending fresh/empty commits LLL.
- Pending empty with EMPTY provenance commits independently of parity.
- Otherwise true parity selects the oldest live root, or commits if absent.
- False parity selects the pending-parent handoff, including immediately
  after deletion of the last live cell.

A marked or historical fresh outer Local cannot substitute an audit copy for
the active occurrence. Tests explicitly place a FRAME-looking redex in an
audit field and verify that the frontend follows RL instead.

## Termination, soundness, and bounds

The table validator checks finite immutable entries, valid targets, uniform
terminal interpretations, and immediate absorption after Rdx. It does **not**
prove termination of arbitrary hand-written tables.

For the compiled controller the compositional termination argument is:

- Each forward carrier, FRAME or unary wrapper pass follows a supported
  nonempty address, strictly decreasing the focused subtree size.
- Each successful inverse pass strictly decreases parent depth. Restoring
  failures take only their finite compiled path.
- Scope/coherence ensures each restoring subquery finishes at its boundary.
- An active-history restart follows a strict RL or admitted R descendant.
  Its internal finite read/restore queries complete before this descent.
- Fresh/marked and pending-ancestor searches ascend strictly between tests.
- There are only three outer priority passes, each followed by a terminating
  explicit root ascent. The Euler suffix visits each occurrence finitely.

Every successful source row designates a syntactically certified redex.
CLOCK verifies its exact saturated head; Euler uses a restoring depth-three
redex test. Thus success executes one legal native contraction and stops.
If all priority passes decline, the complete Euler traversal selects a legal
redex iff one exists. These are mathematical port arguments, not a separately
machine-checked proof of the Python code; the tests below provide independent
bounded evidence.

There is a simple conservative graph-specific linear bound after termination
has been established. Before Rdx the tree is unchanged. On a fixed tree with
N occurrences and Q controls there are at most Q*N represented configurations.
A deterministic terminating read-only run cannot repeat one. Adding the single
mutation gives a bound of **257,300*(N+1)** microticks. This finite-configuration
argument is not, by itself, a termination proof, and no such counter is stored
in control. It also does not promise constant wall-clock cost per Python tick:
immutable zipper tuple movement can cost time proportional to depth.

The test/report harness additionally enforces a strict external cap of
2,000,000 selection microticks per invocation and 120 seconds for the report.
Counters, clocks, fixture expectations and tree-size calculations exist only
in that harness. The graph interpreter itself has none of them. The wall-clock
check occurs between microticks; an enclosing process timeout is appropriate
when compilation and serialization also need a hard elapsed-time cap.

## Checked results

The measured report records:

- 85/85 exact selected addresses, from fresh root/control each time
- 85/85 native outputs matching the published SHA-256 and occurrence count
- 1,315,234 total selection microticks; maximum 41,917 for one selection
- All 626 S trees through 8 leaves: 216 normal, 410 reducible; correct
  normality/progress in every case, maximum 2,577 selection microticks
- Seven initial words: empty, 0, 1, 00, 01, 10, 11; four independently expected
  initial CLOCK addresses and 28 legal native contractions for each seed

The 85-step run advances with the controller's own contraction. The saved
fixture is read only afterward as an expected-address/digest oracle. There
is no recorded-schedule replay in the selector.

Additional persistent regressions cover independent wildcard payloads and
malformed pattern-shaped trees, carrier scope and exact restoration,
EMPTY/tombstone chronology, nearest candidate recovery, all 20 fixture
dispatcher label/stage combinations, FRAME miss restoration, and CLOCK
parity/growth. CLOCK alone is compared with an independent structural oracle
on 8,788 nested starts in the exhaustive small-tree set and 960 generated
parity/wrapper cases. These cases go beyond the shallow malformed trees,
which cannot exercise the fixture's large static action patterns.

## Independent model review

A separate review reproduced the 85 samples in reverse order, with runtime
access to source decoders, CTS helpers, generic selectors, compilers, files,
hashes, whole-term equality, cursor path/root inspection and budget inspection
disabled. This checks that neither prior invocations nor an external source
oracle supply a selected address.

Additional checks cover all 6,918 closed terms through ten leaves, 500
carrier-shaped adversarial terms, a depth-2,000 normal term, and independent
recompilation of the identical 257,299-state graph. The graph digest and all
native counts are recorded in [the measured report](../results/root_selector.json).
The deterministic report option omits only wall-clock durations.

## Reproduce and use

```sh
python -m unittest discover -s tests -v
python -m tools.root_selector_report --deterministic --output /tmp/root-selector.json
```

```python
from s_only.queue_fixture import encode
from s_only.root_selector import selector_table, select_path, reduce_once

controller = selector_table()  # fixed compilation; no input argument
term = encode((1, 0, 1))
assert select_path(term, controller) == (0,)
term = reduce_once(term, controller)
```

`select_path` is a read-only interface. `reduce_once` starts independently and
returns the once-contracted term, or `None` for a normal term. For instrumented
execution, prepare `Configuration(controller.start, Cursor.at(term))` and call
`step` from an external bounded harness. Never feed a prior invocation's
control or cursor into the next selection.
