# Bounded S-level first-event output readout

6 October 2026. [`s_only/s_event_readout.py`](../s_only/s_event_readout.py)
provides the current-S-tree structural output interface proposed in
[the event audit](ut19-s-event-audit.md). It exposes the frozen carrier reader
with actual enforced work accounting; it does **not** call the old unbudgeted
`CompiledReader._queue` and does not claim that finite tests prove native
reachability or scheduler correspondence.

## Interface and exact meaning

```python
read_s_event_result(term, *, limits=SReadoutLimits()) -> tuple[int, ...]
read_ut19_event(term, *, limits=SReadoutLimits()) -> EventReadout
find_ut19_event(term, *, limits=SReadoutLimits()) -> tuple[int, ...] | None
```

The numerical convenience function returns the same `.values` as the detailed
function. `EventReadout` also reports the current occurrence address `.witness`
(`0=L`, `1=R`), validated distinct `.input_nodes`, and charged `.work`.
`find_ut19_event` only tests the exact structural language and returns its first
preorder witness, or `None`; it does not attempt numerical decoding. The result
reader raises `ValueError` if no witness exists or its frozen carrier/UT19 word
is malformed. Exhausted caps raise the existing `cts.ResourceLimit`. No exception
is a negative answer to source halting.

The fixed wrapper has exactly the fixed UT19 CTS program. Its event is the fresh
completed Local pattern `F17`, label `(17,1)`, route `0100011`, with exactly 19
completed-action history arguments. Dormant route code is literal, and every
wildcard is independent. This is neither an arbitrary Local nor an equal
appender-code test. The current pattern witness is found anew on each call.
The numerical operation is precisely

```text
X := first preorder F17 occurrence in the supplied current term
V := X[LLLR]
u := DecodeCarrier(V)
read_cts_result(Configuration(word="1" + u, phase=17))
```

It never uses the current action accumulator for output. In particular it does
not undo the 19-bit appendant: the action accumulator is mutable, whereas the
specified fresh halt audit is the creation-time post-deletion carrier.

If the first structural witness has a malformed payload, numerical readout
rejects rather than searching for a different, convenient payload. Structural
acceptance and numerical grammar acceptance are separate facts. A fabricated
shell with a well-formed payload can pass both; neither acceptance establishes
reachability, source identity, an actual past source event, or firstness.

## Exact input validation, sharing, and opaque fields

Every reachable node must have exactly the repository's `App` or S-atom class;
subclasses and duck-typed objects are rejected before their methods are invoked.
Distinct instances of the exact empty S-atom class denote S. Children are read
through `object.__getattribute__`; absent child slots are rejected. An iterative
three-colour traversal rejects cycles, including cycles hidden in unused audits.
It uses object identities, never input equality or hashing. Every node is
validated before pattern matching or carrier parsing begins, even when a match
is already visible on the left. Limits can refuse during validation.

The traversal builds an input-local postorder DAG whose edges are plain integer
indices. All subsequent operations use that snapshot, and every edge points to
a smaller index. The retained input is assumed immutable during the call, as
its frozen classes specify. The reader neither mutates it nor uses a cache from
a prior call. The cached `_leaves` occurrence count is never read; it may be
missing or nonsensical without affecting the mathematical syntax.

Opaque fields are ignored **semantically**, not exempted from global finite-S
validation. These include independent route/seed/history/continuation audits,
Base retained beta and dormant seed payload, and tombstone audits. Their entire
syntax is validated, and an F17 inside any of them remains visible to the
structural descendant observer. They do not contribute bits to carrier decoding.
The two actual continuation occurrences in a Base are different: the grammar
requires their full structural equality, without requiring object identity.

## Carrier grammar and implementation correspondence

`compile_carrier_reader(program)` is a separate experimental setup helper;
its immutable result exposes `read_carrier(term, limits=...) -> str`. It enables
small-program differential tests. The fixed UT19 wrapper never accepts a caller
program, source seed, source state, counter count, cursor, clock, trace, or step
number. Its grammar is prepared once at module import from the fixed UT19 table.
No compiler runs in any readout call, including the first call after import.
Factory-produced static grammar objects are trusted code, not mutable input.

Setup reuses the existing constructor/compiler's static action and dispatch
metadata, not any of its parser methods. Runtime independently implements the
public carrier grammar in [`cts-reader.md`](cts-reader.md):

1. Attempt a Base. Validate its active environment against the fixed action
   code, primitive `b`, repeated continuation equality, and dormant environment.
   Then decode its queue only as a cell spine. A malformed Base queue does not
   fall through into a different whole-carrier production.
2. Otherwise attempt a fresh or marked Local. Check its halt/seed/continuation
   skeleton, exact completed route, dormant sibling code, `PI` and exact action
   history count. Descend into its accumulator. It need not reflect the label's
   emitted bit values: that would be a reachability assertion absent from this
   permissive public grammar.
3. Otherwise parse a live cell or tombstone, following its canonical predecessor.
   Retain live labels; ignore consumed labels and tombstone audit siblings.
4. At the Base's terminating S, reverse the accumulated outside-in live labels
   once to obtain their logical queue order.

This last reversal is merely traversal-order assembly of a structurally given
word; it is not reversal of mutable accumulator operations or source history.

Each constructor recognizer consists of the same displayed finite pair/arity
and exact-equality tests as the public grammar. Every successful recursive
premise is replaced by an iterative jump to a strict child descendant. Induction
on the postorder index therefore proves both termination and correspondence:
`read_carrier` returns exactly the public decoded queue when the caps suffice,
and rejects precisely when no production in its ordered grammar applies.
In particular it cannot generate additional output by cycling through a DAG.
One live bit comes from one distinct node on a strictly descending path, so the
returned carrier word has length at most the validated node count `N`.

## Witness algorithm

The exact F17 pattern is compiled to a finite immutable DAG of descriptors
`_`, `S`, and pairs. A bottom-up state has one bit per descriptor. At an S node
only the wildcard and S descriptors match. At an application, a pair descriptor
matches iff its left/right descriptor bits hold in the respective child states;
a separate Boolean records a root match or a descendant match.

Every distinct input DAG node is processed once. No occurrence tree is unfolded.
When a match exists, descend from the root: stop on a root match; otherwise take
the left child if it contains a match, and the right child otherwise. This is
exactly first preorder occurrence selection, including shared subtrees, and it
requires at most `N-1` edges. It retains no old address. `LLLR` is then a fixed
four-edge lookup inside the accepted root. Descriptor bits need not represent
reachable automaton states: all finite bitvectors are legal states.

The current implementation retains some unused literal-code descriptors in its
static array. They do not change root recognition, and all their visits are
charged. The runtime code size `FIXED_CODE_SIZE` is 5,165; it includes 1,985 pattern
descriptors, all 2,237 static term-DAG nodes, dispatch entries, history lengths,
and a constant allowance. No exponential transition table is materialized.

## Explicit all-input bound

Let `N` be the number of distinct validated input nodes, and let `C` be the fixed
code-size allowance reported above (or the generic helper's `.code_size`).
The operation budget charges:

- every validation stack pop;
- every pair/atom inspection and every carrier/route iteration;
- every pending-pair pop in every structural comparison, including duplicate
  pairs skipped by that comparison's local identity memo;
- every descriptor visit at every input node, plus each witness edge;
- each retained carrier bit and the final word assembly;
- a reservation of `1024 * (L+1)` before constructing/scanning the restored CTS
  prestate of length `L`.

The last reservation covers prefix assembly, the plain-string CTS constructor's
binary validation, the existing result reader, and the returned tuple. That
reader performs at most a constant number of cursor operations per decoded
symbol and bounded 19-bit block scans. Its Reset loops always advance; its
counter run arithmetic uses bit lengths, not exponentiation or floating logs.
A conservative 1,024 elementary structural/string/cursor units per input bit
also covers its fixed validation and all output writes. The reservation is made
before those operations, and is charged even if a downstream cap/grammar check
then rejects. This gives a compositional bound without wrapping an unbudgeted
source evaluator in a nominal timeout.

Here is a conservative sufficient budget implemented by
`polynomial_work_bound(N,C)`:

```text
W(N,C) = 4096 (N+1)^3 (C+1)^2.
```

Proof of sufficiency, including hostile finite syntax:

1. Validation has at most `3N` stack pops: each distinct App is expanded once,
   producing its exit and two child entries. Shared edges are skipped without
   expansion. It retains at most `N` completed/active identities.
2. A fixed-code comparison processes at most `2NC+1` pending pairs. A comparison
   between arbitrary input continuations processes at most `2N^2+1`. For either,
   only the first visit to a distinct ordered pair pushes its two children.
   These estimates also cover unsuccessful comparisons; no equality function
   recurses or unfolds shared syntax.
3. Successful carrier iterations strictly decrease the current node index,
   including the transition into the Base queue. There are at most `N+1`
   iterations. A failed Base attempt can compare arbitrary continuations once.
   Consequently repeated unsuccessful Base comparisons contribute at most
   `(N+1)(2N^2+1)`, not an exponential unrolling or an uncharged operation.
4. Per carrier iteration there are at most `C+10` fixed-code comparisons:
   every selected route visits at most `C` dispatch entries, and all the other
   constructor checks contribute a fixed allowance. Noncomparison pair, arity,
   route, and history work is at most `(40C+80)(N+1)` overall. The resulting
   comparison contribution is at most `(N+1)(C+10)(2NC+1)`. Here `C>=32` by
   construction. Failed alternatives are included in both estimates.
5. Pattern evaluation, witness finding, and audit lookup cost at most
   `N(C+1)+2N+6`. The carrier has at most `N` bits, so `L<=N+1`; output reservation
   is at most `1024(N+2)`, and assembly is linear in `N`.
6. Adding these conservative estimates is less than `W(N,C)` for `N>=1` and
   `C>=32`. Constant-sized limit validation/code-size arithmetic does not scan
   the term. Refusal/rejection interrupts these operations rather than adding
   a new unbounded loop. Every budget increment checks before performing the
   charged operation, and equality/comparison work is actually metered.

`W` bounds **charged structural work**, not elapsed seconds or machine
instructions. First take fixed caps, or caps derived from a supplied node bound
`n` polynomially bounded in `N+C`. Integers for indices/counters then have
`O(log(N+C))` bits;
pattern states have `O(C)` bits. Standard hash tables are convenient, but a
worst-case complexity claim need not assume constant-time hashing: each table
has at most `O((N+C)^2)` entries, all keys are plain bounded integers or pairs.
Replacing any lookup by a linear scan, and including bounded-key comparisons
and bitvector arithmetic, multiplies the abstract-work bound by at most a
polynomial in `N+C`. Thus a conservative bit-operation asymptotic bound is
`O((N+C+1)^10)` even without an average-case hash assumption. In the usual RAM
accounting, the more informative charged bound is cubic in `N` for fixed code.
For arbitrary caller-supplied cap integers, let `K` be the sum of their bit
lengths plus one per cap. Comparisons, subtraction from the remaining work
budget, and downstream cap arithmetic also depend on `K`; the corresponding
bit-operation bound is polynomial in `N+C+K`. An arbitrarily loose supplied
node bound is included through those cap bit lengths. The charged `W(N,C)`
bound is unchanged. Peak working storage is polynomial too: `O(NC+N^2+C)` bounded-word
slots is sufficient for snapshot, states, local equality memo, stack and output,
plus `O(K)` bits for arbitrary cap integers and their temporary arithmetic.

### Caps and the mathematical total reader

`SReadoutLimits` is an exact frozen/slotted dataclass. Every field is rechecked
as a plain nonnegative integer at each entry, including instances modified by
bypassing the frozen constructor. Defaults are:

| Field | Default | Meaning |
| --- | ---: | --- |
| `max_input_nodes` | 1,000,000 | Distinct reachable S/App identities, including opaque syntax |
| `max_word_bits` | 19,000,000 | Restored CTS word, including the prepended 1; generic helper: carrier word |
| `max_queue_symbols` | 1,000,000 | Restored logical UT19 symbol count |
| `max_counters` | 100,000 | Result tuple entries |
| `max_output_bits` | 1,000,000 | Sum of `max(1,value.bit_length())` |
| `max_work` | 100,000,000 | Charged operations/reservations above |

The separate caps make practical experiments refuse predictably. Work includes
full-DAG validation and searching, not just successful payload parsing. Opaque
syntax and shared code are counted even when they do not affect the answer.
Input/output cap exhaustion remains a refusal; raising a cap cannot alter a
previously obtained structural answer.

For a supplied upper node bound `n`, `limits_for_input_nodes(n)` sets input cap
`n`, all word/symbol/counter/output caps to `n+1`, and work to `W(n,C)`. The generic
helper has the analogous instance method. Every valid carrier output has at
most `n` bits. Restoring 1 gives at most `n+1`; its symbol/counter counts are no
larger. Every output value's bit length is bounded by the already supplied
counter run length, so their total is likewise at most `n+1`. These derived
caps therefore suffice for every exact finite DAG of at most `n` nodes. One may
obtain `n` from the finite input's graph representation or a preliminary bounded
node count; neither depends on the simulated running time. This realizes the
mathematical total reader (result or structural rejection) rather than assuming
a finite experimental cap covers every input. No reader promises to locate a
future event or terminate the source simulation.

## Conditional numerical theorem and remaining transfer boundary

Assume the generated-script/CTS correspondence, stage coverage/order, all-sample
scheduler transfer, and native implementation correspondence listed in
[the independent provenance review](local-event-provenance-review.md#6-inherited-premises-not-independently-discharged-here),
and the source-machine/UT19 first-event simulation theorem. Let `T` be the
**first accepting current S sample**, with sufficient resource caps.

[Local-event provenance](local-event-provenance.md) then gives:

- each completed F17 occurrence is born at response label `(17,1)`;
- its `LLLR` field is the unchanged post-deletion carrier `V`;
- at the first accepting sample, the chosen occurrence represents the first
  source event, not a later retained event.

The carrier grammar correspondence above reads `V` as precisely the old CTS
word with its head 1 deleted. Prepending 1 recovers the phase-17 event prestate.
The existing [UT19 reader theorem](ut19-readout.md) consequently returns exactly
the ordered natural-number source result tuple. The numerical conclusion does
not apply to an arbitrary later sample merely because it contains an old or
new F17. The reader does not test any of these semantic premises itself.

This implementation closes the exposed structural-reader and adequate-budget
interface. It does not independently discharge the generated-scheduler induction,
all-input encoder/selector port correspondence, or upstream source simulation.
Neither the Python tests nor importing fixed code is a replay of Lean proofs.

For the challenge's encoder/decoder restriction: this decoder's work is polynomial
in the supplied finite S DAG and its fixed code. The grammar compiler merely
prepares the one fixed UT19 table; it does not specialize on or evaluate a source
program. Constructing a supplied carrier word is one literal cell wrapper per
bit, with fixed code. The separate source-to-initial-S encoder and scheduler must
still meet their documented construction/correspondence obligations; this output
interface does not lend them unrestricted computational power.

## Tests and bounded verification

[`tests/test_s_event_readout.py`](../tests/test_s_event_readout.py) includes:

- synthetic exact F17 shells whose frozen payloads contain both recorded UT19
  event tails: `+1 -> (1,)`, `-1 -> (0,)`; no UT19 S run is asserted;
- agreement with the independently reconstructed exact F17 pattern automaton;
- correct current preorder witnesses with shared copies and moved roots;
- deliberately unrelated mutable accumulators, malformed frozen audits, wrong
  labels/history counts/freshness, and downstream malformed Reset words;
- differential decoding of every distinct subtree at all 86 samples of the
  existing 85-contraction legacy fixture, comparing both acceptance and data;
- deep Local chains, live cells/tombstones, independently equal/unequal deeply
  shared Base continuations, ignored opaque syntax, and strict Base boundaries;
- hostile/subclass nodes, missing children, cycles and invalid siblings after a
  match, missing/hostile cached size fields, and independently created S atoms;
- exact input, word, symbol, counter, output and work limits; zero/forged caps;
- patched evaluators, reduction, compilers, clock, files, term equality/hash, and
  the old private `_queue` that raise if touched during numerical readout.

Run using only the standard library and a hard process guard:

```sh
timeout 180s sh -c 'ulimit -v 1048576; python -B -m unittest discover -s tests -p test_s_event_readout.py -v'
```

Verified 6 October 2026: all 17 new tests passed in 51.261 seconds under the
180-second/1-GiB guard. A further guarded run passed all 43 existing carrier and
UT19-result-reader tests plus the strengthened runtime-isolation test (44 tests
in 1.936 seconds). No large UT19 S trajectory was executed.

Construction attribution: the S constructors/public grammar are independently
implemented from Cinematic Strawberry's pinned construction at
`85a867988442fc423279341200f81634a1e65582`; the existing MIT notice is in
[`third_party/cinematic-strawberry-MIT.txt`](../third_party/cinematic-strawberry-MIT.txt).
The UT19 table has the existing CC0 provenance. No installation, downloaded-code
execution, large native UT19 reduction, or publication is part of these tests.
