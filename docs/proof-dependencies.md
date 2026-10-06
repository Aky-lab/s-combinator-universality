# The proof and its verification dependencies

The [consolidated theorem](universality-theorem.md) gives a fixed-controller
S-only universality construction with a fixed regular event language and
current-tree output decoding. The [official S Combinator Challenge](https://writings.stephenwolfram.com/2021/06/1920-2020-and-a-20000-prize-announcing-the-s-combinator-challenge/)
discusses selected evaluation paths, results observed during continuing growth,
and bounds on auxiliary encoding/detection/decoding. Its acceptance criterion
also includes human assessment of whether a construction answers the question.

## Construction route

```text
finite register machine + input
    -> restart-safe all-zero BP2 source
    -> compact UT19 initial queue
    -> one fixed 38-phase ordinary binary CTS
    -> exact pinned S encoding and root-reset controller
    -> first regular event and frozen-audit result.
```

The machine and its data vary only through the initial S term. The native
controller, event language, result grammar, and final output coordinate remain
fixed. Every invocation begins at the root with the same finite control and
contracts one occurrence of `S x y z -> x z (y z)` along the encoded path.

## Source compilation and outputs

The [complete machine/input-to-BP2 reduction](universal-bp2-front-end.md)
provides restart-safe initialization, tie-free clock simulation, and a fixed
output convention. For `d` registers, `I` increment instructions, `J` decrement
instructions, and input sum `s`, put `k=d+I+4J`. Its BP2 program has `8k+3`
labels and exactly `168k^2+124k+19+4s` commands. It halts exactly when the
source does and leaves first counter `2n+3` for source result `n`.
[Independent algebraic review](universal-bp2-front-end-review.md) checks the
three intermediate models, arbitrary counter magnitudes, restart boundaries,
and syntax-only size formulas.

The [compact BP2-to-UT19 proof](ut19-simulation-invariants.md) establishes
restart closure, first selected-18 equivalence, no premature queue exhaustion,
and counter runs of lengths `4^(x+1)` at the event. The
[one-hot lemma](alternating-tag.md) transfers that event to CTS phase 17 with
leading bit 1. [Structural readers](ut19-readout.md) recover the complete
counter tuple. The fixed final map `(first-3)/2` recovers the register-machine
result.

The [auxiliary-interface bounds](auxiliary-interface-bounds.md), with
[independent review](auxiliary-interface-bounds-review.md), give exact initial
S size `16,529+306q` for `q` tag symbols and a singly exponential encoder bound
in explicit binary source-description size. Construction loops are bounded by
syntax, independently of source running time.

## Exact S trajectory and first event

The mathematical construction uses the exact generic encoder, dispatcher, and
finite controller in the pinned
[Cinematic Strawberry package](https://github.com/cstrawberry/predictive-universe/tree/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality).
Its source declarations provide arbitrary-finite-input controller totality,
a fixed-root one-contraction contract, and equality with the persistent
scheduler at every contraction sample.

The [labelled prefix proof](cts-event-transfer.md) lifts the actual stage
construction with Local-origin and frozen-snapshot annotations. Each stage
`h` executes `h` jobs, each recomputing the first `h` source responses from the
original seed and phase zero. If `r` is the first target CTS prestate, the
first completed target Local is the final response of the first job in stage
`r+1`.

Only nonempty stages are required: the source proof prevents exhaustion before
the first event, and its nonempty target appendant also preserves `c_(r+1)`.
For a nonhalting source, every finite horizon stays nonempty. This discharges
the restricted stage hypothesis for every input produced by the source
compiler. [Independent transfer review](cts-event-transfer-review.md) checks
the inclusive horizon, every-sample ordering, job resets, fixed syntax,
selector identity, and the public snapshot-decoder bridge.

## Event provenance and current-tree output

The [event-language audit](ut19-s-event-audit.md) identifies a completed fresh
Local with label `(17,1)`, route `0100011`, and 19 action-history arguments.
Descendant occurrence is a regular tree language. Its
[bottom-up automaton](pattern-automaton.md) has a fixed `2^1751` state cover.

The [Local-origin proof](local-event-provenance.md), independently
[reviewed](local-event-provenance-review.md), examines new nodes, copies, and
rebuilt ancestors in every registered construction context. The stage lift
supplies those contexts for all samples needed by the first-event theorem.
It also preserves the literal post-deletion snapshot at Local address `LLLR`.

The [bounded current-tree reader](s-event-readout.md), independently
[reviewed](s-event-readout-review.md), locates the first preorder witness,
reads that frozen snapshot, restores the deleted 1, and applies the fixed CTS
result grammar. Its sufficient charged work is `4096(N+1)^3(C+1)^2`, with
polynomial bit-time and storage under the stated input/cap convention. The
exact upstream theorem `CheckpointRun.decodeCarrier?_of_decode` links the
response's semantic snapshot to this seed-free public grammar.

Thus the first accepting tree contains precisely the source result needed by
the fixed reader. A mutable accumulator is unnecessary: the recorded `101`
fixture shows an old Local accumulator changing from `011` to `11` while its
frozen audit continues to decode `01`.

## Verification ledger

| Component | Current evidence |
| --- | --- |
| Register-machine → BP2 → UT19 → CTS | Written quantified invariants, independent algebraic review, executable finite checks |
| Local provenance and frozen audit | Written occurrence proof, independent review, adversarial native fixtures |
| Nonempty stage lift and first-event composition | Exact pinned source inspection and independent written proof review |
| Regular detector and bounded decoder | Explicit algorithms/bounds, independent review, adversarial implementation tests |
| Generic fixed-root S controller and all-sample transfer | Pinned upstream formal proof sources inspected; local kernel replay pending |
| New composed theorem | Written proof assembled from the components above; local mechanization pending |
| Independent Python controller port | Exact finite-table/trace comparisons and bounded native tests; all-input port correspondence is a separate reproduction theorem |

For the Python reproduction, whole-controller preflight gives 2,122,868,774
indexed controls and original start 2,064,502,462 for the fixed UT19 endpoint.
The independently compiled pooled representation preserves those indices.
This implementation count is separate from the abstract coefficient in the
exact pinned controller's all-input theorem.

The next main validation step is fresh checking of the inherited formal
dependency closure, followed by mechanizing the new event lift/composition.
The [consolidated statement](universality-theorem.md) supplies the target and
[the source index](cts-event-transfer.md#pinned-source-index) supplies the exact
imported declarations. The [supplemental source manifest](../results/first_event_sources.json)
records exact Git-blob and SHA-256 identities for the 33 additionally inspected
proof files.

## Attribution

Cinematic Strawberry supplies the generic S protocol and formal controller
results. UT19 and its underlying component ideas are attributed to ais523.
The project documents its explicit front-end normal forms, compact-source
invariants, Local-event derivation, first-event stage lift, bounded readers,
independent code, and representation analyses alongside those sources.
