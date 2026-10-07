# Fixed 38-phase CTS: formal instance and proof boundary

The project-owned Lean module [`formal/SOnly38.lean`](../formal/SOnly38.lean)
instantiates Cinematic Strawberry's generic construction from
[`cstrawberry/predictive-universe` commit `85a867988442fc423279341200f81634a1e65582`](https://github.com/cstrawberry/predictive-universe/tree/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality).

**Check status, 6–7 October 2026:** the complete module successfully elaborated
with official Lean 4.33.1 against the freshly rebuilt pinned imports, then
passed a separate fresh-process kernel replay. Its 13 printed axiom reports
contain only `propext` and `Quot.sound`, with neither needed for the literal
bit and one counts. All three Python source-identity tests passed. The
upstream dependency closure also passed its replay. See the
[replay report](formal-replay.md) and
[fixed-instance evidence](../results/formal_cts_instance.json).

## Concrete data

The literal `productions` table uses the published labels 1 through 19 and
matches `UT19_PRODUCTIONS` in `s_only/ut19.py`. `oneHot k` has one `true` at
zero-based position `k-1` in a length-19 word. `appendants` concatenates each
production's codewords and then adds 19 empty appendants. `program` has the
upstream `CTS.Program` type and literal period 38.

The following facts are proved in Lean, using `decide` for literal computations
and the upstream leaf-count theorem for the dispatcher:

- The table has 19 productions, and every published symbol is in 1 through 19.
- The appendant table has 38 phases, 760 bits, and 40 ones.
- Enumerating `program.appendant` over every finite phase yields exactly that
  table, so these counts describe the actual upstream program argument.
- The last 19 appendants are empty.
- The zero-based phase-17 appendant is `0^17 10`, of length 19 with one `1`.
- The exact upstream canonical balanced dispatcher has 76 leaves and depth 7.
- Its selected route for `(17,true)` is left-right-left-left-left-right-right,
  or `0100011` with left=0 and right=1; executable lookup reaches that label.

A small semantic consequence, `target_response_nonempty`, shows that the
ordinary nonempty-head response at the designated phase has a nonempty output
for every suffix. Its statement uses the upstream absorbing transition, whose
leading-`true` case is exactly the ordinary CTS response.

The Python source-identity tests in
[`tests/test_formal_cts_instance.py`](../tests/test_formal_cts_instance.py)
compare the Lean production literal with the Python production tuple and the
concrete one-hot compilation. They are a drift check; they neither run Lean
nor substitute for kernel checking.

## Instantiated generic facts

The module's fixed objects are precisely:

- `dispatcher = WeakPathUniversality.canonicalDispatcher program`
- `encode bits = generator (compileActions program dispatcher.tree) bits`
- `selector = RootResetFiniteAllInputsTraceAgreement.selector program`
- `controller = RootResetFinitePrioritySelector.selectorContract program dispatcher`
- `trajectory bits n = RootResetTermOnlyTransfer.run selector n (encode bits)`

The encoder's equality with the upstream realization and the selector's
identity with the contract projection are definitional equalities. The latter
is proved first for the abstract read-only probe's selector functions, then
specialized to the fixed program; this keeps Lean from unnecessarily
normalizing the concrete controller runtime during proof elaboration. The
specializations then expose these facts without an input, stage-completion,
provenance, or universality hypothesis:

1. Each invocation starts at the root in the same control state. The
   between-invocation state is `Unit`.
2. Every finite S tree has a terminal controller invocation within
   `controller.coefficient * (tree.size + 1)` microticks, with a fixed positive
   coefficient.
3. A successful selector answer is one native occurrence contraction with
   exactly one runtime mutation. A failed answer is a normal, unchanged tree
   with zero mutations.
4. For every finite input bitword and every contraction index, the explicit
   root-reset trajectory equals the upstream persistent trajectory as a whole
   S term. The selector succeeds at every such sample, and adjacent terms are
   related by the native S contraction relation.
5. `checkpointRealization` is a constructed specialization of the upstream
   `WeakPath.UniformRealizes` object. At every declared checkpoint, the public
   decoder returns the exact CTS iterate; a successful public decode at any
   sample identifies its exact checkpoint and configuration.

The premise of `selected_one_contraction` merely identifies an answer of an
already constructed selector, and the premise of `checkpoint_accepts_only`
merely identifies a successful decode. Neither assumes source universality
or a simulation theorem. The all-input trajectory and checkpoint construction
are imported, specialized facts, not new proofs of the generic simulation.

## Composition map

This module supplies the fixed-program data, generic root-reset controller,
every-sample trajectory agreement, and exact public-checkpoint layers of the
[universality theorem](universality-theorem.md). The complementary written
proofs supply the remaining composition:

- [Uniform register-machine front end](universal-bp2-front-end.md),
  [compact UT19 invariants](ut19-simulation-invariants.md), and
  [one-hot semantic translation](alternating-tag.md): the source-to-CTS layer
- [Local provenance](local-event-provenance.md) and
  [first-event transfer](cts-event-transfer.md): the first completed F17 event
  along the exact S trajectory
- [Fixed event pattern](ut19-s-event-audit.md) and
  [auxiliary bounds](auxiliary-interface-bounds.md): regular tree recognition
  and the fixed observer's size and evaluation bounds
- [Current-tree readout](s-event-readout.md) and
  [UT19 result reading](ut19-readout.md): recovering the source result from the
  event tree, with the representation and resource bounds

Mechanizing those complementary source, first-event, automaton, and readout
proofs is the next layer of the formal composition. Their current evidence is
the written arguments and independent tests recorded in the linked documents.

The exact decoder interface used here is `PublicDecoder.decode`: it returns
`(horizon, CTS configuration)` at the upstream public checkpoints. In the
complete theorem, `H` instead recognizes a descendant completed F17 shell,
and `D` reads that shell's frozen audit and decodes the source result. Their
connection to this module is the exact whole-term trajectory equality.

## Reproduction boundary

The executed toolchain is the upstream-pinned official Lean 4.33.1. The
upstream imports were rebuilt from the pinned source, with no pre-existing
proof artifacts reused. This project module was staged separately and checked
with `lean -j2 -M3072 -o /work/formal-build/SOnly38.olean /work/SOnly38.lean`;
there are no added packages. Execution used an isolated, socket-denying
filesystem namespace and an independent resource guard. The pinned source,
toolchain, and upstream compiled artifacts remained read-only.

Successful run `fixed38-build-4` exited 0. The inner guard recorded 1.321
seconds and a sampled peak aggregate namespace RSS of 1,183,076,352 bytes.
The guard sampled every 50 milliseconds with a 180-second timeout and a
4,294,967,296-byte sampled-RSS stop threshold; sampling does not establish a
hard instantaneous 4-GiB memory bound. The accepted module is 258,792 bytes.

The separate `leanchecker --fresh -v SOnly38` replay also exited 0. Its guard
recorded 113.727 seconds and a 50-ms sampled peak namespace RSS of
1,513,676,800 bytes. External post-replay verification confirmed unchanged
source and compiled-module hashes, together with all 426 pinned input files,
424 original compiled/helper outputs, and 17,505 toolchain files. The complete
log, guard reports, hashes, and parsed axiom reports are retained in
[`artifacts/formal-replay-2026-10-06/`](../artifacts/formal-replay-2026-10-06/)
and the fixed-instance evidence linked above.

- Checked source SHA-256:
  `3fb5944191b4a22c7152f2594b2b8e3d97579da1b4f86081bd046f4993ee9128`
- Compiled `.olean` SHA-256:
  `e99cf78d1037f8e3104889d26cbbdecb415396af0cb16de0ddfbf37ace36137f`
- Complete successful compiler log SHA-256:
  `bcc5de3a0fb017a578b855af80b9dce7e4e0edba0c22197f47742710eb92cce4`

The 13 printed axiom-dependency reports divide as follows:

- `appendant_bit_count`, `appendant_one_count`: none
- `enumerated_appendants`, `target_selected_route`: `propext`
- `every_input_linear`, `every_input_terminal`, `selected_one_contraction`,
  `rejected_zero_contractions`, `trajectory_eq_persistent`,
  `trajectory_selects`, `trajectory_contracts`, `exact_checkpoint`,
  `checkpoint_accepts_only`: `propext`, `Quot.sound`

The final compilation has no errors and no `sorryAx` or `Classical.choice` in
those reports. Three development attempts preceded it: direct concrete
selector/projection conversion reached the recursion limit; two broader
normalization attempts reached their time caps. None supplied an accepted
artifact. The successful proof uses an abstract `ProbeSpec` function equality,
followed by specialization and explicit equality transport. Those attempts
and their guards remain in the replay evidence alongside the successful run.

The final Python drift check was
`python -m unittest discover -s tests -p 'test_formal_cts_instance.py' -v`:
three tests passed.
