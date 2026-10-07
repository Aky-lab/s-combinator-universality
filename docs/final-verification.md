# Register-machine end-to-end verification

7 October 2026. This is the 56-module numerical-result checkpoint. The
[67-module conventional-Turing-machine extension](formal-turing-universality.md)
adds a checked tape-to-register compiler and has a separate fresh replay.

The complete finite-register-machine-to-S theorem passed a clean source build
and fresh official Lean kernel replay. Its encoder, controller, event observer
and first-current-tree result interface are joined in
[`SOnlyUniversality.lean`](../formal/SOnlyUniversality.lean).

## Exact theorem

`SOnlyUniversality.result_iff_first_event` quantifies over:

- Any natural dimensions d and n
- Any machine with d+1 natural registers and n+1 `INC/DECJZ/HALT` labels
- Any natural input vector
- Any requested natural output value

It proves that the machine halts with that value in register 0 exactly when
there is a first accepted S-tree sample and the fixed current-tree decoder
returns that value. No source-event, liveness, generated-origin, numerical
success or bounded-run hypothesis remains in this statement.

The [recorded theorem types](../artifacts/universality-proof-2026-10-07/main-theorem-types.txt)
also expose `halting_iff_event`, `first_event_correct`, `nonhalting_no_event`,
root reset, Unit inter-invocation state, every-input linear stopping time,
and native S contraction at every encoded step.

## Build and kernel replay

- Official Lean 4.33.1; verified archive SHA-256
  `0376ac87487246b40dd077268c097e701f552e94c6d020d2373b50c7444fa22f`
- Generic construction pinned at `85a867988442fc423279341200f81634a1e65582`
- All 56 project modules built into a fresh output directory, in dependency
  order; every module and the import-only wrapper exited successfully
- Clean project build: 46.807 seconds, sampled namespace RSS peak 1,235,021,824 bytes
- `leanchecker --fresh -v SOnlyUniversalityReplay`: exit 0 in 127.489 seconds,
  sampled namespace RSS peak 1,540,689,920 bytes
- 1,142 explicit public declaration/type/definition queries resolved; their
  reported dependencies are limited to `propext`, `Quot.sound` and
  `Classical.choice`

The replay search directory was read-only and excluded the canary objects.
The toolchain, pinned source/config files and original dependency outputs
were also read-only. The isolation removed private workspace paths and
inherited environment variables and denied new sockets.

Fresh replay reconstructs declarations using the official Lean kernel. It is
a second proof-checking pass, not an alternate kernel implementation or an
independently bootstrapped toolchain.

## Computability and auxiliary interfaces

The encoder, literal machine compiler, event and decoder are ordinary
executable definitions. None of the 56 sources declares `noncomputable` code.
The queried data dependency cones of `encode`, `machineBits` and the literal
BP2 compiler contain only `propext` and `Quot.sound`; event/read contain only
`propext`. `Classical.choice` occurs in logical existence/uniqueness proofs,
not those data definitions.

Executable checks produced a 7,011-command, 51-counter compiled minimal
machine and depth 14. A separate one-counter increment example produced
1,710 CTS input bits and a 44,069-node initial S tree. These check executable
compiler interfaces; the universal result rests on the quantified theorem.

The [finite observer certificate](../formal/SOnlyObserver.lean) constructs
an exhaustive fixed Boolean-state cover and proves exact descendant-pattern
recognition on every finite tree. The actual first-preorder decoder has an
[input-size-fuel equivalence](../formal/SOnlyDecoderBoundCurrent.lean),
output-size and charged-recursion bounds. Its cubic constructor/list and
polynomial bit-time analysis is in [the source audit](lean-current-decoder-bound.md).

The [formal compiler bound](../formal/SOnlyMachineBounds.lean) is polynomial
in source dimensions and unary input values. The chosen UT19 memory width is
linear in literal BP2 program size. The resulting binary-description encoding
bound is singly exponential. Complete bit-cost reasoning is written
mathematics, rather than an instruction-level Lean compiler cost theorem.

## Positive and negative controls

The controls were rebuilt and rerun separately at final verification:

1. A valid arithmetic proof compiled and passed fresh replay.
2. An ordinary invalid proof of False was rejected by the source checker.
3. A deliberate environment-manipulation canary compiled an invalid theorem
   named `invalidFalse`. Fresh replay rejected that exact declaration because
   its proof had type Prop while False was required.

The third failure was a kernel type error, not a timeout, missing import or
resource refusal. No canary object was in the proof search path.

## Integrity

After replay and the negative controls, independent rehashing matched:

- 426 pinned source/configuration files
- 424 original dependency/helper outputs
- 17,505 official toolchain files
- 115 final project source/output/wrapper files
- All 56 live formal source files

Main theorem source SHA-256:
`0cfa1200ea02ebdb5e59df976c8d29301520ec3704c05853c7150684ae37374d`.

[The machine-readable result](../results/formal_universality.json) and
[complete evidence directory](../artifacts/universality-proof-2026-10-07/)
preserve source/object identities, all module build logs, exact theorem types,
axiom queries, wrapper sources, guard receipts and canary results.

## Reference-code regression

The complete 693-test reference suite passed in 799.369 seconds with exit 0.
The eight subsequently added portable-replay helper tests also passed. Thus
all 701 current test methods passed across those two runs. The helper
preflight verified the existing official Lean version and all 482
project/upstream source/config hashes without rebuilding proofs.
[Regression results and logs](../results/final_reference_tests.json) preserve
the exact scope and commands. The portable source-rebuild instructions are in
[formal/README.md](../formal/README.md).

## Mathematical and interpretation boundary

The kernel endpoint is uniform finite-register-machine simulation with exact
first-event numerical output. The standard two-stack Turing-machine reduction
in [the source proof](universal-bp2-front-end.md#7-why-the-chosen-source-suffices-for-arbitrary-effective-computation)
supplies the written universality metatheorem. Complexity is measured in
finite occurrence-tree size; compressed-DAG complexity is a separate model.

This is computation along the specified fixed finite-controller S trajectory
with a regular observation event. Prize interpretation, priority and acceptance
require external assessment. No prize claim or external submission is implied
by a successful kernel check.
