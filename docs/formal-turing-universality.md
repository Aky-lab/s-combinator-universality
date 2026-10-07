# Conventional Turing machines to fixed-controller S computation

7 October 2026. The complete 67-module development passed a clean source
build and fresh official Lean 4.33.1 kernel replay.

## Statement

Fix the closed-S term grammar and native rewrite

```text
term ::= S | (term term)
S x y z → x z (y z)
```

There are one fixed finite root-reset controller C, one fixed regular tree
language H, and an executable encoder E such that, for every finite-state,
finite-alphabet deterministic Turing machine M and every finite input word w,

```text
M halts on w  iff  some tree of the C-selected S trajectory from E(M,w) lies in H.
```

The source tape is genuinely indexed by all integers. Its head is an absolute
integer coordinate; a transition writes a symbol and moves left, stays, or
moves right. An absent transition means halt. The finite input occupies
coordinates zero onward, with the machine's specified blank elsewhere.

The endpoint is
[`SOnlyTuringUniversality.halting_iff_event`](../formal/SOnlyTuringUniversality.lean).
It has no simulation, tape-space, running-time, liveness, generated-origin or
eventual-event hypothesis. `halting_iff_first_event` gives the first accepted
sample; `nonhalting_no_event` excludes every finite observation of a divergent
source. `selector_executes` ties the actual trajectory to the fixed selector,
and `every_step_native` makes each adjacent pair one ordinary S contraction.

C starts at the root on every invocation. Its inter-invocation state is Unit,
and it stops within a fixed linear bound in the supplied occurrence-tree size.
Only the resulting term persists. C and H are exactly the previously checked
38-phase construction, independently of M and w.

This is fixed-selector event universality. Termination of unrestricted S
normalization is a different observation model.

## Concrete source reduction

The proof follows this explicit chain:

```text
integer-indexed tape
  → two finite symbol stacks and finite control
  → three natural registers and a literal INC/DECJZ/HALT table
  → BP2 → UT19 → fixed 38-phase CTS → closed S tree
```

### Every tape cell is represented

`SOnlyTapeStacks` stores the scanned symbol and machine state in finite
control, with nearest-first left and right lists. Empty pop returns blank.
`Represents` quantifies over every cell; `represents_read` reconstructs any
absolute tape coordinate. The step and run proofs cover arbitrary finite
inputs, empty input, blank symbols in input, all movements, and unbounded
visited intervals. There is no finite tape-window premise.

For alphabet size A, use base B=A+1 and digit `symbol.val+1`:

```text
code([]) = 0
code(a :: xs) = digit(a) + B * code(xs)
```

The code is injective, including explicit blanks. Quotient and remainder
recover the tail and top, with remainder zero mapped to blank on an empty
stack. `input_encoded_haltsAfter_iff` connects the actual tape semantics to
the two-natural arithmetic representation.

### Literal finite instruction blocks

`StackMacros` proves execution of actual INC and DECJZ rows. Push multiplies
by B and adds the fixed digit; pop decrements through a finite-control residue
cycle and transfers the quotient back. Both restore shared scratch to zero
and preserve every unrelated register.

For initial stack value a and digit d, push takes exactly

```text
((B+1)*a+1) + (2*B*a+1) + d
```

instructions. For `a=B*q+r`, pop takes

```text
((B+1)*q+r+1) + (2*q+1).
```

These counts are strictly positive, including empty pop. Concrete standalone
finite tables and small closed examples are also checked.

`SOnlyTapeCompiler` assembles the rows into one total three-register machine:
registers 0 and 1 hold the stack codes; register 2 is scratch. Finite labels
are explicitly enumerated from machine state, scanned symbol and macro phase.
The number of labels is

```text
states * symbols * (5*(symbols+1)+5) + 1,
```

including one unreachable padding halt. Lookup correctness is proved against
the literal table. The instruction table depends only on M. The entry label
selects the input's first symbol, or blank for empty input; the remaining word
is placed in the right register. This finite entry selection is part of E.

`action_executes` proves each assembled transition in strictly positive
register-machine time. Every macro row premise is discharged by the compiler.

### Halting at any target microstep

`SOnlyTapeCompilerCheckpoints` supplies cofinal checkpoint simulation: n
successful source steps yield a target checkpoint after at least n microsteps.
If the target halts at microstep t, either the source has already halted before
t source steps or its t-step checkpoint occurs at elapsed time at least t.
Absorbing target HALT makes that later checkpoint the same halted state.
Exact boundary alignment then gives source halting.

Thus internal premature halts are excluded by proof, not by checking only
macro boundaries. `input_halting_iff` exposes the concrete machine and ordinary
`SOnlyMachine.initial` interface used by the existing S-only theorem.

## Output and effective interfaces

The earlier theorem
[`SOnlyUniversality.result_iff_first_event`](../formal/SOnlyUniversality.lean)
continues to return the exact natural result of every finite register machine.
The TM extension additionally proves
`left_stack_result_iff_first_event`: at the first accepted S sample, the fixed
current-tree decoder returns exactly the code of the finite left stack in
this specified simulation.

That code includes retained blanks and visited extent. It is a well-defined
observable of the simulation history, rather than a canonical encoding of an
arbitrary final tape-output region. No tape-output normalization is implicit.

All encoder/compiler data definitions are executable. Their audited dependency
cones contain only `propext` and `Quot.sound`; `Classical.choice` occurs only
in the joined logical proof cone. The same fixed finite event cover and
all-input bounded current-tree decoder remain in use.

The finite source table is polynomial in the explicitly represented TM.
For an n-symbol input, the stack code is at most `(A+1)^n-1`, so its binary
length is O(n log(A+1)). Combined with the existing compiler bounds, E has a
singly exponential binary-description bound. Complete operation/bit-cost
arguments are written mathematics; the checked size, fuel, and finite-cover
lemmas are identified in [the register theorem](universality-theorem.md) and
[decoder analysis](lean-current-decoder-bound.md).

## Verification

- 67 project modules plus the import-only wrapper freshly built: exit 0,
  57.170 seconds, sampled peak namespace RSS 1,134,669,824 bytes
- `leanchecker --fresh -v SOnlyTuringUniversalityReplay`: exit 0,
  125.013 seconds, sampled peak namespace RSS 1,475,002,368 bytes
- 1,359 explicit declaration/type/definition queries resolved; dependencies
  limited to `propext`, `Quot.sound` and `Classical.choice`
- 426 pinned source/config files, 424 dependency outputs, 17,505 official
  toolchain files, and 136 final source/output/wrapper files rehashed unchanged
- Replay used read-only proof objects, pinned dependencies and toolchain in a
  private namespace with socket creation denied; canary objects were excluded

The same unchanged official checker passed the earlier valid-proof and
invalid-False negative controls. An independent semantic audit found no defect.
Its separate bounded transcriptions checked 29,400 assembled transitions,
2,624 pushes, 808 pops and 135,048 tape/stack transitions. These tests supplement
the universal kernel-checked statements.

The distributed helper also passed its full `--target turing` procedure in a
separate source-only workspace: 490 upstream/project modules and the wrapper
were freshly compiled, followed by a 136.142-second kernel replay. The full
procedure took 633.802 seconds. No previous compiled project/dependency files
were mounted. [Portable reproduction receipts](../results/portable_turing_replay.json)
preserve the exact helper hash, every command/status, generated object hashes,
all module logs and resource observations.

All 721 current Python test methods passed: 584 completed before an interrupted
run, and the unfinished case plus the remaining 136 passed in a resumed suite
(64.705 seconds). Discovery order and the exact completed prefix were checked.
The prior complete 693-method baseline also passed in 799.369 seconds. The
29 proof-evidence tests and 20 portable-helper tests passed independently.
[Regression receipts](../results/turing_reference_tests.json) retain the full
logs and scope of these checks.

[Machine-readable result](../results/formal_turing_universality.json) ·
[Exact theorem types and proof evidence](../artifacts/turing-proof-2026-10-07/) ·
[Source-only reproduction instructions](../formal/README.md)

Main source SHA-256:
`9a8b1e653f5e5f0c206a4be305deb24be51e7e1f7ae93e9e9a200862d02056a3`.

## Attribution

Cinematic Strawberry's pinned MIT-licensed construction supplies the generic
CTS-to-S encoding, scheduler and finite selector. Its separate 912-phase
construction already states conventional Boolean-tape universality and output
recovery. The concrete UT19 source
follows the attributed ais523 construction. This development adds the literal
source compilers, compact fixed-38 instantiation, generated first-event and
all-witness output proofs, conventional-tape composition, and independent
reproduction checks. Priority and challenge acceptance require separate
assessment of the stated model and prior work.
