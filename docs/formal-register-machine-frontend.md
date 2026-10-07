# Kernel-checked finite-input register-machine frontend

## The exact compiler proved

`SOnlyMachineNat.compile M input` is a total Lean function that emits a finite
list of ordinary numerical BP2 commands. Its source has `D = d+1` natural
registers and `Q = n+1` labels. Instructions are arbitrary well-formed
`INC(i,t)`, `DECJZ(i,positive,zero)`, and `HALT`; well-formedness is enforced by
finite register/label types. `input` is an arbitrary tuple of natural numbers.
No source execution, proposed runtime bound, or halting answer is used during
compilation.

BP2 increments add one. A decrement at a positive value subtracts one and
advances; a decrement at zero sets that counter to one and restarts at the
first command while retaining all other counters. Falling off the finite
command list is termination. The total iteration used in the proofs preserves
the final state afterward. Every target counter starts at zero.

The main results are:

- `SOnlyMachineNat.compile_bounded`: all zero-based counter labels are below
  `counterCount d n`.
- `compile_dense`: every label in that range actually occurs in the code.
- `counterCount_pos` and `compile_nonempty`: the counter alphabet and code are
  nonempty. Adding one to the zero-based labels gives exactly the published
  positive labels `1,...,counterCount d n`.
- `SOnlyMachineNat.halt_iff`: the actual compiled BP2 program terminates if and
  only if the source machine terminates on the supplied input.
- `SOnlyMachineNat.halt_output`: every actual halted BP2 state has first counter
  `2v+3`, where `v` is the source's final register zero.
- `SOnlyMachineCorrectness.output_iff`: for each specified natural result `v`,
  BP2 terminates with first counter `2v+3` if and only if the source terminates
  with register zero `v`.
- `every_halt_reads_result`: the fixed source-independent reader `(x-3)/2`
  recovers the value at any supplied source halting index, at every target
  halting index. Source halt absorption and determinism establish uniqueness.

These are quantified execution theorems, not fixture theorems or wrappers that
assume the desired simulation. The proof explicitly executes all compiled
initialization, scan, trigger, test, and exit instructions.

## Deliberate differences from the written/Python variant

The construction follows the reduction in
[the written frontend](universal-bp2-front-end.md), but it is a separate,
semantics-preserving formal variant:

1. It allocates all five auxiliary counters `I/S/F/U/V` at **every source
   label**, including labels whose instructions do not use them. Scans traverse
   the complete label order. Unused successful edges halt, and the scan theorem
   proves that those edges are never reached in a simulated instruction.
   Thus the amnesiac counter count is `k = D + 5Q`, not `D + I + 4J`.
2. It uses the same normalized Waterfall vector `V` and the same nonnegative
   rows, but initializes the clocks at `V+5`, not `V+1`. The checked delay
   theorem handles every positive integer offset; this alters finite startup
   time and syntax size but not event order or final output.
3. Clock order is explicit and interleaved per amnesiac counter. Dense
   relabeling preserves register zero as numerical counter zero.

Consequently this proof does **not** claim byte-for-byte equality with the
selective Python reference compiler, nor does the older
`168k²+124k+19+4s` command formula describe this formal compiler.

## Effective size bounds

Let `s` be the sum of the input registers and set

- `k = D + 5Q`
- `N = 4k+1` Waterfall clocks
- `C = 2N+1 = 8k+3` BP2 counters.

`SOnlyMachineBounds.counterCount_exact` proves the stated counter count.
`SOnlyMachineBounds.compile_length_bound` proves the conservative bound

```text
L <= 2C(2s+9) + N(18C+2) + C + 4N + 4.
```

This is a polynomial in the finite source dimensions and unary input size.
Its proof uses the explicit finite enumerations, literal unary expansion,
input-coordinate bounds by `s`, and the kernel-checked bound that every
Waterfall row entry is at most nine. It has no runtime or halting premise.
In particular, compiling does not attempt to decide whether a source halts.

A sharper counting calculation for this exact variant gives

```text
initializer          4s + 76k + 14
nonhalt trigger      168k² + 44k
halt trigger         16k + 6
sweep/tests/exit      20k + 7
--------------------------------
total                168k² + 156k + 27 + 4s
```

The exact command-count identity above is a mathematical count of the emitted
blocks, not a separately formalized Lean identity. The conservative polynomial
bound is the kernel-checked size guarantee. Three small compiler-length
transcription checks produced `7011`, `7023`, and `26115`, matching the sharper
count; these examples are not used in any correctness or size proof.

## Proof layers

1. `SOnlyMachine.lean`: finite source syntax, padded amnesiac compiler, exact
   marker scans and INC/DECJZ macros, arbitrary source runs, halting reflection,
   and retained registers.
2. `SOnlyMachineBP2.lean`: literal BP2 semantics, successful block execution in
   arbitrary surrounding code, arbitrary unary addition/cancellation, active
   guards, and restart-safe initialization.
3. `SOnlyMachineWaterfallBP2.lean`: the actual finite Waterfall compiler,
   ordinary ticks, unique-zero detection, both event restarts, arbitrary
   positive delays, and falling-off halt with final vector `y+1`.
4. `SOnlyMachineClock.lean`: complete explicit Waterfall row arithmetic,
   positive rows and tie-free minima, actual amnesiac-to-BP2 simulation,
   all-zero startup, cofinal arbitrary runs, and two-way halting/output.
5. `SOnlyMachineFinite.lean`: effective bijective dense numbering and exact
   run transport, composition with the register source, density, and the first
   output coordinate.
6. `SOnlyMachineNat.lean`: the natural-label interface consumed by the UT19
   source compiler; projection of every actual run and the final public
   halting/output theorems.
7. `SOnlyMachineBounds.lean`: effective alphabet sizes and a safe polynomial
   bound for this formal variant.
8. `SOnlyMachineCorrectness.lean`: unique final source state and result-specific
   equivalence, independent of the choice of halting index.

The main frontend halting, output, result-equivalence, and size theorems were
checked with the pinned official Lean 4.33.1 toolchain. Their printed axiom
sets contain only `propext` and `Quot.sound`; none uses `sorryAx`,
`Classical.choice`, an added axiom, or a native-decision shortcut.

This frontend proves the reduction for arbitrary finite register machines. It
does not itself formalize a Turing-machine-to-register-machine compiler. That
standard source-model universality argument remains separately described in
the written frontend. The BP2-to-UT19 and fixed-CTS-to-S layers are separate
proof modules and must be composed to obtain the complete S theorem.
