# Structural result readout at the compact UT19 first event

[`s_only/ut19_readout.py`](../s_only/ut19_readout.py) reads the ordered tuple of
natural-number results from the **current configuration only**. Its two entry
points are:

```python
read_tag_result(state: alternating_tag.Configuration, *,
                limits: ReadoutLimits = ReadoutLimits()) -> tuple[int, ...]
read_cts_result(state: cts.Configuration, *,
                limits: ReadoutLimits = ReadoutLimits()) -> tuple[int, ...]
```

The tag input uses the repository's **zero-based** symbol indices and must be
in take phase with head index 17. The ordinary CTS input must have phase 17
and head bit one, with the more precise suffix structure below. Neither reader
accepts a source program, expected counter count, seed, step number, trace,
evaluator, or S term. The implementation imports no source encoder and calls
no tag or CTS transition, one-hot boundary parser, or history search.

This closes the source/ordinary-CTS **result decoding** obligation under the
[first-event simulation theorem](ut19-simulation-invariants.md). The theorem
supplies reachability and firstness; the reader checks syntax and extracts the
result. An S-level checkpoint/event selector and its structural composition
with this reader are separate obligations. These files add no S reduction
experiment or S-combinator universality claim.

## Accepted structural language

All symbols in the grammar in this section are **published one-based labels**.
Let concatenation be implicit, `?` mean zero or one copy, and `+` mean one or
more copies. Define

```text
R = ([18,10] [18,4]?)+
T = (([10,10] | [11,10]) [4,4]?)+
K(x) = [16]^(4^(x+1)), x a natural number.

Q = R_1 K(x_1) R_2 K(x_2) ... R_C K(x_C) R_(C+1) T,
    for any finite C >= 1.
```

The tag reader accepts exactly `(Q, take)` within its resource bounds. It
returns `(x_1,...,x_C)`. Each `R` and `T` is nonempty, and an inverter is
permitted only immediately after a cell, at most once for that cell. The final
two memory blocks are adjacent because the halt counter has disappeared.

The actual proof gives `R_(C+1)=R_H`, the final memory `T`, a common number `W`
of cells, and specific inverter bits determined by the source program. The
reader deliberately accepts the **source-independent structural superlanguage**
above: the cell counts may differ across memories, need not be powers of two,
and the inverter bits and final cell states may be arbitrary. It neither tests
initializer equality against a source program nor tries to infer such a program.
Those restrictions are unnecessary to identify counter runs and their values.

This is stricter than an alphabet-only run decoder. For example,
`[18] [16]^4 [10,10]` has the allowed alphabet, event head, and a valid run,
but is rejected because its memory components are malformed. Repeated inverters,
inverter-only memories, missing memories, truncated cells, and trailing material
outside `T` are rejected too. However, deleting a whole final-memory cell can
leave another accepted word if `T` remains nonempty. Without a source or history,
the reader cannot distinguish that word from another structurally valid input.
Acceptance is never a certificate of reachability, firstness, or source identity.

`C=0` is excluded because the compact source grammar requires a nonempty program
with at least one used counter. There is no fixed upper counter count imposed by
the 19-symbol alphabet; the caller sets a finite resource cap.

## Why the decoded tuple is correct at the first event

The simulation proof's exact event-stage word is of the form `Q` above. Every
memory contains no 16, and every counter is a nonempty 16-run. Therefore the
maximal 16-runs of `Q`, from left to right, are precisely the `C` ordinary source
counters, without merging or a spurious halt-counter run. Their proved lengths
are `4^(x_k+1)`.

The reader consumes one `R`, then a complete 16-run, repeating until the final
`R T`. For a run length `n`, it checks:

1. `n >= 4`;
2. `n & (n - 1) == 0`, so `n` is a power of two;
3. `n.bit_length() - 1` is even, so `n` is a power of four.

It returns `(n.bit_length() - 1) // 2 - 1` for that run. This is exactly `x_k`.
It uses no floating logarithm and never constructs `4**x` or any other large
exponent to validate an input. The integer `n` counts only the already supplied,
bounded symbols.

The parser requires the whole input to finish in the final-memory grammar.
Conversely, every word in the displayed language passes these checks when its
budgets suffice: each `R` parser consumes exactly its cells/inverters, every
`K` passes the run test, and the final `T` parser reaches end of input. Thus the
language is explicit rather than an empirical predicate fitted to samples.

## The ordinary CTS event is 17 bits past the boundary

The fixed one-hot encoding uses 19-bit blocks

```text
E(s) = 0^(s-1) 1 0^(19-s).
```

At the tag event the head is published symbol 18. Its code starts with 17
zeroes, followed by `10`. The corresponding **ordinary CTS pre-transition
event** is at phase 17 after those zeroes have been removed and before its one
is consumed. No appendant has yet been added in this block. Therefore

```text
E(Q) = 0^17 y,   where y = '10' E(Q without its first symbol).
```

`read_cts_result` checks the exact phase, that `y` starts with `10`, and that
`len(y) + 17` is a multiple of 19. It then yields the logically restored head
symbol 18 and decodes successive whole 19-bit one-hot blocks starting at offset
two in `y`. Every block must have exactly one one and eighteen zeroes, with its
symbol in the Reset alphabet. The same Reset parser consumes these symbols.

There is no allocated restored binary word and no materialized decoded queue.
This is equivalent to restoring the 17 zeroes and decoding at a boundary, but
does not confuse a phase-17 current state with a phase-zero block boundary.
A whole encoded `E(Q)` passed at phase 17 is rejected. Phase 36, the corresponding
position during a skip block, is rejected even when its head is one. An 18
elsewhere in a tag queue is also insufficient.

## Bounds, types, errors, and cost

`ReadoutLimits` is an exact frozen, slotted dataclass. Its fields are plain
nonnegative integers, with these caller-adjustable defaults:

| Field | Default | What it bounds |
| --- | ---: | --- |
| `max_queue_symbols` | 1,000,000 | Entire tag queue, or CTS queue's logically restored symbol count |
| `max_word_bits` | 19,000,000 | Actual supplied CTS suffix bits; the virtual 17-zero prefix is not charged |
| `max_counters` | 100,000 | Number of returned values |
| `max_output_bits` | 1,000,000 | Sum of `max(1, x.bit_length())` for returned values |

Zero occupies one binary output digit. Thus `(0,1,2,3,4)` uses nine output bits.
The output-bit cap counts numeric payload, not Python object overhead; the
counter-count cap separately bounds the number of objects. `max_word_bits` is
irrelevant to a tag input because it has no binary string. A zero applicable
cap can refuse otherwise valid input.

The readers require exact configuration classes, a plain immutable tuple of
plain integers for tag data, a plain string for CTS data, and plain phase and
limit field types. They reject subclasses, booleans masquerading as integers,
and malformed fields even if a caller bypassed a configuration constructor.
The input configurations are never mutated; no whole input is copied. Budget
fields are rechecked at reader entry.

After those constant-size shell/phase checks, both relevant input-size caps are
checked before scanning content. The counter cap is checked before retaining
each new value, and the cumulative output-bit cap is checked before appending
that value. A limit violation raises the repository's `cts.ResourceLimit`; a
type, phase, code, alphabet, grammar, or run-length failure raises `ValueError`.
A malformed oversized input can hit a resource limit before its malformed
content is examined. Neither exception class means the source does or does not
halt.

The parser makes a single forward traversal, with bounded 19-character block
temporaries for CTS and constant-size memory grammar state. Besides the returned
values and their bounded temporary list, it retains only a cursor, run length,
and budget counters. It performs `O(n)` symbol/bit visits for `n` input symbols
or bits; run-count integer arithmetic has the usual cost in `O(log n)`-bit
integers. Output values themselves need at most `O(log log n)` bits each.
No unbounded recursion, regex backtracking, code table, trace cache, or evaluator
is involved. These bounds are refusals against supplied finite data, not a
total halting procedure or a bound on reaching the event.

## Independent tests

[`tests/test_ut19_readout.py`](../tests/test_ut19_readout.py) builds its words
directly from the grammar. It does not obtain expected output from a source
interpreter, use the source encoder for synthetic words, or execute a tag/CTS
trajectory. Its offset test implements the 17 literal zero-deletion steps only.

Coverage includes:

- Both complete first-event queues in `results/ut19_source.json`: `+1` decodes to
  `(1,)`, and `-1` decodes to `(0,)`; the reconstructed CTS states match the saved
  whole-configuration hashes.
- 156 combinations of one through three counters, values zero through two, and
  memory widths 1, 2, 3, and 8; further values through four; all three-cell
  inverter/state choices; unequal memory widths; and a 1,025-counter word.
- Malformed heads, phases, alphabet symbols, one-hot blocks, counter lengths,
  Reset cells, optional inverters, final memories, and incomplete bit blocks.
- The proof-sharp 17-bit CTS offset, wrong boundary representations, skipped
  18s, and 18s that are not the head.
- Exact input-size/count/output-bit boundaries, zero budgets, preflight order,
  immutable/plain field checks, subclass rejection, and repeatability.
- Patched evaluators, encoders, and the ordinary boundary parser that raise if
  called during readout.

Run from the repository root using only the Python standard library:

```sh
timeout 180s sh -c 'ulimit -v 524288; python -B -m unittest discover -s tests -p test_ut19_readout.py -v'
```

Verified 6 October 2026: all 18 tests passed under these 180-second/512-MiB
process limits. Finite tests check this implementation; the grammar argument
and linked source/one-hot simulation proofs give the stated conditional result.
