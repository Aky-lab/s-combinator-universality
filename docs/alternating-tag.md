# Finite-alphabet alternating tag to ordinary binary CTS

This independently authored compiler translates any fixed, nonempty finite
alphabet and immutable production table to ordinary binary CTS semantics.

## Exact source convention

Let the alphabet be `{0, ..., m-1}`, with `m >= 1`, and let `P[i]` be a finite
word over this alphabet. A configuration is a finite queue `w` and a phase
`take` or `skip`. If `w = i v` is nonempty, a microstep is

```text
(i v, take) -> (v P[i], skip)
(i v, skip) -> (v,      take).
```

Only an empty queue stops. In particular, a singleton in take phase appends
its production before the following skip can occur. There is no stop rule for
a selected symbol, a short nonempty word, or recurrence.

This convention must remain distinct from conventional deletion-two tag
semantics that stop whenever fewer than two symbols remain. A take/skip pair
starting with at least two symbols agrees with a conventional deletion-two
step. For a singleton that equivalence fails: with `P[0] = (1,0)` and
`P[1] = ()`, `(0; take)` cycles through `(1,0; skip)` back to `(0; take)`.
The conventional system stops at its initial singleton. Both stop on empty
input; take and skip remain distinct stopped boundary phases.

## Compiler and boundary language

Define

```text
E(i) = 0^i 1 0^(m-i-1)
E(i1 ... in) = E(i1) ... E(in),   E(empty) = empty.
Q = (E(P[0]), ..., E(P[m-1]), empty, ..., empty).
                                      m empty appendants
B(w, take) = (E(w), 0)
B(w, skip) = (E(w), m).
```

`Q` has exactly `2m` ordinary binary CTS phases. On every CTS step one bit is
deleted; a deleted `1` appends the current appendant, a deleted `0` appends
nothing, and the phase advances modulo `2m` in either case. This is exactly
`s_only.cts`, including its empty-queue stop behavior.

`decode_boundary` accepts only phase `0` or `m`, a word length divisible by
`m`, and exactly one `1` per block. It returns the encoded queue and phase,
without running the source or consulting a trace. It recognizes a structural
language; acceptance is not proof of reachability from a chosen seed.

## Exact-step simulation lemma, including empty and singleton queues

For every nonempty source configuration `s`, all `m` ordinary CTS steps from
`B(s)` exist, and their final configuration is `B(step(s))`.

Proof: write its head as `i`. In the first `m` CTS steps, the bits being deleted
are precisely the original `E(i)`: appending at the back cannot change which
original bit is next. Before deletion number `t+1`, for `0 <= t < m`, at least
`m-t` original head-block bits remain. Thus the queue cannot become empty
before all `m` deletions, even for a singleton and an empty production.

In take phase the CTS phases are `0, ..., m-1`; its unique deleted `1` occurs
at offset `i` and appends exactly `E(P[i])`. The final queue is `E(v P[i])`
and the final phase is `m`. In skip phase the phases are `m, ..., 2m-1`, all
appendants are empty, and the final queue is `E(v)` at phase `0`. These are
the two required boundaries. This argument includes `m = 1`.

If the source queue is initially empty, its encoded CTS queue is also empty:
neither has a next step. If a source microstep empties the queue, the CTS
queue first empties exactly at the end of its `m` steps. By induction, every
existing source prefix of `j` microsteps corresponds to exactly `mj` CTS
steps. Empty termination occurs at the same boundary. The lemma concerns
unbounded mathematical transition relations; an evaluator may separately
stop at an explicit resource limit.

## Selected-symbol event and exact offset

Fix `h` in the alphabet. For a current CTS configuration define

```text
H_h(c) := c.phase == h and c.word begins with 1.
```

This is a fixed-size check when the program is fixed. Let `s_j` be a nonempty source
prestate at zero-based microstep `j`, starting at either encoded boundary
phase. Along the correctly encoded ordinary CTS trajectory,

```text
s_j has phase take and head h
    iff H_h(c_(mj+h)).
```

Moreover, *every* occurrence of `H_h` lies at one of these offsets and comes
from a take-phase head `h`. In each block the phase is either `t` (take) or
`m+t` (skip); only offset `t = h` of a take block can have phase `h`, and its
bit is `1` exactly when the source head is `h`. In a skip block, an ignored
head `h` appears at CTS phase `m+h` and must not signal. Empty trajectories
have no selected event.

A source event logged after microstep `j+1` describes the prestate `s_j`.
`selection_position` returns CTS prestate index `mj+h` and CTS logged-step
index `mj+h+1`. It returns `None` for skipped symbols, including skipped `h`.
Its event numbering must start at the initial boundary used for CTS encoding;
it checks event/table consistency but cannot prove a fabricated event occurred.

This supplies the designated-production premise of
[event composition](event-composition.md). It does not supply a theorem that
selection of `h` is equivalent to some independently defined machine's halt,
nor an S encoder, selector, or bounded S reader. Those are separate obligations.
For this partial transition system, event offsets refer to existing prestates;
a compatible totalization may keep an empty configuration unchanged forever,
which creates no `H_h` event. A different totalization needs its own check.

## Bounded executable interfaces

`s_only.alternating_tag` exports:

- Immutable `Program(productions)` and `Configuration(queue, phase)`.
  Productions and queues are tuples; symbols are exact integers, not booleans.
  Public entry points require exact source object classes, rejecting subclasses
  that could replace immutable fields with mutable properties.
- `step(..., max_queue_symbols=N)` and deque-backed
  `Machine(..., max_steps=J, max_queue_symbols=N)`.
- `evaluate(...)`, returning the final configuration, executed step count,
  peak queue size, `empty` or `step_limit`, selected-event count, and first
  selected-event position. It stores no unbounded event history. A requested
  next step exceeding the queue bound raises `ResourceLimit`.
- `compile_program(..., max_phases=F, max_program_bits=B)`, with separate
  limits on phase-table entries and the total number of appendant bits.
- `encode_word` and `encode_configuration`, with a mandatory output-bit bound.
- `decode_boundary`, with both input-bit and output-symbol bounds.
- `selected_cts_event`, `selection_position`, and `simulation_bounds`.

CTS reader/predicate inputs must be exact, normally constructed
`cts.Configuration` objects with plain `str` words and nonnegative exact `int`
phases. Subclass overrides are rejected. The CTS constructor establishes binary
word validity; the event predicate does not repeat that linear scan. As with
other frozen dataclasses, deliberate low-level mutation bypassing the constructor
and frozen-field protections is outside the value contract.

Compilation checks *all* output lengths before generating any encoded
production. No `m` by `m` code table is allocated. Encoding, decoding, and
evaluation allocate only proportional to explicitly bounded output or current
queue size, plus the input program. Input objects themselves are already
materialized and their validation takes time proportional to input size.
Limits are not byte-exact Python heap limits; run in an OS resource envelope
when that is needed. Queue and step bounds are checked before state mutation;
`MemoryError` from the host is not a transactional resource-bound guarantee.

If source boundaries have at most `N` symbols, CTS boundaries have at most
`mN` bits, but **that alone is not always a sufficient CTS memory bound**.
When a take head `i` appends its production, before the trailing zeros of its
code are deleted, the CTS word has the final boundary's size plus
`m-i-1` bits. A uniform sufficient bound is `mN + m-1` (`0` when `N=0`).
`simulation_bounds` returns this bit bound and `mJ` steps. For example,
`m=3`, `P[0]=(0)`, and singleton head `0` has three-bit boundaries but a
five-bit intermediate queue. Resource-limited CTS execution with only three
bits would reject a valid source microstep; it would not refute the lemma.

## Independent checks

The tests exhaust all tables whose productions have length at most two,
all queues of length at most two, and both phases, for `m=1,2,3`:
**57,826 boundary configurations**. Each nonempty case checks exactly `m`
ordinary CTS steps, the boundary parser, all selected-symbol events, and
independent list-based source and literal-bit encoding oracles. Additional
multi-step exhaustive domains, empty and singleton cases, transient memory,
ignored selected symbols, immutable values, malformed inputs, and
transactional resource failures are covered.

Run this focused suite under a 180-second wall / 1-GiB address-space envelope:

```sh
timeout --signal=KILL 180s bash -c \
  'ulimit -v 1048576; exec python -m unittest discover -s tests -p test_alternating_tag.py -v'
```

Finite tests check this implementation; the all-input simulation and event
statements rest on the block proof above.
