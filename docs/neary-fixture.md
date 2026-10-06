# Compact binary-TM-to-CTS fixture

This fixture independently implements the left-moving construction in Turlough
Neary's *Small universal Turing machines* (2008), Theorem 4.3.2, printed
pages 65-75, [primary thesis PDF](https://tilde.ini.uzh.ch/users/tneary/public_html/tneary_Thesis.pdf).
It connects a small source machine to an ordinary cyclic tag system (CTS).

## Machine and encoding

The source machine has two states, including halt, and symbols `a,b`, with
blank `b`:

- `(q1,a) -> (b,L,q2)`
- `(q1,b) -> (a,L,q2)`
- `q2` halts

Both examples begin with two tape cells and the head on the second cell.
Tape `bb` becomes `ba`; tape `ba` becomes `bb`. In both outputs the head is
on the first cell. Head indices in JSON are zero-based.

The thesis sets `z = 60|Q| + 121`, so here `z = 241` and the program has
`2z = 482` appendants. In a one-hot word of length `n`, offset `k` means
`0^k 1 0^(n-k-1)`:

- `H1`: length 482, offset 110
- `H2`: length 482, offset 170
- encoded `a`, `b`, and infinite blank boundary `B`: length 482, offsets 1, 2, 3
- counter `mu`: length 241, offset 7

The primary seed is `H1 B mu^4 B b-hat b-hat`, with 3,374 bits and initial
phase 0. The second seed replaces only its final encoded symbol with `a`.
The tape-length counter has four objects because there are two cells plus
two boundary objects. The same compiled program runs both seeds.

## Table expansion

`s_only/neary_fixture.py` expands Tables 4.3.1-4.3.7. The state-dependent
transition rows are specialized to `q1`; the final-state self-copy rule is
from the halt paragraph on page 75. Table assignments are conflict-checked.
The construction includes the spare-capacity flag and doubling rows even
though these two examples do not exercise them.

The summary tables explicitly omit identity-copy rows. The implementation
expands those rows for the object types present at their respective stages:

- Table 4.3.3, phases 20 and `z+20`: primed tape, marked tape, and primed/marked counter
- Table 4.3.4, phases 30 and `z+30`: the same copies, plus the explicit full-to-short dummy row
- Table 4.3.5, phases 40 and `z+40`: marked tape and marked counter copies; the other rows are explicit

There are 128 specified appendant indices, including two specified empty
appendants that erase dummy symbols. The other 354 entries are filled with
epsilon. This deterministically completes unused entries for the two valid fixture seeds.
Each generated entry carries its table provenance.

Ordinary phase rotation visits all 482 indices. Selecting an appendant means
consuming a `1` at that phase; consuming `0` only deletes the bit and advances
the phase. Both runs check **every consumed-1 event** and reject any selection
of an unspecified entry. The report lists the selected indices separately
from phase coverage. Each run consumes 139 ones and 60,111 zeros. Each of the
482 phases also occurs while consuming a zero.

## Executed results

Both cases have these measured checkpoints:

| Observation | Ordinary CTS step count |
| --- | ---: |
| Initial, structurally decoded source configuration | 0 |
| Structurally decoded `q2` result at phase 0 | 55,912 |
| First consumed-1 event selecting halt appendant 170 | 56,083 |
| Exact nonempty boundary configuration repeats | 60,250 |

The peak dataword size is 5,187 bits. At the output boundary the dataword has
4,338 bits and its counter is `mu/ mup mu/ mup`, as allowed by the overlapping
counter pass described on page 74. The repeat period is 4,338 ordinary CTS
steps. The default hard limits are 100,000 steps and 16,384 queued bits.

The designated source halt is appendant `alpha_170 = H2`, which copies the halt
token while the queue stays nonempty. Source-state decoding, the subsequent
halt-token event, and exact ordinary CTS recurrence are recorded separately.
Recognizing the designated token prevents confusing other source loops with halting.
The generic interpreter has no knowledge of source states or halt tokens.

## Structural decoding and independent checks

The macro-boundary decoder parses the binary word directly at phase 0:
ordinary stage-1 state, right-side tape, boundary, correctly sized counter,
boundary, and left-side tape. It reconstructs tape order and head position
from that structure. A head index of `-1` represents the implicit blank
boundary immediately left of the stored tape, which the thesis permits. The
`source_step` reference helper covers an in-window `q1` step; the two executed
fixtures stay within that input domain. Boundary extension is a later source-model test.
The structural parser rejects marked tape, partial tokens, trailing bits,
wrong phases, and counter capacities inconsistent with tape length. It does
not use an expected step number to recognize a boundary.

The tests independently expand every appendant using literal `Q=2` indices
and independently replay all 60,250 steps per input using string operations.
They compare binary output words, checkpoint hashes, peak size, selected
appendant indices, and the halt-token event. Separate exhaustive short-word
checks compare the deque interpreter against a list-based interpreter.
Budget overruns leave the unexecuted step unchanged and cannot yield a
successful fixture result.

## Reproduce

Python 3.10 or later, standard library only:

```sh
python -m unittest discover -s tests -p 'test_cts.py' -v
python -m unittest discover -s tests -p 'test_neary_fixture.py' -v
python -m tools.neary_fixture --output-dir /tmp/neary-left-toggle
```

The generator writes `program.json`, `seed-a.txt`, `seed-b.txt`, `runs.json`,
and `manifest.json`. `seed-a` means the head reads `a`, hence initial tape
`ba`; `seed-b` means initial tape `bb`. Seed text files end with a newline;
the seed hashes in `runs.json` cover only binary digits. The manifest hashes
cover exact file bytes, including that newline. The program digest covers
its canonical JSON document, including provenance. Both bounded runs finish
before any artifact is written, and emitted bytes are read back and hashed.

## Scope and remaining bridge

The implemented scope is a fixed two-state, left-moving source machine and
two length-two inputs. Further validation covers tape extension, counter
doubling, additional programs and right-moving transitions.

The [generic closed-S encoder](cts-encoding.md) handles finite CTS program
and seed construction. Executing the resulting 482-phase program requires
its finite selector and structural source-output bridge. The
[event-composition lemma](event-composition.md) states the detector interface
needed to carry the distinguished halt-production event into S readout.
