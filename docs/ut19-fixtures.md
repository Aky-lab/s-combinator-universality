# Compact UT19 source fixtures

These reproducible source-machine fixtures execute the published UT19 table
and compact Brainpocalypse II encoder using alternating-tag and binary CTS
transitions.

The generic one-hot translation has an exact simulation argument in
[alternating-tag.md](alternating-tag.md). The
[compact-source proof](ut19-simulation-invariants.md) establishes initialization,
restart preservation, first-event equivalence, and structural result grammar
for every source program in the specified grammar. The experiments below
check the executable implementation.

## Provenance and interface

The fixed 19-row numerical table comes from ais523's
[UT19 article, revision 154545](https://esolangs.org/w/index.php?title=UT19&oldid=154545).
Source semantics are from
[Brainpocalypse II, revision 172507](https://esolangs.org/w/index.php?title=Brainpocalypse_II&oldid=172507).
Both wiki articles carry a CC0 dedication. This implementation was derived from
the published mathematical construction and the
[local reconstruction](compact-universal-programs.md#source-level-encoder-formulas).
The independently written encoder follows these mathematical formulas.

`s_only/ut19.py` exposes:

- Immutable `Command(counter, delta)`, `SourceProgram(commands)`, and
  `SourceConfiguration(pc, counters)` with strict integer and tuple validation.
- `parse_source`, `initial_source`, and a bounded pure `source_step`.
- The exact, published one-based `UT19_PRODUCTIONS`, and `TAG_PROGRAM` converted
  to the generic alternating-tag API's zero-based labels.
- `running_xor_initial`, `EncodingLimits`, and `encode_source`.
- `compile_cts`, which has exactly 38 phases, 18 nonempty appendants, 760
  appendant bits, 40 appendant ones, and maximum appendant length 76.
- `selected_source_event`, a pre-transition test for taking published symbol 18.

The numeric source syntax is deliberately restricted to nonempty programs
using dense positive counter labels `1,...,C`. Every command has delta `+1` or
`-1`; all counters initially equal zero. A decrement of zero sets that counter
to 1 and restarts at instruction 0, retaining all other counters. Reaching
instruction `L` is fall-through halting. Counter tuples and instruction pointers
are actual source configurations, not execution history or restart counters.

## Compact encoding and resource preflight

Let `L` be source command count, `C` its counter count, and `N` the least power
of two at least `L+3`. The envelope has an initialization command, the `L` source
commands, two halt-control commands, and idle commands through length `N`.
There are `C+2` memory blocks with `2N` width bits each and `C+1` initially zero
counters, including the added halt counter.

The encoder applies the explicit width formulas in the reconstruction note.
Its running-XOR transform is

```text
a_i = XOR { v_j : (i AND j) = i }.
```

An in-place butterfly computes this transform on a bounded copy. The tests use
both a separate quadratic subset-enumeration oracle and a temporal oracle
that repeatedly replaces cell `i` with the XOR of old cells `0,...,i` and
observes the parity of the whole memory. All width vectors of lengths 1, 2, 4,
and 8 are checked, including the transform's self-inverse property.

For every transformed bit, emit `[5,6]` when zero or `[5,6,1,1,19]` when one.
A zero counter is `[12,13,12,13]`. The seed starts with `[19]`, then alternates
memory blocks and zero counters, ending with memory. It contains no cleanup
padding. If `I` is the total number of transformed ones, its exact size is

```text
seed symbols = 1 + 4(C+1) + 4N(C+2) + 3I
seed bits    = 19 * seed symbols
seed symbols <= 1 + 4(C+1) + 10N(C+2).
```

Dense labels imply `C <= L`, so this seed-size bound is quadratic in the number
of explicitly written source commands. It is not a bound for every possible
encoding of a source machine or its input.

Preflight is staged so a small exact output cap remains usable:

1. Reject source command/counter caps and total memory-vector-entry caps before
   allocating vectors. Also reject an already-impossible seed-size lower bound.
2. Construct bounded width and transformed vectors; count exact inverter and
   seed sizes.
3. Check exact tag-symbol and binary-bit limits before materializing the seed.
4. Check the CTS output limit before constructing its binary word.

`max_memory_entries` bounds `2N(C+2)` entries **per vector family**. Both desired
and initial families are retained, for twice that many entries; a transform
also uses a temporary bounded copy of one vector. This parameter is an entry
count, not a RAM-byte estimate. All parser/encoder/simulator bounds reject
booleans, negative values, and non-integers. Source entry points reject
subclasses of the immutable source types to keep preflight inputs stable.

`source_step` checks counter count, existing values and the prospective changed
value before copying a counter tuple. The report separately bounds source
steps, tag steps, CTS steps, queue sizes, and the total symbol count held by
exact recurrence-state keys. A resource failure raises an error; it never
becomes an asserted halt or completed certificate.

## Exact observed fixtures

[The machine-readable report](../results/ut19_source.json) records full table
and seed hashes, width vectors, exact event configurations, recurrence
certificates, limits, and independently evaluated BP2 results.

| Source | Seed symbols / bits | First event or recurrence | Peak tag symbols / CTS bits |
| --- | ---: | --- | ---: |
| `+1` | 90 / 1,710 | Event after 1,508 tag steps, before CTS step 28,670 | 111 / 2,124 |
| `-1` | 90 / 1,710 | Event after 2,476 tag steps, before CTS step 47,062 | 111 / 2,124 |
| `-1 -1` | 144 / 2,736 | Equal tag configurations at 1,562 and 4,124 | 175 / 3,340 |

For `+1`, the separate BP2 evaluator halts after one increment with counter 1
holding 1. For `-1`, it restarts once, then decrements 1 to 0 and halts after
two commands. The [structural readers](ut19-readout.md) independently recover
these same tuples from the actual tag and CTS event configurations. The report
records all three results and asserts their equality.

The event predicates are both pre-transition:

```text
UT19: take/produce phase and head label 18
CTS:  phase 17 and first bit 1
```

At a tag event after `k` completed source microsteps, the one-hot CTS has
completed `19k + 17` steps when this predicate is first true. Its logger would
number the selecting transition `19k + 18`, but the report stops before that
transition. Thus the positive fixtures' completed CTS counts are **28,669**
and **47,061**. The 17-bit offset consumes the leading zeros of the selected
one-hot symbol; it does not consume the selecting one or append its production.

All complete one-hot boundary states were checked for exact equality at every
19 CTS steps: 1,509 boundaries for `+1`, 2,477 for `-1`, and 4,125 for `-1 -1`.
Every intervening CTS prestate was checked for an earlier or spurious event.
The peak CTS sizes include partial-block growth, rather than merely multiplying
the largest complete tag queue by 19. An ignored 18, or an 18 elsewhere in the
queue, is not the designated event. The ordinary CTS has no special halt token.

### Event-free recurrence certificate

For `-1 -1`, the complete tag configuration (queue and take/skip phase) at step
1,562 repeats at step 4,124. Equality is checked on the full immutable state,
not merely its hash. The corresponding CTS states, including phase, are equal
at steps 29,678 and 78,356. Therefore the periods are 2,562 tag microsteps and
48,678 CTS steps.

The report checks all 29,678 CTS prestates in the prefix and all 48,678 in the
cycle: no selected event and no empty queue occurs. The tests replay the whole
trace using a separately written literal-table/string interpreter and then
replay one additional complete cycle. Determinism and exact recurrence prove
an infinite event-free, nonempty execution for **this particular seed**.
This is stronger than a trace that merely fails to halt before its bound;
it does not establish correctness of the encoder on arbitrary source programs.

The recurring tag configuration's SHA256 is
`3d39058c4321b474650dc1e3ed30f318ada549387bf9fe5a71590606c7627482`.
The recurring CTS configuration's SHA256 is
`a73af680d95363b7a081d87b39936e94bddc14067d10880c7617f1d00864f6fc`.
Full recurring tag symbols and prefix/cycle trace hashes are in the report.
Configuration hashes use compact, sorted-key JSON, with published one-based tag
labels. A boundary-trace hash is the SHA256 of concatenated raw 32-byte
configuration hashes, one per source prestate, with the repeated endpoint
excluded. The certificate's equality checks do not depend on hash collision
resistance.

## Reproduce

From the repository root, with Python's standard library only:

```sh
(ulimit -v 1048576; timeout 180s python -m tools.ut19_source_report \
  --output results/ut19_source.json)
(ulimit -v 1048576; timeout 180s python -m unittest discover \
  -s tests -p 'test_ut19*.py' -v)
```

The report has no timestamp or timing-dependent field; regenerations are
byte-identical. Tests cover exact table expansion, the three literal seeds,
source restarts and retained counters, small dense-program size accounting,
independent running-XOR oracles, strict validation, immutable input types,
allocation preflight, event offsets, exact cycle replay, and report determinism.
The 180-second/1-GiB external guards apply to each command. No package installs
are needed. The source report completes in roughly one second in the current
workspace; that observation is not a portable performance guarantee.

## Connections to the S backend

The source proof and generic one-hot lemma provide a fixed 38-phase CTS with
an exact designated event and preserved counter results. Native S integration
requires its fixed controller, a corresponding S event observer, and a
structural output-reader composition. Arbitrary-machine/input compilation into
BP2 also needs a restart-safe initializer. Empty-queue cleanup follows a
different interface from the designated event used here.
