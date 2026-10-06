# Compile-only sharing of exact controller code

`s_only.pooled_selector` is an opt-in construction-time sharing prototype.
It admits the same conservative syntax as `succinct_periodic`: one through five
phases and at most eight total appendant bits. It emits an ordinary exact
`SuccinctSelectorTable`, with no new runtime representation or interpreter.
The original compiler APIs retain their defaults and graph contracts.

## What is shared

One `_CodePool` belongs to one compilation. Its dictionaries intern two kinds
of immutable finite-code values:

- Exact `_Descriptor` records, including their local child indices and counts.
- Exact `SuccinctProbeTable` values, including the entire ordered descriptor
  tuple and root index.

Every descriptor candidate passes exact-type and plain-field validation before
hashing. Complete probe candidates pass the existing child-order and arithmetic
recurrence validator before becoming keys. The factory does not hash or compare
source pattern tuples, recursively inspect source terms, alter descriptor
indices, or identify occurrence controls. Its keys have bounded record nesting:
probe, flat tuple, scalar-field descriptors. Large integer sizes still affect
hashing cost.

Two equal descriptor records can safely share an object even when used in
different probe tables: child indices are interpreted in the containing table,
exactly as before. A whole probe is shared only when its complete indexed code
is equal. Equal occurrence trees with different identity-DAG serializations are
not rewritten or given a new normal form.

The existing row/walker compilers accept a private `_factory` hook. A new
`PooledGraphBuilder` calls those opt-in paths; original builders do not. Both
builders use the same original-order `_assemble_program` composition and the
same fragment embedding, intervals, state numbers, validators and primitive
lookup methods.

The factory does allocate a candidate record/table before finding an equal
existing value. Hits discard the candidate. Thus this is construction-time
sharing of retained code, not a claim that duplicate allocation attempts vanish.
The pool is not retained by emitted code. The inherited builder/reservations
facade forms a compile-only cycle; garbage collection releases it and the pool.
The report explicitly collects this garbage before measuring retained
allocations. There is no global mutable pool,
monkeypatch, source evaluator, invocation cache, runtime interning, or term-tree
inspection during transition lookup.

## Exactness argument

For each descriptor request the factory returns the original value or an
exactly equal value of the exact same frozen class. The compiler's descriptor
list positions and child indices never change. The same argument holds for a
whole probe, whose ordered nodes and root are equal. Hence each row and walker
has equal fields and the same transition function; failure profiles, row order,
continuations, zero-width cases and feedback controls are preserved.

Fragment widths and graph-building order are unchanged. Inductively, every
fragment origin, target and direct row is equal to the unpooled build. Both
finished values are `SuccinctSelectorTable` instances with equal immutable
code. They therefore have identical status and primitive transition functions
at every control and all six observations, including unreachable controls.
The unchanged occurrence-zipper interpreter consequently preserves each
microtick, selected address and native contraction.

This is an equality-preserving physical-code change. It is not state
minimization, a reduced microtick bound, or a new universality proof.

## Budgets and measurements

`compile_table` returns only the ordinary frozen table.
`compile_with_statistics` returns that table plus a separate frozen
`PoolStatistics` snapshot. `PooledGraphBuilder.pool_statistics` supplies the
same counts for component experiments.

The defaults are:

- At most 5 phases and 8 appendant bits; callers can lower these ceilings.
- At most 250,000 referenced metadata slots, as defined by the existing
  `metadata_records` property.
- At most 100,000 retained pool entries: unique descriptor records plus unique
  whole probe-table values. A hit adds no entry.
- A 10-second cooperative compilation deadline, checked by the inherited
  builder and by factory requests.

No budget is a byte bound. A probe candidate is constructed and validated before
its pool-entry check, and existing source-pattern work still occurs. The pool
never evicts, so the final number of pool entries equals its peak entry count.
It can retain values absent from the final graph, for example a zero-width hole
probe whose embedding allocated no interval. Those entries and all candidate
requests are reported separately from reachable final objects.

`tools.pooled_selector_report` runs each program/mode in a fresh Python process.
Its report distinguishes:

1. Virtual states and referenced metadata/probe slots.
2. Identity-distinct reachable descriptors, probe tables and all code objects.
3. Equality-distinct probe values and compilation-local pool entries.
4. Reachable-object `sys.getsizeof` bytes, counting each identity once and
   including scalar values. This excludes class objects and interpreter heaps.
5. `tracemalloc` current/peak allocation during compilation and post-compile
   garbage collection. Current is sampled after that collection. Peak minus current
   is an allocation excess, not an exact accounting of all temporary bytes.
   Imports first triggered by compilation can contribute persistent module
   allocations to the traced current total.
6. Process peak RSS through compilation, including interpreter/import overhead
   and the memory cost of tracing itself. It is not comparable directly to the
   reachable-object byte sum.

The report hashes the complete immutable value code independently of identity.
This hash is expressly distinct from the archive's all-transition graph hash.
It also records pool entries absent from final reachable code. The report is
observational: time, RSS and allocation counts can vary across Python versions
and hosts.

## Bounded reproduction

Standard library only, from the repository root:

```sh
timeout 180s sh -c 'ulimit -v 524288; exec python -m unittest tests.test_pooled_selector -v'
timeout 180s sh -c 'ulimit -v 524288; exec python -m tools.pooled_selector_report --output /tmp/pooled-selector.json'
```

`ulimit -v 524288` is a 512 MiB address-space ceiling on the measured Linux host;
these shell commands provide hard external limits. The library's cooperative
clock checks do not provide equivalent enforcement. The report admits only its
five fixed small cases and at most 160 seconds of child-process measurement.

The focused tests compare every entry in small probes, forward/inverse rows,
descent/ascent walkers and mixed builder graphs. They compare exact immutable
code and all interval boundaries/midpoints for periods 1–5; check every microtick
of the first three seed-11 native selections for each program; exercise hostile
field rejection and exact budget boundaries; and confirm the pool can be
collected while the finished table still works. A 1,500-level shared pattern DAG
tests flat code hashing without recursive pattern hashing.

## Observed small-program results

The archived [measurement report](../results/pooled-selector.json) was generated
on CPython 3.12.14/Linux under the 180-second/512-MiB external limits above.
Both modes have identical immutable value-code hashes for every case.

| Period / appendants | Referenced slots, unchanged | Reachable descriptors, before → after | Probe objects, before → after | Reachable bytes, before → after |
| --- | ---: | ---: | ---: | ---: |
| 1: `01` | 16,431 | 12,093 → 479 | 520 → 47 | 1,326,962 → 224,058 |
| 2: `1`, empty | 33,040 | 25,888 → 644 | 804 → 57 | 2,736,002 → 316,182 |
| 3: `01`, empty, `01` | 70,326 | 59,072 → 1,252 | 1,136 → 75 | 6,036,918 → 480,086 |
| 4: `10`, `1`, empty, `10` | 113,584 | 97,890 → 1,794 | 1,500 → 89 | 9,910,414 → 641,966 |
| 5: `01`, empty, `1`, `01`, `001` | 182,697 | 160,811 → 2,725 | 1,912 → 107 | 16,243,546 → 868,874 |

For period 5, all 2,134,486 virtual controls remain. The reachable-object byte
sum falls by 94.65%. The pool received 160,811 descriptor candidates and 1,912
probe candidates; it retained 2,725 descriptors plus 107 probes (2,832 entries).
All those retained values are reachable in this particular final graph. The
zero-width synthetic test separately checks that this need not hold generally.

The period-5 traced allocation peak was 16,851,885 bytes
unpooled and 1,408,970 bytes pooled. After collecting
compile-only garbage, traced current allocations were
16,671,653 and 1,103,054 bytes;
peak minus current was therefore 180,232 and
305,916 bytes. Process peak RSS through compilation
was 54,489,088 and 18,632,704 bytes,
respectively. These measures include different overheads and must not be
substituted for one another. Sharing improved retained code size; it does not
promise faster compilation, and the extra hashing/validation added overhead in
several measured cases.

## Why there is no global index arena yet

A shared cross-probe arena would replace per-probe child-before-parent indices,
root-final validation and flat probe tuples. It would require new exact record
types, remapping/provenance rules, validators, lookup bounds and substantially
more equivalence work. Equal-value sharing already removes duplicate retained
objects while keeping those established contracts intact.

The target UT19-derived CTS has 38 phases and 760 appendant bits, outside this
prototype's admission ceiling. Its selected-action component alone has
85,600,964 virtual states. That is not a byte estimate or a full-controller
count. No full UT19 controller is compiled here. Small-program savings do not
establish a safe 38-phase compile budget. Before any larger attempt, separately
bound source-pattern construction, descriptor requests and distinct retained
code, then choose new external memory/time limits and staged equivalence tests.
