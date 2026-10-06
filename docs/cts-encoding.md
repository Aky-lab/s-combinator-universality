# Generic ordinary CTS initial terms

`s_only.encoding` constructs a closed S-only initial term for any finite binary
cyclic-tag program of **positive period**, starting at phase zero. Empty data
words and empty appendants are supported. A zero-period program is rejected,
because ordinary cyclic-tag semantics require a current phase.

This is an independently written implementation of the mathematical
constructors in Cinematic Strawberry's *Pure S Is Computationally Universal
Under a Fixed Root-Restarted Finite Controller*, pinned at
[`85a867988442fc423279341200f81634a1e65582`](https://github.com/cstrawberry/predictive-universe/tree/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality).
It generalizes the initial syntax of the independently checked
[two-phase fixture](queue-replication.md). Controller execution and structural
readout are separate integration layers.

## Constructors and ordering

All names below abbreviate closed terms. Application associates left:

```text
b = S S                    C0 = S b b
pi = S b                   v0 = S C0
v1 = S (S C0)              Li = b vi
Word([]) = S               Word(w followed by i) = Li Word(w)
Push_J(N) = S (S N) J
Leaf(F) = b F              Node(L,R) = b (S L R)
H* = b (b S)               Act = S H* Actions
Seed = S Word(w)           E* = S (S Act Seed)
Initial(P,w) = (C0 C0) E*
```

The logical front of a word is its **innermost** cell. An appender for `abc`
is `Push_La(Push_Lb(Push_Lc(pi)))`: construct the pushes in reverse order so
that the outermost push emits the first bit.

The action for label `(j,0)` is `pi`; the action for `(j,1)` appends the entire
appendant at phase `j`. Dispatcher leaves are phase-major and zero-before-one:
`(0,0), (0,1), (1,0), (1,1), ...`.

The deterministic layout matches upstream `BalancedActionTree`: pair adjacent
trees from left to right, carry an unpaired last tree unchanged, and repeat
until one tree remains. There is no power-of-two padding. For a three-phase
program the six leaves have depths `3,3,3,3,2,2`. This is a specific bottom-up
layout, not midpoint splitting. Its maximum depth is `ceil(log2(2p))`.
Identical compiled subtrees may share Python objects; their differently labeled
source occurrences still occupy distinct positions in the unfolded dispatcher.

The paper's Sections 3 and 4.2 specify the constructors and grammar. Appendix
E.1 fixes the complete two-phase example. The pinned
[`Appender.lean`](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/PureS/Appender.lean)
explicitly defines the appender by a right fold, and
[`BalancedActionTree.lean`](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/PureS/BalancedActionTree.lean)
specifies adjacent pairing. The generic dispatcher interface in
[`ActionTree.lean`](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/PureS/ActionTree.lean)
requires valid routes to every phase/bit label and permits other complete
finite layouts. These upstream files were inspected as source text, not run.

## Exact unfolded size

Let:

- `p` be the positive number of appendants
- `M` and `O` be total appendant bits and ones, counting each program position
- `n` and `u` be the input data length and number of ones

Sizes count S leaves **and application nodes** in the unshared occurrence tree.
The fixed sizes are `|pi|=5`, `|L0|=15`, `|L1|=17`. Therefore:

```text
|Word(w)| = 1 + 16n + 2u
|Appender(a)| = 5 + 20*len(a) + 2*ones(a)
|Leaf(F)| = 4 + |F|
|Node(L,R)| = 7 + |L| + |R|
|Actions(P)| = 32p - 7 + 20M + 2O
|Initial(P,w)| = 39 + |Actions(P)| + |Word(w)|
               = 33 + 32p + 20M + 2O + 16n + 2u
```

The dispatcher has `2p` leaf occurrences and `2p-1` internal nodes. The two
phase actions contribute `18p + 20M + 2O` nodes before internal-node overhead.
The result has `(|Initial|+1)/2` S leaves. The formulas do not depend on the
balanced tree's particular shape, but its prefix digest does.

`encoding_stats` computes these counts directly from the source without
constructing any term. Identical appendants still contribute at every phase;
`unique_appendant_count` separately counts distinct strings, including the
empty string when present.

## Sharing and memory

Application nodes are immutable and preserve the exact unfolded leaf count
already used by `s_only.terms`. Per-compilation identity interning shares
identical appender suffixes, repeated actions and repeated dispatcher subtrees.
Interning uses child identities instead of recursive term hashing or equality.
Repeated dataword prefixes are constructed iteratively. The interning table is
released after compilation; the resulting terms retain only reachable nodes.

`unique_objects(term)` counts reachable Python object identities, including the
singleton S. This is an implementation-storage measurement and must not replace
unfolded size. Sharing never authorizes a simultaneous graph reduction.

Both construction and serialization avoid recursion on appendant/dataword
length. The complete A/S prefix can be hashed in chunks without allocating one
large string. Hashing still visits **every unfolded occurrence** and takes time
linear in unfolded size; an explicit maximum node count is checked first.
Auxiliary streaming storage is bounded by term depth and chunk size.

## API and bounded inspection

```python
from s_only.cts import Program
from s_only.encoding import compile_program, encode, encoding_stats

program = Program(("1", ""))
term = encode(program, "101")
stats = encoding_stats(program, "101")

# Reuse one fixed dispatcher for multiple phase-zero initial words.
compiled = compile_program(program)
other_term = compiled.encode("001")
```

Programs use the existing `Program` type and binary strings. Whitespace,
nonbinary characters, integers and Boolean values are rejected as word inputs.
The encoder supplies only phase-zero initialization; it does not silently
rotate a program or reinterpret a nonzero-phase configuration.

```sh
# Symbolic counts only; no term allocated.
python -m tools.inspect_cts_encoding

# Also construct, verify cached size, count shared objects, and hash all bytes.
python -m tools.inspect_cts_encoding --sha256

# Inspect a generated program JSON and its seed file.
python -m tools.inspect_cts_encoding \
  --program /path/to/program.json --word-file /path/to/seed-b.txt --sha256

# Explicit empty initial word.
python -m tools.inspect_cts_encoding --program /path/to/program.json --word ''
```

The program JSON may be an array of binary strings, or an object containing an
`appendants` array. A seed file contains ASCII bits and at most one trailing
LF or CRLF. When a custom program is supplied, a word or word file is required.
With no program argument, the default is the published two-phase example.

The CLI bounds each input file to 2,000,000 bytes, total source bits to
1,000,000, and program phases to 10,000 by default. `--max-input-bytes`,
`--max-source-bits` and `--max-phases` change those caps. A bounded file read
occurs before JSON parsing. `--build` requests object counting; `--sha256`
implies construction. Both are guarded before construction by `--max-nodes`
(default 10,000,000 unfolded nodes). Symbolic inspection works even when that
construction cap is too small. Limit failures exit nonzero without emitting a
successful inspection report. No inspection path executes source transitions
or S contractions.

## Replicated inputs

The two-phase program `("1", "")` with input `101` produces exactly the
171-character prefix in `fixtures/queue_101_path.json`, byte for byte. Its
SHA-256 is:

```text
3c66d04a273dd1e8401995ae114be5e8bbacaae1dd936a4d6dd169ffa60d60be
```

The generated [two-state Neary source fixture](compact-encoding.md) was also
inspected after its source artifacts were available. These are initial-syntax
measurements, separate from the source fixture's CTS execution audit.

| Quantity | Both seeds |
|---|---:|
| Program phases | 482 |
| Total appendant bits | 63,644 |
| Total appendant ones | 140 |
| Distinct appendants, including epsilon | 41 |
| Nonempty appendant positions | 126 |
| Initial data bits | 3,374 |
| Initial data ones | 9 |
| Dispatcher unfolded nodes | 1,288,577 |
| Word unfolded nodes | 54,003 |
| Complete initial unfolded nodes | 1,342,619 |
| Complete initial S leaves | 671,310 |
| Reachable object identities | 27,547 |

For seed `a` (source tape `ba`, head on the second cell), the initial prefix
SHA-256 is:

```text
885d301dafa776825385fbe833c1a7c0fe0e7c0a7c5917a7aa0ad7229737752b
```

For seed `b` (source tape `bb`, head on the second cell), it is:

```text
1d6d86481511868b45b02f40fac7b6c2ceb273974b8c697d10f7016674e44bdb
```

The exact input file hashes, including the seed files' trailing newlines, were:

```text
program.json  aa28952e044bc498b505f9720e6208400865f97d87ca80a2baf875d8232bb865
seed-a.txt    8cddac13c38beca71bda136bfa9feeca901469bbf1ce5024133bc4502fd5938c
seed-b.txt    e458871d38a5e96bfea3f142495edcc7854fb1dc73a50cc51810f99f6b84f462
```

This inspection covers initial construction and hashing. Later trajectory
growth and runtime depend on the generic controller and source-to-S
halt/readout bridge.

## Verification and attribution

`tests/test_encoding.py` checks a tuple-only independent formula expansion,
phase/bit order, appender order (including small native two-step-per-bit
checks), non-power-of-two layouts, empty and invalid inputs, closed immutable
syntax, exact expanded-size accounting, suffix
sharing, deep iterative construction, chunked digests and CLI resource limits.
Its reference tree construction uses equal-height block merging rather than
the production implementation's forest rounds.

```sh
python -m unittest discover -s tests -p test_encoding.py -v
```

Primary constructor source:
[`paper.md`, Sections 3, 4.2 and E.1](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/paper.md).
The mathematical construction is attributed to Cinematic Strawberry; the
repository retains its [MIT notice](../third_party/cinematic-strawberry-MIT.txt).
The source fixture comes from Neary's thesis as documented in
[the compact-encoding note](compact-encoding.md). This Python implementation
and its tests were written independently from the mathematical constructor specification.
