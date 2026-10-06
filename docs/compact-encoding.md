# A compact source-encoding route

The next source-compiler experiment uses a direct binary-Turing-machine-to-cyclic-tag construction. This avoids carrying the current counter/tag/Rogozhin/Cook detour into the new implementation.

## Direct binary machine to CTS

Neary's *Small Universal Turing Machines*, Theorem 4.3.2, gives a direct construction with `z = 60Q + 121` and `2z` appendants for a binary machine with `Q` states. For `n` explicit tape cells, let `s = n + 2` include two boundary markers. The initial cyclic-tag word has length

```text
z * (2*(s + 1) + 2^ceil(log2(s))) < z * (4*s + 2).
```

For fixed `Q`, this is linear in the represented input tape. The encoding appears on printed pages 65–66; the left-transition tables are 4.3.1–4.3.7 on pages 67, 70, 71, 71, 72, 74 and 75. The surrounding text specifies implicit copy entries. [Author-hosted thesis](https://tilde.ini.uzh.ch/users/tneary/public_html/tneary_Thesis.pdf)

This bound measures the initial CTS data word. Appendant storage, its S dispatcher, and intermediate reduction growth have separate costs. The existing counter encoding already contains exponential multiplicities, so replacing only the final Cook stage would leave earlier expansion in place.

## First executable target

Use states `q1` and halting `q2`, symbols `a,b`, and blank `b`:

```text
(q1, a) -> (b, left, q2)
(q1, b) -> (a, left, q2)
```

Start with explicit tape `bb` and the head on its second cell. The expected source result is tape `ba`, with the head on its first cell. This fixture has `z = 241`, 482 appendants, and seed

```text
H1 B μ^4 B b̂ b̂
```

of 3,374 bits. The mirrored input-symbol case is a second regression fixture. The source specifies left-moving tables directly and refers elsewhere for right-moving transitions; mixed-direction compilation is a later, separately verified extension.

Implementation acceptance requires the entire deterministic appendant table, exact seed, macro-boundary readout, both write cases and the designated halt event. Counts for generated appendants and execution belong beside the resulting artifact.

## Halting observation

The designated halt appendant regenerates a halt token, leading to a repeating CTS mode. The direct construction uses

```text
h = 60Q + 50
H_h = 0^h 1 0^(2z-h-1)
α_h = H_h.
```

For the first fixture, `h = 170`. The observer must recognize the designated token in its valid phase and block alignment. Merely finding a repeated CTS configuration would incorrectly classify nonhalting source loops.

The required bridge is an equivalence between reaching this distinguished event and reaching the source halt state, followed by structural tape readout at the corresponding macro-boundary. A related published construction explicitly uses a distinguished appendant emitted exactly upon source halting. [Neary 2015, Lemma 9, page 655](https://drops.dagstuhl.de/storage/00lipics/lipics-vol030-stacs2015/LIPIcs.STACS.2015.649/LIPIcs.STACS.2015.649.pdf)

## One fixed controller

A generic compiler produces different CTS programs for different source transition tables. To obtain a single fixed endpoint, first choose one fixed universal binary machine with an explicit program/input format, compile its transition table once, and encode varying computations only in its initial tape. The direct input-length bound then applies with fixed `Q`.

The first two-state fixture checks the construction on a tractable source. Choosing and validating the universal-machine front end is a separate composition step.

## Other routes considered

- The earlier [Neary–Woods 2006 route](https://tilde.ini.uzh.ch/users/tneary/public_html/NearyWoodsBCRI-04-06.pdf), Lemmas 1–2, passes through clockwise machines and supports polynomial simulation with explicit symbol-string encodings.
- [Cook 2009, Sections 1.2–1.3 and 3](https://arxiv.org/pdf/0906.3248), discusses the unary expansion, a six-stage non-unary clockwise-machine-to-tag route, and one-hot conversion from tag systems to CTS. Moving input writing into a machine's transition table changes the controller with that input, so fixedness must be handled explicitly.
- [Geary et al. 2018, Proposition 2](https://drops.dagstuhl.de/storage/00lipics/lipics-vol123-isaac2018/LIPIcs.ISAAC.2018.23/LIPIcs.ISAAC.2018.23.pdf), gives a polynomial compilation with linear input encoding for empty-word-halting skipping CTS. Their phase behavior differs from ordinary CTS and requires its own backend interface.

The direct Neary fixture is the immediate implementation target because its data layout and left-transition rules are explicit and its initial word is small enough to materialize.

## Reproduced fixture

The [two-state implementation](neary-fixture.md) now runs both input-symbol cases. Its 482-appendant table contains 63,644 appendant bits. Both runs recover the source result at CTS step 55,912, use the distinguished halt appendant at step 56,083, and stay within 5,187 queued bits. [Generated program, seeds and reports](../artifacts/neary-left-toggle/)

The [generic closed-S constructor](cts-encoding.md) expands each resulting initial condition to exactly 1,342,619 tree nodes, represented by 27,547 immutable objects. These are initial-term construction and hashing measurements; the ordinary CTS runs and native S execution are recorded separately.
