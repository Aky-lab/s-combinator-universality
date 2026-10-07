# Compact fixed controller S computation

The 14-page technical manuscript presents the 38-phase cyclic-tag construction,
its register and conventional-tape compilers, global first-event output proof,
resource bounds and reproducible formal verification. It identifies the generic
Cinematic Strawberry construction and the prior 912-phase universality result
explicitly. The statement concerns the prescribed selected-path model.

Read `compact-s-combinator-construction.pdf`. The editable sources are
`manuscript.tex`, `source-section.tex`, `preamble.tex` and `references.tex`.
The manuscript gives the proof argument and exact Lean entry points; the full
construction definitions and kernel proofs are in the companion formal source
artifact identified by its recorded hashes.

## Build

Use an existing LaTeX distribution with the standard `article`, AMS, Latin
Modern, `geometry`, `microtype`, `hyperref`, `xurl`, `enumitem` and `booktabs`
packages. A normal installation can run:

```sh
pdflatex -no-shell-escape manuscript.tex
pdflatex -no-shell-escape manuscript.tex
```

`sh build.sh` also supports an installed TeX Live tree without a generated
system format/cache. It creates those files locally, enables no shell escape,
and downloads nothing. The generated PDF is `manuscript.pdf`; the reviewed
copy is distributed as `compact-s-combinator-construction.pdf`.

## Verification

The mathematical statements and proof scope were checked against the formal
sources and the pinned prior-work comparison. All 14 PDF pages were rendered
and inspected. The final build has no overfull boxes, unresolved references or
missing glyphs. `manuscript-metadata.json` records source/PDF hashes and the
formal artifact identities. The manuscript is an exposition of the existing
verified construction; its preparation did not require changing the proofs.
