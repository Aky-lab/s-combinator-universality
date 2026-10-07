# Exact generic formal import closure

6 October 2026. **Read-only source audit.** No Lean, Lake, upstream Python,
installer, script, native executable, or dependency code was run for this
audit. The result inventories a concrete replay target; it is not a kernel
check, an axiom census, or a formalization of this project's new first-event
composition.

## Result

The exact requested imports have a closure of **423 project modules**, with
818 project-to-project import edges and five explicit imports of official
`Std`. The project sources contain 10,109,218 bytes and 204,336 lines. Every
module was checked against its pinned Git blob, and a separate SHA-256 was
recorded. No project dependency is missing and the import graph is acyclic.

The smallest import-irredundant root set generating this exact union is:

```text
PureSFormal.Research.RootResetFiniteAllInputsTraceAgreement
PureSFormal.Research.RootResetContractProjection
PureSFormal.PureS.EncoderSize
```

The first root reaches 421 modules. Each of the remaining roots adds exactly
itself. This is minimal **within this exact import union**: none of these
three roots is reached from another module in the union. It is not a claim
that a larger upstream umbrella module could not provide a single root with
a larger, unwanted closure.

The six originally proposed explicit roots are also valid. They produce the
same 423-module union, with the following individual closure sizes:

| Root, after `PureSFormal.` | Project modules | Needed explicitly? |
| --- | ---: | --- |
| `Research.RootResetFiniteAllInputsTraceAgreement` | 421 | Yes |
| `Research.RootResetFinitePrioritySelector` | 279 | Already reached by all-input agreement |
| `Research.RootResetContractProjection` | 34 | Yes |
| `PureS.SchedulerStageAssembly` | 91 | Already reached by all-input agreement |
| `PureS.CheckpointRun` | 44 | Already reached by all-input agreement |
| `PureS.EncoderSize` | 13 | Yes |

The complete per-module inventory, direct imports, dependency-first ordering,
source URLs, exact identities, scan locations, and 22 declaration targets are
in [the machine-readable result](../results/generic_formal_closure.json).

## Pin and source identity

Repository: `cstrawberry/predictive-universe`.

- [Commit](https://github.com/cstrawberry/predictive-universe/commit/85a867988442fc423279341200f81634a1e65582): `85a867988442fc423279341200f81634a1e65582`
- Repository tree: `6bde297a47b3c532b5eb6c86c94f0e95255e8be8`
- `docs/paper/related/pure_s_universality/formalization` tree: `250f4136cb84cf8e26fbe96815cc5c2f8b86a6ed`
- `formalization/PureSFormal` tree: `5e27cdfeeeca1d95447568698fcabe1f675ce627`

The commit and untruncated recursive tree were independently retrieved through
read-only GitHub access. The commit is unsigned; this binds the inventory to
the requested pin, not to a verified signer identity. All selected files have
Git mode `100644`; no symlink or executable-mode source was selected.

Of the 423 modules, 52 were reused from previous source caches and 371 were
retrieved only as the import traversal discovered them. For 51 reused modules,
at least one old cache representation had an extra final newline. Exactly one
newline was removed only when that candidate byte string matched the pinned
Git blob. No other normalization was accepted. All staged source bytes match
the pin, including original line endings.

The canonical identity manifest has SHA-256:

```text
137262fb17399781c759f9f1bd1926e136a07f33ef65d4e219e5fe5b1252ad97
```

To reproduce this digest, take the result's `modules` array in module-name
order; retain `relative_path`, `git_blob_sha1`, `sha256`, and `bytes` in each
row; serialize the array as UTF-8 JSON with sorted object keys and compact
comma/colon separators; append one LF; hash those bytes with SHA-256.

## Coverage of the mathematical interfaces

All names below start with `PureSFormal.`. These are source declarations to
query in a later checked environment, not assertions that this audit
elaborated them.

| Interface | Exact declaration or defining module |
| --- | --- |
| Finite all-input selector contract | `Research.RootResetFinitePrioritySelector.selectorContract`, `.all_input_linear`, `.all_input_terminal` |
| Root restart and no retained invocation state | `Research.RootResetSelectorContract.Contract.initial` and `.InterInvocationState`, the latter definitionally `Unit` |
| One contraction, normal-form rejection, primitive bound | `Research.RootResetContractProjection.some_result`, `.none_result`, `.invocation_bound` |
| Agreement at every contraction sample | `Research.RootResetFiniteAllInputsTraceAgreement.selectsEveryContractionRun` and `.termOnlyPath_eq_persistentPath` |
| Exact nonempty stage assembly | `PureS.SchedulerStageAssembly.allNonemptyRawAt` |
| Premise-free complete stage facts | `PureS.SchedulerRecurrence.positiveStages`, `.initialGood`, `.exactCheckpoint`, all defined in `SchedulerStageAssembly.lean` |
| Selected response and frozen-carrier decode | `PureS.SchedulerCycle.SelectedResponseTrace`, including its `targetDecode` field |
| Literal response contraction list | `PureS.SchedulerCycle.normalResponse_exactPositionedMutationChain`, `.normalResponse_exactPairedMutationChain`, and `PureS.SchedulerResponseInvariant.responseEntries_spec` |
| Public seed-free decoder bridge | `PureS.CheckpointRun.decodeCarrier?_of_decode` |
| Exact encoder counts | `PureS.generator_size_counts_exact`, defined in `EncoderSize.lean` directly under `PureS`, with no `EncoderSize` namespace |
| Static balanced dispatcher | `PureS.BalancedActionTree.dispatcher` and `WeakPathUniversality.canonicalDispatcher` |

The exact response, decoder, and dispatcher modules are reached transitively;
they do not need extra roots. The closure also includes the nonfinal-job,
nested-response, clock/fuel/handoff, continuation, trace-algebra, and exact
checkpoint-count modules used in [the written stage lift](cts-event-transfer.md).

### Generic theorem use versus unavoidable module imports

The [38-phase construction](universality-theorem.md) uses the generic CTS
definitions and declarations, not the upstream 912-phase headline compiler.
Nevertheless, the upstream files group generic declarations with stronger
specializations. An unmodified source replay therefore has this import path:

```text
Research.RootResetFiniteAllInputsTraceAgreement
  -> Research.RootResetAllInputsTraceAgreement
  -> Research.RootResetTermOnlyUniversalityTransfer
  -> WeakPathUniversality
  -> Computation.CounterMachinePureS
```

`WeakPathUniversality` also directly imports `Computation.DeterministicTapePureS`
and the encoded sigma-one event modules. Likewise,
`PureS.BalancedActionTree` imports the concrete Cook program. These imports
bring Cook/Rogozhin, source-machine, and ProtectedTrie modules into the 423-file
closure even though their specialized universality conclusions are not premises
of this project's generic CTS composition.

The all-input agreement and premise-free stage modules also import initially
empty and first-empty branches. Those sources cannot be removed from an
unmodified import replay merely because the new written first-event lift uses
only nonempty prefixes. Editing imports or extracting declarations would be a
different, modified-source verification target.

Thus “generic replay” describes the selected interfaces. It does not mean that
every compiled declaration concerns only the generic interface. The bounded
audit followed exact imports, rather than fetching the full 1,239-module
verification inventory.

## Official toolchain boundary

The five explicit nonproject import edges are:

```text
PureSFormal.CTS.Core                         -> Std
PureSFormal.PureS.Term                       -> Std
PureSFormal.Computation.Enumerable           -> Std
PureSFormal.Rogozhin.Table                   -> Std
PureSFormal.Research.ProtectedTrieCertificates -> Std
```

Ordinary project modules also receive Lean's implicit `Init` import. There are
no explicit project-source `Lean` or `Lake` imports. `Std`, `Init`, their
transitive official dependencies, elaborator/tactics, runtime, and the Lake
build driver belong to the separately pinned official toolchain boundary.
Their vendor-source import graphs and executable internals were not rescanned
in this bounded project-source audit.

The pinned [toolchain record](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/VERIFICATION-TOOLCHAIN.json)
specifies Lean 4.33.1, source commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, and Lake 5.0.0. The official Linux
ZIP digest is
`0376ac87487246b40dd077268c097e701f552e94c6d020d2373b50c7444fa22f`.
The result records the individual Lean, Lake, and leanchecker executable hashes
as well. Those expected identities do not themselves report an execution.

The three original build-control files were also Git-blob verified:

| File | Git blob SHA-1 |
| --- | --- |
| `lakefile.toml` | `a4cbc73d93878fe88413a41f5ffbeeccfd1cb8bc` |
| `lake-manifest.json` | `cf18fc1c8d10f0f7dae335d07adbef29101374b2` |
| `lean-toolchain` | `1fcd511f69df6d2ee25b40c3beac5da7e7d8c77f` |

The Lake file is declarative TOML, defining the library and an optional demo
executable. It has no custom hooks or dependency declarations. Its default
target is the broader `PureSFormal`, so a bounded replay must select the three
explicit module roots instead of using the default target. The manifest has an
empty external-package list. Mathlib, Batteries, lean4lean, Docker, Python
packages, the demo, and upstream verification runners are unnecessary for the
selected official build/fresh-replay scope.

## Executable-surface and trust scan

An independently authored Python standard-library scanner blanked nested Lean
comments and quoted strings while preserving line numbers, parsed literal
import headers, and inspected the resulting graph and active source tokens.
It did not import any upstream Python or invoke a Lean parser.

Across all 423 project sources there were zero active matches for:

- `axiom`, `sorry`, `admit`, `sorryAx`
- `unsafe`, `partial`, `native_decide`
- `run_cmd`, `run_elab`, `initialize`, `builtin_initialize`
- `#eval` or other hash commands; native reduction bridge names
- custom `elab`, `elab_rules`, `macro`, `macro_rules`, or `syntax` commands
- `extern`, `implemented_by`, environment-mutation/compiler override names
- qualified `IO`, `System`, `Lean`, `Meta`, or `Elab` API references

The broad word scan found 216 uses of `macro`. They are scheduler inductive
constructors, patterns, and references, not elaborator commands. A separate
command-position scan found no custom syntax/metaprogram definitions.

This does **not** make elaboration inert. The files contain ordinary tactic
proofs, 1,016 `@[simp]` annotations, and 217 deriving sites using the official
`BEq`, `DecidableEq`, `Inhabited`, and `Repr` machinery. These invoke the
official elaborator and tactic implementation. There are 33 `set_option` uses
in 24 modules: transparency compatibility, unused-variable linting, and larger
heartbeat/recursion limits. One imported ProtectedTrie proof requests a local
`maxRecDepth` of 10,000,000. Process-level resource limits must therefore remain
external to the proof sources.

Two `classical` uses occur in `Research.ProtectedTrieStrong`. Thirty
`noncomputable def` declarations occur in `Research.ProtectedTrieSimplePath`,
`Research.ProtectedTrieSubdivision`, and `Research.ProtectedTrieStrongTheorem`.
They are in the unavoidable specialized import branch. Their presence neither
establishes nor refutes a particular target theorem's dependency on
`Classical.choice`.

Absence of explicit `axiom` or `sorry` is not a compiled axiom audit. Standard
axioms such as `propext`, `Quot.sound`, or `Classical.choice` may enter through
proof dependencies. Compiler-generated runtime declarations may also differ
from source-level `unsafe`/`partial` counts. Query the actual target declaration
types and axiom dependencies after a clean build, and distinguish safe
declarations from anything the replay tool skips.

## What a later replay must keep separate

1. Build only the identified roots, using the pinned official toolchain and
   byte-verified sources. Keep the build offline and isolated; do not reuse
   upstream compiled caches or execute upstream verification scripts.
2. Record the actual compiled module coverage and source/output identities.
   Source reachability is not proof that a build or replay processed them.
3. Run a fresh official kernel replay of the exact roots and their imports;
   validate appropriate positive/negative controls separately.
4. Query the exact declarations in the result JSON, their types, and their
   axiom dependencies. A module name is not necessarily a declaration namespace.
5. Report the new Local-event provenance and first-event composition as a
   written proof unless separately formalized and checked. Checking imported
   generic Lean declarations does not check this additional composition or
   establish all-input equivalence of the independent Python port.

This audit's stopping condition is satisfied: exact project roots, source
identities, full project import closure, official-toolchain boundary, and the
bounded source-scan findings are established. No upstream execution result is
claimed here.
