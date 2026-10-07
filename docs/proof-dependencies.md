# Proof dependency map

The conventional Turing-machine endpoint is
[`SOnlyTuringUniversality.halting_iff_event`](../formal/SOnlyTuringUniversality.lean).
The numerical register-machine endpoint remains
[`SOnlyUniversality.result_iff_first_event`](../formal/SOnlyUniversality.lean).
[The 67-module verification](formal-turing-universality.md) records the extended
clean build, fresh replay and 1,359-declaration audit; the
[register checkpoint](final-verification.md) also preserves negative controls.

## 0. Conventional tape machines to three registers

- `SOnlyTapeStacks`: true Int-indexed tapes, every-cell stack representation, finite runs, halting/divergence and injective arithmetic stack codes
- `StackMacros`: actual finite INC/DECJZ push/pop execution and scratch restoration
- `StackPushTable`, `StackPopTable`, `StackMacroTime`: concrete tables and exact positive macro lengths
- `SOnlyTapeCompilerCheckpoints`: cofinal checkpoint simulation and all-microstep halting/final-state reflection
- `SOnlyTapeCompiler`: explicit finite label table, literal macro rows, arbitrary finite-input halting and chosen-left-stack result
- `SOnlyTuringUniversality`: composition with the same fixed S encoder/controller/observer/decoder

[Conventional tape theorem and proof map](formal-turing-universality.md)

## 1. Source machine and explicit compiler

- `SOnlyMachine`: typed INC/DECJZ/HALT source, amnesiac macro simulation and halting equivalence
- `SOnlyMachineBP2`: actual literal BP2 execution, guarded blocks and initialization
- `SOnlyMachineWaterfallBP2`: finite Waterfall-to-BP2 compiler
- `SOnlyMachineClock`: amnesiac clock rows and complete BP2 simulation
- `SOnlyMachineFinite`, `SOnlyMachineNat`: finite/dense counter enumeration and Nat-label projection
- `SOnlyMachineCorrectness`: halted-output uniqueness and value-specific equivalence
- `SOnlyMachineBounds`: polynomial size bound for the actual uniform-helper compiler

[Frontend definitions and bounds](formal-register-machine-frontend.md)

## 2. Fixed UT19 computation

- `SOnlyCounter`: all raw counter branches, including protected odd Reset
- `SOnlyMemory`: actual local memory passes, prefix-XOR update and microstep safety
- `SOnlyTemporalMemory`: explicit initializer, protected forcing window and stride-transform identity
- `SOnlySimulation`, `Normal`, `Exceptional`, `Halt`: assembled-word normal/zero/halt transitions
- `SOnlySimulationEpoch`, `Schedule`, `Instructions`, `Restart`: actual source epochs, programmed widths and restart
- `SOnlySimulationComplete`: arbitrary BP2 halting/event equivalence and cofinal nontermination safety
- `SOnlySimulationReadout`, `Interface`, `Universal`, `Output`: event grammar, efficient depth, machine input composition and specified numerical output
- `SOnlySimulationPublished`: all-slot published-width and initialized-memory agreement

[Written source invariants](ut19-simulation-invariants.md)

## 3. One-hot translation and generic S controller

- `SOnlySource`: exact source/CTS simulation, every-offset events and least-event index
- `SOnly38`: literal 38-phase program, exact route, fixed controller contract and every-sample agreement
- Pinned `PureSFormal`: generic encoding, native scheduler, finite selector and root-reset trajectory

[Pinned dependency replay](formal-replay.md) · [Concrete instance](formal-cts-instance.md)

## 4. Generated origins and first acceptance

- `SOnlyEventTransfer`, `EventPattern`, `EventResponse`: exact samples, literal target pattern and public audit
- `SOnlyProvenance`, `ProvenanceRows`: H6 congruence and actual constructor/context inheritance
- `SOnlyGeneratedOrigins`, `CanonicalOrigins`: label/snapshot licenses and canonical C4 preservation
- `SOnlySchedulerOrigins`, `GlobalAncestors`, `GlobalOrigins`, `GlobalTerminal`: actual phase, parent, response and job closure
- `SOnlyResponseLabels`, `GlobalStages`, `GlobalFirstPrefix`: source-indexed labels and constructed whole-stage prefixes
- `SOnlyFirstEventOrigins`, `FirstEventResponse`, `GlobalFirstEvent`, `GlobalFirstStructure`: sharp creation time and identical frozen audits at every first-event match
- `SOnlyEventEquivalence`: source/S event equivalence under source liveness, discharged by the final compiler

## 5. Fixed observation and current-tree result

- `SOnlyObserver`: finite bottom-up cover and exact descendant recognition
- `SOnlyInitial`: all-input initial event absence
- `SOnlyResult`, `ResultBits`: exact first-counter arithmetic and unaligned event-bitword recovery
- `SOnlyWitnessResult`: numerical result in a genuine accepted sample
- `SOnlyCurrentDecoder`: fixed first-preorder choice and all-witness correctness interface
- `SOnlyDecoderBound`, `DecoderBoundCurrent`: input-size-fuel simulation, output size and charged recursion

[All-input decoder complexity](lean-current-decoder-bound.md)

## 6. End-to-end statement

`SOnlyUniversality` joins the concrete encoder, fixed controller, fixed regular
observer and fixed current-tree result function. Its halting and output
statements have no remaining source-event, liveness, origin or numerical
success hypotheses.

The conventional Turing-machine-to-register-machine reduction is now checked
by layer 0. Complete bit-cost interpretation remains written mathematics, as
identified in [the theorem](universality-theorem.md). Earlier component reports
preserve their dated checkpoint scope.
