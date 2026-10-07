import SOnlyTuringUniversalityReplay
import SOnly38
import SOnlyProvenance
import SOnlyProvenanceRows
import SOnlyEventPattern
import SOnlyEventTransfer
import SOnlyGeneratedOrigins
import SOnlyCanonicalOrigins
import SOnlySource
import SOnlyCounter
import SOnlyEventResponse
import SOnlyObserver
import SOnlyStageEvents
import SOnlyResult
import SOnlyResultBits
import SOnlyWitnessResult
import SOnlyCurrentDecoder
import SOnlyDecoderBound
import SOnlyDecoderBoundCurrent
import SOnlySchedulerOrigins
import SOnlyResponseLabels
import SOnlyGlobalAncestors
import SOnlyGlobalOrigins
import SOnlyGlobalTerminal
import SOnlyFirstEventOrigins
import SOnlyGlobalStages
import SOnlyEventEquivalence
import SOnlyFirstEventResponse
import SOnlyGlobalFirstPrefix
import SOnlyGlobalFirstEvent
import SOnlyGlobalFirstStructure
import SOnlyInitial
import SOnlyMachine
import SOnlyMachineBP2
import SOnlyMachineWaterfallBP2
import SOnlyMachineClock
import SOnlyMachineFinite
import SOnlyMachineNat
import SOnlyMachineBounds
import SOnlyMachineCorrectness
import SOnlyMemory
import SOnlyTemporalMemory
import SOnlySimulation
import SOnlySimulationNormal
import SOnlySimulationExceptional
import SOnlySimulationHalt
import SOnlySimulationEpoch
import SOnlySimulationSchedule
import SOnlySimulationInstructions
import SOnlySimulationRestart
import SOnlySimulationComplete
import SOnlySimulationReadout
import SOnlySimulationInterface
import SOnlySimulationUniversal
import SOnlySimulationOutput
import SOnlySimulationPublished
import SOnlyUniversality

#check SOnly38.productions
#print axioms SOnly38.productions
#check SOnly38.oneHot
#print axioms SOnly38.oneHot
#check SOnly38.appendants
#print axioms SOnly38.appendants
#check SOnly38.program
#print axioms SOnly38.program
#check SOnly38.production_count
#print axioms SOnly38.production_count
#check SOnly38.production_symbols_valid
#print axioms SOnly38.production_symbols_valid
#check SOnly38.period_eq
#print axioms SOnly38.period_eq
#check SOnly38.appendant_count
#print axioms SOnly38.appendant_count
#check SOnly38.enumerated_appendants
#print axioms SOnly38.enumerated_appendants
#check SOnly38.appendant_bit_count
#print axioms SOnly38.appendant_bit_count
#check SOnly38.appendant_one_count
#print axioms SOnly38.appendant_one_count
#check SOnly38.skip_appendants
#print axioms SOnly38.skip_appendants
#check SOnly38.targetPhase
#print axioms SOnly38.targetPhase
#check SOnly38.targetLabel
#print axioms SOnly38.targetLabel
#check SOnly38.targetAppendant
#print axioms SOnly38.targetAppendant
#check SOnly38.target_appendant
#print axioms SOnly38.target_appendant
#check SOnly38.target_appendant_length
#print axioms SOnly38.target_appendant_length
#check SOnly38.target_appendant_one_count
#print axioms SOnly38.target_appendant_one_count
#check SOnly38.target_response_nonempty
#print axioms SOnly38.target_response_nonempty
#check SOnly38.dispatcher
#print axioms SOnly38.dispatcher
#check SOnly38.targetRoute
#print axioms SOnly38.targetRoute
#check SOnly38.dispatcher_leaf_count
#print axioms SOnly38.dispatcher_leaf_count
#check SOnly38.dispatcher_depth
#print axioms SOnly38.dispatcher_depth
#check SOnly38.target_selected_route
#print axioms SOnly38.target_selected_route
#check SOnly38.target_route_lookup
#print axioms SOnly38.target_route_lookup
#check SOnly38.target_has_route
#print axioms SOnly38.target_has_route
#check SOnly38.encode
#print axioms SOnly38.encode
#check SOnly38.selector
#print axioms SOnly38.selector
#check SOnly38.controller
#print axioms SOnly38.controller
#check SOnly38.trajectory
#print axioms SOnly38.trajectory
#check SOnly38.encode_eq_upstream
#print axioms SOnly38.encode_eq_upstream
#check SOnly38.selector_eq_projected
#print axioms SOnly38.selector_eq_projected
#check SOnly38.same_root_start
#print axioms SOnly38.same_root_start
#check SOnly38.boundary_state_is_unit
#print axioms SOnly38.boundary_state_is_unit
#check SOnly38.coefficient_positive
#print axioms SOnly38.coefficient_positive
#check SOnly38.every_input_linear
#print axioms SOnly38.every_input_linear
#check SOnly38.every_input_terminal
#print axioms SOnly38.every_input_terminal
#check SOnly38.selected_one_contraction
#print axioms SOnly38.selected_one_contraction
#check SOnly38.rejected_zero_contractions
#print axioms SOnly38.rejected_zero_contractions
#check SOnly38.trajectory_eq_persistent
#print axioms SOnly38.trajectory_eq_persistent
#check SOnly38.trajectory_selects
#print axioms SOnly38.trajectory_selects
#check SOnly38.trajectory_contracts
#print axioms SOnly38.trajectory_contracts
#check SOnly38.checkpointRealization
#print axioms SOnly38.checkpointRealization
#check SOnly38.checkpointTime
#print axioms SOnly38.checkpointTime
#check SOnly38.exact_checkpoint
#print axioms SOnly38.exact_checkpoint
#check SOnly38.checkpoint_accepts_only
#print axioms SOnly38.checkpoint_accepts_only
#check SOnlyProvenance.State
#print axioms SOnlyProvenance.State
#check SOnlyProvenance.delta
#print axioms SOnlyProvenance.delta
#check SOnlyProvenance.classify
#print axioms SOnlyProvenance.classify
#check SOnlyProvenance.delta_ne_s
#print axioms SOnlyProvenance.delta_ne_s
#check SOnlyProvenance.delta_b_iff
#print axioms SOnlyProvenance.delta_b_iff
#check SOnlyProvenance.delta_h_iff
#print axioms SOnlyProvenance.delta_h_iff
#check SOnlyProvenance.delta_h0_iff
#print axioms SOnlyProvenance.delta_h0_iff
#check SOnlyProvenance.delta_h1_iff
#print axioms SOnlyProvenance.delta_h1_iff
#check SOnlyProvenance.delta_h2_iff
#print axioms SOnlyProvenance.delta_h2_iff
#check SOnlyProvenance.delta_h3_iff
#print axioms SOnlyProvenance.delta_h3_iff
#check SOnlyProvenance.delta_h4_iff
#print axioms SOnlyProvenance.delta_h4_iff
#check SOnlyProvenance.classify_s_iff
#print axioms SOnlyProvenance.classify_s_iff
#check SOnlyProvenance.classify_b_iff
#print axioms SOnlyProvenance.classify_b_iff
#check SOnlyProvenance.classify_h_iff
#print axioms SOnlyProvenance.classify_h_iff
#check SOnlyProvenance.classify_h0_iff
#print axioms SOnlyProvenance.classify_h0_iff
#check SOnlyProvenance.classify_h1_iff
#print axioms SOnlyProvenance.classify_h1_iff
#check SOnlyProvenance.classify_h2_iff
#print axioms SOnlyProvenance.classify_h2_iff
#check SOnlyProvenance.classify_h3_iff
#print axioms SOnlyProvenance.classify_h3_iff
#check SOnlyProvenance.classify_h4_iff
#print axioms SOnlyProvenance.classify_h4_iff
#check SOnlyProvenance.extension_h6_iff
#print axioms SOnlyProvenance.extension_h6_iff
#check SOnlyProvenance.safe_extension
#print axioms SOnlyProvenance.safe_extension
#check SOnlyProvenance.fresh_audit
#print axioms SOnlyProvenance.fresh_audit
#check SOnlyProvenance.AllH6
#print axioms SOnlyProvenance.AllH6
#check SOnlyProvenance.allH6_s
#print axioms SOnlyProvenance.allH6_s
#check SOnlyProvenance.app_no_new
#print axioms SOnlyProvenance.app_no_new
#check SOnlyProvenance.app_registered_root
#print axioms SOnlyProvenance.app_registered_root
#check SOnlyProvenance.Endpoint
#print axioms SOnlyProvenance.Endpoint
#check SOnlyProvenance.endpoint_ne_h3
#print axioms SOnlyProvenance.endpoint_ne_h3
#check SOnlyProvenance.endpoint_ne_s
#print axioms SOnlyProvenance.endpoint_ne_s
#check SOnlyProvenance.endpoint_extension
#print axioms SOnlyProvenance.endpoint_extension
#check SOnlyProvenance.applyArgs_other
#print axioms SOnlyProvenance.applyArgs_other
#check SOnlyProvenance.s_pair_carries
#print axioms SOnlyProvenance.s_pair_carries
#check SOnlyProvenance.s_one_carries
#print axioms SOnlyProvenance.s_one_carries
#check SOnlyProvenance.chosen_other
#print axioms SOnlyProvenance.chosen_other
#check SOnlyProvenance.chosen_carries
#print axioms SOnlyProvenance.chosen_carries
#check SOnlyProvenance.haltCode_carries
#print axioms SOnlyProvenance.haltCode_carries
#check SOnlyProvenance.h_prefix1_carries
#print axioms SOnlyProvenance.h_prefix1_carries
#check SOnlyProvenance.fresh_shell_carries
#print axioms SOnlyProvenance.fresh_shell_carries
#check SOnlyProvenance.completed_outer_carries
#print axioms SOnlyProvenance.completed_outer_carries
#check SOnlyProvenance.rebuilt_outer_audit
#print axioms SOnlyProvenance.rebuilt_outer_audit
#check SOnlyProvenance.classify_p
#print axioms SOnlyProvenance.classify_p
#check SOnlyProvenance.classify_push
#print axioms SOnlyProvenance.classify_push
#check SOnlyProvenance.classify_appender
#print axioms SOnlyProvenance.classify_appender
#check SOnlyProvenance.classify_selectedAction
#print axioms SOnlyProvenance.classify_selectedAction
#check SOnlyProvenance.classify_compileDispatcher
#print axioms SOnlyProvenance.classify_compileDispatcher
#check SOnlyProvenance.classify_compileActions
#print axioms SOnlyProvenance.classify_compileActions
#check SOnlyProvenance.classify_C
#print axioms SOnlyProvenance.classify_C
#check SOnlyProvenance.classify_valueTag
#print axioms SOnlyProvenance.classify_valueTag
#check SOnlyProvenance.classify_live
#print axioms SOnlyProvenance.classify_live
#check SOnlyProvenance.classify_environment
#print axioms SOnlyProvenance.classify_environment
#check SOnlyProvenance.classify_act
#print axioms SOnlyProvenance.classify_act
#check SOnlyProvenance.classify_dispatcher
#print axioms SOnlyProvenance.classify_dispatcher
#check SOnlyProvenance.classify_clockWrappers
#print axioms SOnlyProvenance.classify_clockWrappers
#check SOnlyProvenance.classify_clockExit
#print axioms SOnlyProvenance.classify_clockExit
#check SOnlyProvenance.classify_base
#print axioms SOnlyProvenance.classify_base
#check SOnlyProvenance.classify_frame
#print axioms SOnlyProvenance.classify_frame
#check SOnlyProvenance.classify_freshLocal
#print axioms SOnlyProvenance.classify_freshLocal
#check SOnlyProvenance.classify_frameFirst
#print axioms SOnlyProvenance.classify_frameFirst
#check SOnlyProvenance.classify_frameSecond
#print axioms SOnlyProvenance.classify_frameSecond
#check SOnlyProvenance.classify_liveCell
#print axioms SOnlyProvenance.classify_liveCell
#check SOnlyProvenance.appenderAccumulator_endpoint
#print axioms SOnlyProvenance.appenderAccumulator_endpoint
#check SOnlyProvenance.response_endpoint
#print axioms SOnlyProvenance.response_endpoint
#check SOnlyProvenance.Descendant
#print axioms SOnlyProvenance.Descendant
#check SOnlyProvenance.Descendant.app_cases
#print axioms SOnlyProvenance.Descendant.app_cases
#check SOnlyProvenance.Descendant.s_eq
#print axioms SOnlyProvenance.Descendant.s_eq
#check SOnlyProvenance.Template
#print axioms SOnlyProvenance.Template
#check SOnlyProvenance.Template.instantiate
#print axioms SOnlyProvenance.Template.instantiate
#check SOnlyProvenance.Template.abstract
#print axioms SOnlyProvenance.Template.abstract
#check SOnlyProvenance.Template.abstraction_exact
#print axioms SOnlyProvenance.Template.abstraction_exact
#check SOnlyProvenance.Template.holes
#print axioms SOnlyProvenance.Template.holes
#check SOnlyProvenance.Template.scaffold
#print axioms SOnlyProvenance.Template.scaffold
#check SOnlyProvenance.Template.descendant_decomposition
#print axioms SOnlyProvenance.Template.descendant_decomposition
#check SOnlyProvenance.Template.h6_decomposition
#print axioms SOnlyProvenance.Template.h6_decomposition
#check SOnlyProvenance.Template.transfer
#print axioms SOnlyProvenance.Template.transfer
#check SOnlyProvenanceRows.b_carries
#print axioms SOnlyProvenanceRows.b_carries
#check SOnlyProvenanceRows.p_carries
#print axioms SOnlyProvenanceRows.p_carries
#check SOnlyProvenanceRows.valueTag_carries
#print axioms SOnlyProvenanceRows.valueTag_carries
#check SOnlyProvenanceRows.live_carries
#print axioms SOnlyProvenanceRows.live_carries
#check SOnlyProvenanceRows.appender_carries
#print axioms SOnlyProvenanceRows.appender_carries
#check SOnlyProvenanceRows.selectedAction_carries
#print axioms SOnlyProvenanceRows.selectedAction_carries
#check SOnlyProvenanceRows.compileDispatcher_carries
#print axioms SOnlyProvenanceRows.compileDispatcher_carries
#check SOnlyProvenanceRows.compileActions_carries
#print axioms SOnlyProvenanceRows.compileActions_carries
#check SOnlyProvenanceRows.live_fold_carries
#print axioms SOnlyProvenanceRows.live_fold_carries
#check SOnlyProvenanceRows.word_carries
#print axioms SOnlyProvenanceRows.word_carries
#check SOnlyProvenanceRows.seed_carries
#print axioms SOnlyProvenanceRows.seed_carries
#check SOnlyProvenanceRows.environment_carries
#print axioms SOnlyProvenanceRows.environment_carries
#check SOnlyProvenanceRows.other_app_carries
#print axioms SOnlyProvenanceRows.other_app_carries
#check SOnlyProvenanceRows.other_app_class
#print axioms SOnlyProvenanceRows.other_app_class
#check SOnlyProvenanceRows.compiled_call_carries
#print axioms SOnlyProvenanceRows.compiled_call_carries
#check SOnlyProvenanceRows.compiled_call_other
#print axioms SOnlyProvenanceRows.compiled_call_other
#check SOnlyProvenanceRows.route_row_other
#print axioms SOnlyProvenanceRows.route_row_other
#check SOnlyProvenanceRows.route_row_carries
#print axioms SOnlyProvenanceRows.route_row_carries
#check SOnlyProvenanceRows.extend_carries
#print axioms SOnlyProvenanceRows.extend_carries
#check SOnlyProvenanceRows.history_carries
#print axioms SOnlyProvenanceRows.history_carries
#check SOnlyProvenanceRows.pushFirst_other
#print axioms SOnlyProvenanceRows.pushFirst_other
#check SOnlyProvenanceRows.pushSecond_other
#print axioms SOnlyProvenanceRows.pushSecond_other
#check SOnlyProvenanceRows.pushFirst_carries
#print axioms SOnlyProvenanceRows.pushFirst_carries
#check SOnlyProvenanceRows.pushSecond_carries
#print axioms SOnlyProvenanceRows.pushSecond_carries
#check SOnlyProvenanceRows.action_row_carries
#print axioms SOnlyProvenanceRows.action_row_carries
#check SOnlyProvenanceRows.c4_carries
#print axioms SOnlyProvenanceRows.c4_carries
#check SOnlyProvenanceRows.withResponse_other
#print axioms SOnlyProvenanceRows.withResponse_other
#check SOnlyProvenanceRows.withResponse_carries
#print axioms SOnlyProvenanceRows.withResponse_carries
#check SOnlyProvenanceRows.frameFirst_carries
#print axioms SOnlyProvenanceRows.frameFirst_carries
#check SOnlyProvenanceRows.frameSecond_carries
#print axioms SOnlyProvenanceRows.frameSecond_carries
#check SOnlyProvenanceRows.activeShell_carries
#print axioms SOnlyProvenanceRows.activeShell_carries
#check SOnlyProvenanceRows.response_row_carries
#print axioms SOnlyProvenanceRows.response_row_carries
#check SOnlyProvenanceRows.allH6_of_descendants
#print axioms SOnlyProvenanceRows.allH6_of_descendants
#check SOnlyProvenanceRows.allH6_descendant
#print axioms SOnlyProvenanceRows.allH6_descendant
#check SOnlyProvenanceRows.response_h6_inherited_or_root
#print axioms SOnlyProvenanceRows.response_h6_inherited_or_root
#check SOnlyProvenanceRows.response_root_audit
#print axioms SOnlyProvenanceRows.response_root_audit
#check SOnlyProvenanceRows.pending_carries
#print axioms SOnlyProvenanceRows.pending_carries
#check SOnlyProvenanceRows.mutableBase_carries
#print axioms SOnlyProvenanceRows.mutableBase_carries
#check SOnlyProvenanceRows.tombstone_context_carries
#print axioms SOnlyProvenanceRows.tombstone_context_carries
#check SOnlyProvenanceRows.action_context_carries
#print axioms SOnlyProvenanceRows.action_context_carries
#check SOnlyProvenanceRows.completed_context_carries
#print axioms SOnlyProvenanceRows.completed_context_carries
#check SOnlyProvenanceRows.OuterContext
#print axioms SOnlyProvenanceRows.OuterContext
#check SOnlyProvenanceRows.outer_context_carries
#print axioms SOnlyProvenanceRows.outer_context_carries
#check SOnlyEventPattern.routePattern
#print axioms SOnlyEventPattern.routePattern
#check SOnlyEventPattern.targetPattern
#print axioms SOnlyEventPattern.targetPattern
#check SOnlyEventPattern.target_history_count
#print axioms SOnlyEventPattern.target_history_count
#check SOnlyEventPattern.routePattern_sound
#print axioms SOnlyEventPattern.routePattern_sound
#check SOnlyEventPattern.routePattern_matches
#print axioms SOnlyEventPattern.routePattern_matches
#check SOnlyEventPattern.localPattern_sound
#print axioms SOnlyEventPattern.localPattern_sound
#check SOnlyEventPattern.localPattern_matches
#print axioms SOnlyEventPattern.localPattern_matches
#check SOnlyEventPattern.targetPattern_iff
#print axioms SOnlyEventPattern.targetPattern_iff
#check SOnlyEventPattern.completed_target_matches
#print axioms SOnlyEventPattern.completed_target_matches
#check SOnlyEventTransfer.exactChain_sample
#print axioms SOnlyEventTransfer.exactChain_sample
#check SOnlyEventTransfer.persistentSystem
#print axioms SOnlyEventTransfer.persistentSystem
#check SOnlyEventTransfer.trajectory_eq_contractionRun
#print axioms SOnlyEventTransfer.trajectory_eq_contractionRun
#check SOnlyEventTransfer.exactChain_rootReset_sample
#print axioms SOnlyEventTransfer.exactChain_rootReset_sample
#check SOnlyEventTransfer.auditAddress
#print axioms SOnlyEventTransfer.auditAddress
#check SOnlyEventTransfer.readAudit
#print axioms SOnlyEventTransfer.readAudit
#check SOnlyEventTransfer.readPrestate
#print axioms SOnlyEventTransfer.readPrestate
#check SOnlyEventTransfer.freshShell_audit
#print axioms SOnlyEventTransfer.freshShell_audit
#check SOnlyEventTransfer.completed_audit
#print axioms SOnlyEventTransfer.completed_audit
#check SOnlyEventTransfer.freshLayer_audit
#print axioms SOnlyEventTransfer.freshLayer_audit
#check SOnlyEventTransfer.completed_readPrestate
#print axioms SOnlyEventTransfer.completed_readPrestate
#check SOnlyEventTransfer.selectedResponse_readPrestate
#print axioms SOnlyEventTransfer.selectedResponse_readPrestate
#check SOnlyGeneratedOrigins.OriginSet
#print axioms SOnlyGeneratedOrigins.OriginSet
#check SOnlyGeneratedOrigins.RootLicensed
#print axioms SOnlyGeneratedOrigins.RootLicensed
#check SOnlyGeneratedOrigins.Licensed
#print axioms SOnlyGeneratedOrigins.Licensed
#check SOnlyGeneratedOrigins.completed_root_licensed_iff
#print axioms SOnlyGeneratedOrigins.completed_root_licensed_iff
#check SOnlyGeneratedOrigins.rejected_root_licensed
#print axioms SOnlyGeneratedOrigins.rejected_root_licensed
#check SOnlyGeneratedOrigins.response_root_licensed
#print axioms SOnlyGeneratedOrigins.response_root_licensed
#check SOnlyGeneratedOrigins.response_licensed
#print axioms SOnlyGeneratedOrigins.response_licensed
#check SOnlyGeneratedOrigins.holds_endpoint
#print axioms SOnlyGeneratedOrigins.holds_endpoint
#check SOnlyGeneratedOrigins.Preserves
#print axioms SOnlyGeneratedOrigins.Preserves
#check SOnlyGeneratedOrigins.context_inner
#print axioms SOnlyGeneratedOrigins.context_inner
#check SOnlyGeneratedOrigins.preserves_hole
#print axioms SOnlyGeneratedOrigins.preserves_hole
#check SOnlyGeneratedOrigins.preserves_comp
#print axioms SOnlyGeneratedOrigins.preserves_comp
#check SOnlyGeneratedOrigins.queue_context_preserves
#print axioms SOnlyGeneratedOrigins.queue_context_preserves
#check SOnlyGeneratedOrigins.all_applyArgs_parts
#print axioms SOnlyGeneratedOrigins.all_applyArgs_parts
#check SOnlyGeneratedOrigins.action_context_preserves
#print axioms SOnlyGeneratedOrigins.action_context_preserves
#check SOnlyGeneratedOrigins.route_context_other
#print axioms SOnlyGeneratedOrigins.route_context_other
#check SOnlyGeneratedOrigins.route_context_preserves
#print axioms SOnlyGeneratedOrigins.route_context_preserves
#check SOnlyCanonicalOrigins.base_queue_preserves
#print axioms SOnlyCanonicalOrigins.base_queue_preserves
#check SOnlyCanonicalOrigins.fresh_completed_preserves
#print axioms SOnlyCanonicalOrigins.fresh_completed_preserves
#check SOnlyCanonicalOrigins.marked_dispatch_preserves
#print axioms SOnlyCanonicalOrigins.marked_dispatch_preserves
#check SOnlyCanonicalOrigins.local_route_action_preserves
#print axioms SOnlyCanonicalOrigins.local_route_action_preserves
#check SOnlyCanonicalOrigins.selectedFront_context_preserves
#print axioms SOnlyCanonicalOrigins.selectedFront_context_preserves
#check SOnlyCanonicalOrigins.selectedFront_delete_licensed
#print axioms SOnlyCanonicalOrigins.selectedFront_delete_licensed
#check SOnlyCanonicalOrigins.selectedResponse_deleted_licensed
#print axioms SOnlyCanonicalOrigins.selectedResponse_deleted_licensed
#check SOnlySource.scan
#print axioms SOnlySource.scan
#check SOnlySource.iteratePhase_next
#print axioms SOnlySource.iteratePhase_next
#check SOnlySource.consume_prefix
#print axioms SOnlySource.consume_prefix
#check SOnlySource.consume_partial
#print axioms SOnlySource.consume_partial
#check SOnlySource.ordinary_exists_in_prefix
#print axioms SOnlySource.ordinary_exists_in_prefix
#check SOnlySource.Symbol
#print axioms SOnlySource.Symbol
#check SOnlySource.code
#print axioms SOnlySource.code
#check SOnlySource.encodeWord
#print axioms SOnlySource.encodeWord
#check SOnlySource.production
#print axioms SOnlySource.production
#check SOnlySource.production_matches_published
#print axioms SOnlySource.production_matches_published
#check SOnlySource.Config
#print axioms SOnlySource.Config
#check SOnlySource.step
#print axioms SOnlySource.step
#check SOnlySource.iterate
#print axioms SOnlySource.iterate
#check SOnlySource.boundaryPhase
#print axioms SOnlySource.boundaryPhase
#check SOnlySource.encode
#print axioms SOnlySource.encode
#check SOnlySource.code_length
#print axioms SOnlySource.code_length
#check SOnlySource.encodeWord_nil
#print axioms SOnlySource.encodeWord_nil
#check SOnlySource.encodeWord_cons
#print axioms SOnlySource.encodeWord_cons
#check SOnlySource.encodeWord_append
#print axioms SOnlySource.encodeWord_append
#check SOnlySource.scan_code
#print axioms SOnlySource.scan_code
#check SOnlySource.phase_block
#print axioms SOnlySource.phase_block
#check SOnlySource.step_simulation
#print axioms SOnlySource.step_simulation
#check SOnlySource.trajectory_simulation
#print axioms SOnlySource.trajectory_simulation
#check SOnlySource.ordinary_at_offset
#print axioms SOnlySource.ordinary_at_offset
#check SOnlySource.Selected
#print axioms SOnlySource.Selected
#check SOnlySource.Event
#print axioms SOnlySource.Event
#check SOnlySource.phase_at_offset
#print axioms SOnlySource.phase_at_offset
#check SOnlySource.code_head_at_offset
#print axioms SOnlySource.code_head_at_offset
#check SOnlySource.event_in_block
#print axioms SOnlySource.event_in_block
#check SOnlySource.event_at_time
#print axioms SOnlySource.event_at_time
#check SOnlySource.event_at_arbitrary_time
#print axioms SOnlySource.event_at_arbitrary_time
#check SOnlySource.event_exists_iff
#print axioms SOnlySource.event_exists_iff
#check SOnlySource.first_event_exact
#print axioms SOnlySource.first_event_exact
#check SOnlyCounter.pass
#print axioms SOnlyCounter.pass
#check SOnlyCounter.phaseAfter
#print axioms SOnlyCounter.phaseAfter
#check SOnlyCounter.iterate_add
#print axioms SOnlyCounter.iterate_add
#check SOnlyCounter.consume_source_prefix
#print axioms SOnlyCounter.consume_source_prefix
#check SOnlyCounter.pass_append
#print axioms SOnlyCounter.pass_append
#check SOnlyCounter.copies
#print axioms SOnlyCounter.copies
#check SOnlyCounter.copies_zero
#print axioms SOnlyCounter.copies_zero
#check SOnlyCounter.copies_succ
#print axioms SOnlyCounter.copies_succ
#check SOnlyCounter.copies_one
#print axioms SOnlyCounter.copies_one
#check SOnlyCounter.copies_nil
#print axioms SOnlyCounter.copies_nil
#check SOnlyCounter.copies_add
#print axioms SOnlyCounter.copies_add
#check SOnlyCounter.copies_copies
#print axioms SOnlyCounter.copies_copies
#check SOnlyCounter.copies_length
#print axioms SOnlyCounter.copies_length
#check SOnlyCounter.pass_pairs
#print axioms SOnlyCounter.pass_pairs
#check SOnlyCounter.pass_constant_pairs
#print axioms SOnlyCounter.pass_constant_pairs
#check SOnlyCounter.production_12
#print axioms SOnlyCounter.production_12
#check SOnlyCounter.production_13
#print axioms SOnlyCounter.production_13
#check SOnlyCounter.production_14
#print axioms SOnlyCounter.production_14
#check SOnlyCounter.production_15
#print axioms SOnlyCounter.production_15
#check SOnlyCounter.production_16
#print axioms SOnlyCounter.production_16
#check SOnlyCounter.production_17
#print axioms SOnlyCounter.production_17
#check SOnlyCounter.C
#print axioms SOnlyCounter.C
#check SOnlyCounter.T
#print axioms SOnlyCounter.T
#check SOnlyCounter.D
#print axioms SOnlyCounter.D
#check SOnlyCounter.halfcommand
#print axioms SOnlyCounter.halfcommand
#check SOnlyCounter.twice_pow
#print axioms SOnlyCounter.twice_pow
#check SOnlyCounter.two_copies
#print axioms SOnlyCounter.two_copies
#check SOnlyCounter.four_copies
#print axioms SOnlyCounter.four_copies
#check SOnlyCounter.protected_word
#print axioms SOnlyCounter.protected_word
#check SOnlyCounter.C_length
#print axioms SOnlyCounter.C_length
#check SOnlyCounter.T_length
#print axioms SOnlyCounter.T_length
#check SOnlyCounter.increment_command
#print axioms SOnlyCounter.increment_command
#check SOnlyCounter.increment
#print axioms SOnlyCounter.increment
#check SOnlyCounter.protected_command
#print axioms SOnlyCounter.protected_command
#check SOnlyCounter.protected_increment
#print axioms SOnlyCounter.protected_increment
#check SOnlyCounter.decrement_command
#print axioms SOnlyCounter.decrement_command
#check SOnlyCounter.decrement_parity
#print axioms SOnlyCounter.decrement_parity
#check SOnlyCounter.decrement_even_reset
#print axioms SOnlyCounter.decrement_even_reset
#check SOnlyCounter.decrement_odd_reset
#print axioms SOnlyCounter.decrement_odd_reset
#check SOnlyCounter.zero_decrement_command
#print axioms SOnlyCounter.zero_decrement_command
#check SOnlyCounter.zero_decrement_parity_even
#print axioms SOnlyCounter.zero_decrement_parity_even
#check SOnlyCounter.zero_decrement_parity_odd
#print axioms SOnlyCounter.zero_decrement_parity_odd
#check SOnlyCounter.zero_decrement_saturates
#print axioms SOnlyCounter.zero_decrement_saturates
#check SOnlyCounter.zero_decrement_protects
#print axioms SOnlyCounter.zero_decrement_protects
#check SOnlyCounter.zero_decrement_deletes
#print axioms SOnlyCounter.zero_decrement_deletes
#check SOnlyCounter.protected_restart_first
#print axioms SOnlyCounter.protected_restart_first
#check SOnlyCounter.protected_restart_complete
#print axioms SOnlyCounter.protected_restart_complete
#check SOnlyCounter.command_words_even
#print axioms SOnlyCounter.command_words_even
#check SOnlyCounter.parity_word_parity
#print axioms SOnlyCounter.parity_word_parity
#check SOnlyCounter.protected_parity_even
#print axioms SOnlyCounter.protected_parity_even
#check SOnlyCounter.reset_word_even
#print axioms SOnlyCounter.reset_word_even
#check SOnlyCounter.protected_reset_even
#print axioms SOnlyCounter.protected_reset_even
#check SOnlyCounter.CounterWord
#print axioms SOnlyCounter.CounterWord
#check SOnlyCounter.counter_productions_closed
#print axioms SOnlyCounter.counter_productions_closed
#check SOnlyCounter.counterWord_append
#print axioms SOnlyCounter.counterWord_append
#check SOnlyCounter.counterWord_copies
#print axioms SOnlyCounter.counterWord_copies
#check SOnlyCounter.ordinary_counter_word
#print axioms SOnlyCounter.ordinary_counter_word
#check SOnlyCounter.protected_counter_word
#print axioms SOnlyCounter.protected_counter_word
#check SOnlyCounter.pass_counter_word
#print axioms SOnlyCounter.pass_counter_word
#check SOnlyCounter.counter_word_no_selected
#print axioms SOnlyCounter.counter_word_no_selected
#check SOnlyCounter.counter_stages_no_selected
#print axioms SOnlyCounter.counter_stages_no_selected
#check SOnlyEventResponse.target_response_cost
#print axioms SOnlyEventResponse.target_response_cost
#check SOnlyEventResponse.response_final_sample
#print axioms SOnlyEventResponse.response_final_sample
#check SOnlyEventResponse.target_final_sample
#print axioms SOnlyEventResponse.target_final_sample
#check SOnlyEventResponse.target_completion_event_and_readout
#print axioms SOnlyEventResponse.target_completion_event_and_readout
#check SOnlyEventResponse.selectedTarget_event_and_readout
#print axioms SOnlyEventResponse.selectedTarget_event_and_readout
#check SOnlyObserver.Bits
#print axioms SOnlyObserver.Bits
#check SOnlyObserver.rootBit
#print axioms SOnlyObserver.rootBit
#check SOnlyObserver.cover
#print axioms SOnlyObserver.cover
#check SOnlyObserver.cover_complete
#print axioms SOnlyObserver.cover_complete
#check SOnlyObserver.cover_length
#print axioms SOnlyObserver.cover_length
#check SOnlyObserver.leafBits
#print axioms SOnlyObserver.leafBits
#check SOnlyObserver.joinBits
#print axioms SOnlyObserver.joinBits
#check SOnlyObserver.specification
#print axioms SOnlyObserver.specification
#check SOnlyObserver.root_specification
#print axioms SOnlyObserver.root_specification
#check SOnlyObserver.leaf_specification
#print axioms SOnlyObserver.leaf_specification
#check SOnlyObserver.join_specification
#print axioms SOnlyObserver.join_specification
#check SOnlyObserver.State
#print axioms SOnlyObserver.State
#check SOnlyObserver.stateCover
#print axioms SOnlyObserver.stateCover
#check SOnlyObserver.stateCover_complete
#print axioms SOnlyObserver.stateCover_complete
#check SOnlyObserver.stateCover_length
#print axioms SOnlyObserver.stateCover_length
#check SOnlyObserver.leafState
#print axioms SOnlyObserver.leafState
#check SOnlyObserver.joinState
#print axioms SOnlyObserver.joinState
#check SOnlyObserver.run
#print axioms SOnlyObserver.run
#check SOnlyObserver.Occurs
#print axioms SOnlyObserver.Occurs
#check SOnlyObserver.run_bits
#print axioms SOnlyObserver.run_bits
#check SOnlyObserver.accepts_iff_occurs
#print axioms SOnlyObserver.accepts_iff_occurs
#check SOnlyObserver.occurs_iff_subterm
#print axioms SOnlyObserver.occurs_iff_subterm
#check SOnlyObserver.finite_observer_correct
#print axioms SOnlyObserver.finite_observer_correct
#check SOnlyObserver.event
#print axioms SOnlyObserver.event
#check SOnlyObserver.event_iff_matches
#print axioms SOnlyObserver.event_iff_matches
#check SOnlyObserver.event_iff
#print axioms SOnlyObserver.event_iff
#check SOnlyObserver.event_finite_cover
#print axioms SOnlyObserver.event_finite_cover
#check SOnlyStageEvents.selectedResponse_chain
#print axioms SOnlyStageEvents.selectedResponse_chain
#check SOnlyStageEvents.stageStartTime
#print axioms SOnlyStageEvents.stageStartTime
#check SOnlyStageEvents.stageStart_prefix
#print axioms SOnlyStageEvents.stageStart_prefix
#check SOnlyStageEvents.firstJobPreResponseTime
#print axioms SOnlyStageEvents.firstJobPreResponseTime
#check SOnlyStageEvents.firstJob_response_prefix
#print axioms SOnlyStageEvents.firstJob_response_prefix
#check SOnlyStageEvents.sourceTarget_witness_at
#print axioms SOnlyStageEvents.sourceTarget_witness_at
#check SOnlyStageEvents.nonempty_prefix_of_nonempty_iterate
#print axioms SOnlyStageEvents.nonempty_prefix_of_nonempty_iterate
#check SOnlyStageEvents.sourceEvent_reaches_observer
#print axioms SOnlyStageEvents.sourceEvent_reaches_observer
#check SOnlyResult.leadingRun
#print axioms SOnlyResult.leadingRun
#check SOnlyResult.firstRun
#print axioms SOnlyResult.firstRun
#check SOnlyResult.decodeLength
#print axioms SOnlyResult.decodeLength
#check SOnlyResult.readCounter
#print axioms SOnlyResult.readCounter
#check SOnlyResult.decodeMachineValue
#print axioms SOnlyResult.decodeMachineValue
#check SOnlyResult.readMachineValue
#print axioms SOnlyResult.readMachineValue
#check SOnlyResult.leadingRun_non16
#print axioms SOnlyResult.leadingRun_non16
#check SOnlyResult.leadingRun_replicate
#print axioms SOnlyResult.leadingRun_replicate
#check SOnlyResult.firstRun_prefix
#print axioms SOnlyResult.firstRun_prefix
#check SOnlyResult.firstRun_counter
#print axioms SOnlyResult.firstRun_counter
#check SOnlyResult.pow_four
#print axioms SOnlyResult.pow_four
#check SOnlyResult.decodeLength_counter
#print axioms SOnlyResult.decodeLength_counter
#check SOnlyResult.readCounter_correct
#print axioms SOnlyResult.readCounter_correct
#check SOnlyResult.decodeMachineValue_correct
#print axioms SOnlyResult.decodeMachineValue_correct
#check SOnlyResult.readMachineValue_correct
#print axioms SOnlyResult.readMachineValue_correct
#check SOnlyResultBits.decodeBlock
#print axioms SOnlyResultBits.decodeBlock
#check SOnlyResultBits.decodeBlocks
#print axioms SOnlyResultBits.decodeBlocks
#check SOnlyResultBits.published
#print axioms SOnlyResultBits.published
#check SOnlyResultBits.decodeEventWord
#print axioms SOnlyResultBits.decodeEventWord
#check SOnlyResultBits.readMachineBits
#print axioms SOnlyResultBits.readMachineBits
#check SOnlyResultBits.decodeBlock_code
#print axioms SOnlyResultBits.decodeBlock_code
#check SOnlyResultBits.encodeWord_length
#print axioms SOnlyResultBits.encodeWord_length
#check SOnlyResultBits.decodeBlocks_encode
#print axioms SOnlyResultBits.decodeBlocks_encode
#check SOnlyResultBits.event_word
#print axioms SOnlyResultBits.event_word
#check SOnlyResultBits.decodeEventWord_correct
#print axioms SOnlyResultBits.decodeEventWord_correct
#check SOnlyResultBits.readMachineBits_correct
#print axioms SOnlyResultBits.readMachineBits_correct
#check SOnlyResultBits.source_event_result
#print axioms SOnlyResultBits.source_event_result
#check SOnlyWitnessResult.readShell
#print axioms SOnlyWitnessResult.readShell
#check SOnlyWitnessResult.numerical_witness
#print axioms SOnlyWitnessResult.numerical_witness
#check SOnlyCurrentDecoder.findShell
#print axioms SOnlyCurrentDecoder.findShell
#check SOnlyCurrentDecoder.read
#print axioms SOnlyCurrentDecoder.read
#check SOnlyCurrentDecoder.findShell_sound
#print axioms SOnlyCurrentDecoder.findShell_sound
#check SOnlyCurrentDecoder.findShell_none_iff
#print axioms SOnlyCurrentDecoder.findShell_none_iff
#check SOnlyCurrentDecoder.event_iff_found
#print axioms SOnlyCurrentDecoder.event_iff_found
#check SOnlyCurrentDecoder.read_of_found
#print axioms SOnlyCurrentDecoder.read_of_found
#check SOnlyCurrentDecoder.read_of_all_witnesses
#print axioms SOnlyCurrentDecoder.read_of_all_witnesses
#check SOnlyDecoderBound.parseBase_queue_size_lt
#print axioms SOnlyDecoderBound.parseBase_queue_size_lt
#check SOnlyDecoderBound.cellSpine_output_length
#print axioms SOnlyDecoderBound.cellSpine_output_length
#check SOnlyDecoderBound.carrier_output_length
#print axioms SOnlyDecoderBound.carrier_output_length
#check SOnlyDecoderBound.carrierFuel
#print axioms SOnlyDecoderBound.carrierFuel
#check SOnlyDecoderBound.carrierFuel_eq
#print axioms SOnlyDecoderBound.carrierFuel_eq
#check SOnlyDecoderBound.carrierCharge
#print axioms SOnlyDecoderBound.carrierCharge
#check SOnlyDecoderBound.carrierCharge_le
#print axioms SOnlyDecoderBound.carrierCharge_le
#check SOnlyDecoderBound.carrier_cubic_charge
#print axioms SOnlyDecoderBound.carrier_cubic_charge
#check SOnlyDecoderBound.spineVisits
#print axioms SOnlyDecoderBound.spineVisits
#check SOnlyDecoderBound.spine_length_lt
#print axioms SOnlyDecoderBound.spine_length_lt
#check SOnlyDecoderBound.spineVisits_le
#print axioms SOnlyDecoderBound.spineVisits_le
#check SOnlyDecoderBound.spineVisits_quadratic
#print axioms SOnlyDecoderBound.spineVisits_quadratic
#check SOnlyDecoderBoundCurrent.subterm_size_le
#print axioms SOnlyDecoderBoundCurrent.subterm_size_le
#check SOnlyDecoderBoundCurrent.findShell_size_le
#print axioms SOnlyDecoderBoundCurrent.findShell_size_le
#check SOnlyDecoderBoundCurrent.readShellFuel
#print axioms SOnlyDecoderBoundCurrent.readShellFuel
#check SOnlyDecoderBoundCurrent.readShellFuel_eq
#print axioms SOnlyDecoderBoundCurrent.readShellFuel_eq
#check SOnlyDecoderBoundCurrent.readFuel
#print axioms SOnlyDecoderBoundCurrent.readFuel
#check SOnlyDecoderBoundCurrent.readFuel_eq
#print axioms SOnlyDecoderBoundCurrent.readFuel_eq
#check SOnlyDecoderBoundCurrent.selected_audit_size_le
#print axioms SOnlyDecoderBoundCurrent.selected_audit_size_le
#check SOnlySchedulerOrigins.allH6_mono
#print axioms SOnlySchedulerOrigins.allH6_mono
#check SOnlySchedulerOrigins.Wraps
#print axioms SOnlySchedulerOrigins.Wraps
#check SOnlySchedulerOrigins.wraps_nil
#print axioms SOnlySchedulerOrigins.wraps_nil
#check SOnlySchedulerOrigins.wraps_left
#print axioms SOnlySchedulerOrigins.wraps_left
#check SOnlySchedulerOrigins.wraps_right
#print axioms SOnlySchedulerOrigins.wraps_right
#check SOnlySchedulerOrigins.Ordinary
#print axioms SOnlySchedulerOrigins.Ordinary
#check SOnlySchedulerOrigins.ordinary_app
#print axioms SOnlySchedulerOrigins.ordinary_app
#check SOnlySchedulerOrigins.ordinary_s_pair
#print axioms SOnlySchedulerOrigins.ordinary_s_pair
#check SOnlySchedulerOrigins.ordinary_b_app
#print axioms SOnlySchedulerOrigins.ordinary_b_app
#check SOnlySchedulerOrigins.C_ordinary
#print axioms SOnlySchedulerOrigins.C_ordinary
#check SOnlySchedulerOrigins.environment_ordinary
#print axioms SOnlySchedulerOrigins.environment_ordinary
#check SOnlySchedulerOrigins.clockWrappers_ordinary
#print axioms SOnlySchedulerOrigins.clockWrappers_ordinary
#check SOnlySchedulerOrigins.clockExit_ordinary
#print axioms SOnlySchedulerOrigins.clockExit_ordinary
#check SOnlySchedulerOrigins.base_ordinary
#print axioms SOnlySchedulerOrigins.base_ordinary
#check SOnlySchedulerOrigins.pending_wraps
#print axioms SOnlySchedulerOrigins.pending_wraps
#check SOnlySchedulerOrigins.clock_wrappers_wraps
#print axioms SOnlySchedulerOrigins.clock_wrappers_wraps
#check SOnlySchedulerOrigins.positive_clock_licensed
#print axioms SOnlySchedulerOrigins.positive_clock_licensed
#check SOnlySchedulerOrigins.zero_clock_licensed
#print axioms SOnlySchedulerOrigins.zero_clock_licensed
#check SOnlySchedulerOrigins.fuel_rows_licensed
#print axioms SOnlySchedulerOrigins.fuel_rows_licensed
#check SOnlySchedulerOrigins.SamplesLicensed
#print axioms SOnlySchedulerOrigins.SamplesLicensed
#check SOnlySchedulerOrigins.fuel_list_licensed
#print axioms SOnlySchedulerOrigins.fuel_list_licensed
#check SOnlySchedulerOrigins.clock_tail_licensed
#print axioms SOnlySchedulerOrigins.clock_tail_licensed
#check SOnlySchedulerOrigins.clock_list_licensed
#print axioms SOnlySchedulerOrigins.clock_list_licensed
#check SOnlySchedulerOrigins.phase_list_licensed
#print axioms SOnlySchedulerOrigins.phase_list_licensed
#check SOnlySchedulerOrigins.handoff_list_licensed
#print axioms SOnlySchedulerOrigins.handoff_list_licensed
#check SOnlySchedulerOrigins.initial_licensed
#print axioms SOnlySchedulerOrigins.initial_licensed
#check SOnlySchedulerOrigins.prelude_list_licensed
#print axioms SOnlySchedulerOrigins.prelude_list_licensed
#check SOnlyResponseLabels.responseLabel?
#print axioms SOnlyResponseLabels.responseLabel?
#check SOnlyResponseLabels.OnlyLabel
#print axioms SOnlyResponseLabels.OnlyLabel
#check SOnlyResponseLabels.exactChains_same_samples
#print axioms SOnlyResponseLabels.exactChains_same_samples
#check SOnlyResponseLabels.responsePairs_onlyLabel
#print axioms SOnlyResponseLabels.responsePairs_onlyLabel
#check SOnlyResponseLabels.selectedResponse_labelledChain
#print axioms SOnlyResponseLabels.selectedResponse_labelledChain
#check SOnlyResponseLabels.selectedResponse_onlyLabel
#print axioms SOnlyResponseLabels.selectedResponse_onlyLabel
#check SOnlyResponseLabels.sourceLabel?
#print axioms SOnlyResponseLabels.sourceLabel?
#check SOnlyResponseLabels.SourceLabels
#print axioms SOnlyResponseLabels.SourceLabels
#check SOnlyResponseLabels.sourceLabels_prepend
#print axioms SOnlyResponseLabels.sourceLabels_prepend
#check SOnlyResponseLabels.selectedNonemptyPendingPrefix_labelled
#print axioms SOnlyResponseLabels.selectedNonemptyPendingPrefix_labelled
#check SOnlyResponseLabels.sourceLabels_append_last
#print axioms SOnlyResponseLabels.sourceLabels_append_last
#check SOnlyResponseLabels.completeNonemptyJob_sourceLabels
#print axioms SOnlyResponseLabels.completeNonemptyJob_sourceLabels
#check SOnlyResponseLabels.target_sourceLabel_iff
#print axioms SOnlyResponseLabels.target_sourceLabel_iff
#check SOnlyResponseLabels.no_target_script_of_no_source_event
#print axioms SOnlyResponseLabels.no_target_script_of_no_source_event
#check SOnlyResponseLabels.NoResponseLabels
#print axioms SOnlyResponseLabels.NoResponseLabels
#check SOnlyResponseLabels.noResponse_sourceLabels
#print axioms SOnlyResponseLabels.noResponse_sourceLabels
#check SOnlyResponseLabels.sourceLabels_append
#print axioms SOnlyResponseLabels.sourceLabels_append
#check SOnlyResponseLabels.fuel_noResponse
#print axioms SOnlyResponseLabels.fuel_noResponse
#check SOnlyResponseLabels.clockTail_noResponse
#print axioms SOnlyResponseLabels.clockTail_noResponse
#check SOnlyResponseLabels.phase_noResponse
#print axioms SOnlyResponseLabels.phase_noResponse
#check SOnlyResponseLabels.handoff_noResponse
#print axioms SOnlyResponseLabels.handoff_noResponse
#check SOnlyResponseLabels.LabelledNonfinalJobs
#print axioms SOnlyResponseLabels.LabelledNonfinalJobs
#check SOnlyResponseLabels.nonfinalJobs_labelled
#print axioms SOnlyResponseLabels.nonfinalJobs_labelled
#check SOnlyResponseLabels.allNonemptyRaw_labelled
#print axioms SOnlyResponseLabels.allNonemptyRaw_labelled
#check SOnlyResponseLabels.sourceLabels_mono
#print axioms SOnlyResponseLabels.sourceLabels_mono
#check SOnlyResponseLabels.prelude_noResponse
#print axioms SOnlyResponseLabels.prelude_noResponse
#check SOnlyResponseLabels.positiveStages_labelled
#print axioms SOnlyResponseLabels.positiveStages_labelled
#check SOnlyResponseLabels.contractionRun_label_has_source
#print axioms SOnlyResponseLabels.contractionRun_label_has_source
#check SOnlyResponseLabels.no_target_script_on_event_free_run
#print axioms SOnlyResponseLabels.no_target_script_on_event_free_run
#check SOnlyResponseLabels.stageStart_labelled
#print axioms SOnlyResponseLabels.stageStart_labelled
#check SOnlyResponseLabels.firstJob_response_prefix_labelled
#print axioms SOnlyResponseLabels.firstJob_response_prefix_labelled
#check SOnlyResponseLabels.no_target_script_before_firstJob_response
#print axioms SOnlyResponseLabels.no_target_script_before_firstJob_response
#check SOnlyGlobalAncestors.appenderResult_ordinary
#print axioms SOnlyGlobalAncestors.appenderResult_ordinary
#check SOnlyGlobalAncestors.actionResult_ordinary
#print axioms SOnlyGlobalAncestors.actionResult_ordinary
#check SOnlyGlobalAncestors.completedRoute_ordinary
#print axioms SOnlyGlobalAncestors.completedRoute_ordinary
#check SOnlyGlobalAncestors.completed_licensed
#print axioms SOnlyGlobalAncestors.completed_licensed
#check SOnlyGlobalAncestors.freshContinuationParents_wraps
#print axioms SOnlyGlobalAncestors.freshContinuationParents_wraps
#check SOnlyGlobalAncestors.markedHField_ordinary
#print axioms SOnlyGlobalAncestors.markedHField_ordinary
#check SOnlyGlobalAncestors.markedCompleted_ordinary
#print axioms SOnlyGlobalAncestors.markedCompleted_ordinary
#check SOnlyGlobalAncestors.markedCompleted_of_completed
#print axioms SOnlyGlobalAncestors.markedCompleted_of_completed
#check SOnlyGlobalAncestors.markedContinuationParents_wraps
#print axioms SOnlyGlobalAncestors.markedContinuationParents_wraps
#check SOnlyGlobalAncestors.markedContinuationParents_wraps_of_completed
#print axioms SOnlyGlobalAncestors.markedContinuationParents_wraps_of_completed
#check SOnlyGlobalAncestors.normalMarker_licensed_of_completed
#print axioms SOnlyGlobalAncestors.normalMarker_licensed_of_completed
#check SOnlyGlobalAncestors.normalMarker_licensed
#print axioms SOnlyGlobalAncestors.normalMarker_licensed
#check SOnlyGlobalAncestors.emptyMarker_licensed
#print axioms SOnlyGlobalAncestors.emptyMarker_licensed
#check SOnlyGlobalAncestors.rebuild_inner
#print axioms SOnlyGlobalAncestors.rebuild_inner
#check SOnlyGlobalAncestors.normalMarker_licensed_of_erase
#print axioms SOnlyGlobalAncestors.normalMarker_licensed_of_erase
#check SOnlyGlobalAncestors.LicensedParents
#print axioms SOnlyGlobalAncestors.LicensedParents
#check SOnlyGlobalAncestors.LicensedParents.wraps
#print axioms SOnlyGlobalAncestors.LicensedParents.wraps
#check SOnlyGlobalAncestors.LicensedParents.mono
#print axioms SOnlyGlobalAncestors.LicensedParents.mono
#check SOnlyGlobalAncestors.LicensedParents.nil
#print axioms SOnlyGlobalAncestors.LicensedParents.nil
#check SOnlyGlobalAncestors.LicensedParents.fresh
#print axioms SOnlyGlobalAncestors.LicensedParents.fresh
#check SOnlyGlobalAncestors.LicensedParents.marked
#print axioms SOnlyGlobalAncestors.LicensedParents.marked
#check SOnlyGlobalAncestors.LicensedParents.empty
#print axioms SOnlyGlobalAncestors.LicensedParents.empty
#check SOnlyGlobalAncestors.LicensedParents.pending
#print axioms SOnlyGlobalAncestors.LicensedParents.pending
#check SOnlyGlobalAncestors.LicensedParents.left
#print axioms SOnlyGlobalAncestors.LicensedParents.left
#check SOnlyGlobalAncestors.LicensedParents.right
#print axioms SOnlyGlobalAncestors.LicensedParents.right
#check SOnlyGlobalAncestors.LicensedParents.clock_wrappers
#print axioms SOnlyGlobalAncestors.LicensedParents.clock_wrappers
#check SOnlyGlobalOrigins.samples_append
#print axioms SOnlyGlobalOrigins.samples_append
#check SOnlyGlobalOrigins.responsePairs_licensed
#print axioms SOnlyGlobalOrigins.responsePairs_licensed
#check SOnlyGlobalOrigins.selectedResponse_licensedChain
#print axioms SOnlyGlobalOrigins.selectedResponse_licensedChain
#check SOnlyGlobalOrigins.selectedResponse_licensed
#print axioms SOnlyGlobalOrigins.selectedResponse_licensed
#check SOnlyGlobalOrigins.SourceAllowed
#print axioms SOnlyGlobalOrigins.SourceAllowed
#check SOnlyGlobalOrigins.sourceAllowed_mono
#print axioms SOnlyGlobalOrigins.sourceAllowed_mono
#check SOnlyGlobalOrigins.sourceAllowed_tail
#print axioms SOnlyGlobalOrigins.sourceAllowed_tail
#check SOnlyGlobalOrigins.selectedNonemptyPendingPrefix_licensed
#print axioms SOnlyGlobalOrigins.selectedNonemptyPendingPrefix_licensed
#check SOnlyGlobalOrigins.selectedNonemptySweepToFreshCheck_licensed
#print axioms SOnlyGlobalOrigins.selectedNonemptySweepToFreshCheck_licensed
#check SOnlyGlobalOrigins.completeNonemptyJob_licensed
#print axioms SOnlyGlobalOrigins.completeNonemptyJob_licensed
#check SOnlyGlobalTerminal.completeNonemptyTerminalJobRaw_licensed
#print axioms SOnlyGlobalTerminal.completeNonemptyTerminalJobRaw_licensed
#check SOnlyFirstEventOrigins.AddOrigin
#print axioms SOnlyFirstEventOrigins.AddOrigin
#check SOnlyFirstEventOrigins.rootLicensed_mono
#print axioms SOnlyFirstEventOrigins.rootLicensed_mono
#check SOnlyFirstEventOrigins.licensed_mono
#print axioms SOnlyFirstEventOrigins.licensed_mono
#check SOnlyFirstEventOrigins.licensed_add
#print axioms SOnlyFirstEventOrigins.licensed_add
#check SOnlyFirstEventOrigins.incomplete_response_licensed
#print axioms SOnlyFirstEventOrigins.incomplete_response_licensed
#check SOnlyFirstEventOrigins.response_licensed_add
#print axioms SOnlyFirstEventOrigins.response_licensed_add
#check SOnlyFirstEventOrigins.descendant_of_subterm
#print axioms SOnlyFirstEventOrigins.descendant_of_subterm
#check SOnlyFirstEventOrigins.fresh_shape_h6
#print axioms SOnlyFirstEventOrigins.fresh_shape_h6
#check SOnlyFirstEventOrigins.target_witness_origin
#print axioms SOnlyFirstEventOrigins.target_witness_origin
#check SOnlyFirstEventOrigins.event_false_of_excludes
#print axioms SOnlyFirstEventOrigins.event_false_of_excludes
#check SOnlyFirstEventOrigins.all_target_audits
#print axioms SOnlyFirstEventOrigins.all_target_audits
#check SOnlyFirstEventOrigins.all_target_prestates
#print axioms SOnlyFirstEventOrigins.all_target_prestates
#check SOnlyFirstEventOrigins.current_read_of_added_origin
#print axioms SOnlyFirstEventOrigins.current_read_of_added_origin
#check SOnlyGlobalStages.LicensedNonfinalJobs
#print axioms SOnlyGlobalStages.LicensedNonfinalJobs
#check SOnlyGlobalStages.nonfinalJobs_licensed
#print axioms SOnlyGlobalStages.nonfinalJobs_licensed
#check SOnlyGlobalStages.allNonemptyRaw_licensed
#print axioms SOnlyGlobalStages.allNonemptyRaw_licensed
#check SOnlyGlobalStages.positiveStages_licensed
#print axioms SOnlyGlobalStages.positiveStages_licensed
#check SOnlyGlobalStages.contractionRun_licensed
#print axioms SOnlyGlobalStages.contractionRun_licensed
#check SOnlyGlobalStages.no_event_on_nonempty_event_free_run
#print axioms SOnlyGlobalStages.no_event_on_nonempty_event_free_run
#check SOnlyEventEquivalence.NoPrematureEmpty
#print axioms SOnlyEventEquivalence.NoPrematureEmpty
#check SOnlyEventEquivalence.nonempty_of_event_free
#print axioms SOnlyEventEquivalence.nonempty_of_event_free
#check SOnlyEventEquivalence.event_exists_iff
#print axioms SOnlyEventEquivalence.event_exists_iff
#check SOnlyFirstEventResponse.response_endpoint
#print axioms SOnlyFirstEventResponse.response_endpoint
#check SOnlyFirstEventResponse.responsePairs_licensed_split
#print axioms SOnlyFirstEventResponse.responsePairs_licensed_split
#check SOnlyFirstEventResponse.zeroRun_erase
#print axioms SOnlyFirstEventResponse.zeroRun_erase
#check SOnlyFirstEventResponse.target_response_sharp
#print axioms SOnlyFirstEventResponse.target_response_sharp
#check SOnlyFirstEventResponse.target_response_all_witnesses
#print axioms SOnlyFirstEventResponse.target_response_all_witnesses
#check SOnlyFirstEventResponse.selectedTarget_response_all_witnesses
#print axioms SOnlyFirstEventResponse.selectedTarget_response_all_witnesses
#check SOnlyGlobalFirstPrefix.stageStart_licensed
#print axioms SOnlyGlobalFirstPrefix.stageStart_licensed
#check SOnlyGlobalFirstPrefix.firstJob_response_prefix_licensed
#print axioms SOnlyGlobalFirstPrefix.firstJob_response_prefix_licensed
#check SOnlyGlobalFirstEvent.licensed_prefix_silent
#print axioms SOnlyGlobalFirstEvent.licensed_prefix_silent
#check SOnlyGlobalFirstEvent.sourceTarget_globally_first
#print axioms SOnlyGlobalFirstEvent.sourceTarget_globally_first
#check SOnlyGlobalFirstEvent.firstSourceEvent_current_read
#print axioms SOnlyGlobalFirstEvent.firstSourceEvent_current_read
#check SOnlyGlobalFirstStructure.target_response_structure
#print axioms SOnlyGlobalFirstStructure.target_response_structure
#check SOnlyGlobalFirstStructure.selectedTarget_response_structure
#print axioms SOnlyGlobalFirstStructure.selectedTarget_response_structure
#check SOnlyGlobalFirstStructure.sourceTarget_first_structure
#print axioms SOnlyGlobalFirstStructure.sourceTarget_first_structure
#check SOnlyGlobalFirstStructure.firstSourceEvent_structure
#print axioms SOnlyGlobalFirstStructure.firstSourceEvent_structure
#check SOnlyGlobalFirstStructure.firstSourceEvent_first_acceptance
#print axioms SOnlyGlobalFirstStructure.firstSourceEvent_first_acceptance
#check SOnlyInitial.Low
#print axioms SOnlyInitial.Low
#check SOnlyInitial.Low.arity
#print axioms SOnlyInitial.Low.arity
#check SOnlyInitial.Low.subterm
#print axioms SOnlyInitial.Low.subterm
#check SOnlyInitial.low_live
#print axioms SOnlyInitial.low_live
#check SOnlyInitial.live_arity
#print axioms SOnlyInitial.live_arity
#check SOnlyInitial.low_word
#print axioms SOnlyInitial.low_word
#check SOnlyInitial.low_appender
#print axioms SOnlyInitial.low_appender
#check SOnlyInitial.low_action
#print axioms SOnlyInitial.low_action
#check SOnlyInitial.low_compile
#print axioms SOnlyInitial.low_compile
#check SOnlyInitial.low_generator
#print axioms SOnlyInitial.low_generator
#check SOnlyInitial.initial_low
#print axioms SOnlyInitial.initial_low
#check SOnlyInitial.low_not_local
#print axioms SOnlyInitial.low_not_local
#check SOnlyInitial.initial_event_false
#print axioms SOnlyInitial.initial_event_false
#check SOnlyMachine.put
#print axioms SOnlyMachine.put
#check SOnlyMachine.put_same
#print axioms SOnlyMachine.put_same
#check SOnlyMachine.put_other
#print axioms SOnlyMachine.put_other
#check SOnlyMachine.put_put
#print axioms SOnlyMachine.put_put
#check SOnlyMachine.put_self
#print axioms SOnlyMachine.put_self
#check SOnlyMachine.put_comm
#print axioms SOnlyMachine.put_comm
#check SOnlyMachine.Action
#print axioms SOnlyMachine.Action
#check SOnlyMachine.Row
#print axioms SOnlyMachine.Row
#check SOnlyMachine.State
#print axioms SOnlyMachine.State
#check SOnlyMachine.Table
#print axioms SOnlyMachine.Table
#check SOnlyMachine.step
#print axioms SOnlyMachine.step
#check SOnlyMachine.run
#print axioms SOnlyMachine.run
#check SOnlyMachine.run_zero
#print axioms SOnlyMachine.run_zero
#check SOnlyMachine.run_succ
#print axioms SOnlyMachine.run_succ
#check SOnlyMachine.run_add
#print axioms SOnlyMachine.run_add
#check SOnlyMachine.run_halt
#print axioms SOnlyMachine.run_halt
#check SOnlyMachine.next
#print axioms SOnlyMachine.next
#check SOnlyMachine.scan_from
#print axioms SOnlyMachine.scan_from
#check SOnlyMachine.scan
#print axioms SOnlyMachine.scan
#check SOnlyMachine.Instruction
#print axioms SOnlyMachine.Instruction
#check SOnlyMachine.Machine
#print axioms SOnlyMachine.Machine
#check SOnlyMachine.SourceState
#print axioms SOnlyMachine.SourceState
#check SOnlyMachine.sourceStep
#print axioms SOnlyMachine.sourceStep
#check SOnlyMachine.Cell
#print axioms SOnlyMachine.Cell
#check SOnlyMachine.entry
#print axioms SOnlyMachine.entry
#check SOnlyMachine.compile
#print axioms SOnlyMachine.compile
#check SOnlyMachine.normal
#print axioms SOnlyMachine.normal
#check SOnlyMachine.encode
#print axioms SOnlyMachine.encode
#check SOnlyMachine.normal_data
#print axioms SOnlyMachine.normal_data
#check SOnlyMachine.normal_I
#print axioms SOnlyMachine.normal_I
#check SOnlyMachine.normal_S
#print axioms SOnlyMachine.normal_S
#check SOnlyMachine.normal_F
#print axioms SOnlyMachine.normal_F
#check SOnlyMachine.normal_U
#print axioms SOnlyMachine.normal_U
#check SOnlyMachine.normal_V
#print axioms SOnlyMachine.normal_V
#check SOnlyMachine.normal_put
#print axioms SOnlyMachine.normal_put
#check SOnlyMachine.inc_macro
#print axioms SOnlyMachine.inc_macro
#check SOnlyMachine.run_join
#print axioms SOnlyMachine.run_join
#check SOnlyMachine.dec_success_macro
#print axioms SOnlyMachine.dec_success_macro
#check SOnlyMachine.dec_zero_macro
#print axioms SOnlyMachine.dec_zero_macro
#check SOnlyMachine.macroCost
#print axioms SOnlyMachine.macroCost
#check SOnlyMachine.macroCost_pos
#print axioms SOnlyMachine.macroCost_pos
#check SOnlyMachine.macro_simulation
#print axioms SOnlyMachine.macro_simulation
#check SOnlyMachine.sourceRun
#print axioms SOnlyMachine.sourceRun
#check SOnlyMachine.elapsed
#print axioms SOnlyMachine.elapsed
#check SOnlyMachine.elapsed_ge
#print axioms SOnlyMachine.elapsed_ge
#check SOnlyMachine.run_simulation
#print axioms SOnlyMachine.run_simulation
#check SOnlyMachine.entry_halt_iff
#print axioms SOnlyMachine.entry_halt_iff
#check SOnlyMachine.run_after_halt
#print axioms SOnlyMachine.run_after_halt
#check SOnlyMachine.halt_iff
#print axioms SOnlyMachine.halt_iff
#check SOnlyMachine.halt_output
#print axioms SOnlyMachine.halt_output
#check SOnlyMachine.initial
#print axioms SOnlyMachine.initial
#check SOnlyMachine.arbitrary_input_halt_iff
#print axioms SOnlyMachine.arbitrary_input_halt_iff
#check SOnlyMachineBP2.Command
#print axioms SOnlyMachineBP2.Command
#check SOnlyMachineBP2.Program
#print axioms SOnlyMachineBP2.Program
#check SOnlyMachineBP2.State
#print axioms SOnlyMachineBP2.State
#check SOnlyMachineBP2.execute
#print axioms SOnlyMachineBP2.execute
#check SOnlyMachineBP2.step?
#print axioms SOnlyMachineBP2.step?
#check SOnlyMachineBP2.advance
#print axioms SOnlyMachineBP2.advance
#check SOnlyMachineBP2.run
#print axioms SOnlyMachineBP2.run
#check SOnlyMachineBP2.Halted
#print axioms SOnlyMachineBP2.Halted
#check SOnlyMachineBP2.run_zero
#print axioms SOnlyMachineBP2.run_zero
#check SOnlyMachineBP2.run_succ
#print axioms SOnlyMachineBP2.run_succ
#check SOnlyMachineBP2.run_add
#print axioms SOnlyMachineBP2.run_add
#check SOnlyMachineBP2.step_none_iff
#print axioms SOnlyMachineBP2.step_none_iff
#check SOnlyMachineBP2.advance_halted
#print axioms SOnlyMachineBP2.advance_halted
#check SOnlyMachineBP2.run_halted
#print axioms SOnlyMachineBP2.run_halted
#check SOnlyMachineBP2.Straight
#print axioms SOnlyMachineBP2.Straight
#check SOnlyMachineBP2.straight_append
#print axioms SOnlyMachineBP2.straight_append
#check SOnlyMachineBP2.fetch_boundary
#print axioms SOnlyMachineBP2.fetch_boundary
#check SOnlyMachineBP2.advance_boundary
#print axioms SOnlyMachineBP2.advance_boundary
#check SOnlyMachineBP2.straight_run
#print axioms SOnlyMachineBP2.straight_run
#check SOnlyMachineBP2.zero_guard
#print axioms SOnlyMachineBP2.zero_guard
#check SOnlyMachineBP2.add
#print axioms SOnlyMachineBP2.add
#check SOnlyMachineBP2.sub
#print axioms SOnlyMachineBP2.sub
#check SOnlyMachineBP2.add_straight
#print axioms SOnlyMachineBP2.add_straight
#check SOnlyMachineBP2.sub_straight
#print axioms SOnlyMachineBP2.sub_straight
#check SOnlyMachineBP2.addMany
#print axioms SOnlyMachineBP2.addMany
#check SOnlyMachineBP2.subMany
#print axioms SOnlyMachineBP2.subMany
#check SOnlyMachineBP2.plus
#print axioms SOnlyMachineBP2.plus
#check SOnlyMachineBP2.minus
#print axioms SOnlyMachineBP2.minus
#check SOnlyMachineBP2.plus_nil
#print axioms SOnlyMachineBP2.plus_nil
#check SOnlyMachineBP2.minus_nil
#print axioms SOnlyMachineBP2.minus_nil
#check SOnlyMachineBP2.plus_at
#print axioms SOnlyMachineBP2.plus_at
#check SOnlyMachineBP2.plus_absent
#print axioms SOnlyMachineBP2.plus_absent
#check SOnlyMachineBP2.plus_cons
#print axioms SOnlyMachineBP2.plus_cons
#check SOnlyMachineBP2.minus_plus
#print axioms SOnlyMachineBP2.minus_plus
#check SOnlyMachineBP2.addMany_straight
#print axioms SOnlyMachineBP2.addMany_straight
#check SOnlyMachineBP2.subMany_straight
#print axioms SOnlyMachineBP2.subMany_straight
#check SOnlyMachineBP2.guarded
#print axioms SOnlyMachineBP2.guarded
#check SOnlyMachineBP2.guard_pair_straight
#print axioms SOnlyMachineBP2.guard_pair_straight
#check SOnlyMachineBP2.guarded_inactive
#print axioms SOnlyMachineBP2.guarded_inactive
#check SOnlyMachineBP2.guarded_active
#print axioms SOnlyMachineBP2.guarded_active
#check SOnlyMachineBP2.initializer
#print axioms SOnlyMachineBP2.initializer
#check SOnlyMachineBP2.initializer_first
#print axioms SOnlyMachineBP2.initializer_first
#check SOnlyMachineBP2.initializer_restart
#print axioms SOnlyMachineBP2.initializer_restart
#check SOnlyMachineBP2.Enumeration
#print axioms SOnlyMachineBP2.Enumeration
#check SOnlyMachineBP2.unary
#print axioms SOnlyMachineBP2.unary
#check SOnlyMachineBP2.count_unary_of_nodup
#print axioms SOnlyMachineBP2.count_unary_of_nodup
#check SOnlyMachineBP2.count_unary
#print axioms SOnlyMachineBP2.count_unary
#check SOnlyMachineBP2.absent_unary
#print axioms SOnlyMachineBP2.absent_unary
#check SOnlyMachineBP2.plus_unary
#print axioms SOnlyMachineBP2.plus_unary
#check SOnlyMachineBP2.straight_flatMap
#print axioms SOnlyMachineBP2.straight_flatMap
#check SOnlyMachineBP2.run_join
#print axioms SOnlyMachineBP2.run_join
#check SOnlyMachineBP2.Reaches
#print axioms SOnlyMachineBP2.Reaches
#check SOnlyMachineBP2.reaches_trans
#print axioms SOnlyMachineBP2.reaches_trans
#check SOnlyMachineWaterfallBP2.Cell
#print axioms SOnlyMachineWaterfallBP2.Cell
#check SOnlyMachineWaterfallBP2.cells
#print axioms SOnlyMachineWaterfallBP2.cells
#check SOnlyMachineWaterfallBP2.store
#print axioms SOnlyMachineWaterfallBP2.store
#check SOnlyMachineWaterfallBP2.ready
#print axioms SOnlyMachineWaterfallBP2.ready
#check SOnlyMachineWaterfallBP2.initWeight
#print axioms SOnlyMachineWaterfallBP2.initWeight
#check SOnlyMachineWaterfallBP2.triggerWeight
#print axioms SOnlyMachineWaterfallBP2.triggerWeight
#check SOnlyMachineWaterfallBP2.initCode
#print axioms SOnlyMachineWaterfallBP2.initCode
#check SOnlyMachineWaterfallBP2.triggerCode
#print axioms SOnlyMachineWaterfallBP2.triggerCode
#check SOnlyMachineWaterfallBP2.sweepWeight
#print axioms SOnlyMachineWaterfallBP2.sweepWeight
#check SOnlyMachineWaterfallBP2.sweep
#print axioms SOnlyMachineWaterfallBP2.sweep
#check SOnlyMachineWaterfallBP2.test
#print axioms SOnlyMachineWaterfallBP2.test
#check SOnlyMachineWaterfallBP2.prologue
#print axioms SOnlyMachineWaterfallBP2.prologue
#check SOnlyMachineWaterfallBP2.compile
#print axioms SOnlyMachineWaterfallBP2.compile
#check SOnlyMachineWaterfallBP2.initialization
#print axioms SOnlyMachineWaterfallBP2.initialization
#check SOnlyMachineWaterfallBP2.prologue_straight
#print axioms SOnlyMachineWaterfallBP2.prologue_straight
#check SOnlyMachineWaterfallBP2.sweep_straight
#print axioms SOnlyMachineWaterfallBP2.sweep_straight
#check SOnlyMachineWaterfallBP2.test_straight
#print axioms SOnlyMachineWaterfallBP2.test_straight
#check SOnlyMachineWaterfallBP2.tests_straight
#print axioms SOnlyMachineWaterfallBP2.tests_straight
#check SOnlyMachineWaterfallBP2.marker_dec
#print axioms SOnlyMachineWaterfallBP2.marker_dec
#check SOnlyMachineWaterfallBP2.ordinary_marker_pair
#print axioms SOnlyMachineWaterfallBP2.ordinary_marker_pair
#check SOnlyMachineWaterfallBP2.tick
#print axioms SOnlyMachineWaterfallBP2.tick
#check SOnlyMachineWaterfallBP2.exit_pass
#print axioms SOnlyMachineWaterfallBP2.exit_pass
#check SOnlyMachineWaterfallBP2.pending
#print axioms SOnlyMachineWaterfallBP2.pending
#check SOnlyMachineWaterfallBP2.test_active
#print axioms SOnlyMachineWaterfallBP2.test_active
#check SOnlyMachineWaterfallBP2.split_at
#print axioms SOnlyMachineWaterfallBP2.split_at
#check SOnlyMachineWaterfallBP2.detect_event
#print axioms SOnlyMachineWaterfallBP2.detect_event
#check SOnlyMachineWaterfallBP2.dispatch_raw
#print axioms SOnlyMachineWaterfallBP2.dispatch_raw
#check SOnlyMachineWaterfallBP2.dispatch_nonhalt
#print axioms SOnlyMachineWaterfallBP2.dispatch_nonhalt
#check SOnlyMachineWaterfallBP2.dispatch_halt
#print axioms SOnlyMachineWaterfallBP2.dispatch_halt
#check SOnlyMachineWaterfallBP2.nonhalt_event
#print axioms SOnlyMachineWaterfallBP2.nonhalt_event
#check SOnlyMachineWaterfallBP2.halt_event
#print axioms SOnlyMachineWaterfallBP2.halt_event
#check SOnlyMachineWaterfallBP2.wait_ticks
#print axioms SOnlyMachineWaterfallBP2.wait_ticks
#check SOnlyMachineWaterfallBP2.delayed_nonhalt_event
#print axioms SOnlyMachineWaterfallBP2.delayed_nonhalt_event
#check SOnlyMachineWaterfallBP2.delayed_halt_event
#print axioms SOnlyMachineWaterfallBP2.delayed_halt_event
#check SOnlyMachineWaterfallBP2.compile_nonempty
#print axioms SOnlyMachineWaterfallBP2.compile_nonempty
#check SOnlyMachineWaterfallBP2.final_output
#print axioms SOnlyMachineWaterfallBP2.final_output
#check SOnlyMachineWaterfallBP2.readOutput
#print axioms SOnlyMachineWaterfallBP2.readOutput
#check SOnlyMachineWaterfallBP2.readOutput_correct
#print axioms SOnlyMachineWaterfallBP2.readOutput_correct
#check SOnlyMachineClock.Clock
#print axioms SOnlyMachineClock.Clock
#check SOnlyMachineClock.normalized
#print axioms SOnlyMachineClock.normalized
#check SOnlyMachineClock.row
#print axioms SOnlyMachineClock.row
#check SOnlyMachineClock.normalized_zero
#print axioms SOnlyMachineClock.normalized_zero
#check SOnlyMachineClock.normalized_other
#print axioms SOnlyMachineClock.normalized_other
#check SOnlyMachineClock.row_positive
#print axioms SOnlyMachineClock.row_positive
#check SOnlyMachineClock.increment_row
#print axioms SOnlyMachineClock.increment_row
#check SOnlyMachineClock.branch
#print axioms SOnlyMachineClock.branch
#check SOnlyMachineClock.decrement_row
#print axioms SOnlyMachineClock.decrement_row
#check SOnlyMachineClock.branch_zero
#print axioms SOnlyMachineClock.branch_zero
#check SOnlyMachineClock.branch_zero_other
#print axioms SOnlyMachineClock.branch_zero_other
#check SOnlyMachineClock.failure_row
#print axioms SOnlyMachineClock.failure_row
#check SOnlyMachineClock.recovery
#print axioms SOnlyMachineClock.recovery
#check SOnlyMachineClock.recovery_zero
#print axioms SOnlyMachineClock.recovery_zero
#check SOnlyMachineClock.recovery_other
#print axioms SOnlyMachineClock.recovery_other
#check SOnlyMachineClock.recovery_delay
#print axioms SOnlyMachineClock.recovery_delay
#check SOnlyMachineClock.success_row
#print axioms SOnlyMachineClock.success_row
#check SOnlyMachineClock.clockList
#print axioms SOnlyMachineClock.clockList
#check SOnlyMachineClock.mem_clockList
#print axioms SOnlyMachineClock.mem_clockList
#check SOnlyMachineClock.clockList_nodup
#print axioms SOnlyMachineClock.clockList_nodup
#check SOnlyMachineClock.clocks
#print axioms SOnlyMachineClock.clocks
#check SOnlyMachineClock.BPCell
#print axioms SOnlyMachineClock.BPCell
#check SOnlyMachineClock.program
#print axioms SOnlyMachineClock.program
#check SOnlyMachineClock.raw
#print axioms SOnlyMachineClock.raw
#check SOnlyMachineClock.encode
#print axioms SOnlyMachineClock.encode
#check SOnlyMachineClock.normalize
#print axioms SOnlyMachineClock.normalize
#check SOnlyMachineClock.finish_macro
#print axioms SOnlyMachineClock.finish_macro
#check SOnlyMachineClock.step_simulation
#print axioms SOnlyMachineClock.step_simulation
#check SOnlyMachineClock.initial_simulation
#print axioms SOnlyMachineClock.initial_simulation
#check SOnlyMachineClock.run_simulation
#print axioms SOnlyMachineClock.run_simulation
#check SOnlyMachineClock.initialized_run
#print axioms SOnlyMachineClock.initialized_run
#check SOnlyMachineClock.encode_halted_iff
#print axioms SOnlyMachineClock.encode_halted_iff
#check SOnlyMachineClock.halt_boundary
#print axioms SOnlyMachineClock.halt_boundary
#check SOnlyMachineClock.halt_iff
#print axioms SOnlyMachineClock.halt_iff
#check SOnlyMachineClock.halt_output
#print axioms SOnlyMachineClock.halt_output
#check SOnlyMachineFinite.number
#print axioms SOnlyMachineFinite.number
#check SOnlyMachineFinite.unnumber
#print axioms SOnlyMachineFinite.unnumber
#check SOnlyMachineFinite.unnumber_number
#print axioms SOnlyMachineFinite.unnumber_number
#check SOnlyMachineFinite.number_unnumber
#print axioms SOnlyMachineFinite.number_unnumber
#check SOnlyMachineFinite.renameCommand
#print axioms SOnlyMachineFinite.renameCommand
#check SOnlyMachineFinite.renameProgram
#print axioms SOnlyMachineFinite.renameProgram
#check SOnlyMachineFinite.encode
#print axioms SOnlyMachineFinite.encode
#check SOnlyMachineFinite.put_number
#print axioms SOnlyMachineFinite.put_number
#check SOnlyMachineFinite.execute_number
#print axioms SOnlyMachineFinite.execute_number
#check SOnlyMachineFinite.advance_number
#print axioms SOnlyMachineFinite.advance_number
#check SOnlyMachineFinite.run_number
#print axioms SOnlyMachineFinite.run_number
#check SOnlyMachineFinite.halted_number
#print axioms SOnlyMachineFinite.halted_number
#check SOnlyMachineFinite.Dense
#print axioms SOnlyMachineFinite.Dense
#check SOnlyMachineFinite.dense_number
#print axioms SOnlyMachineFinite.dense_number
#check SOnlyMachineFinite.auxList
#print axioms SOnlyMachineFinite.auxList
#check SOnlyMachineFinite.mem_auxList
#print axioms SOnlyMachineFinite.mem_auxList
#check SOnlyMachineFinite.auxList_nodup
#print axioms SOnlyMachineFinite.auxList_nodup
#check SOnlyMachineFinite.machineCells
#print axioms SOnlyMachineFinite.machineCells
#check SOnlyMachineFinite.typedProgram
#print axioms SOnlyMachineFinite.typedProgram
#check SOnlyMachineFinite.targetCells
#print axioms SOnlyMachineFinite.targetCells
#check SOnlyMachineFinite.compile
#print axioms SOnlyMachineFinite.compile
#check SOnlyMachineFinite.halt_iff
#print axioms SOnlyMachineFinite.halt_iff
#check SOnlyMachineFinite.waterfall_dense
#print axioms SOnlyMachineFinite.waterfall_dense
#check SOnlyMachineFinite.compile_dense
#print axioms SOnlyMachineFinite.compile_dense
#check SOnlyMachineFinite.compile_nonempty
#print axioms SOnlyMachineFinite.compile_nonempty
#check SOnlyMachineFinite.outputCell
#print axioms SOnlyMachineFinite.outputCell
#check SOnlyMachineFinite.output_number_zero
#print axioms SOnlyMachineFinite.output_number_zero
#check SOnlyMachineFinite.counter_count_pos
#print axioms SOnlyMachineFinite.counter_count_pos
#check SOnlyMachineFinite.firstCounter
#print axioms SOnlyMachineFinite.firstCounter
#check SOnlyMachineFinite.first_is_output
#print axioms SOnlyMachineFinite.first_is_output
#check SOnlyMachineFinite.halt_output
#print axioms SOnlyMachineFinite.halt_output
#check SOnlyMachineFinite.readout_correct
#print axioms SOnlyMachineFinite.readout_correct
#check SOnlyMachineNat.liftProgram
#print axioms SOnlyMachineNat.liftProgram
#check SOnlyMachineNat.project
#print axioms SOnlyMachineNat.project
#check SOnlyMachineNat.project_put
#print axioms SOnlyMachineNat.project_put
#check SOnlyMachineNat.execute_project
#print axioms SOnlyMachineNat.execute_project
#check SOnlyMachineNat.advance_project
#print axioms SOnlyMachineNat.advance_project
#check SOnlyMachineNat.run_project
#print axioms SOnlyMachineNat.run_project
#check SOnlyMachineNat.halted_project
#print axioms SOnlyMachineNat.halted_project
#check SOnlyMachineNat.bounded
#print axioms SOnlyMachineNat.bounded
#check SOnlyMachineNat.counterCount
#print axioms SOnlyMachineNat.counterCount
#check SOnlyMachineNat.compile
#print axioms SOnlyMachineNat.compile
#check SOnlyMachineNat.compile_bounded
#print axioms SOnlyMachineNat.compile_bounded
#check SOnlyMachineNat.counterCount_pos
#print axioms SOnlyMachineNat.counterCount_pos
#check SOnlyMachineNat.compile_nonempty
#print axioms SOnlyMachineNat.compile_nonempty
#check SOnlyMachineNat.compile_dense
#print axioms SOnlyMachineNat.compile_dense
#check SOnlyMachineNat.initialState
#print axioms SOnlyMachineNat.initialState
#check SOnlyMachineNat.halt_iff
#print axioms SOnlyMachineNat.halt_iff
#check SOnlyMachineNat.halt_output
#print axioms SOnlyMachineNat.halt_output
#check SOnlyMachineNat.readout_correct
#print axioms SOnlyMachineNat.readout_correct
#check SOnlyMachineBounds.sum_le
#print axioms SOnlyMachineBounds.sum_le
#check SOnlyMachineBounds.member_le_sum
#print axioms SOnlyMachineBounds.member_le_sum
#check SOnlyMachineBounds.flatMap_length_le
#print axioms SOnlyMachineBounds.flatMap_length_le
#check SOnlyMachineBounds.unary_length_le
#print axioms SOnlyMachineBounds.unary_length_le
#check SOnlyMachineBounds.guarded_length
#print axioms SOnlyMachineBounds.guarded_length
#check SOnlyMachineBounds.guarded_length_le
#print axioms SOnlyMachineBounds.guarded_length_le
#check SOnlyMachineBounds.auxList_length
#print axioms SOnlyMachineBounds.auxList_length
#check SOnlyMachineBounds.helperCount
#print axioms SOnlyMachineBounds.helperCount
#check SOnlyMachineBounds.machineCells_length
#print axioms SOnlyMachineBounds.machineCells_length
#check SOnlyMachineBounds.clockList_length
#print axioms SOnlyMachineBounds.clockList_length
#check SOnlyMachineBounds.clocks_length
#print axioms SOnlyMachineBounds.clocks_length
#check SOnlyMachineBounds.cells_length
#print axioms SOnlyMachineBounds.cells_length
#check SOnlyMachineBounds.counterCount_exact
#print axioms SOnlyMachineBounds.counterCount_exact
#check SOnlyMachineBounds.row_le_nine
#print axioms SOnlyMachineBounds.row_le_nine
#check SOnlyMachineBounds.waterfall_length_bound
#print axioms SOnlyMachineBounds.waterfall_length_bound
#check SOnlyMachineBounds.inputSum
#print axioms SOnlyMachineBounds.inputSum
#check SOnlyMachineBounds.input_le_sum
#print axioms SOnlyMachineBounds.input_le_sum
#check SOnlyMachineBounds.polynomialBound
#print axioms SOnlyMachineBounds.polynomialBound
#check SOnlyMachineBounds.compile_length_bound
#print axioms SOnlyMachineBounds.compile_length_bound
#check SOnlyMachineCorrectness.sourceRun_add
#print axioms SOnlyMachineCorrectness.sourceRun_add
#check SOnlyMachineCorrectness.source_halt_stable
#print axioms SOnlyMachineCorrectness.source_halt_stable
#check SOnlyMachineCorrectness.source_halted_unique
#print axioms SOnlyMachineCorrectness.source_halted_unique
#check SOnlyMachineCorrectness.output_iff
#print axioms SOnlyMachineCorrectness.output_iff
#check SOnlyMachineCorrectness.every_halt_reads_result
#print axioms SOnlyMachineCorrectness.every_halt_reads_result
#check SOnlyMemory.Cell
#print axioms SOnlyMemory.Cell
#check SOnlyMemory.cellWord
#print axioms SOnlyMemory.cellWord
#check SOnlyMemory.inverter
#print axioms SOnlyMemory.inverter
#check SOnlyMemory.component
#print axioms SOnlyMemory.component
#check SOnlyMemory.memory
#print axioms SOnlyMemory.memory
#check SOnlyMemory.nextAlignment
#print axioms SOnlyMemory.nextAlignment
#check SOnlyMemory.updatedDynamic
#print axioms SOnlyMemory.updatedDynamic
#check SOnlyMemory.normalUpdate
#print axioms SOnlyMemory.normalUpdate
#check SOnlyMemory.reset
#print axioms SOnlyMemory.reset
#check SOnlyMemory.markerComponent
#print axioms SOnlyMemory.markerComponent
#check SOnlyMemory.markerWord
#print axioms SOnlyMemory.markerWord
#check SOnlyMemory.memory_nil
#print axioms SOnlyMemory.memory_nil
#check SOnlyMemory.memory_cons
#print axioms SOnlyMemory.memory_cons
#check SOnlyMemory.component_phase
#print axioms SOnlyMemory.component_phase
#check SOnlyMemory.command_phase_stable
#print axioms SOnlyMemory.command_phase_stable
#check SOnlyMemory.parity_phase_stable
#print axioms SOnlyMemory.parity_phase_stable
#check SOnlyMemory.component_normal
#print axioms SOnlyMemory.component_normal
#check SOnlyMemory.component_reset
#print axioms SOnlyMemory.component_reset
#check SOnlyMemory.component_marker
#print axioms SOnlyMemory.component_marker
#check SOnlyMemory.halfcommand_component
#print axioms SOnlyMemory.halfcommand_component
#check SOnlyMemory.memory_normal
#print axioms SOnlyMemory.memory_normal
#check SOnlyMemory.memory_reset
#print axioms SOnlyMemory.memory_reset
#check SOnlyMemory.memory_marker
#print axioms SOnlyMemory.memory_marker
#check SOnlyMemory.marker_event
#print axioms SOnlyMemory.marker_event
#check SOnlyMemory.normal_fixed
#print axioms SOnlyMemory.normal_fixed
#check SOnlyMemory.combined
#print axioms SOnlyMemory.combined
#check SOnlyMemory.runningXor
#print axioms SOnlyMemory.runningXor
#check SOnlyMemory.memory_running_xor
#print axioms SOnlyMemory.memory_running_xor
#check SOnlyMemory.memory_reset_vector
#print axioms SOnlyMemory.memory_reset_vector
#check SOnlyMemory.widthParity
#print axioms SOnlyMemory.widthParity
#check SOnlyMemory.component_width
#print axioms SOnlyMemory.component_width
#check SOnlyMemory.memory_width
#print axioms SOnlyMemory.memory_width
#check SOnlyMemory.safePass
#print axioms SOnlyMemory.safePass
#check SOnlyMemory.safePass_cons
#print axioms SOnlyMemory.safePass_cons
#check SOnlyMemory.safePass_append
#print axioms SOnlyMemory.safePass_append
#check SOnlyMemory.safe_prefix_no_event
#print axioms SOnlyMemory.safe_prefix_no_event
#check SOnlyMemory.component_command_safe
#print axioms SOnlyMemory.component_command_safe
#check SOnlyMemory.component_parity_safe
#print axioms SOnlyMemory.component_parity_safe
#check SOnlyMemory.component_reset_safe
#print axioms SOnlyMemory.component_reset_safe
#check SOnlyMemory.memory_command_safe
#print axioms SOnlyMemory.memory_command_safe
#check SOnlyMemory.memory_parity_safe
#print axioms SOnlyMemory.memory_parity_safe
#check SOnlyMemory.memory_reset_safe
#print axioms SOnlyMemory.memory_reset_safe
#check SOnlyMemory.componentCount
#print axioms SOnlyMemory.componentCount
#check SOnlyMemory.command_component_length
#print axioms SOnlyMemory.command_component_length
#check SOnlyMemory.parity_component_length
#print axioms SOnlyMemory.parity_component_length
#check SOnlyMemory.memory_command_length
#print axioms SOnlyMemory.memory_command_length
#check SOnlyMemory.memory_parity_length
#print axioms SOnlyMemory.memory_parity_length
#check SOnlyMemory.componentCount_positive
#print axioms SOnlyMemory.componentCount_positive
#check SOnlyMemory.intermediate_words_nonempty
#print axioms SOnlyMemory.intermediate_words_nonempty
#check SOnlyTemporalMemory.weave
#print axioms SOnlyTemporalMemory.weave
#check SOnlyTemporalMemory.weave_length
#print axioms SOnlyTemporalMemory.weave_length
#check SOnlyTemporalMemory.runningXor_length
#print axioms SOnlyTemporalMemory.runningXor_length
#check SOnlyTemporalMemory.double_prefix_weave
#print axioms SOnlyTemporalMemory.double_prefix_weave
#check SOnlyTemporalMemory.run
#print axioms SOnlyTemporalMemory.run
#check SOnlyTemporalMemory.run_length
#print axioms SOnlyTemporalMemory.run_length
#check SOnlyTemporalMemory.run_add
#print axioms SOnlyTemporalMemory.run_add
#check SOnlyTemporalMemory.run_even_weave
#print axioms SOnlyTemporalMemory.run_even_weave
#check SOnlyTemporalMemory.observe
#print axioms SOnlyTemporalMemory.observe
#check SOnlyTemporalMemory.observe_weave
#print axioms SOnlyTemporalMemory.observe_weave
#check SOnlyTemporalMemory.observe_prefix_weave
#print axioms SOnlyTemporalMemory.observe_prefix_weave
#check SOnlyTemporalMemory.observe_even
#print axioms SOnlyTemporalMemory.observe_even
#check SOnlyTemporalMemory.observe_odd
#print axioms SOnlyTemporalMemory.observe_odd
#check SOnlyTemporalMemory.Vector
#print axioms SOnlyTemporalMemory.Vector
#check SOnlyTemporalMemory.toList
#print axioms SOnlyTemporalMemory.toList
#check SOnlyTemporalMemory.vxor
#print axioms SOnlyTemporalMemory.vxor
#check SOnlyTemporalMemory.transform
#print axioms SOnlyTemporalMemory.transform
#check SOnlyTemporalMemory.lookup
#print axioms SOnlyTemporalMemory.lookup
#check SOnlyTemporalMemory.tabulate
#print axioms SOnlyTemporalMemory.tabulate
#check SOnlyTemporalMemory.toList_length
#print axioms SOnlyTemporalMemory.toList_length
#check SOnlyTemporalMemory.vxor_shuffle
#print axioms SOnlyTemporalMemory.vxor_shuffle
#check SOnlyTemporalMemory.vxor_cancel
#print axioms SOnlyTemporalMemory.vxor_cancel
#check SOnlyTemporalMemory.lookup_xor
#print axioms SOnlyTemporalMemory.lookup_xor
#check SOnlyTemporalMemory.transform_xor
#print axioms SOnlyTemporalMemory.transform_xor
#check SOnlyTemporalMemory.transform_involution
#print axioms SOnlyTemporalMemory.transform_involution
#check SOnlyTemporalMemory.lookup_tabulate
#print axioms SOnlyTemporalMemory.lookup_tabulate
#check SOnlyTemporalMemory.run_single
#print axioms SOnlyTemporalMemory.run_single
#check SOnlyTemporalMemory.observation_transform
#print axioms SOnlyTemporalMemory.observation_transform
#check SOnlyTemporalMemory.initialized_observation
#print axioms SOnlyTemporalMemory.initialized_observation
#check SOnlyTemporalMemory.initializer
#print axioms SOnlyTemporalMemory.initializer
#check SOnlyTemporalMemory.initializer_length
#print axioms SOnlyTemporalMemory.initializer_length
#check SOnlyTemporalMemory.initializer_correct
#print axioms SOnlyTemporalMemory.initializer_correct
#check SOnlyTemporalMemory.weave_replicate
#print axioms SOnlyTemporalMemory.weave_replicate
#check SOnlyTemporalMemory.doubled_replicate
#print axioms SOnlyTemporalMemory.doubled_replicate
#check SOnlyTemporalMemory.impulse
#print axioms SOnlyTemporalMemory.impulse
#check SOnlyTemporalMemory.impulse_even
#print axioms SOnlyTemporalMemory.impulse_even
#check SOnlyTemporalMemory.impulse_odd
#print axioms SOnlyTemporalMemory.impulse_odd
#check SOnlyTemporalMemory.impulse_before
#print axioms SOnlyTemporalMemory.impulse_before
#check SOnlyTemporalMemory.impulse_boundary
#print axioms SOnlyTemporalMemory.impulse_boundary
#check SOnlyTemporalMemory.xorList
#print axioms SOnlyTemporalMemory.xorList
#check SOnlyTemporalMemory.prefix_xor
#print axioms SOnlyTemporalMemory.prefix_xor
#check SOnlyTemporalMemory.run_xor
#print axioms SOnlyTemporalMemory.run_xor
#check SOnlyTemporalMemory.observe_xor
#print axioms SOnlyTemporalMemory.observe_xor
#check SOnlyTemporalMemory.xorList_zeros
#print axioms SOnlyTemporalMemory.xorList_zeros
#check SOnlyTemporalMemory.prefix_zeros
#print axioms SOnlyTemporalMemory.prefix_zeros
#check SOnlyTemporalMemory.prefix_forcing
#print axioms SOnlyTemporalMemory.prefix_forcing
#check SOnlyTemporalMemory.run_zeros
#print axioms SOnlyTemporalMemory.run_zeros
#check SOnlyTemporalMemory.observe_zeros
#print axioms SOnlyTemporalMemory.observe_zeros
#check SOnlyTemporalMemory.observe_constant_forcing
#print axioms SOnlyTemporalMemory.observe_constant_forcing
#check SOnlyTemporalMemory.one_forcing_effect
#print axioms SOnlyTemporalMemory.one_forcing_effect
#check SOnlyTemporalMemory.forcedRun
#print axioms SOnlyTemporalMemory.forcedRun
#check SOnlyTemporalMemory.forcedRun_length
#print axioms SOnlyTemporalMemory.forcedRun_length
#check SOnlyTemporalMemory.response
#print axioms SOnlyTemporalMemory.response
#check SOnlyTemporalMemory.forcing_response
#print axioms SOnlyTemporalMemory.forcing_response
#check SOnlyTemporalMemory.response_before
#print axioms SOnlyTemporalMemory.response_before
#check SOnlyTemporalMemory.forcing_invisible
#print axioms SOnlyTemporalMemory.forcing_invisible
#check SOnlyTemporalMemory.forced_initializer_correct
#print axioms SOnlyTemporalMemory.forced_initializer_correct
#check SOnlyTemporalMemory.unitPulse
#print axioms SOnlyTemporalMemory.unitPulse
#check SOnlyTemporalMemory.unitPulse_run
#print axioms SOnlyTemporalMemory.unitPulse_run
#check SOnlyTemporalMemory.first_disturbed_output
#print axioms SOnlyTemporalMemory.first_disturbed_output
#check SOnlyTemporalMemory.stage
#print axioms SOnlyTemporalMemory.stage
#check SOnlyTemporalMemory.stages
#print axioms SOnlyTemporalMemory.stages
#check SOnlyTemporalMemory.stages_branch
#print axioms SOnlyTemporalMemory.stages_branch
#check SOnlyTemporalMemory.increasing_strides_eq_transform
#print axioms SOnlyTemporalMemory.increasing_strides_eq_transform
#check SOnlyTemporalMemory.lookup_stage
#print axioms SOnlyTemporalMemory.lookup_stage
#check SOnlyTemporalMemory.initialCells
#print axioms SOnlyTemporalMemory.initialCells
#check SOnlyTemporalMemory.initialCells_combined
#print axioms SOnlyTemporalMemory.initialCells_combined
#check SOnlyTemporalMemory.memoryRun
#print axioms SOnlyTemporalMemory.memoryRun
#check SOnlyTemporalMemory.memoryRun_combined
#print axioms SOnlyTemporalMemory.memoryRun_combined
#check SOnlyTemporalMemory.source_programmed_width
#print axioms SOnlyTemporalMemory.source_programmed_width
#check SOnlyTemporalMemory.initial_memory_length
#print axioms SOnlyTemporalMemory.initial_memory_length
#check SOnlyTemporalMemory.initializer_memory_bounds
#print axioms SOnlyTemporalMemory.initializer_memory_bounds
#check SOnlyTemporalMemory.weave_get_even
#print axioms SOnlyTemporalMemory.weave_get_even
#check SOnlyTemporalMemory.weave_get_odd
#print axioms SOnlyTemporalMemory.weave_get_odd
#check SOnlyTemporalMemory.toList_lookup
#print axioms SOnlyTemporalMemory.toList_lookup
#check SOnlyTemporalMemory.initializer_eq_increasing_strides
#print axioms SOnlyTemporalMemory.initializer_eq_increasing_strides
#check SOnlySimulation.phaseAfter_add
#print axioms SOnlySimulation.phaseAfter_add
#check SOnlySimulation.phaseAfter_even
#print axioms SOnlySimulation.phaseAfter_even
#check SOnlySimulation.phaseAfter_odd
#print axioms SOnlySimulation.phaseAfter_odd
#check SOnlySimulation.phaseAfter_of_even
#print axioms SOnlySimulation.phaseAfter_of_even
#check SOnlySimulation.phaseAfter_mod
#print axioms SOnlySimulation.phaseAfter_mod
#check SOnlySimulation.memory_next_phase
#print axioms SOnlySimulation.memory_next_phase
#check SOnlySimulation.memory_command_phase
#print axioms SOnlySimulation.memory_command_phase
#check SOnlySimulation.memory_parity_phase
#print axioms SOnlySimulation.memory_parity_phase
#check SOnlySimulation.ordinary_phase
#print axioms SOnlySimulation.ordinary_phase
#check SOnlySimulation.protected_phase
#print axioms SOnlySimulation.protected_phase
#check SOnlySimulation.prefix_nonempty
#print axioms SOnlySimulation.prefix_nonempty
#check SOnlySimulation.SafeRun
#print axioms SOnlySimulation.SafeRun
#check SOnlySimulation.SafeRun.trans
#print axioms SOnlySimulation.SafeRun.trans
#check SOnlySimulation.safe_pass_run
#print axioms SOnlySimulation.safe_pass_run
#check SOnlySimulation.counter_safe
#print axioms SOnlySimulation.counter_safe
#check SOnlySimulation.Piece
#print axioms SOnlySimulation.Piece
#check SOnlySimulation.Piece.word
#print axioms SOnlySimulation.Piece.word
#check SOnlySimulation.assemble
#print axioms SOnlySimulation.assemble
#check SOnlySimulation.alignments
#print axioms SOnlySimulation.alignments
#check SOnlySimulation.passPieces
#print axioms SOnlySimulation.passPieces
#check SOnlySimulation.pass_assemble
#print axioms SOnlySimulation.pass_assemble
#check SOnlySimulation.assembled_command_safe
#print axioms SOnlySimulation.assembled_command_safe
#check SOnlySimulation.assembled_parity_safe
#print axioms SOnlySimulation.assembled_parity_safe
#check SOnlySimulation.assembled_reset_even
#print axioms SOnlySimulation.assembled_reset_even
#check SOnlySimulation.assembled_odd_reset_safe
#print axioms SOnlySimulation.assembled_odd_reset_safe
#check SOnlySimulation.NormalAction
#print axioms SOnlySimulation.NormalAction
#check SOnlySimulation.NormalAction.take
#print axioms SOnlySimulation.NormalAction.take
#check SOnlySimulation.NormalAction.input
#print axioms SOnlySimulation.NormalAction.input
#check SOnlySimulation.NormalAction.output
#print axioms SOnlySimulation.NormalAction.output
#check SOnlySimulation.NormalAction.input_even
#print axioms SOnlySimulation.NormalAction.input_even
#check SOnlySimulation.NormalAction.command_even
#print axioms SOnlySimulation.NormalAction.command_even
#check SOnlySimulation.NormalAction.parity_even
#print axioms SOnlySimulation.NormalAction.parity_even
#check SOnlySimulation.NormalAction.update
#print axioms SOnlySimulation.NormalAction.update
#check SOnlySimulation.NormalRow
#print axioms SOnlySimulation.NormalRow
#check SOnlySimulation.rowsPieces
#print axioms SOnlySimulation.rowsPieces
#check SOnlySimulation.rowsWord
#print axioms SOnlySimulation.rowsWord
#check SOnlySimulation.rowsWord_nil
#print axioms SOnlySimulation.rowsWord_nil
#check SOnlySimulation.rowsWord_cons
#print axioms SOnlySimulation.rowsWord_cons
#check SOnlySimulation.Fits
#print axioms SOnlySimulation.Fits
#check SOnlySimulation.fits_counter_phase
#print axioms SOnlySimulation.fits_counter_phase
#check SOnlySimulation.fits_global_phase
#print axioms SOnlySimulation.fits_global_phase
#check SOnlySimulation.normal_command_phase
#print axioms SOnlySimulation.normal_command_phase
#check SOnlySimulation.normalOutput
#print axioms SOnlySimulation.normalOutput
#check SOnlySimulation.normal_halfcommand
#print axioms SOnlySimulation.normal_halfcommand
#check SOnlySimulation.normal_reset_safe
#print axioms SOnlySimulation.normal_reset_safe
#check SOnlySimulation.memory_prefix_nonempty
#print axioms SOnlySimulation.memory_prefix_nonempty
#check SOnlySimulation.normal_run
#print axioms SOnlySimulation.normal_run
#check SOnlySimulation.IncrementRow
#print axioms SOnlySimulation.IncrementRow
#check SOnlySimulation.incrementPrefix
#print axioms SOnlySimulation.incrementPrefix
#check SOnlySimulation.incrementPieces
#print axioms SOnlySimulation.incrementPieces
#check SOnlySimulation.incrementPrefix_assemble
#print axioms SOnlySimulation.incrementPrefix_assemble
#check SOnlySimulation.incrementEnd
#print axioms SOnlySimulation.incrementEnd
#check SOnlySimulation.IncrementFits
#print axioms SOnlySimulation.IncrementFits
#check SOnlySimulation.incrementPrefix_phase
#print axioms SOnlySimulation.incrementPrefix_phase
#check SOnlySimulation.incrementPrefix_command_phase
#print axioms SOnlySimulation.incrementPrefix_command_phase
#check SOnlySimulation.incrementPrefix_reset
#print axioms SOnlySimulation.incrementPrefix_reset
#check SOnlySimulation.incrementResultPrefix
#print axioms SOnlySimulation.incrementResultPrefix
#check SOnlySimulation.incrementPrefix_marker
#print axioms SOnlySimulation.incrementPrefix_marker
#check SOnlySimulation.exceptionalWord
#print axioms SOnlySimulation.exceptionalWord
#check SOnlySimulation.exceptionalPieces
#print axioms SOnlySimulation.exceptionalPieces
#check SOnlySimulation.exceptional_assemble
#print axioms SOnlySimulation.exceptional_assemble
#check SOnlySimulation.ExceptionalFits
#print axioms SOnlySimulation.ExceptionalFits
#check SOnlySimulation.exceptional_command_phase
#print axioms SOnlySimulation.exceptional_command_phase
#check SOnlySimulation.exceptional_parity_phase
#print axioms SOnlySimulation.exceptional_parity_phase
#check SOnlySimulation.exceptional_reset
#print axioms SOnlySimulation.exceptional_reset
#check SOnlySimulation.exceptional_nonempty
#print axioms SOnlySimulation.exceptional_nonempty
#check SOnlySimulation.exceptional_reset_run
#print axioms SOnlySimulation.exceptional_reset_run
#check SOnlySimulation.haltOutput
#print axioms SOnlySimulation.haltOutput
#check SOnlySimulation.halt_output_exact
#print axioms SOnlySimulation.halt_output_exact
#check SOnlySimulation.markerWord_head
#print axioms SOnlySimulation.markerWord_head
#check SOnlySimulation.halt_output_selected
#print axioms SOnlySimulation.halt_output_selected
#check SOnlySimulation.halt_run
#print axioms SOnlySimulation.halt_run
#check SOnlySimulation.result_counter_word
#print axioms SOnlySimulation.result_counter_word
#check SOnlySimulation.finalResult
#print axioms SOnlySimulation.finalResult
#check SOnlySimulation.halt_output_grammar
#print axioms SOnlySimulation.halt_output_grammar
#check SOnlySimulation.marker_no_result_symbol
#print axioms SOnlySimulation.marker_no_result_symbol
#check SOnlySimulation.component_parity_no_result
#print axioms SOnlySimulation.component_parity_no_result
#check SOnlySimulation.memory_parity_no_result
#print axioms SOnlySimulation.memory_parity_no_result
#check SOnlySimulation.result_separator_properties
#print axioms SOnlySimulation.result_separator_properties
#check SOnlySimulation.indexedWord
#print axioms SOnlySimulation.indexedWord
#check SOnlySimulation.indexedRows
#print axioms SOnlySimulation.indexedRows
#check SOnlySimulation.indexed_input
#print axioms SOnlySimulation.indexed_input
#check SOnlySimulation.indexed_output
#print axioms SOnlySimulation.indexed_output
#check SOnlySimulation.indexed_fits
#print axioms SOnlySimulation.indexed_fits
#check SOnlySimulation.indexed_normal_run
#print axioms SOnlySimulation.indexed_normal_run
#check SOnlySimulation.epochMemory
#print axioms SOnlySimulation.epochMemory
#check SOnlySimulation.epoch_width
#print axioms SOnlySimulation.epoch_width
#check SOnlySimulation.epoch_next
#print axioms SOnlySimulation.epoch_next
#check SOnlySimulation.normalUpdate_length
#print axioms SOnlySimulation.normalUpdate_length
#check SOnlySimulation.memoryRun_length
#print axioms SOnlySimulation.memoryRun_length
#check SOnlySimulation.epoch_length
#print axioms SOnlySimulation.epoch_length
#check SOnlySimulation.epoch_nonempty
#print axioms SOnlySimulation.epoch_nonempty
#check SOnlySimulation.memoryRun_fixed
#print axioms SOnlySimulation.memoryRun_fixed
#check SOnlySimulation.epoch_reset
#print axioms SOnlySimulation.epoch_reset
#check SOnlySimulation.epoch_normal_run
#print axioms SOnlySimulation.epoch_normal_run
#check SOnlySimulation.epoch_horizon
#print axioms SOnlySimulation.epoch_horizon
#check SOnlySimulation.BPProgram
#print axioms SOnlySimulation.BPProgram
#check SOnlySimulation.BPCommand
#print axioms SOnlySimulation.BPCommand
#check SOnlySimulation.Macro
#print axioms SOnlySimulation.Macro
#check SOnlySimulation.expandedAt
#print axioms SOnlySimulation.expandedAt
#check SOnlySimulation.macroAction
#print axioms SOnlySimulation.macroAction
#check SOnlySimulation.scheduledAction
#print axioms SOnlySimulation.scheduledAction
#check SOnlySimulation.scheduledParity
#print axioms SOnlySimulation.scheduledParity
#check SOnlySimulation.scheduledEntry
#print axioms SOnlySimulation.scheduledEntry
#check SOnlySimulation.scheduledExit
#print axioms SOnlySimulation.scheduledExit
#check SOnlySimulation.scheduledWidth
#print axioms SOnlySimulation.scheduledWidth
#check SOnlySimulation.programMemory
#print axioms SOnlySimulation.programMemory
#check SOnlySimulation.programWord
#print axioms SOnlySimulation.programWord
#check SOnlySimulation.scheduledEntry_next
#print axioms SOnlySimulation.scheduledEntry_next
#check SOnlySimulation.scheduledEntry_first
#print axioms SOnlySimulation.scheduledEntry_first
#check SOnlySimulation.scheduled_normal_run
#print axioms SOnlySimulation.scheduled_normal_run
#check SOnlySimulation.expandedAt_zero
#print axioms SOnlySimulation.expandedAt_zero
#check SOnlySimulation.expandedAt_source
#print axioms SOnlySimulation.expandedAt_source
#check SOnlySimulation.expandedAt_halt
#print axioms SOnlySimulation.expandedAt_halt
#check SOnlySimulation.scheduledAction_zero
#print axioms SOnlySimulation.scheduledAction_zero
#check SOnlySimulation.scheduledAction_one
#print axioms SOnlySimulation.scheduledAction_one
#check SOnlySimulation.scheduledAction_source_first
#print axioms SOnlySimulation.scheduledAction_source_first
#check SOnlySimulation.scheduledAction_source_second
#print axioms SOnlySimulation.scheduledAction_source_second
#check SOnlySimulation.scheduledAction_halt_first
#print axioms SOnlySimulation.scheduledAction_halt_first
#check SOnlySimulation.scheduledAction_halt_second
#print axioms SOnlySimulation.scheduledAction_halt_second
#check SOnlySimulation.scheduledParity_normal
#print axioms SOnlySimulation.scheduledParity_normal
#check SOnlySimulation.scheduledParity_halt
#print axioms SOnlySimulation.scheduledParity_halt
#check SOnlySimulation.seed
#print axioms SOnlySimulation.seed
#check SOnlySimulation.seed_prefix_run
#print axioms SOnlySimulation.seed_prefix_run
#check SOnlySimulation.valueWords
#print axioms SOnlySimulation.valueWords
#check SOnlySimulation.boundary
#print axioms SOnlySimulation.boundary
#check SOnlySimulation.dummy_run
#print axioms SOnlySimulation.dummy_run
#check SOnlySimulation.protectedWords
#print axioms SOnlySimulation.protectedWords
#check SOnlySimulation.protected_dummy_run
#print axioms SOnlySimulation.protected_dummy_run
#check SOnlySimulation.source_increment_run
#print axioms SOnlySimulation.source_increment_run
#check SOnlySimulation.source_positive_decrement_run
#print axioms SOnlySimulation.source_positive_decrement_run
#check SOnlySimulation.indexedIncrementRows
#print axioms SOnlySimulation.indexedIncrementRows
#check SOnlySimulation.indexedPrefix
#print axioms SOnlySimulation.indexedPrefix
#check SOnlySimulation.indexedWord_prefix
#print axioms SOnlySimulation.indexedWord_prefix
#check SOnlySimulation.indexedWord_split
#print axioms SOnlySimulation.indexedWord_split
#check SOnlySimulation.indexedPrefix_increments
#print axioms SOnlySimulation.indexedPrefix_increments
#check SOnlySimulation.indexed_exceptional_word
#print axioms SOnlySimulation.indexed_exceptional_word
#check SOnlySimulation.indexedIncrement_map
#print axioms SOnlySimulation.indexedIncrement_map
#check SOnlySimulation.indexedIncrement_nonempty
#print axioms SOnlySimulation.indexedIncrement_nonempty
#check SOnlySimulation.indexedIncrement_fits
#print axioms SOnlySimulation.indexedIncrement_fits
#check SOnlySimulation.scheduled_exceptional_fits
#print axioms SOnlySimulation.scheduled_exceptional_fits
#check SOnlySimulation.scheduled_zero_reset_run
#print axioms SOnlySimulation.scheduled_zero_reset_run
#check SOnlySimulation.source_zero_decrement_run
#print axioms SOnlySimulation.source_zero_decrement_run
#check SOnlySimulation.finalEvent
#print axioms SOnlySimulation.finalEvent
#check SOnlySimulation.source_halt_run
#print axioms SOnlySimulation.source_halt_run
#check SOnlySimulation.WellFormed
#print axioms SOnlySimulation.WellFormed
#check SOnlySimulation.initialState
#print axioms SOnlySimulation.initialState
#check SOnlySimulation.sourceConfig
#print axioms SOnlySimulation.sourceConfig
#check SOnlySimulation.source_step_run
#print axioms SOnlySimulation.source_step_run
#check SOnlySimulation.source_invariants
#print axioms SOnlySimulation.source_invariants
#check SOnlySimulation.source_run_succ
#print axioms SOnlySimulation.source_run_succ
#check SOnlySimulation.source_run_invariants
#print axioms SOnlySimulation.source_run_invariants
#check SOnlySimulation.startup_run
#print axioms SOnlySimulation.startup_run
#check SOnlySimulation.source_prefix_run
#print axioms SOnlySimulation.source_prefix_run
#check SOnlySimulation.source_termination_first_event
#print axioms SOnlySimulation.source_termination_first_event
#check SOnlySimulation.nonhalting_prefix_progress
#print axioms SOnlySimulation.nonhalting_prefix_progress
#check SOnlySimulation.source_nontermination_safe
#print axioms SOnlySimulation.source_nontermination_safe
#check SOnlySimulation.source_halting_iff_event
#print axioms SOnlySimulation.source_halting_iff_event
#check SOnlySimulation.runLengthsAux
#print axioms SOnlySimulation.runLengthsAux
#check SOnlySimulation.runLengths
#print axioms SOnlySimulation.runLengths
#check SOnlySimulation.runLengths_skip
#print axioms SOnlySimulation.runLengths_skip
#check SOnlySimulation.runLengths_separator
#print axioms SOnlySimulation.runLengths_separator
#check SOnlySimulation.runLengths_copies
#print axioms SOnlySimulation.runLengths_copies
#check SOnlySimulation.finalResult_readout
#print axioms SOnlySimulation.finalResult_readout
#check SOnlySimulation.indexedIncrement_map_double
#print axioms SOnlySimulation.indexedIncrement_map_double
#check SOnlySimulation.encodedRunLengths
#print axioms SOnlySimulation.encodedRunLengths
#check SOnlySimulation.indexedIncrement_runLengths
#print axioms SOnlySimulation.indexedIncrement_runLengths
#check SOnlySimulation.finalEvent_readout
#print axioms SOnlySimulation.finalEvent_readout
#check SOnlySimulation.first_event_exact
#print axioms SOnlySimulation.first_event_exact
#check SOnlySimulation.compact_capacity
#print axioms SOnlySimulation.compact_capacity
#check SOnlySimulation.compact_source_halting_iff_event
#print axioms SOnlySimulation.compact_source_halting_iff_event
#check SOnlySimulation.compilerDepth
#print axioms SOnlySimulation.compilerDepth
#check SOnlySimulation.compiledSeed
#print axioms SOnlySimulation.compiledSeed
#check SOnlySimulation.compiledBits
#print axioms SOnlySimulation.compiledBits
#check SOnlySimulation.compiler_capacity
#print axioms SOnlySimulation.compiler_capacity
#check SOnlySimulation.compiler_width_bound
#print axioms SOnlySimulation.compiler_width_bound
#check SOnlySimulation.published_copies
#print axioms SOnlySimulation.published_copies
#check SOnlySimulation.published_no16
#print axioms SOnlySimulation.published_no16
#check SOnlySimulation.finalEvent_readCounter
#print axioms SOnlySimulation.finalEvent_readCounter
#check SOnlySimulation.finalEvent_readMachineValue
#print axioms SOnlySimulation.finalEvent_readMachineValue
#check SOnlySimulation.cts_nonempty_from_source
#print axioms SOnlySimulation.cts_nonempty_from_source
#check SOnlySimulation.selected_nonempty
#print axioms SOnlySimulation.selected_nonempty
#check SOnlySimulation.compiled_noPrematureEmpty
#print axioms SOnlySimulation.compiled_noPrematureEmpty
#check SOnlySimulation.compiled_halting_iff_cts_event
#print axioms SOnlySimulation.compiled_halting_iff_cts_event
#check SOnlySimulation.machineBits
#print axioms SOnlySimulation.machineBits
#check SOnlySimulation.machine_halting_iff_cts_event
#print axioms SOnlySimulation.machine_halting_iff_cts_event
#check SOnlySimulation.machine_noPrematureEmpty
#print axioms SOnlySimulation.machine_noPrematureEmpty
#check SOnlySimulation.selected_readMachineBits
#print axioms SOnlySimulation.selected_readMachineBits
#check SOnlySimulation.machine_first_cts_result
#print axioms SOnlySimulation.machine_first_cts_result
#check SOnlySimulation.machine_first_cts_reads_given_result
#print axioms SOnlySimulation.machine_first_cts_reads_given_result
#check SOnlySimulation.machine_first_cts_reads_value
#print axioms SOnlySimulation.machine_first_cts_reads_value
#check SOnlySimulation.machine_result_iff_first_cts_result
#print axioms SOnlySimulation.machine_result_iff_first_cts_result
#check SOnlySimulation.publishedWidth
#print axioms SOnlySimulation.publishedWidth
#check SOnlySimulation.publishedEntry
#print axioms SOnlySimulation.publishedEntry
#check SOnlySimulation.publishedParity
#print axioms SOnlySimulation.publishedParity
#check SOnlySimulation.Macro.Bounded
#print axioms SOnlySimulation.Macro.Bounded
#check SOnlySimulation.published_width_difference
#print axioms SOnlySimulation.published_width_difference
#check SOnlySimulation.published_entry_scheduled
#print axioms SOnlySimulation.published_entry_scheduled
#check SOnlySimulation.published_parity_scheduled
#print axioms SOnlySimulation.published_parity_scheduled
#check SOnlySimulation.expandedAt_bounded
#print axioms SOnlySimulation.expandedAt_bounded
#check SOnlySimulation.scheduledWidth_eq_published
#print axioms SOnlySimulation.scheduledWidth_eq_published
#check SOnlySimulation.publishedMemory
#print axioms SOnlySimulation.publishedMemory
#check SOnlySimulation.programMemory_zero_eq_published
#print axioms SOnlySimulation.programMemory_zero_eq_published
#check SOnlyUniversality.controller
#print axioms SOnlyUniversality.controller
#check SOnlyUniversality.selector
#print axioms SOnlyUniversality.selector
#check SOnlyUniversality.event
#print axioms SOnlyUniversality.event
#check SOnlyUniversality.decode
#print axioms SOnlyUniversality.decode
#check SOnlyUniversality.encode
#print axioms SOnlyUniversality.encode
#check SOnlyUniversality.trajectory
#print axioms SOnlyUniversality.trajectory
#check SOnlyUniversality.Halts
#print axioms SOnlyUniversality.Halts
#check SOnlyUniversality.FirstEvent
#print axioms SOnlyUniversality.FirstEvent
#check SOnlyUniversality.starts_at_encoder
#print axioms SOnlyUniversality.starts_at_encoder
#check SOnlyUniversality.root_reset
#print axioms SOnlyUniversality.root_reset
#check SOnlyUniversality.no_interinvocation_state
#print axioms SOnlyUniversality.no_interinvocation_state
#check SOnlyUniversality.all_input_linear
#print axioms SOnlyUniversality.all_input_linear
#check SOnlyUniversality.every_step_native
#print axioms SOnlyUniversality.every_step_native
#check SOnlyUniversality.halting_iff_event
#print axioms SOnlyUniversality.halting_iff_event
#check SOnlyUniversality.halting_first_result
#print axioms SOnlyUniversality.halting_first_result
#check SOnlyUniversality.first_event_correct
#print axioms SOnlyUniversality.first_event_correct
#check SOnlyUniversality.result_iff_first_event
#print axioms SOnlyUniversality.result_iff_first_event
#check SOnlyUniversality.nonhalting_no_event
#print axioms SOnlyUniversality.nonhalting_no_event

#check SOnlyTapeCompiler.Phase
#print axioms SOnlyTapeCompiler.Phase

#check SOnlyTapeCompiler.Label
#print axioms SOnlyTapeCompiler.Label

#check SOnlyTapeCompiler.phases
#print axioms SOnlyTapeCompiler.phases

#check SOnlyTapeCompiler.mem_phases
#print axioms SOnlyTapeCompiler.mem_phases

#check SOnlyTapeCompiler.labels
#print axioms SOnlyTapeCompiler.labels

#check SOnlyTapeCompiler.mem_labels
#print axioms SOnlyTapeCompiler.mem_labels

#check SOnlyTapeCompiler.labelCount
#print axioms SOnlyTapeCompiler.labelCount

#check SOnlyTapeCompiler.PC
#print axioms SOnlyTapeCompiler.PC

#check SOnlyTapeCompiler.pc
#print axioms SOnlyTapeCompiler.pc

#check SOnlyTapeCompiler.lookup_pc
#print axioms SOnlyTapeCompiler.lookup_pc

#check SOnlyTapeCompiler.withPhase
#print axioms SOnlyTapeCompiler.withPhase

#check SOnlyTapeCompiler.boundary
#print axioms SOnlyTapeCompiler.boundary

#check SOnlyTapeCompiler.pushReg
#print axioms SOnlyTapeCompiler.pushReg

#check SOnlyTapeCompiler.popReg
#print axioms SOnlyTapeCompiler.popReg

#check SOnlyTapeCompiler.mulLabel
#print axioms SOnlyTapeCompiler.mulLabel

#check SOnlyTapeCompiler.consumeLabel
#print axioms SOnlyTapeCompiler.consumeLabel

#check SOnlyTapeCompiler.digitLabel
#print axioms SOnlyTapeCompiler.digitLabel

#check SOnlyTapeCompiler.mulLabel_withPhase
#print axioms SOnlyTapeCompiler.mulLabel_withPhase

#check SOnlyTapeCompiler.consumeLabel_withPhase
#print axioms SOnlyTapeCompiler.consumeLabel_withPhase

#check SOnlyTapeCompiler.digitLabel_withPhase
#print axioms SOnlyTapeCompiler.digitLabel_withPhase

#check SOnlyTapeCompiler.residue
#print axioms SOnlyTapeCompiler.residue

#check SOnlyTapeCompiler.exitLabel
#print axioms SOnlyTapeCompiler.exitLabel

#check SOnlyTapeCompiler.emit
#print axioms SOnlyTapeCompiler.emit

#check SOnlyTapeCompiler.compile
#print axioms SOnlyTapeCompiler.compile

#check SOnlyTapeCompiler.compile_row
#print axioms SOnlyTapeCompiler.compile_row

#check SOnlyTapeCompiler.pushRows
#print axioms SOnlyTapeCompiler.pushRows

#check SOnlyTapeCompiler.popRows
#print axioms SOnlyTapeCompiler.popRows

#check SOnlyTapeCompiler.registers
#print axioms SOnlyTapeCompiler.registers

#check SOnlyTapeCompiler.registers_left
#print axioms SOnlyTapeCompiler.registers_left

#check SOnlyTapeCompiler.registers_right
#print axioms SOnlyTapeCompiler.registers_right

#check SOnlyTapeCompiler.registers_scratch
#print axioms SOnlyTapeCompiler.registers_scratch

#check SOnlyTapeCompiler.values_left
#print axioms SOnlyTapeCompiler.values_left

#check SOnlyTapeCompiler.values_right
#print axioms SOnlyTapeCompiler.values_right

#check SOnlyTapeCompiler.encode
#print axioms SOnlyTapeCompiler.encode

#check SOnlyTapeCompiler.action_executes
#print axioms SOnlyTapeCompiler.action_executes

#check SOnlyTapeCompiler.encoded_step_executes
#print axioms SOnlyTapeCompiler.encoded_step_executes

#check SOnlyTapeCompiler.encoded_boundary_halt
#print axioms SOnlyTapeCompiler.encoded_boundary_halt

#check SOnlyTapeCompiler.encoded_halting_iff
#print axioms SOnlyTapeCompiler.encoded_halting_iff

#check SOnlyTapeCompiler.instruction_independent
#print axioms SOnlyTapeCompiler.instruction_independent

#check SOnlyTapeCompiler.inputMachine
#print axioms SOnlyTapeCompiler.inputMachine

#check SOnlyTapeCompiler.inputValues
#print axioms SOnlyTapeCompiler.inputValues

#check SOnlyTapeCompiler.input_initial
#print axioms SOnlyTapeCompiler.input_initial

#check SOnlyTapeCompiler.input_tape_simulate
#print axioms SOnlyTapeCompiler.input_tape_simulate

#check SOnlyTapeCompiler.input_halting_iff
#print axioms SOnlyTapeCompiler.input_halting_iff

#check SOnlyTapeCompiler.encoded_left_result
#print axioms SOnlyTapeCompiler.encoded_left_result

#check SOnlyTapeCompiler.stack_step_executes
#print axioms SOnlyTapeCompiler.stack_step_executes

#check SOnlyTapeCompiler.stack_boundary_halt
#print axioms SOnlyTapeCompiler.stack_boundary_halt

#check SOnlyTapeCompiler.input_left_stack_result_iff
#print axioms SOnlyTapeCompiler.input_left_stack_result_iff

#check SOnlyTapeCompiler.phases_length
#print axioms SOnlyTapeCompiler.phases_length

#check SOnlyTapeCompiler.labelCount_eq
#print axioms SOnlyTapeCompiler.labelCount_eq

#check SOnlyTapeCompilerCheckpoints.sourceStep_halt
#print axioms SOnlyTapeCompilerCheckpoints.sourceStep_halt

#check SOnlyTapeCompilerCheckpoints.sourceRun_halt
#print axioms SOnlyTapeCompilerCheckpoints.sourceRun_halt

#check SOnlyTapeCompilerCheckpoints.sourceRun_after_halt
#print axioms SOnlyTapeCompilerCheckpoints.sourceRun_after_halt

#check SOnlyTapeCompilerCheckpoints.sourceRun_halts_equal
#print axioms SOnlyTapeCompilerCheckpoints.sourceRun_halts_equal

#check SOnlyTapeCompilerCheckpoints.partial_run_cases
#print axioms SOnlyTapeCompilerCheckpoints.partial_run_cases

#check SOnlyTapeCompilerCheckpoints.simulate_run
#print axioms SOnlyTapeCompilerCheckpoints.simulate_run

#check SOnlyTapeCompilerCheckpoints.reflects_halt_bounded
#print axioms SOnlyTapeCompilerCheckpoints.reflects_halt_bounded

#check SOnlyTapeCompilerCheckpoints.halting_iff
#print axioms SOnlyTapeCompilerCheckpoints.halting_iff

#check SOnlyTapeCompilerCheckpoints.reflects_halt_state
#print axioms SOnlyTapeCompilerCheckpoints.reflects_halt_state

#check SOnlyTapeCompilerCheckpoints.result_iff
#print axioms SOnlyTapeCompilerCheckpoints.result_iff

#check SOnlyTapeStacks.Direction
#print axioms SOnlyTapeStacks.Direction

#check SOnlyTapeStacks.Action
#print axioms SOnlyTapeStacks.Action

#check SOnlyTapeStacks.Machine
#print axioms SOnlyTapeStacks.Machine

#check SOnlyTapeStacks.TapeConfig
#print axioms SOnlyTapeStacks.TapeConfig

#check SOnlyTapeStacks.StackConfig
#print axioms SOnlyTapeStacks.StackConfig

#check SOnlyTapeStacks.ray
#print axioms SOnlyTapeStacks.ray

#check SOnlyTapeStacks.ray_nil
#print axioms SOnlyTapeStacks.ray_nil

#check SOnlyTapeStacks.ray_cons_zero
#print axioms SOnlyTapeStacks.ray_cons_zero

#check SOnlyTapeStacks.ray_cons_succ
#print axioms SOnlyTapeStacks.ray_cons_succ

#check SOnlyTapeStacks.ray_tail
#print axioms SOnlyTapeStacks.ray_tail

#check SOnlyTapeStacks.writeAt
#print axioms SOnlyTapeStacks.writeAt

#check SOnlyTapeStacks.writeAt_same
#print axioms SOnlyTapeStacks.writeAt_same

#check SOnlyTapeStacks.writeAt_other
#print axioms SOnlyTapeStacks.writeAt_other

#check SOnlyTapeStacks.displacement
#print axioms SOnlyTapeStacks.displacement

#check SOnlyTapeStacks.applyTape
#print axioms SOnlyTapeStacks.applyTape

#check SOnlyTapeStacks.applyStacks
#print axioms SOnlyTapeStacks.applyStacks

#check SOnlyTapeStacks.Represents
#print axioms SOnlyTapeStacks.Represents

#check SOnlyTapeStacks.readStacks
#print axioms SOnlyTapeStacks.readStacks

#check SOnlyTapeStacks.represents_read
#print axioms SOnlyTapeStacks.represents_read

#check SOnlyTapeStacks.apply_represents
#print axioms SOnlyTapeStacks.apply_represents

#check SOnlyTapeStacks.tapeStep
#print axioms SOnlyTapeStacks.tapeStep

#check SOnlyTapeStacks.stackStep
#print axioms SOnlyTapeStacks.stackStep

#check SOnlyTapeStacks.OptionRelated
#print axioms SOnlyTapeStacks.OptionRelated

#check SOnlyTapeStacks.step_represents
#print axioms SOnlyTapeStacks.step_represents

#check SOnlyTapeStacks.run
#print axioms SOnlyTapeStacks.run

#check SOnlyTapeStacks.run_represents
#print axioms SOnlyTapeStacks.run_represents

#check SOnlyTapeStacks.inputCells
#print axioms SOnlyTapeStacks.inputCells

#check SOnlyTapeStacks.tapeInput
#print axioms SOnlyTapeStacks.tapeInput

#check SOnlyTapeStacks.stackInput
#print axioms SOnlyTapeStacks.stackInput

#check SOnlyTapeStacks.input_represents
#print axioms SOnlyTapeStacks.input_represents

#check SOnlyTapeStacks.input_run_represents
#print axioms SOnlyTapeStacks.input_run_represents

#check SOnlyTapeStacks.optionRelated_none_iff
#print axioms SOnlyTapeStacks.optionRelated_none_iff

#check SOnlyTapeStacks.step_none_iff
#print axioms SOnlyTapeStacks.step_none_iff

#check SOnlyTapeStacks.run_none_iff
#print axioms SOnlyTapeStacks.run_none_iff

#check SOnlyTapeStacks.HaltsAfter
#print axioms SOnlyTapeStacks.HaltsAfter

#check SOnlyTapeStacks.haltsAfter_iff
#print axioms SOnlyTapeStacks.haltsAfter_iff

#check SOnlyTapeStacks.input_haltsAfter_iff
#print axioms SOnlyTapeStacks.input_haltsAfter_iff

#check SOnlyTapeStacks.input_halts_iff
#print axioms SOnlyTapeStacks.input_halts_iff

#check SOnlyTapeStacks.input_diverges_iff
#print axioms SOnlyTapeStacks.input_diverges_iff

#check SOnlyTapeStacks.digit
#print axioms SOnlyTapeStacks.digit

#check SOnlyTapeStacks.stackCode
#print axioms SOnlyTapeStacks.stackCode

#check SOnlyTapeStacks.stackCode_nil
#print axioms SOnlyTapeStacks.stackCode_nil

#check SOnlyTapeStacks.stackCode_cons
#print axioms SOnlyTapeStacks.stackCode_cons

#check SOnlyTapeStacks.digit_positive
#print axioms SOnlyTapeStacks.digit_positive

#check SOnlyTapeStacks.digit_lt_base
#print axioms SOnlyTapeStacks.digit_lt_base

#check SOnlyTapeStacks.stackCode_cons_positive
#print axioms SOnlyTapeStacks.stackCode_cons_positive

#check SOnlyTapeStacks.stackCode_eq_zero_iff
#print axioms SOnlyTapeStacks.stackCode_eq_zero_iff

#check SOnlyTapeStacks.stackCode_div
#print axioms SOnlyTapeStacks.stackCode_div

#check SOnlyTapeStacks.stackCode_mod
#print axioms SOnlyTapeStacks.stackCode_mod

#check SOnlyTapeStacks.decodeDigit
#print axioms SOnlyTapeStacks.decodeDigit

#check SOnlyTapeStacks.decodeDigit_zero
#print axioms SOnlyTapeStacks.decodeDigit_zero

#check SOnlyTapeStacks.decodeDigit_digit
#print axioms SOnlyTapeStacks.decodeDigit_digit

#check SOnlyTapeStacks.code_pop
#print axioms SOnlyTapeStacks.code_pop

#check SOnlyTapeStacks.code_pop_symbol
#print axioms SOnlyTapeStacks.code_pop_symbol

#check SOnlyTapeStacks.code_pop_rest
#print axioms SOnlyTapeStacks.code_pop_rest

#check SOnlyTapeStacks.stackCode_injective
#print axioms SOnlyTapeStacks.stackCode_injective

#check SOnlyTapeStacks.EncodedConfig
#print axioms SOnlyTapeStacks.EncodedConfig

#check SOnlyTapeStacks.encodeStacks
#print axioms SOnlyTapeStacks.encodeStacks

#check SOnlyTapeStacks.applyEncoded
#print axioms SOnlyTapeStacks.applyEncoded

#check SOnlyTapeStacks.applyEncoded_encodeStacks
#print axioms SOnlyTapeStacks.applyEncoded_encodeStacks

#check SOnlyTapeStacks.encodedStep
#print axioms SOnlyTapeStacks.encodedStep

#check SOnlyTapeStacks.encodedStep_encodeStacks
#print axioms SOnlyTapeStacks.encodedStep_encodeStacks

#check SOnlyTapeStacks.run_map
#print axioms SOnlyTapeStacks.run_map

#check SOnlyTapeStacks.encodedRun_encodeStacks
#print axioms SOnlyTapeStacks.encodedRun_encodeStacks

#check SOnlyTapeStacks.encoded_haltsAfter_iff
#print axioms SOnlyTapeStacks.encoded_haltsAfter_iff

#check SOnlyTapeStacks.input_encoded_haltsAfter_iff
#print axioms SOnlyTapeStacks.input_encoded_haltsAfter_iff

#check TapeStacksTests.backtrack
#print axioms TapeStacksTests.backtrack

#check TapeStacksTests.finalBacktrack
#print axioms TapeStacksTests.finalBacktrack

#check TapeStacksTests.emptyWalk
#print axioms TapeStacksTests.emptyWalk

#check TapeStacksTests.stays
#print axioms TapeStacksTests.stays

#check SOnlyTuringUniversality.controller
#print axioms SOnlyTuringUniversality.controller

#check SOnlyTuringUniversality.selector
#print axioms SOnlyTuringUniversality.selector

#check SOnlyTuringUniversality.event
#print axioms SOnlyTuringUniversality.event

#check SOnlyTuringUniversality.decode
#print axioms SOnlyTuringUniversality.decode

#check SOnlyTuringUniversality.TapeMachine
#print axioms SOnlyTuringUniversality.TapeMachine

#check SOnlyTuringUniversality.Halts
#print axioms SOnlyTuringUniversality.Halts

#check SOnlyTuringUniversality.encode
#print axioms SOnlyTuringUniversality.encode

#check SOnlyTuringUniversality.trajectory
#print axioms SOnlyTuringUniversality.trajectory

#check SOnlyTuringUniversality.FirstEvent
#print axioms SOnlyTuringUniversality.FirstEvent

#check SOnlyTuringUniversality.starts_at_encoder
#print axioms SOnlyTuringUniversality.starts_at_encoder

#check SOnlyTuringUniversality.root_reset
#print axioms SOnlyTuringUniversality.root_reset

#check SOnlyTuringUniversality.no_interinvocation_state
#print axioms SOnlyTuringUniversality.no_interinvocation_state

#check SOnlyTuringUniversality.all_input_linear
#print axioms SOnlyTuringUniversality.all_input_linear

#check SOnlyTuringUniversality.every_step_native
#print axioms SOnlyTuringUniversality.every_step_native

#check SOnlyTuringUniversality.selector_executes
#print axioms SOnlyTuringUniversality.selector_executes

#check SOnlyTuringUniversality.halting_iff_event
#print axioms SOnlyTuringUniversality.halting_iff_event

#check SOnlyTuringUniversality.halting_first_result
#print axioms SOnlyTuringUniversality.halting_first_result

#check SOnlyTuringUniversality.halting_iff_first_event
#print axioms SOnlyTuringUniversality.halting_iff_first_event

#check SOnlyTuringUniversality.nonhalting_no_event
#print axioms SOnlyTuringUniversality.nonhalting_no_event

#check SOnlyTuringUniversality.LeftStackResult
#print axioms SOnlyTuringUniversality.LeftStackResult

#check SOnlyTuringUniversality.left_stack_result_iff_first_event
#print axioms SOnlyTuringUniversality.left_stack_result_iff_first_event

#check SOnlyStack.sourceRun_join
#print axioms SOnlyStack.sourceRun_join

#check SOnlyStack.transfer_exact
#print axioms SOnlyStack.transfer_exact

#check SOnlyStack.multiply_exact
#print axioms SOnlyStack.multiply_exact

#check SOnlyStack.push_macro_exact
#print axioms SOnlyStack.push_macro_exact

#check SOnlyStack.push_macro_positive
#print axioms SOnlyStack.push_macro_positive

#check SOnlyStack.push_entry_nonhalting
#print axioms SOnlyStack.push_entry_nonhalting

#check SOnlyStack.pop_cycle_exact
#print axioms SOnlyStack.pop_cycle_exact

#check SOnlyStack.pop_consume_exact
#print axioms SOnlyStack.pop_consume_exact

#check SOnlyStack.pop_macro_exact
#print axioms SOnlyStack.pop_macro_exact

#check SOnlyStack.pop_macro_positive
#print axioms SOnlyStack.pop_macro_positive

#check SOnlyStack.pop_entry_nonhalting
#print axioms SOnlyStack.pop_entry_nonhalting

#check SOnlyStack.sourceRun_add
#print axioms SOnlyStack.sourceRun_add

#check SOnlyStack.Reaches
#print axioms SOnlyStack.Reaches

#check SOnlyStack.inc_step
#print axioms SOnlyStack.inc_step

#check SOnlyStack.dec_pos_step
#print axioms SOnlyStack.dec_pos_step

#check SOnlyStack.dec_zero_step
#print axioms SOnlyStack.dec_zero_step

#check SOnlyStack.inc_chain
#print axioms SOnlyStack.inc_chain

#check SOnlyStack.transfer
#print axioms SOnlyStack.transfer

#check SOnlyStack.values
#print axioms SOnlyStack.values

#check SOnlyStack.values_t
#print axioms SOnlyStack.values_t

#check SOnlyStack.values_x
#print axioms SOnlyStack.values_x

#check SOnlyStack.values_put_t
#print axioms SOnlyStack.values_put_t

#check SOnlyStack.values_put_x
#print axioms SOnlyStack.values_put_x

#check SOnlyStack.multiply_loop
#print axioms SOnlyStack.multiply_loop

#check SOnlyStack.transfer_values
#print axioms SOnlyStack.transfer_values

#check SOnlyStack.PushRows
#print axioms SOnlyStack.PushRows

#check SOnlyStack.push_macro
#print axioms SOnlyStack.push_macro

#check SOnlyStack.dec_chain
#print axioms SOnlyStack.dec_chain

#check SOnlyStack.PopRows
#print axioms SOnlyStack.PopRows

#check SOnlyStack.pop_cycle
#print axioms SOnlyStack.pop_cycle

#check SOnlyStack.pop_consume
#print axioms SOnlyStack.pop_consume

#check SOnlyStack.pop_macro
#print axioms SOnlyStack.pop_macro

#check SOnlyStack.pop_macro_div_mod
#print axioms SOnlyStack.pop_macro_div_mod

#check SOnlyStack.PopTable.consume
#print axioms SOnlyStack.PopTable.consume

#check SOnlyStack.PopTable.quotientAdd
#print axioms SOnlyStack.PopTable.quotientAdd

#check SOnlyStack.PopTable.transfer
#print axioms SOnlyStack.PopTable.transfer

#check SOnlyStack.PopTable.transferAdd
#print axioms SOnlyStack.PopTable.transferAdd

#check SOnlyStack.PopTable.done
#print axioms SOnlyStack.PopTable.done

#check SOnlyStack.PopTable.machine
#print axioms SOnlyStack.PopTable.machine

#check SOnlyStack.PopTable.consume_row
#print axioms SOnlyStack.PopTable.consume_row

#check SOnlyStack.PopTable.cycle_end
#print axioms SOnlyStack.PopTable.cycle_end

#check SOnlyStack.PopTable.quotient_row
#print axioms SOnlyStack.PopTable.quotient_row

#check SOnlyStack.PopTable.transfer_row
#print axioms SOnlyStack.PopTable.transfer_row

#check SOnlyStack.PopTable.transfer_add_row
#print axioms SOnlyStack.PopTable.transfer_add_row

#check SOnlyStack.PopTable.done_row
#print axioms SOnlyStack.PopTable.done_row

#check SOnlyStack.PopTable.rows
#print axioms SOnlyStack.PopTable.rows

#check SOnlyStack.PopTable.executes
#print axioms SOnlyStack.PopTable.executes

#check SOnlyStack.PushLabel
#print axioms SOnlyStack.PushLabel

#check SOnlyStack.pushEntry
#print axioms SOnlyStack.pushEntry

#check SOnlyStack.pushMultiplyAdd
#print axioms SOnlyStack.pushMultiplyAdd

#check SOnlyStack.pushTransfer
#print axioms SOnlyStack.pushTransfer

#check SOnlyStack.pushTransferAdd
#print axioms SOnlyStack.pushTransferAdd

#check SOnlyStack.pushDigitAdd
#print axioms SOnlyStack.pushDigitAdd

#check SOnlyStack.pushDone
#print axioms SOnlyStack.pushDone

#check SOnlyStack.pushMachine
#print axioms SOnlyStack.pushMachine

#check SOnlyStack.pushMachine_entry_row
#print axioms SOnlyStack.pushMachine_entry_row

#check SOnlyStack.pushMachine_multiply_rows
#print axioms SOnlyStack.pushMachine_multiply_rows

#check SOnlyStack.pushMachine_multiply_back
#print axioms SOnlyStack.pushMachine_multiply_back

#check SOnlyStack.pushMachine_transfer_row
#print axioms SOnlyStack.pushMachine_transfer_row

#check SOnlyStack.pushMachine_transfer_add_row
#print axioms SOnlyStack.pushMachine_transfer_add_row

#check SOnlyStack.pushMachine_digit_rows
#print axioms SOnlyStack.pushMachine_digit_rows

#check SOnlyStack.pushMachine_digit_done
#print axioms SOnlyStack.pushMachine_digit_done

#check SOnlyStack.pushMachine_done_row
#print axioms SOnlyStack.pushMachine_done_row

#check SOnlyStack.pushRows
#print axioms SOnlyStack.pushRows

#check SOnlyStack.pushMachine_correct
#print axioms SOnlyStack.pushMachine_correct

#check SOnlyStack.pushMachine_final_fixed
#print axioms SOnlyStack.pushMachine_final_fixed
