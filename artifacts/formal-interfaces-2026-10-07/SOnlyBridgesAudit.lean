import SOnlyStageEvents
import SOnlyInitial
import SOnlyProvenance
import SOnlyCounter

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
