import NearCompression

#print axioms NearCompression.boundaryLinks_length
#print axioms NearCompression.exact_chain
#print axioms NearCompression.certified_chain_or_collision
#print axioms NearCompression.certified_run_or_collision
#print axioms NearCompression.terminal_tag_matters
#print axioms NearCompression.boundary_collision_to_hash
#print axioms NearCompression.certified_run_or_hash_collision
#print axioms NearCompression.erased_tag_cannot_decode
#print axioms NearCompression.legacy_gas_cap
#print axioms NearCompression.target_exceeds_legacy
#print axioms NearCompression.gas_capacity_290

#print axioms NearCompression.capture_restore_real
#print axioms NearCompression.restore_capture_state
#print axioms NearCompression.capture_restore_state
#print axioms NearCompression.restored_state_backed
#print axioms NearCompression.backed_state_roundtrip
#print axioms NearCompression.capture_restore_result
#print axioms NearCompression.restore_capture_result
#print axioms NearCompression.backed_result_roundtrip
#print axioms NearCompression.capture_state_injective_on_backed
#print axioms NearCompression.boundary_store_agrees
#print axioms NearCompression.step_preserves_backing
#print axioms NearCompression.segment_preserves_backing
#print axioms NearCompression.finite_segment_correct
#print axioms NearCompression.restore_result_injective
#print axioms NearCompression.different_backing_changes_state
#print axioms NearCompression.finite_fold_correct
#print axioms NearCompression.finite_run_correct
#print axioms NearCompression.boundary_links_backed
#print axioms NearCompression.finite_codec_roundtrip
#print axioms NearCompression.finite_codec_boundary_decodes

#print axioms NearCompression.finite_certified_run_or_hash_collision

open NearCompression NearSpecV3.Wasm

-- Identity boundary encoding is not assumed. Even with an arbitrary digest,
-- a zero-length exact segment is valid for every actual machine state.
example {D : Type} (commit : Res → D) (cfg : NearCfg) (p : Prepared) (s : St) :
    CertifiedChain commit cfg p (.cont s) [⟨0, s, .cont s⟩] (.cont s) := by
  constructor
  · intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    subst w
    rfl
  · intro a b hab
    simp only [boundaryLinks, List.mem_cons, List.not_mem_nil, or_false] at hab
    rcases hab with hab | hab <;> cases hab <;> rfl

-- Terminal continuations remain distinct even if gas and all memory agree.
example (s : St) : (Res.fin s) ≠ Res.cont s := by intro h; cases h

-- This is a byte-encoder alias, not a cryptographic hash collision. The decoder
-- theorem is what prevents such aliases from being called hash collisions.
example (decode : List UInt8 → Option Res) (s : St)
    (hf : decode [] = some (.fin s)) (hc : decode [] = some (.cont s)) : False :=
  erased_tag_cannot_decode (fun _ => []) decode s rfl hf hc

#print axioms NearCompression.rebuild_map_equiv
#print axioms NearCompression.normalize_acct_equiv
#print axioms NearCompression.normalize_recorder_equiv
#print axioms NearCompression.acct_touch_equiv
#print axioms NearCompression.acct_touch_all_equiv
#print axioms NearCompression.recorder_record_equiv
#print axioms NearCompression.recorder_record_nodes_equiv
#print axioms NearCompression.accounting_commit_equiv

#print axioms NearCompression.byte_array_beq_eq

#print axioms NearCompression.normalized_overlay_lookup

#print axioms NearCompression.normalized_over_limit

#print axioms NearCompression.normalized_deref

#print axioms NearCompression.normalized_storage_has_key

#print axioms NearCompression.normalized_storage_read

#print axioms NearCompression.normalized_write_like

#print axioms NearCompression.normalized_real_equiv
#print axioms NearCompression.state_equiv_gas
#print axioms NearCompression.real_equiv_install
#print axioms NearCompression.state_equiv_install
#print axioms NearCompression.real_op_host_run
#print axioms NearCompression.real_op_host_equiv
#print axioms NearCompression.normalized_read_host
#print axioms NearCompression.normalized_write_host
#print axioms NearCompression.normalized_has_key_host

#print axioms NearCompression.real_equiv_overlay_insert

#print axioms NearCompression.real_put_host_equiv

#print axioms NearCompression.host_bind_equiv

#print axioms NearCompression.normalized_state_equiv

#print axioms NearCompression.real_set_host_equiv

#print axioms NearCompression.normalized_read_host_from_state

#print axioms NearCompression.storage_read_equiv
#print axioms NearCompression.storage_write_like_equiv
#print axioms NearCompression.storage_has_key_equiv
#print axioms NearCompression.storage_read_host_equiv
#print axioms NearCompression.storage_write_host_equiv
#print axioms NearCompression.storage_has_key_host_equiv
#print axioms NearCompression.real_equiv_remove_record
#print axioms NearCompression.real_equiv_over_limit

#print axioms NearCompression.host_get_bind_run
#print axioms NearCompression.real_get_host_equiv

#print axioms NearCompression.real_has_host_equiv
#print axioms NearCompression.observe_host_equiv

#print axioms NearCompression.host_sim_pure
#print axioms NearCompression.host_sim_error
#print axioms NearCompression.host_sim_bind
#print axioms NearCompression.host_sim_get_bind
#print axioms NearCompression.state_equiv_set_gas
#print axioms NearCompression.with_gas_run
#print axioms NearCompression.host_sim_with_gas
#print axioms NearCompression.state_equiv_mem_bytes
#print axioms NearCompression.state_equiv_read_byte
#print axioms NearCompression.state_equiv_read_bytes
#print axioms NearCompression.host_sim_read_mem

#print axioms NearCompression.host_sim_charged_read

#print axioms NearCompression.host_sim_charged_return

#print axioms NearCompression.host_sim_reg_get

#print axioms NearCompression.host_sim_mem_or_reg

#print axioms NearCompression.state_equiv_set_registers
#print axioms NearCompression.register_write_body_equiv
#print axioms NearCompression.host_sim_charged_register_write
#print axioms NearCompression.host_sim_reg_set

#print axioms NearCompression.state_equiv_write_byte

#print axioms NearCompression.for_in_state_equiv

#print axioms NearCompression.state_equiv_write_bytes

#print axioms NearCompression.host_sim_charged_memory_write

#print axioms NearCompression.host_sim_write_mem

#print axioms NearCompression.state_equiv_pop_n
#print axioms NearCompression.state_equiv_push_v
#print axioms NearCompression.host_sim_push_ret
#print axioms NearCompression.host_sim_for_in_list
#print axioms NearCompression.host_sim_for_in
#print axioms NearCompression.host_sim_pop_iteration
#print axioms NearCompression.host_sim_pop_args

#print axioms NearCompression.host_sim_has_key_finish
#print axioms NearCompression.host_sim_has_key_code
#print axioms NearCompression.actual_storage_has_key_code
#print axioms NearCompression.actual_storage_has_key_sim

#print axioms NearCompression.host_sim_read_result

#print axioms NearCompression.host_sim_mock_read_value

#print axioms NearCompression.host_sim_read_finish

#print axioms NearCompression.host_sim_read_code

#print axioms NearCompression.actual_storage_read_code

#print axioms NearCompression.actual_storage_read_sim

#print axioms NearCompression.host_sim_storage_usage
#print axioms NearCompression.host_sim_record_removal
#print axioms NearCompression.host_sim_remove_result
#print axioms NearCompression.host_sim_remove_finish
#print axioms NearCompression.host_sim_remove_code
#print axioms NearCompression.actual_storage_remove_code
#print axioms NearCompression.actual_storage_remove_sim

#print axioms NearCompression.host_set_then_equiv

#print axioms NearCompression.host_sim_write_result

#print axioms NearCompression.storage_write_external_equiv

#print axioms NearCompression.host_sim_write_finish

#print axioms NearCompression.host_sim_write_charged_finish

#print axioms NearCompression.host_sim_write_value_code

#print axioms NearCompression.host_sim_write_code

#print axioms NearCompression.actual_storage_write_code

#print axioms NearCompression.actual_storage_write_sim


#print axioms NearCompression.real_equiv_refl
#print axioms NearCompression.real_equiv_symm
#print axioms NearCompression.real_equiv_trans
#print axioms NearCompression.optional_real_equiv_refl
#print axioms NearCompression.optional_real_equiv_symm
#print axioms NearCompression.optional_real_equiv_trans
#print axioms NearCompression.state_equiv_refl
#print axioms NearCompression.state_equiv_symm
#print axioms NearCompression.state_equiv_trans
#print axioms NearCompression.result_equiv_refl
#print axioms NearCompression.result_equiv_symm
#print axioms NearCompression.result_equiv_trans
#print axioms NearCompression.result_equiv_bind
#print axioms NearCompression.segment_equiv_of_step
#print axioms NearCompression.fold_equiv_of_step
#print axioms NearCompression.run_equiv_of_step
#print axioms NearCompression.normalized_run_of_step
#print axioms NearCompression.result_equiv_terminal_tag

#print axioms NearCompression.observational_chain

#print axioms NearCompression.observational_encoding_alias

#print axioms NearCompression.observational_chain_or_hash_collision

#print axioms NearCompression.observational_run_or_hash_collision

#print axioms NearCompression.state_equiv_set_frame

#print axioms NearCompression.do_return_equiv

#print axioms NearCompression.do_br_equiv

#print axioms NearCompression.mem_copy_equiv

#print axioms NearCompression.mem_init_equiv

#print axioms NearCompression.sync_equiv

#print axioms NearCompression.charge_equiv

#print axioms NearCompression.state_equiv_control_update
#print axioms NearCompression.state_equiv_set_stack

#print axioms NearCompression.step_equiv_of_exec

#print axioms NearCompression.state_equiv_real_is_some
#print axioms NearCompression.call_host_equiv

#print axioms NearCompression.core_storage_call_equiv

#print axioms NearCompression.state_equiv_set_stack_rem

#print axioms NearCompression.state_equiv_stack_frames

#print axioms NearCompression.entry_frame_equiv

#print axioms NearCompression.enter_equiv

#print axioms NearCompression.call_func_equiv

#print axioms NearCompression.exec_call_equiv
#print axioms NearCompression.exec_call_indirect_equiv

#print axioms NearCompression.exec_num_equiv

#print axioms NearCompression.exec_numeric_instruction_equiv

#print axioms NearCompression.pop_n_stack_form

#print axioms NearCompression.stack_control_instruction_equiv

#print axioms NearCompression.pop_ref_stack_form
#print axioms NearCompression.state_equiv_stack_globals

#print axioms NearCompression.state_equiv_data_update
#print axioms NearCompression.memory_table_instruction_equiv

#print axioms NearCompression.state_equiv_read_le
#print axioms NearCompression.load_instruction_equiv

#print axioms NearCompression.for_in_plain_state_equiv

#print axioms NearCompression.state_equiv_write_le

#print axioms NearCompression.mem_fill_equiv

#print axioms NearCompression.store_instruction_equiv

#print axioms NearCompression.bulk_memory_instruction_equiv

#print axioms NearCompression.state_equiv_table_elements

#print axioms NearCompression.table_init_equiv

#print axioms NearCompression.bulk_table_instruction_equiv

#print axioms NearCompression.table_init_instruction_equiv

#print axioms NearCompression.exec_equiv_of_imports
#print axioms NearCompression.step_preserves_maps_of_imports

#print axioms NearCompression.host_sim_hash_call_code

#print axioms NearCompression.actual_sha256_code

#print axioms NearCompression.actual_keccak256_code

#print axioms NearCompression.actual_keccak512_code

#print axioms NearCompression.actual_ripemd160_code

#print axioms NearCompression.actual_hash_call_sim

#print axioms NearCompression.hash_call_host_equiv

#print axioms NearCompression.proved_host_sim

#print axioms NearCompression.checked_imports_preserve_maps

#print axioms NearCompression.checked_imports_step_preservation

#print axioms NearCompression.checked_imports_run_or_hash_collision

#print axioms NearCompression.context_register_code_sim

#print axioms NearCompression.actual_context_register_code

#print axioms NearCompression.actual_context_register_sim

#print axioms NearCompression.context_nat_value_equiv

#print axioms NearCompression.context_nat_code_sim

#print axioms NearCompression.actual_context_nat_code

#print axioms NearCompression.actual_context_nat_sim

#print axioms NearCompression.actual_context_host_sim

#print axioms NearCompression.context_register_body_sim

#print axioms NearCompression.read_register_code_sim

#print axioms NearCompression.write_register_code_sim

#print axioms NearCompression.register_len_code_sim

#print axioms NearCompression.actual_read_register_code

#print axioms NearCompression.actual_write_register_code

#print axioms NearCompression.actual_register_len_code

#print axioms NearCompression.actual_register_host_sim

#print axioms NearCompression.host_sim_get_u128

#print axioms NearCompression.host_sim_set_u128

#print axioms NearCompression.balance_host_value_equiv

#print axioms NearCompression.balance_host_code_sim

#print axioms NearCompression.actual_balance_host_code

#print axioms NearCompression.actual_balance_host_sim

#print axioms NearCompression.listed_balance_host_sim

#print axioms NearCompression.get_u128_code_sim

#print axioms NearCompression.return_commit_sim

#print axioms NearCompression.return_checked_commit_sim

#print axioms NearCompression.return_finish_sim

#print axioms NearCompression.value_return_code_sim

#print axioms NearCompression.actual_value_return_code

#print axioms NearCompression.actual_value_return_sim

#print axioms NearCompression.host_sim_log_len_exceeded

#print axioms NearCompression.host_sim_check_can_log

#print axioms NearCompression.host_sim_append_log

#print axioms NearCompression.host_sim_checked_append_log

#print axioms NearCompression.host_sim_push_log

#print axioms NearCompression.host_sim_guest_panic

#print axioms NearCompression.panic_code_sim

#print axioms NearCompression.actual_panic_code

#print axioms NearCompression.actual_panic_sim

#print axioms NearCompression.utf16_buffer_sim

#print axioms NearCompression.utf16_finish_sim

#print axioms NearCompression.utf16_code_sim

#print axioms NearCompression.actual_utf16_code

#print axioms NearCompression.host_sim_utf16

#print axioms NearCompression.utf16_decoded_sim
#print axioms NearCompression.utf16_length_checked_sim

#print axioms NearCompression.host_bind_if

#print axioms NearCompression.host_error_bind

#print axioms NearCompression.decoded_log_code_sim

#print axioms NearCompression.actual_log_utf16_code

#print axioms NearCompression.actual_log_utf16_sim

#print axioms NearCompression.utf8_accumulate_sim

#print axioms NearCompression.utf8_scan_step_sim

#print axioms NearCompression.utf8_buffer_sim

#print axioms NearCompression.utf8_finish_sim

#print axioms NearCompression.utf8_code_sim

#print axioms NearCompression.actual_utf8_code

#print axioms NearCompression.host_sim_utf8

#print axioms NearCompression.actual_log_utf8_code

#print axioms NearCompression.actual_log_utf8_sim

#print axioms NearCompression.decoded_panic_code_sim

#print axioms NearCompression.actual_panic_utf8_code

#print axioms NearCompression.actual_panic_utf8_sim

#print axioms NearCompression.abort_finish_sim

#print axioms NearCompression.abort_read_sim

#print axioms NearCompression.abort_code_sim

#print axioms NearCompression.actual_abort_code

#print axioms NearCompression.actual_abort_sim

#print axioms NearCompression.ed25519_code_sim

#print axioms NearCompression.actual_ed25519_code

#print axioms NearCompression.actual_ed25519_sim

#print axioms NearCompression.promise_result_body_sim

#print axioms NearCompression.promise_result_code_sim

#print axioms NearCompression.promise_return_body_sim

#print axioms NearCompression.promise_return_code_sim

#print axioms NearCompression.actual_promise_result_code

#print axioms NearCompression.actual_promise_return_code

#print axioms NearCompression.actual_promise_result_sim

#print axioms NearCompression.actual_promise_return_sim

#print axioms NearCompression.state_equiv_return_receipt

#print axioms NearCompression.account_id_code_sim

#print axioms NearCompression.host_sim_read_account_id

#print axioms NearCompression.host_sim_push_action

#print axioms NearCompression.state_equiv_set_promises

#print axioms NearCompression.host_sim_push_promise

#print axioms NearCompression.host_sim_new_receipt

#print axioms NearCompression.create_receipt_code_sim

#print axioms NearCompression.batch_create_code_sim

#print axioms NearCompression.actual_batch_create_code

#print axioms NearCompression.actual_batch_create_sim

#print axioms NearCompression.host_sim_then_data_ids

#print axioms NearCompression.batch_then_body_sim

#print axioms NearCompression.batch_then_code_sim

#print axioms NearCompression.actual_batch_then_code

#print axioms NearCompression.actual_batch_then_sim

#print axioms NearCompression.promise_and_finish_sim

#print axioms NearCompression.promise_and_code_sim

#print axioms NearCompression.actual_promise_and_code

#print axioms NearCompression.actual_promise_and_sim

#print axioms NearCompression.host_sim_promise_receipt

#print axioms NearCompression.host_sim_action_base

#print axioms NearCompression.host_sim_action_byte

#print axioms NearCompression.host_sim_deduct_balance

#print axioms NearCompression.transfer_body_sim

#print axioms NearCompression.transfer_code_sim

#print axioms NearCompression.actual_transfer_code

#print axioms NearCompression.actual_transfer_sim

#print axioms NearCompression.action_deposit_sim

#print axioms NearCompression.append_function_action_sim

#print axioms NearCompression.function_action_code_sim

#print axioms NearCompression.actual_function_action_code

#print axioms NearCompression.host_sim_function_action

#print axioms NearCompression.actual_function_call_sim
#print axioms NearCompression.actual_function_call_weight_sim

#print axioms NearCompression.create_receipt_then_sim

#print axioms NearCompression.dependent_receipt_then_sim

#print axioms NearCompression.call_and_return_sim

#print axioms NearCompression.promise_create_code_sim

#print axioms NearCompression.actual_promise_create_code

#print axioms NearCompression.actual_promise_create_sim

#print axioms NearCompression.promise_then_code_sim

#print axioms NearCompression.actual_promise_then_code

#print axioms NearCompression.actual_promise_then_sim

#print axioms NearCompression.deploy_action_code_sim

#print axioms NearCompression.actual_deploy_action_code

#print axioms NearCompression.actual_deploy_action_sim

#print axioms NearCompression.create_account_action_code_sim

#print axioms NearCompression.actual_create_account_action_code

#print axioms NearCompression.actual_create_account_action_sim

#print axioms NearCompression.key_action_code_sim

#print axioms NearCompression.actual_full_access_code

#print axioms NearCompression.actual_delete_key_code

#print axioms NearCompression.actual_full_access_sim

#print axioms NearCompression.actual_delete_key_sim

#print axioms NearCompression.restricted_key_finish_sim

#print axioms NearCompression.restricted_key_body_sim

#print axioms NearCompression.restricted_key_code_sim

#print axioms NearCompression.actual_restricted_key_code

#print axioms NearCompression.actual_restricted_key_sim

#print axioms NearCompression.stake_action_code_sim

#print axioms NearCompression.actual_stake_action_code

#print axioms NearCompression.actual_stake_action_sim

#print axioms NearCompression.refund_body_sim

#print axioms NearCompression.delete_account_body_sim

#print axioms NearCompression.account_action_code_sim

#print axioms NearCompression.actual_refund_code

#print axioms NearCompression.actual_delete_account_code

#print axioms NearCompression.actual_refund_sim

#print axioms NearCompression.actual_delete_account_sim

#print axioms NearCompression.yield_resume_body_sim

#print axioms NearCompression.yield_resume_code_sim

#print axioms NearCompression.actual_yield_resume_code

#print axioms NearCompression.actual_yield_resume_sim

#print axioms NearCompression.state_equiv_data_id

#print axioms NearCompression.yield_receipt_then_sim

#print axioms NearCompression.yield_create_finish_sim

#print axioms NearCompression.yield_create_code_sim

#print axioms NearCompression.actual_yield_create_code

#print axioms NearCompression.actual_yield_create_sim

#print axioms NearCompression.append_yield_action_sim

#print axioms NearCompression.yield_id_receipt_then_sim

#print axioms NearCompression.yield_id_finish_sim

#print axioms NearCompression.yield_id_code_sim

#print axioms NearCompression.actual_yield_id_code

#print axioms NearCompression.host_sim_yield_id

#print axioms NearCompression.actual_yield_id_sim

#print axioms NearCompression.gas_dispatch_sim

#print axioms NearCompression.actual_gas_sim

#print axioms NearCompression.deprecated_dispatch_sim

#print axioms NearCompression.actual_iterator_prefix_sim

#print axioms NearCompression.actual_iterator_range_sim

#print axioms NearCompression.actual_iterator_next_sim

#print axioms NearCompression.validator_output_sim

#print axioms NearCompression.validator_stake_code_sim

#print axioms NearCompression.validator_total_code_sim

#print axioms NearCompression.actual_validator_stake_code

#print axioms NearCompression.actual_validator_total_code

#print axioms NearCompression.actual_validator_stake_sim

#print axioms NearCompression.actual_validator_total_sim

#print axioms NearCompression.contract_code_body_sim

#print axioms NearCompression.contract_code_code_sim

#print axioms NearCompression.actual_contract_code_code

#print axioms NearCompression.actual_contract_code_sim

#print axioms NearCompression.resume_resolved_id_sim

#print axioms NearCompression.yield_id_resume_body_sim

#print axioms NearCompression.yield_id_resume_code_sim

#print axioms NearCompression.actual_yield_id_resume_code

#print axioms NearCompression.actual_yield_id_resume_sim

#print axioms NearCompression.real_gated_call_rejects

#print axioms NearCompression.real_gated_call_equiv

#print axioms NearCompression.listed_real_wrapper_equiv

#print axioms NearCompression.checked_real_call_func_equiv

#print axioms NearCompression.checked_real_direct_call_equiv

#print axioms NearCompression.pop_n_real

#print axioms NearCompression.set_frame_real

#print axioms NearCompression.checked_real_indirect_call_equiv

#print axioms NearCompression.checked_real_exec_equiv

#print axioms NearCompression.charge_cont_real

#print axioms NearCompression.result_equiv_bind_cont

#print axioms NearCompression.checked_real_step_equiv

#print axioms NearCompression.sync_keeps_backend

#print axioms NearCompression.charge_keeps_backend

#print axioms NearCompression.return_keeps_backend

#print axioms NearCompression.branch_keeps_backend

#print axioms NearCompression.result_bind_keeps_backend

#print axioms NearCompression.backend_invariant_cont

#print axioms NearCompression.enter_keeps_backend

#print axioms NearCompression.host_real_pure

#print axioms NearCompression.host_real_throw

#print axioms NearCompression.host_real_bind

#print axioms NearCompression.host_real_get_bind

#print axioms NearCompression.host_real_modify

#print axioms NearCompression.host_real_with_gas

#print axioms NearCompression.host_real_op

#print axioms NearCompression.host_real_put

#print axioms NearCompression.host_real_set

#print axioms NearCompression.host_real_get

#print axioms NearCompression.host_real_has

#print axioms NearCompression.call_host_keeps_real

#print axioms NearCompression.call_func_keeps_real

#print axioms NearCompression.host_real_for_in_list

#print axioms NearCompression.host_real_for_in

#print axioms NearCompression.host_real_pop_args

#print axioms NearCompression.host_real_push_ret

#print axioms NearCompression.host_real_charged_read

#print axioms NearCompression.host_real_read_mem

#print axioms NearCompression.host_real_register_body

#print axioms NearCompression.host_real_charged_register

#print axioms NearCompression.host_real_reg_set

#print axioms NearCompression.host_real_charged_return

#print axioms NearCompression.host_real_reg_get

#print axioms NearCompression.host_real_mem_or_reg

#print axioms NearCompression.for_in_preserves_real

#print axioms NearCompression.write_bytes_real

#print axioms NearCompression.host_real_charged_memory_write

#print axioms NearCompression.host_real_write_mem

#print axioms NearCompression.host_real_push_action

#print axioms NearCompression.host_real_push_promise

#print axioms NearCompression.host_real_promise_receipt

#print axioms NearCompression.host_real_then_data_ids

#print axioms NearCompression.host_real_deduct_balance

#print axioms NearCompression.host_real_action_deposit

#print axioms NearCompression.host_real_action_base

#print axioms NearCompression.host_real_action_byte

#print axioms NearCompression.host_real_new_receipt

#print axioms NearCompression.host_real_account_id_code

#print axioms NearCompression.host_real_read_account_id

#print axioms NearCompression.key_action_keeps_real

#print axioms NearCompression.actual_full_access_keeps_real

#print axioms NearCompression.actual_delete_key_keeps_real

#print axioms NearCompression.host_real_get_u128_code

#print axioms NearCompression.host_real_get_u128

#print axioms NearCompression.host_real_set_u128

#print axioms NearCompression.append_function_keeps_real

#print axioms NearCompression.function_action_keeps_real

#print axioms NearCompression.host_real_function_action

#print axioms NearCompression.actual_function_call_keeps_real

#print axioms NearCompression.actual_function_call_weight_keeps_real

#print axioms NearCompression.create_receipt_keeps_real

#print axioms NearCompression.dependent_receipt_keeps_real

#print axioms NearCompression.call_and_return_keeps_real

#print axioms NearCompression.promise_create_keeps_real

#print axioms NearCompression.actual_promise_create_keeps_real

#print axioms NearCompression.promise_then_keeps_real

#print axioms NearCompression.actual_promise_then_keeps_real

#print axioms NearCompression.batch_create_keeps_real

#print axioms NearCompression.actual_batch_create_keeps_real

#print axioms NearCompression.batch_then_keeps_real

#print axioms NearCompression.actual_batch_then_keeps_real

#print axioms NearCompression.deploy_action_code_keeps_real

#print axioms NearCompression.actual_deploy_action_keeps_real

#print axioms NearCompression.create_account_action_code_keeps_real

#print axioms NearCompression.actual_create_account_action_keeps_real

#print axioms NearCompression.stake_action_code_keeps_real

#print axioms NearCompression.actual_stake_action_keeps_real

#print axioms NearCompression.transfer_body_keeps_real

#print axioms NearCompression.transfer_code_keeps_real

#print axioms NearCompression.actual_transfer_keeps_real

#print axioms NearCompression.refund_body_keeps_real

#print axioms NearCompression.restricted_key_finish_keeps_real

#print axioms NearCompression.delete_account_body_keeps_real

#print axioms NearCompression.account_action_code_keeps_real

#print axioms NearCompression.actual_refund_keeps_real

#print axioms NearCompression.actual_delete_account_keeps_real

#print axioms NearCompression.restricted_key_body_keeps_real

#print axioms NearCompression.restricted_key_code_keeps_real

#print axioms NearCompression.actual_restricted_key_keeps_real

#print axioms NearCompression.promise_result_body_keeps_real

#print axioms NearCompression.promise_return_body_keeps_real

#print axioms NearCompression.promise_and_finish_keeps_real

#print axioms NearCompression.promise_result_code_keeps_real

#print axioms NearCompression.promise_return_code_keeps_real

#print axioms NearCompression.actual_promise_result_keeps_real

#print axioms NearCompression.actual_promise_return_keeps_real

#print axioms NearCompression.promise_and_code_keeps_real

#print axioms NearCompression.actual_promise_and_keeps_real

#print axioms NearCompression.context_register_body_keeps_real

#print axioms NearCompression.context_register_code_keeps_real

#print axioms NearCompression.actual_context_register_keeps_real

#print axioms NearCompression.context_nat_code_keeps_real

#print axioms NearCompression.actual_context_nat_keeps_real

#print axioms NearCompression.actual_context_host_keeps_real

#print axioms NearCompression.read_register_code_keeps_real

#print axioms NearCompression.write_register_code_keeps_real

#print axioms NearCompression.register_len_code_keeps_real

#print axioms NearCompression.actual_register_host_keeps_real

#print axioms NearCompression.host_real_hash_call_code

#print axioms NearCompression.actual_hash_call_keeps_real

#print axioms NearCompression.balance_host_code_keeps_real

#print axioms NearCompression.actual_balance_host_keeps_real

#print axioms NearCompression.listed_balance_host_keeps_real

#print axioms NearCompression.return_commit_keeps_real

#print axioms NearCompression.return_checked_commit_keeps_real

#print axioms NearCompression.return_finish_keeps_real

#print axioms NearCompression.value_return_code_keeps_real

#print axioms NearCompression.actual_value_return_keeps_real

#print axioms NearCompression.ed25519_code_keeps_real

#print axioms NearCompression.actual_ed25519_keeps_real

#print axioms NearCompression.validator_output_keeps_real

#print axioms NearCompression.validator_stake_code_keeps_real

#print axioms NearCompression.validator_total_code_keeps_real

#print axioms NearCompression.actual_validator_stake_keeps_real

#print axioms NearCompression.actual_validator_total_keeps_real

#print axioms NearCompression.contract_code_body_keeps_real

#print axioms NearCompression.contract_code_code_keeps_real

#print axioms NearCompression.actual_contract_code_keeps_real

#print axioms NearCompression.gas_dispatch_keeps_real

#print axioms NearCompression.actual_gas_keeps_real

#print axioms NearCompression.deprecated_dispatch_keeps_real

#print axioms NearCompression.actual_iterator_prefix_keeps_real

#print axioms NearCompression.actual_iterator_range_keeps_real

#print axioms NearCompression.actual_iterator_next_keeps_real

#print axioms NearCompression.yield_resume_body_keeps_real

#print axioms NearCompression.yield_resume_code_keeps_real

#print axioms NearCompression.actual_yield_resume_keeps_real

#print axioms NearCompression.host_real_set_state

#print axioms NearCompression.yield_receipt_then_keeps_real

#print axioms NearCompression.append_yield_action_keeps_real

#print axioms NearCompression.yield_id_receipt_then_keeps_real

#print axioms NearCompression.resume_resolved_id_keeps_real

#print axioms NearCompression.yield_id_resume_body_keeps_real

#print axioms NearCompression.yield_create_finish_keeps_real

#print axioms NearCompression.yield_create_code_keeps_real

#print axioms NearCompression.actual_yield_create_keeps_real

#print axioms NearCompression.yield_id_finish_keeps_real

#print axioms NearCompression.yield_id_code_keeps_real

#print axioms NearCompression.host_real_yield_id

#print axioms NearCompression.actual_yield_id_keeps_real

#print axioms NearCompression.yield_id_resume_code_keeps_real

#print axioms NearCompression.actual_yield_id_resume_keeps_real

#print axioms NearCompression.host_real_log_len_exceeded

#print axioms NearCompression.host_real_check_can_log

#print axioms NearCompression.host_real_append_log

#print axioms NearCompression.host_real_checked_append_log

#print axioms NearCompression.host_real_push_log

#print axioms NearCompression.host_real_guest_panic

#print axioms NearCompression.panic_code_keeps_real

#print axioms NearCompression.actual_panic_keeps_real

#print axioms NearCompression.utf16_buffer_keeps_real

#print axioms NearCompression.utf16_decoded_keeps_real

#print axioms NearCompression.utf16_length_checked_keeps_real

#print axioms NearCompression.utf16_finish_keeps_real

#print axioms NearCompression.utf16_code_keeps_real

#print axioms NearCompression.host_real_utf16

#print axioms NearCompression.decoded_log_code_keeps_real

#print axioms NearCompression.actual_log_utf16_keeps_real

#print axioms NearCompression.utf8_accumulate_keeps_real

#print axioms NearCompression.utf8_scan_step_keeps_real

#print axioms NearCompression.utf8_buffer_keeps_real

#print axioms NearCompression.utf8_finish_keeps_real

#print axioms NearCompression.utf8_code_keeps_real

#print axioms NearCompression.host_real_utf8

#print axioms NearCompression.actual_log_utf8_keeps_real

#print axioms NearCompression.decoded_panic_code_keeps_real

#print axioms NearCompression.actual_panic_utf8_keeps_real

#print axioms NearCompression.abort_finish_keeps_real

#print axioms NearCompression.abort_read_keeps_real

#print axioms NearCompression.abort_code_keeps_real

#print axioms NearCompression.actual_abort_keeps_real

#print axioms NearCompression.host_real_observe

#print axioms NearCompression.host_real_storage_usage

#print axioms NearCompression.host_real_record_removal

#print axioms NearCompression.host_real_read_result

#print axioms NearCompression.host_real_remove_result

#print axioms NearCompression.host_real_write_result

#print axioms NearCompression.host_real_has_key_finish

#print axioms NearCompression.host_real_read_finish

#print axioms NearCompression.host_real_remove_finish

#print axioms NearCompression.host_real_write_finish

#print axioms NearCompression.host_real_has_key_code

#print axioms NearCompression.actual_storage_has_key_keeps_real

#print axioms NearCompression.host_real_read_code

#print axioms NearCompression.actual_storage_read_keeps_real

#print axioms NearCompression.host_real_remove_code

#print axioms NearCompression.actual_storage_remove_keeps_real

#print axioms NearCompression.host_real_write_charged_finish

#print axioms NearCompression.host_real_write_value_code

#print axioms NearCompression.host_real_write_code

#print axioms NearCompression.actual_storage_write_keeps_real

#print axioms NearCompression.proved_host_keeps_real

#print axioms NearCompression.listed_real_wrapper_keeps_backend

#print axioms NearCompression.checked_real_call_func_keeps_backend

#print axioms NearCompression.result_keeps_backend_change_start

#print axioms NearCompression.checked_real_direct_call_keeps_backend

#print axioms NearCompression.checked_real_indirect_call_keeps_backend

#print axioms NearCompression.exec_num_keeps_real

#print axioms NearCompression.numeric_instruction_keeps_backend

#print axioms NearCompression.stack_control_instruction_keeps_backend

#print axioms NearCompression.memory_table_instruction_keeps_backend

#print axioms NearCompression.load_instruction_keeps_backend

#print axioms NearCompression.for_in_plain_real

#print axioms NearCompression.write_le_real

#print axioms NearCompression.mem_copy_keeps_backend

#print axioms NearCompression.mem_init_keeps_backend

#print axioms NearCompression.mem_fill_keeps_backend

#print axioms NearCompression.store_instruction_keeps_backend

#print axioms NearCompression.bulk_memory_instruction_keeps_backend

#print axioms NearCompression.table_init_keeps_backend

#print axioms NearCompression.bulk_table_instruction_keeps_backend

#print axioms NearCompression.table_init_instruction_keeps_backend

#print axioms NearCompression.checked_real_exec_keeps_backend

#print axioms NearCompression.result_keeps_backend_trans

#print axioms NearCompression.checked_real_step_keeps_backend

#print axioms NearCompression.checked_real_run_keeps_backend

#print axioms NearCompression.checked_real_run_equiv

#print axioms NearCompression.keeps_backend_has_real

#print axioms NearCompression.result_equiv_has_real

#print axioms NearCompression.checked_real_segment_keeps_backend

#print axioms NearCompression.checked_real_segment_equiv

#print axioms NearCompression.checked_real_fold_equiv

#print axioms NearCompression.checked_real_observational_chain

#print axioms NearCompression.checked_real_chain_or_hash_collision

#print axioms NearCompression.checked_real_run_or_hash_collision

#print axioms NearCompression.boundary_body_roundtrip

#print axioms NearCompression.boundary_envelope_roundtrip

#print axioms NearCompression.boundary_envelope_decode_encode

#print axioms NearCompression.boundary_envelope_injective

#print axioms NearCompression.boundary_envelope_rejects_suffix

#print axioms NearCompression.boundary_envelope_cont_fin_distinct

#print axioms NearCompression.value_wire_roundtrip

#print axioms NearCompression.stack_wire_roundtrip

#print axioms NearCompression.promise_wire_roundtrip

#print axioms NearCompression.value_wire_injective

#print axioms NearCompression.promise_wire_injective

#print axioms NearCompression.bool_wire_roundtrip

#print axioms NearCompression.label_wire_roundtrip

#print axioms NearCompression.frame_wire_roundtrip

#print axioms NearCompression.frames_wire_roundtrip

#print axioms NearCompression.frame_wire_injective

#print axioms NearCompression.gas_wire_roundtrip

#print axioms NearCompression.gas_wire_injective

#print axioms NearCompression.array_wire_roundtrip

#print axioms NearCompression.bytes_wire_roundtrip

#print axioms NearCompression.byte_arrays_wire_roundtrip

#print axioms NearCompression.ref_wire_roundtrip

#print axioms NearCompression.table_wire_roundtrip

#print axioms NearCompression.elements_wire_roundtrip

#print axioms NearCompression.register_wire_roundtrip

#print axioms NearCompression.registers_wire_roundtrip

#print axioms NearCompression.option_wire_roundtrip

#print axioms NearCompression.pair_wire_roundtrip

#print axioms NearCompression.optional_bytes_wire_roundtrip

#print axioms NearCompression.storage_entry_wire_roundtrip

#print axioms NearCompression.trie_wire_roundtrip

#print axioms NearCompression.write_entry_wire_roundtrip

#print axioms NearCompression.writes_wire_roundtrip

#print axioms NearCompression.deletion_empty_value_distinct

#print axioms NearCompression.writes_wire_injective

#print axioms NearCompression.map_wire_roundtrip

#print axioms NearCompression.map_wire_observed_roundtrip

#print axioms NearCompression.map_wire_alias_equiv

#print axioms NearCompression.overlay_wire_roundtrip

#print axioms NearCompression.unit_wire_roundtrip

#print axioms NearCompression.key_set_wire_roundtrip

#print axioms NearCompression.acct_wire_roundtrip

#print axioms NearCompression.acct_wire_observed_roundtrip

#print axioms NearCompression.recorder_wire_roundtrip

#print axioms NearCompression.recorder_wire_observed_roundtrip

#print axioms NearCompression.real_boundary_wire_roundtrip

#print axioms NearCompression.restore_normalized_real_boundary

#print axioms NearCompression.real_boundary_wire_observed_roundtrip

#print axioms NearCompression.real_boundary_wire_alias_equiv

#print axioms NearCompression.optional_real_boundary_wire_roundtrip

#print axioms NearCompression.string_utf8_roundtrip

#print axioms NearCompression.string_wire_roundtrip

#print axioms NearCompression.promise_result_wire_roundtrip

#print axioms NearCompression.promise_result_wire_injective

#print axioms NearCompression.nat128_wire_roundtrip

#print axioms NearCompression.validator_wire_roundtrip

#print axioms NearCompression.context_wire_roundtrip

#print axioms NearCompression.context_wire_injective

#print axioms NearCompression.state_init_wire_roundtrip

#print axioms NearCompression.action_wire_roundtrip

#print axioms NearCompression.actions_wire_roundtrip

#print axioms NearCompression.return_value_wire_roundtrip

#print axioms NearCompression.return_wire_roundtrip

#print axioms NearCompression.return_wire_injective

#print axioms NearCompression.state_boundary_wire_roundtrip

#print axioms NearCompression.restore_normalized_state_boundary

#print axioms NearCompression.state_boundary_wire_observed_roundtrip

#print axioms NearCompression.decode_complete_roundtrip

#print axioms NearCompression.result_payload_wire_roundtrip

#print axioms NearCompression.result_boundary_wire_roundtrip

#print axioms NearCompression.restore_normalized_result_boundary

#print axioms NearCompression.result_boundary_wire_observed_roundtrip

#print axioms NearCompression.result_boundary_wire_rejects_suffix

#print axioms NearCompression.execution_result_wire_observed_decodes

#print axioms NearCompression.execution_boundary_wire_observed_decodes

#print axioms NearCompression.encoded_real_run_or_hash_collision

#print axioms NearCompression.backed_wire_boundaries

#print axioms NearCompression.restored_result_backed

#print axioms NearCompression.restored_segment_starts_backed

#print axioms NearCompression.finite_start_wire_run_or_hash_collision

#print axioms NearCompression.memory_page_encoding_injective

#print axioms NearCompression.page_opening_or_collision

#print axioms NearCompression.page_opening_read_or_collision

#print axioms NearCompression.page_directory_write_other

#print axioms NearCompression.page_directory_write_target

#print axioms NearCompression.page_node_encoding_injective

#print axioms NearCompression.page_tree_opening_or_collision

#print axioms NearCompression.page_opening_message_count

#print axioms NearCompression.page_index_path_length

#print axioms NearCompression.built_page_tree_lookup

#print axioms NearCompression.memory_page_at_wf

#print axioms NearCompression.built_page_tree_wf

#print axioms NearCompression.indexed_page_opening_or_collision

#print axioms NearCompression.built_page_opening_directions

#print axioms NearCompression.built_page_opening_root

#print axioms NearCompression.memory_descriptor_payload_roundtrip

#print axioms NearCompression.memory_descriptor_encoding_injective

#print axioms NearCompression.memory_descriptor_binding_or_collision

#print axioms NearCompression.padded_root_allocation_ambiguity

#print axioms NearCompression.memory_descriptor_count_distinct

#print axioms NearCompression.committed_memory_read_or_collision

#print axioms NearCompression.check_memory_page_correct

#print axioms NearCompression.build_page_tree_congr

#print axioms NearCompression.build_page_tree_modify_outside

#print axioms NearCompression.memory_page_modify_target

#print axioms NearCompression.build_page_tree_modify_inside

#print axioms NearCompression.write_byte_page_tree

#print axioms NearCompression.built_opening_replacement_root

#print axioms NearCompression.write_byte_root_from_opening

#print axioms NearCompression.page_tree_update_or_collision

#print axioms NearCompression.untrusted_write_byte_root_or_collision

#print axioms NearCompression.committed_memory_write_or_collision

#print axioms NearCompression.bytes_wire_wf_set

#print axioms NearCompression.write_byte_pages_wf

#print axioms NearCompression.describe_memory_wf

#print axioms NearCompression.checked_memory_write_chain

#print axioms NearCompression.for_in_bytes_fold

#print axioms NearCompression.write_bytes_requests_exact

#print axioms NearCompression.execute_memory_witness_requests

#print axioms NearCompression.write_bytes_witness_exact

#print axioms NearCompression.checked_write_bytes_correct_or_collision

#print axioms NearCompression.page_array_modify_id

#print axioms NearCompression.page_array_modify_comp

#print axioms NearCompression.page_batch_execution_exact

#print axioms NearCompression.apply_page_writes_wf

#print axioms NearCompression.page_batch_tree

#print axioms NearCompression.checked_page_batch_correct_or_collision

#print axioms NearCompression.execute_byte_requests_pages_wf

#print axioms NearCompression.checked_page_batch_chain

#print axioms NearCompression.execute_page_batches_requests

#print axioms NearCompression.checked_batched_write_bytes_correct_or_collision

#print axioms NearCompression.bounded_extract_read

#print axioms NearCompression.subpage_region_bound

#print axioms NearCompression.subpage_size

#print axioms NearCompression.subpage_read

#print axioms NearCompression.wasm_read_subpage

#print axioms NearCompression.extract_write_inside

#print axioms NearCompression.extract_write_outside

#print axioms NearCompression.subpage_write

#print axioms NearCompression.wasm_write_subpage

#print axioms NearCompression.global_block_page_index

#print axioms NearCompression.global_block_local_index

#print axioms NearCompression.global_block_byte_offset

#print axioms NearCompression.global_subpage_lookup

#print axioms NearCompression.global_block_allocated

#print axioms NearCompression.subpage_directory_lookup

#print axioms NearCompression.wasm_read_global_subpage

#print axioms NearCompression.wasm_read_subpage_directory

#print axioms NearCompression.global_subpage_write_target

#print axioms NearCompression.subpage_directory_write_target

#print axioms NearCompression.global_subpage_write_other

#print axioms NearCompression.subpage_directory_write_other

#print axioms NearCompression.subpage_directory_write_exact

#print axioms NearCompression.zero_page_full

#print axioms NearCompression.allocated_pages_full

#print axioms NearCompression.grown_pages_full

#print axioms NearCompression.write_byte_full_pages

#print axioms NearCompression.execute_requests_full_pages

#print axioms NearCompression.write_bytes_full_pages

#print axioms NearCompression.full_pages_wire_wf

#print axioms NearCompression.for_in_full_pages

#print axioms NearCompression.write_le_full_pages

#print axioms NearCompression.mem_copy_full_pages

#print axioms NearCompression.mem_init_full_pages

#print axioms NearCompression.mem_fill_full_pages

#print axioms NearCompression.subpage_count_positive

#print axioms NearCompression.subpage_block_bound

#print axioms NearCompression.allocated_subpage_exists

#print axioms NearCompression.subpage_directory_entry_size

#print axioms NearCompression.subpage_directory_wire_wf

#print axioms NearCompression.block_hash_collision_lift

#print axioms NearCompression.subpage_committed_read_or_collision

#print axioms NearCompression.subpage_tree_write_exact

#print axioms NearCompression.subpage_committed_write_or_collision

#print axioms NearCompression.block_descriptor_payload_roundtrip

#print axioms NearCompression.block_descriptor_encoding_injective

#print axioms NearCompression.block_descriptor_binding_or_collision

#print axioms NearCompression.check_block_opening_correct

#print axioms NearCompression.authenticated_block_read_or_collision

#print axioms NearCompression.authenticated_block_write_or_collision

#print axioms NearCompression.checked_block_write_or_collision

#print axioms NearCompression.describe_subpage_memory_wf
#print axioms NearCompression.checked_block_write_chain

#print axioms NearCompression.check_write_witness_wf_correct
#print axioms NearCompression.checked_block_write_bytes_correct_or_collision
#print axioms NearCompression.check_block_write_bytes_rejects_wrong_requests

#print axioms NearCompression.block_batch_directory_exact
#print axioms NearCompression.block_batch_tree_exact

#print axioms NearCompression.subpage_batch_root_or_collision

#print axioms NearCompression.execute_byte_requests_page_count
#print axioms NearCompression.checked_block_batch_correct_or_collision

#print axioms NearCompression.checked_block_batch_chain

#print axioms NearCompression.execute_block_batches_requests

#print axioms NearCompression.checked_block_batched_write_bytes_correct_or_collision

#print axioms NearCompression.check_block_batched_bytes_rejects_wrong_requests

#print axioms NearCompression.built_page_opening_wf
#print axioms NearCompression.honest_block_batch_accepted

#print axioms NearCompression.honest_block_sequence_requests

#print axioms NearCompression.honest_block_sequence_accepted

#print axioms NearCompression.honest_block_batched_bytes_accepted

#print axioms NearCompression.prepend_block_request_exact

#print axioms NearCompression.grouped_block_requests_exact

#print axioms NearCompression.prepend_block_request_valid

#print axioms NearCompression.grouped_block_requests_valid

#print axioms NearCompression.honest_write_bytes_witness_accepted

#print axioms NearCompression.cached_page_root_exact

#print axioms NearCompression.cached_page_replace_exact

#print axioms NearCompression.cached_block_batch_update_exact

#print axioms NearCompression.cached_built_page_opening

#print axioms NearCompression.cached_page_at_exact
#print axioms NearCompression.cached_block_sequence_exact

#print axioms NearCompression.cached_block_sequence_accepted

#print axioms NearCompression.in_bounds_block_plan_valid

#print axioms NearCompression.cached_write_bytes_witness_exact

#print axioms NearCompression.cached_write_bytes_witness_accepted

#print axioms NearCompression.charged_memory_write_phases

#print axioms NearCompression.actual_memory_write_phases

#print axioms NearCompression.memory_write_host_full_pages

#print axioms NearCompression.memory_write_phases_full_pages

#print axioms NearCompression.byte_requests_preserve_gas

#print axioms NearCompression.write_bytes_preserve_gas

#print axioms NearCompression.checked_memory_host_phases

#print axioms NearCompression.checked_actual_memory_host

#print axioms NearCompression.instruction_add_limb_sound

#print axioms NearCompression.instruction_add_boolean_bound

#print axioms NearCompression.instruction_add32_equations

#print axioms NearCompression.instruction_add32_binop

#print axioms NearCompression.instruction_add32_exec_num

#print axioms NearCompression.instruction_add32_from_carries

#print axioms NearCompression.instruction_add32_witness_holds

#print axioms NearCompression.instruction_add32_witness_ranges

#print axioms NearCompression.instruction_add32_witness_inputs

#print axioms NearCompression.instruction_local_eval

#print axioms NearCompression.instruction_add32_trace_holds

#print axioms NearCompression.instruction_add32_trace_binop

#print axioms NearCompression.instruction_add32_table_wf

#print axioms NearCompression.instruction_bit_expr_bound

#print axioms NearCompression.instruction_add32_range_arithmetic

#print axioms NearCompression.instruction_add32_range_sound

#print axioms NearCompression.instruction_add32_range_binop

#print axioms NearCompression.instruction_add32_range_exec_num

#print axioms NearCompression.instruction_bit_expr_complete

#print axioms NearCompression.instruction_add32_range_witness_prefix

#print axioms NearCompression.instruction_add32_range_witness_bit

#print axioms NearCompression.instruction_add32_range_witness_holds

#print axioms NearCompression.instruction_bit_expr_local

#print axioms NearCompression.instruction_range_constraints_local

#print axioms NearCompression.instruction_range_trace_holds

#print axioms NearCompression.instruction_range_trace_binop

#print axioms NearCompression.instruction_add32_range_table_wf

#print axioms NearCompression.instruction_add32_range_table_size

#print axioms NearCompression.instruction_add32_pop_push

#print axioms NearCompression.instruction_add32_exec_stack

#print axioms NearCompression.instruction_add32_step_no_charge

#print axioms NearCompression.instruction_add32_charge_success

#print axioms NearCompression.instruction_add32_step_charge_abort

#print axioms NearCompression.instruction_add32_step_charge_unmodeled

#print axioms NearCompression.instruction_add32_pop_gas

#print axioms NearCompression.instruction_add32_step_charge_success

#print axioms NearCompression.instruction_add32_charge_overflow

#print axioms NearCompression.instruction_add32_charge_insufficient

#print axioms NearCompression.instruction_add32_exec

#print axioms NearCompression.instruction_control_range_sound

#print axioms NearCompression.instruction_control_small_sum

#print axioms NearCompression.instruction_control_addition_holds

#print axioms NearCompression.instruction_control_metadata_sound

#print axioms NearCompression.instruction_control_witness_metadata

#print axioms NearCompression.instruction_control_witness_bit

#print axioms NearCompression.instruction_control_nat_range

#print axioms NearCompression.instruction_control_prefix_eval

#print axioms NearCompression.instruction_control_base_column_bounds

#print axioms NearCompression.instruction_control_witness_metadata_holds

#print axioms NearCompression.instruction_control_witness_holds

#print axioms NearCompression.instruction_control_table_wf

#print axioms NearCompression.instruction_control_table_size

#print axioms NearCompression.instruction_control_constraints_local

#print axioms NearCompression.instruction_control_trace_holds

#print axioms NearCompression.instruction_control_bound_step

#print axioms NearCompression.instruction_sequence_eval_link

#print axioms NearCompression.instruction_sequence_eval_final

#print axioms NearCompression.instruction_sequence_eval_complete

#print axioms NearCompression.instruction_sequence_trace_link

#print axioms NearCompression.instruction_sequence_control_holds

#print axioms NearCompression.instruction_sequence_metadata_link

#print axioms NearCompression.instruction_sequence_metadata_progression

#print axioms NearCompression.instruction_sequence_table_wf

#print axioms NearCompression.instruction_sequence_table_size

#print axioms NearCompression.instruction_sequence_capacity

#print axioms NearCompression.instruction_operand_control_holds

#print axioms NearCompression.instruction_operand_right_link

#print axioms NearCompression.instruction_operand_row_binop

#print axioms NearCompression.instruction_operand_recurrence

#print axioms NearCompression.instruction_operand_accumulated_sum

#print axioms NearCompression.instruction_operand_table_wf

#print axioms NearCompression.instruction_operand_table_size

#print axioms NearCompression.instruction_stack_output_bound

#print axioms NearCompression.instruction_stack_pair_exact

#print axioms NearCompression.instruction_stack_value_wf_check

#print axioms NearCompression.instruction_stack_wf_check

#print axioms NearCompression.instruction_stack_encoding_injective

#print axioms NearCompression.instruction_stack_binding_or_collision

#print axioms NearCompression.instruction_stack_opening_correct

#print axioms NearCompression.instruction_stack_pair_committed

#print axioms NearCompression.instruction_stack_opening_complete

#print axioms NearCompression.instruction_stack_pair_height_bindings

#print axioms NearCompression.instruction_stack_pair_committed_heights

#print axioms NearCompression.instruction_add64_ranges

#print axioms NearCompression.instruction_add64_carry

#print axioms NearCompression.instruction_add64_equation

#print axioms NearCompression.instruction_add64_binop

#print axioms NearCompression.instruction_add64_exec_num

#print axioms NearCompression.instruction_add64_table_wf

#print axioms NearCompression.instruction_add64_table_size

#print axioms NearCompression.instruction_add64_carry_bound

#print axioms NearCompression.instruction_add64_nat_range

#print axioms NearCompression.instruction_add64_witness_prefix

#print axioms NearCompression.instruction_add64_witness_bit

#print axioms NearCompression.instruction_add64_nat_equation

#print axioms NearCompression.instruction_add64_witness_holds

#print axioms NearCompression.instruction_add64_witness_inputs

#print axioms NearCompression.sha512_add_air_sound

#print axioms NearCompression.sha512_round_addition_composition

#print axioms NearCompression.sha512_bt_mask64

#print axioms NearCompression.sha512_testBit_rotr

#print axioms NearCompression.sha512_bt_rotr

#print axioms NearCompression.sha512_bt_sig3

#print axioms NearCompression.sha512_bt_sigS

#print axioms NearCompression.sha512_bt_ch

#print axioms NearCompression.sha512_bt_maj

#print axioms NearCompression.sha512_rotr_lt

#print axioms NearCompression.sha512_sig3_lt

#print axioms NearCompression.sha512_sigS_lt

#print axioms NearCompression.sha512_ch_lt

#print axioms NearCompression.sha512_maj_lt

#print axioms NearCompression.sha512_xor_field

#print axioms NearCompression.sha512_choice_field

#print axioms NearCompression.sha512_majority_field

#print axioms NearCompression.sha512_bits_input_boolean

#print axioms NearCompression.sha512_bits_input_bound

#print axioms NearCompression.sha512_bits_input_bit

#print axioms NearCompression.sha512_xor3_expr_eval

#print axioms NearCompression.sha512_rot_expr_eval

#print axioms NearCompression.sha512_shift_expr_eval

#print axioms NearCompression.sha512_bits_expr_correct

#print axioms NearCompression.sha512_bits_function_bound

#print axioms NearCompression.sha512_bits_output_bit

#print axioms NearCompression.sha512_bits_output

#print axioms NearCompression.sha512_bits_witness_input_bit

#print axioms NearCompression.sha512_bits_witness_output_bit

#print axioms NearCompression.sha512_bits_witness_holds

#print axioms NearCompression.sha512_bits_table_wf

#print axioms NearCompression.sha512_bits_table_size

#print axioms NearCompression.sha512_bits_witness_input

#print axioms NearCompression.sha512_relocate_eval

#print axioms NearCompression.sha512_bit_expr_field

#print axioms NearCompression.sha512_word_bits_split

#print axioms NearCompression.sha512_bits_output_boolean

#print axioms NearCompression.sha512_bit_limb_binding

#print axioms NearCompression.sha512_bit_word_binding

#print axioms NearCompression.sha512_round_component_holds

#print axioms NearCompression.sha512_round_bits_holds

#print axioms NearCompression.sha512_round_add_holds

#print axioms NearCompression.sha512_round_wire_limb

#print axioms NearCompression.sha512_round_limb_word_wire

#print axioms NearCompression.sha512_round_bit_word_wire

#print axioms NearCompression.sha512_round_inputs

#print axioms NearCompression.sha512_round_sound

#print axioms NearCompression.sha512_round_full_output

#print axioms NearCompression.sha512_round_table_wf

#print axioms NearCompression.sha512_round_table_size

#print axioms NearCompression.sha512_bit_word_binding_reverse

#print axioms NearCompression.sha512_round_witness_bits_prefix

#print axioms NearCompression.sha512_round_witness_add_prefix

#print axioms NearCompression.sha512_round_component_bounds

#print axioms NearCompression.sha512_round_witness_bits_holds

#print axioms NearCompression.sha512_round_witness_add_holds

#print axioms NearCompression.sha512_round_witness_inputs_bound

#print axioms NearCompression.sha512_four_limb_unique

#print axioms NearCompression.sha512_round_witness_add_words

#print axioms NearCompression.sha512_round_witness_add_output

#print axioms NearCompression.sha512_round_witness_bits_input

#print axioms NearCompression.sha512_round_witness_bits_output

#print axioms NearCompression.sha512_round_witness_inputs

#print axioms NearCompression.sha512_round_witness_limb_link

#print axioms NearCompression.sha512_round_witness_bit_link

#print axioms NearCompression.sha512_round_witness_wires

#print axioms NearCompression.sha512_round_witness_holds

#print axioms NearCompression.sha512_current_expr_local

#print axioms NearCompression.sha512_round_constraints_current

#print axioms NearCompression.sha512_round_constraints_local

#print axioms NearCompression.sha512_round_trace_holds

#print axioms NearCompression.sha512_round_trace_sound

#print axioms NearCompression.sha512_round_trace_complete

#print axioms NearCompression.sha512_round_witness_trace_holds

#print axioms NearCompression.sha512_add_word_bits

#print axioms NearCompression.sha512_sequence_row_holds

#print axioms NearCompression.sha512_sequence_word_link

#print axioms NearCompression.sha512_sequence_table_wf

#print axioms NearCompression.sha512_sequence_table_size

#print axioms NearCompression.sha512_round_add_bits

#print axioms NearCompression.sha512_sequence_state_link

#print axioms NearCompression.sha512_sequence_round_recurrence

#print axioms NearCompression.sha512_sequence_final

#print axioms NearCompression.sha512_sequence_prefix

#print axioms NearCompression.sha512_sequence_terminal

#print axioms NearCompression.sha512_schedule_component_holds

#print axioms NearCompression.sha512_schedule_bits_holds

#print axioms NearCompression.sha512_schedule_add_holds

#print axioms NearCompression.sha512_schedule_wire_limb

#print axioms NearCompression.sha512_schedule_limb_word_wire

#print axioms NearCompression.sha512_schedule_bit_word_wire

#print axioms NearCompression.sha512_schedule_sound

#print axioms NearCompression.sha512_schedule_next_window

#print axioms NearCompression.sha512_schedule_table_wf

#print axioms NearCompression.sha512_schedule_table_size

#print axioms NearCompression.sha512_schedule_witness_bits_prefix

#print axioms NearCompression.sha512_schedule_witness_add_prefix

#print axioms NearCompression.sha512_schedule_witness_bits_holds

#print axioms NearCompression.sha512_schedule_witness_add_holds

#print axioms NearCompression.sha512_schedule_witness_inputs_bound

#print axioms NearCompression.sha512_schedule_witness_add_words

#print axioms NearCompression.sha512_schedule_witness_add_output

#print axioms NearCompression.sha512_schedule_witness_bits_input

#print axioms NearCompression.sha512_schedule_witness_bits_output

#print axioms NearCompression.sha512_schedule_witness_limb_link

#print axioms NearCompression.sha512_schedule_witness_bit_link

#print axioms NearCompression.sha512_schedule_witness_wires

#print axioms NearCompression.sha512_schedule_witness_inputs

#print axioms NearCompression.sha512_schedule_witness_holds

#print axioms NearCompression.sha512_schedule_constraints_current

#print axioms NearCompression.sha512_schedule_constraints_local

#print axioms NearCompression.sha512_schedule_trace_holds

#print axioms NearCompression.sha512_schedule_trace_sound

#print axioms NearCompression.sha512_schedule_trace_complete

#print axioms NearCompression.sha512_schedule_witness_trace_holds

#print axioms NearCompression.sha512_window_core_holds

#print axioms NearCompression.sha512_window_core_words

#print axioms NearCompression.sha512_window_word_link

#print axioms NearCompression.sha512_schedule_window_recurrence

#print axioms NearCompression.sha512_window_final

#print axioms NearCompression.sha512_window_table_wf

#print axioms NearCompression.sha512_window_table_size

#print axioms NearCompression.sha512_schedule_window_output

#print axioms NearCompression.sha512_window_prefix

#print axioms NearCompression.sha512_window_terminal

#print axioms NearCompression.sha512_combined_relocate_eval

#print axioms NearCompression.sha512_combined_project_holds

#print axioms NearCompression.sha512_relocate_zero

#print axioms NearCompression.sha512_combined_schedule_holds

#print axioms NearCompression.sha512_combined_round_holds

#print axioms NearCompression.sha512_combined_word_bits

#print axioms NearCompression.sha512_combined_message_binding

#print axioms NearCompression.sha512_combined_table_wf

#print axioms NearCompression.sha512_combined_table_size

#print axioms NearCompression.sha512_combined_output

#print axioms NearCompression.sha512_combined_recurrence

#print axioms NearCompression.sha512_combined_final

#print axioms NearCompression.sha512_combined_segment

#print axioms NearCompression.sha512_combined_terminal

#print axioms NearCompression.sha512_constants_first

#print axioms NearCompression.sha512_constants_step

#print axioms NearCompression.sha512_constants_phase

#print axioms NearCompression.sha512_constants_height

#print axioms NearCompression.sha512_constants_table_wf

#print axioms NearCompression.sha512_constants_table_size

#print axioms NearCompression.sha512_constants_sum_eval

#print axioms NearCompression.sha512_constants_key_limb

#print axioms NearCompression.sha512_constants_digits

#print axioms NearCompression.sha512_constants_key

#print axioms NearCompression.sha512_constants_combined_holds

#print axioms NearCompression.sha512_constants_keys

#print axioms NearCompression.sha512_constants_endpoint

#print axioms NearCompression.sha512_ff_constants_holds

#print axioms NearCompression.sha512_ff_add_local

#print axioms NearCompression.sha512_ff_add_holds

#print axioms NearCompression.sha512_ff_first_bit

#print axioms NearCompression.sha512_ff_constant_bit

#print axioms NearCompression.sha512_ff_result_bit

#print axioms NearCompression.sha512_ff_table_wf

#print axioms NearCompression.sha512_ff_table_size

#print axioms NearCompression.sha512_ff_input_words

#print axioms NearCompression.sha512_ff_output_words

#print axioms NearCompression.sha512_ff_round_holds

#print axioms NearCompression.sha512_ff_inputs

#print axioms NearCompression.sha512_ff_output

#print axioms NearCompression.sha512_ff_endpoint

#print axioms NearCompression.sha512_add_range_bit

#print axioms NearCompression.sha512_add_word_bit

#print axioms NearCompression.sha512_window_bit_boolean

#print axioms NearCompression.sha512_window_word_bound

#print axioms NearCompression.sha512_word_byte_split

#print axioms NearCompression.sha512_word_bytes_parse

#print axioms NearCompression.sha512_word_bytes_parse_many

#print axioms NearCompression.sha512_decoded_block_words

#print axioms NearCompression.sha512_decoded_block_length

#print axioms NearCompression.sha512_window_byte_bound

#print axioms NearCompression.sha512_word_bytes_bound

#print axioms NearCompression.sha512_compression_sound

#print axioms NearCompression.sha512_compression_bytes_bound

#print axioms NearCompression.sha512_vars_list_roundtrip

#print axioms NearCompression.sha512_compress_vars

#print axioms NearCompression.sha512_vars_feedforward_list

#print axioms NearCompression.sha512_nat_word_bytes_length

#print axioms NearCompression.sha512_nat_word_bytes_bound

#print axioms NearCompression.sha512_nat_word_bytes_bits

#print axioms NearCompression.sha512_public_ff_holds

#print axioms NearCompression.sha512_public_bitexpr_eval

#print axioms NearCompression.sha512_public_state_field

#print axioms NearCompression.sha512_public_message_field

#print axioms NearCompression.sha512_public_height

#print axioms NearCompression.sha512_public_output_field

#print axioms NearCompression.sha512_public_limb_decode

#print axioms NearCompression.sha512_public_word_decode

#print axioms NearCompression.sha512_public_state_bits

#print axioms NearCompression.sha512_public_message_bits

#print axioms NearCompression.sha512_public_state_word

#print axioms NearCompression.sha512_public_message_word

#print axioms NearCompression.sha512_public_output_word

#print axioms NearCompression.sha512_public_state_binding

#print axioms NearCompression.sha512_public_output_binding

#print axioms NearCompression.sha512_public_block_binding

#print axioms NearCompression.sha512_public_limb_ranges

#print axioms NearCompression.sha512_public_word_bound

#print axioms NearCompression.sha512_public_claim_canonical

#print axioms NearCompression.sha512_public_compression

#print axioms NearCompression.sha512_public_block_bytes

#print axioms NearCompression.sha512_public_table_wf

#print axioms NearCompression.sha512_public_table_size

#print axioms NearCompression.sha512_chain_check_iff

#print axioms NearCompression.sha512_chain_empty

#print axioms NearCompression.sha512_chain_input_length

#print axioms NearCompression.sha512_chain_input_bytes

#print axioms NearCompression.sha512_blocks_cons_exact

#print axioms NearCompression.sha512_chain_links_blocks

#print axioms NearCompression.sha512_chain_sound

#print axioms NearCompression.sha512_chain_consumed

#print axioms NearCompression.sha512_message_sound

#print axioms NearCompression.sha512_message_check_sound

#print axioms NearCompression.sha512_message_block_count

#print axioms NearCompression.sha512_window_next_valid

#print axioms NearCompression.sha512_window_run_valid

#print axioms NearCompression.sha512_window_getD_bound

#print axioms NearCompression.sha512_window_next_shift

#print axioms NearCompression.sha512_window_next_last

#print axioms NearCompression.sha512_window_witness_prefix

#print axioms NearCompression.sha512_window_witness_extra

#print axioms NearCompression.sha512_window_witness_core_bounds

#print axioms NearCompression.sha512_window_core_column_bound

#print axioms NearCompression.sha512_window_witness_core_holds

#print axioms NearCompression.sha512_window_witness_extra_boolean

#print axioms NearCompression.sha512_window_witness_holds

#print axioms NearCompression.sha512_window_witness_core_bits

#print axioms NearCompression.sha512_window_witness_core_word

#print axioms NearCompression.sha512_window_witness_core_inputs

#print axioms NearCompression.sha512_window_extra_layout

#print axioms NearCompression.sha512_window_extra_coverage

#print axioms NearCompression.sha512_window_witness_extra_word

#print axioms NearCompression.sha512_window_witness_word

#print axioms NearCompression.sha512_window_witness_decode

#print axioms NearCompression.sha512_window_witness_boolean

#print axioms NearCompression.sha512_word_bit_decode

#print axioms NearCompression.sha512_window_witness_bit

#print axioms NearCompression.sha512_window_witness_output

#print axioms NearCompression.sha512_window_witness_output_bit

#print axioms NearCompression.sha512_window_witness_next_bit

#print axioms NearCompression.sha512_window_constraints_current

#print axioms NearCompression.sha512_window_witness_trace_holds

#print axioms NearCompression.sha512_window_witness_trace_decode

#print axioms NearCompression.sha512_vars_round_valid

#print axioms NearCompression.sha512_vars_input_bounds

#print axioms NearCompression.sha512_combined_state_run_valid

#print axioms NearCompression.sha512_combined_run_input_bounds

#print axioms NearCompression.sha512_standard_keys_bound

#print axioms NearCompression.sha512_initial_state_valid

#print axioms NearCompression.sha512_round_state_boolean

#print axioms NearCompression.sha512_round_link_bits

#print axioms NearCompression.sha512_combined_witness_schedule_prefix

#print axioms NearCompression.sha512_combined_witness_round_prefix

#print axioms NearCompression.sha512_trace_prefix_eval

#print axioms NearCompression.sha512_combined_round_witness_holds

#print axioms NearCompression.sha512_combined_witness_component_bounds

#print axioms NearCompression.sha512_round_witness_message_bit

#print axioms NearCompression.sha512_combined_witness_message_bit

#print axioms NearCompression.sha512_combined_witness_trace_holds

#print axioms NearCompression.sha512_combined_standard_witness_holds

#print axioms NearCompression.sha512_combined_witness_inputs

#print axioms NearCompression.sha512_word_limb_nat

#print axioms NearCompression.sha512_word_limb_field

#print axioms NearCompression.sha512_word_limb_bound

#print axioms NearCompression.sha512_constants_witness_at

#print axioms NearCompression.sha512_constants_witness_prefix

#print axioms NearCompression.sha512_constants_witness_phase

#print axioms NearCompression.sha512_constants_witness_combined_bound

#print axioms NearCompression.sha512_constants_witness_first

#print axioms NearCompression.sha512_constants_witness_step

#print axioms NearCompression.sha512_constants_witness_last

#print axioms NearCompression.sha512_constants_witness_key_limb

#print axioms NearCompression.sha512_constants_witness_binding

#print axioms NearCompression.sha512_constants_witness_holds

#print axioms NearCompression.sha512_combined_inputs_prefix

#print axioms NearCompression.sha512_constants_witness_inputs

#print axioms NearCompression.sha512_constants_witness_endpoint

#print axioms NearCompression.instruction_layer_raise_eval
#print axioms NearCompression.instruction_layer_cast_eval
#print axioms NearCompression.instruction_layer_join_eval
#print axioms NearCompression.instruction_layer_gate_degree
#print axioms NearCompression.instruction_layer_compile_local
#print axioms NearCompression.instruction_layer_compile_eval
#print axioms NearCompression.instruction_layer_compile_trace_eval
#print axioms NearCompression.instruction_layer_gate_relation_degree
#print axioms NearCompression.instruction_layer_gate_relation_holds
#print axioms NearCompression.instruction_layer_add32_compiles
#print axioms NearCompression.instruction_layer_add32_holds_iff
#print axioms NearCompression.instruction_layer_add32_binop
#print axioms NearCompression.instruction_layer_add32_witness

#print axioms NearCompression.instruction_lerp_zero
#print axioms NearCompression.instruction_lerp_one
#print axioms NearCompression.instruction_cube_index_bound
#print axioms NearCompression.instruction_rows_mle_boolean
#print axioms NearCompression.instruction_folded_compile_eval
#print axioms NearCompression.instruction_constraint_batch_zero
#print axioms NearCompression.instruction_sumcheck_boolean_value
#print axioms NearCompression.instruction_sum_map_zero
#print axioms NearCompression.instruction_add_sumcheck_zero
#print axioms NearCompression.instruction_compiled_sumcheck_zero
#print axioms NearCompression.instruction_boolean_constraint_off_cube
#print axioms NearCompression.instruction_sumcheck_source_degree
#print axioms NearCompression.instruction_sumcheck_first_round_consistency
#print axioms NearCompression.instruction_sumcheck_first_round_zero

#print axioms NearCompression.instruction_public_limb_eq
#print axioms NearCompression.instruction_public_word_eq
#print axioms NearCompression.instruction_public_add_binop
#print axioms NearCompression.instruction_public_mle_eq
#print axioms NearCompression.instruction_public_binding_zero
#print axioms NearCompression.instruction_public_sumcheck_zero

#print axioms NearCompression.air_polynomial_lower_eval
#print axioms NearCompression.air_polynomial_lower_degree
#print axioms NearCompression.air_polynomial_lower_trace_eval
#print axioms NearCompression.air_polynomial_lower_trace_zero
#print axioms NearCompression.air_polynomial_output_gate
#print axioms NearCompression.air_polynomial_honest_output_gate
#print axioms NearCompression.air_polynomial_row_env
#print axioms NearCompression.air_polynomial_row_eval
#print axioms NearCompression.air_polynomial_row_affine

#print axioms NearCompression.instruction_round_difference_nonzero
#print axioms NearCompression.instruction_round_bad_roots_degree
#print axioms NearCompression.instruction_round_bad_roots

#print axioms NearCompression.air_sumcheck_weighted_degree
#print axioms NearCompression.air_sumcheck_weighted_bad_roots

#print axioms NearCompression.generic_row_bit_index_bound
#print axioms NearCompression.generic_row_mle_boolean
#print axioms NearCompression.generic_row_mle_congr
#print axioms NearCompression.generic_row_mle_zero
#print axioms NearCompression.generic_row_mle_add
#print axioms NearCompression.generic_row_mle_scale
#print axioms NearCompression.generic_row_next_mle_boolean
#print axioms NearCompression.generic_row_next_mle_air
#print axioms NearCompression.generic_row_next_mle_nonfinal
#print axioms NearCompression.generic_row_next_mle_final

#print axioms NearCompression.shift_kernel_dp_linear_sum
#print axioms NearCompression.shift_kernel_dp_boolean_sum
#print axioms NearCompression.shift_weighted_cube_sum_scale
#print axioms NearCompression.shift_kernel_sum_weighted
#print axioms NearCompression.shift_kernel_dp_weighted
#print axioms NearCompression.shift_kernel_sum_boolean
#print axioms NearCompression.shift_kernel_dp_boolean

#print axioms NearCompression.shift_list_bit_index_bound
#print axioms NearCompression.shift_subtract_bits_length
#print axioms NearCompression.shift_subtract_false
#print axioms NearCompression.shift_subtract_index_carry
#print axioms NearCompression.shift_subtract_index_mod
#print axioms NearCompression.shift_subtract_successor_mod
#print axioms NearCompression.shift_list_generic_index
#print axioms NearCompression.shift_subtract_generic_index
#print axioms NearCompression.shift_predecessor_next_mle

#print axioms NearCompression.generic_air_weighted_lower_degree
#print axioms NearCompression.generic_air_constraint_polynomial_eval
#print axioms NearCompression.generic_air_constraint_polynomial_degree
#print axioms NearCompression.generic_air_round_polynomial_eval
#print axioms NearCompression.generic_air_round_polynomial_degree
#print axioms NearCompression.generic_air_round_bad_roots

#print axioms NearCompression.generic_coordinate_mle
#print axioms NearCompression.generic_coordinate_next_mle
#print axioms NearCompression.generic_coordinate_reconstruct_four
#print axioms NearCompression.generic_coordinate_four_mle
#print axioms NearCompression.generic_coordinate_four_next_mle

#print axioms NearCompression.generic_bus_prod_append_single
#print axioms NearCompression.generic_bus_prefix_zero
#print axioms NearCompression.generic_bus_prefix_succ
#print axioms NearCompression.generic_bus_accumulator_prefix
#print axioms NearCompression.generic_bus_accumulator_product
#print axioms NearCompression.generic_bus_accumulator_complete
#print axioms NearCompression.generic_bus_accumulator_of_gates
#print axioms NearCompression.generic_bus_product_of_gates

#print axioms NearCompression.generic_bus_selected_factor_eval
#print axioms NearCompression.generic_bus_first_residual_eval
#print axioms NearCompression.generic_bus_accumulator_gate_eval
#print axioms NearCompression.generic_bus_selected_factor_degree
#print axioms NearCompression.generic_bus_first_residual_degree
#print axioms NearCompression.generic_bus_accumulator_gate_degree

#print axioms NearCompression.monomial_split_lengths
#print axioms NearCompression.monomial_polynomial_split
#print axioms NearCompression.generic_monomial_curve_power
#print axioms NearCompression.generic_monomial_tensor_curve
#print axioms NearCompression.generic_monomial_tensor_power_curve

#print axioms NearCompression.generic_mle_fold_one
#print axioms NearCompression.generic_mle_fold_prefix
#print axioms NearCompression.generic_mle_fold_complete
#print axioms NearCompression.generic_mle_fold_affine

#print axioms NearCompression.generic_zero_traffic_row_expand
#print axioms NearCompression.generic_zero_traffic_padding_expand
#print axioms NearCompression.generic_traffic_expand_append
#print axioms NearCompression.generic_traffic_append_zero_padding
#print axioms NearCompression.generic_traffic_two_padding_expansions
#print axioms NearCompression.generic_traffic_row_count_expand
#print axioms NearCompression.generic_traffic_count_fold
#print axioms NearCompression.generic_traffic_two_padding_counts
#print axioms NearCompression.generic_air_row_count_acc
#print axioms NearCompression.generic_air_table_count
#print axioms NearCompression.generic_air_table_count_padding_invariant

#print axioms NearCompression.generic_padding_local
#print axioms NearCompression.generic_padding_empty_local
#print axioms NearCompression.generic_padding_row_env
#print axioms NearCompression.generic_padding_expr_zero
#print axioms NearCompression.generic_padding_empty_expr_zero

#print axioms NearCompression.generic_bus_count_go_congr
#print axioms NearCompression.generic_bus_count_congr
#print axioms NearCompression.generic_padding_holds_transfer
#print axioms NearCompression.generic_padding_holds_of_decompositions

#print axioms NearCompression.generic_padding_shrink_local
#print axioms NearCompression.generic_padding_expr_shrink
#print axioms NearCompression.generic_cmp_padding_cells
#print axioms NearCompression.generic_cmp_aligned_padding_cells
#print axioms NearCompression.generic_cmp_aligned_padding_eval
#print axioms NearCompression.generic_cmp_padding_constraints
#print axioms NearCompression.generic_cmp_padding_bits
#print axioms NearCompression.generic_cmp_padding_local
#print axioms NearCompression.generic_cmp_interaction_values
#print axioms NearCompression.generic_cmp_row_count
#print axioms NearCompression.generic_cmp_count
#print axioms NearCompression.generic_cmp_padding_traffic
#print axioms NearCompression.merkle_old_cells
#print axioms NearCompression.padding_expr_property_shrink
#print axioms NearCompression.merkle_shrink_local
#print axioms NearCompression.merkle_current_cells
#print axioms NearCompression.merkle_interaction_values
#print axioms NearCompression.merkle_padding_mult_zero
#print axioms NearCompression.merkle_row_count_eq
#print axioms NearCompression.merkle_shrink_bus_count
#print axioms NearCompression.merkle_shrink_honest_bus_count
#print axioms NearCompression.whir_cube_congr
#print axioms NearCompression.whir_cube_scale
#print axioms NearCompression.whir_cube_add
#print axioms NearCompression.whir_tensor_reproducing
#print axioms NearCompression.whir_tensor_linear
#print axioms NearCompression.whir_tensor_fold
#print axioms NearCompression.whir_power_length
#print axioms NearCompression.whir_power_kernel
#print axioms NearCompression.whir_power_kernel_append
#print axioms NearCompression.whir_injected_terminal
#print axioms NearCompression.whir_cube_zero
#print axioms NearCompression.whir_injected_terminal_list
#print axioms NearCompression.whir_kernel_append
#print axioms NearCompression.whir_original_terminal
#print axioms NearCompression.whir_terminal_weight_identity
#print axioms NearCompression.whir_scheduled_weight_split
#print axioms NearCompression.whir_scheduled_terminal_identity
#print axioms NearCompression.whir_honest_quadratic_eval
#print axioms NearCompression.whir_honest_quadratic_endpoints
#print axioms NearCompression.whir_accumulate_queries
#print axioms NearCompression.whir_stage_update
#print axioms NearCompression.whir_run_arithmetic_ledger
#print axioms NearCompression.whir_honest_fold_step
#print axioms NearCompression.whir_honest_weight_injection
#print axioms NearCompression.whir_accepted_terminal_recurrence
#print axioms NearCompression.whir_scheduled_accepted_recurrence
#print axioms NearCompression.rejection_preimages
#print axioms NearCompression.rejection_preimages_distinct
#print axioms NearCompression.rejection_preimages_word_bound
#print axioms NearCompression.rejection_preimages_mem
#print axioms NearCompression.rejection_preimages_nodup
#print axioms NearCompression.rejection_preimages_card
#print axioms NearCompression.rejection_equal_preimage_counts
#print axioms NearCompression.rejection_prime32
#print axioms NearCompression.rejection_word_preimages_perm
#print axioms NearCompression.rejection_word_preimages_card
#print axioms NearCompression.rejection_prime32_card
#print axioms NearCompression.rejection_word_equal_counts
#print axioms NearCompression.prepared_gas_word_bound
#print axioms NearCompression.prepared_gas_nat_total
#print axioms NearCompression.prepared_gas_nat_borrow
#print axioms NearCompression.prepared_gas_bits_horner
#print axioms NearCompression.prepared_gas_boolean
#print axioms NearCompression.prepared_gas_limb_bound
#print axioms NearCompression.prepared_gas_limb_equation
#print axioms NearCompression.prepared_gas_borrow_sound
#print axioms NearCompression.prepared_expr_sum_eval
#print axioms NearCompression.prepared_sum_nat_bound
#print axioms NearCompression.prepared_nat_sum_zero
#print axioms NearCompression.prepared_nat_sum_one
#print axioms NearCompression.prepared_onehot
#print axioms NearCompression.prepared_row_boolean
#print axioms NearCompression.prepared_row_pc_sp
#print axioms NearCompression.prepared_sum_zero
#print axioms NearCompression.prepared_sum_select
#print axioms NearCompression.prepared_fetch_selected
#print axioms NearCompression.prepared_stack_limb_eval
#print axioms NearCompression.prepared_operand_selected
#print axioms NearCompression.prepared_stack_limb_bound
#print axioms NearCompression.prepared_row_fetch_and_operands
#print axioms NearCompression.prepared_balanced16_eval
#print axioms NearCompression.prepared_fetch_python_eval
#print axioms NearCompression.prepared_python_choices
#print axioms NearCompression.prepared_active_add_depth
#print axioms NearCompression.prepared_fetch_fee_bounds
#print axioms NearCompression.prepared_opcode_selected
#print axioms NearCompression.rs_pair_decode_encode
#print axioms NearCompression.rs_pair_encode_decode
#print axioms NearCompression.rs_polynomial_pair_encode
#print axioms NearCompression.rs_polynomial_pair_decode
#print axioms NearCompression.rs_tensor_pair_decode
#print axioms NearCompression.rs_pair_encode_injective
#print axioms NearCompression.rs_pair_fold_tensor
#print axioms NearCompression.prepared_gas_fetch_source
#print axioms NearCompression.prepared_gas_subtract_source
#print axioms NearCompression.prepared_gas_extract_source
#print axioms NearCompression.prepared_gas_public_fee_bounds
#print axioms NearCompression.prepared_gas_public_sound
#print axioms NearCompression.prepared_gas_row_env
#print axioms NearCompression.prepared_gas_table_local
#print axioms NearCompression.prepared_bits_row_horner
#print axioms NearCompression.prepared_operand_python_eval
#print axioms NearCompression.prepared_operand_python_selected
#print axioms NearCompression.prepared_add_pair_binop
#print axioms NearCompression.prepared_active_add_binop
#print axioms NearCompression.generic_row_mle_split_axes
#print axioms NearCompression.generic_packed_values_index
#print axioms NearCompression.generic_packed_mle_identity
#print axioms NearCompression.generic_padded_column_mle_zero
#print axioms NearCompression.scalar_rs_domain_unique
#print axioms NearCompression.scalar_rs_terminal_unique
#print axioms NearCompression.scalar_rs_residual_congr
#print axioms NearCompression.scalar_rs_residual_add
#print axioms NearCompression.scalar_rs_residual_scale
#print axioms NearCompression.scalar_rs_terminal_claim
#print axioms NearCompression.scalar_rs_word_checks_complete
#print axioms NearCompression.scalar_rs_word_terminal_claim
#print axioms NearCompression.prepared_transition_bits_horner
#print axioms NearCompression.prepared_sp_index_selected
#print axioms NearCompression.prepared_success_advance
#print axioms NearCompression.prepared_add_pc_next
#print axioms NearCompression.prepared_add_sp_next
#print axioms NearCompression.prepared_add_stack_limb_next
#print axioms NearCompression.prepared_stack_word_limbs
#print axioms NearCompression.prepared_add_result_limbs
#print axioms NearCompression.prepared_add_stack_word_next
#print axioms NearCompression.prepared_add_transition_sound
#print axioms NearCompression.prepared_add_transition_source_extract
#print axioms NearCompression.packed_claim_lane_bits
#print axioms NearCompression.packed_claim_restriction_eval
#print axioms NearCompression.packed_claim_restriction_degree
#print axioms NearCompression.packed_claim_interpolants_differ
#print axioms NearCompression.packed_claim_valid_lane_nonzero
#print axioms NearCompression.packed_claim_restriction_nonzero
#print axioms NearCompression.packed_claim_line_bad_roots
#print axioms NearCompression.packed_grid_length
#print axioms NearCompression.packed_grid_budget_closed
#print axioms NearCompression.packed_grid_eval_cons
#print axioms NearCompression.packed_grid_zero_bound
#print axioms NearCompression.packed_grid_zero_bound_closed
#print axioms NearCompression.packed_grid_eval_sub
#print axioms NearCompression.packed_claim_grid_bad_count
#print axioms NearCompression.packed_claim_grid_probability_count
#print axioms NearCompression.reconstructed_rs_collision_or_correct
#print axioms NearCompression.reconstructed_rs_binding_correct
#print axioms NearCompression.reconstructed_rs_pair_semantics
#print axioms NearCompression.reconstructed_rs_representation_unique
#print axioms NearCompression.prepared_no_first_eval
#print axioms NearCompression.prepared_table_nonlast_eval
#print axioms NearCompression.prepared_choices_recontext
#print axioms NearCompression.prepared_table_row_choices
#print axioms NearCompression.prepared_transition_no_first
#print axioms NearCompression.prepared_transition_source_member
#print axioms NearCompression.prepared_table_add_transitions
#print axioms NearCompression.prepared_next_gas_success
#print axioms NearCompression.prepared_success_flags
#print axioms NearCompression.prepared_table_local_add
#print axioms NearCompression.packed_row_mle_point_congr
#print axioms NearCompression.packed_opening_point_identity
#print axioms NearCompression.packed_source_claim_valid
#print axioms NearCompression.packed_source_claim_padding
#print axioms NearCompression.packed_opening_bad_count
#print axioms NearCompression.packed_opening_original_lane_bad_count
#print axioms NearCompression.packed_opening_zero_pack_rejects
#print axioms NearCompression.prepared_terminal_flags_local
#print axioms NearCompression.prepared_terminal_flags_table
#print axioms NearCompression.prepared_gas_updates_table
#print axioms NearCompression.prepared_gas_failure_freeze
#print axioms NearCompression.prepared_table_exhaustion
#print axioms NearCompression.prepared_quiet_projection
#print axioms NearCompression.prepared_table_exhaustion_projection
#print axioms NearCompression.prepared_table_end
#print axioms NearCompression.one_fold_quadratic_eval
#print axioms NearCompression.one_fold_quadratic_endpoints
#print axioms NearCompression.one_fold_honest_round
#print axioms NearCompression.one_fold_polynomial
#print axioms NearCompression.one_fold_scalar_pair
#print axioms NearCompression.one_fold_source_residual
#print axioms NearCompression.one_fold_shapes
#print axioms NearCompression.one_fold_terminal_residual
#print axioms NearCompression.one_fold_honest_terminal
#print axioms NearCompression.prepared_stack_pointer_next
#print axioms NearCompression.prepared_stack_case_limb_next
#print axioms NearCompression.prepared_stack_case_word_next
#print axioms NearCompression.prepared_stack_case_projection
#print axioms NearCompression.prepared_table_const_drop
#print axioms NearCompression.affine_fold_parameter_exclusion
#print axioms NearCompression.affine_fold_inverse_exclusion
#print axioms NearCompression.affine_fold_inverse_forward
#print axioms NearCompression.affine_fold_forward_inverse
#print axioms NearCompression.affine_fold_parameter_injective
#print axioms NearCompression.affine_fold_subtype_left_inverse
#print axioms NearCompression.affine_fold_subtype_right_inverse
#print axioms NearCompression.affine_fold_monomial_scale
#print axioms NearCompression.affine_fold_scaled_equality
#print axioms NearCompression.affine_fold_exceptional
#print axioms NearCompression.affine_fold_sample_exclusion
#print axioms NearCompression.affine_fold_sample_nodup
#print axioms NearCompression.affine_fold_bad_count_transport
#print axioms NearCompression.affine_fold_equality_count_transport
#print axioms NearCompression.affine_fold_shape
#print axioms NearCompression.affine_fold_quadratic_eval
#print axioms NearCompression.affine_fold_quadratic_endpoints
#print axioms NearCompression.affine_fold_next_shape
#print axioms NearCompression.repeated_affine_honest
#print axioms NearCompression.affine_fold_round_challenges
#print axioms NearCompression.affine_fold_terminal_dot
#print axioms NearCompression.repeated_affine_ledger
#print axioms NearCompression.repeated_affine_terminal
#print axioms NearCompression.affine_fold_coordinates
#print axioms NearCompression.lane_power_batch_polynomial
#print axioms NearCompression.lane_polynomial_batch_eval
#print axioms NearCompression.lane_polynomial_batch_coeff
#print axioms NearCompression.lane_tensor_monomial
#print axioms NearCompression.lane_polynomial_batch_tensor
#print axioms NearCompression.lane_batch_affine_fold
#print axioms NearCompression.lane_batch_decoded_pair_fold
#print axioms NearCompression.lane_claim_batch_bad_count
#print axioms NearCompression.lane_claim_batch_bad_count_le
#print axioms NearCompression.prepared_wasm_stack_congr
#print axioms NearCompression.prepared_wasm_step_charge
#print axioms NearCompression.prepared_wasm_stack_projection
#print axioms NearCompression.prepared_wasm_const_drop
#print axioms NearCompression.prepared_table_wasm_const_drop
#print axioms NearCompression.prepared_wasm_stack_word_bound
#print axioms NearCompression.prepared_wasm_exec_add
#print axioms NearCompression.prepared_wasm_add
#print axioms NearCompression.prepared_table_wasm_add
#print axioms NearCompression.compact_weight_accumulator
#print axioms NearCompression.compact_tensor_weights_append
#print axioms NearCompression.compact_tensor_weights_length
#print axioms NearCompression.affine_fold_values_scale
#print axioms NearCompression.compact_tensor_one_fold
#print axioms NearCompression.affine_fold_values_final_scale
#print axioms NearCompression.compact_affine_weights
#print axioms NearCompression.affine_fold_final_weights
#print axioms NearCompression.compact_affine_final_state_weights
#print axioms NearCompression.compact_affine_weights_length
#print axioms NearCompression.prepared_wasm_sync
#print axioms NearCompression.prepared_wasm_gas_context_charge
#print axioms NearCompression.prepared_wasm_exhaustion
#print axioms NearCompression.prepared_wasm_end
#print axioms NearCompression.prepared_wasm_end_sync
#print axioms NearCompression.prepared_wasm_failure_burn
#print axioms NearCompression.prepared_wasm_exhaustion_trap
#print axioms NearCompression.prepared_wasm_failure_sync
#print axioms NearCompression.prepared_table_wasm_end
#print axioms NearCompression.prepared_table_wasm_exhaustion
#print axioms NearCompression.prepared_wasm_continue
#print axioms NearCompression.prepared_wasm_continue_gas
#print axioms NearCompression.prepared_wasm_end_certificate
#print axioms NearCompression.prepared_wasm_exhausted_certificate
#print axioms NearCompression.prepared_wasm_execution_run
#print axioms NearCompression.prepared_wasm_execution_call_entry
#print axioms NearCompression.basefold_auxiliary_row_mle
#print axioms NearCompression.basefold_tensor_lane_tensor
#print axioms NearCompression.basefold_weight_zero
#print axioms NearCompression.basefold_weight_one
#print axioms NearCompression.basefold_coefficient_inner_product
#print axioms NearCompression.basefold_coefficient_inner_product_monomial
#print axioms NearCompression.basefold_coefficient_boolean_value
#print axioms NearCompression.basefold_auxiliary_affine_fold
#print axioms NearCompression.basefold_weight_affine_restriction
#print axioms NearCompression.prepared_inspect_instruction
#print axioms NearCompression.prepared_inspect_fee
#print axioms NearCompression.prepared_code_entry_checked
#print axioms NearCompression.prepared_code_public_checked
#print axioms NearCompression.prepared_code_digit_nat
#print axioms NearCompression.prepared_code_digits64
#print axioms NearCompression.prepared_code_digits32
#print axioms NearCompression.prepared_code_selected_fee
#print axioms NearCompression.prepared_code_field_bound
#print axioms NearCompression.prepared_code_public_limb_bounds
#print axioms NearCompression.prepared_code_public_build_checked
#print axioms NearCompression.prepared_wasm_enter
#print axioms NearCompression.prepared_wasm_entry_gas
#print axioms NearCompression.prepared_wasm_checked_call_entry
#print axioms NearCompression.global_chain_pow_mod
#print axioms NearCompression.global_chain_projection
#print axioms NearCompression.global_chain_pair_indices
#print axioms NearCompression.global_chain_next_pair_side
#print axioms NearCompression.global_chain_source_square
#print axioms NearCompression.global_chain_decode_fold
#print axioms NearCompression.global_chain_next_pair_evaluation
#print axioms NearCompression.global_chain_pair_check_iff
#print axioms NearCompression.prepared_code_terminated_shape
#print axioms NearCompression.prepared_code_live_successor
#print axioms NearCompression.prepared_code_selected_successor
#print axioms NearCompression.virtual_wide_pair_shape
#print axioms NearCompression.virtual_combined_pair_exact
#print axioms NearCompression.virtual_first_fold_exact
#print axioms NearCompression.virtual_wide_checks_sound
#print axioms NearCompression.virtual_wide_checks_complete
#print axioms NearCompression.virtual_wide_oracle_checks_iff
#print axioms NearCompression.virtual_explicit_batch_oracle_iff
#print axioms NearCompression.virtual_first_chain_embedding
#print axioms NearCompression.prepared_last_done
#print axioms NearCompression.prepared_public_classification
#print axioms NearCompression.prepared_wasm_continue_row
#print axioms NearCompression.prepared_wasm_construct_execution
#print axioms NearCompression.prepared_first_value
#print axioms NearCompression.prepared_wasm_initial_state
#print axioms NearCompression.prepared_wasm_air_call_entry
#print axioms NearCompression.finite_candidate_union_count
#print axioms NearCompression.finite_candidate_claim_cancellation
#print axioms NearCompression.finite_polynomial_candidate_cancellation
#print axioms NearCompression.prepared_public_boundary_record
#print axioms NearCompression.prepared_boundary_public_messages
#print axioms NearCompression.prepared_boundary_no_table_receives
#print axioms NearCompression.prepared_boundary_message_bound
#print axioms NearCompression.prepared_boundary_gas_field
#print axioms NearCompression.prepared_public_gas_field
#print axioms NearCompression.prepared_boundary_gas_bound
#print axioms NearCompression.prepared_boundary_status_bound
#print axioms NearCompression.prepared_boundary_initial_gas
#print axioms NearCompression.prepared_done_padding_step
#print axioms NearCompression.prepared_snapshot_eq_trans
#print axioms NearCompression.prepared_done_padding_suffix
#print axioms NearCompression.finite_rs_agreement_partition
#print axioms NearCompression.finite_rs_mismatch_symm
#print axioms NearCompression.finite_rs_mismatch_triangle
#print axioms NearCompression.finite_rs_distinct_agreement
#print axioms NearCompression.finite_rs_minimum_distance
#print axioms NearCompression.finite_rs_minimum_distance_sub
#print axioms NearCompression.finite_rs_unique_candidate
#print axioms NearCompression.finite_rs_unique_radius
#print axioms NearCompression.lane_polynomial_batch_degree
#print axioms NearCompression.lane_polynomial_batch_residual
#print axioms NearCompression.virtual_batch_joint_distance
#print axioms NearCompression.unique_virtual_batch_candidate
#print axioms NearCompression.unique_virtual_batch_bad_count
#print axioms NearCompression.prepared_final_row_padding
#print axioms NearCompression.prepared_end_final_row
#print axioms NearCompression.prepared_failure_gas_fast
#print axioms NearCompression.prepared_exhausted_final_row
#print axioms NearCompression.prepared_execution_final_row
#print axioms NearCompression.prepared_execution_last_row
#print axioms NearCompression.prepared_boundary_sp_field
#print axioms NearCompression.prepared_boundary_stack_field
#print axioms NearCompression.prepared_public_stack_field
#print axioms NearCompression.prepared_boundary_stack_word
#print axioms NearCompression.prepared_public_stack_decode
#print axioms NearCompression.prepared_final_row_published
#print axioms NearCompression.prepared_boundary_local
#print axioms NearCompression.prepared_wasm_public_call_entry
#print axioms NearCompression.two_lane_reconstruction_point
#print axioms NearCompression.two_lane_reconstruction_degree
#print axioms NearCompression.two_lane_reconstruction_residual
#print axioms NearCompression.two_lane_reconstruction_distance
#print axioms NearCompression.two_lane_candidates_reconstruct
#print axioms NearCompression.two_lane_far_bad_count
#print axioms NearCompression.affine_reconstruction_degree
#print axioms NearCompression.affine_reconstruction_source_pair
#print axioms NearCompression.affine_reconstruction_pair_errors
#print axioms NearCompression.affine_weighted_residual_quadratic
#print axioms NearCompression.affine_weighted_residual_endpoints
#print axioms NearCompression.affine_weighted_residual_actual
#print axioms NearCompression.full_domain_errors_le_twice_pair_errors
#print axioms NearCompression.two_weighted_challenges_insufficient
#print axioms NearCompression.consistency_mass_mono
#print axioms NearCompression.consistency_gated_agreement
#print axioms NearCompression.consistency_projected_mass
#print axioms NearCompression.consistency_pair_pullback
#print axioms NearCompression.consistency_projected_bound
#print axioms NearCompression.prepared_run_call_path
#print axioms NearCompression.prepared_run_call_setup_core_provenance
#print axioms NearCompression.prepared_run_call_setup_sound
#print axioms NearCompression.prepared_run_call_checked
#print axioms NearCompression.prepared_wasm_public_run_call
#print axioms NearCompression.global_chain_fiber_split
#print axioms NearCompression.global_chain_weight_exact
#print axioms NearCompression.global_chain_total_mass
#print axioms NearCompression.global_rs_chain_query_count
#print axioms NearCompression.rs_interleave_eval
#print axioms NearCompression.rs_interleave_length
#print axioms NearCompression.rs_interleave_degree
#print axioms NearCompression.rs_interleave_pair
#print axioms NearCompression.weighted_rs_interleaved_pullback
#print axioms NearCompression.canonical_polynomial_length
#print axioms NearCompression.canonical_polynomial_coeff
#print axioms NearCompression.canonical_polynomial_eval
#print axioms NearCompression.canonical_polynomial_residual
#print axioms NearCompression.scalar_residual_dot
#print axioms NearCompression.interleaved_coefficient_dot
#print axioms NearCompression.scalar_residual_interleaved
#print axioms NearCompression.weighted_fold_residual_polynomial_eval
#print axioms NearCompression.weighted_fold_parent_of_extraction
#print axioms NearCompression.weighted_fold_bad_count
#print axioms NearCompression.weighted_gated_fold_success_transfer
#print axioms NearCompression.weighted_gated_fold_bad_count
#print axioms NearCompression.indexed_terminal_candidate_of_queries
#print axioms NearCompression.global_chain_terminal_decomposition
#print axioms NearCompression.adaptive_round_failure_budget
#print axioms NearCompression.indexed_pair_mass_pullback
#print axioms NearCompression.indexed_weighted_parent
#print axioms NearCompression.indexed_fold_bad_count
#print axioms NearCompression.scalar_residual_weight_scale
#print axioms NearCompression.indexed_child_implies_fold_success
#print axioms NearCompression.indexed_outcome_implies_parent
#print axioms NearCompression.global_chain_query_bound_outside_extraction_bad

#print axioms NearCompression.prepared_code_bits_eval
#print axioms NearCompression.prepared_code_boolean
#print axioms NearCompression.prepared_code_limb_bound
#print axioms NearCompression.prepared_code_active_previous
#print axioms NearCompression.prepared_code_pc_successor
#print axioms NearCompression.prepared_code_pc_initial
#print axioms NearCompression.prepared_code_pc_index
#print axioms NearCompression.prepared_code_key_injective

#print axioms NearCompression.uniform_tuples_length
#print axioms NearCompression.independent_query_count
#print axioms NearCompression.adaptive_failure_leaves_exact
#print axioms NearCompression.interactive_accepted_cartesian
#print axioms NearCompression.interactive_round_query_budget
#print axioms NearCompression.global_chain_repeated_query_count

#print axioms NearCompression.prepared_code_mult_zero
#print axioms NearCompression.prepared_code_receive_active
#print axioms NearCompression.prepared_code_receive_count
#print axioms NearCompression.prepared_code_fetch_matched
#print axioms NearCompression.prepared_code_no_public_table_receives
#print axioms NearCompression.prepared_code_public_count_record
#print axioms NearCompression.prepared_code_published
#print axioms NearCompression.prepared_code_table_local
#print axioms NearCompression.prepared_code_fetch_authenticated
#print axioms NearCompression.prepared_code_message_pc
#print axioms NearCompression.prepared_code_fetch_at_pc

#print axioms NearCompression.shared_curve_below_threshold_count
#print axioms NearCompression.shared_curve_joint_agreement
#print axioms NearCompression.shared_polynomial_curve_extraction

#print axioms NearCompression.weighted_distinct_polynomial_agreement
#print axioms NearCompression.recovered_affine_curve_degree
#print axioms NearCompression.weighted_three_candidate_curve
#print axioms NearCompression.weighted_unique_regime_extraction
#print axioms NearCompression.sumcheck_linear_recovery
#print axioms NearCompression.sumcheck_linear_endpoint
#print axioms NearCompression.sumcheck_linear_roundtrip

#print axioms NearCompression.prepared_code_variable_entry_checked
#print axioms NearCompression.prepared_code_variable_checked
#print axioms NearCompression.prepared_code_public_record_field
#print axioms NearCompression.prepared_code_variable_record_pc
#print axioms NearCompression.prepared_code_variable_fetch
#print axioms NearCompression.prepared_code_variable_build_checked
#print axioms NearCompression.prepared_code_prepared_checked
#print axioms NearCompression.prepared_code_prepared_fetch
#print axioms NearCompression.weighted_unique_extraction_count
#print axioms NearCompression.weighted_unique_extraction_bad_count

#print axioms NearCompression.finite_point_index_inverse
#print axioms NearCompression.finite_point_domain_nodup
#print axioms NearCompression.finite_index_mass_transport
#print axioms NearCompression.finite_index_weight_sum

#print axioms NearCompression.indexed_unique_extraction
#print axioms NearCompression.indexed_unique_bad_count
#print axioms NearCompression.global_chain_weight_cap
#print axioms NearCompression.range_pair_weight_sum
#print axioms NearCompression.global_chain_projected_mass_bound
#print axioms NearCompression.global_chain_projected_cap

#print axioms NearCompression.halving_degree_product
#print axioms NearCompression.global_chain_unique_bad_count

#print axioms NearCompression.interactive_unique_fold_soundness

#print axioms NearCompression.prepared_exec_substitute_eval
#print axioms NearCompression.prepared_exec_ghost_env
#print axioms NearCompression.prepared_exec_substitute_row
#print axioms NearCompression.prepared_exec_simplify_eval
#print axioms NearCompression.prepared_exec_lower_eval
#print axioms NearCompression.prepared_exec_row_choices
#print axioms NearCompression.prepared_exec_add_binop
#print axioms NearCompression.prepared_exec_boolean
#print axioms NearCompression.prepared_exec_limb_bound
#print axioms NearCompression.prepared_exec_pc_transition

#print axioms NearCompression.checked_fold_reject_prefix
#print axioms NearCompression.checked_fold_reject_terminal
#print axioms NearCompression.checked_interactive_unique_fold_soundness
#print axioms NearCompression.prepared_exec_fetch_lower
#print axioms NearCompression.prepared_exec_advance_lower
#print axioms NearCompression.prepared_exec_python_choices
#print axioms NearCompression.prepared_exec_ghost_pc_step
#print axioms NearCompression.prepared_exec_transition_holds
#print axioms NearCompression.prepared_exec_source_eval
#print axioms NearCompression.prepared_exec_table_boolean
#print axioms NearCompression.prepared_exec_table_projection
#print axioms NearCompression.prepared_exec_table_add
#print axioms NearCompression.prepared_exec_wasm_add_local
#print axioms NearCompression.prepared_exec_table_wasm_add
#print axioms NearCompression.prepared_exec_stack_depth
#print axioms NearCompression.prepared_exec_wasm_stack_local
#print axioms NearCompression.weighted_lane_eval
#print axioms NearCompression.weighted_lane_degree
#print axioms NearCompression.weighted_lane_residual
#print axioms NearCompression.weighted_virtual_joint_distance
#print axioms NearCompression.weighted_virtual_unique_candidate
#print axioms NearCompression.weighted_virtual_no_candidate
#print axioms NearCompression.weighted_virtual_no_initial
#print axioms NearCompression.sha384_chain_boundary_sound
#print axioms NearCompression.prepared_exec_gas_equation
#print axioms NearCompression.prepared_exec_gas_borrow
#print axioms NearCompression.prepared_exec_gas_update_word
#print axioms NearCompression.prepared_exec_gas_success
#print axioms NearCompression.prepared_exec_gas_exhaustion
#print axioms NearCompression.prepared_exec_authenticated_fee
#print axioms NearCompression.prepared_exec_authenticated_opcode
#print axioms NearCompression.prepared_exec_table_local
#print axioms NearCompression.prepared_exec_authenticated_add
#print axioms NearCompression.kernel_monomial_degree
#print axioms NearCompression.kernel_monomial_leading
#print axioms NearCompression.structured_batch_kernel
#print axioms NearCompression.exact_degree_far_from_lower
#print axioms NearCompression.structured_kernel_joint_distance
#print axioms NearCompression.structured_kernel_no_joint_tuple
#print axioms NearCompression.structured_kernel_exact_scalar_candidate
#print axioms NearCompression.prepared_exec_immediate_projection
#print axioms NearCompression.prepared_exec_authenticated_immediate
#print axioms NearCompression.prepared_exec_table_wasm_stack
#print axioms NearCompression.prepared_exec_sp_onehot
#print axioms NearCompression.prepared_exec_opcode_projection
#print axioms NearCompression.prepared_exec_ghost_next_column
#print axioms NearCompression.prepared_exec_next_stack
#print axioms NearCompression.prepared_exec_add_next_sp
#print axioms NearCompression.prepared_exec_success_flags
#print axioms NearCompression.prepared_exec_authenticated_add_closed
#print axioms NearCompression.sha384_multiblock_ff_holds
#print axioms NearCompression.weighted_lane_coefficient
#print axioms NearCompression.functional_batch_boolean
#print axioms NearCompression.functional_equivalence_well_defined
#print axioms NearCompression.shared_functional_equivalence_well_defined
#print axioms NearCompression.scalar_representative_unique_candidate
#print axioms NearCompression.scalar_representative_no_candidate
#print axioms NearCompression.shared_functional_no_candidate
#print axioms NearCompression.scalar_representative_no_initial
#print axioms NearCompression.prepared_exec_stack_next_sp
#print axioms NearCompression.prepared_exec_authenticated_stack_closed
#print axioms NearCompression.prepared_exec_terminal_flags
#print axioms NearCompression.prepared_exec_authenticated_exhaustion
#print axioms NearCompression.prepared_exec_authenticated_end
#print axioms NearCompression.vector_shared_curve_joint_agreement
#print axioms NearCompression.vector_affine_extraction
#print axioms NearCompression.vector_affine_bad_count
#print axioms NearCompression.prepared_literal_exec_boolean
#print axioms NearCompression.prepared_literal_code_boolean
#print axioms NearCompression.prepared_literal_code_order
#print axioms NearCompression.prepared_literal_code_inactive
#print axioms NearCompression.prepared_literal_exec_pc
#print axioms NearCompression.prepared_literal_exec_gas
#print axioms NearCompression.prepared_literal_exec_local
#print axioms NearCompression.prepared_literal_exec_closure
#print axioms NearCompression.prepared_literal_exec_stack_guard
#print axioms NearCompression.prepared_literal_exec_end_guard
#print axioms NearCompression.tensor_child_count
#print axioms NearCompression.tensor_far_success_count
#print axioms NearCompression.tensor_bad_bound_closed
#print axioms NearCompression.sha384_padding_length
#print axioms NearCompression.sha384_padding_byte
#print axioms NearCompression.sha384_padding_expr
#print axioms NearCompression.interpolate_source_shape
#print axioms NearCompression.interpolate_source_degree
#print axioms NearCompression.interpolate_source_values
#print axioms NearCompression.common_points_reconstruct_rows
#print axioms NearCompression.shared_lane_reconstruction
#print axioms NearCompression.weighted_mass_implies_enough_points
#print axioms NearCompression.weighted_shared_lane_reconstruction
#print axioms NearCompression.prepared_exec_authenticated_stack_exact
#print axioms NearCompression.prepared_exec_continue_context
#print axioms NearCompression.prepared_literal_continue
#print axioms NearCompression.prepared_literal_active_nonlast
#print axioms NearCompression.prepared_literal_execution_run
#print axioms NearCompression.sha384_word_bytes
#print axioms NearCompression.prepared_exec_boundary_record
#print axioms NearCompression.prepared_exec_boundary_no_receives
#print axioms NearCompression.prepared_exec_boundary_public_unique
#print axioms NearCompression.prepared_exec_boundary_bound
#print axioms NearCompression.prepared_literal_boundary_gas
#print axioms NearCompression.tensor_cube_index_bits
#print axioms NearCompression.tensor_cube_index_surjective
#print axioms NearCompression.tensor_evaluate_row_mle
#print axioms NearCompression.weighted_values_mle
#print axioms NearCompression.structured_beta_tensor_identity
#print axioms NearCompression.compressed_tensor_reconstructs_lanes
#print axioms NearCompression.fixed_family_all_points_agree
#print axioms NearCompression.fixed_family_scalar_representative
#print axioms NearCompression.structured_beta_far_count
#print axioms NearCompression.prepared_literal_initial
#print axioms NearCompression.prepared_literal_enter
#print axioms NearCompression.prepared_literal_call_entry
#print axioms NearCompression.prepared_literal_run_call_checked
#print axioms NearCompression.prepared_literal_run_call
#print axioms NearCompression.sha384_multiblock_holds
#print axioms NearCompression.sha384_multiblock_table
#print axioms NearCompression.sha384_multiblock_compression
#print axioms NearCompression.sha384_multiblock_height_phase
#print axioms NearCompression.sha384_multiblock_receive_match
#print axioms NearCompression.sha384_multiblock_sender
#print axioms NearCompression.sha384_multiblock_state_message
#print axioms NearCompression.sha384_multiblock_state_link
#print axioms NearCompression.sha384_multiblock_boundary_zero
#print axioms NearCompression.sha384_multiblock_byte_field
#print axioms NearCompression.sha384_multiblock_digest_field
#print axioms NearCompression.sha384_multiblock_decoded_link
#print axioms NearCompression.sha384_multiblock_message_bits
#print axioms NearCompression.sha384_multiblock_byte_nat
#print axioms NearCompression.sha384_multiblock_iv_field
#print axioms NearCompression.sha384_multiblock_state_bits
#print axioms NearCompression.sha384_multiblock_initial
#print axioms NearCompression.sha384_multiblock_decoded_block_shape
#print axioms NearCompression.sha384_multiblock_padded_block
#print axioms NearCompression.sha384_multiblock_output_add
#print axioms NearCompression.sha384_multiblock_digest_nat
#print axioms NearCompression.sha384_multiblock_digest_bytes
#print axioms NearCompression.sha384_multiblock_blocks_step
#print axioms NearCompression.sha384_multiblock_blocks_chain
#print axioms NearCompression.sha384_multiblock_final_state
#print axioms NearCompression.sha384_multiblock_digest_sound
#print axioms NearCompression.sha384_message_public_prefix
#print axioms NearCompression.sha384_message_public_digest
#print axioms NearCompression.sha384_message_sound
#print axioms NearCompression.pair_fold_polynomial_degree
#print axioms NearCompression.pair_fold_polynomial_eval
#print axioms NearCompression.pair_fold_polynomial_endpoints
#print axioms NearCompression.affine_fold_final_append
#print axioms NearCompression.affine_fold_prefix_shape
#print axioms NearCompression.weighted_sumcheck_round_count
#print axioms NearCompression.weighted_sumcheck_false_persists
#print axioms NearCompression.adaptive_weighted_sumcheck_count
#print axioms NearCompression.pair_fold_range
#print axioms NearCompression.pair_fold_block_terminal
#print axioms NearCompression.pair_fold_blocks_append
#print axioms NearCompression.weighted_lane_blocks_shape
#print axioms NearCompression.weighted_lane_blocks_terminal
#print axioms NearCompression.weighted_terminal_dot
#print axioms NearCompression.weighted_terminal_beta
#print axioms NearCompression.weighted_initial_functional
#print axioms NearCompression.prepared_exec_choices_at
#print axioms NearCompression.prepared_exec_ghost_quiet
#print axioms NearCompression.prepared_exec_quiet
#print axioms NearCompression.prepared_literal_padding_step
#print axioms NearCompression.prepared_exec_snapshot_trans
#print axioms NearCompression.prepared_literal_padding_suffix
#print axioms NearCompression.quotient_expr_eval
#print axioms NearCompression.quotient_interaction_msg
#print axioms NearCompression.quotient_interaction_mult
#print axioms NearCompression.quotient_table_bus_count
#print axioms NearCompression.quotient_tables_length
#print axioms NearCompression.quotient_tables_get
#print axioms NearCompression.quotient_bus_count
#print axioms NearCompression.quotient_holdsP
#print axioms NearCompression.equality_weight_read_mle
#print axioms NearCompression.scalar_residual_eq_weights_mle
#print axioms NearCompression.equality_weights_length

#print axioms NearCompression.sha384_quotient_digest_sound
#print axioms NearCompression.prepared_exec_final_row_transport
#print axioms NearCompression.prepared_exec_ghost_bits
#print axioms NearCompression.prepared_literal_boundary_stack_word
#print axioms NearCompression.prepared_exec_public_stack_decode
#print axioms NearCompression.prepared_literal_final_row_published
#print axioms NearCompression.prepared_literal_terminal_published
#print axioms NearCompression.weighted_polynomial_mle
#print axioms NearCompression.close_family_sumcheck_candidate_count
#print axioms NearCompression.close_family_sumcheck_residual_count
#print axioms NearCompression.prepared_literal_witness_final_row
#print axioms NearCompression.prepared_literal_witness_published
#print axioms NearCompression.prepared_literal_public_run_call
#print axioms NearCompression.sha384_endpoint_core_holds
#print axioms NearCompression.sha384_endpoint_core_rounds
#print axioms NearCompression.sha384_endpoint_add_holds
#print axioms NearCompression.sha384_endpoint_add_sound
#print axioms NearCompression.sha384_endpoint_last_iff
#print axioms NearCompression.functional_opening_reduction_count
#print axioms NearCompression.equality_weights_append
#print axioms NearCompression.bound_opening_initial_candidate
#print axioms NearCompression.functional_opening_fold_count
#print axioms NearCompression.sparse_lift_mle
#print axioms NearCompression.repeated_low_weight_mle
#print axioms NearCompression.sparse_lift_block
#print axioms NearCompression.repeated_weight_block
#print axioms NearCompression.prepared_control_inspect
#print axioms NearCompression.prepared_control_target_checked
#print axioms NearCompression.prepared_control_entry_checked
#print axioms NearCompression.prepared_control_step_block
#print axioms NearCompression.prepared_control_step_br_if
#print axioms NearCompression.prepared_control_code_checked
#print axioms NearCompression.prepared_control_step_nested_end
#print axioms NearCompression.sha384_endpoint_core_table
#print axioms NearCompression.sha384_endpoint_core_constants
#print axioms NearCompression.sha384_endpoint_core_height_phase
#print axioms NearCompression.sha384_endpoint_core_round_holds
#print axioms NearCompression.sha384_endpoint_state_bits
#print axioms NearCompression.sha384_split_byte_field
#print axioms NearCompression.sha384_split_iv_field
#print axioms NearCompression.sha384_split_message_bits
#print axioms NearCompression.sha384_split_state_bits
#print axioms NearCompression.sha384_split_byte_nat
#print axioms NearCompression.sha384_split_initial
#print axioms NearCompression.sha384_split_padded_block
#print axioms NearCompression.sha384_split_compression
#print axioms NearCompression.cube_sum_split
#print axioms NearCompression.lower_zeta_add
#print axioms NearCompression.upper_zeta_add
#print axioms NearCompression.dual_zeta_dot
#print axioms NearCompression.lower_zeta_mobius
#print axioms NearCompression.dual_mobius_dot
#print axioms NearCompression.row_equality_dot
#print axioms NearCompression.current_dual_mobius
#print axioms NearCompression.cyclic_sum_successor
#print axioms NearCompression.cyclic_predecessor_dot
#print axioms NearCompression.next_dual_mobius
#print axioms NearCompression.current_next_dual_mobius
#print axioms NearCompression.current_next_coefficient_functional
#print axioms NearCompression.prepared_control_bit_sum
#print axioms NearCompression.prepared_control_condition_selected
#print axioms NearCompression.prepared_control_inverse_zero
#print axioms NearCompression.prepared_control_bit_sum_zero
#print axioms NearCompression.prepared_control_horner_zero
#print axioms NearCompression.prepared_control_stack_word
#print axioms NearCompression.prepared_control_stack_zero
#print axioms NearCompression.prepared_control_condition_sound
#print axioms NearCompression.prepared_control_literal_condition_source
#print axioms NearCompression.prepared_control_literal_onehot
#print axioms NearCompression.prepared_control_literal_condition
#print axioms NearCompression.cube_sum_split_axes
#print axioms NearCompression.packed_dual_weight_index
#print axioms NearCompression.packed_dual_weight_mle
#print axioms NearCompression.mobius_split_axes
#print axioms NearCompression.packed_mobius_tensor
#print axioms NearCompression.tensor_dual_mobius_dot
#print axioms NearCompression.packed_current_next_functional
#print axioms NearCompression.packed_full_mobius_functional
#print axioms NearCompression.prepared_control_bus_mult_zero
#print axioms NearCompression.prepared_control_bus_receive_active
#print axioms NearCompression.prepared_control_bus_receive_count
#print axioms NearCompression.prepared_control_bus_fetch_matched
#print axioms NearCompression.prepared_control_bus_no_public_table_receives
#print axioms NearCompression.prepared_control_bus_public_count_record
#print axioms NearCompression.prepared_control_bus_published
#print axioms NearCompression.prepared_control_bus_table_local
#print axioms NearCompression.prepared_control_bus_fetch_authenticated
#print axioms NearCompression.prepared_control_bus_message_pc
#print axioms NearCompression.prepared_control_bus_fetch_at_pc
#print axioms NearCompression.prepared_control_bus_literal_air
#print axioms NearCompression.prepared_control_bus_literal_boolean
#print axioms NearCompression.prepared_control_bus_literal_order
#print axioms NearCompression.prepared_control_bus_literal_inactive
#print axioms NearCompression.prepared_control_literal_fetch
#print axioms NearCompression.sha384_core_message_eval
#print axioms NearCompression.sha384_endpoint_message_eval
#print axioms NearCompression.sha384_endpoint_table_index
#print axioms NearCompression.sha384_endpoint_receive_match
#print axioms NearCompression.sha384_endpoint_input_sender
#print axioms NearCompression.sha384_endpoint_input_match
#print axioms NearCompression.sha384_endpoint_inputs_same_core
#print axioms NearCompression.sha384_endpoint_limb_ext
#print axioms NearCompression.sha384_endpoint_word_decode
#print axioms NearCompression.sha384_endpoint_output_compression
#print axioms NearCompression.sha384_endpoint_output_sender
#print axioms NearCompression.sha384_endpoint_send_active
#print axioms NearCompression.sha384_endpoint_compression_link
#print axioms NearCompression.prepared_control_public_record_field
#print axioms NearCompression.prepared_control_record_pc
#print axioms NearCompression.prepared_control_authenticated_fetch
#print axioms NearCompression.sha384_endpoint_public_count
#print axioms NearCompression.sha384_endpoint_public_match
#print axioms NearCompression.sha384_endpoint_blocks_step
#print axioms NearCompression.sha384_endpoint_blocks_chain
#print axioms NearCompression.sha384_endpoint_final_state
#print axioms NearCompression.sha384_endpoint_digest_bytes
#print axioms NearCompression.sha384_endpoint_final_digest
#print axioms NearCompression.sha384_endpoint_digest_sound
#print axioms NearCompression.sha384_endpoint_public_prefix
#print axioms NearCompression.sha384_endpoint_public_digest_layout
#print axioms NearCompression.sha384_endpoint_public_count_layout
#print axioms NearCompression.sha384_endpoint_message_sound
#print axioms NearCompression.prepared_control_literal_boolean
#print axioms NearCompression.prepared_control_branch_opcode
#print axioms NearCompression.prepared_control_taken_eval
#print axioms NearCompression.prepared_control_taken_pc
#print axioms NearCompression.prepared_control_taken_gates
#print axioms NearCompression.prepared_control_taken_label
#print axioms NearCompression.prepared_control_setup_checked
#print axioms NearCompression.prepared_control_setup_fetch
#print axioms NearCompression.upper_zeta_mle_dual_sum
#print axioms NearCompression.dual_row_sum_boolean_cube
#print axioms NearCompression.dual_borrow_dp_linear_sum
#print axioms NearCompression.dual_borrow_sum_cube
#print axioms NearCompression.row_equality_weight_bits
#print axioms NearCompression.cyclic_row_weight_bits
#print axioms NearCompression.dual_borrow_shift_mle
#print axioms NearCompression.current_weight_accumulator_product
#print axioms NearCompression.dual_borrow_current_mle
#print axioms NearCompression.optimized_row_weight_mles
#print axioms NearCompression.bit_runs_upper_zeta
#print axioms NearCompression.zeta_source_bit_set
#print axioms NearCompression.sequential_zeta_pass_exact
#print axioms NearCompression.zeta_python_guard
#print axioms NearCompression.mutable_zeta_runs_exact
#print axioms NearCompression.mutable_upper_zeta
#print axioms NearCompression.zeta_write_python
#print axioms NearCompression.mutable_upper_zeta_list
#print axioms NearCompression.prepared_control_index_selected
#print axioms NearCompression.prepared_control_branch_height
#print axioms NearCompression.prepared_control_taken_sp
#print axioms NearCompression.prepared_control_below_selected
#print axioms NearCompression.prepared_control_taken_stack
#print axioms NearCompression.prepared_control_taken_stack_projection
#print axioms NearCompression.prepared_control_gas_boolean
#print axioms NearCompression.prepared_control_gas_limb_bound
#print axioms NearCompression.prepared_control_gas_equation
#print axioms NearCompression.prepared_control_gas_borrow
#print axioms NearCompression.prepared_control_gas_update_word
#print axioms NearCompression.prepared_control_gas_success
#print axioms NearCompression.prepared_control_gas_exhaustion
#print axioms NearCompression.prepared_control_literal_gas_source
#print axioms NearCompression.prepared_control_literal_limb
#print axioms NearCompression.prepared_control_sequential_pc
#print axioms NearCompression.prepared_control_continue_status
#print axioms NearCompression.prepared_control_label_equations
#print axioms NearCompression.prepared_control_untaken_pc_label
#print axioms NearCompression.prepared_control_charged_taken
#print axioms NearCompression.prepared_control_charged_untaken
#print axioms NearCompression.sha384_batch_constraint
#print axioms NearCompression.sha384_batch_active_boolean
#print axioms NearCompression.sha384_batch_first
#print axioms NearCompression.sha384_batch_no_restart
#print axioms NearCompression.sha384_batch_phase_step
#print axioms NearCompression.sha384_batch_active_phase
#print axioms NearCompression.sha384_batch_active_prefix
#print axioms NearCompression.sha384_batch_inactive_phase
#print axioms NearCompression.sha384_batch_tag_step
#print axioms NearCompression.sha384_batch_active_tag
#print axioms NearCompression.sha384_batch_height_small
#print axioms NearCompression.sha384_batch_stop_index
#print axioms NearCompression.sha384_batch_stop_last
#print axioms NearCompression.sha384_batch_stop_next_inactive
#print axioms NearCompression.sha384_batch_required_active
#print axioms NearCompression.sha384_batch_capacity
#print axioms NearCompression.sha384_batch_active_bounded
#print axioms NearCompression.sha384_batch_active_iff
#print axioms NearCompression.sha384_batch_segment_metadata
#print axioms NearCompression.sha384_batch_padding_selectors
#print axioms NearCompression.sha384_batch_tag_identifies_block
#print axioms NearCompression.sha384_batch_payload_length
#print axioms NearCompression.sha384_batch_iv_payload_length
#print axioms NearCompression.sha384_batch_count_bytes_length
#print axioms NearCompression.sha384_batched_public_length
#print axioms NearCompression.sha384_batched_public_prefix
#print axioms NearCompression.beta_wide_pair_exact
#print axioms NearCompression.source_pair_full_index
#print axioms NearCompression.heterogeneous_source_projection
#print axioms NearCompression.heterogeneous_beta_pair_exact
#print axioms NearCompression.heterogeneous_source_query_indices
#print axioms NearCompression.heterogeneous_half_order
#print axioms NearCompression.heterogeneous_bound_initial_pair
#print axioms NearCompression.weighted_virtual_append
#print axioms NearCompression.sha384_batch_combined_shapes
#print axioms NearCompression.sha384_batch_link_shape
#print axioms NearCompression.sha384_batch_gate_current
#print axioms NearCompression.sha384_batch_gated_constraint
#print axioms NearCompression.sha384_batch_pair_holds
#print axioms NearCompression.sha384_batch_output
#print axioms NearCompression.sha384_batch_recurrence
#print axioms NearCompression.sha384_batch_round_holds
#print axioms NearCompression.sha384_batch_constant_sum
#print axioms NearCompression.sha384_batch_key_limb
#print axioms NearCompression.sha384_batch_key
#print axioms NearCompression.sha384_batch_round_segment
#print axioms NearCompression.sha384_batch_rounds
#print axioms NearCompression.sha384_batch_compression
#print axioms NearCompression.sha384_flat_payload_index
#print axioms NearCompression.sha384_batch_payload_index
#print axioms NearCompression.sha384_batch_iv_payload_index
#print axioms NearCompression.sha384_batched_public_payload_index
#print axioms NearCompression.coefficient_polynomial_eval
#print axioms NearCompression.sparse_lift_monomial_tensor
#print axioms NearCompression.sparse_lift_polynomial_eval
#print axioms NearCompression.branch_words_polynomial_eval
#print axioms NearCompression.branch_words_degree
#print axioms NearCompression.branch_words_stride_coefficient
#print axioms NearCompression.branch_words_authenticated_pair
#print axioms NearCompression.prepared_control_untaken_sp
#print axioms NearCompression.prepared_control_untaken_stack
#print axioms NearCompression.prepared_control_untaken_stack_projection
#print axioms NearCompression.prepared_control_opcode_selected
#print axioms NearCompression.prepared_control_opcode_exclusive
#print axioms NearCompression.prepared_control_block_label
#print axioms NearCompression.prepared_control_nested_end_label
#print axioms NearCompression.prepared_control_frame_stack
#print axioms NearCompression.prepared_control_frame_sp
#print axioms NearCompression.prepared_control_stack_size
#print axioms NearCompression.prepared_control_block_state
#print axioms NearCompression.prepared_control_nested_end_state
#print axioms NearCompression.prepared_control_charged_untaken_stack
#print axioms NearCompression.sha384_batch_receive_match
#print axioms NearCompression.sha384_batch_state_message_eval
#print axioms NearCompression.sha384_batch_input_sender
#print axioms NearCompression.sha384_batch_phase_location
#print axioms NearCompression.sha384_batch_endpoint_input
#print axioms NearCompression.sha384_batch_endpoint_inputs
#print axioms NearCompression.sha384_batch_endpoint_compression
#print axioms NearCompression.sha384_batch_output_sender
#print axioms NearCompression.sha384_batch_endpoint_send_active
#print axioms NearCompression.sha384_batch_compression_link
#print axioms NearCompression.sha384_batch_no_high_sender
#print axioms NearCompression.sha384_batch_public_receive
#print axioms NearCompression.sha384_batch_iv_record
#print axioms NearCompression.sha384_batch_initial
#print axioms NearCompression.sha384_batched_iv_content
#print axioms NearCompression.sha384_batched_iv_count_byte
#print axioms NearCompression.sha384_batched_iv_count
#print axioms NearCompression.sha384_batched_public_initial
#print axioms NearCompression.sha384_batch_padded_byte_bound
#print axioms NearCompression.sha384_batch_message_limb_bound
#print axioms NearCompression.sha384_batched_public_field_lookup
#print axioms NearCompression.sha384_batched_public_limb_nat
#print axioms NearCompression.sha384_batch_message_limb_bytes
#print axioms NearCompression.sha384_batch_message_record
#print axioms NearCompression.sha384_batch_message_payload
#print axioms NearCompression.sha384_batch_message_limb
#print axioms NearCompression.sha384_batched_message_count_byte
#print axioms NearCompression.sha384_batched_message_count_digit
#print axioms NearCompression.sha384_batch_count_reconstruction
#print axioms NearCompression.sha384_batched_message_count
#print axioms NearCompression.sha384_batch_digest_count
#print axioms NearCompression.sha384_batch_digest_match
#print axioms NearCompression.sha384_batch_digest_bytes
#print axioms NearCompression.sha384_batch_final_digest
#print axioms NearCompression.sha384_batched_endpoint_expansion
#print axioms NearCompression.sha384_batched_endpoint_public_get
#print axioms NearCompression.sha384_batched_digest_count_layout
#print axioms NearCompression.sha384_batched_digest_layout
#print axioms NearCompression.sha384_batch_blocks_step
#print axioms NearCompression.sha384_batch_blocks_chain
#print axioms NearCompression.sha384_batched_final_state_of_decoded
#print axioms NearCompression.sha384_batched_message_sound_of_decoded
#print axioms NearCompression.sha384_batch_message_bits
#print axioms NearCompression.sha384_batch_trace_limb
#print axioms NearCompression.sha384_batch_trace_limb_bytes
#print axioms NearCompression.sha384_batch_trace_byte
#print axioms NearCompression.sha384_batched_decoded_block
#print axioms NearCompression.sha384_batched_message_sound
#print axioms NearCompression.prepared_control_exec_local
#print axioms NearCompression.prepared_control_authenticated_decode
#print axioms NearCompression.prepared_control_setup_block_state
#print axioms NearCompression.prepared_control_setup_nested_end_state
#print axioms NearCompression.prepared_control_setup_untaken_state
#print axioms NearCompression.prepared_control_branch_height_lt
#print axioms NearCompression.prepared_control_stack_word_bound
#print axioms NearCompression.prepared_control_stack_extract
#print axioms NearCompression.prepared_control_setup_taken_state
#print axioms NearCompression.prepared_control_setup_branch_continue
#print axioms NearCompression.fft_block_stage_invariant
#print axioms NearCompression.fft_stages_natural_evaluation
#print axioms NearCompression.fft_stages_zero_padded_evaluation
#print axioms NearCompression.fft_stages_rs_pair
#print axioms NearCompression.prepared_control_no_branch_eval
#print axioms NearCompression.prepared_control_legacy_source_eval
#print axioms NearCompression.prepared_control_legacy_sp_source
#print axioms NearCompression.prepared_control_legacy_stack_source
#print axioms NearCompression.prepared_control_legacy_choice_source
#print axioms NearCompression.prepared_control_legacy_add_depth_source
#print axioms NearCompression.prepared_control_legacy_add_carry_source
#print axioms NearCompression.prepared_control_legacy_stack_depth_source
#print axioms NearCompression.prepared_control_legacy_projection
#print axioms NearCompression.prepared_control_authenticated_legacy_projection
#print axioms NearCompression.prepared_control_legacy_add_next_sp
#print axioms NearCompression.prepared_control_legacy_stack_next_sp
#print axioms NearCompression.prepared_control_legacy_wasm_add
#print axioms NearCompression.prepared_control_legacy_wasm_stack
#print axioms NearCompression.prepared_control_legacy_pc_label
#print axioms NearCompression.prepared_control_labels_transport
#print axioms NearCompression.prepared_control_setup_add_state
#print axioms NearCompression.prepared_control_authenticated_immediate
#print axioms NearCompression.prepared_control_setup_stack_state
#print axioms NearCompression.fft_reverse_bits_bound
#print axioms NearCompression.fft_reverse_carry_xor
#print axioms NearCompression.fft_reverse_carry_successor
#print axioms NearCompression.fft_reverse_counter_exact
#print axioms NearCompression.fft_reverse_test_bit
#print axioms NearCompression.fft_reverse_involutive
#print axioms NearCompression.fft_bit_reverse_swaps
#print axioms NearCompression.fft_native_bit_reversal
#print axioms NearCompression.sha384_committed_pad_constraint
#print axioms NearCompression.sha384_committed_pad_first
#print axioms NearCompression.sha384_committed_pad_step
#print axioms NearCompression.sha384_committed_pad_selector
#print axioms NearCompression.sha384_committed_pad_inactive
#print axioms NearCompression.sha384_committed_pad_constant
#print axioms NearCompression.prepared_control_terminal_flags
#print axioms NearCompression.prepared_control_root_height_zero
#print axioms NearCompression.prepared_control_root_end_depth
#print axioms NearCompression.prepared_control_setup_exhaustion
#print axioms NearCompression.prepared_control_setup_root_end
#print axioms NearCompression.prepared_control_exec_gas
#print axioms NearCompression.prepared_control_setup_continue_context
#print axioms NearCompression.sha384_committed_pad_sum
#print axioms NearCompression.sha384_committed_pad_tag
#print axioms NearCompression.prepared_control_active_nonlast
#print axioms NearCompression.prepared_control_execution_run
#print axioms NearCompression.sha384_committed_input_constraint
#print axioms NearCompression.sha384_committed_input_bits
#print axioms NearCompression.sha384_committed_pad_bits
#print axioms NearCompression.sha384_committed_fixed_byte
#print axioms NearCompression.sha384_committed_bitexpr_eval
#print axioms NearCompression.sha384_committed_input_byte_bound
#print axioms NearCompression.sha384_committed_pad_byte_bound
#print axioms NearCompression.fft_butterfly_write_pair
#print axioms NearCompression.fft_block_writes_exact
#print axioms NearCompression.fft_block_writes_outside
#print axioms NearCompression.fft_twiddle_walk_power
#print axioms NearCompression.fft_stage_writes_exact
#print axioms NearCompression.fft_stage_writes_refine
#print axioms NearCompression.sha384_committed_fixed_byte_nat
#print axioms NearCompression.sha384_committed_pad_constant_bound
#print axioms NearCompression.sha384_committed_pad_constant_nat
#print axioms NearCompression.fft_mutable_schedule_stage
#print axioms NearCompression.fft_mutable_schedule_evaluation
#print axioms NearCompression.fft_mutable_zero_padded_evaluation
#print axioms NearCompression.fft_mutable_rs_pair
#print axioms NearCompression.prepared_control_boundary_no_receives
#print axioms NearCompression.prepared_control_boundary_public_unique
#print axioms NearCompression.prepared_control_boundary_bound
#print axioms NearCompression.prepared_control_boundary_gas
#print axioms NearCompression.prepared_control_initial
#print axioms NearCompression.prepared_control_enter
#print axioms NearCompression.prepared_control_call_entry
#print axioms NearCompression.prepared_control_run_call_checked
#print axioms NearCompression.prepared_control_run_call
#print axioms NearCompression.bit_runs_lower_mobius
#print axioms NearCompression.mobius_source_bit_clear
#print axioms NearCompression.sequential_mobius_pass_exact
#print axioms NearCompression.mutable_mobius_runs_exact
#print axioms NearCompression.mutable_lower_mobius
#print axioms NearCompression.mobius_write_native
#print axioms NearCompression.mutable_lower_mobius_list
#print axioms NearCompression.sha384_committed_receive_match
#print axioms NearCompression.sha384_committed_input_send_location
#print axioms NearCompression.sha384_committed_byte_sender
#print axioms NearCompression.sha384_committed_pad_input_byte
#print axioms NearCompression.packed_computed_coefficients_length
#print axioms NearCompression.packed_computed_coefficient
#print axioms NearCompression.packed_computed_degree
#print axioms NearCompression.packed_computed_functional
#print axioms NearCompression.packed_computed_fft_evaluation
#print axioms NearCompression.packed_computed_leaf_pair
#print axioms NearCompression.packed_computed_wide_leaf
#print axioms NearCompression.packed_computed_beta_pair
#print axioms NearCompression.mobius_mutable_runs_outside
#print axioms NearCompression.packed_computed_buffer
#print axioms NearCompression.packed_computed_pipeline
#print axioms NearCompression.sha384_committed_message_length
#print axioms NearCompression.sha384_committed_message_byte
#print axioms NearCompression.sha384_committed_message_byte_bound
#print axioms NearCompression.sha384_committed_padded_byte
#print axioms NearCompression.prepared_control_quiet_stack
#print axioms NearCompression.prepared_control_quiet_sp
#print axioms NearCompression.prepared_control_quiet
#print axioms NearCompression.prepared_control_padding_step
#print axioms NearCompression.prepared_control_padding_suffix
#print axioms NearCompression.prepared_control_boundary_stack_word
#print axioms NearCompression.prepared_control_final_row_published
#print axioms NearCompression.prepared_control_terminal_published
#print axioms NearCompression.prepared_control_witness_final_row
#print axioms NearCompression.prepared_control_witness_published
#print axioms NearCompression.prepared_control_public_run_call
#print axioms NearCompression.gkr_input_functional_weights
#print axioms NearCompression.gkr_universal_functionals_separate
#print axioms NearCompression.gkr_common_input_predicate
#print axioms NearCompression.gkr_adaptive_input_kernel
#print axioms NearCompression.gkr_adaptive_kernel_not_fixed
#print axioms NearCompression.gkr_fixed_ones_functional
#print axioms NearCompression.sha384_direct_byte
#print axioms NearCompression.sha384_direct_input_bits
#print axioms NearCompression.sha384_direct_message_byte_bound
#print axioms NearCompression.sha384_direct_limb
#print axioms NearCompression.gkr_universal_rows_slots_separate
#print axioms NearCompression.gkr_universal_rows_predicate
#print axioms NearCompression.gkr_universal_weight_functional
#print axioms NearCompression.gkr_universal_coefficient_family_separates
#print axioms NearCompression.sha384_direct_receive_match
#print axioms NearCompression.sha384_direct_block_sender
#print axioms NearCompression.sha384_direct_sender_location
#print axioms NearCompression.sha384_direct_block_receive
#print axioms NearCompression.sha384_direct_public_length
#print axioms NearCompression.sha384_direct_public_digest_byte
#print axioms NearCompression.sha384_direct_public_iv_byte
#print axioms NearCompression.sha384_direct_public_count_byte
#print axioms NearCompression.sha384_direct_segment_count
#print axioms NearCompression.sha384_direct_digest_record
#print axioms NearCompression.sha384_direct_iv_record
#print axioms NearCompression.sha384_direct_batched_iv_record
#print axioms NearCompression.sha384_direct_core_no_public
#print axioms NearCompression.sha384_direct_eval_public
#print axioms NearCompression.sha384_direct_table_count_public
#print axioms NearCompression.sha384_direct_project
#print axioms NearCompression.sha384_direct_message_bytes_length
#print axioms NearCompression.sha384_direct_message_bytes_exact
#print axioms NearCompression.sha384_first_row_traffic
#print axioms NearCompression.sha384_first_row_count
#print axioms NearCompression.sha384_direct_input_count
#print axioms NearCompression.sha384_direct_canonical_block
#print axioms NearCompression.sha384_direct_canonical_records
#print axioms NearCompression.sha384_direct_batched_digest_count
#print axioms NearCompression.sha384_direct_batched_digest_record
#print axioms NearCompression.sha384_direct_batched_digest_messages
#print axioms NearCompression.sha384_direct_batched_public_fit
#print axioms NearCompression.sha384_direct_batched_iv_messages
#print axioms NearCompression.sha384_direct_public_counts
#print axioms NearCompression.sha384_direct_message_sound

#print axioms NearCompression.row_equality_coordinate_affine
#print axioms NearCompression.row_mle_coordinate_affine
#print axioms NearCompression.affine_coordinate_polynomial
#print axioms NearCompression.gkr_weight_row_coordinate_affine
#print axioms NearCompression.gkr_weight_left_coordinate_affine
#print axioms NearCompression.gkr_weight_right_coordinate_affine
#print axioms NearCompression.gkr_weight_gamma_affine
#print axioms NearCompression.gkr_beta_coordinate_affine
#print axioms NearCompression.gkr_beta_coordinate_degree
#print axioms NearCompression.sha384_direct_public_check_canonical
#print axioms NearCompression.sha384_direct_public_check_exists
#print axioms NearCompression.sha384_direct_public_decode
#print axioms NearCompression.sha384_direct_public_check_complete
#print axioms NearCompression.sha384_direct_public_check_sound
#print axioms NearCompression.tensor_cube_values_length
#print axioms NearCompression.multiaffine_tensor_realization
#print axioms NearCompression.gkr_list_insert_coordinate
#print axioms NearCompression.point_affine_list_multiaffine
#print axioms NearCompression.multiaffine_candidate_far_count
#print axioms NearCompression.gkr_joint_beta_affine
#print axioms NearCompression.gkr_joint_source_tensor_identity
#print axioms NearCompression.joint_tensor_reconstruct
#print axioms NearCompression.joint_beta_candidate_far_count
#print axioms NearCompression.gkr_joint_candidate_far_count
#print axioms NearCompression.joint_source_initial_candidate
#print axioms NearCompression.joint_source_far_checked_count
#print axioms NearCompression.prepared_locals_lookup
#print axioms NearCompression.prepared_locals_exec_get
#print axioms NearCompression.prepared_locals_exec_set
#print axioms NearCompression.prepared_locals_exec_tee
#print axioms NearCompression.prepared_locals_step_charge
#print axioms NearCompression.heterogeneous_column_private_lookup
#print axioms NearCompression.heterogeneous_column_affine
#print axioms NearCompression.heterogeneous_beta_coordinate_affine
#print axioms NearCompression.heterogeneous_joint_beta_affine
#print axioms NearCompression.heterogeneous_lane_weight_mle
#print axioms NearCompression.heterogeneous_betas_affine
#print axioms NearCompression.heterogeneous_source_tensor_identity
#print axioms NearCompression.heterogeneous_candidate_far_count
#print axioms NearCompression.heterogeneous_far_checked_count
#print axioms NearCompression.prepared_locals_base_member
#print axioms NearCompression.prepared_locals_selector_boolean
#print axioms NearCompression.prepared_locals_selected
#print axioms NearCompression.prepared_locals_index
#print axioms NearCompression.prepared_locals_operand
#print axioms NearCompression.prepared_locals_inspect
#print axioms NearCompression.prepared_locals_target_checked
#print axioms NearCompression.prepared_locals_code_shape
#print axioms NearCompression.prepared_locals_code_entry
#print axioms NearCompression.prepared_locals_entry_checked
#print axioms NearCompression.prepared_locals_setup_checked
#print axioms NearCompression.checked_table_metadata_lane
#print axioms NearCompression.checked_table_metadata_lanes
#print axioms NearCompression.checked_metadata_all_lanes
#print axioms NearCompression.prepared_locals_bus_mult_zero
#print axioms NearCompression.prepared_locals_bus_receive_active
#print axioms NearCompression.prepared_locals_bus_receive_count
#print axioms NearCompression.prepared_locals_bus_fetch_matched
#print axioms NearCompression.prepared_locals_bus_no_public_table_receives
#print axioms NearCompression.prepared_locals_bus_public_count_record
#print axioms NearCompression.prepared_locals_bus_published
#print axioms NearCompression.prepared_locals_bus_table_local
#print axioms NearCompression.prepared_locals_bus_fetch_authenticated
#print axioms NearCompression.prepared_locals_bus_message_pc
#print axioms NearCompression.prepared_locals_bus_fetch_at_pc
#print axioms NearCompression.prepared_locals_bus_literal_air
#print axioms NearCompression.prepared_locals_bus_literal_boolean
#print axioms NearCompression.prepared_locals_bus_literal_order
#print axioms NearCompression.prepared_locals_bus_literal_inactive
#print axioms NearCompression.prepared_locals_literal_fetch
#print axioms NearCompression.prepared_locals_public_record_field
#print axioms NearCompression.prepared_locals_record_pc
#print axioms NearCompression.prepared_locals_authenticated_fetch
#print axioms NearCompression.prepared_locals_bits_boolean
#print axioms NearCompression.prepared_locals_update_source
#print axioms NearCompression.prepared_locals_limb_step
#print axioms NearCompression.prepared_locals_limb_bound
#print axioms NearCompression.prepared_locals_initial_bit
#print axioms NearCompression.prepared_locals_initial_limb
#print axioms NearCompression.prepared_locals_initial_word
#print axioms NearCompression.prepared_locals_initial_array
#print axioms NearCompression.prepared_locals_top_selected
#print axioms NearCompression.prepared_locals_words_write
#print axioms NearCompression.prepared_locals_array_set
#print axioms NearCompression.prepared_locals_array_write
#print axioms NearCompression.rotate_polynomial_coeff
#print axioms NearCompression.rotate_polynomial_eval
#print axioms NearCompression.rotate_polynomial_degree
#print axioms NearCompression.power_projected_source_symmetry
#print axioms NearCompression.projected_source_rotation
#print axioms NearCompression.projected_source_sparse_coefficients
#print axioms NearCompression.recovered_projected_degree
#print axioms NearCompression.recovered_projected_coefficients
#print axioms NearCompression.prepared_locals_gas_source
#print axioms NearCompression.prepared_locals_authenticated_fee
#print axioms NearCompression.prepared_locals_setup_authenticated_fee
#print axioms NearCompression.row_mle_at_zero
#print axioms NearCompression.upper_zeta_at_zero
#print axioms NearCompression.row_equality_mass
#print axioms NearCompression.heterogeneous_beta_zero_current
#print axioms NearCompression.row_equality_boolean_selector
#print axioms NearCompression.heterogeneous_column_boolean_selector
#print axioms NearCompression.heterogeneous_beta_select_live
#print axioms NearCompression.heterogeneous_beta_select_absent
#print axioms NearCompression.live_slot_interval
#print axioms NearCompression.live_slot_disjoint
#print axioms NearCompression.metadata_lane_nonempty
#print axioms NearCompression.nonempty_lane_first_slot
#print axioms NearCompression.bounded_bits_index
#print axioms NearCompression.joint_separator_local
#print axioms NearCompression.cube_from_bits_values
#print axioms NearCompression.joint_separator_cube
#print axioms NearCompression.canonical_joint_lane_selector
#print axioms NearCompression.joint_lane_pointwise_agreement
#print axioms NearCompression.joint_representative_lane_mass
#print axioms NearCompression.checked_lane_selectors
#print axioms NearCompression.prepared_locals_stack_word
#print axioms NearCompression.prepared_locals_frame_write
#print axioms NearCompression.prepared_locals_array_preserved
#print axioms NearCompression.prepared_locals_exec_local
#print axioms NearCompression.prepared_locals_authenticated_instruction
#print axioms NearCompression.prepared_locals_authenticated_selected
#print axioms NearCompression.joint_representative_lane_radius
#print axioms NearCompression.joint_representative_projected_recovery
#print axioms NearCompression.range_rotation_permutation
#print axioms NearCompression.natural_rs_rotation
#print axioms NearCompression.projected_root_order
#print axioms NearCompression.natural_rs_distinct
#print axioms NearCompression.projected_rs_domain_certificates
#print axioms NearCompression.natural_rs_joint_projected_recovery
#print axioms NearCompression.prepared_locals_literal_limb
#print axioms NearCompression.prepared_locals_sequential_pc
#print axioms NearCompression.prepared_locals_continue_status
#print axioms NearCompression.prepared_locals_label_equations
#print axioms NearCompression.prepared_locals_pc_label
#print axioms NearCompression.prepared_locals_onehot
#print axioms NearCompression.prepared_locals_depth_step
#print axioms NearCompression.sha384_shared_core_constraints
#print axioms NearCompression.sha384_shared_endpoint_constraints
#print axioms NearCompression.sha384_shared_constraint
#print axioms NearCompression.sha384_shared_add_holds
#print axioms NearCompression.sha384_shared_add_sound
#print axioms NearCompression.power_two_exact_order
#print axioms NearCompression.power_two_order_from_half
#print axioms NearCompression.native_babybear_generator
#print axioms NearCompression.native_babybear_root_eq
#print axioms NearCompression.native_babybear_root_order
#print axioms NearCompression.native_babybear_root_value
#print axioms NearCompression.native_babybear_domain_distinct
#print axioms NearCompression.native_babybear_half_mod
#print axioms NearCompression.native_babybear_period_mod
#print axioms NearCompression.native_babybear_rate_four_value
#print axioms NearCompression.sha384_local_constraint
#print axioms NearCompression.sha384_local_active_boolean
#print axioms NearCompression.sha384_local_first
#print axioms NearCompression.sha384_local_no_restart
#print axioms NearCompression.sha384_local_phase_step
#print axioms NearCompression.sha384_local_active_phase
#print axioms NearCompression.sha384_local_active_prefix
#print axioms NearCompression.sha384_local_inactive_phase
#print axioms NearCompression.sha384_local_tag_step
#print axioms NearCompression.sha384_local_active_tag
#print axioms NearCompression.sha384_local_height_small
#print axioms NearCompression.sha384_local_stop_index
#print axioms NearCompression.sha384_local_required_active
#print axioms NearCompression.sha384_local_capacity
#print axioms NearCompression.sha384_local_active_bounded
#print axioms NearCompression.sha384_local_active_iff
#print axioms NearCompression.sha384_local_segment_metadata
#print axioms NearCompression.sha384_local_gated_constraint
#print axioms NearCompression.sha384_local_pair_holds
#print axioms NearCompression.sha384_local_output
#print axioms NearCompression.sha384_local_recurrence
#print axioms NearCompression.sha384_local_round_holds
#print axioms NearCompression.sha384_local_key_limb
#print axioms NearCompression.sha384_local_key
#print axioms NearCompression.sha384_local_round_segment
#print axioms NearCompression.sha384_local_rounds
#print axioms NearCompression.sha384_local_compression
#print axioms NearCompression.sha384_shared_core_local
#print axioms NearCompression.sha384_shared_compression
#print axioms NearCompression.prepared_locals_read_selected
#print axioms NearCompression.prepared_locals_stack_limb
#print axioms NearCompression.prepared_locals_stack_word_next
#print axioms NearCompression.sparse_lift_polynomial_coefficient
#print axioms NearCompression.recovered_projected_sparse_storage
#print axioms NearCompression.recovered_projected_evaluation
#print axioms NearCompression.prepared_locals_stack_array
#print axioms NearCompression.prepared_locals_success_state
#print axioms NearCompression.prepared_locals_authenticated_flags
#print axioms NearCompression.prepared_locals_setup_success_state
#print axioms NearCompression.prepared_locals_boundary_no_receives
#print axioms NearCompression.prepared_locals_boundary_public_unique
#print axioms NearCompression.prepared_locals_boundary_bound
#print axioms NearCompression.prepared_locals_boundary_gas
#print axioms NearCompression.prepared_locals_entry_frame
#print axioms NearCompression.sha384_shared_receive_match
#print axioms NearCompression.sha384_shared_record_sender
#print axioms NearCompression.sha384_shared_record_mult_active
#print axioms NearCompression.sha384_shared_call_record
#print axioms NearCompression.sha384_shared_use_counts
#print axioms NearCompression.shared_prefix_boolean
#print axioms NearCompression.shared_prefix_first
#print axioms NearCompression.shared_prefix_no_restart
#print axioms NearCompression.shared_prefix_tag_step
#print axioms NearCompression.shared_prefix_tag
#print axioms NearCompression.shared_prefix_stop_last
#print axioms NearCompression.shared_prefix_stop_next
#print axioms NearCompression.shared_prefix_stop_index
#print axioms NearCompression.shared_prefix_required
#print axioms NearCompression.shared_prefix_capacity
#print axioms NearCompression.shared_prefix_bounded
#print axioms NearCompression.shared_prefix_exact
#print axioms NearCompression.shared_prefix_unique
#print axioms NearCompression.sha384_shared_record_prefix
#print axioms NearCompression.sha384_shared_endpoint_prefix
#print axioms NearCompression.prepared_locals_initial
#print axioms NearCompression.prepared_locals_enter
#print axioms NearCompression.prepared_locals_setup_enter
#print axioms NearCompression.diagnostic_ext4_roundtrip
#print axioms NearCompression.diagnostic_ext4_tower_roundtrip
#print axioms NearCompression.diagnostic_ext4_embed_injective
#print axioms NearCompression.diagnostic_ext4_embed_one
#print axioms NearCompression.diagnostic_ext4_embed_mul
#print axioms NearCompression.diagnostic_ext4_embed_pow
#print axioms NearCompression.diagnostic_ext4_root_order
#print axioms NearCompression.diagnostic_ext4_mul_refinement
#print axioms NearCompression.diagnostic_ext4_add_refinement
#print axioms NearCompression.diagnostic_ext4_sub_refinement
#print axioms NearCompression.diagnostic_ext4_domain_embedding
#print axioms NearCompression.diagnostic_ext4_projected_recovery
#print axioms NearCompression.prepared_locals_legacy_specialize_eval
#print axioms NearCompression.prepared_locals_legacy_source_eval
#print axioms NearCompression.prepared_locals_legacy_sp_source
#print axioms NearCompression.prepared_locals_legacy_stack_source
#print axioms NearCompression.prepared_locals_legacy_choice_source
#print axioms NearCompression.prepared_locals_legacy_add_depth_source
#print axioms NearCompression.prepared_locals_legacy_add_carry_source
#print axioms NearCompression.prepared_locals_legacy_stack_depth_source
#print axioms NearCompression.prepared_locals_legacy_projection
#print axioms NearCompression.sha384_shared_node_sender
#print axioms NearCompression.sha384_shared_record_input_active
#print axioms NearCompression.sha384_shared_receive_A
#print axioms NearCompression.sha384_shared_phase_location
#print axioms NearCompression.sha384_shared_record_tag_identifies
#print axioms NearCompression.sha384_shared_core_A
#print axioms NearCompression.sha384_shared_endpoint_A
#print axioms NearCompression.sha384_shared_endpoint_B
#print axioms NearCompression.sha384_shared_endpoint_compression
#print axioms NearCompression.sha384_shared_core_M
#print axioms NearCompression.sha384_shared_record_CD
#print axioms NearCompression.prepared_locals_legacy_add_next_sp
#print axioms NearCompression.prepared_locals_legacy_stack_next_sp
#print axioms NearCompression.prepared_locals_legacy_wasm_add
#print axioms NearCompression.prepared_locals_legacy_wasm_stack
#print axioms NearCompression.prepared_locals_control_decode
#print axioms NearCompression.prepared_locals_setup_add_state
#print axioms NearCompression.prepared_locals_setup_stack_state
#print axioms NearCompression.mobius_lower_zeta
#print axioms NearCompression.recovered_table_coefficients
#print axioms NearCompression.recovered_table_current_next
#print axioms NearCompression.recovered_table_gkr_functional
#print axioms NearCompression.sparse_lift_weight_functional
#print axioms NearCompression.recovered_lifted_functional
#print axioms NearCompression.recovered_lifted_gkr_functional
#print axioms NearCompression.recovered_lifted_heterogeneous_functional
#print axioms NearCompression.prepared_locals_terminal_flags
#print axioms NearCompression.prepared_locals_root_height_zero
#print axioms NearCompression.prepared_locals_root_end_depth
#print axioms NearCompression.prepared_locals_setup_exhaustion
#print axioms NearCompression.prepared_locals_setup_root_end
#print axioms NearCompression.prepared_locals_condition_source
#print axioms NearCompression.prepared_locals_condition
#print axioms NearCompression.joint_representative_shared_functional
#print axioms NearCompression.joint_representative_near_sumcheck_count
#print axioms NearCompression.sha384_shared_record_C_limbs
#print axioms NearCompression.sha384_shared_record_C_words
#print axioms NearCompression.sha384_shared_record_D_fields
#print axioms NearCompression.sha384_shared_digest_decode
#print axioms NearCompression.sha384_shared_record_D_bytes
#print axioms NearCompression.sha384_call_constraint
#print axioms NearCompression.sha384_call_active_boolean
#print axioms NearCompression.sha384_call_first
#print axioms NearCompression.sha384_call_no_restart
#print axioms NearCompression.sha384_call_phase_step
#print axioms NearCompression.sha384_call_active_phase
#print axioms NearCompression.sha384_call_active_prefix
#print axioms NearCompression.sha384_call_inactive_phase
#print axioms NearCompression.sha384_call_tag_step
#print axioms NearCompression.sha384_call_active_tag
#print axioms NearCompression.sha384_call_height_small
#print axioms NearCompression.sha384_call_stop_index
#print axioms NearCompression.sha384_call_stop_last
#print axioms NearCompression.sha384_call_stop_next_inactive
#print axioms NearCompression.sha384_call_required_active
#print axioms NearCompression.sha384_call_capacity
#print axioms NearCompression.sha384_call_active_bounded
#print axioms NearCompression.sha384_call_active_iff
#print axioms NearCompression.sha384_call_segment_metadata
#print axioms NearCompression.sha384_call_initial
#print axioms NearCompression.sha384_call_state_link
#print axioms NearCompression.sha384_call_final_byte
#print axioms NearCompression.sha384_shared_input_projection_eval
#print axioms NearCompression.sha384_shared_message_length
#print axioms NearCompression.sha384_shared_input_bits
#print axioms NearCompression.sha384_shared_message_byte_bound
#print axioms NearCompression.sha384_shared_direct_limb
#print axioms NearCompression.sha384_shared_input_sender
#print axioms NearCompression.sha384_shared_sender_row
#print axioms NearCompression.sha384_shared_input_send_eval
#print axioms NearCompression.sha384_shared_record_A_words
#print axioms NearCompression.sha384_shared_message_bits
#print axioms NearCompression.sha384_shared_record_M_limb
#print axioms NearCompression.sha384_shared_record_M_words
#print axioms NearCompression.sha384_shared_block_receive
#print axioms NearCompression.sha384_shared_call_M
#print axioms NearCompression.sha384_shared_call_padded_limbs
#print axioms NearCompression.shared_flat_words_transfer
#print axioms NearCompression.sha384_shared_call_record_cells
#print axioms NearCompression.sha384_shared_node_tag_unique
#print axioms NearCompression.sha384_shared_call_word_vectors
#print axioms NearCompression.sha384_shared_call_output
#print axioms NearCompression.sha384_paired_limb_bytes
#print axioms NearCompression.sha384_paired_decoded_block
#print axioms NearCompression.sha384_shared_padded_byte_bound
#print axioms NearCompression.sha384_shared_padded_block
#print axioms NearCompression.sha384_shared_call_initial_words
#print axioms NearCompression.sha384_shared_call_link_words
#print axioms NearCompression.sha384_shared_call_final_words
#print axioms NearCompression.sha384_shared_blocks_chain
#print axioms NearCompression.prepared_locals_quiet_stack
#print axioms NearCompression.prepared_locals_quiet_sp
#print axioms NearCompression.prepared_locals_quiet
#print axioms NearCompression.prepared_locals_padding_step
#print axioms NearCompression.prepared_locals_padding_suffix
#print axioms NearCompression.prepared_locals_boundary_stack_word
#print axioms NearCompression.prepared_locals_final_row_published
#print axioms NearCompression.prepared_locals_terminal_published
#print axioms NearCompression.prepared_locals_exec_gas
#print axioms NearCompression.prepared_locals_setup_continue_context
#print axioms NearCompression.prepared_locals_opcode_selected
#print axioms NearCompression.prepared_locals_opcode_exclusive
#print axioms NearCompression.prepared_locals_control_opcode_exclusive
#print axioms NearCompression.prepared_locals_branch_opcode
#print axioms NearCompression.prepared_locals_taken_pc
#print axioms NearCompression.prepared_locals_taken_gates
#print axioms NearCompression.prepared_locals_taken_label
#print axioms NearCompression.prepared_locals_branch_height
#print axioms NearCompression.prepared_locals_taken_sp
#print axioms NearCompression.prepared_locals_taken_stack
#print axioms NearCompression.prepared_locals_taken_stack_projection
#print axioms NearCompression.prepared_locals_untaken_sp
#print axioms NearCompression.prepared_locals_untaken_stack
#print axioms NearCompression.prepared_locals_untaken_stack_projection
#print axioms NearCompression.prepared_locals_untaken_pc_label
#print axioms NearCompression.prepared_locals_branch_height_lt
#print axioms NearCompression.prepared_locals_stack_word_bound
#print axioms NearCompression.prepared_locals_control_array_preserved
#print axioms NearCompression.prepared_locals_setup_untaken_state
#print axioms NearCompression.prepared_locals_setup_taken_state
#print axioms NearCompression.prepared_locals_setup_branch_continue
#print axioms NearCompression.prepared_locals_block_label
#print axioms NearCompression.prepared_locals_nested_end_label
#print axioms NearCompression.prepared_locals_frame_stack
#print axioms NearCompression.prepared_locals_frame_sp
#print axioms NearCompression.prepared_locals_block_state
#print axioms NearCompression.prepared_locals_nested_end_state
#print axioms NearCompression.prepared_locals_setup_block_state
#print axioms NearCompression.prepared_locals_setup_nested_end_state
#print axioms NearCompression.prepared_locals_active_nonlast
#print axioms NearCompression.prepared_locals_execution_run
#print axioms NearCompression.prepared_locals_call_entry
#print axioms NearCompression.prepared_locals_run_call_checked
#print axioms NearCompression.prepared_locals_run_call
#print axioms NearCompression.prepared_locals_witness_final_row
#print axioms NearCompression.prepared_locals_witness_published
#print axioms NearCompression.prepared_locals_public_run_call
#print axioms NearCompression.sha384_shared_call_compression
#print axioms NearCompression.sha384_shared_final_state
#print axioms NearCompression.sha384_shared_message_roundtrip
#print axioms NearCompression.sha384_shared_message_sound
#print axioms NearCompression.recovered_heterogeneous_functional
#print axioms NearCompression.recovered_heterogeneous_near_count
#print axioms NearCompression.row_mle_slot_delta
#print axioms NearCompression.gkr_scatter_functional
#print axioms NearCompression.gkr_scatter_unassigned
#print axioms NearCompression.gkr_scatter_owned
#print axioms NearCompression.metadata_column_coverage
#print axioms NearCompression.packed_column_owner_unique
#print axioms NearCompression.checked_all_lane_supports
#print axioms NearCompression.lane_private_slots_bounds
#print axioms NearCompression.lane_private_slots_weighted_sum
#print axioms NearCompression.recovered_private_vector_functional
#print axioms NearCompression.recovered_private_vector_pcs
#print axioms NearCompression.lane_private_keys_support
#print axioms NearCompression.lane_private_slots_keys
#print axioms NearCompression.lane_private_keys_nodup
#print axioms NearCompression.recovered_private_keys_nodup
#print axioms NearCompression.lane_private_value_covered
#print axioms NearCompression.recovered_private_lane_read
#print axioms NearCompression.canonical_column_decoded_owner
#print axioms NearCompression.gkr_wiring_false_inputs
#print axioms NearCompression.gkr_gamma_transition_bad_count
#print axioms NearCompression.gkr_known_input_subtraction
#print axioms NearCompression.gkr_axis_gate_affine
#print axioms NearCompression.gkr_round_term_eval
#print axioms NearCompression.gkr_round_term_degree
#print axioms NearCompression.gkr_round_term_endpoints
#print axioms NearCompression.gkr_round_polynomial_degree
#print axioms NearCompression.gkr_round_polynomial_eval
#print axioms NearCompression.gkr_round_polynomial_endpoints
#print axioms NearCompression.gkr_honest_round_bad_count
#print axioms NearCompression.gkr_index_selected_value
#print axioms NearCompression.gkr_state_endpoints
#print axioms NearCompression.gkr_advance_contribution
#print axioms NearCompression.gkr_state_advance
#print axioms NearCompression.gkr_state_degree
#print axioms NearCompression.gkr_state_bad_count
#print axioms NearCompression.gkr_round_state_final_append
#print axioms NearCompression.gkr_adaptive_round_count
#print axioms NearCompression.gkr_adaptive_false_persists
#print axioms NearCompression.gkr_adaptive_rounds_count
#print axioms NearCompression.gkr_mle_first_fold
#print axioms NearCompression.gkr_axis_values_mle
#print axioms NearCompression.gkr_axis_term_exact
#print axioms NearCompression.gkr_axis_contribution
#print axioms NearCompression.gkr_left_initial_claim
#print axioms NearCompression.gkr_axis_reset
#print axioms NearCompression.gkr_axes_terminal_wiring
#print axioms NearCompression.gkr_round_history_axis
#print axioms NearCompression.gkr_history_axis_reset
#print axioms NearCompression.gkr_history_terminal_wiring
#print axioms NearCompression.gkr_adaptive_bad_paths_count
#print axioms NearCompression.gkr_two_axes_false_persists
#print axioms NearCompression.gkr_two_axes_gamma_bad_count
#print axioms NearCompression.conditional_scaled_sum
#print axioms NearCompression.two_axis_fresh_budget
#print axioms NearCompression.gkr_layer_repair_count
#print axioms NearCompression.gkr_query_weights_functional
#print axioms NearCompression.gkr_layer_initial_queries
#print axioms NearCompression.gkr_next_queries
#print axioms NearCompression.gkr_root_query
#print axioms NearCompression.terminal_signed_join
#print axioms NearCompression.terminal_signed_pass_sum
#print axioms NearCompression.terminal_signed_pass_length
#print axioms NearCompression.terminal_signed_balance_sum
#print axioms NearCompression.terminal_residual_balance
#print axioms NearCompression.terminal_dag_preserves_earlier
#print axioms NearCompression.terminal_node_value_congr
#print axioms NearCompression.terminal_dag_node_equation
#print axioms NearCompression.terminal_layer_route_values
#print axioms NearCompression.terminal_layer_chain_values
#print axioms NearCompression.terminal_compiled_root
#print axioms NearCompression.terminal_initial_route_values
#print axioms NearCompression.terminal_certified_root

#print axioms NearCompression.chunk_log_bound
#print axioms NearCompression.sha384_chunk_height_small
#print axioms NearCompression.sha384_chunk_core_local
#print axioms NearCompression.sha384_chunk_record_prefix
#print axioms NearCompression.sha384_chunk_endpoint_prefix
#print axioms NearCompression.sha384_chunk_use_prefix
#print axioms NearCompression.sha384_chunk_add_holds
#print axioms NearCompression.sha384_chunk_add_sound

#print axioms NearCompression.prepared_typed_ranges
#print axioms NearCompression.prepared_typed_word_bound
#print axioms NearCompression.prepared_typed_i32_bound
#print axioms NearCompression.prepared_typed_sum_no_wrap
#print axioms NearCompression.prepared_typed_eqz
#print axioms NearCompression.prepared_typed_value_exact
#print axioms NearCompression.prepared_typed_tag_boolean
#print axioms NearCompression.prepared_typed_eqz_shape
#print axioms NearCompression.prepared_typed_eqz_wf

#print axioms NearCompression.prepared_typed_pop_i64
#print axioms NearCompression.prepared_typed_exec_add64
#print axioms NearCompression.prepared_typed_exec_eqz64
#print axioms NearCompression.prepared_typed_exec_const64
#print axioms NearCompression.prepared_typed_step_charge

#print axioms NearCompression.sha384_chunk_receive_match
#print axioms NearCompression.sha384_chunk_record_sender
#print axioms NearCompression.chunk_mult_zero
#print axioms NearCompression.sha384_chunk_record_mult_active
#print axioms NearCompression.sha384_chunk_use_record
#print axioms NearCompression.sha384_chunk_use_counts
#print axioms NearCompression.chunk_global_match

#print axioms NearCompression.terminal_dag_preserves_later
#print axioms NearCompression.terminal_dag_total_equations

#print axioms NearCompression.terminal_arithmetic_route_value
#print axioms NearCompression.terminal_arithmetic_executed

#print axioms NearCompression.terminal_signed_expansion_value
#print axioms NearCompression.terminal_signed_expansion_executed

#print axioms NearCompression.terminal_program_instruction_lower
#print axioms NearCompression.terminal_program_run_lower
#print axioms NearCompression.terminal_program_register_equation

#print axioms NearCompression.terminal_join_route_value
#print axioms NearCompression.terminal_pass_route_value
#print axioms NearCompression.terminal_balance_route_value
#print axioms NearCompression.terminal_rebuilt_expansion_value

#print axioms NearCompression.terminal_rebuild_route_value
#print axioms NearCompression.terminal_program_rebuilt_value

#print axioms NearCompression.sha384_chunk_node_sender
#print axioms NearCompression.sha384_chunk_record_input_active
#print axioms NearCompression.sha384_chunk_receive_A
#print axioms NearCompression.sha384_chunk_phase_location
#print axioms NearCompression.sha384_chunk_record_tag_identifies
#print axioms NearCompression.sha384_chunk_core_A
#print axioms NearCompression.sha384_chunk_endpoint_A
#print axioms NearCompression.sha384_chunk_endpoint_B
#print axioms NearCompression.sha384_chunk_endpoint_compression
#print axioms NearCompression.sha384_chunk_core_M
#print axioms NearCompression.sha384_chunk_record_CD

#print axioms NearCompression.terminal_program_layer_value

#print axioms NearCompression.sha384_chunk_record_C_limbs
#print axioms NearCompression.sha384_chunk_record_C_words
#print axioms NearCompression.sha384_chunk_record_D_fields
#print axioms NearCompression.sha384_chunk_digest_decode
#print axioms NearCompression.sha384_chunk_record_D_bytes
#print axioms NearCompression.sha384_chunk_record_A_words
#print axioms NearCompression.sha384_chunk_message_bits
#print axioms NearCompression.sha384_chunk_record_M_limb
#print axioms NearCompression.sha384_chunk_record_M_words


#print axioms NearCompression.prepared_typed_inspect
#print axioms NearCompression.prepared_typed_target_checked
#print axioms NearCompression.prepared_typed_code_shape
#print axioms NearCompression.prepared_typed_code_entry
#print axioms NearCompression.prepared_typed_entry_checked
#print axioms NearCompression.prepared_typed_setup_checked
#print axioms NearCompression.prepared_typed_local_type

#print axioms NearCompression.sha384_chunk_use_cells
#print axioms NearCompression.sha384_chunk_use_words
#print axioms NearCompression.sha384_chunk_block_byte_bound
#print axioms NearCompression.sha384_chunk_active_use_sound
#print axioms NearCompression.sha384_chunk_declared_use_sound

#print axioms NearCompression.chunk_ordinal_membership
#print axioms NearCompression.chunk_ordinals_nodup
#print axioms NearCompression.chunk_ordinals_ordered
#print axioms NearCompression.chunk_owner_bound
#print axioms NearCompression.chunk_ordinal_location
#print axioms NearCompression.chunk_ordinal_unique
#print axioms NearCompression.chunk_ordinal_coverage
#print axioms NearCompression.chunk_reconstruct_values

#print axioms NearCompression.air_program_route_value
#print axioms NearCompression.terminal_program_total_equations
#print axioms NearCompression.air_program_executed_value

#print axioms NearCompression.air_layer_expression_value

#print axioms NearCompression.prepared_typed_source_boolean
#print axioms NearCompression.prepared_typed_source_limb
#print axioms NearCompression.prepared_typed_source_sp
#print axioms NearCompression.prepared_typed_source_local_type
#print axioms NearCompression.prepared_typed_stack_limb_bound
#print axioms NearCompression.prepared_typed_stack_word_bound

#print axioms NearCompression.adaptive_layer_failures_bounded
#print axioms NearCompression.adaptive_layer_failure_budget

#print axioms NearCompression.chunk_node_count_le
#print axioms NearCompression.chunk_owner_interval
#print axioms NearCompression.chunk_global_local

#print axioms NearCompression.gkr_challenge_block_length
#print axioms NearCompression.gkr_challenge_block_count
#print axioms NearCompression.gkr_challenge_block_repair

#print axioms NearCompression.air_accumulator_route_value
#print axioms NearCompression.air_mix_residuals_value
#print axioms NearCompression.air_program_weighted_finish

#print axioms NearCompression.prepared_typed_stack_upper_zero
#print axioms NearCompression.prepared_typed_stack_i32_bound
#print axioms NearCompression.prepared_typed_stack_value_exact
#print axioms NearCompression.prepared_typed_stack_lookup

#print axioms NearCompression.prepared_typed_selected_limb
#print axioms NearCompression.prepared_typed_selected_sum
#print axioms NearCompression.prepared_typed_source_eqz

#print axioms NearCompression.gkr_strategy_repair_bound

#print axioms NearCompression.chunk_binding_at_ordinal
#print axioms NearCompression.chunk_use_field_transport
#print axioms NearCompression.sha384_chunks_global_use_sound

#print axioms NearCompression.prepared_typed_eqz_selected_type
#print axioms NearCompression.prepared_typed_eqz_operand

#print axioms NearCompression.gkr_adaptive_layer_failures_bounded
#print axioms NearCompression.gkr_adaptive_layers_repair_budget

#print axioms NearCompression.bus_chain_fold_factor
#print axioms NearCompression.bus_aux_chain_final
#print axioms NearCompression.bus_aux_factor
#print axioms NearCompression.bus_boolean_factor
#print axioms NearCompression.bus_bit_constraint_boolean
#print axioms NearCompression.bus_aux_boolean_factor

#print axioms NearCompression.sha384_chunk_repeated_use
#print axioms NearCompression.sha384_chunks_repeated_node_payload

#print axioms NearCompression.gkr_checked_correct_repairs
#print axioms NearCompression.gkr_adjacent_correctness
#print axioms NearCompression.gkr_checked_path_has_repair

#print axioms NearCompression.bus_program_formula_route_value
#print axioms NearCompression.bus_program_formula_executed
#print axioms NearCompression.bus_square_formula_value
#print axioms NearCompression.bus_product_formula_value
#print axioms NearCompression.bus_boundary_formulas_value

#print axioms NearCompression.bus_program_chain_zero
#print axioms NearCompression.bus_executed_chain_zero
#print axioms NearCompression.bus_executed_boundary_zero

#print axioms NearCompression.prepared_typed_opcode_selected

#print axioms NearCompression.prepared_typed_eqz_stack_limb
#print axioms NearCompression.prepared_typed_eqz_stack_tag
#print axioms NearCompression.prepared_typed_eqz_stack_value
#print axioms NearCompression.prepared_typed_eqz_stack_projection

#print axioms NearCompression.sha384_compress_words_congr
#print axioms NearCompression.sha384_exact_block_fold
#print axioms NearCompression.sha384_chunks_canonical_compression
#print axioms NearCompression.sha384_chunks_call_sound

#print axioms NearCompression.terminal_mix_register_values
#print axioms NearCompression.residual_routes_values
#print axioms NearCompression.source_aux_program_value
#print axioms NearCompression.source_aux_terminal_weighted_value

#print axioms NearCompression.terminal_boolean_row_source
#print axioms NearCompression.terminal_boolean_row_residuals

#print axioms NearCompression.gkr_challenge_paths_length
#print axioms NearCompression.gkr_path_repair_count
#print axioms NearCompression.gkr_linked_checked_path_budget

#print axioms NearCompression.sha384_hash_prefix_length
#print axioms NearCompression.sha384_framed_parts_length
#print axioms NearCompression.sha384_hash_frame_length
#print axioms NearCompression.sha384_hash_frame_lengths_exact
#print axioms NearCompression.sha384_hash_frame_digest_transfer

#print axioms NearCompression.gkr_weighted_adjacent_functional
#print axioms NearCompression.gkr_fixed_layer_adjacent_correctness

#print axioms NearCompression.prepared_typed_bus_mult_zero
#print axioms NearCompression.prepared_typed_bus_receive_active
#print axioms NearCompression.prepared_typed_bus_receive_count
#print axioms NearCompression.prepared_typed_bus_fetch_matched
#print axioms NearCompression.prepared_typed_bus_no_public_table_receives
#print axioms NearCompression.prepared_typed_bus_public_count_record
#print axioms NearCompression.prepared_typed_bus_published
#print axioms NearCompression.prepared_typed_bus_table_local
#print axioms NearCompression.prepared_typed_bus_fetch_authenticated
#print axioms NearCompression.prepared_typed_bus_message_pc
#print axioms NearCompression.prepared_typed_bus_fetch_at_pc
#print axioms NearCompression.prepared_typed_bus_literal_air
#print axioms NearCompression.prepared_typed_bus_literal_boolean
#print axioms NearCompression.prepared_typed_bus_literal_order
#print axioms NearCompression.prepared_typed_bus_literal_inactive
#print axioms NearCompression.prepared_typed_literal_fetch

#print axioms NearCompression.prepared_typed_public_record_field
#print axioms NearCompression.prepared_typed_record_pc
#print axioms NearCompression.prepared_typed_authenticated_fetch
#print axioms NearCompression.prepared_typed_authenticated_fee
#print axioms NearCompression.prepared_typed_setup_authenticated_fee

#print axioms NearCompression.prepared_typed_literal_limb
#print axioms NearCompression.prepared_typed_sequential_pc
#print axioms NearCompression.prepared_typed_continue_status
#print axioms NearCompression.prepared_typed_label_equations
#print axioms NearCompression.prepared_typed_pc_label

#print axioms NearCompression.prepared_typed_gas_source

#print axioms NearCompression.prepared_typed_eqz_depth

#print axioms NearCompression.prepared_typed_local_preserve
#print axioms NearCompression.prepared_typed_local_value_preserve
#print axioms NearCompression.prepared_typed_local_array_preserve

#print axioms NearCompression.prepared_typed_stack_succ
#print axioms NearCompression.prepared_typed_stack_congr
#print axioms NearCompression.prepared_typed_eqz_arrays

#print axioms NearCompression.prepared_typed_eqz_success_state

#print axioms NearCompression.prepared_typed_exec_local
#print axioms NearCompression.prepared_typed_authenticated_eqz
#print axioms NearCompression.prepared_typed_setup_eqz_state

#print axioms NearCompression.sha384_read_parts_append
#print axioms NearCompression.sha384_read_frame_append
#print axioms NearCompression.sha384_decode_frame_encode
#print axioms NearCompression.sha384_hash_frame_injective
#print axioms NearCompression.sha384_decode_frame_trailing

#print axioms NearCompression.gkr_circuit_path_linked
#print axioms NearCompression.gkr_circuit_checked_path_budget

#print axioms NearCompression.gkr_root_output_wrong
#print axioms NearCompression.gkr_false_output_path_budget

#print axioms NearCompression.sha384_read_parts_sound
#print axioms NearCompression.sha384_read_frame_sound
#print axioms NearCompression.sha384_decode_frame_sound
#print axioms NearCompression.sha384_chunks_decoded_call_sound

#print axioms NearCompression.gkr_remove_constants_exact
#print axioms NearCompression.gkr_recovered_terminal_iff

#print axioms NearCompression.prepared_typed_boundary_record
#print axioms NearCompression.prepared_typed_boundary_no_receives
#print axioms NearCompression.prepared_typed_boundary_public_unique
#print axioms NearCompression.prepared_typed_boundary_bound
#print axioms NearCompression.prepared_typed_boundary_gas

#print axioms NearCompression.prepared_typed_initial_local_bit
#print axioms NearCompression.prepared_typed_initial_local_limb
#print axioms NearCompression.prepared_typed_initial_local_word
#print axioms NearCompression.prepared_typed_entry_frame

#print axioms NearCompression.prepared_typed_initial
#print axioms NearCompression.prepared_typed_enter
#print axioms NearCompression.prepared_typed_setup_enter

#print axioms NearCompression.sha384_commit_operand_check
#print axioms NearCompression.sha384_commit_operand_positions
#print axioms NearCompression.sha384_chunks_transcript_commit

#print axioms NearCompression.prepared_typed_const_stack_limb
#print axioms NearCompression.prepared_typed_const_stack_tag
#print axioms NearCompression.prepared_typed_const_stack_value

#print axioms NearCompression.prepared_typed_const_depth

#print axioms NearCompression.prepared_typed_const_success_state

#print axioms NearCompression.prepared_typed_authenticated_const
#print axioms NearCompression.prepared_typed_setup_const_state

#print axioms NearCompression.gkr_verifier_path_split
#print axioms NearCompression.gkr_verifier_terminal_error_budget

#print axioms NearCompression.prepared_typed_terminal_flags
#print axioms NearCompression.prepared_typed_root_height_zero
#print axioms NearCompression.prepared_typed_root_end_depth
#print axioms NearCompression.prepared_typed_setup_exhaustion
#print axioms NearCompression.prepared_typed_setup_root_end

#print axioms NearCompression.prepared_typed_quiet_stack_limb
#print axioms NearCompression.prepared_typed_quiet_stack_tag
#print axioms NearCompression.prepared_typed_quiet_stack_value

#print axioms NearCompression.prepared_typed_quiet_depth
#print axioms NearCompression.prepared_typed_quiet_pc_labels

#print axioms NearCompression.prepared_typed_quiet_local_limb
#print axioms NearCompression.prepared_typed_quiet_local_value
#print axioms NearCompression.prepared_typed_quiet_local_array

#print axioms NearCompression.prepared_typed_padding_step
#print axioms NearCompression.prepared_typed_snapshot_refl
#print axioms NearCompression.prepared_typed_snapshot_trans
#print axioms NearCompression.prepared_typed_padding_suffix
#print axioms NearCompression.prepared_typed_snapshot_value
#print axioms NearCompression.prepared_typed_snapshot_state

#print axioms NearCompression.prepared_typed_exec_gas
#print axioms NearCompression.prepared_typed_setup_continue_context

#print axioms NearCompression.prepared_typed_exit_flags
#print axioms NearCompression.prepared_typed_done_public_exit

#print axioms NearCompression.sha384_sample_limit_exact
#print axioms NearCompression.sha384_accept_word_some
#print axioms NearCompression.sha384_accept_word_none
#print axioms NearCompression.sha384_accept_word_range
#print axioms NearCompression.sha384_scan_values_range
#print axioms NearCompression.sha384_scan_done_length
#print axioms NearCompression.sha384_draw_failure_preserves_seed
#print axioms NearCompression.sha384_digest_words_shape
#print axioms NearCompression.sha384_scan_length_le
#print axioms NearCompression.sha384_draw_loop_range
#print axioms NearCompression.sha384_draw_loop_length
#print axioms NearCompression.sha384_draw_values_range
#print axioms NearCompression.sha384_draw_values_length
#print axioms NearCompression.sha384_accept_word_preimages

#print axioms NearCompression.prepared_typed_setup_exhaustion_snapshot

#print axioms NearCompression.sha384_scan_consumed_bound
#print axioms NearCompression.sha384_draw_loop_budget
#print axioms NearCompression.sha384_draw_request_budget

#print axioms NearCompression.prepared_typed_add_selected_types
#print axioms NearCompression.prepared_typed_add_operands

#print axioms NearCompression.prepared_typed_add_selection
#print axioms NearCompression.prepared_typed_add_field_equation
#print axioms NearCompression.prepared_typed_result_bound
#print axioms NearCompression.prepared_typed_carry_bound
#print axioms NearCompression.prepared_typed_add_nat_equation
#print axioms NearCompression.prepared_typed_add_binop

#print axioms NearCompression.prepared_typed_add_stack_limb
#print axioms NearCompression.prepared_typed_add_stack_tag
#print axioms NearCompression.prepared_typed_add_stack_value

#print axioms NearCompression.prepared_typed_add_depth

#print axioms NearCompression.prepared_typed_add_success_state

#print axioms NearCompression.prepared_typed_authenticated_add
#print axioms NearCompression.prepared_typed_setup_add_state

#print axioms NearCompression.prepared_typed_local_selected
#print axioms NearCompression.prepared_typed_local_index

#print axioms NearCompression.prepared_typed_local_limb_step
#print axioms NearCompression.prepared_typed_selected_type_eval
#print axioms NearCompression.prepared_typed_store_type
#print axioms NearCompression.prepared_typed_local_store_value

#print axioms NearCompression.prepared_typed_local_depth

#print axioms NearCompression.gkr_terminal_recovered_near_count

#print axioms NearCompression.sha384_merkle_query_binding
#print axioms NearCompression.sha384_merkle_conflicting_openings
#print axioms NearCompression.sha384_merkle_fold_query_count
#print axioms NearCompression.sha384_merkle_path_query_count

#print axioms NearCompression.prepared_typed_const32_stack_limb
#print axioms NearCompression.prepared_typed_const32_stack_tag
#print axioms NearCompression.prepared_typed_const32_stack_value

#print axioms NearCompression.prepared_typed_const32_depth

#print axioms NearCompression.prepared_typed_const32_success_state

#print axioms NearCompression.prepared_typed_authenticated_const32
#print axioms NearCompression.prepared_typed_setup_const32_state

#print axioms NearCompression.prepared_typed_drop_stack_limb
#print axioms NearCompression.prepared_typed_drop_stack_tag
#print axioms NearCompression.prepared_typed_drop_stack_value

#print axioms NearCompression.prepared_typed_drop_depth

#print axioms NearCompression.prepared_typed_drop_success_state

#print axioms NearCompression.prepared_typed_authenticated_drop
#print axioms NearCompression.prepared_typed_setup_drop_state

#print axioms NearCompression.prepared_typed_add32_selected_types

#print axioms NearCompression.prepared_typed_add32_operands

#print axioms NearCompression.prepared_typed_add32_field_equation

#print axioms NearCompression.prepared_typed_add32_nat_equation

#print axioms NearCompression.prepared_typed_add32_upper_zero

#print axioms NearCompression.prepared_typed_add32_binop

#print axioms NearCompression.prepared_typed_add32_stack_limb

#print axioms NearCompression.prepared_typed_add32_stack_tag

#print axioms NearCompression.prepared_typed_add32_stack_value

#print axioms NearCompression.prepared_typed_add32_depth

#print axioms NearCompression.prepared_typed_add32_success_state

#print axioms NearCompression.prepared_typed_authenticated_add32

#print axioms NearCompression.prepared_typed_setup_add32_state

#print axioms NearCompression.prepared_typed_local_lookup

#print axioms NearCompression.prepared_typed_local_array_set

#print axioms NearCompression.prepared_typed_local_array_write

#print axioms NearCompression.prepared_typed_selected_local_eval

#print axioms NearCompression.prepared_typed_local_stack_limb

#print axioms NearCompression.prepared_typed_local_stack_tag

#print axioms NearCompression.prepared_typed_local_stack_value

#print axioms NearCompression.prepared_typed_local_stack_arrays

#print axioms NearCompression.prepared_typed_local_get_state

#print axioms NearCompression.prepared_typed_authenticated_local_get

#print axioms NearCompression.prepared_typed_setup_local_get_state

#print axioms NearCompression.sha384_tree_value_width

#print axioms NearCompression.sha384_tree_path_shape

#print axioms NearCompression.sha384_tree_path_fold

#print axioms NearCompression.sha384_source_constructed_root

#print axioms NearCompression.sha384_source_path_accepts

#print axioms NearCompression.sha384_fixed_source_opening

#print axioms NearCompression.prepared_typed_local_set_state

#print axioms NearCompression.prepared_typed_local_tee_state

#print axioms NearCompression.prepared_typed_authenticated_local_set

#print axioms NearCompression.prepared_typed_setup_local_set_state

#print axioms NearCompression.prepared_typed_authenticated_local_tee

#print axioms NearCompression.prepared_typed_setup_local_tee_state

#print axioms NearCompression.prepared_typed_opcode_total

#print axioms NearCompression.prepared_typed_table_active_nonlast

#print axioms NearCompression.prepared_typed_active_nonlast

#print axioms NearCompression.prepared_typed_run_call_checked

#print axioms NearCompression.prepared_typed_exhaustion_public_exit

#print axioms NearCompression.prepared_typed_root_end_public_exit

#print axioms NearCompression.prepared_typed_block_label

#print axioms NearCompression.prepared_typed_nested_end_label

#print axioms NearCompression.prepared_typed_frame_stack_limb

#print axioms NearCompression.prepared_typed_frame_stack_tag

#print axioms NearCompression.prepared_typed_frame_stack_value

#print axioms NearCompression.prepared_typed_frame_depth

#print axioms NearCompression.prepared_typed_block_state

#print axioms NearCompression.prepared_typed_nested_end_state

#print axioms NearCompression.prepared_typed_setup_block_state

#print axioms NearCompression.prepared_typed_setup_nested_end_state

#print axioms NearCompression.sha384_field_words_length

#print axioms NearCompression.sha384_field_words_read

#print axioms NearCompression.sha384_field_words_injective

#print axioms NearCompression.sha384_fixed_source_words

#print axioms NearCompression.sha384_fixed_source_projected_pair

#print axioms NearCompression.prepared_typed_witness_published

#print axioms NearCompression.sha384_fp_pair_words_length

#print axioms NearCompression.sha384_fp_pair_words_canonical

#print axioms NearCompression.sha384_fp_pair_words_roundtrip

#print axioms NearCompression.sha384_computed_source_decodes

#print axioms NearCompression.sha384_authenticated_computed_source

#print axioms NearCompression.prepared_typed_condition_source

#print axioms NearCompression.prepared_typed_branch_operand

#print axioms NearCompression.prepared_typed_branch_opcode

#print axioms NearCompression.prepared_typed_taken_pc

#print axioms NearCompression.prepared_typed_taken_gates

#print axioms NearCompression.prepared_typed_taken_label

#print axioms NearCompression.prepared_typed_branch_present

#print axioms NearCompression.prepared_typed_branch_height_lt

#print axioms NearCompression.prepared_typed_branch_stack_limb

#print axioms NearCompression.prepared_typed_branch_stack_tag

#print axioms NearCompression.prepared_typed_branch_stack_value

#print axioms NearCompression.prepared_typed_branch_depth

#print axioms NearCompression.prepared_typed_untaken_pc_label

#print axioms NearCompression.prepared_typed_stack_extract

#print axioms NearCompression.prepared_typed_stack_i32_word

#print axioms NearCompression.prepared_typed_branch_array

#print axioms NearCompression.prepared_typed_boundary_stack_value

#print axioms NearCompression.prepared_typed_boundary_stack

#print axioms NearCompression.prepared_typed_done_public_stack

#print axioms NearCompression.prepared_typed_branch_state

#print axioms NearCompression.prepared_typed_setup_branch_continue

#print axioms NearCompression.prepared_typed_execution_run_indexed

#print axioms NearCompression.prepared_typed_execution_run

#print axioms NearCompression.prepared_typed_call_entry_indexed

#print axioms NearCompression.prepared_typed_call_entry

#print axioms NearCompression.prepared_typed_run_call_indexed

#print axioms NearCompression.prepared_typed_run_call

#print axioms NearCompression.prepared_typed_public_run_call

#print axioms NearCompression.prepared_typed_sync_stack

#print axioms NearCompression.prepared_typed_exhaustion_public_stack

#print axioms NearCompression.prepared_typed_root_end_public_stack

#print axioms NearCompression.sha384_packing_field_bounds

#print axioms NearCompression.sha384_u64_words_length

#print axioms NearCompression.sha384_u64_words_read

#print axioms NearCompression.sha384_packing_context_length

#print axioms NearCompression.sha384_packing_context_fields

#print axioms NearCompression.sha384_packing_context_injective

#print axioms NearCompression.sha384_packing_root_field

#print axioms NearCompression.sha384_native_packed_half

#print axioms NearCompression.sha384_authenticated_native_packed_source

#print axioms NearCompression.prepared_typed_witness_stack

#print axioms NearCompression.prepared_typed_public_stack_run_call

#print axioms NearCompression.prepared_scalar_read_exact

#print axioms NearCompression.prepared_scalar_write_exact

#print axioms NearCompression.prepared_scalar_store_checked

#print axioms NearCompression.prepared_memory_load_exec

#print axioms NearCompression.prepared_memory_store_i32_exec

#print axioms NearCompression.prepared_memory_store_i64_exec

#print axioms NearCompression.prepared_memory_store_i64_commitment

#print axioms NearCompression.sha384_evaluated_source_words

#print axioms NearCompression.sha384_evaluated_source

#print axioms NearCompression.sha384_word_pairs_lift

#print axioms NearCompression.sha384_native_projected_word_pair

#print axioms NearCompression.prepared_memory_read_checked

#print axioms NearCompression.prepared_memory_load_checked

#print axioms NearCompression.prepared_memory_service_clocks

#print axioms NearCompression.prepared_memory_service_checked

#print axioms NearCompression.diagnostic_ext4_embed_zero

#print axioms NearCompression.diagnostic_ext4_embed_add

#print axioms NearCompression.diagnostic_ext4_embed_neg

#print axioms NearCompression.diagnostic_ext4_embed_sub

#print axioms NearCompression.diagnostic_ext4_embed_word

#print axioms NearCompression.diagnostic_ext4_embed_nat

#print axioms NearCompression.diagnostic_ext4_characteristic

#print axioms NearCompression.diagnostic_ext4_polynomial_eval

#print axioms NearCompression.diagnostic_ext4_mobius

#print axioms NearCompression.diagnostic_ext4_packed_values

#print axioms NearCompression.diagnostic_ext4_packed_polynomial

#print axioms NearCompression.diagnostic_ext4_packed_eval

#print axioms NearCompression.diagnostic_ext4_source_pair

#print axioms NearCompression.sha384_native_ext4_projected_pair

#print axioms NearCompression.prepared_memory_mixed_clocks

#print axioms NearCompression.prepared_memory_mixed_checked

#print axioms NearCompression.joint_source_representative_unique

#print axioms NearCompression.joint_source_normal_form_unique

#print axioms NearCompression.recovered_table_of_coefficient_identity

#print axioms NearCompression.chosen_joint_source_representative_valid

#print axioms NearCompression.prepared_memory_address_boolean

#print axioms NearCompression.prepared_memory_address_limb_bound

#print axioms NearCompression.prepared_memory_address_exact

#print axioms NearCompression.joint_source_entries_sparse

#print axioms NearCompression.chosen_gkr_terminal_near_count

#print axioms NearCompression.rate_four_unique_separation

#print axioms NearCompression.rate_four_unique_minimum

#print axioms NearCompression.rate_four_far_minimum

#print axioms NearCompression.rate_four_joint_minimum

#print axioms NearCompression.prepared_memory_bounds_opcode

#print axioms NearCompression.prepared_memory_bounds_success

#print axioms NearCompression.prepared_memory_literal_bounds

#print axioms NearCompression.recursive_residual_complete
#print axioms NearCompression.recursive_residual_false_zero_count

#print axioms NearCompression.prepared_memory_sign_extension

#print axioms NearCompression.prepared_memory_result_bits

#print axioms NearCompression.prepared_memory_raw_high_zero

#print axioms NearCompression.prepared_memory_store_raw_bits

#print axioms NearCompression.prepared_memory_bits_prefix

#print axioms NearCompression.prepared_memory_bits_mod

#print axioms NearCompression.prepared_memory_store_word

#print axioms NearCompression.prepared_memory_load_spec

#print axioms NearCompression.prepared_memory_unsigned_word

#print axioms NearCompression.prepared_memory_unsigned_value

#print axioms NearCompression.prepared_memory_raw_prefix

#print axioms NearCompression.prepared_memory_signed_word

#print axioms NearCompression.prepared_memory_load_value

#print axioms NearCompression.weighted_replay_scale_loop

#print axioms NearCompression.weighted_replay_parent_weights

#print axioms NearCompression.weighted_replay_next_weights

#print axioms NearCompression.weighted_replay_initial_weights

#print axioms NearCompression.weighted_replay_terminal_weights

#print axioms NearCompression.weighted_replay_sent_degree

#print axioms NearCompression.weighted_replay_transcript_checks

#print axioms NearCompression.weighted_replay_candidate_or_bad

#print axioms NearCompression.rate_four_fold_minimum

#print axioms NearCompression.rate_four_complete_regime

#print axioms NearCompression.prepared_memory_address_uint32

#print axioms NearCompression.prepared_memory_load_service_exec

#print axioms NearCompression.prepared_memory_store_exec_row

#print axioms NearCompression.prepared_memory_store_service_exec

#print axioms NearCompression.weighted_replay_initial_candidate

#print axioms NearCompression.weighted_replay_no_candidate_count

#print axioms NearCompression.weighted_prefix_oracle
#print axioms NearCompression.weighted_prefix_source
#print axioms NearCompression.weighted_prefix_check
#print axioms NearCompression.weighted_prefix_mass
#print axioms NearCompression.weighted_prefix_snapshot
#print axioms NearCompression.weighted_prefix_no_candidate_count

#print axioms NearCompression.recursive_operand_reconstruct
#print axioms NearCompression.recursive_operand_weighted
#print axioms NearCompression.recursive_operand_functional

#print axioms NearCompression.prepared_memory_sender_boolean
#print axioms NearCompression.prepared_memory_sender_sp
#print axioms NearCompression.prepared_memory_sender_top_selected
#print axioms NearCompression.prepared_memory_sender_second_selected
#print axioms NearCompression.prepared_memory_sender_opcode
#print axioms NearCompression.prepared_memory_sender_write_selected
#print axioms NearCompression.prepared_memory_sender_store_depth
#print axioms NearCompression.prepared_memory_sender_value_message
#print axioms NearCompression.prepared_memory_sender_address_message
#print axioms NearCompression.prepared_memory_sender_operands
#print axioms NearCompression.prepared_memory_sender_i32_high
#print axioms NearCompression.prepared_memory_sender_address_type
#print axioms NearCompression.prepared_memory_sender_store_type

#print axioms NearCompression.ext8_base_pow
#print axioms NearCompression.ext8_native_root_order
#print axioms NearCompression.ext8_replay_extraction_227
#print axioms NearCompression.ext8_replay_extraction_not_228
#print axioms NearCompression.ext8_replay_314_budget

#print axioms NearCompression.recursive_operand_weight_split
#print axioms NearCompression.recursive_operand_zero_weight
#print axioms NearCompression.recursive_operand_weight_high_zero
#print axioms NearCompression.recursive_operand_padded_mle
#print axioms NearCompression.recursive_operand_group_mle
#print axioms NearCompression.recursive_operand_packed_slot
#print axioms NearCompression.recursive_operand_column_functional
#print axioms NearCompression.recursive_operand_branches_functional

#print axioms NearCompression.prepared_memory_limb_nat
#print axioms NearCompression.prepared_memory_word_limbs
#print axioms NearCompression.prepared_memory_word_of_limb_eq
#print axioms NearCompression.prepared_memory_message_field
#print axioms NearCompression.prepared_memory_message_opcode
#print axioms NearCompression.prepared_memory_message_address
#print axioms NearCompression.prepared_memory_message_store_value
#print axioms NearCompression.prepared_memory_matched_operands
#print axioms NearCompression.prepared_memory_message_offset
#print axioms NearCompression.prepared_memory_message_result
#print axioms NearCompression.prepared_memory_message_clock
#print axioms NearCompression.prepared_memory_attached_load_exec
#print axioms NearCompression.prepared_memory_attached_store_exec

#print axioms NearCompression.recursive_fixed_slot_coverage
#print axioms NearCompression.recursive_free_operand_exact
#print axioms NearCompression.recursive_fold_fixed_coverage
#print axioms NearCompression.recursive_source_fixed_coverage
#print axioms NearCompression.recursive_fixed_residuals_zero_iff
#print axioms NearCompression.recursive_arithmetic_zero_relations
#print axioms NearCompression.recursive_bad_fixed_escape_count
#print axioms NearCompression.recursive_fixed_residual_length_bound
#print axioms NearCompression.recursive_single_root_fixed_escape_count
#print axioms NearCompression.recursive_single_root_zero_semantics
#print axioms NearCompression.recursive_single_root_same_vector_escape_count

#print axioms NearCompression.recursive_source_route_value
#print axioms NearCompression.recursive_source_route_executed
#print axioms NearCompression.recursive_source_lane_eval
#print axioms NearCompression.recursive_source_query_eval
#print axioms NearCompression.recursive_source_output_eval
#print axioms NearCompression.recursive_source_program_length
#print axioms NearCompression.recursive_source_output_executed
#print axioms NearCompression.recursive_source_program_fixed_escape
#print axioms NearCompression.recursive_source_program_residuals

#print axioms NearCompression.ext8_operand_reconstruct
#print axioms NearCompression.ext8_operand_weighted
#print axioms NearCompression.ext8_operand_column_functional
#print axioms NearCompression.ext8_operand_branches_functional

#print axioms NearCompression.rate_shift_mixing_completeness
#print axioms NearCompression.rate_shift_mixing_error
#print axioms NearCompression.rate_shift_fixed_candidate_bad_count

#print axioms NearCompression.prepared_memory_sender_stack_lookup

#print axioms NearCompression.prepared_memory_sender_stack_push

#print axioms NearCompression.prepared_memory_sender_stack_value_exact

#print axioms NearCompression.prepared_memory_sender_stack_address

#print axioms NearCompression.prepared_memory_sender_stack_stored

#print axioms NearCompression.prepared_memory_sender_load_input

#print axioms NearCompression.prepared_memory_sender_store_input

#print axioms NearCompression.recursive_shared_lane_acyclic

#print axioms NearCompression.recursive_shared_lane_value

#print axioms NearCompression.recursive_shared_run_append

#print axioms NearCompression.recursive_shared_acyclic_append

#print axioms NearCompression.recursive_shared_lane_program_length

#print axioms NearCompression.recursive_shared_lane_index_bound

#print axioms NearCompression.recursive_shared_lane_program_acyclic

#print axioms NearCompression.recursive_shared_lane_program_value

#print axioms NearCompression.rate_shift_monomial_weights_length

#print axioms NearCompression.rate_shift_monomial_weights_coordinate

#print axioms NearCompression.rate_shift_monomial_dot

#print axioms NearCompression.rate_shift_add_weights_length

#print axioms NearCompression.rate_shift_add_weights_dot

#print axioms NearCompression.rate_shift_accumulated_weights_functional

#print axioms NearCompression.rate_shift_list_mixing_bound

#print axioms NearCompression.rate_shift_close_unique

#print axioms NearCompression.rate_shift_unique_list_length

#print axioms NearCompression.rate_shift_unique_list_complete

#print axioms NearCompression.rate_shift_unique_mixing_bound

#print axioms NearCompression.general_fold_weights_functional

#print axioms NearCompression.general_fold_residual_eval

#print axioms NearCompression.general_fold_residual_endpoints

#print axioms NearCompression.general_shared_curve_extraction

#print axioms NearCompression.general_weighted_unique_extraction

#print axioms NearCompression.general_weighted_extraction_count

#print axioms NearCompression.general_weighted_extraction_bad_count

#print axioms NearCompression.general_residual_interleaved

#print axioms NearCompression.general_indexed_parent

#print axioms NearCompression.general_indexed_fold_bad_count

#print axioms NearCompression.general_indexed_unique_extraction

#print axioms NearCompression.general_indexed_unique_bad_count

#print axioms NearCompression.general_indexed_child_implies_success

#print axioms NearCompression.general_indexed_outcome_implies_parent

#print axioms NearCompression.general_chain_query_bound_outside_bad

#print axioms NearCompression.general_global_chain_bad_count

#print axioms NearCompression.general_interactive_fold_soundness

#print axioms NearCompression.general_checked_fold_reject_prefix

#print axioms NearCompression.general_checked_fold_reject_terminal

#print axioms NearCompression.general_checked_interactive_fold_soundness

#print axioms NearCompression.rate_shift_normalize_length

#print axioms NearCompression.rate_shift_normalize_coeff

#print axioms NearCompression.rate_shift_normalize_eval

#print axioms NearCompression.rate_shift_continuation_candidate

#print axioms NearCompression.rate_shift_indexed_candidate

#print axioms NearCompression.rate_shift_continuation_composition

#print axioms NearCompression.rate_shift_unmixed_constraints

#print axioms NearCompression.rate_shift_query_family_bound

#print axioms NearCompression.rate_shift_query_no_correct_bound

#print axioms NearCompression.virtual_fold_consistency

#print axioms NearCompression.general_chain_no_candidate_outside_bad

#print axioms NearCompression.virtual_fold_weight_exact

#print axioms NearCompression.virtual_fold_insufficient_agreement

#print axioms NearCompression.virtual_weights_prefix

#print axioms NearCompression.virtual_oracles_prefix

#print axioms NearCompression.virtual_snapshot_prefix

#print axioms NearCompression.virtual_prefix_bad_path_bound

#print axioms NearCompression.virtual_prefix_no_bad_transitions

#print axioms NearCompression.virtual_prefix_weight_length

#print axioms NearCompression.virtual_prefix_weight_layout

#print axioms NearCompression.virtual_prefix_checked_absence

#print axioms NearCompression.virtual_prefix_checked_no_close

#print axioms NearCompression.rate_shift_unique_list_sound

#print axioms NearCompression.checked_virtual_source_query_bound

#print axioms NearCompression.checked_virtual_source_stage_bound

#print axioms NearCompression.checked_rate_shift_composition

#print axioms NearCompression.general_list_curve_extraction_bad_count

#print axioms NearCompression.list_curve_candidate_identity

#print axioms NearCompression.finite_agreement_list_bound
#print axioms NearCompression.finite_rs_johnson_list_bound
#print axioms NearCompression.finite_rs_johnson_gap_bound

#print axioms NearCompression.johnson_candidate_list_sound
#print axioms NearCompression.johnson_candidate_list_complete
#print axioms NearCompression.johnson_candidate_list_distinct
#print axioms NearCompression.johnson_candidate_list_gap_bound

#print axioms NearCompression.bus_joint_challenge_bound

#print axioms NearCompression.bus_tagged_padding_injective

#print axioms NearCompression.bus_tagged_fingerprint

#print axioms NearCompression.bus_tagged_joint_challenge_bound

#print axioms NearCompression.bus_trace_messages_count

#print axioms NearCompression.bus_trace_balance_iff_perm

#print axioms NearCompression.bus_trace_unbalanced_not_perm

#print axioms NearCompression.bus_encode_message_injective

#print axioms NearCompression.bus_trace_joint_challenge_bound

#print axioms NearCompression.bus_fp8_encoding_conditions

#print axioms NearCompression.bus_trace_fp8_joint_bound

#print axioms NearCompression.bus_trace_support_covers

#print axioms NearCompression.bus_trace_support_length

#print axioms NearCompression.bus_trace_support_shape

#print axioms NearCompression.bus_trace_supported_fp8_bound

#print axioms NearCompression.bus_interaction_multiplicity_bound

#print axioms NearCompression.bus_trace_mass_bound

#print axioms NearCompression.bus_trace_budget_fp8_bound

#print axioms NearCompression.prepared_literal_bus_source_shape

#print axioms NearCompression.prepared_literal_bus_public_shape

#print axioms NearCompression.prepared_literal_bus_joint_bound

#print axioms NearCompression.prepared_literal_wrong_output_bus_bound

#print axioms NearCompression.air_mix_value_power_batch

#print axioms NearCompression.air_residual_batch_zero_count

#print axioms NearCompression.air_equality_weighted_mle

#print axioms NearCompression.air_cube_boolean_congr

#print axioms NearCompression.air_equality_weighted_target

#print axioms NearCompression.air_weighted_target_zero_count

#print axioms NearCompression.air_row_mle_expression_boolean

#print axioms NearCompression.air_source_batch_boolean

#print axioms NearCompression.air_source_weighted_target

#print axioms NearCompression.air_source_weighted_zero_count

#print axioms NearCompression.air_first_selector_product

#print axioms NearCompression.air_last_selector_product

#print axioms NearCompression.air_transition_selector_product

#print axioms NearCompression.air_product_selector_env

#print axioms NearCompression.air_product_selector_expression_boolean

#print axioms NearCompression.air_expression_ext8_lift

#print axioms NearCompression.air_ext8_product_expression_boolean

#print axioms NearCompression.air_boolean_mle_value

#print axioms NearCompression.bus_formula_boolean_row

#print axioms NearCompression.air_combined_residual_boolean

#print axioms NearCompression.air_combined_weighted_zero_count

#print axioms NearCompression.air_aux_coordinate_column

#print axioms NearCompression.air_aux_coordinate_environment

#print axioms NearCompression.air_aux_coordinate_formula_boolean

#print axioms NearCompression.air_aux_coordinate_source_eval

#print axioms NearCompression.bus_chain_layout_columns

#print axioms NearCompression.bus_chain_layout_lengths

#print axioms NearCompression.bus_chain_layout_zero

#print axioms NearCompression.bus_interaction_layout_factor
#print axioms NearCompression.bus_interaction_layout_length
#print axioms NearCompression.bus_interaction_residuals_zero

#print axioms NearCompression.bus_interaction_layout_product

#print axioms NearCompression.bus_table_allocation_sources
#print axioms NearCompression.bus_table_chain_length
#print axioms NearCompression.bus_table_group_permutation
#print axioms NearCompression.bus_table_binding_pairs
#print axioms NearCompression.bus_table_interaction_residual_mem
#print axioms NearCompression.bus_table_layout_product

#print axioms NearCompression.bus_source_formula_value
#print axioms NearCompression.bus_tagged_formula_value
#print axioms NearCompression.bus_lowered_interaction_values
#print axioms NearCompression.bus_source_formula_row
#print axioms NearCompression.bus_source_interaction_factor

#print axioms NearCompression.bus_source_table_product

#print axioms NearCompression.bus_value_factor
#print axioms NearCompression.bus_value_multiplicity_source
#print axioms NearCompression.bus_source_natural_factor
#print axioms NearCompression.bus_table_source_bits
#print axioms NearCompression.bus_source_factor_expanded
#print axioms NearCompression.bus_source_table_natural_product

#print axioms NearCompression.bus_expanded_row_product
#print axioms NearCompression.bus_expanded_table_product
#print axioms NearCompression.bus_expanded_tables_product
#print axioms NearCompression.bus_expanded_global_product
#print axioms NearCompression.bus_global_side_fp8_bound

#print axioms NearCompression.bus_bound_side_formula_product
#print axioms NearCompression.bus_bound_side_natural_product
#print axioms NearCompression.bus_bound_tables_natural_product
#print axioms NearCompression.bus_bound_global_product

#print axioms NearCompression.bus_ext8_coordinate_mult
#print axioms NearCompression.bus_ext8_coordinate_message
#print axioms NearCompression.bus_ext8_coordinate_final
#print axioms NearCompression.bus_ext8_bound_side_product
#print axioms NearCompression.bus_ext8_bound_tables_product
#print axioms NearCompression.bus_ext8_claimed_global_product

#print axioms NearCompression.bus_attached_source_eval
#print axioms NearCompression.bus_attached_source_interaction
#print axioms NearCompression.bus_attached_tables_fixed
#print axioms NearCompression.bus_adaptive_auxiliary_implies_source
#print axioms NearCompression.bus_adaptive_auxiliary_fp8_bound
#print axioms NearCompression.prepared_literal_wrong_output_adaptive_bus_bound

#print axioms NearCompression.polynomial_sumcheck_round_count
#print axioms NearCompression.polynomial_sumcheck_false_persists
#print axioms NearCompression.adaptive_polynomial_sumcheck_count
#print axioms NearCompression.polynomial_sumcheck_truth_endpoints
#print axioms NearCompression.polynomial_sumcheck_truth_terminal
#print axioms NearCompression.adaptive_polynomial_cube_sumcheck_count

#print axioms NearCompression.bus_polynomial_lower_eval
#print axioms NearCompression.bus_polynomial_lower_degree
#print axioms NearCompression.combined_air_polynomial_eval
#print axioms NearCompression.combined_air_polynomial_degree
#print axioms NearCompression.combined_air_round_eval
#print axioms NearCompression.combined_air_round_degree
#print axioms NearCompression.combined_air_adaptive_sumcheck_count

#print axioms NearCompression.air_mle_coordinate_affine
#print axioms NearCompression.air_coordinate_polynomial_eval
#print axioms NearCompression.air_coordinate_polynomial_degree
#print axioms NearCompression.air_trace_coordinate_affine
#print axioms NearCompression.air_trace_coordinate_environment
#print axioms NearCompression.bus_trace_coordinate_environment
#print axioms NearCompression.combined_trace_coordinate_eval
#print axioms NearCompression.air_kernel_coordinate_affine
#print axioms NearCompression.air_kernel_coordinate_eval
#print axioms NearCompression.air_kernel_coordinate_degree
#print axioms NearCompression.air_trace_round_represents
#print axioms NearCompression.air_trace_adaptive_sumcheck_count

#print axioms NearCompression.air_local_invalid_trace_count

#print axioms NearCompression.shift_weighted_cube_row_mle
#print axioms NearCompression.shift_kernel_row_mle
#print axioms NearCompression.shift_kernel_zipped_row_mle
#print axioms NearCompression.shift_reduction_coordinate_eval
#print axioms NearCompression.shift_reduction_coordinate_degree
#print axioms NearCompression.shift_reduction_slice_degree
#print axioms NearCompression.shift_reduction_slice_eval

#print axioms NearCompression.row_mle_cube_dot
#print axioms NearCompression.shift_kernel_initial_sum
#print axioms NearCompression.shift_reduction_initial_sum
#print axioms NearCompression.lane_power_batch_append
#print axioms NearCompression.row_mle_lane_batch
#print axioms NearCompression.shift_reduction_batched_initial
#print axioms NearCompression.shift_initial_claim_bad_count

#print axioms NearCompression.air_boolean_suffix_length
#print axioms NearCompression.air_boolean_suffix_sum
#print axioms NearCompression.conditional_scaled_accept_count

#print axioms NearCompression.shift_honest_round_degree
#print axioms NearCompression.shift_honest_round_represents
#print axioms NearCompression.shift_adaptive_round_count
#print axioms NearCompression.shift_trace_initial_sum
#print axioms NearCompression.shift_wrong_vector_count

#print axioms NearCompression.mobius_tensor_row_mle
#print axioms NearCompression.packed_computed_tensor
#print axioms NearCompression.packed_computed_opening_bad_count

#print axioms NearCompression.packed_computed_accept_decomposition
#print axioms NearCompression.packed_computed_opening_failure_budget

#print axioms NearCompression.weighted_replay_representative_no_candidate
#print axioms NearCompression.weighted_prefix_representative_wrong_count

#print axioms NearCompression.weighted_agreement_list_bound
#print axioms NearCompression.weighted_rs_johnson_list_bound
#print axioms NearCompression.weighted_curve_johnson_list_bound
#print axioms NearCompression.weighted_curve_johnson_gap_bound

#print axioms NearCompression.weighted_curve_candidates_sound
#print axioms NearCompression.weighted_curve_candidates_complete
#print axioms NearCompression.weighted_curve_candidates_distinct
#print axioms NearCompression.weighted_curve_candidates_gap_bound

#print axioms NearCompression.general_fixed_curve_many_outcome
#print axioms NearCompression.general_concentration_extraction_bad_count

#print axioms NearCompression.curve_f5_zero_exception_transfer_counterexample

#print axioms NearCompression.curve_support_interpolation
#print axioms NearCompression.supported_curve_bad_count

#print axioms NearCompression.packed_computed_gkr_table
#print axioms NearCompression.bound_polynomial_gkr_table
#print axioms NearCompression.packed_computed_gkr_functional

#print axioms NearCompression.shared_representative_equivalent
#print axioms NearCompression.shared_representative_functionals_unique

#print axioms NearCompression.joint_source_far_acceptance_count

#print axioms NearCompression.weighted_terminal_pair_constant
#print axioms NearCompression.weighted_terminal_collision_or_authenticated
#print axioms NearCompression.weighted_terminal_binding_authenticated

#print axioms NearCompression.sha384_source_tree_collision

#print axioms NearCompression.canonical_field_word_bytes_length
#print axioms NearCompression.canonical_field_words_read_append
#print axioms NearCompression.canonical_field_word_bytes_injective
#print axioms NearCompression.canonical_field_word_tree_injective
#print axioms NearCompression.canonical_field_tree_hash_collision

#print axioms NearCompression.ext4_pair_words_canonical
#print axioms NearCompression.ext4_pair_words_injective
#print axioms NearCompression.ext4_pair_bytes_length
#print axioms NearCompression.ext4_pair_bytes_injective
#print axioms NearCompression.ext4_pair_word_tree_injective
#print axioms NearCompression.ext4_pair_tree_hash_collision

#print axioms NearCompression.ext4_terminal_check_authenticates_or_collision
#print axioms NearCompression.ext4_terminal_check_authenticated

#print axioms NearCompression.finite_product_acceptance_budget

#print axioms NearCompression.near_functional_fold_acceptance_count

#print axioms NearCompression.literal193_gkr_lanes_well_formed
#print axioms NearCompression.literal193_gkr_lane_selectors

#print axioms NearCompression.gkr_envelope_index_bound
#print axioms NearCompression.gkr_envelope_operand_value
#print axioms NearCompression.gkr_envelope_first_layer
#print axioms NearCompression.gkr_envelope_circuit

#print axioms NearCompression.chosen_gkr_terminal_acceptance_count

#print axioms NearCompression.heterogeneous_lifted_joint_coefficients
#print axioms NearCompression.heterogeneous_lifted_joint_oracle

#print axioms NearCompression.uniform_tuples_append
#print axioms NearCompression.chronological_suffix_count

#print axioms NearCompression.near_history_fold_acceptance_count

#print axioms NearCompression.chosen_gkr_history_acceptance_count

#print axioms NearCompression.gkr_history_joint_coefficients
#print axioms NearCompression.gkr_history_joint_oracle
#print axioms NearCompression.gkr_joint_split_oracle
#print axioms NearCompression.gkr_pcs_point_length
#print axioms NearCompression.gkr_pcs_point_eq_drop

#print axioms NearCompression.gkr_history_far_acceptance_count

#print axioms NearCompression.uniform_tuple_member_length
#print axioms NearCompression.gkr_joint_failure_acceptance_count

#print axioms NearCompression.gkr_terminal_mismatch_last
#print axioms NearCompression.gkr_terminal_recovered_mismatch
#print axioms NearCompression.gkr_continuation_terminal_error_budget

#print axioms NearCompression.gkr_finite_circuit_append
#print axioms NearCompression.gkr_reverse_circuit_output
#print axioms NearCompression.gkr_reverse_circuit_input
#print axioms NearCompression.gkr_reverse_circuit_step
#print axioms NearCompression.gkr_evaluated_recovered_terminal_mismatch

#print axioms NearCompression.gkr_bind_values_preserves_checks
#print axioms NearCompression.gkr_evaluated_path_shape
#print axioms NearCompression.gkr_evaluated_path_linked
#print axioms NearCompression.gkr_evaluated_continuation_budget
#print axioms NearCompression.gkr_evaluated_path_recovered_mismatch

#print axioms NearCompression.terminal_finite_gate_value
#print axioms NearCompression.terminal_finite_chain_values
#print axioms NearCompression.terminal_finite_certified_root

#print axioms NearCompression.terminal_stored_route_checked
#print axioms NearCompression.terminal_stored_chain_checked
#print axioms NearCompression.terminal_stored_certified_root
#print axioms NearCompression.terminal_stored_route_regressions

#print axioms NearCompression.terminal_acyclic_checked
#print axioms NearCompression.terminal_initial_stored_checked
#print axioms NearCompression.terminal_checked_bundle_root
#print axioms NearCompression.terminal_stored_bundle_regressions

#print axioms NearCompression.terminal_arithmetic_witness_checked
#print axioms NearCompression.terminal_stored_arithmetic_checked
#print axioms NearCompression.terminal_program_checked_bundle_value
#print axioms NearCompression.terminal_arithmetic_check_regressions

#print axioms NearCompression.terminal_expansion_checked
#print axioms NearCompression.terminal_expansion_checked_bounds
#print axioms NearCompression.terminal_expansion_checked_value
#print axioms NearCompression.terminal_expansion_check_regressions

#print axioms NearCompression.terminal_join_checked
#print axioms NearCompression.terminal_pass_checked
#print axioms NearCompression.terminal_balance_checked
#print axioms NearCompression.terminal_balance_checked_value
#print axioms NearCompression.terminal_balance_check_regressions

#print axioms NearCompression.terminal_rebuild_record_checked
#print axioms NearCompression.terminal_rebuild_records_checked
#print axioms NearCompression.terminal_program_rebuild_checked_value
#print axioms NearCompression.terminal_rebuild_check_regressions

#print axioms NearCompression.terminal_batch_entry_checked
#print axioms NearCompression.terminal_batch_entries_checked
#print axioms NearCompression.terminal_batch_root_checked
#print axioms NearCompression.terminal_batch_checked_value
#print axioms NearCompression.terminal_batch_check_regressions

#print axioms NearCompression.terminal_compiled_table_checked
#print axioms NearCompression.terminal_compiled_dag_checked
#print axioms NearCompression.terminal_compiled_finite_checked
#print axioms NearCompression.terminal_compiled_check_regressions

#print axioms NearCompression.gkr_scatter_split_initial
#print axioms NearCompression.recovered_private_slots_capacity
#print axioms NearCompression.recovered_circuit_input_initial
#print axioms NearCompression.recovered_compiled_finite_value
#print axioms NearCompression.recovered_compiled_reverse_output
#print axioms NearCompression.recovered_scatter_split_regressions

#print axioms NearCompression.air_expression_checked
#print axioms NearCompression.air_expression_checked_execution
#print axioms NearCompression.air_expression_checked_compiled_table
#print axioms NearCompression.air_expression_check_regressions

#print axioms NearCompression.air_accumulator_checked
#print axioms NearCompression.air_weighted_program_checked
#print axioms NearCompression.air_expression_mix_checked
#print axioms NearCompression.air_weighted_expressions_checked
#print axioms NearCompression.air_weighted_expressions_compiled
#print axioms NearCompression.air_accumulator_check_regressions

#print axioms NearCompression.bus_formula_checked
#print axioms NearCompression.bus_formula_checked_execution
#print axioms NearCompression.air_bus_residual_checked
#print axioms NearCompression.air_bus_mix_checked
#print axioms NearCompression.air_bus_weighted_compiled
#print axioms NearCompression.bus_formula_check_regressions

#print axioms NearCompression.terminal_symbolic_record_value
#print axioms NearCompression.terminal_symbolic_records_value
#print axioms NearCompression.terminal_symbolic_rebuild_executed
#print axioms NearCompression.terminal_symbolic_instruction_value
#print axioms NearCompression.terminal_symbolic_program_run
#print axioms NearCompression.terminal_symbolic_compiled_program
#print axioms NearCompression.terminal_symbolic_rebuild_regressions

#print axioms NearCompression.symbolic_compiled_table_value
#print axioms NearCompression.symbolic_compiled_finite_value
#print axioms NearCompression.symbolic_compiled_recovered_value
#print axioms NearCompression.symbolic_compiled_check_regressions

#print axioms NearCompression.symbolic_program_acyclic_check
#print axioms NearCompression.symbolic_formula_table_value
#print axioms NearCompression.symbolic_formula_compiler_value
#print axioms NearCompression.symbolic_formula_recovered_value
#print axioms NearCompression.symbolic_formula_check_regressions

#print axioms NearCompression.recovered_symbolic_column_owner
#print axioms NearCompression.recovered_symbolic_environment
#print axioms NearCompression.recovered_environment_placement_regressions

#print axioms NearCompression.air_expression_environment_transport
#print axioms NearCompression.bus_formula_environment_transport
#print axioms NearCompression.mixed_formula_environment_transport
#print axioms NearCompression.mixed_sum_environment_transport
#print axioms NearCompression.recovered_decoded_environment_agreement
#print axioms NearCompression.recovered_mixed_formula_transport
#print axioms NearCompression.formula_environment_transport_regressions

#print axioms NearCompression.decoded_formula_outputs
#print axioms NearCompression.decoded_formula_recovered_circuit

#print axioms NearCompression.symbolic_selector_checked
#print axioms NearCompression.decoded_common_point_environment
#print axioms NearCompression.decoded_common_point_mixture
#print axioms NearCompression.decoded_selector_regressions

#print axioms NearCompression.gkr_table_history_point_length
#print axioms NearCompression.gkr_table_history_lane_alignment
#print axioms NearCompression.gkr_table_history_point_unpadded
#print axioms NearCompression.history_decoded_environment
#print axioms NearCompression.history_decoded_mixture
#print axioms NearCompression.history_decoded_formula_outputs
#print axioms NearCompression.history_decoded_regressions

#print axioms NearCompression.decoded_air_row_environment
#print axioms NearCompression.decoded_bus_row_environment
#print axioms NearCompression.mixed_formula_power_batch
#print axioms NearCompression.decoded_combined_residual_values
#print axioms NearCompression.decoded_combined_mixture
#print axioms NearCompression.decoded_combined_mixture_boolean
#print axioms NearCompression.decoded_mixture_weighted_zero_count

#print axioms NearCompression.decoded_local_accepted_count_eq
#print axioms NearCompression.decoded_local_invalid_trace_count
#print axioms NearCompression.decoded_local_acceptance_split

#print axioms NearCompression.terminal_residual_power_batch
#print axioms NearCompression.terminal_residual_cancellation_count
#print axioms NearCompression.terminal_circuit_cancellation_count
#print axioms NearCompression.terminal_batch_continuation_budget
#print axioms NearCompression.terminal_batch_cancellation_regressions

#print axioms NearCompression.evaluated_gkr_zero_root_wrong
#print axioms NearCompression.batched_evaluated_gkr_budget

#print axioms NearCompression.gkr_block_coordinates_uniform
#print axioms NearCompression.gkr_challenge_paths_append
#print axioms NearCompression.gkr_rows_final_block_history
#print axioms NearCompression.gkr_rows_block_pcs_coordinates
#print axioms NearCompression.gkr_rows_block_pcs_event_count
#print axioms NearCompression.gkr_block_coordinate_regressions

#print axioms NearCompression.gkr_joint_history_accessors
#print axioms NearCompression.gkr_joint_history_rows_unchanged
#print axioms NearCompression.gkr_joint_history_suffix_split
#print axioms NearCompression.gkr_evaluated_joint_terminal_event
#print axioms NearCompression.gkr_joint_accessor_regressions

#print axioms NearCompression.gkr_finite_sample_exchange
#print axioms NearCompression.gkr_earlier_joint_event_count
#print axioms NearCompression.gkr_earlier_joint_event_budget

#print axioms NearCompression.gkr_history_block_inverse
#print axioms NearCompression.gkr_history_reindex_inverse
#print axioms NearCompression.gkr_history_terminal_claim_inverse
#print axioms NearCompression.gkr_history_strategy_terminal_event
#print axioms NearCompression.gkr_history_strategy_regressions

#print axioms NearCompression.gkr_pcs_family_reindex
#print axioms NearCompression.gkr_pcs_checks_reindex
#print axioms NearCompression.gkr_pcs_initial_reindex
#print axioms NearCompression.gkr_pcs_accepted_mismatch_reindex

#print axioms NearCompression.gkr_concrete_pcs_event_count
#print axioms NearCompression.gkr_concrete_joint_failure_count

#print axioms NearCompression.joint_pcs_challenge_arithmetic
#print axioms NearCompression.joint_pcs_query_arithmetic

#print axioms NearCompression.joint_pcs_near_factor
#print axioms NearCompression.joint_pcs_far_factor
#print axioms NearCompression.joint_pcs_merged_factor
#print axioms NearCompression.joint_pcs_normalized_target
#print axioms NearCompression.literal193_original_merged_target

#print axioms NearCompression.conditional_scaled_accept_errors
#print axioms NearCompression.terminal_batch_averaged_errors
#print axioms NearCompression.sum_scaled_error_budget
#print axioms NearCompression.batched_evaluated_gkr_averaged_errors

#print axioms NearCompression.decoded_local_prefix_count
#print axioms NearCompression.decoded_local_continuation_split
#print axioms NearCompression.decoded_invalid_trace_continuation_budget

#print axioms NearCompression.decoded_table_before_placement
#print axioms NearCompression.decoded_family_before_compiler
#print axioms NearCompression.preselected_decoded_mixture
#print axioms NearCompression.preselected_formula_outputs

#print axioms NearCompression.terminal_outputs_semantic_projection
#print axioms NearCompression.terminal_outputs_fixed_meaning
#print axioms NearCompression.terminal_pair_mismatch_index
#print axioms NearCompression.local_terminal_semantic_mismatch
#print axioms NearCompression.preselected_semantic_outputs
#print axioms NearCompression.local_terminal_compiler_cancellation

#print axioms NearCompression.checked_semantic_circuit_value
#print axioms NearCompression.checked_semantic_circuit_cancellation

#print axioms NearCompression.decoded_local_batched_gkr_split
#print axioms NearCompression.local_gkr_joint_error_count

#print axioms NearCompression.concrete_pcs_sample_lengths
#print axioms NearCompression.concrete_gkr_error_inclusion
#print axioms NearCompression.concrete_gkr_accepted_failure_budget

#print axioms NearCompression.gkr_full_pcs_event_count
#print axioms NearCompression.gkr_full_pcs_event_budget
#print axioms NearCompression.evaluated_gkr_full_pcs_count
#print axioms NearCompression.evaluated_gkr_joint_pcs_budget

#print axioms NearCompression.two_table_local_regroup
#print axioms NearCompression.two_table_local_joint_coordinates
#print axioms NearCompression.two_table_local_joint_budget

#print axioms NearCompression.table_history_segment
#print axioms NearCompression.two_table_history_points
#print axioms NearCompression.recovered_input_history_suffix
#print axioms NearCompression.concrete_pcs_recovered_input_binding

#print axioms NearCompression.two_table_gkr_pcs_joint_budget

#print axioms NearCompression.local_terminal_binding_checked

#print axioms NearCompression.checked_local_terminal_mismatch
#print axioms NearCompression.checked_formula_table_mismatch
#print axioms NearCompression.checked_formula_batch_cancellation

#print axioms NearCompression.decoded_invalid_table_after_earlier_budget
#print axioms NearCompression.earlier_local_error_count

#print axioms NearCompression.table_source_residuals_local
#print axioms NearCompression.table_local_failure_residual
#print axioms NearCompression.table_local_failure_combined_residual
#print axioms NearCompression.prepared_wrong_output_residual_or_bus

#print axioms NearCompression.project_polynomial_coefficient
#print axioms NearCompression.project_polynomial_evaluation
#print axioms NearCompression.polynomial_descent_from_agreement
#print axioms NearCompression.fp8_base_projection_linear
#print axioms NearCompression.fp8_polynomial_base_descent
#print axioms NearCompression.fp8_projected_coefficients_base
#print axioms NearCompression.fp8_lower_zeta_base
#print axioms NearCompression.fp8_recovered_column_base

#print axioms NearCompression.fp8_joint_representative_base
#print axioms NearCompression.fp8_typed_joint_recovered_base
#print axioms NearCompression.fp8_natural_domain_base

#print axioms NearCompression.decoded_base_trace_cell
#print axioms NearCompression.decoded_base_trace_source_eval
#print axioms NearCompression.decoded_base_trace_table_local
#print axioms NearCompression.decoded_base_residual_nonzero
#print axioms NearCompression.decoded_wrong_output_residual_or_bus

#print axioms NearCompression.decoded_base_trace_attached
#print axioms NearCompression.decoded_bus_implies_adaptive_accept
#print axioms NearCompression.decoded_adaptive_bus_error_bound

#print axioms NearCompression.recovered_column_coefficient_congr
#print axioms NearCompression.joint_shared_source_recovered_equal
#print axioms NearCompression.fixed_source_column_before_auxiliary

#print axioms NearCompression.fixed_decoded_base_source_trace
#print axioms NearCompression.fixed_source_decoded_bus_family

#print axioms NearCompression.fixed_joint_representative_source_trace

#print axioms NearCompression.live_lane_index_unique
#print axioms NearCompression.metadata_source_column_index
#print axioms NearCompression.indexed_lane_polynomial
#print axioms NearCompression.decoded_source_indexed_provenance

#print axioms NearCompression.metadata_source_index_family
#print axioms NearCompression.metadata_joint_fixed_source_trace

#print axioms NearCompression.prefix_event_continuation_count
#print axioms NearCompression.prepared_decoded_bus_continuation_bound

#print axioms NearCompression.decoded_adaptive_table_after_earlier_budget

#print axioms NearCompression.fixed_source_decoded_expression
#print axioms NearCompression.fixed_source_decoded_nonzero

#print axioms NearCompression.decoded_table_expression

#print axioms NearCompression.fixed_source_invalid_residual_index

#print axioms NearCompression.fixed_source_invalid_local_budget

#print axioms NearCompression.second_table_fixed_source_pcs_budget

#print axioms NearCompression.first_table_fixed_source_pcs_budget

#print axioms NearCompression.two_table_terminal_repair

#print axioms NearCompression.second_table_evaluated_gkr_pcs_budget

#print axioms NearCompression.first_table_evaluated_gkr_pcs_budget

#print axioms NearCompression.checked_terminal_gkr_repair

#print axioms NearCompression.two_table_concrete_pcs_failure_budget

#print axioms NearCompression.prepared_fixed_source_branch_budget

#print axioms NearCompression.decoded_adaptive_witness_after_earlier_budget

#print axioms NearCompression.decoded_adaptive_invalid_rows_budget

#print axioms NearCompression.bus_ext8_tables_from_generated_residuals

#print axioms NearCompression.bus_ext8_generated_residual_failure

#print axioms NearCompression.auxiliary_nonzero_combined_index

#print axioms NearCompression.bus_formula_sum_value

#print axioms NearCompression.bus_coordinate_formula_value

#print axioms NearCompression.ext8_coordinate_sum

#print axioms NearCompression.bus_coordinate_row_environment

#print axioms NearCompression.bus_coordinate_lowering_row_value

#print axioms NearCompression.bus_formula_sum_degree

#print axioms NearCompression.bus_coordinate_column_degree

#print axioms NearCompression.bus_coordinate_lowering_degree

#print axioms NearCompression.decoded_bus_coordinate_lowering

#print axioms NearCompression.bus_formula_bounded_base_projection

#print axioms NearCompression.decoded_bus_coordinate_lowering_bounded

#print axioms NearCompression.typed_joint_bus_coordinate_lowering

#print axioms NearCompression.lowered_auxiliary_failure_index

#print axioms NearCompression.bus_formula_sum_column_bound

#print axioms NearCompression.bus_coordinate_column_coverage

#print axioms NearCompression.bus_coordinate_formula_coverage

#print axioms NearCompression.typed_joint_zip_recovered_base

#print axioms NearCompression.metadata_typed_coordinate_formula

#print axioms NearCompression.bus_formula_foldl_value

#print axioms NearCompression.native_style_coordinate_value

#print axioms NearCompression.bus_formula_foldl_bounds

#print axioms NearCompression.native_style_coordinate_bounds

#print axioms NearCompression.native_style_lowering_value

#print axioms NearCompression.native_style_lowering_bounds

#print axioms NearCompression.generated_ext8_bus_spec_checked

#print axioms NearCompression.checked_bus_decoded_row_values

#print axioms NearCompression.checked_bus_failure_combined_index

#print axioms NearCompression.checked_bus_rows_zero

#print axioms NearCompression.checked_bus_tables_residuals_zero

#print axioms NearCompression.decoded_table_combined_residuals

#print axioms NearCompression.checked_bus_invalid_table_witness

#print axioms NearCompression.checked_auxiliary_after_earlier_budget

#print axioms NearCompression.history_three_branch_count

#print axioms NearCompression.history_three_branch_budget

#print axioms NearCompression.prepared_history_branch_budget

#print axioms NearCompression.history_fixed_joint_coordinate_trace

#print axioms NearCompression.fixed_coordinate_bus_formula

#print axioms NearCompression.fixed_coordinate_combined_residuals

#print axioms NearCompression.two_table_auxiliary_none

#print axioms NearCompression.two_table_auxiliary_selected_invalid

#print axioms NearCompression.selected_auxiliary_decoded_witness

#print axioms NearCompression.unselected_auxiliary_decoded_bus_validity

#print axioms NearCompression.table_local_all_constraints_zero

#print axioms NearCompression.prepared_checked_history_budget

#print axioms NearCompression.selected_auxiliary_local_error_count

#print axioms NearCompression.selected_auxiliary_gkr_error_count

#print axioms NearCompression.selected_auxiliary_future_gkr_error_count

#print axioms NearCompression.selected_history_filter_count

#print axioms NearCompression.first_selected_history_reindex

#print axioms NearCompression.second_selected_history_reindex

#print axioms NearCompression.first_selected_branch_count

#print axioms NearCompression.second_selected_branch_count

#print axioms NearCompression.two_table_filtered_history_budget

#print axioms NearCompression.selected_last_evidence_bound

#print axioms NearCompression.selected_future_evidence_bound

#print axioms NearCompression.two_table_selected_gkr_composition

#print axioms NearCompression.prepared_selected_gkr_budget

#print axioms NearCompression.concrete_two_table_evidence_bound

#print axioms NearCompression.history_concrete_pcs_failure_budget

#print axioms NearCompression.prepared_concrete_soundness_budget

#print axioms NearCompression.selected_history_counts_le_length

#print axioms NearCompression.selected_history_weighted_budget

#print axioms NearCompression.expanded_bus_tagged_value

#print axioms NearCompression.expanded_bus_fingerprint_value

#print axioms NearCompression.expanded_bus_tagged_degree

#print axioms NearCompression.expanded_bus_tagged_columns

#print axioms NearCompression.expanded_bus_fingerprint_checked_execution

#print axioms NearCompression.expanded_bus_fingerprint_check_regressions

#print axioms NearCompression.replace_bus_formula_value

#print axioms NearCompression.expand_bus_fingerprint_in_value

#print axioms NearCompression.bus_expanded_formula_checked

#print axioms NearCompression.bus_expanded_list_checked

#print axioms NearCompression.generated_expanded_bus_spec_checked

#print axioms NearCompression.rate_shift_truthful_ood_iff

#print axioms NearCompression.rate_shift_truthful_ood_query_count

#print axioms NearCompression.rate_shift_source_threshold_sharp

#print axioms NearCompression.weighted_fold_prefix_escape_bound
#print axioms NearCompression.weighted_fold_adaptive_escape_budget

#print axioms NearCompression.checked_fold_escape_implies_bad
#print axioms NearCompression.checked_fold_continuation_escape_bound

#print axioms NearCompression.indexed_candidate_snapshot_congr
#print axioms NearCompression.checked_history_escape_bound
#print axioms NearCompression.checked_history_adaptive_escape_budget

#print axioms NearCompression.checked_history_no_escape_preserves_doom
#print axioms NearCompression.checked_history_terminal_few_queries
#print axioms NearCompression.checked_history_terminal_query_budget
#print axioms NearCompression.checked_history_terminal_acceptance_budget

#print axioms NearCompression.checked_history_adaptive_escape_sum_budget
#print axioms NearCompression.checked_history_interactive_acceptance_budget

#print axioms NearCompression.indexed_initial_candidate_agreement
#print axioms NearCompression.checked_history_joint_far_acceptance_budget

#print axioms NearCompression.check_chunk_call_wiring_iff
#print axioms NearCompression.check_chunk_call_sound
#print axioms NearCompression.sha384_chunks_checked_call_sound

#print axioms NearCompression.call_word_limb_nat
#print axioms NearCompression.call_word_limbs_decode
#print axioms NearCompression.call_constant_limbs_words
#print axioms NearCompression.call_state_link_residuals_sound
#print axioms NearCompression.call_input_slot_injective
#print axioms NearCompression.call_constant_residuals_words
#print axioms NearCompression.call_link_residuals_wiring
#print axioms NearCompression.call_iv_residuals_sound

#print axioms NearCompression.call_private_cell
#print axioms NearCompression.call_constant_equations_eval
#print axioms NearCompression.call_state_equations_eval
#print axioms NearCompression.call_digest_equations_sound

#print axioms NearCompression.call_scatter_dot
#print axioms NearCompression.call_linear_compilation
#print axioms NearCompression.call_residual_batch_zero_count
#print axioms NearCompression.call_compiled_score_mle
#print axioms NearCompression.call_compiled_batch_zero_count

#print axioms NearCompression.call_array_update_size
#print axioms NearCompression.call_array_update_read
#print axioms NearCompression.call_array_run_sound
#print axioms NearCompression.call_array_zero_compile
#print axioms NearCompression.call_array_functional

#print axioms NearCompression.call_padding_residual
#print axioms NearCompression.call_padded_residual
#print axioms NearCompression.call_short_batch_mle
#print axioms NearCompression.call_short_array_mle
#print axioms NearCompression.call_short_array_zero_count

#print axioms NearCompression.call_block_descriptors_valid
#print axioms NearCompression.call_descriptors_valid
#print axioms NearCompression.call_descriptor_lift
#print axioms NearCompression.call_descriptor_ext8_nonzero
#print axioms NearCompression.call_generated_ext8_residuals
#print axioms NearCompression.call_descriptor_array_zero_count

#print axioms NearCompression.call_circuit_functional
#print axioms NearCompression.call_circuit_residual_sum

#print axioms NearCompression.call_circuit_checked_route
#print axioms NearCompression.call_circuit_checked_functional
#print axioms NearCompression.call_layered_checked_functional

#print axioms NearCompression.call_layered_checked_residual_sum

#print axioms NearCompression.call_checked_gkr_root_wrong
#print axioms NearCompression.call_gkr_terminal_budget

#print axioms NearCompression.gkr_axis_message_checked
#print axioms NearCompression.gkr_layer_message_checked

#print axioms NearCompression.gkr_path_message_checked
#print axioms NearCompression.gkr_path_message_linked

#print axioms NearCompression.gkr_root_message_checked
#print axioms NearCompression.call_root_message_wrong

#print axioms NearCompression.call_source_mle
#print axioms NearCompression.call_source_two_queries
#print axioms NearCompression.call_initial_input_split
#print axioms NearCompression.call_source_outside_private
#print axioms NearCompression.call_source_initial_split
#print axioms NearCompression.call_source_opening_mismatch

#print axioms NearCompression.call_source_words_or_collision
#print axioms NearCompression.call_source_pair_or_collision

#print axioms NearCompression.checked_history_joint_near_acceptance_budget

#print axioms NearCompression.terminal_weighted_expansion_value
#print axioms NearCompression.terminal_weighted_expansion_transport
#print axioms NearCompression.terminal_weighted_expansion_executed

#print axioms NearCompression.terminal_weighted_insert_value
#print axioms NearCompression.terminal_weighted_aggregate_value
#print axioms NearCompression.terminal_weighted_zero_drop
#print axioms NearCompression.terminal_weighted_permutation_value

#print axioms NearCompression.terminal_heap_route_value
#print axioms NearCompression.terminal_weighted_heap_rebuild

#print axioms NearCompression.terminal_weighted_leaf_route

#print axioms NearCompression.separable_coefficient_claim

#print axioms NearCompression.derived_fold_affine_value
#print axioms NearCompression.fold_pair_restore_exact
#print axioms NearCompression.fold_transport_restore_exact
#print axioms NearCompression.fold_transport_preserves_checks

#print axioms NearCompression.pooled_row_mask_dot
#print axioms NearCompression.pooled_current_row_functional
#print axioms NearCompression.pooled_next_row_functional
#print axioms NearCompression.pooled_current_next_row_functional

#print axioms NearCompression.pooled_scatter_coefficient_functional

#print axioms NearCompression.pooled_upper_zeta_mask
#print axioms NearCompression.pooled_row_mask_mle
#print axioms NearCompression.pooled_upper_weight_mle

#print axioms NearCompression.switch_inject_coefficients
#print axioms NearCompression.switch_inject_dot
#print axioms NearCompression.switch_inject_all_residual
#print axioms NearCompression.switch_honest_residual_zero
#print axioms NearCompression.switch_inject_all_honest
#print axioms NearCompression.switch_wrong_answer_unique_mixer
#print axioms NearCompression.grouped_affine_values_eval
#print axioms NearCompression.grouped_affine_pair_eval
#print axioms NearCompression.grouped_four_fold_eval

#print axioms NearCompression.switch_inject_all_coefficients
#print axioms NearCompression.switch_stage_honest
#print axioms NearCompression.switch_chain_honest

#print axioms NearCompression.switch_fold_pair_add
#print axioms NearCompression.switch_fold_pair_sum
#print axioms NearCompression.heterogeneous_switch_query
#print axioms NearCompression.weighted_switch_polynomial_query

#print axioms NearCompression.switch_inject_rolling_equiv
#print axioms NearCompression.switch_inject_rolling_dot

#print axioms NearCompression.switch_independent_mixing_count
#print axioms NearCompression.switch_bound_residual
#print axioms NearCompression.switch_injection_tuple_residual
#print axioms NearCompression.switch_fixed_candidate_mixing_count
#print axioms NearCompression.switch_candidate_family_mixing_count
#print axioms NearCompression.switch_candidate_family_mixing_scaled

#print axioms NearCompression.switch_polynomial_pairs_coefficients
#print axioms NearCompression.switch_johnson_mixing_count
#print axioms NearCompression.switch_johnson_mixing_gap

#print axioms NearCompression.switch_inject_verifier_independent
#print axioms NearCompression.switch_continuation_functional
#print axioms NearCompression.switch_indexed_continuation_candidate
#print axioms NearCompression.switch_continuation_candidate_count

#print axioms NearCompression.switch_query_unmixed
#print axioms NearCompression.switch_query_correct_family_count
#print axioms NearCompression.switch_query_mixing_joint_count

#print axioms NearCompression.support_preserving_weighted_lift

#print axioms NearCompression.synthetic_quotient_coefficient
#print axioms NearCompression.synthetic_zero_from_quotient
#print axioms NearCompression.synthetic_root_certificate_zero
#print axioms NearCompression.synthetic_taylor_evaluation
#print axioms NearCompression.synthetic_taylor_coefficient
#print axioms NearCompression.synthetic_jets_certificate
#print axioms NearCompression.synthetic_multiplicity_bound

#print axioms NearCompression.synthetic_quotient_tail
#print axioms NearCompression.synthetic_quotients_commute
#print axioms NearCompression.synthetic_quotient_jet_step
#print axioms NearCompression.synthetic_quotient_preserves_jets
#print axioms NearCompression.synthetic_multipoint_certificate
#print axioms NearCompression.synthetic_multipoint_bound

#print axioms NearCompression.polynomial_order_mul
#print axioms NearCompression.synthetic_jet_zero
#print axioms NearCompression.bivariate_substitution_order
#print axioms NearCompression.bivariate_substitution_jets

#print axioms NearCompression.polynomial_translate_eval
#print axioms NearCompression.polynomial_translate_coeff
#print axioms NearCompression.bivariate_translate_eval
#print axioms NearCompression.bivariate_substitution_at_center
#print axioms NearCompression.bivariate_multiplicity_forces_zero

#print axioms NearCompression.bivariate_substitution_degree
#print axioms NearCompression.bivariate_weighted_degree_rows
#print axioms NearCompression.bivariate_weighted_multiplicity_zero

#print axioms NearCompression.kernel_dot_elimination
#print axioms NearCompression.homogeneous_nonzero_kernel

#print axioms NearCompression.gs_monomial_member
#print axioms NearCompression.gs_monomials_distinct
#print axioms NearCompression.gs_monomial_count
#print axioms NearCompression.gs_encode_coefficient
#print axioms NearCompression.gs_encode_weighted_degree
#print axioms NearCompression.gs_encode_nonzero
#print axioms NearCompression.gs_linear_interpolant
#print axioms NearCompression.gs_jet_order_member
#print axioms NearCompression.gs_jet_order_count
#print axioms NearCompression.gs_jet_orders_distinct
#print axioms NearCompression.gs_constraint_count

#print axioms NearCompression.synthetic_jet_congr
#print axioms NearCompression.synthetic_jet_add
#print axioms NearCompression.synthetic_jet_scale
#print axioms NearCompression.synthetic_jet_sum
#print axioms NearCompression.polynomial_translate_linear
#print axioms NearCompression.jet_monomial_coefficient
#print axioms NearCompression.synthetic_jet_coefficient_matrix
#print axioms NearCompression.synthetic_jet_vector_matrix

#print axioms NearCompression.synthetic_jet_cons_succ
#print axioms NearCompression.bivariate_translate_y_coefficient
#print axioms NearCompression.bivariate_translate_mixed_jet
#print axioms NearCompression.bivariate_order_mixed_jets
#print axioms NearCompression.gs_mixed_matrix_correct
#print axioms NearCompression.gs_interpolant_exists
#print axioms NearCompression.gs_interpolant_exists_counted
