import NearCompression.StoragePersistence

/-! One persistence certificate for every ungated dispatcher family. -/
namespace NearCompression
open NearSpecV3.Wasm

theorem proved_host_keeps_real (name : String) (hn : name ∈ provedHostNames)
    (call : HM Unit) (hc : hostCall name = some call) : HostKeepsReal call := by
  simp only [provedHostNames, List.mem_append] at hn
  rcases hn with ((((hs | hh) | hcxt) | hr) | hb) | hv
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with hs | hs | hs | hs
    · subst name; exact actual_storage_read_keeps_real call hc
    · subst name; exact actual_storage_write_keeps_real call hc
    · subst name; exact actual_storage_remove_keeps_real call hc
    · subst name; exact actual_storage_has_key_keeps_real call hc
  · exact actual_hash_call_keeps_real name hh call hc
  · exact actual_context_host_keeps_real name (List.mem_append.mpr hcxt) call hc
  · exact actual_register_host_keeps_real name hr call hc
  · exact listed_balance_host_keeps_real name hb call hc
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with hv | hv | hv | hv | hv | hv | hv | hv | hv | hv | hv | hv | hv | hv | hv | hv | hv | hv | hv | hv | hv | hv | hv | hv | hv | hv | hv | hv | hv | hv | hv | hv | hv | hv | hv | hv
    · subst name
      exact actual_value_return_keeps_real call hc
    · subst name
      exact actual_panic_keeps_real call hc
    · subst name
      exact actual_log_utf16_keeps_real call hc
    · subst name
      exact actual_log_utf8_keeps_real call hc
    · subst name
      exact actual_panic_utf8_keeps_real call hc
    · subst name
      exact actual_abort_keeps_real call hc
    · subst name
      exact actual_ed25519_keeps_real call hc
    · subst name
      exact actual_promise_result_keeps_real call hc
    · subst name
      exact actual_promise_return_keeps_real call hc
    · subst name
      exact actual_batch_create_keeps_real call hc
    · subst name
      exact actual_batch_then_keeps_real call hc
    · subst name
      exact actual_promise_and_keeps_real call hc
    · subst name
      exact actual_transfer_keeps_real call hc
    · subst name
      exact actual_function_call_keeps_real call hc
    · subst name
      exact actual_function_call_weight_keeps_real call hc
    · subst name
      exact actual_promise_create_keeps_real call hc
    · subst name
      exact actual_promise_then_keeps_real call hc
    · subst name
      exact actual_deploy_action_keeps_real call hc
    · subst name
      exact actual_create_account_action_keeps_real call hc
    · subst name
      exact actual_full_access_keeps_real call hc
    · subst name
      exact actual_delete_key_keeps_real call hc
    · subst name
      exact actual_restricted_key_keeps_real call hc
    · subst name
      exact actual_stake_action_keeps_real call hc
    · subst name
      exact actual_refund_keeps_real call hc
    · subst name
      exact actual_delete_account_keeps_real call hc
    · subst name
      exact actual_yield_resume_keeps_real call hc
    · subst name
      exact actual_yield_create_keeps_real call hc
    · subst name
      exact actual_yield_id_keeps_real call hc
    · subst name
      exact actual_gas_keeps_real call hc
    · subst name
      exact actual_iterator_prefix_keeps_real call hc
    · subst name
      exact actual_iterator_range_keeps_real call hc
    · subst name
      exact actual_iterator_next_keeps_real call hc
    · subst name
      exact actual_validator_stake_keeps_real call hc
    · subst name
      exact actual_validator_total_keeps_real call hc
    · subst name
      exact actual_contract_code_keeps_real call hc
    · subst name
      exact actual_yield_id_resume_keeps_real call hc

end NearCompression
