import NearCompression.YieldIdResume
import NearCompression.ObservedChain

/-! Executable coverage certificate for the host families proved so far.
This is a sufficient simulation check, not a new admission or semantic scope. -/
namespace NearCompression
open NearSpecV3.Wasm

def provedHostNames : List String :=
  ["storage_read", "storage_write", "storage_remove", "storage_has_key"] ++
  ["sha256", "keccak256", "keccak512", "ripemd160"] ++
  (contextRegisterNames ++ contextNatNames) ++
  ["read_register", "write_register", "register_len"] ++ balanceHostNames ++ ["value_return", "panic", "log_utf16", "log_utf8", "panic_utf8", "abort", "ed25519_verify", "promise_result", "promise_return", "promise_batch_create", "promise_batch_then", "promise_and", "promise_batch_action_transfer", "promise_batch_action_function_call", "promise_batch_action_function_call_weight", "promise_create", "promise_then", "promise_batch_action_deploy_contract", "promise_batch_action_create_account", "promise_batch_action_add_key_with_full_access", "promise_batch_action_delete_key", "promise_batch_action_add_key_with_function_call", "promise_batch_action_stake", "promise_set_refund_to", "promise_batch_action_delete_account", "promise_yield_resume", "promise_yield_create", "promise_yield_create_with_id", "gas", "storage_iter_prefix", "storage_iter_range", "storage_iter_next", "validator_stake", "validator_total_stake", "current_contract_code", "promise_yield_resume_with_yield_id"]

def checkProvedImports (p : Prepared) : Bool :=
  p.m.imports.all (fun imp => provedHostNames.contains imp.name)

theorem proved_host_sim (name : String) (hn : name ∈ provedHostNames)
    (call : HM Unit) (hc : hostCall name = some call) : HostSim call call := by
  simp only [provedHostNames, List.mem_append] at hn
  rcases hn with ((((hs | hh) | hcxt) | hr) | hb) | hv
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with hs | hs | hs | hs
    · subst name; exact actual_storage_read_sim call hc
    · subst name; exact actual_storage_write_sim call hc
    · subst name; exact actual_storage_remove_sim call hc
    · subst name; exact actual_storage_has_key_sim call hc
  · exact actual_hash_call_sim name hh call hc
  · exact actual_context_host_sim name (List.mem_append.mpr hcxt) call hc
  · exact actual_register_host_sim name hr call hc
  · exact listed_balance_host_sim name hb call hc
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with hv | hv | hv | hv | hv | hv | hv | hv | hv | hv | hv | hv | hv | hv | hv | hv | hv | hv | hv | hv | hv | hv | hv | hv | hv | hv | hv | hv | hv | hv | hv | hv | hv | hv | hv | hv
    · subst name
      exact actual_value_return_sim call hc
    · subst name
      exact actual_panic_sim call hc
    · subst name
      exact actual_log_utf16_sim call hc
    · subst name
      exact actual_log_utf8_sim call hc
    · subst name
      exact actual_panic_utf8_sim call hc
    · subst name
      exact actual_abort_sim call hc
    · subst name
      exact actual_ed25519_sim call hc
    · subst name
      exact actual_promise_result_sim call hc
    · subst name
      exact actual_promise_return_sim call hc
    · subst name
      exact actual_batch_create_sim call hc
    · subst name
      exact actual_batch_then_sim call hc
    · subst name
      exact actual_promise_and_sim call hc
    · subst name
      exact actual_transfer_sim call hc
    · subst name
      exact actual_function_call_sim call hc
    · subst name
      exact actual_function_call_weight_sim call hc
    · subst name
      exact actual_promise_create_sim call hc
    · subst name
      exact actual_promise_then_sim call hc
    · subst name
      exact actual_deploy_action_sim call hc
    · subst name
      exact actual_create_account_action_sim call hc
    · subst name
      exact actual_full_access_sim call hc
    · subst name
      exact actual_delete_key_sim call hc
    · subst name
      exact actual_restricted_key_sim call hc
    · subst name
      exact actual_stake_action_sim call hc
    · subst name
      exact actual_refund_sim call hc
    · subst name
      exact actual_delete_account_sim call hc
    · subst name
      exact actual_yield_resume_sim call hc
    · subst name
      exact actual_yield_create_sim call hc
    · subst name
      exact actual_yield_id_sim call hc
    · subst name
      exact actual_gas_sim call hc
    · subst name
      exact actual_iterator_prefix_sim call hc
    · subst name
      exact actual_iterator_range_sim call hc
    · subst name
      exact actual_iterator_next_sim call hc
    · subst name
      exact actual_validator_stake_sim call hc
    · subst name
      exact actual_validator_total_sim call hc
    · subst name
      exact actual_contract_code_sim call hc
    · subst name
      exact actual_yield_id_resume_sim call hc

theorem checked_imports_preserve_maps (p : Prepared) (checked : checkProvedImports p = true) :
    ImportsPreserveMaps p := by
  intro i hi call hc
  have hall := Array.all_eq_true.mp checked
  have hn : p.m.imports[i].name ∈ provedHostNames := by
    exact List.contains_iff_mem.mp (hall i hi)
  exact proved_host_sim _ hn call hc

theorem checked_imports_step_preservation (cfg : NearCfg) (p : Prepared)
    (checked : checkProvedImports p = true) : StepPreservesMaps cfg p :=
  step_preserves_maps_of_imports cfg p (checked_imports_preserve_maps p checked)

theorem checked_imports_run_or_hash_collision {Digest : Type} (hash : List UInt8 → Digest)
    (encode : Res → List UInt8) (decode : List UInt8 → Option Res)
    (cfg : NearCfg) (p : Prepared) (checked : checkProvedImports p = true)
    (start : St) (ws : List SegmentWitness) (output : Res) (remainingFuel : Nat)
    (cert : CertifiedChain (fun r => hash (encode r)) cfg p (.cont start) ws output)
    (roundtrip : ObservedBoundaryDecodes encode decode (.cont start) ws output) :
    ResultEquivalent (run cfg p ((ws.map SegmentWitness.steps).sum + remainingFuel) start)
        (output.bind (run cfg p remainingFuel)) ∨
      ∃ a b, (a, b) ∈ boundaryLinks (.cont start) ws output ∧
        encode a ≠ encode b ∧ hash (encode a) = hash (encode b) :=
  observational_run_or_hash_collision hash encode decode cfg p
    (checked_imports_step_preservation cfg p checked) start ws output remainingFuel cert roundtrip

end NearCompression
