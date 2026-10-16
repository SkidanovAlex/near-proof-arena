import NearCompression.HashHosts

/-! Context host families with exact dispatch correspondence. The input host's
special no-byte-charge register behavior is retained. -/
namespace NearCompression
open NearSpecV3.Wasm

inductive ContextRegisterHost where
  | current | signer | signerPk | predecessor | refund | chain | input | random

def contextRegisterName : ContextRegisterHost → String
  | .current => "current_account_id" | .signer => "signer_account_id"
  | .signerPk => "signer_account_pk" | .predecessor => "predecessor_account_id"
  | .refund => "refund_to_account_id" | .chain => "chain_id"
  | .input => "input" | .random => "random_seed"

def contextRegisterValue : ContextRegisterHost → CallCtx → ByteArray
  | .current, c => c.currentAccount.toUTF8 | .signer, c => c.signer.toUTF8
  | .signerPk, c => c.signerPk | .predecessor, c => c.predecessor.toUTF8
  | .refund, c => c.refundTo.toUTF8 | .chain, c => c.chainId.toUTF8
  | .input, c => c.input | .random, c => c.randomSeed

def contextRegisterCharge : ContextRegisterHost → Bool
  | .input => false | _ => true

def contextRegisterCode (kind : ContextRegisterHost) (base : Cost) : HM Unit := do
  let args ← popArgs 1
  payBaseH base
  regSetH args[0] (contextRegisterValue kind (← get).ctx) (contextRegisterCharge kind)

theorem context_register_body_sim (kind : ContextRegisterHost) (reg : Nat) :
    HostSim (do regSetH reg (contextRegisterValue kind (← get).ctx) (contextRegisterCharge kind))
      (do regSetH reg (contextRegisterValue kind (← get).ctx) (contextRegisterCharge kind)) := by
  intro s t h
  rw [host_get_bind_run, host_get_bind_run]
  have hc : s.ctx = t.ctx := by have he := congrArg St.ctx h.core; exact he
  rw [hc]
  have hr : HostSim (regSetH reg (contextRegisterValue kind t.ctx) (contextRegisterCharge kind))
      (regSetH reg (contextRegisterValue kind t.ctx) (contextRegisterCharge kind)) := by
    with_reducible exact host_sim_reg_set reg (contextRegisterValue kind t.ctx) (contextRegisterCharge kind)
  unfold HostSim at hr
  with_reducible exact hr s t h

theorem context_register_code_sim (kind : ContextRegisterHost) (base : Cost) :
    HostSim (contextRegisterCode kind base) (contextRegisterCode kind base) := by
  unfold contextRegisterCode
  with_reducible apply host_sim_bind
  · exact host_sim_pop_args 1
  intro args
  with_reducible apply host_sim_bind
  · unfold payBaseH
    exact host_sim_with_gas _
  intro _
  with_reducible exact context_register_body_sim kind args[0]

theorem actual_context_register_code (kind : ContextRegisterHost) :
    hostCall (contextRegisterName kind) = some (contextRegisterCode kind C.base) := by
  cases kind <;> rfl

theorem actual_context_register_sim (kind : ContextRegisterHost) (call : HM Unit)
    (hc : hostCall (contextRegisterName kind) = some call) : HostSim call call := by
  rw [actual_context_register_code] at hc
  cases Option.some.inj hc
  with_reducible exact context_register_code_sim kind C.base

inductive ContextNatHost where
  | block | timestamp | epoch | usage | prepaid | used | results

def contextNatName : ContextNatHost → String
  | .block => "block_index" | .timestamp => "block_timestamp" | .epoch => "epoch_height"
  | .usage => "storage_usage" | .prepaid => "prepaid_gas" | .used => "used_gas"
  | .results => "promise_results_count"

def contextNatValue : ContextNatHost → St → Nat
  | .block, s => s.ctx.blockHeight | .timestamp, s => s.ctx.blockTimestamp
  | .epoch, s => s.ctx.epochHeight | .usage, s => s.storageUsage
  | .prepaid, s => s.ctx.prepaidGas | .used, s => s.gas.used
  | .results, s => s.ctx.promiseResults.size

def contextNatCode (kind : ContextNatHost) (base : Cost) : HM Unit := do
  payBaseH base
  pushRet (contextNatValue kind (← get))

theorem context_nat_value_equiv (kind : ContextNatHost) (s t : St) (h : StateEquivalent s t) :
    contextNatValue kind s = contextNatValue kind t := by
  have he := congrArg (contextNatValue kind) h.core
  cases kind <;> exact he

theorem context_nat_code_sim (kind : ContextNatHost) (base : Cost) :
    HostSim (contextNatCode kind base) (contextNatCode kind base) := by
  unfold contextNatCode
  with_reducible apply host_sim_bind
  · unfold payBaseH
    exact host_sim_with_gas _
  intro _
  with_reducible apply host_sim_get_bind
  intro s t h
  rw [context_nat_value_equiv kind s t h]
  exact host_sim_push_ret _ true s t h

theorem actual_context_nat_code (kind : ContextNatHost) :
    hostCall (contextNatName kind) = some (contextNatCode kind C.base) := by
  cases kind <;> rfl

theorem actual_context_nat_sim (kind : ContextNatHost) (call : HM Unit)
    (hc : hostCall (contextNatName kind) = some call) : HostSim call call := by
  rw [actual_context_nat_code] at hc
  cases Option.some.inj hc
  with_reducible exact context_nat_code_sim kind C.base

def contextRegisterNames : List String :=
  ([.current, .signer, .signerPk, .predecessor, .refund, .chain, .input, .random] :
    List ContextRegisterHost).map contextRegisterName

def contextNatNames : List String :=
  ([.block, .timestamp, .epoch, .usage, .prepaid, .used, .results] : List ContextNatHost).map contextNatName

theorem actual_context_host_sim (name : String) (hn : name ∈ contextRegisterNames ++ contextNatNames)
    (call : HM Unit) (hc : hostCall name = some call) : HostSim call call := by
  simp only [List.mem_append, contextRegisterNames, contextNatNames, List.mem_map] at hn
  rcases hn with ⟨kind, _, rfl⟩ | ⟨kind, _, rfl⟩
  · exact actual_context_register_sim kind call hc
  · exact actual_context_nat_sim kind call hc

end NearCompression
