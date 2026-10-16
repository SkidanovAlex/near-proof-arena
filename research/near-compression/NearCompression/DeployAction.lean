import NearCompression.PromiseCalls

/-! Local contract deployment action: reads, limits, fees and ordered insertion. -/
namespace NearCompression
open NearSpecV3.Wasm

def deployActionCode (base : Cost) (fee byteFee : Fee3)
    (read : Nat → Nat → HM ByteArray) : HM Unit := do
  let a ← popArgs 3
  payBaseH base
  let code ← read a[2] a[1]
  if code.size > maxContractSize then
    hErr s!"ContractSizeExceeded \{ size: {code.size}, limit: {maxContractSize} }"
  let (r, sir) ← promiseReceiptH a[0]
  payActionBaseH fee sir
  payActionPerByteH byteFee code.size sir
  let _ ← pushAction { text := s!"DC@{r}:{hexStr code}" }

theorem deploy_action_code_sim (base : Cost) (fee byteFee : Fee3)
    (read : Nat → Nat → HM ByteArray)
    (readSim : ∀ ptr len, HostSim (read ptr len) (read ptr len)) :
    HostSim (deployActionCode base fee byteFee read) (deployActionCode base fee byteFee read) := by
  unfold deployActionCode
  apply host_sim_bind
  · exact host_sim_pop_args 3
  intro a
  apply host_sim_bind
  · unfold payBaseH; exact host_sim_with_gas _
  intro _
  apply host_sim_bind
  · exact readSim _ _
  intro code
  dsimp only
  split
  · simp only [host_error_bind]; exact host_sim_error _
  · apply host_sim_bind
    · exact host_sim_promise_receipt _
    intro receipt
    apply host_sim_bind
    · exact host_sim_action_base _ _
    intro _
    apply host_sim_bind
    · exact host_sim_action_byte _ _ _
    intro _
    apply host_sim_bind
    · exact host_sim_push_action _
    intro _
    exact host_sim_pure ()

theorem actual_deploy_action_code : hostCall "promise_batch_action_deploy_contract" =
    some (deployActionCode C.base F.deployContract F.deployContractByte memOrRegH) := by rfl

theorem actual_deploy_action_sim (call : HM Unit)
    (hc : hostCall "promise_batch_action_deploy_contract" = some call) : HostSim call call := by
  rw [actual_deploy_action_code] at hc
  cases Option.some.inj hc
  with_reducible exact deploy_action_code_sim C.base F.deployContract F.deployContractByte memOrRegH host_sim_mem_or_reg

def createAccountActionCode (base : Cost) (fee : Fee3) : HM Unit := do
  let a ← popArgs 1
  payBaseH base
  let (r, sir) ← promiseReceiptH a[0]
  payActionBaseH fee sir
  let _ ← pushAction { text := s!"CA@{r}" }

theorem create_account_action_code_sim (base : Cost) (fee : Fee3) :
    HostSim (createAccountActionCode base fee) (createAccountActionCode base fee) := by
  unfold createAccountActionCode
  apply host_sim_bind
  · exact host_sim_pop_args 1
  intro a
  apply host_sim_bind
  · unfold payBaseH; exact host_sim_with_gas _
  intro _
  apply host_sim_bind
  · exact host_sim_promise_receipt _
  intro receipt
  apply host_sim_bind
  · exact host_sim_action_base _ _
  intro _
  apply host_sim_bind
  · exact host_sim_push_action _
  intro _
  exact host_sim_pure ()

theorem actual_create_account_action_code : hostCall "promise_batch_action_create_account" =
    some (createAccountActionCode C.base F.createAccount) := by rfl

theorem actual_create_account_action_sim (call : HM Unit)
    (hc : hostCall "promise_batch_action_create_account" = some call) : HostSim call call := by
  rw [actual_create_account_action_code] at hc
  cases Option.some.inj hc
  with_reducible exact create_account_action_code_sim C.base F.createAccount

end NearCompression
