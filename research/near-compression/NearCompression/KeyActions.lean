import NearCompression.DeployAction

/-! Key action construction preserves validation after fee charging. -/
namespace NearCompression
open NearSpecV3.Wasm

def keyActionCode (n : Nat) (hn : 2 < n) (base : Cost) (fee : Fee3)
    (read : Nat → Nat → HM ByteArray) (render : Vector Nat n → Nat → ByteArray → String) : HM Unit := do
  let a ← popArgs n
  payBaseH base
  let pk ← read a[2] a[1]
  let (r, sir) ← promiseReceiptH a[0]
  payActionBaseH fee sir
  if !pkValid pk then hErr "InvalidPublicKey"
  let _ ← pushAction { text := render a r pk }

theorem key_action_code_sim (n : Nat) (hn : 2 < n) (base : Cost) (fee : Fee3)
    (read : Nat → Nat → HM ByteArray) (render : Vector Nat n → Nat → ByteArray → String)
    (readSim : ∀ ptr len, HostSim (read ptr len) (read ptr len)) :
    HostSim (keyActionCode n hn base fee read render) (keyActionCode n hn base fee read render) := by
  unfold keyActionCode
  apply host_sim_bind
  · exact host_sim_pop_args n
  intro a
  apply host_sim_bind
  · unfold payBaseH; exact host_sim_with_gas _
  intro _
  apply host_sim_bind
  · exact readSim _ _
  intro pk
  apply host_sim_bind
  · exact host_sim_promise_receipt _
  intro receipt
  apply host_sim_bind
  · exact host_sim_action_base _ _
  intro _
  dsimp only
  split
  · simp only [host_error_bind]; exact host_sim_error _
  · apply host_sim_bind
    · exact host_sim_push_action _
    intro _
    exact host_sim_pure ()

def fullAccessText (a : Vector Nat 4) (r : Nat) (pk : ByteArray) : String :=
  s!"AF@{r}:{hexStr pk}:{a[3]}"
def deleteKeyText (_ : Vector Nat 3) (r : Nat) (pk : ByteArray) : String :=
  s!"DK@{r}:{hexStr pk}"

theorem actual_full_access_code : hostCall "promise_batch_action_add_key_with_full_access" =
    some (keyActionCode 4 (by decide) C.base F.addFullAccessKey memOrRegH fullAccessText) := by rfl

theorem actual_delete_key_code : hostCall "promise_batch_action_delete_key" =
    some (keyActionCode 3 (by decide) C.base F.deleteKey memOrRegH deleteKeyText) := by rfl

theorem actual_full_access_sim (call : HM Unit)
    (hc : hostCall "promise_batch_action_add_key_with_full_access" = some call) : HostSim call call := by
  rw [actual_full_access_code] at hc
  cases Option.some.inj hc
  with_reducible exact key_action_code_sim 4 (by decide) C.base F.addFullAccessKey memOrRegH fullAccessText host_sim_mem_or_reg

theorem actual_delete_key_sim (call : HM Unit)
    (hc : hostCall "promise_batch_action_delete_key" = some call) : HostSim call call := by
  rw [actual_delete_key_code] at hc
  cases Option.some.inj hc
  with_reducible exact key_action_code_sim 3 (by decide) C.base F.deleteKey memOrRegH deleteKeyText host_sim_mem_or_reg

end NearCompression
