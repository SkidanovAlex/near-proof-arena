import NearCompression.BalanceHosts

/-! Return bytes and their data-receipt charges are part of observable execution. -/
namespace NearCompression
open NearSpecV3.Wasm

def returnCommit (value : ByteArray) (burn : Nat) : HM Unit := do
  payActionH burn burn burn
  modify fun s => { s with ret := some (.inl value) }

theorem return_commit_sim (value : ByteArray) (burn : Nat) :
    HostSim (returnCommit value burn) (returnCommit value burn) := by
  unfold returnCommit
  with_reducible apply host_sim_bind
  · unfold payActionH
    exact host_sim_with_gas _
  intro _ s t h
  exact ⟨rfl, congrArg (fun s : St => { s with ret := some (.inl value) }) h.core, h.real⟩

def returnCheckedCommit (value : ByteArray) (burn : Nat) : HM Unit := do
  if burn ≥ u64Bound then hErr "IntegerOverflow"
  returnCommit value burn

theorem return_checked_commit_sim (value : ByteArray) (burn : Nat) :
    HostSim (returnCheckedCommit value burn) (returnCheckedCommit value burn) := by
  unfold returnCheckedCommit
  split
  · with_reducible apply host_sim_bind
    · exact host_sim_error _
    intro _
    exact return_commit_sim value burn
  · exact return_commit_sim value burn

def returnFinish (fee : Fee3) (value : ByteArray) : HM Unit := do
  let s ← get
  let burn := s.ctx.receivers.foldl (fun acc r =>
    let sir := r = s.ctx.currentAccount
    acc + (fee.send sir + fee.exec) * value.size) 0
  returnCheckedCommit value burn

theorem return_finish_sim (fee : Fee3) (value : ByteArray) :
    HostSim (returnFinish fee value) (returnFinish fee value) := by
  unfold returnFinish
  apply host_sim_get_bind
  intro s t h
  have hc : s.ctx = t.ctx := by have he := congrArg St.ctx h.core; exact he
  rw [hc]
  exact return_checked_commit_sim value _ s t h

def valueReturnCode (base : Cost) (fee : Fee3) : HM Unit := do
  let a ← popArgs 2
  payBaseH base
  let v ← memOrRegH a[1] a[0]
  if v.size > maxLengthReturnedData then
    hErr s!"ReturnedValueLengthExceeded \{ length: {v.size}, limit: {maxLengthReturnedData} }"
  returnFinish fee v

theorem value_return_code_sim (base : Cost) (fee : Fee3) :
    HostSim (valueReturnCode base fee) (valueReturnCode base fee) := by
  unfold valueReturnCode
  with_reducible apply host_sim_bind
  · exact host_sim_pop_args 2
  intro a
  with_reducible apply host_sim_bind
  · unfold payBaseH
    exact host_sim_with_gas _
  intro _
  with_reducible apply host_sim_bind
  · with_reducible exact host_sim_mem_or_reg a[1] a[0]
  intro value
  dsimp only
  split
  · with_reducible apply host_sim_bind
    · exact host_sim_error _
    intro _
    exact return_finish_sim fee value
  · exact return_finish_sim fee value

theorem actual_value_return_code : hostCall "value_return" =
    some (valueReturnCode C.base F.newDataReceiptByte) := by rfl

theorem actual_value_return_sim (call : HM Unit)
    (hc : hostCall "value_return" = some call) : HostSim call call := by
  rw [actual_value_return_code] at hc
  cases Option.some.inj hc
  with_reducible exact value_return_code_sim C.base F.newDataReceiptByte

end NearCompression
