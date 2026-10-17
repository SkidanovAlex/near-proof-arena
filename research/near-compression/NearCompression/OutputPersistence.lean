import NearCompression.ContextPersistence

/-! Backend persistence for balance outputs, value returns and Ed25519 execution.
No signature security property is assumed or established. -/
namespace NearCompression
open NearSpecV3.Wasm

theorem balance_host_code_keeps_real (kind : BalanceHost) (base memoryBase memoryByte : Cost) :
    HostKeepsReal (balanceHostCode kind base memoryBase memoryByte) := by
  unfold balanceHostCode
  with_reducible apply host_real_bind
  · exact host_real_pop_args 1
  intro args
  with_reducible apply host_real_bind
  · unfold payBaseH
    exact host_real_with_gas _
  intro _
  apply host_real_get_bind
  intro s hs
  exact host_real_charged_memory_write memoryBase memoryByte args[0] _ s hs

theorem actual_balance_host_keeps_real (kind : BalanceHost) (call : HM Unit)
    (hc : hostCall (balanceHostName kind) = some call) : HostKeepsReal call := by
  rw [actual_balance_host_code] at hc
  cases Option.some.inj hc
  with_reducible exact balance_host_code_keeps_real kind C.base C.writeMemoryBase C.writeMemoryByte

theorem listed_balance_host_keeps_real (name : String) (hn : name ∈ balanceHostNames)
    (call : HM Unit) (hc : hostCall name = some call) : HostKeepsReal call := by
  simp only [balanceHostNames, List.mem_map] at hn
  obtain ⟨kind, _, rfl⟩ := hn
  exact actual_balance_host_keeps_real kind call hc

theorem return_commit_keeps_real (value : ByteArray) (burn : Nat) :
    HostKeepsReal (returnCommit value burn) := by
  unfold returnCommit
  with_reducible apply host_real_bind
  · unfold payActionH
    exact host_real_with_gas _
  intro _ s hs
  exact hs

theorem return_checked_commit_keeps_real (value : ByteArray) (burn : Nat) :
    HostKeepsReal (returnCheckedCommit value burn) := by
  unfold returnCheckedCommit
  split
  · with_reducible apply host_real_bind
    · exact host_real_throw _
    intro _
    exact return_commit_keeps_real value burn
  · exact return_commit_keeps_real value burn

theorem return_finish_keeps_real (fee : Fee3) (value : ByteArray) :
    HostKeepsReal (returnFinish fee value) := by
  unfold returnFinish
  apply host_real_get_bind
  intro s hs
  exact return_checked_commit_keeps_real value _ s hs

theorem value_return_code_keeps_real (base : Cost) (fee : Fee3) :
    HostKeepsReal (valueReturnCode base fee) := by
  unfold valueReturnCode
  with_reducible apply host_real_bind
  · exact host_real_pop_args 2
  intro a
  with_reducible apply host_real_bind
  · unfold payBaseH
    exact host_real_with_gas _
  intro _
  with_reducible apply host_real_bind
  · with_reducible exact host_real_mem_or_reg a[1] a[0]
  intro value
  dsimp only
  split
  · with_reducible apply host_real_bind
    · exact host_real_throw _
    intro _
    exact return_finish_keeps_real fee value
  · exact return_finish_keeps_real fee value

theorem actual_value_return_keeps_real (call : HM Unit)
    (hc : hostCall "value_return" = some call) : HostKeepsReal call := by
  rw [actual_value_return_code] at hc
  cases Option.some.inj hc
  with_reducible exact value_return_code_keeps_real C.base F.newDataReceiptByte

theorem ed25519_code_keeps_real (base byte : Cost) (read : Nat → Nat → HM ByteArray)
    (readSim : ∀ ptr len, HostKeepsReal (read ptr len)) :
    HostKeepsReal (ed25519Code base byte read) := by
  unfold ed25519Code
  apply host_real_bind
  · exact host_real_pop_args 6
  intro args
  apply host_real_bind
  · unfold payBaseH
    exact host_real_with_gas _
  intro _
  apply host_real_bind
  · exact readSim args[1] args[0]
  intro sig
  dsimp only
  split
  · exact host_real_throw _
  · split
    · exact host_real_push_ret 0 true
    · apply host_real_bind
      · exact readSim args[3] args[2]
      intro msg
      apply host_real_bind
      · unfold payPerH
        exact host_real_with_gas _
      intro _
      apply host_real_bind
      · exact readSim args[5] args[4]
      intro pk
      split
      · apply host_real_bind
        · exact host_real_throw _
        intro _
        exact host_real_push_ret _ true
      · exact host_real_push_ret _ true

theorem actual_ed25519_keeps_real (call : HM Unit) (hc : hostCall "ed25519_verify" = some call) :
    HostKeepsReal call := by
  rw [actual_ed25519_code] at hc
  cases Option.some.inj hc
  with_reducible exact ed25519_code_keeps_real C.ed25519VerifyBase C.ed25519VerifyByte memOrRegH host_real_mem_or_reg

theorem validator_output_keeps_real (write : Nat → Nat → HM Unit)
    (writeSim : ∀ ptr val, HostKeepsReal (write ptr val)) (select : Array (String × Nat) → Nat) (ptr : Nat) :
    HostKeepsReal (validatorOutput write select ptr) := by
  unfold validatorOutput
  apply host_real_get_bind
  intro s hs
  exact writeSim ptr (select s.ctx.validators) s hs

theorem validator_stake_code_keeps_real (base stakeBase : Cost) (readAccount : Nat → Nat → HM String)
    (write : Nat → Nat → HM Unit) (writeSim : ∀ ptr val, HostKeepsReal (write ptr val))
    (readSim : ∀ len ptr, HostKeepsReal (readAccount len ptr)) :
    HostKeepsReal (validatorStakeCode base stakeBase readAccount write) := by
  unfold validatorStakeCode
  apply host_real_bind
  · exact host_real_pop_args 3
  intro a
  apply host_real_bind
  · unfold payBaseH; exact host_real_with_gas _
  intro _
  apply host_real_bind
  · exact readSim _ _
  intro acct
  apply host_real_bind
  · unfold payBaseH; exact host_real_with_gas _
  intro _
  exact validator_output_keeps_real write writeSim _ _

theorem validator_total_code_keeps_real (base totalBase : Cost) (write : Nat → Nat → HM Unit)
    (writeSim : ∀ ptr val, HostKeepsReal (write ptr val)) :
    HostKeepsReal (validatorTotalCode base totalBase write) := by
  unfold validatorTotalCode
  apply host_real_bind
  · exact host_real_pop_args 1
  intro a
  apply host_real_bind
  · unfold payBaseH; exact host_real_with_gas _
  intro _
  apply host_real_bind
  · unfold payBaseH; exact host_real_with_gas _
  intro _
  exact validator_output_keeps_real write writeSim _ _

theorem actual_validator_stake_keeps_real (call : HM Unit)
    (hc : hostCall "validator_stake" = some call) : HostKeepsReal call := by
  rw [actual_validator_stake_code] at hc
  cases Option.some.inj hc
  with_reducible exact validator_stake_code_keeps_real C.base C.validatorStakeBase readAccountIdH setU128H host_real_set_u128 host_real_read_account_id

theorem actual_validator_total_keeps_real (call : HM Unit)
    (hc : hostCall "validator_total_stake" = some call) : HostKeepsReal call := by
  rw [actual_validator_total_code] at hc
  cases Option.some.inj hc
  with_reducible exact validator_total_code_keeps_real C.base C.validatorTotalStakeBase setU128H host_real_set_u128

end NearCompression
