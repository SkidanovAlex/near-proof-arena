import NearCompression.LegacyHosts

/-! Validator queries preserve context lookup, aggregation and memory output. -/
namespace NearCompression
open NearSpecV3.Wasm

def validatorOutput (write : Nat → Nat → HM Unit) (select : Array (String × Nat) → Nat) (ptr : Nat) : HM Unit := do
  write ptr (select (← get).ctx.validators)

theorem validator_output_sim (write : Nat → Nat → HM Unit)
    (writeSim : ∀ ptr val, HostSim (write ptr val) (write ptr val)) (select : Array (String × Nat) → Nat) (ptr : Nat) :
    HostSim (validatorOutput write select ptr) (validatorOutput write select ptr) := by
  unfold validatorOutput
  apply host_sim_get_bind
  intro s t h
  have hc : s.ctx = t.ctx := by have he := congrArg St.ctx h.core; exact he
  rw [hc]
  exact writeSim ptr (select t.ctx.validators) s t h

def validatorStakeCode (base stakeBase : Cost) (readAccount : Nat → Nat → HM String) (write : Nat → Nat → HM Unit) : HM Unit := do
  let a ← popArgs 3
  payBaseH base
  let acct ← readAccount a[0] a[1]
  payBaseH stakeBase
  validatorOutput write (fun vs => ((vs.find? (·.1 = acct)).map (·.2)).getD 0) a[2]

theorem validator_stake_code_sim (base stakeBase : Cost) (readAccount : Nat → Nat → HM String)
    (write : Nat → Nat → HM Unit) (writeSim : ∀ ptr val, HostSim (write ptr val) (write ptr val))
    (readSim : ∀ len ptr, HostSim (readAccount len ptr) (readAccount len ptr)) :
    HostSim (validatorStakeCode base stakeBase readAccount write) (validatorStakeCode base stakeBase readAccount write) := by
  unfold validatorStakeCode
  apply host_sim_bind
  · exact host_sim_pop_args 3
  intro a
  apply host_sim_bind
  · unfold payBaseH; exact host_sim_with_gas _
  intro _
  apply host_sim_bind
  · exact readSim _ _
  intro acct
  apply host_sim_bind
  · unfold payBaseH; exact host_sim_with_gas _
  intro _
  exact validator_output_sim write writeSim _ _

def validatorTotalCode (base totalBase : Cost) (write : Nat → Nat → HM Unit) : HM Unit := do
  let a ← popArgs 1
  payBaseH base
  payBaseH totalBase
  validatorOutput write (fun vs => vs.foldl (fun acc v => acc + v.2) 0) a[0]

theorem validator_total_code_sim (base totalBase : Cost) (write : Nat → Nat → HM Unit)
    (writeSim : ∀ ptr val, HostSim (write ptr val) (write ptr val)) :
    HostSim (validatorTotalCode base totalBase write) (validatorTotalCode base totalBase write) := by
  unfold validatorTotalCode
  apply host_sim_bind
  · exact host_sim_pop_args 1
  intro a
  apply host_sim_bind
  · unfold payBaseH; exact host_sim_with_gas _
  intro _
  apply host_sim_bind
  · unfold payBaseH; exact host_sim_with_gas _
  intro _
  exact validator_output_sim write writeSim _ _

theorem actual_validator_stake_code : hostCall "validator_stake" =
    some (validatorStakeCode C.base C.validatorStakeBase readAccountIdH setU128H) := by rfl

theorem actual_validator_total_code : hostCall "validator_total_stake" =
    some (validatorTotalCode C.base C.validatorTotalStakeBase setU128H) := by rfl

theorem actual_validator_stake_sim (call : HM Unit)
    (hc : hostCall "validator_stake" = some call) : HostSim call call := by
  rw [actual_validator_stake_code] at hc
  cases Option.some.inj hc
  with_reducible exact validator_stake_code_sim C.base C.validatorStakeBase readAccountIdH setU128H host_sim_set_u128 host_sim_read_account_id

theorem actual_validator_total_sim (call : HM Unit)
    (hc : hostCall "validator_total_stake" = some call) : HostSim call call := by
  rw [actual_validator_total_code] at hc
  cases Option.some.inj hc
  with_reducible exact validator_total_code_sim C.base C.validatorTotalStakeBase setU128H host_sim_set_u128

end NearCompression
