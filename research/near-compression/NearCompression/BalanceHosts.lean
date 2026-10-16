import NearCompression.RegisterHosts

/-! Balance and deposit queries preserve the actual 16-byte little-endian
memory output, charge order, and failure state. -/
namespace NearCompression
open NearSpecV3.Wasm

def getU128Code (base byte : Cost) (ptr : Nat) : HM Nat := do
  pure (leNat (← chargedRead base byte ptr 16))

theorem get_u128_code_sim (base byte : Cost) (ptr : Nat) :
    HostSim (getU128Code base byte ptr) (getU128Code base byte ptr) := by
  unfold getU128Code
  with_reducible apply host_sim_bind
  · exact host_sim_charged_read base byte ptr 16
  intro bytes
  exact host_sim_pure (leNat bytes)

theorem host_sim_get_u128 (ptr : Nat) : HostSim (getU128H ptr) (getU128H ptr) := by
  change HostSim (getU128Code C.readMemoryBase C.readMemoryByte ptr)
    (getU128Code C.readMemoryBase C.readMemoryByte ptr)
  with_reducible exact get_u128_code_sim C.readMemoryBase C.readMemoryByte ptr

theorem host_sim_set_u128 (ptr value : Nat) : HostSim (setU128H ptr value) (setU128H ptr value) := by
  unfold setU128H
  with_reducible exact host_sim_write_mem ptr (natLE value 16)

inductive BalanceHost where
  | available | locked | deposit

def balanceHostName : BalanceHost → String
  | .available => "account_balance"
  | .locked => "account_locked_balance"
  | .deposit => "attached_deposit"

def balanceHostValue : BalanceHost → St → Nat
  | .available, s => s.balance
  | .locked, s => s.ctx.accountLocked
  | .deposit, s => s.ctx.attachedDeposit

theorem balance_host_value_equiv (kind : BalanceHost) (s t : St) (h : StateEquivalent s t) :
    balanceHostValue kind s = balanceHostValue kind t := by
  have he := congrArg (balanceHostValue kind) h.core
  cases kind <;> exact he

def balanceHostCode (kind : BalanceHost) (base memoryBase memoryByte : Cost) : HM Unit := do
  let args ← popArgs 1
  payBaseH base
  let s ← get
  chargedMemoryWrite memoryBase memoryByte args[0] (natLE (balanceHostValue kind s) 16)

theorem balance_host_code_sim (kind : BalanceHost) (base memoryBase memoryByte : Cost) :
    HostSim (balanceHostCode kind base memoryBase memoryByte)
      (balanceHostCode kind base memoryBase memoryByte) := by
  unfold balanceHostCode
  with_reducible apply host_sim_bind
  · exact host_sim_pop_args 1
  intro args
  with_reducible apply host_sim_bind
  · unfold payBaseH
    exact host_sim_with_gas _
  intro _
  apply host_sim_get_bind
  intro s t h
  rw [balance_host_value_equiv kind s t h]
  exact host_sim_charged_memory_write memoryBase memoryByte args[0] _ s t h

theorem actual_balance_host_code (kind : BalanceHost) : hostCall (balanceHostName kind) =
    some (balanceHostCode kind C.base C.writeMemoryBase C.writeMemoryByte) := by
  cases kind <;> rfl

theorem actual_balance_host_sim (kind : BalanceHost) (call : HM Unit)
    (hc : hostCall (balanceHostName kind) = some call) : HostSim call call := by
  rw [actual_balance_host_code] at hc
  cases Option.some.inj hc
  with_reducible exact balance_host_code_sim kind C.base C.writeMemoryBase C.writeMemoryByte

def balanceHostNames : List String :=
  ([.available, .locked, .deposit] : List BalanceHost).map balanceHostName

theorem listed_balance_host_sim (name : String) (hn : name ∈ balanceHostNames)
    (call : HM Unit) (hc : hostCall name = some call) : HostSim call call := by
  simp only [balanceHostNames, List.mem_map] at hn
  obtain ⟨kind, _, rfl⟩ := hn
  exact actual_balance_host_sim kind call hc

end NearCompression
