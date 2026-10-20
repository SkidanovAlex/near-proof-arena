import NearCompression.ContextHosts

/-! Register dispatches, preserving exact argument order, charges and errors. -/
namespace NearCompression
open NearSpecV3.Wasm

def readRegisterCode (base : Cost) : HM Unit := do
  let a ← popArgs 2
  payBaseH base
  let d ← regGetH a[0]
  writeMemH a[1] d

def writeRegisterCode (base readBase readByte writeBase writeByte : Cost) : HM Unit := do
  let a ← popArgs 3
  payBaseH base
  let d ← chargedRead readBase readByte a[2] a[1]
  chargedRegisterWrite writeBase writeByte a[0] d true

def registerLenCode (base : Cost) : HM Unit := do
  let a ← popArgs 1
  payBaseH base
  pushRet (((← get).registers.find? (·.1 = a[0])).map (·.2.size) |>.getD (u64Bound - 1))

theorem read_register_code_sim (base : Cost) : HostSim (readRegisterCode base) (readRegisterCode base) := by
  unfold readRegisterCode
  with_reducible apply host_sim_bind
  · exact host_sim_pop_args 2
  intro a
  with_reducible apply host_sim_bind
  · unfold payBaseH
    exact host_sim_with_gas _
  intro _
  with_reducible apply host_sim_bind
  · with_reducible exact host_sim_reg_get a[0]
  intro bytes
  with_reducible exact host_sim_write_mem a[1] bytes

theorem write_register_code_sim (base readBase readByte writeBase writeByte : Cost) :
    HostSim (writeRegisterCode base readBase readByte writeBase writeByte)
      (writeRegisterCode base readBase readByte writeBase writeByte) := by
  unfold writeRegisterCode
  with_reducible apply host_sim_bind
  · exact host_sim_pop_args 3
  intro a
  with_reducible apply host_sim_bind
  · unfold payBaseH
    exact host_sim_with_gas _
  intro _
  with_reducible apply host_sim_bind
  · exact host_sim_charged_read readBase readByte a[2] a[1]
  intro bytes
  exact host_sim_charged_register_write writeBase writeByte a[0] bytes true

theorem register_len_code_sim (base : Cost) : HostSim (registerLenCode base) (registerLenCode base) := by
  unfold registerLenCode
  with_reducible apply host_sim_bind
  · exact host_sim_pop_args 1
  intro a
  with_reducible apply host_sim_bind
  · unfold payBaseH
    exact host_sim_with_gas _
  intro _
  apply host_sim_get_bind
  intro s t h
  have hr : s.registers = t.registers := by have he := congrArg St.registers h.core; exact he
  rw [hr]
  exact host_sim_push_ret _ true s t h

theorem actual_read_register_code : hostCall "read_register" = some (readRegisterCode C.base) := by rfl

theorem actual_write_register_code : hostCall "write_register" = some (writeRegisterCode C.base C.readMemoryBase C.readMemoryByte C.writeRegisterBase C.writeRegisterByte) := by rfl

theorem actual_register_len_code : hostCall "register_len" = some (registerLenCode C.base) := by rfl

theorem actual_register_host_sim (name : String)
    (hn : name ∈ ["read_register", "write_register", "register_len"])
    (call : HM Unit) (hc : hostCall name = some call) : HostSim call call := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with hn | hn | hn
  · subst name
    rw [actual_read_register_code] at hc
    cases Option.some.inj hc
    with_reducible exact read_register_code_sim C.base
  · subst name
    rw [actual_write_register_code] at hc
    cases Option.some.inj hc
    with_reducible exact write_register_code_sim C.base C.readMemoryBase C.readMemoryByte C.writeRegisterBase C.writeRegisterByte
  · subst name
    rw [actual_register_len_code] at hc
    cases Option.some.inj hc
    with_reducible exact register_len_code_sim C.base

end NearCompression
