import NearCompression.CoreHost

/-! Simulation of state-mutating host helpers under logical map equivalence.
All register metadata, byte values, gas and failures remain exact. -/
namespace NearCompression
open NearSpecV3.Wasm

theorem state_equiv_set_registers (s t : St) (h : StateEquivalent s t)
    (registers : Array (Nat × ByteArray)) (usage : Nat) :
    StateEquivalent { s with registers, regUsage := usage }
      { t with registers, regUsage := usage } :=
  ⟨congrArg (fun s : St => { s with registers, regUsage := usage }) h.core, h.real⟩

/-- Exact post-charge register body from regSetH. -/
def registerWriteBody (s : St) (id : Nat) (d : ByteArray) : HM Unit := do
  if d.size > maxRegisterSize then hErr "MemoryAccessViolation"
  if s.registers.size ≥ maxNumberRegisters then hErr "MemoryAccessViolation"
  let old := match s.registers.find? (·.1 = id) with
    | some (_, o) => o.size + 8
    | none => 0
  let usage := s.regUsage - old + (d.size + 8)
  if usage > registersMemoryLimit then hErr "MemoryAccessViolation"
  let regs := match s.registers.findIdx? (·.1 = id) with
    | some i => s.registers.set! i (id, d)
    | none => s.registers.push (id, d)
  set { s with registers := regs, regUsage := usage }

theorem register_write_body_equiv (s t : St) (h : StateEquivalent s t)
    (id : Nat) (d : ByteArray) :
    HostResultEquivalent ((registerWriteBody s id d).run s)
      ((registerWriteBody t id d).run t) := by
  have hr : s.registers = t.registers := by
    have he := congrArg St.registers h.core
    exact he
  have hu : s.regUsage = t.regUsage := by
    have he := congrArg St.regUsage h.core
    exact he
  unfold registerWriteBody
  rw [hr, hu]
  repeat' (split <;> (try simp_all only []))
  all_goals first
    | exact ⟨rfl, h⟩
    | exact ⟨rfl, state_equiv_set_registers s t h _ _⟩

/-- Generic costs prevent elaboration from evaluating concrete gas numerals.
The final theorem instantiates exactly NEAR's regSetH definition. -/
def chargedRegisterWrite (base byte : Cost) (id : Nat) (d : ByteArray)
    (chargeBytes : Bool) : HM Unit := do
  payBaseH base
  if chargeBytes then payPerH byte d.size
  let s ← get
  registerWriteBody s id d

theorem host_sim_charged_register_write (base byte : Cost) (id : Nat) (d : ByteArray)
    (chargeBytes : Bool) :
    HostSim (chargedRegisterWrite base byte id d chargeBytes)
      (chargedRegisterWrite base byte id d chargeBytes) := by
  have hb : HostSim (payBaseH base) (payBaseH base) := by
    unfold payBaseH
    exact host_sim_with_gas _
  have hp : HostSim (payPerH byte d.size) (payPerH byte d.size) := by
    unfold payPerH
    exact host_sim_with_gas _
  have hr : HostSim (get >>= fun s => registerWriteBody s id d)
      (get >>= fun s => registerWriteBody s id d) := by
    apply host_sim_get_bind
    intro s t hs
    exact register_write_body_equiv s t hs id d
  unfold chargedRegisterWrite
  with_reducible apply host_sim_bind
  · exact hb
  intro _
  cases chargeBytes
  · exact hr
  · simp only [ite_true]
    with_reducible apply host_sim_bind
    · exact hp
    intro _
    exact hr

/-- Includes the existing full-register-file replacement rejection and both
chargeBytes branches, without weakening gas or failure behavior. -/
theorem host_sim_reg_set (id : Nat) (d : ByteArray) (chargeBytes : Bool) :
    HostSim (regSetH id d chargeBytes) (regSetH id d chargeBytes) := by
  change HostSim (chargedRegisterWrite C.writeRegisterBase C.writeRegisterByte id d chargeBytes)
    (chargedRegisterWrite C.writeRegisterBase C.writeRegisterByte id d chargeBytes)
  with_reducible exact host_sim_charged_register_write C.writeRegisterBase C.writeRegisterByte id d chargeBytes

theorem state_equiv_write_byte (s t : St) (h : StateEquivalent s t) (addr : Nat) (v : UInt8) :
    StateEquivalent (writeByte s addr v) (writeByte t addr v) := by
  constructor
  · exact congrArg (fun s => writeByte s addr v) h.core
  · exact h.real

/-- The dependent-index loop used by the real memory writer preserves related
states when each iteration does. No replacement list-fold implementation. -/
theorem for_in_state_equiv : ∀ (xs : List Nat)
    (f : (x : Nat) → x ∈ xs → St → St) (s t : St), StateEquivalent s t →
    (∀ x hx u v, StateEquivalent u v → StateEquivalent (f x hx u) (f x hx v)) →
    StateEquivalent
      (forIn' (m := Id) xs s fun x hx st => ForInStep.yield (f x hx st))
      (forIn' (m := Id) xs t fun x hx st => ForInStep.yield (f x hx st))
  | [], _, _, _, hs, _ => hs
  | x :: xs, f, s, t, hs, hf => by
    simp only [List.forIn'_cons]
    exact for_in_state_equiv xs (fun y hy => f y (List.mem_cons_of_mem _ hy))
      _ _ (hf x (by simp) s t hs)
      (fun y hy u v huv => hf y _ u v huv)

theorem state_equiv_write_bytes (s t : St) (h : StateEquivalent s t) (addr : Nat) (d : ByteArray) :
    StateEquivalent (writeBytes s addr d) (writeBytes t addr d) := by
  unfold writeBytes
  simp only [Id.run, Std.Legacy.Range.forIn'_eq_forIn'_range']
  apply for_in_state_equiv _ _ s t h
  intro x hx u v huv
  exact state_equiv_write_byte u v huv _ _

def chargedMemoryWrite (base byte : Cost) (ptr : Nat) (d : ByteArray) : HM Unit := do
  payBaseH base
  payPerH byte d.size
  let s ← get
  if ptr + d.size > memBytes s then hErr "MemoryAccessViolation"
  set (writeBytes s ptr d)

theorem host_sim_charged_memory_write (base byte : Cost) (ptr : Nat) (d : ByteArray) :
    HostSim (chargedMemoryWrite base byte ptr d) (chargedMemoryWrite base byte ptr d) := by
  unfold chargedMemoryWrite
  with_reducible apply host_sim_bind
  · unfold payBaseH
    exact host_sim_with_gas _
  intro _
  with_reducible apply host_sim_bind
  · unfold payPerH
    exact host_sim_with_gas _
  intro _
  apply host_sim_get_bind
  intro s t hs
  rw [state_equiv_mem_bytes s t hs]
  split
  · exact ⟨rfl, hs⟩
  · exact ⟨rfl, state_equiv_write_bytes s t hs ptr d⟩

theorem host_sim_write_mem (ptr : Nat) (d : ByteArray) :
    HostSim (writeMemH ptr d) (writeMemH ptr d) := by
  change HostSim (chargedMemoryWrite C.writeMemoryBase C.writeMemoryByte ptr d)
    (chargedMemoryWrite C.writeMemoryBase C.writeMemoryByte ptr d)
  with_reducible exact host_sim_charged_memory_write C.writeMemoryBase C.writeMemoryByte ptr d

end NearCompression
