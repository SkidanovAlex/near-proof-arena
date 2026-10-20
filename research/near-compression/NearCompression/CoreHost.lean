import NearCompression.StorageEquivalence

/-! Compositional simulation for gas and read-only memory/register host code.
The relation keeps all non-map fields exact; failures keep the charged state. -/
namespace NearCompression
open NearSpecV3.Wasm

def HostSim {A : Type} (x y : HM A) : Prop :=
  ∀ s t, StateEquivalent s t → HostResultEquivalent (x.run s) (y.run t)

theorem host_sim_pure {A : Type} (a : A) : HostSim (pure a) (pure a) :=
  fun _ _ hs => ⟨rfl, hs⟩

theorem host_sim_error {A : Type} (e : String) : HostSim (hErr e : HM A) (hErr e) :=
  fun _ _ hs => ⟨rfl, hs⟩

theorem host_sim_bind {A B : Type} (x y : HM A) (f g : A → HM B)
    (h : HostSim x y) (hn : ∀ a, HostSim (f a) (g a)) :
    HostSim (x >>= f) (y >>= g) := by
  intro s t hs
  exact host_bind_equiv x y f g s t (h s t hs) (fun a u v huv => hn a u v huv)

theorem host_sim_get_bind {A : Type} (f g : St → HM A)
    (h : ∀ s t, StateEquivalent s t → HostResultEquivalent ((f s).run s) ((g t).run t)) :
    HostSim (get >>= f) (get >>= g) := h

theorem state_equiv_set_gas (s t : St) (h : StateEquivalent s t) (gas : Gas) :
    StateEquivalent { s with gas } { t with gas } :=
  ⟨congrArg (fun s : St => { s with gas }) h.core, h.real⟩

theorem with_gas_run (f : Gas → Gas × Option String) (s : St) :
    (withGas f).run s =
      let out := f s.gas
      let t := { s with gas := out.1 }
      match out.2 with
      | none => .ok () t
      | some e => .error e t := by
  let out := f s.gas
  let t := { s with gas := out.1 }
  change (match out.2 with | some e => EStateM.throw e | none => EStateM.pure ()) t =
    (match out.2 with | none => .ok () t | some e => .error e t)
  cases out.2 <;> rfl

theorem host_sim_with_gas (f : Gas → Gas × Option String) : HostSim (withGas f) (withGas f) := by
  intro s t hs
  rw [with_gas_run, with_gas_run, state_equiv_gas s t hs]
  dsimp only
  cases (f t.gas).2 <;> exact ⟨rfl, state_equiv_set_gas s t hs _⟩

theorem state_equiv_mem_bytes (s t : St) (h : StateEquivalent s t) : memBytes s = memBytes t := by
  have hm := congrArg memBytes h.core
  exact hm

theorem state_equiv_read_byte (s t : St) (h : StateEquivalent s t) (addr : Nat) :
    readByte s addr = readByte t addr := by
  have hm := congrArg (fun s => readByte s addr) h.core
  exact hm

theorem state_equiv_read_bytes (s t : St) (h : StateEquivalent s t) (addr len : Nat) :
    readBytes s addr len = readBytes t addr len := by
  have hm := congrArg (fun s => readBytes s addr len) h.core
  exact hm

/-- Parameterized copy of the read sequence, definitionally equal to the
actual helper at its protocol costs. Abstract costs avoid numeral reduction
while elaborating the simulation proof. -/
def chargedRead (base byte : Cost) (ptr len : Nat) : HM ByteArray := do
  payBaseH base
  payPerH byte len
  let s ← get
  if ptr + len > memBytes s then hErr "MemoryAccessViolation"
  pure (readBytes s ptr len)

/-- Actual host memory reads: both gas charges occur before bounds checking. -/
theorem host_sim_charged_read (base byte : Cost) (ptr len : Nat) :
    HostSim (chargedRead base byte ptr len) (chargedRead base byte ptr len) := by
  let finish : St → HM ByteArray := fun s => do
    if ptr + len > memBytes s then hErr "MemoryAccessViolation"
    pure (readBytes s ptr len)
  let rest : Unit → HM ByteArray := fun _ => get >>= finish
  let afterBase : Unit → HM ByteArray := fun _ => withGas (fun gs => payPer gs byte len) >>= rest
  change HostSim (withGas (fun gs => payBase gs base) >>= afterBase)
    (withGas (fun gs => payBase gs base) >>= afterBase)
  have hb : HostSim (withGas (fun gs => payBase gs base)) (withGas (fun gs => payBase gs base)) := by
    exact host_sim_with_gas _
  have hp : HostSim (withGas (fun gs => payPer gs byte len)) (withGas (fun gs => payPer gs byte len)) := by
    exact host_sim_with_gas _
  have hh := @host_sim_bind Unit ByteArray (withGas (fun gs => payBase gs base)) (withGas (fun gs => payBase gs base)) afterBase afterBase hb
  apply hh
  intro _
  change HostSim (withGas (fun gs => payPer gs byte len) >>= rest) (withGas (fun gs => payPer gs byte len) >>= rest)
  have hh2 := @host_sim_bind Unit ByteArray (withGas (fun gs => payPer gs byte len)) (withGas (fun gs => payPer gs byte len)) rest rest hp
  apply hh2
  intro _
  apply host_sim_get_bind finish finish
  intro s t hs
  dsimp only [finish]
  rw [state_equiv_mem_bytes s t hs, state_equiv_read_bytes s t hs]
  split <;> exact ⟨rfl, hs⟩

/-- The original host helper is the exact instantiation of the proved
sequence: no cost, error, or ordering change is made. -/
theorem host_sim_read_mem (ptr len : Nat) : HostSim (readMemH ptr len) (readMemH ptr len) := by
  change HostSim (chargedRead C.readMemoryBase C.readMemoryByte ptr len)
    (chargedRead C.readMemoryBase C.readMemoryByte ptr len)
  with_reducible exact host_sim_charged_read C.readMemoryBase C.readMemoryByte ptr len

def chargedReturn {A : Type} (base byte : Cost) (len : Nat) (value : A) : HM A := do
  payBaseH base
  payPerH byte len
  pure value

theorem host_sim_charged_return {A : Type} (base byte : Cost) (len : Nat) (value : A) :
    HostSim (chargedReturn base byte len value) (chargedReturn base byte len value) := by
  unfold chargedReturn
  with_reducible apply host_sim_bind
  · unfold payBaseH
    exact host_sim_with_gas _
  intro _
  with_reducible apply host_sim_bind
  · unfold payPerH
    exact host_sim_with_gas _
  intro _
  exact host_sim_pure value

theorem host_sim_reg_get (id : Nat) : HostSim (regGetH id) (regGetH id) := by
  intro s t hs
  unfold regGetH
  rw [host_get_bind_run, host_get_bind_run]
  have he : s.registers = t.registers := by
    have h := congrArg St.registers hs.core
    exact h
  rw [he]
  split
  · rename_i idx bytes found
    change HostResultEquivalent
      ((chargedReturn C.readRegisterBase C.readRegisterByte bytes.size bytes).run s)
      ((chargedReturn C.readRegisterBase C.readRegisterByte bytes.size bytes).run t)
    have hg : HostSim
        (chargedReturn C.readRegisterBase C.readRegisterByte bytes.size bytes)
        (chargedReturn C.readRegisterBase C.readRegisterByte bytes.size bytes) := by
      with_reducible exact host_sim_charged_return C.readRegisterBase C.readRegisterByte bytes.size bytes
    unfold HostSim at hg
    with_reducible exact hg s t hs
  · exact ⟨rfl, hs⟩

theorem host_sim_mem_or_reg (ptr len : Nat) : HostSim (memOrRegH ptr len) (memOrRegH ptr len) := by
  unfold memOrRegH
  split
  · with_reducible exact host_sim_reg_get ptr
  · with_reducible exact host_sim_read_mem ptr len

end NearCompression
