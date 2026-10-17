import NearCompression.CachedWriteBytes

/-! Exact charge/bounds/write phases for the actual memory-writing host helper.
Failure states retain charged gas; failed operations do not write memory. -/
namespace NearCompression
open NearSpec NearSpecV3 NearSpecV3.Wasm

def memoryWriteCharges (base byte : Cost) (length : Nat) (gas : Gas) : Gas × Option String :=
  let first := payBase gas base
  match first.2 with
  | some error => (first.1, some error)
  | none => payPer first.1 byte length

def memoryWritePhases (base byte : Cost) (s : St) (address : Nat) (data : ByteArray) :
    EStateM.Result String St Unit :=
  let charged := memoryWriteCharges base byte data.size s.gas
  let t := { s with gas := charged.1 }
  match charged.2 with
  | some error => .error error t
  | none => if address + data.size > memBytes t then .error "HostError(MemoryAccessViolation)" t
    else .ok () (writeBytes t address data)

theorem charged_memory_write_phases (base byte : Cost) (s : St) (address : Nat) (data : ByteArray) :
    (chargedMemoryWrite base byte address data).run s = memoryWritePhases base byte s address data := by
  unfold chargedMemoryWrite
  change EStateM.bind (withGas (fun g => payBase g base))
    (fun _ => EStateM.bind (withGas (fun g => payPer g byte data.size))
      (fun _ => do
        let t ← get
        if address + data.size > memBytes t then hErr "MemoryAccessViolation"
        set (writeBytes t address data))) s = _
  simp only [EStateM.bind]
  rw [show (withGas (fun g => payBase g base)) s = _ from with_gas_run _ s]
  unfold memoryWritePhases memoryWriteCharges
  cases hb : (payBase s.gas base).2 with
  | some error => simp only [hb]
  | none =>
    simp only [hb]
    rw [show (withGas (fun g => payPer g byte data.size)) { s with gas := (payBase s.gas base).1 } = _
      from with_gas_run _ _]
    cases hp : (payPer (payBase s.gas base).1 byte data.size).2 <;> simp only [hp]
    dsimp [bind, get, getThe, set, EStateM.bind, EStateM.get, EStateM.instMonadStateOf, MonadStateOf.get, HM]
    split <;> rfl

theorem actual_memory_write_phases (s : St) (address : Nat) (data : ByteArray) :
    (writeMemH address data).run s = memoryWritePhases C.writeMemoryBase C.writeMemoryByte s address data := by
  change (chargedMemoryWrite C.writeMemoryBase C.writeMemoryByte address data).run s = _
  with_reducible exact charged_memory_write_phases C.writeMemoryBase C.writeMemoryByte s address data

def hostMemoryFull : EStateM.Result String St Unit → Prop
  | .ok _ s => fullPages s.pages
  | .error _ s => fullPages s.pages

theorem memory_write_phases_full_pages (base byte : Cost) (s : St) (full : fullPages s.pages)
    (address : Nat) (data : ByteArray) :
    hostMemoryFull (memoryWritePhases base byte s address data) := by
  dsimp only [memoryWritePhases]
  split
  · exact full
  · split
    · exact full
    · exact write_bytes_full_pages { s with gas := (memoryWriteCharges base byte data.size s.gas).1 } full address data

theorem memory_write_host_full_pages (s : St) (full : fullPages s.pages) (address : Nat) (data : ByteArray) :
    hostMemoryFull ((writeMemH address data).run s) := by
  rw [actual_memory_write_phases]
  with_reducible exact memory_write_phases_full_pages C.writeMemoryBase C.writeMemoryByte s full address data

end NearCompression
