import NearCompression.PreparedMemoryAttachedExec
namespace NearCompression
open NearSpecV3.Wasm ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Sha.View ZkFormal.Sha.Sound

set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

/-- Decode every live slot, preserving its individual i32/i64 tag. -/
def preparedMemorySenderStackValue (row : Nat→Fp) (slot : Nat) : Val :=
  if row (512+slot)=0 then .i32 (UInt32.ofNat (preparedMemoryWord row (64*slot)))
  else .i64 (UInt64.ofNat (preparedMemoryWord row (64*slot)))
def preparedMemorySenderStack (row : Nat→Fp) (sp : Nat) : Array Val :=
  ((List.range sp).map (preparedMemorySenderStackValue row)).toArray

theorem prepared_memory_sender_stack_lookup (row : Nat→Fp) (sp slot : Nat) (hs:slot<sp) :
    (preparedMemorySenderStack row sp)[slot]?=some (preparedMemorySenderStackValue row slot) := by
  simp [preparedMemorySenderStack,hs]

theorem prepared_memory_sender_stack_push (row : Nat→Fp) (sp : Nat) :
    preparedMemorySenderStack row (sp+1)=
      (preparedMemorySenderStack row sp).push (preparedMemorySenderStackValue row sp) := by
  simp [preparedMemorySenderStack,List.range_succ,List.map_append]

/-- Boolean source bits give a canonical natural value; the i32 guard is
used for its narrower bound rather than silently reducing an arbitrary word. -/
theorem prepared_memory_sender_stack_value_exact (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH:TableLocal preparedMemorySenderLiteralTable tr t pub) (hr:r<tr.height t)
    (slot:Fin 8) :
    match preparedMemorySenderStackValue (tr.cell t r) slot with
    | .i32 v=>v.toNat=preparedMemoryWord (tr.cell t r) (64*slot)
    | .i64 v=>v.toNat=preparedMemoryWord (tr.cell t r) (64*slot)
    | .ref _=>False := by
  have bits : ∀b,b<64→(tr.cell t r (64*slot+b)).toNat≤1 := by
    intro b hb
    exact prepared_memory_sender_boolean tr t r pub localH hr _ (by have :=slot.isLt;omega)
  by_cases tag:tr.cell t r (512+slot)=0
  · simp only [preparedMemorySenderStackValue,if_pos tag]
    have eq:preparedMemoryWord (tr.cell t r) (64*slot)=
        ofBits (fun b=>(tr.cell t r (64*slot+b)).toNat) 32 := by
      unfold preparedMemoryWord
      calc
        _=ofBits (fun b=>if b<32 then (tr.cell t r (64*slot+b)).toNat else 0) 64 := by
          apply ofBits_congr
          intro b hb
          split
          · rfl
          · rw [prepared_memory_sender_i32_high tr t r pub localH hr slot tag b (by omega) hb];rfl
        _=_:=prepared_memory_bits_prefix _ 32 64 (by decide)
    change _%2^32=_
    apply Nat.mod_eq_of_lt
    rw [eq]
    exact ofBits_lt (fun b hb=>bits b (by omega))
  · simp only [preparedMemorySenderStackValue,if_neg tag]
    exact Nat.mod_eq_of_lt (ofBits_lt bits)

/-- The canonical i32 address decoder agrees with the complete stack slot. -/
theorem prepared_memory_sender_stack_address (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH:TableLocal preparedMemorySenderLiteralTable tr t pub) (hr:r<tr.height t)
    (slot:Fin 8) (tag:tr.cell t r (512+slot)=0) :
    preparedMemorySenderStackValue (tr.cell t r) slot=
      .i32 (UInt32.ofNat (preparedMemoryAddressWord (tr.cell t r) (64*slot))) := by
  have bits : ∀b,b<64→(tr.cell t r (64*slot+b)).toNat≤1 := by
    intro b hb;exact prepared_memory_sender_boolean tr t r pub localH hr _ (by have:=slot.isLt;omega)
  have generic (a b c d : Nat) : UInt32.ofNat (a+65536*b+4294967296*c+281474976710656*d)=UInt32.ofNat (a+65536*b) := by
    apply UInt32.toNat_inj.mp
    change (_+_+4294967296*_+281474976710656*_)%4294967296=(_+_)%4294967296
    omega
  have words:=prepared_memory_word_limbs (tr.cell t r) (64*slot) bits
  have eq:=congrArg UInt32.ofNat words
  have result:=eq.trans (generic _ _ _ _)
  change preparedMemorySenderStackValue (tr.cell t r) slot= _
  rw [preparedMemorySenderStackValue,if_pos tag]
  exact congrArg Val.i32 result

theorem prepared_memory_sender_stack_stored (row : Nat→Fp) (sp op : Nat)
    (tag:row (512+(sp-1))=if preparedMemoryIs64 op then 1 else 0) :
    preparedMemorySenderStackValue row (sp-1)=preparedMemorySenderValue row sp op := by
  unfold preparedMemorySenderStackValue preparedMemorySenderValue
  rw [tag]
  split <;> simp_all [show (1:Fp)≠0 by decide]
end NearCompression
