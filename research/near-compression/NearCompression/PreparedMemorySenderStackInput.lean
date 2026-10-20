import NearCompression.PreparedMemorySenderStack
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpecV3.Wasm
set_option maxHeartbeats 1000000

/-- The complete decoded load input stack, not an arbitrary lower state. -/
theorem prepared_memory_sender_load_input (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH:TableLocal preparedMemorySenderLiteralTable tr t pub) (hr:r<tr.height t)
    (op sp : Nat) (hop:op<19) (load:op<12) (positive:0<sp) (hp:sp<9)
    (hot:∀i,i<19→tr.cell t r (529+i)=if i=op then 1 else 0)
    (spHot:∀i,i<9→tr.cell t r (520+i)=if i=sp then 1 else 0) :
    preparedMemorySenderStack (tr.cell t r) sp=
      (preparedMemorySenderStack (tr.cell t r) (sp-1)).push
        (.i32 (UInt32.ofNat (preparedMemoryAddressWord (tr.cell t r) (64*(sp-1))))) := by
  have tag:=prepared_memory_sender_address_type tr t r pub localH hr op sp hop hot positive hp spHot
  rw [if_neg (show ¬12≤op by omega)] at tag
  have value:=prepared_memory_sender_stack_address tr t r pub localH hr ⟨sp-1,by omega⟩ tag
  have eq:=prepared_memory_sender_stack_push (tr.cell t r) (sp-1)
  rw [show sp-1+1=sp by omega,value] at eq
  exact eq

/-- Both consumed store values and every mixed prefix slot are tied to the
same complete decoded sender stack. -/
theorem prepared_memory_sender_store_input (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH:TableLocal preparedMemorySenderLiteralTable tr t pub) (hr:r<tr.height t)
    (op sp : Nat) (hop:op<19) (store:12≤op) (positive:0<sp) (hp:sp<9)
    (hot:∀i,i<19→tr.cell t r (529+i)=if i=op then 1 else 0)
    (spHot:∀i,i<9→tr.cell t r (520+i)=if i=sp then 1 else 0) :
    preparedMemorySenderStack (tr.cell t r) sp=
      ((preparedMemorySenderStack (tr.cell t r) (sp-2)).push
        (.i32 (UInt32.ofNat (preparedMemoryAddressWord (tr.cell t r) (64*(sp-2)))))).push
        (preparedMemorySenderValue (tr.cell t r) sp op) := by
  have depth:=prepared_memory_sender_store_depth tr t r pub localH hr op sp hop store hot positive hp spHot
  have tag:=prepared_memory_sender_address_type tr t r pub localH hr op sp hop hot positive hp spHot
  rw [if_pos store] at tag
  have value:=prepared_memory_sender_stack_address tr t r pub localH hr ⟨sp-2,by omega⟩ tag
  have kind:=prepared_memory_sender_store_type tr t r pub localH hr op sp hop store hot positive hp spHot
  have top:=prepared_memory_sender_stack_stored (tr.cell t r) sp op kind
  have eq1:=prepared_memory_sender_stack_push (tr.cell t r) (sp-1)
  have eq2:=prepared_memory_sender_stack_push (tr.cell t r) (sp-2)
  rw [show sp-1+1=sp by omega,top] at eq1
  rw [show sp-2+1=sp-1 by omega,value] at eq2
  rw [eq1,eq2]
end NearCompression
