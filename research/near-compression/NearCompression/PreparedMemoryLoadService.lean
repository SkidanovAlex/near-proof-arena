import NearCompression.PreparedMemorySigned
import NearCompression.PreparedMemoryService
namespace NearCompression
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
open NearSpec NearSpecV3 NearSpecV3.Wasm ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

def preparedMemoryEffectiveAddress (row : Nat→Fp) : Nat :=
  preparedMemoryAddressWord row 179+4294967296*(row 211).toNat

/-- Exact read service request decoded from the scalar-memory source row.
Clock/instance association with an EXEC sender still needs the bus attachment. -/
def preparedMemoryLoadRequest (row : Nat→Fp) (selected : Nat)
    (openings : List PreparedMemoryReadOpening) : PreparedMemoryRequest :=
  ⟨preparedMemoryWord row 51,preparedMemoryEffectiveAddress row,preparedMemoryWidth selected,
    .read (preparedMemoryWord row 293) openings⟩

theorem prepared_memory_address_uint32 (row : Nat→Fp) (holds : PreparedMemoryAddressHolds row)
    (base : Nat) (hb:base+32≤460) :
    (UInt32.ofNat (preparedMemoryAddressWord row base)).toNat=preparedMemoryAddressWord row base := by
  have lo:=prepared_memory_address_limb_bound row holds base (by omega)
  have hi:=prepared_memory_address_limb_bound row holds (base+16) (by omega)
  have small:preparedMemoryAddressWord row base<4294967296:=by unfold preparedMemoryAddressWord;omega
  exact Nat.mod_eq_of_lt small

/-- Exact actual load execution and post-stack result from literal AIR and
service acceptance. The input stack is explicitly the decoded i32 operand
above arbitrary state s; CODE/stack/gas provenance is not supplied by this table. -/
theorem prepared_memory_load_service_exec
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal preparedMemoryLiteralTable tr t pub) (hr:r<tr.height t)
    (selected : Fin 19) (hot:∀i,i<19→tr.cell t r i=if i=selected.val then 1 else 0)
    (load:selected.val<12) (hash : Bytes→ByteArray) (digestBound:∀bs,bytesWireWf (hash bs))
    (cfg : NearCfg) (p : Prepared) (s : St) (full:fullPages s.pages)
    (block count depth : Nat) (wf:blockDescriptorWf (describeSubpageMemory hash s block count depth))
    (f : Frame) (pf : PFunc) (align : Nat) (openings : List PreparedMemoryReadOpening)
    (output : BlockDescriptor)
    (accepted : preparedMemoryServiceCheck hash (describeSubpageMemory hash s block count depth)
      (preparedMemoryWord (tr.cell t r) 51) [preparedMemoryLoadRequest (tr.cell t r) selected openings]=some output) :
    (exec cfg p (pushV s (.i32 (UInt32.ofNat (preparedMemoryAddressWord (tr.cell t r) 115)))) f pf
        (.load (preparedMemoryOpcode selected) align (preparedMemoryAddressWord (tr.cell t r) 147))=
      .cont (setFrame (pushV s (preparedMemoryResultValue (tr.cell t r) selected)) {f with pc:=f.pc+1}) ∧
      output=describeSubpageMemory hash s block count depth) ∨
    PreparedMemoryReadCollision hash s block count depth (preparedMemoryWidth selected) openings := by
  simp only [preparedMemoryServiceCheck,preparedMemoryLoadRequest,ite_true] at accepted
  have parse (b : Bool) (d : BlockDescriptor)
      (h:(if b then some d else none)=some output) : b=true ∧ output=d := by
    cases b <;> simp_all
  obtain ⟨checks,out⟩:=parse _ _ accepted
  simp only [Bool.and_eq_true,decide_eq_true_eq] at checks
  obtain ⟨_,_,bounds,result⟩:=prepared_memory_read_checked hash digestBound s full block count depth
    (preparedMemoryEffectiveAddress (tr.cell t r)) (preparedMemoryWidth selected) wf openings checks.1
  rcases result with correct|collision
  · apply Or.inl
    refine ⟨?_,out⟩
    have h:=prepared_memory_literal_bounds tr t r pub localH hr
    have ea:=prepared_memory_address_exact (tr.cell t r) h.1
    have addr:=prepared_memory_address_uint32 (tr.cell t r) h.1 115 (by decide)
    have spec:=prepared_memory_load_spec selected load
    have readEq : readLE s (preparedMemoryEffectiveAddress (tr.cell t r)) (preparedMemoryWidth selected)=
        preparedMemoryWord (tr.cell t r) 293 := correct.trans (of_decide_eq_true checks.2).symm
    rw [prepared_memory_load_exec,addr,spec]
    change preparedMemoryEffectiveAddress (tr.cell t r)=_ at ea
    rw [←ea]
    rw [ite_eq_right (by omega),←prepared_scalar_read_exact,readEq,
      ←prepared_memory_load_value tr t r pub localH hr selected hot load]
  · exact Or.inr collision
end NearCompression
