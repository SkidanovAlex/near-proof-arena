import NearCompression.PreparedTypedLocalPreserve
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpecV3.Wasm
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
private def localWrite (slot : Nat) : Expr := .mul preparedExecGasSuccess (.mul (.add (.col 684 false) (.col 685 false)) (.col (814+slot) false))
def preparedTypedQuietLocalStep (slot limb : Nat) : Expr :=
  .mul .isTransition (.add (preparedCodeBits (preparedTypedLocalBase slot limb) true)
    (.neg (.add (.mul (.add (.const 1) (.neg (localWrite slot))) (preparedCodeBits (preparedTypedLocalBase slot limb)))
      (.mul (localWrite slot) (preparedTypedSelectedLimb limb)))))
private theorem local_at : ∀count:Fin 5,∀slot:Fin 4,∀limb:Fin 4,
    (preparedTypedLiteralExec count)[1565+66*(4-count.val)+4*slot.val+limb.val]?=some (preparedTypedQuietLocalStep slot limb) := by decide

theorem prepared_typed_quiet_local_limb (count : Nat) (hc : count≤4)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedTypedLiteralExecTable count) tr t pub) (nonlast : r+1<tr.height t)
    (quiet : preparedExecGasSuccess.eval tr t r pub=0)
    (slot limb : Nat) (hs : slot<4) (hl : limb<4) :
    preparedTypedLocalLimb (tr.cell t (r+1)) slot limb=preparedTypedLocalLimb (tr.cell t r) slot limb := by
  have h:=localH.constr r (by omega) _ (List.mem_of_getElem? (local_at ⟨count,by omega⟩ ⟨slot,hs⟩ ⟨limb,hl⟩))
  have write : (localWrite slot).eval tr t r pub=0 := by
    change preparedExecGasSuccess.eval tr t r pub*((tr.cell t r 684+tr.cell t r 685)*tr.cell t r (814+slot))=0
    rw [quiet];grind
  change (if r+1=tr.height t then (0:Fp) else 1)*
    ((preparedCodeBits (preparedTypedLocalBase slot limb) true).eval tr t r pub+
      -(((1:Fp)+ -(localWrite slot).eval tr t r pub)*(preparedCodeBits (preparedTypedLocalBase slot limb)).eval tr t r pub+
      (localWrite slot).eval tr t r pub*(preparedTypedSelectedLimb limb).eval tr t r pub))=0 at h
  rw [if_neg (by omega),write,prepared_code_bits_eval,prepared_code_bits_eval] at h
  simp only [ite_true,Bool.false_eq_true,ite_false,Nat.mod_eq_of_lt nonlast] at h
  unfold preparedTypedLocalLimb
  grind

theorem prepared_typed_quiet_local_value (count : Nat) (hc : count≤4)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedTypedLiteralExecTable count) tr t pub) (nonlast : r+1<tr.height t)
    (quiet : preparedExecGasSuccess.eval tr t r pub=0)
    (slot : Nat) (hs : slot<4) :
    preparedTypedLocalValue (tr.cell t (r+1)) slot=preparedTypedLocalValue (tr.cell t r) slot := by
  have tag:tr.cell t (r+1) (1210+slot)=tr.cell t r (1210+slot):=
    (prepared_typed_source_local_type count hc tr t (r+1) pub localH nonlast slot hs).trans
      (prepared_typed_source_local_type count hc tr t r pub localH (by omega) slot hs).symm
  have word : preparedTypedLocalWord (tr.cell t (r+1)) slot=preparedTypedLocalWord (tr.cell t r) slot := by
    unfold preparedTypedLocalWord instructionAdd64Word
    rw [prepared_typed_quiet_local_limb count hc tr t r pub localH nonlast quiet slot 0 hs (by decide),
      prepared_typed_quiet_local_limb count hc tr t r pub localH nonlast quiet slot 1 hs (by decide),
      prepared_typed_quiet_local_limb count hc tr t r pub localH nonlast quiet slot 2 hs (by decide),
      prepared_typed_quiet_local_limb count hc tr t r pub localH nonlast quiet slot 3 hs (by decide)]
  simp only [preparedTypedLocalValue,tag,word]

theorem prepared_typed_quiet_local_array (count : Nat) (hc : count≤4)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedTypedLiteralExecTable count) tr t pub) (nonlast : r+1<tr.height t)
    (quiet : preparedExecGasSuccess.eval tr t r pub=0) :
    preparedTypedLocalArray (tr.cell t (r+1)) count=preparedTypedLocalArray (tr.cell t r) count := by
  unfold preparedTypedLocalArray
  congr 1
  apply List.map_congr_left
  intro slot member
  exact prepared_typed_quiet_local_value count hc tr t r pub localH nonlast quiet slot (by have h:=List.mem_range.mp member;omega)
end NearCompression
