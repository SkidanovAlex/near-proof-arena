import NearCompression.PreparedTypedEqzSource
import NearCompression.PreparedTypedOpcode
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpecV3.Wasm
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
def preparedTypedLocalBase (slot limb : Nat) : Nat :=
  (if limb<2 then 686 else 1082)+32*slot+16*(limb%2)
def preparedTypedLocalLimb (row : Nat→Fp) (slot limb : Nat) : Fp := preparedCodeLimb row (preparedTypedLocalBase slot limb)
def preparedTypedLocalWord (row : Nat→Fp) (slot : Nat) : Nat := instructionAdd64Word (preparedTypedLocalLimb row slot) 0
def preparedTypedLocalValue (row : Nat→Fp) (slot : Nat) : Val :=
  if row (1210+slot)=0 then .i32 (UInt32.ofNat (preparedTypedLocalWord row slot)) else .i64 (UInt64.ofNat (preparedTypedLocalWord row slot))
def preparedTypedLocalArray (row : Nat→Fp) (count : Nat) : Array Val := ((List.range count).map (preparedTypedLocalValue row)).toArray
private def localWrite (slot : Nat) : Expr := .mul preparedExecGasSuccess (.mul (.add (.col 684 false) (.col 685 false)) (.col (814+slot) false))
def preparedTypedLocalStep (slot limb : Nat) : Expr :=
  .mul .isTransition (.add (preparedCodeBits (preparedTypedLocalBase slot limb) true)
    (.neg (.add (.mul (.add (.const 1) (.neg (localWrite slot))) (preparedCodeBits (preparedTypedLocalBase slot limb)))
      (.mul (localWrite slot) (preparedTypedSelectedLimb limb)))))
private theorem local_at : ∀count:Fin 5,∀slot:Fin 4,∀limb:Fin 4,
    (preparedTypedLiteralExec count)[1565+66*(4-count.val)+4*slot.val+limb.val]?=some (preparedTypedLocalStep slot limb) := by decide

theorem prepared_typed_local_preserve (count : Nat) (hc : count≤4)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedTypedLiteralExecTable count) tr t pub) (nonlast : r+1<tr.height t)
    (notSet : tr.cell t r 684=0) (notTee : tr.cell t r 685=0)
    (slot limb : Nat) (hs : slot<4) (hl : limb<4) :
    preparedTypedLocalLimb (tr.cell t (r+1)) slot limb=preparedTypedLocalLimb (tr.cell t r) slot limb := by
  have h:=localH.constr r (by omega) _ (List.mem_of_getElem? (local_at ⟨count,by omega⟩ ⟨slot,hs⟩ ⟨limb,hl⟩))
  have write : (localWrite slot).eval tr t r pub=0 := by
    change preparedExecGasSuccess.eval tr t r pub*((tr.cell t r 684+tr.cell t r 685)*tr.cell t r (814+slot))=0
    rw [notSet,notTee];grind
  change (if r+1=tr.height t then (0:Fp) else 1)*
    ((preparedCodeBits (preparedTypedLocalBase slot limb) true).eval tr t r pub+
      -(((1:Fp)+ -(localWrite slot).eval tr t r pub)*(preparedCodeBits (preparedTypedLocalBase slot limb)).eval tr t r pub+
      (localWrite slot).eval tr t r pub*(preparedTypedSelectedLimb limb).eval tr t r pub))=0 at h
  rw [if_neg (by omega),write,prepared_code_bits_eval,prepared_code_bits_eval] at h
  simp only [ite_true,Bool.false_eq_true,ite_false,Nat.mod_eq_of_lt nonlast] at h
  unfold preparedTypedLocalLimb
  grind

theorem prepared_typed_local_value_preserve (count : Nat) (hc : count≤4)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedTypedLiteralExecTable count) tr t pub) (nonlast : r+1<tr.height t)
    (notSet : tr.cell t r 684=0) (notTee : tr.cell t r 685=0)
    (slot : Nat) (hs : slot<4) :
    preparedTypedLocalValue (tr.cell t (r+1)) slot=preparedTypedLocalValue (tr.cell t r) slot := by
  have tag:tr.cell t (r+1) (1210+slot)=tr.cell t r (1210+slot):=
    (prepared_typed_source_local_type count hc tr t (r+1) pub localH nonlast slot hs).trans
      (prepared_typed_source_local_type count hc tr t r pub localH (by omega) slot hs).symm
  have word : preparedTypedLocalWord (tr.cell t (r+1)) slot=preparedTypedLocalWord (tr.cell t r) slot := by
    unfold preparedTypedLocalWord instructionAdd64Word
    rw [prepared_typed_local_preserve count hc tr t r pub localH nonlast notSet notTee slot 0 hs (by decide),
      prepared_typed_local_preserve count hc tr t r pub localH nonlast notSet notTee slot 1 hs (by decide),
      prepared_typed_local_preserve count hc tr t r pub localH nonlast notSet notTee slot 2 hs (by decide),
      prepared_typed_local_preserve count hc tr t r pub localH nonlast notSet notTee slot 3 hs (by decide)]
  simp only [preparedTypedLocalValue,tag,word]

theorem prepared_typed_local_array_preserve (count : Nat) (hc : count≤4)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedTypedLiteralExecTable count) tr t pub) (nonlast : r+1<tr.height t)
    (notSet : tr.cell t r 684=0) (notTee : tr.cell t r 685=0) :
    preparedTypedLocalArray (tr.cell t (r+1)) count=preparedTypedLocalArray (tr.cell t r) count := by
  unfold preparedTypedLocalArray
  congr 1
  apply List.map_congr_left
  intro slot member
  exact prepared_typed_local_value_preserve count hc tr t r pub localH nonlast notSet notTee slot (by have h:=List.mem_range.mp member;omega)
end NearCompression
