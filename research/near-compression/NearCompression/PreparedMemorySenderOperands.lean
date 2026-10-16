import NearCompression.PreparedMemorySenderSource
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

def preparedMemorySenderSelector (weights : Nat→Nat) : Expr :=
  preparedMemorySum19 (fun i=>.mul (.col (529+i) false) (.const (weights i)))
def preparedMemorySenderWrite : Expr := preparedMemorySenderSelector (fun i=>if 12≤i then 1 else 0)
private theorem weighted_eval (row : Nat→Fp) (weights : Nat→Nat) :
    (preparedMemorySenderSelector weights).evalWith (preparedGasEnv row [])=
      preparedFieldSum 19 (fun i=>row (529+i)*Fp.ofNat (weights i)) := by
  simp only [preparedMemorySenderSelector,preparedMemorySum19,preparedGasSumTree,Expr.evalWith,
    preparedFieldSum,Nat.reduceAdd,Nat.reducePow,preparedGasEnv,instructionAddEnv]
  grind
private theorem value_shape : ∀i:Fin 4,preparedMemorySenderLiteralMessage0[15+i.val]?=
    some (.mul preparedMemorySenderWrite (preparedMemorySenderTop i)) := by decide
private theorem address_shape : ∀i:Fin 2,preparedMemorySenderLiteralMessage0[9+i.val]?=
    some (.add (.mul (.add (.const 1) (.neg preparedMemorySenderWrite)) (preparedMemorySenderTop i))
      (.mul preparedMemorySenderWrite (preparedMemorySenderSecond i))) := by decide

theorem prepared_memory_sender_opcode (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH:TableLocal preparedMemorySenderLiteralTable tr t pub) (hr:r<tr.height t) :
    ∃op,op<19 ∧ ∀i,i<19→tr.cell t r (529+i)=if i=op then 1 else 0 := by
  have memberAt:preparedMemorySenderLiteralConstraints[796]?=some preparedMemorySenderLiteral0796:=by decide
  have h:=localH.constr r hr _ (List.mem_of_getElem? memberAt)
  have sum:preparedFieldSum 19 (fun i=>tr.cell t r (529+i))=1 := by
    change (((((tr.cell t r 529+tr.cell t r 530)+(tr.cell t r 531+tr.cell t r 532))+
      ((tr.cell t r 533+tr.cell t r 534)+(tr.cell t r 535+tr.cell t r 536)))+
      (((tr.cell t r 537+tr.cell t r 538)+(tr.cell t r 539+tr.cell t r 540))+
      ((tr.cell t r 541+tr.cell t r 542)+(tr.cell t r 543+tr.cell t r 544))))+
      ((tr.cell t r 545+tr.cell t r 546)+tr.cell t r 547))+ -(1:Fp)=0 at h
    simp only [preparedFieldSum,Nat.reduceAdd]
    grind
  exact prepared_onehot 19 529 (tr.cell t r) (by decide)
    (fun i hi=>prepared_memory_sender_boolean tr t r pub localH hr (529+i) (by omega)) sum

theorem prepared_memory_sender_write_selected (row : Nat→Fp) (op : Nat) (hop:op<19)
    (hot:∀i,i<19→row (529+i)=if i=op then 1 else 0) :
    preparedMemorySenderWrite.evalWith (preparedGasEnv row [])=if 12≤op then 1 else 0 := by
  unfold preparedMemorySenderWrite
  rw [weighted_eval,prepared_sum_select 19 op _ _ hop hot]
  split <;> rfl

/-- Actual store depth guard prevents selecting a default/missing address. -/
theorem prepared_memory_sender_store_depth (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH:TableLocal preparedMemorySenderLiteralTable tr t pub) (hr:r<tr.height t)
    (op sp : Nat) (hop:op<19) (store:12≤op)
    (hot:∀i,i<19→tr.cell t r (529+i)=if i=op then 1 else 0)
    (positive:0<sp) (bound:sp<9) (spHot:∀i,i<9→tr.cell t r (520+i)=if i=sp then 1 else 0) : 2≤sp := by
  have memberAt:preparedMemorySenderLiteralConstraints[798]?=some preparedMemorySenderLiteral0798:=by decide
  have h:=localH.constr r hr _ (List.mem_of_getElem? memberAt)
  change preparedMemorySenderWrite.evalWith (preparedGasEnv (tr.cell t r) [])*tr.cell t r 521+ -(0:Fp)=0 at h
  rw [prepared_memory_sender_write_selected _ op hop hot,if_pos store] at h
  have first:=spHot 1 (by decide)
  change tr.cell t r 521=(if 1=sp then 1 else 0) at first
  by_cases one:sp=1
  · rw [one,if_pos rfl] at first
    rw [first] at h
    have bad : (1:Fp)*1+ -0≠0:=by decide
    exact False.elim (bad h)
  · omega

/-- All four exact EXEC payload value limbs are bound to the actual selected
store-value stack slot; loads emit zero in these fields. -/
theorem prepared_memory_sender_value_message (row : Nat→Fp) (op sp : Nat)
    (hop:op<19) (hot:∀i,i<19→row (529+i)=if i=op then 1 else 0)
    (positive:0<sp) (bound:sp<9) (spHot:∀i,i<9→row (520+i)=if i=sp then 1 else 0)
    (limb : Fin 4) :
    (preparedMemorySenderLiteralMessage0[15+limb.val]'(by change 15+limb.val<23;omega)).evalWith (preparedGasEnv row [])=
      if 12≤op then (preparedGasBits (64*(sp-1)+16*limb)).evalWith (preparedGasEnv row []) else 0 := by
  have shape:=value_shape limb
  have eq:=List.getElem?_eq_some_iff.mp shape
  rw [eq.2]
  change preparedMemorySenderWrite.evalWith (preparedGasEnv row [])*
    (preparedMemorySenderTop limb).evalWith (preparedGasEnv row [])=_
  rw [prepared_memory_sender_write_selected row op hop hot,
    prepared_memory_sender_top_selected row sp limb positive bound spHot]
  split <;> grind

/-- Both exact EXEC address limbs select top for loads and second for stores. -/
theorem prepared_memory_sender_address_message (row : Nat→Fp) (op sp : Nat)
    (hop:op<19) (hot:∀i,i<19→row (529+i)=if i=op then 1 else 0)
    (positive:0<sp) (bound:sp<9) (storeDepth:12≤op→2≤sp)
    (spHot:∀i,i<9→row (520+i)=if i=sp then 1 else 0) (limb : Fin 2) :
    (preparedMemorySenderLiteralMessage0[9+limb.val]'(by change 9+limb.val<23;omega)).evalWith (preparedGasEnv row [])=
      (preparedGasBits (64*(sp-(if 12≤op then 2 else 1))+16*limb)).evalWith (preparedGasEnv row []) := by
  have shape:=address_shape limb
  have eq:=List.getElem?_eq_some_iff.mp shape
  rw [eq.2]
  change ((1:Fp)+ -preparedMemorySenderWrite.evalWith (preparedGasEnv row []))*
    (preparedMemorySenderTop limb).evalWith (preparedGasEnv row [])+
    preparedMemorySenderWrite.evalWith (preparedGasEnv row [])*
    (preparedMemorySenderSecond limb).evalWith (preparedGasEnv row [])=_
  rw [prepared_memory_sender_write_selected row op hop hot]
  by_cases store:12≤op
  · rw [if_pos store,prepared_memory_sender_second_selected row sp limb (storeDepth store) bound spHot]
    grind
  · rw [if_neg store,prepared_memory_sender_top_selected row sp limb positive bound spHot]
    grind

/-- Concrete EXEC sender attachment: the opcode and stack indices are derived
from literal AIR, and every address/value message limb is the corresponding
current-stack limb. No operand lookup or chosen-SP premise is supplied. -/
theorem prepared_memory_sender_operands (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH:TableLocal preparedMemorySenderLiteralTable tr t pub) (hr:r<tr.height t) :
    ∃op sp,op<19 ∧ 0<sp ∧ sp<9 ∧
      (∀i,i<19→tr.cell t r (529+i)=if i=op then 1 else 0) ∧
      (∀i,i<9→tr.cell t r (520+i)=if i=sp then 1 else 0) ∧
      (12≤op→2≤sp) ∧
      (∀limb:Fin 2,(preparedMemorySenderLiteralMessage0[9+limb.val]'(by change 9+limb.val<23;omega)).evalWith
        (preparedGasEnv (tr.cell t r) [])=
        (preparedGasBits (64*(sp-(if 12≤op then 2 else 1))+16*limb)).evalWith (preparedGasEnv (tr.cell t r) [])) ∧
      (∀limb:Fin 4,(preparedMemorySenderLiteralMessage0[15+limb.val]'(by change 15+limb.val<23;omega)).evalWith
        (preparedGasEnv (tr.cell t r) [])=
        if 12≤op then (preparedGasBits (64*(sp-1)+16*limb)).evalWith (preparedGasEnv (tr.cell t r) []) else 0) := by
  obtain ⟨sp,positive,bound,spHot⟩:=prepared_memory_sender_sp tr t r pub localH hr
  obtain ⟨op,hop,hot⟩:=prepared_memory_sender_opcode tr t r pub localH hr
  have depth:=fun store=>prepared_memory_sender_store_depth tr t r pub localH hr op sp hop store hot positive bound spHot
  exact ⟨op,sp,hop,positive,bound,hot,spHot,depth,
    fun limb=>prepared_memory_sender_address_message _ op sp hop hot positive bound depth spHot limb,
    fun limb=>prepared_memory_sender_value_message _ op sp hop hot positive bound spHot limb⟩
end NearCompression
