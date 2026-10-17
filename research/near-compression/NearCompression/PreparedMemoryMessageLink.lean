import NearCompression.PreparedMemorySenderTypes
import NearCompression.PreparedMemoryWordBinding
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

def PreparedMemoryMessagesMatch (sender adapter : Nat→Fp) : Prop :=
  preparedMemorySenderLiteralMessage0.map (fun e=>e.evalWith (preparedGasEnv sender []))=
    preparedMemoryLiteralMessage0.map (fun e=>e.evalWith (preparedGasEnv adapter []))

theorem prepared_memory_message_field (sender adapter : Nat→Fp)
    (matched:PreparedMemoryMessagesMatch sender adapter) (i : Fin 23) :
    (preparedMemorySenderLiteralMessage0[i.val]'(by exact i.isLt)).evalWith (preparedGasEnv sender [])=
      (preparedMemoryLiteralMessage0[i.val]'(by exact i.isLt)).evalWith (preparedGasEnv adapter []) := by
  have h:=congrArg (fun xs:List Fp=>xs[i.val]?) matched
  simp only [List.getElem?_map,getElem?_pos preparedMemorySenderLiteralMessage0 i.val i.isLt,
    getElem?_pos preparedMemoryLiteralMessage0 i.val i.isLt,Option.map_some] at h
  exact Option.some.inj h

private def opcodeExpr (base : Nat) : Expr :=
  preparedMemorySum19 (fun i=>.mul (.col (base+i) false) (.const (preparedMemoryOpcode i)))
private theorem opcode_eval (row : Nat→Fp) (base op : Nat) (hop:op<19)
    (hot:∀i,i<19→row (base+i)=if i=op then 1 else 0) :
    (opcodeExpr base).evalWith (preparedGasEnv row [])=Fp.ofNat (preparedMemoryOpcode op) := by
  have sum:(opcodeExpr base).evalWith (preparedGasEnv row [])=
      preparedFieldSum 19 (fun i=>row (base+i)*Fp.ofNat (preparedMemoryOpcode i)) := by
    simp only [opcodeExpr,preparedMemorySum19,preparedGasSumTree,Expr.evalWith,
      preparedFieldSum,Nat.reduceAdd,Nat.reducePow,preparedGasEnv,instructionAddEnv]
    grind
  rw [sum]
  exact prepared_sum_select 19 op _ _ hop hot

/-- Literal opcode identifiers are canonical and injective in this19-opcode
family. Matching field6 therefore identifies the same opcode, not just a tag. -/
theorem prepared_memory_message_opcode (sender adapter : Nat→Fp)
    (matched:PreparedMemoryMessagesMatch sender adapter) (sop aop : Fin 19)
    (shot:∀i,i<19→sender (529+i)=if i=sop.val then 1 else 0)
    (ahot:∀i,i<19→adapter i=if i=aop.val then 1 else 0) : sop=aop := by
  have h:=prepared_memory_message_field sender adapter matched ⟨6,by decide⟩
  change (opcodeExpr 529).evalWith (preparedGasEnv sender [])=(opcodeExpr 0).evalWith (preparedGasEnv adapter []) at h
  rw [opcode_eval sender 529 sop sop.isLt shot,
    opcode_eval adapter 0 aop aop.isLt (by simpa only [Nat.zero_add] using ahot)] at h
  have bounded : ∀i:Fin 19,preparedMemoryOpcode i<ZkFormal.Algebra.P := by decide
  have nat:=congrArg Fp.toNat h
  simp only [Fp.toNat_ofNat,Nat.mod_eq_of_lt (bounded sop),Nat.mod_eq_of_lt (bounded aop)] at nat
  have injective : ∀i j:Fin 19,preparedMemoryOpcode i=preparedMemoryOpcode j→i=j := by decide
  exact injective sop aop nat

private theorem address_shape : ∀i:Fin 2,preparedMemoryLiteralMessage0[9+i.val]?=
    some (preparedGasBits (115+16*i)) := by decide
private theorem value_shape : ∀i:Fin 4,preparedMemoryLiteralMessage0[15+i.val]?=
    some (preparedGasBits (229+16*i)) := by decide

/-- Matching the exact two address limbs recovers the selected natural i32
address. Store depth is the source-proved guard, not a defaulted stack lookup. -/
theorem prepared_memory_message_address (sender adapter : Nat→Fp)
    (matched:PreparedMemoryMessagesMatch sender adapter) (op sp : Nat)
    (hop:op<19) (hot:∀i,i<19→sender (529+i)=if i=op then 1 else 0)
    (positive:0<sp) (bound:sp<9) (storeDepth:12≤op→2≤sp)
    (spHot:∀i,i<9→sender (520+i)=if i=sp then 1 else 0) :
    preparedMemoryAddressWord adapter 115=
      preparedMemoryAddressWord sender (64*(sp-(if 12≤op then 2 else 1))) := by
  have limb (i:Fin 2) : preparedMemoryAddressLimb adapter (115+16*i)=
      preparedMemoryAddressLimb sender (64*(sp-(if 12≤op then 2 else 1))+16*i) := by
    have h:=prepared_memory_message_field sender adapter matched ⟨9+i.val,by omega⟩
    have chosen:=prepared_memory_sender_address_message sender op sp hop hot positive bound storeDepth spHot i
    have eq:=List.getElem?_eq_some_iff.mp (address_shape i)
    have decoded:=congrArg (fun e=>e.evalWith (preparedGasEnv adapter [])) eq.2
    exact decoded.symm.trans (h.symm.trans chosen)
  have lo:=limb ⟨0,by decide⟩;have hi:=limb ⟨1,by decide⟩
  simp only [Nat.mul_zero,Nat.add_zero,Nat.reduceMul,Nat.reduceAdd] at lo hi
  unfold preparedMemoryAddressWord
  rw [lo,hi]

/-- Four matched value limbs recover the full natural64-bit selected store
operand. Both tables enforce bit ranges, preventing field reduction aliases. -/
theorem prepared_memory_message_store_value
    (str atr : Trace Fp) (st sr atable ar : Nat) (spub apub : List Fp)
    (sH:TableLocal preparedMemorySenderLiteralTable str st spub) (shr:sr<str.height st)
    (aH:TableLocal preparedMemoryLiteralTable atr atable apub) (ahr:ar<atr.height atable)
    (matched:PreparedMemoryMessagesMatch (str.cell st sr) (atr.cell atable ar))
    (op sp : Nat) (hop:op<19) (store:12≤op)
    (hot:∀i,i<19→str.cell st sr (529+i)=if i=op then 1 else 0)
    (positive:0<sp) (bound:sp<9) (spHot:∀i,i<9→str.cell st sr (520+i)=if i=sp then 1 else 0) :
    preparedMemoryWord (atr.cell atable ar) 229=preparedMemoryWord (str.cell st sr) (64*(sp-1)) := by
  apply prepared_memory_word_of_limb_eq
  · have h:=prepared_memory_literal_bounds atr atable ar apub aH ahr
    intro i hi;exact prepared_memory_address_boolean _ h.1 _ (by omega)
  · intro i hi
    have slot:sp-1<8:=by omega
    exact prepared_memory_sender_boolean str st sr spub sH shr _ (by omega)
  · intro i
    have h:=prepared_memory_message_field _ _ matched ⟨15+i.val,by omega⟩
    have chosen:=prepared_memory_sender_value_message (str.cell st sr) op sp hop hot positive bound spHot i
    rw [if_pos store] at chosen
    have eq:=List.getElem?_eq_some_iff.mp (value_shape i)
    have decoded:=congrArg (fun e=>e.evalWith (preparedGasEnv (atr.cell atable ar) [])) eq.2
    exact decoded.symm.trans (h.symm.trans chosen)
end NearCompression
