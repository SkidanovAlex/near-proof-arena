import NearCompression.PreparedMemoryMatchedOperands
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
set_option maxRecDepth 8192

private theorem offset_shapes : ∀i:Fin 2,
    preparedMemorySenderLiteralMessage0[11+i.val]?=some (preparedGasBits (548+16*i)) ∧
    preparedMemoryLiteralMessage0[11+i.val]?=some (preparedGasBits (147+16*i)) := by decide

theorem prepared_memory_message_offset (sender adapter : Nat→Fp)
    (matched:PreparedMemoryMessagesMatch sender adapter) :
    preparedMemoryAddressWord adapter 147=preparedMemoryAddressWord sender 548 := by
  have limb (i:Fin 2) : preparedMemoryAddressLimb adapter (147+16*i)=preparedMemoryAddressLimb sender (548+16*i) := by
    have h:=prepared_memory_message_field sender adapter matched ⟨11+i.val,by omega⟩
    have s:=congrArg (fun e=>e.evalWith (preparedGasEnv sender []))
      (List.getElem?_eq_some_iff.mp (offset_shapes i).1).2
    have a:=congrArg (fun e=>e.evalWith (preparedGasEnv adapter []))
      (List.getElem?_eq_some_iff.mp (offset_shapes i).2).2
    exact a.symm.trans (h.symm.trans s)
  have lo:=limb ⟨0,by decide⟩;have hi:=limb ⟨1,by decide⟩
  simp only [Nat.mul_zero,Nat.add_zero,Nat.reduceMul,Nat.reduceAdd] at lo hi
  unfold preparedMemoryAddressWord
  rw [lo,hi]

private theorem result_shapes : ∀i:Fin 4,
    preparedMemorySenderLiteralMessage0[19+i.val]?=some (preparedGasBits (693+16*i)) ∧
    preparedMemoryLiteralMessage0[19+i.val]?=some (preparedGasBits (357+16*i)) := by decide
private theorem clock_shapes : ∀i:Fin 4,
    preparedMemorySenderLiteralMessage0[2+i.val]?=some (preparedGasBits (580+16*i)) ∧
    preparedMemoryLiteralMessage0[2+i.val]?=some (preparedGasBits (51+16*i)) := by decide

/-- Result limbs are bound to the sender's actual result columns, which its
stack-transition constraints use as the pushed value. -/
theorem prepared_memory_message_result
    (str atr : Trace Fp) (st sr atable ar : Nat) (spub apub : List Fp)
    (sH:TableLocal preparedMemorySenderLiteralTable str st spub) (shr:sr<str.height st)
    (aH:TableLocal preparedMemoryLiteralTable atr atable apub) (ahr:ar<atr.height atable)
    (matched:PreparedMemoryMessagesMatch (str.cell st sr) (atr.cell atable ar)) :
    preparedMemoryWord (atr.cell atable ar) 357=preparedMemoryWord (str.cell st sr) 693 := by
  apply prepared_memory_word_of_limb_eq
  · have h:=prepared_memory_literal_bounds atr atable ar apub aH ahr
    intro i hi;exact prepared_memory_address_boolean _ h.1 _ (by omega)
  · intro i hi;exact prepared_memory_sender_boolean str st sr spub sH shr _ (by omega)
  · intro i
    have h:=prepared_memory_message_field _ _ matched ⟨19+i.val,by omega⟩
    have s:=congrArg (fun e=>e.evalWith (preparedGasEnv (str.cell st sr) []))
      (List.getElem?_eq_some_iff.mp (result_shapes i).1).2
    have a:=congrArg (fun e=>e.evalWith (preparedGasEnv (atr.cell atable ar) []))
      (List.getElem?_eq_some_iff.mp (result_shapes i).2).2
    exact a.symm.trans (h.symm.trans s)

theorem prepared_memory_message_clock
    (str atr : Trace Fp) (st sr atable ar : Nat) (spub apub : List Fp)
    (sH:TableLocal preparedMemorySenderLiteralTable str st spub) (shr:sr<str.height st)
    (aH:TableLocal preparedMemoryLiteralTable atr atable apub) (ahr:ar<atr.height atable)
    (matched:PreparedMemoryMessagesMatch (str.cell st sr) (atr.cell atable ar)) :
    preparedMemoryWord (atr.cell atable ar) 51=preparedMemoryWord (str.cell st sr) 580 := by
  apply prepared_memory_word_of_limb_eq
  · have h:=prepared_memory_literal_bounds atr atable ar apub aH ahr
    intro i hi;exact prepared_memory_address_boolean _ h.1 _ (by omega)
  · intro i hi;exact prepared_memory_sender_boolean str st sr spub sH shr _ (by omega)
  · intro i
    have h:=prepared_memory_message_field _ _ matched ⟨2+i.val,by omega⟩
    have s:=congrArg (fun e=>e.evalWith (preparedGasEnv (str.cell st sr) []))
      (List.getElem?_eq_some_iff.mp (clock_shapes i).1).2
    have a:=congrArg (fun e=>e.evalWith (preparedGasEnv (atr.cell atable ar) []))
      (List.getElem?_eq_some_iff.mp (clock_shapes i).2).2
    exact a.symm.trans (h.symm.trans s)
end NearCompression
