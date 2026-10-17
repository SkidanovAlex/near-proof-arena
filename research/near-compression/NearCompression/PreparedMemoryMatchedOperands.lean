import NearCompression.PreparedMemoryMessageLink
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

/-- Local linkage of two concrete AIR rows. Message equality is explicit;
this theorem does not infer a particular pairing from global bus balance. -/
theorem prepared_memory_matched_operands
    (str atr : Trace Fp) (st sr atable ar : Nat) (spub apub : List Fp)
    (sH:TableLocal preparedMemorySenderLiteralTable str st spub) (shr:sr<str.height st)
    (aH:TableLocal preparedMemoryLiteralTable atr atable apub) (ahr:ar<atr.height atable)
    (matched:PreparedMemoryMessagesMatch (str.cell st sr) (atr.cell atable ar)) :
    ∃op:Fin 19,∃sp,0<sp ∧ sp<9 ∧
      (∀i,i<19→str.cell st sr (529+i)=if i=op.val then 1 else 0) ∧
      (∀i,i<19→atr.cell atable ar i=if i=op.val then 1 else 0) ∧
      (∀i,i<9→str.cell st sr (520+i)=if i=sp then 1 else 0) ∧
      (12≤op.val→2≤sp) ∧
      preparedMemoryAddressWord (atr.cell atable ar) 115=
        preparedMemoryAddressWord (str.cell st sr) (64*(sp-(if 12≤op.val then 2 else 1))) ∧
      str.cell st sr (512+(sp-(if 12≤op.val then 2 else 1)))=0 ∧
      (12≤op.val→preparedMemoryWord (atr.cell atable ar) 229=
          preparedMemoryWord (str.cell st sr) (64*(sp-1))) ∧
      (12≤op.val→str.cell st sr (512+(sp-1))=if preparedMemoryIs64 op then 1 else 0) := by
  obtain ⟨sp,positive,bound,spHot⟩:=prepared_memory_sender_sp str st sr spub sH shr
  obtain ⟨sop,hsop,shot⟩:=prepared_memory_sender_opcode str st sr spub sH shr
  have ah:=prepared_memory_literal_bounds atr atable ar apub aH ahr
  obtain ⟨aop,haop,ahot,_,_⟩:=prepared_memory_bounds_opcode _ ah
  have equal : sop=aop:=congrArg Fin.val
    (prepared_memory_message_opcode _ _ matched ⟨sop,hsop⟩ ⟨aop,haop⟩ shot ahot)
  subst aop
  have depth:=fun store=>prepared_memory_sender_store_depth str st sr spub sH shr sop sp hsop store shot positive bound spHot
  exact ⟨⟨sop,hsop⟩,sp,positive,bound,shot,ahot,spHot,depth,
    prepared_memory_message_address _ _ matched sop sp hsop shot positive bound depth spHot,
    prepared_memory_sender_address_type str st sr spub sH shr sop sp hsop shot positive bound spHot,
    fun store=>prepared_memory_message_store_value str atr st sr atable ar spub apub sH shr aH ahr matched sop sp hsop store shot positive bound spHot,
    fun store=>prepared_memory_sender_store_type str st sr spub sH shr sop sp hsop store shot positive bound spHot⟩
end NearCompression
