import NearCompression.PreparedMemoryMessageFields
import NearCompression.PreparedMemoryStoreBridge
namespace NearCompression
open NearSpec NearSpecV3 NearSpecV3.Wasm ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

def preparedMemorySenderResultValue (row : Nat→Fp) (op : Nat) : Val :=
  if preparedMemoryIs64 op then .i64 (UInt64.ofNat (preparedMemoryWord row 693))
  else .i32 (UInt32.ofNat (preparedMemoryWord row 693))
def preparedMemorySenderValue (row : Nat→Fp) (sp op : Nat) : Val :=
  if preparedMemoryIs64 op then .i64 (UInt64.ofNat (preparedMemoryWord row (64*(sp-1))))
  else .i32 (UInt32.ofNat (preparedMemoryWord row (64*(sp-1))))
private theorem chosen_eq (row : Nat→Fp) (chosen selected : Fin 19)
    (hot:∀i,i<19→row (529+i)=if i=chosen.val then 1 else 0)
    (opcode:row (529+selected.val)=1) : chosen=selected := by
  apply Fin.ext
  have h:=hot selected selected.isLt
  rw [opcode] at h
  by_cases same:selected.val=chosen.val
  · omega
  · rw [if_neg same] at h
    exact False.elim ((by decide:(1:Fp)≠0) h)

/-- Exact load execution uses the selected sender stack operand and sender
result columns. Only the local message equality is assumed; neither a selected
SP nor operand equality is supplied by the caller. The remaining lower stack
state s and actual code/charge context belong to the EXEC state relation. -/
theorem prepared_memory_attached_load_exec
    (str atr : Trace Fp) (st sr atable ar : Nat) (spub apub : List Fp)
    (sH:TableLocal preparedMemorySenderLiteralTable str st spub) (shr:sr<str.height st)
    (aH:TableLocal preparedMemoryLiteralTable atr atable apub) (ahr:ar<atr.height atable)
    (matched:PreparedMemoryMessagesMatch (str.cell st sr) (atr.cell atable ar))
    (selected:Fin 19) (opcode:str.cell st sr (529+selected.val)=1) (load:selected.val<12)
    (hash:Bytes→ByteArray) (digestBound:∀bs,bytesWireWf (hash bs))
    (cfg:NearCfg) (p:Prepared) (s:St) (full:fullPages s.pages)
    (block count depth:Nat) (wf:blockDescriptorWf (describeSubpageMemory hash s block count depth))
    (f:Frame) (pf:PFunc) (align:Nat) (openings:List PreparedMemoryReadOpening) (output:BlockDescriptor)
    (accepted:preparedMemoryServiceCheck hash (describeSubpageMemory hash s block count depth)
      (preparedMemoryWord (str.cell st sr) 580) [preparedMemoryLoadRequest (atr.cell atable ar) selected openings]=some output) :
    ∃sp,0<sp ∧ sp<9 ∧ str.cell st sr (512+(sp-1))=0 ∧
      ((exec cfg p (pushV s (.i32 (UInt32.ofNat (preparedMemoryAddressWord (str.cell st sr) (64*(sp-1)))))) f pf
        (.load (preparedMemoryOpcode selected) align (preparedMemoryAddressWord (str.cell st sr) 548))=
        .cont (setFrame (pushV s (preparedMemorySenderResultValue (str.cell st sr) selected)) {f with pc:=f.pc+1}) ∧
        output=describeSubpageMemory hash s block count depth) ∨
      PreparedMemoryReadCollision hash s block count depth (preparedMemoryWidth selected) openings) := by
  obtain ⟨chosen,sp,positive,bound,shot,ahot,spHot,_,address,addressType,_,_⟩:=
    prepared_memory_matched_operands str atr st sr atable ar spub apub sH shr aH ahr matched
  have eq:=chosen_eq _ chosen selected shot opcode
  subst chosen
  have notStore:¬12≤selected.val:=by omega
  rw [if_neg notStore] at address addressType
  have clock:=prepared_memory_message_clock str atr st sr atable ar spub apub sH shr aH ahr matched
  have offset:=prepared_memory_message_offset _ _ matched
  have result:=prepared_memory_message_result str atr st sr atable ar spub apub sH shr aH ahr matched
  have acceptedA:preparedMemoryServiceCheck hash (describeSubpageMemory hash s block count depth)
      (preparedMemoryWord (atr.cell atable ar) 51) [preparedMemoryLoadRequest (atr.cell atable ar) selected openings]=some output := by
    rw [clock];exact accepted
  have execution:=prepared_memory_load_service_exec atr atable ar apub aH ahr selected ahot load hash digestBound cfg p s full block count depth wf f pf align openings output acceptedA
  refine ⟨sp,positive,bound,addressType,?_⟩
  rcases execution with success|bad
  · apply Or.inl
    rw [address,offset] at success
    have value:preparedMemoryResultValue (atr.cell atable ar) selected=preparedMemorySenderResultValue (str.cell st sr) selected := by
      unfold preparedMemoryResultValue preparedMemorySenderResultValue
      rw [result]
    rw [value] at success
    exact success
  · exact Or.inr bad

/-- Exact stores consume the selected mixed-type sender value and the i32
address beneath it. Source and adapter are linked limbwise; service acceptance
supplies actual memory consistency or a finitely supported collision. -/
theorem prepared_memory_attached_store_exec
    (str atr : Trace Fp) (st sr atable ar : Nat) (spub apub : List Fp)
    (sH:TableLocal preparedMemorySenderLiteralTable str st spub) (shr:sr<str.height st)
    (aH:TableLocal preparedMemoryLiteralTable atr atable apub) (ahr:ar<atr.height atable)
    (matched:PreparedMemoryMessagesMatch (str.cell st sr) (atr.cell atable ar))
    (selected:Fin 19) (opcode:str.cell st sr (529+selected.val)=1) (store:12≤selected.val)
    (hash:Bytes→ByteArray) (digestBound:∀bs,bytesWireWf (hash bs))
    (cfg:NearCfg) (p:Prepared) (s:St) (full:fullPages s.pages)
    (block count depth:Nat) (f:Frame) (pf:PFunc) (align:Nat) (batches:List PageBatchWitness) (output:BlockDescriptor)
    (accepted:preparedMemoryServiceCheck hash (describeSubpageMemory hash s block count depth)
      (preparedMemoryWord (str.cell st sr) 580) [preparedMemoryStoreRequest (atr.cell atable ar) selected batches]=some output) :
    ∃sp,2≤sp ∧ sp<9 ∧ str.cell st sr (512+(sp-2))=0 ∧
      str.cell st sr (512+(sp-1))=(if preparedMemoryIs64 selected then 1 else 0) ∧
      ((∃next,exec cfg p (pushV (pushV s (.i32 (UInt32.ofNat
          (preparedMemoryAddressWord (str.cell st sr) (64*(sp-2))))))
          (preparedMemorySenderValue (str.cell st sr) sp selected)) f pf
        (.store (preparedMemoryOpcode selected) align (preparedMemoryAddressWord (str.cell st sr) 548))=.cont next ∧
        output=describeSubpageMemory hash next block count depth) ∨
      blockBatchCollision hash block count depth s batches) := by
  obtain ⟨chosen,sp,positive,bound,shot,ahot,spHot,depthGuard,address,addressType,value,kind⟩:=
    prepared_memory_matched_operands str atr st sr atable ar spub apub sH shr aH ahr matched
  have eq:=chosen_eq _ chosen selected shot opcode
  subst chosen
  rw [if_pos store] at address addressType
  have clock:=prepared_memory_message_clock str atr st sr atable ar spub apub sH shr aH ahr matched
  have offset:=prepared_memory_message_offset _ _ matched
  have acceptedA:preparedMemoryServiceCheck hash (describeSubpageMemory hash s block count depth)
      (preparedMemoryWord (atr.cell atable ar) 51) [preparedMemoryStoreRequest (atr.cell atable ar) selected batches]=some output := by
    rw [clock];exact accepted
  have execution:=prepared_memory_store_service_exec atr atable ar apub aH ahr selected ahot store hash digestBound cfg p s full block count depth f pf align batches output acceptedA
  refine ⟨sp,depthGuard store,bound,addressType,kind store,?_⟩
  rcases execution with success|bad
  · apply Or.inl
    rw [address,offset] at success
    have val:preparedMemoryStoreValue (atr.cell atable ar) selected=preparedMemorySenderValue (str.cell st sr) sp selected := by
      unfold preparedMemoryStoreValue preparedMemorySenderValue
      rw [value store]
    rw [val] at success
    exact success
  · exact Or.inr bad
end NearCompression
