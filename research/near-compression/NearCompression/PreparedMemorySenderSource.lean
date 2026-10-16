import NearCompression.PreparedMemorySenderLiteral
import NearCompression.PreparedMemoryResultBits
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
private theorem bit_prefix : preparedMemorySenderLiteralConstraints.take 795=
    (List.range 795).map preparedGasBoolean := by rfl

def preparedMemorySenderTop (limb : Nat) : Expr :=
  preparedGasSumTree (fun i=>.mul (.col (521+i) false) (preparedGasBits (64*i+16*limb))) 3 0
def preparedMemorySenderSecond (limb : Nat) : Expr :=
  let term:=fun i=>.mul (.col (522+i) false) (preparedGasBits (64*i+16*limb))
  .add (preparedGasSumTree term 2 0) (.add (preparedGasSumTree term 1 4) (term 6))

theorem prepared_memory_sender_boolean (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH:TableLocal preparedMemorySenderLiteralTable tr t pub) (hr:r<tr.height t)
    (i : Nat) (hi:i<795) : (tr.cell t r i).toNat≤1 := by
  have mem:preparedGasBoolean i∈(List.range 795).map preparedGasBoolean := List.mem_map.mpr ⟨i,List.mem_range.mpr hi,rfl⟩
  rw [←bit_prefix] at mem
  have h:=localH.constr r hr _ (List.mem_of_mem_take mem)
  change tr.cell t r i*(tr.cell t r i + -(1:Fp))+ -(0:Fp)=0 at h
  exact instruction_add_boolean_bound _ (by grind)

/-- Stack pointer is derived from the actual source one-hot and nonempty
constraints, not supplied as an operand-lookup assumption. -/
theorem prepared_memory_sender_sp (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH:TableLocal preparedMemorySenderLiteralTable tr t pub) (hr:r<tr.height t) :
    ∃sp,0<sp ∧ sp<9 ∧ ∀i,i<9→tr.cell t r (520+i)=if i=sp then 1 else 0 := by
  have sumAt:preparedMemorySenderLiteralConstraints[795]?=some preparedMemorySenderLiteral0795 := by decide
  have zeroAt:preparedMemorySenderLiteralConstraints[797]?=some preparedMemorySenderLiteral0797 := by decide
  have h:=localH.constr r hr _ (List.mem_of_getElem? sumAt)
  have hz:=localH.constr r hr _ (List.mem_of_getElem? zeroAt)
  change tr.cell t r 520+ -(0:Fp)=0 at hz
  have zero:tr.cell t r 520=0:=by grind
  have sum:preparedFieldSum 9 (fun i=>tr.cell t r (520+i))=1 := by
    change (((tr.cell t r 520+tr.cell t r 521)+(tr.cell t r 522+tr.cell t r 523))+
      ((tr.cell t r 524+tr.cell t r 525)+(tr.cell t r 526+tr.cell t r 527)))+tr.cell t r 528+ -(1:Fp)=0 at h
    simp only [preparedFieldSum,Nat.reduceAdd]
    grind
  obtain ⟨sp,hs,hot⟩:=prepared_onehot 9 520 (tr.cell t r) (by decide)
    (fun i hi=>prepared_memory_sender_boolean tr t r pub localH hr (520+i) (by omega)) sum
  refine ⟨sp,?_,hs,hot⟩
  have first:=hot 0 (by decide)
  simp only [Nat.add_zero,zero] at first
  by_cases hsp:sp=0
  · rw [hsp,if_pos rfl] at first
    exact False.elim ((by decide : (0:Fp)≠1) first)
  · omega

private theorem top_eval (row : Nat→Fp) (limb : Nat) :
    (preparedMemorySenderTop limb).evalWith (preparedGasEnv row [])=
      preparedFieldSum 8 (fun i=>row (521+i)*(preparedGasBits (64*i+16*limb)).evalWith (preparedGasEnv row [])) := by
  simp only [preparedMemorySenderTop,preparedGasSumTree,Expr.evalWith,preparedFieldSum,Nat.reduceAdd,Nat.reducePow,preparedGasEnv,instructionAddEnv]
  grind
private theorem second_eval (row : Nat→Fp) (limb : Nat) :
    (preparedMemorySenderSecond limb).evalWith (preparedGasEnv row [])=
      preparedFieldSum 7 (fun i=>row (522+i)*(preparedGasBits (64*i+16*limb)).evalWith (preparedGasEnv row [])) := by
  simp only [preparedMemorySenderSecond,preparedGasSumTree,Expr.evalWith,preparedFieldSum,Nat.reduceAdd,Nat.reducePow,preparedGasEnv,instructionAddEnv]
  grind

/-- Exact source top-operand expression selects the current stack slot. -/
theorem prepared_memory_sender_top_selected (row : Nat→Fp) (sp limb : Nat)
    (positive:0<sp) (bound:sp<9) (hot:∀i,i<9→row (520+i)=if i=sp then 1 else 0) :
    (preparedMemorySenderTop limb).evalWith (preparedGasEnv row [])=
      (preparedGasBits (64*(sp-1)+16*limb)).evalWith (preparedGasEnv row []) := by
  rw [top_eval]
  apply prepared_sum_select 8 (sp-1) _ _ (by omega)
  intro i hi
  have eq:=hot (i+1) (by omega)
  have index:520+(i+1)=521+i:=by omega
  rw [index] at eq
  rw [eq]
  split <;> split <;> simp_all <;> omega

/-- Exact source second operand expression selects beneath the store value. -/
theorem prepared_memory_sender_second_selected (row : Nat→Fp) (sp limb : Nat)
    (positive:2≤sp) (bound:sp<9) (hot:∀i,i<9→row (520+i)=if i=sp then 1 else 0) :
    (preparedMemorySenderSecond limb).evalWith (preparedGasEnv row [])=
      (preparedGasBits (64*(sp-2)+16*limb)).evalWith (preparedGasEnv row []) := by
  rw [second_eval]
  apply prepared_sum_select 7 (sp-2) _ _ (by omega)
  intro i hi
  have eq:=hot (i+2) (by omega)
  have index:520+(i+2)=522+i:=by omega
  rw [index] at eq
  rw [eq]
  split <;> split <;> simp_all <;> omega
end NearCompression
