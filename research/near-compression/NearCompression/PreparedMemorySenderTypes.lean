import NearCompression.PreparedMemorySenderOperands
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

def preparedMemorySenderType (depth : Nat) : Expr :=
  let term:=fun i=>.mul (.col (520+depth+i) false) (.col (512+i) false)
  if depth=1 then preparedGasSumTree term 3 0
  else .add (preparedGasSumTree term 2 0) (.add (preparedGasSumTree term 1 4) (term 6))
private theorem type_eval (row : Nat→Fp) (depth : Nat) (hd:depth=1∨depth=2) :
    (preparedMemorySenderType depth).evalWith (preparedGasEnv row [])=
      preparedFieldSum (9-depth) (fun i=>row (520+depth+i)*row (512+i)) := by
  rcases hd with rfl|rfl <;>
    simp only [preparedMemorySenderType,preparedGasSumTree,Expr.evalWith,preparedFieldSum,Nat.reduceAdd,Nat.reduceSub,Nat.reducePow,
      Nat.reduceEqDiff,ite_true,ite_false,preparedGasEnv,instructionAddEnv] <;> grind
private theorem type_selected (row : Nat→Fp) (sp depth : Nat) (hd:depth=1∨depth=2)
    (positive:depth≤sp) (bound:sp<9) (hot:∀i,i<9→row (520+i)=if i=sp then 1 else 0) :
    (preparedMemorySenderType depth).evalWith (preparedGasEnv row [])=row (512+(sp-depth)) := by
  rw [type_eval row depth hd]
  apply prepared_sum_select (9-depth) (sp-depth) _ _ (by omega)
  intro i hi
  have eq:=hot (depth+i) (by omega)
  have index:520+(depth+i)=520+depth+i:=by omega
  rw [index] at eq
  rw [eq]
  split <;> split <;> simp_all <;> omega

/-- Canonical i32 values have zero high bits in every stack slot, derived from
actual source constraints even before a slot is selected. -/
theorem prepared_memory_sender_i32_high (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH:TableLocal preparedMemorySenderLiteralTable tr t pub) (hr:r<tr.height t)
    (slot : Fin 8) (tag:tr.cell t r (512+slot)=0) (bit : Nat) (low:32≤bit) (high:bit<64) :
    tr.cell t r (64*slot+bit)=0 := by
  have shapes : ∀j:Fin 8,∀b:Fin 32,
      preparedMemorySenderLiteralConstraints[835+97*j.val+2*b.val]?=
        some (.add (.mul (.add (.const 1) (.neg (.col (512+j.val) false)))
          (.col (64*j.val+32+b.val) false)) (.neg (.const 0))) := by decide
  have h:=localH.constr r hr _ (List.mem_of_getElem? (shapes slot ⟨bit-32,by omega⟩))
  change ((1:Fp)+ -tr.cell t r (512+slot)) * tr.cell t r (64*slot+32+(bit-32))+ -0=0 at h
  have idx:64*slot+32+(bit-32)=64*slot+bit:=by omega
  rw [tag,idx] at h
  grind

/-- Both load and store address operands are i32. Store depth is supplied by
its proved literal guard, not an arbitrary missing-slot convention. -/
theorem prepared_memory_sender_address_type (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH:TableLocal preparedMemorySenderLiteralTable tr t pub) (hr:r<tr.height t)
    (op sp : Nat) (hop:op<19) (hot:∀i,i<19→tr.cell t r (529+i)=if i=op then 1 else 0)
    (positive:0<sp) (bound:sp<9) (spHot:∀i,i<9→tr.cell t r (520+i)=if i=sp then 1 else 0) :
    tr.cell t r (512+(sp-(if 12≤op then 2 else 1)))=0 := by
  have shape:preparedMemorySenderLiteralConstraints[799]?=some
      (.add (.add (.mul (.add (.const 1) (.neg preparedMemorySenderWrite)) (preparedMemorySenderType 1))
        (.mul preparedMemorySenderWrite (preparedMemorySenderType 2))) (.neg (.const 0))) := by decide
  have h:=localH.constr r hr _ (List.mem_of_getElem? shape)
  change ((1:Fp)+ -preparedMemorySenderWrite.evalWith (preparedGasEnv (tr.cell t r) []))*
    (preparedMemorySenderType 1).evalWith (preparedGasEnv (tr.cell t r) [])+
    preparedMemorySenderWrite.evalWith (preparedGasEnv (tr.cell t r) [])*
    (preparedMemorySenderType 2).evalWith (preparedGasEnv (tr.cell t r) [])+ -0=0 at h
  rw [prepared_memory_sender_write_selected _ op hop hot] at h
  by_cases store:12≤op
  · have depth:=prepared_memory_sender_store_depth tr t r pub localH hr op sp hop store hot positive bound spHot
    rw [if_pos store,type_selected _ sp 2 (Or.inr rfl) depth bound spHot] at h
    rw [if_pos store]
    grind
  · rw [if_neg store,type_selected _ sp 1 (Or.inl rfl) positive bound spHot] at h
    rw [if_neg store]
    grind

private def kindExpr : Expr := preparedMemorySenderSelector (fun i=>if preparedMemoryIs64 i then 1 else 0)
private theorem kind_selected (row : Nat→Fp) (op : Nat) (hop:op<19)
    (hot:∀i,i<19→row (529+i)=if i=op then 1 else 0) :
    kindExpr.evalWith (preparedGasEnv row [])=if preparedMemoryIs64 op then 1 else 0 := by
  have sum:kindExpr.evalWith (preparedGasEnv row [])=
      preparedFieldSum 19 (fun i=>row (529+i)*Fp.ofNat (if preparedMemoryIs64 i then 1 else 0)) := by
    simp only [kindExpr,preparedMemorySenderSelector,preparedMemorySum19,preparedGasSumTree,Expr.evalWith,
      preparedFieldSum,Nat.reduceAdd,Nat.reducePow,preparedGasEnv,instructionAddEnv]
    grind
  rw [sum,prepared_sum_select 19 op _ _ hop hot]
  split <;> rfl

/-- Stored top values must have the i32/i64 type selected by the actual
memory opcode. Together with i32_high this rules out hidden high limbs. -/
theorem prepared_memory_sender_store_type (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH:TableLocal preparedMemorySenderLiteralTable tr t pub) (hr:r<tr.height t)
    (op sp : Nat) (hop:op<19) (store:12≤op)
    (hot:∀i,i<19→tr.cell t r (529+i)=if i=op then 1 else 0)
    (positive:0<sp) (bound:sp<9) (spHot:∀i,i<9→tr.cell t r (520+i)=if i=sp then 1 else 0) :
    tr.cell t r (512+(sp-1))=if preparedMemoryIs64 op then 1 else 0 := by
  have shape:preparedMemorySenderLiteralConstraints[800]?=some
      (.add (.mul preparedMemorySenderWrite (.add (preparedMemorySenderType 1) (.neg kindExpr))) (.neg (.const 0))) := by decide
  have h:=localH.constr r hr _ (List.mem_of_getElem? shape)
  change preparedMemorySenderWrite.evalWith (preparedGasEnv (tr.cell t r) [])*
    ((preparedMemorySenderType 1).evalWith (preparedGasEnv (tr.cell t r) [])+
      -kindExpr.evalWith (preparedGasEnv (tr.cell t r) []))+ -0=0 at h
  rw [prepared_memory_sender_write_selected _ op hop hot,if_pos store,
    type_selected _ sp 1 (Or.inl rfl) positive bound spHot,kind_selected _ op hop hot] at h
  grind
end NearCompression
