import NearCompression.PreparedTypedSource
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpecV3.Wasm
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
private theorem selector_at : ∀count:Fin 5,(preparedTypedLiteralExec count)[1287]?=some preparedLocalsLiteralExec0821 := by decide
private theorem low_at : ∀count:Fin 5,(preparedTypedLiteralExec count)[1288]?=some preparedLocalsLiteralExec0822 := by decide
private theorem high_at : ∀count:Fin 5,(preparedTypedLiteralExec count)[1289]?=some preparedLocalsLiteralExec0823 := by decide
private theorem disabled_slice : ∀count:Fin 5,
    ((preparedTypedLiteralExec count).drop 1290).take (4-count.val)=
      (List.range (4-count.val)).map (fun j=>Expr.add (.col (814+count.val+j) false) (.neg (.const 0))) := by
  intro ⟨n,hn⟩
  have cases : n=0 ∨ n=1 ∨ n=2 ∨ n=3 ∨ n=4:=by omega
  rcases cases with rfl|rfl|rfl|rfl|rfl <;> rfl
/-- Actual source equations yield a valid onehot local selection. -/
theorem prepared_typed_local_selected (count : Nat) (bounded : count≤4)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedTypedLiteralExecTable count) tr t pub) (hr : r<tr.height t)
    (localOp : tr.cell t r 683+(tr.cell t r 684+tr.cell t r 685)=1) :
    ∃i,i<count ∧ ∀j,j<4 → tr.cell t r (814+j)=if j=i then 1 else 0 := by
  have eq1:=localH.constr r hr _ (List.mem_of_getElem? (selector_at ⟨count,by omega⟩))
  change (tr.cell t r 814+tr.cell t r 815)+(tr.cell t r 816+tr.cell t r 817)+
    -(tr.cell t r 683+(tr.cell t r 684+tr.cell t r 685))=0 at eq1
  have sum : preparedFieldSum 4 (fun i=>tr.cell t r (814+i))=1 := by
    simp only [preparedFieldSum,Nat.reduceAdd]
    rw [localOp] at eq1
    grind
  obtain ⟨i,hi,hot⟩:=prepared_onehot 4 814 (tr.cell t r) (by decide)
    (fun i hi=>prepared_typed_source_boolean count bounded tr t r pub localH hr (814+i) (by omega) (by omega) (by omega)) sum
  have valid : i<count := by
    by_cases lt:i<count
    · exact lt
    · have mem : (.add (.col (814+i) false) (.neg (.const 0)))∈preparedTypedLiteralExec count := by
        have disabled : (.add (.col (814+i) false) (.neg (.const 0)))∈
            (List.range (4-count)).map (fun j=>Expr.add (.col (814+count+j) false) (.neg (.const 0))) := by
          apply List.mem_map.mpr
          refine ⟨i-count,List.mem_range.mpr (by omega),?_⟩
          congr 2 <;> omega
        apply List.mem_of_mem_drop (i:=1290)
        apply List.mem_of_mem_take (i:=4-count)
        rw [disabled_slice ⟨count,by omega⟩]
        exact disabled
      have zero:=localH.constr r hr _ mem
      change tr.cell t r (814+i)+ -(0:Fp)=0 at zero
      have one:=hot i hi
      simp only [ite_true] at one
      rw [one] at zero
      have nope : (1:Fp)≠0 := by decide
      exact False.elim (nope (by grind))
  exact ⟨i,valid,hot⟩

/-- Separate16-bit source equations bind the selected index without accepting
an immediate shifted by a multiple of the field modulus. -/
theorem prepared_typed_local_index (count : Nat) (bounded : count≤4) (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedTypedLiteralExecTable count) tr t pub) (hr : r<tr.height t)
    (localOp : tr.cell t r 683+(tr.cell t r 684+tr.cell t r 685)=1)
    (i : Nat) (hi : i<4) (hot : ∀j,j<4 → tr.cell t r (814+j)=if j=i then 1 else 0) :
    (preparedCodeLimb (tr.cell t r) 470).toNat+
      65536*(preparedCodeLimb (tr.cell t r) 486).toNat=i := by
  have low:=localH.constr r hr _ (List.mem_of_getElem? (low_at ⟨count,by omega⟩))
  have high:=localH.constr r hr _ (List.mem_of_getElem? (high_at ⟨count,by omega⟩))
  change (tr.cell t r 683+(tr.cell t r 684+tr.cell t r 685))*(preparedCodeBits 470).eval tr t r pub+
    -(((0:Fp)*tr.cell t r 814+1*tr.cell t r 815)+(2*tr.cell t r 816+3*tr.cell t r 817))=0 at low
  change (tr.cell t r 683+(tr.cell t r 684+tr.cell t r 685))*(preparedCodeBits 486).eval tr t r pub+ -(0:Fp)=0 at high
  rw [localOp,prepared_code_bits_eval] at low high
  simp only [Bool.false_eq_true,ite_false] at low high
  have h0:=hot 0 (by decide);have h1:=hot 1 (by decide)
  have h2:=hot 2 (by decide);have h3:=hot 3 (by decide)
  have hz : preparedCodeLimb (tr.cell t r) 486=0 := by grind
  rw [hz]
  have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
  rcases cases with rfl|rfl|rfl|rfl
  all_goals simp only [Nat.reduceAdd,Nat.reduceEqDiff,ite_true,ite_false] at h0 h1 h2 h3
  all_goals rw [h0,h1,h2,h3] at low
  · have hl : preparedCodeLimb (tr.cell t r) 470=0 := by grind
    rw [hl];rfl
  · have hl : preparedCodeLimb (tr.cell t r) 470=1 := by grind
    rw [hl];rfl
  · have hl : preparedCodeLimb (tr.cell t r) 470=2 := by grind
    rw [hl];rfl
  · have hl : preparedCodeLimb (tr.cell t r) 470=3 := by grind
    rw [hl];rfl
end NearCompression
