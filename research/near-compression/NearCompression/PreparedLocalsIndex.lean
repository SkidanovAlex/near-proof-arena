import NearCompression.PreparedLocalsLiteral
import NearCompression.PreparedLocalsStep
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpecV3.Wasm
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

theorem prepared_locals_base_member (count : Nat) (e : Expr)
    (member : e∈preparedLocalsLiteralExecBase) : e∈preparedLocalsLiteralExec count := by
  rw [←List.take_append_drop 824 preparedLocalsLiteralExecBase] at member
  rcases List.mem_append.mp member with left|right
  · simp only [preparedLocalsLiteralExec,List.mem_append];grind
  · rw [←List.take_append_drop 128 (preparedLocalsLiteralExecBase.drop 824)] at right
    rcases List.mem_append.mp right with middle|last
    · simp only [preparedLocalsLiteralExec,List.mem_append];grind
    · simp only [List.drop_drop,show 824+128=952 from rfl] at last
      simp only [preparedLocalsLiteralExec,List.mem_append];grind

theorem prepared_locals_selector_boolean (count : Nat) (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedLocalsLiteralExecTable count) tr t pub) (hr : r<tr.height t)
    (i : Nat) (hi : i<4) : (tr.cell t r (814+i)).toNat≤1 := by
  have source : ∀i,i<4 → preparedGasBoolean (814+i)∈preparedLocalsLiteralExecBase := by
    intro j hj
    have cases : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
    rcases cases with rfl|rfl|rfl|rfl
    · exact List.getElem_mem (l:=preparedLocalsLiteralExecBase) (n:=813) (by decide)
    · exact List.getElem_mem (l:=preparedLocalsLiteralExecBase) (n:=814) (by decide)
    · exact List.getElem_mem (l:=preparedLocalsLiteralExecBase) (n:=815) (by decide)
    · exact List.getElem_mem (l:=preparedLocalsLiteralExecBase) (n:=816) (by decide)
  have h:=localH.constr r hr _ (prepared_locals_base_member count _ (source i hi))
  change tr.cell t r (814+i)*(tr.cell t r (814+i)+ -(1:Fp))+ -(0:Fp)=0 at h
  apply instruction_add_boolean_bound
  grind

/-- Actual source equations yield a valid onehot local selection. -/
theorem prepared_locals_selected (count : Nat) (bounded : count≤4)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedLocalsLiteralExecTable count) tr t pub) (hr : r<tr.height t)
    (localOp : tr.cell t r 683+(tr.cell t r 684+tr.cell t r 685)=1) :
    ∃i,i<count ∧ ∀j,j<4 → tr.cell t r (814+j)=if j=i then 1 else 0 := by
  have source : preparedLocalsLiteralExec0821∈preparedLocalsLiteralExecBase := List.getElem_mem (l:=preparedLocalsLiteralExecBase) (n:=821) (by decide)
  have eq1:=localH.constr r hr _ (prepared_locals_base_member count _ source)
  change (tr.cell t r 814+tr.cell t r 815)+(tr.cell t r 816+tr.cell t r 817)+
    -(tr.cell t r 683+(tr.cell t r 684+tr.cell t r 685))=0 at eq1
  have sum : preparedFieldSum 4 (fun i=>tr.cell t r (814+i))=1 := by
    simp only [preparedFieldSum,Nat.reduceAdd]
    rw [localOp] at eq1
    grind
  obtain ⟨i,hi,hot⟩:=prepared_onehot 4 814 (tr.cell t r) (by decide)
    (prepared_locals_selector_boolean count tr t r pub localH hr) sum
  have valid : i<count := by
    by_cases lt:i<count
    · exact lt
    · have mem : (.add (.col (814+i) false) (.neg (.const 0)))∈preparedLocalsLiteralExec count := by
        have disabled : (.add (.col (814+i) false) (.neg (.const 0)))∈
            (List.range (4-count)).map (fun j=>Expr.add (.col (814+count+j) false) (.neg (.const 0))) := by
          apply List.mem_map.mpr
          refine ⟨i-count,List.mem_range.mpr (by omega),?_⟩
          congr 2 <;> omega
        simp only [preparedLocalsLiteralExec,List.mem_append];grind
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
theorem prepared_locals_index (count : Nat) (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedLocalsLiteralExecTable count) tr t pub) (hr : r<tr.height t)
    (localOp : tr.cell t r 683+(tr.cell t r 684+tr.cell t r 685)=1)
    (i : Nat) (hi : i<4) (hot : ∀j,j<4 → tr.cell t r (814+j)=if j=i then 1 else 0) :
    (preparedCodeLimb (tr.cell t r) 470).toNat+
      65536*(preparedCodeLimb (tr.cell t r) 486).toNat=i := by
  have lo : preparedLocalsLiteralExec0822∈preparedLocalsLiteralExecBase := List.getElem_mem (l:=preparedLocalsLiteralExecBase) (n:=822) (by decide)
  have hh : preparedLocalsLiteralExec0823∈preparedLocalsLiteralExecBase := List.getElem_mem (l:=preparedLocalsLiteralExecBase) (n:=823) (by decide)
  have low:=localH.constr r hr _ (prepared_locals_base_member count _ lo)
  have high:=localH.constr r hr _ (prepared_locals_base_member count _ hh)
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
