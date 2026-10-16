import NearCompression.PreparedTypedEqzStack
import NearCompression.PreparedTypedEqzDepth
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpecV3.Wasm
set_option maxRecDepth 65536

theorem prepared_typed_stack_succ (row : Nat→Fp) (n : Nat) :
    preparedTypedStack row (n+1)=(preparedTypedStack row n).push (preparedTypedStackValue row n) := by
  simp [preparedTypedStack,List.range_succ,List.map_append]

theorem prepared_typed_stack_congr (row next : Nat→Fp) (n : Nat)
    (values : ∀i,i<n → preparedTypedStackValue next i=preparedTypedStackValue row i) :
    preparedTypedStack next n=preparedTypedStack row n := by
  unfold preparedTypedStack
  congr 1
  apply List.map_congr_left
  intro i hi
  exact values i (List.mem_range.mp hi)

/-- Both exact array equalities needed by actual pop/push semantics. The
prefixEq is decoded from the current row; next-row source writes determine it. -/
theorem prepared_typed_eqz_arrays (count : Nat) (hc : count≤4)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedTypedLiteralExecTable count) tr t pub) (nonlast : r+1<tr.height t)
    (active : tr.cell t r 41=0) (charged : tr.cell t r 430=0) (opcode : tr.cell t r 1282=1) :
    ∃sp,sp<9 ∧ 0<sp ∧
      (∀i,i<9 → tr.cell t r (32+i)=if i=sp then 1 else 0) ∧
      (∀i,i<9 → tr.cell t (r+1) (32+i)=if i=sp then 1 else 0) ∧
      preparedTypedStack (tr.cell t r) sp=(preparedTypedStack (tr.cell t r) (sp-1)).push
        (.i64 (UInt64.ofNat (preparedTypedStackWord (tr.cell t r) (sp-1)))) ∧
      preparedTypedStack (tr.cell t (r+1)) sp=(preparedTypedStack (tr.cell t r) (sp-1)).push
        (.i32 (if preparedTypedStackWord (tr.cell t r) (sp-1)=0 then 1 else 0)) := by
  obtain ⟨sp,hs,pos,hot,top,values⟩:=prepared_typed_eqz_stack_projection count hc tr t r pub localH nonlast active charged opcode
  refine ⟨sp,hs,pos,hot,prepared_typed_eqz_depth count hc tr t r pub localH nonlast opcode sp hs hot,?_,?_⟩
  · have eq:sp=(sp-1)+1:=by omega
    have e:=prepared_typed_stack_succ (tr.cell t r) (sp-1)
    rw [←eq] at e
    rw [e,top]
  · have prefixEq : preparedTypedStack (tr.cell t (r+1)) (sp-1)=preparedTypedStack (tr.cell t r) (sp-1) := by
      apply prepared_typed_stack_congr
      intro i hi
      simpa only [show ¬i+1=sp by omega,ite_false] using values i (by omega)
    have eq:sp=(sp-1)+1:=by omega
    have e:=prepared_typed_stack_succ (tr.cell t (r+1)) (sp-1)
    rw [←eq] at e
    rw [e,prefixEq]
    have v:=values (sp-1) (by omega)
    simp only [show sp-1+1=sp by omega,ite_true] at v
    rw [v]
end NearCompression
