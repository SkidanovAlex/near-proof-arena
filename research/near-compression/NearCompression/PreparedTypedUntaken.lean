import NearCompression.PreparedTypedBranch
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpecV3.Wasm
theorem prepared_typed_untaken_pc_label (count : Nat) (hc : count≤4) (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedTypedLiteralExecTable count) tr t pub) (nonlast : r+1<tr.height t)
    (active : tr.cell t r 41=0) (charged : tr.cell t r 430=0)
    (branch : tr.cell t r 606=1) (zero : tr.cell t r 681=0) :
    preparedCodeExecPC (tr.cell t (r+1))=preparedCodeExecPC (tr.cell t r)+1 ∧
    tr.cell t (r+1) 41=0 ∧ tr.cell t (r+1) 42=0 ∧
    tr.cell t (r+1) 639=tr.cell t r 639 ∧
    (∀ i,i<9 → tr.cell t (r+1) (640+i)=tr.cell t r (640+i)) ∧
    preparedControlSavedTarget (tr.cell t (r+1))=preparedControlSavedTarget (tr.cell t r) := by
  have ops:=prepared_typed_branch_opcode count hc tr t r pub localH (by omega) branch
  have notTaken : preparedControlTaken.eval tr t r pub=0 := by
    change preparedExecGasSuccess.eval tr t r pub*(tr.cell t r 606*tr.cell t r 681)=0
    rw [zero];grind
  have advance : preparedControlAdvance.eval tr t r pub=Fp.ofNat 1 := by
    change (((1:Fp)+ -tr.cell t r 41)*((1:Fp)+ -tr.cell t r 430))*
      ((1:Fp)+ -(tr.cell t r 469*((1:Fp)+ -tr.cell t r 639)+tr.cell t r 606*tr.cell t r 681))=1
    rw [active,charged,ops.1 3 (by decide),zero];grind
  have status:=prepared_typed_continue_status count hc tr t r pub localH nonlast active charged (by rw [ops.1 3 (by decide)];grind)
  have opened : preparedControlOpened.eval tr t r pub=0 := by
    change preparedExecGasSuccess.eval tr t r pub*tr.cell t r 605=0
    rw [ops.2];grind
  have keep : preparedControlKeep.eval tr t r pub=1 := by
    change (1:Fp)+ -(preparedControlOpened.eval tr t r pub+
      (preparedControlTaken.eval tr t r pub+preparedExecGasSuccess.eval tr t r pub*(tr.cell t r 469*tr.cell t r 639)))=1
    rw [opened,notTaken,ops.1 3 (by decide)];grind
  have labels:=prepared_typed_label_equations count hc tr t r pub localH nonlast
  rw [opened,keep] at labels
  refine ⟨prepared_typed_sequential_pc count hc tr t r pub localH nonlast notTaken 1 (by decide) advance,
    status.2.1,status.2.2,by grind,?_,?_⟩
  · intro i hi;have h:=labels.2.1 i hi;grind
  · have low:=labels.2.2 0 (by decide)
    have high:=labels.2.2 1 (by decide)
    have l : preparedCodeLimb (tr.cell t (r+1)) 649=preparedCodeLimb (tr.cell t r) 649:=by simpa only [Nat.mul_zero,Nat.add_zero] using (show _=_ from by grind)
    have h : preparedCodeLimb (tr.cell t (r+1)) 665=preparedCodeLimb (tr.cell t r) 665:=by simpa only [Nat.mul_one,Nat.reduceAdd] using (show _=_ from by grind)
    unfold preparedControlSavedTarget
    rw [l,h]

end NearCompression
