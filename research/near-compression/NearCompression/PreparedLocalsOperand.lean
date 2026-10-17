import NearCompression.PreparedLocalsIndex

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpecV3.Wasm

/-- The literal local-index constraints and actual frame-state relation jointly
supply an in-range interpreter lookup. Full next-state refinement is separate. -/
theorem prepared_locals_operand (count : Nat) (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedLocalsLiteralExecTable count) tr t pub)
    (hr : r<tr.height t)
    (localOp : tr.cell t r 683+(tr.cell t r 684+tr.cell t r 685)=1)
    (s : St) (f : Frame) (fs : List Frame) (sp : Nat) (root : Label)
    (state : PreparedLocalsState (tr.cell t r) s f fs sp count root) :
    ∃ i,i<count ∧
      (preparedCodeLimb (tr.cell t r) 470).toNat+
        65536*(preparedCodeLimb (tr.cell t r) 486).toNat=i ∧
      f.locals[i]?=some (.i32 (UInt32.ofNat (preparedLocalsWord (tr.cell t r) i))) := by
  obtain ⟨control,bounded,locals⟩:=state
  obtain ⟨i,hi,hot⟩:=prepared_locals_selected count bounded tr t r pub localH hr localOp
  refine ⟨i,hi,prepared_locals_index count tr t r pub localH hr localOp i (by omega) hot,?_⟩
  rw [locals]
  exact prepared_locals_lookup (tr.cell t r) count i hi

end NearCompression
