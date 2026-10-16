import NearCompression.PreparedControlLegacyAdapter

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2 NearSpecV3.Wasm

/-- An authenticated ordinary instruction supplies the no-branch condition
needed by the reusable arithmetic/stack interface. The tag premise classifies
the decoded actual instruction; it does not assume a trace flag is zero. -/
theorem prepared_control_authenticated_legacy_projection (count : Nat) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedControlLiteralAir count) pub tr)
    (pf : PFunc) (fn : Nat) (checked : preparedControlCodeCheck pf fn pub=true)
    (r : Nat) (nonlast : r+1<tr.height 0)
    (ordinary : ∀ op : PreparedControlInstruction,
      pf.code[preparedCodeExecPC (tr.cell 0 r)]?=some op.instr → op.tag<4) :
    let row:=preparedExecGhostRow (tr.cell 0 r)
    let next:=preparedExecGhostNext (tr.cell 0 r) (tr.cell 0 (r+1)) (fun i=>pub.getD i 0)
    let fields:=preparedExecGhostPub (tr.cell 0 r) (tr.cell 0 (r+1)) (fun i=>pub.getD i 0)
    preparedRowChoices row next fields 0 0 ∧ PreparedAddTransitionHolds row next fields := by
  obtain ⟨_,op,code,_,_,ops,_⟩:=prepared_control_authenticated_decode count tr pub holds pf fn checked r (by omega)
  have tag:=ordinary op code
  have absent:=ops 5 (by decide)
  change tr.cell 0 r 606=(if 5=op.tag then 1 else 0) at absent
  rw [ite_eq_right (by omega)] at absent
  exact prepared_control_legacy_projection tr 0 r pub (prepared_control_exec_local count tr pub holds)
    nonlast absent

end NearCompression
