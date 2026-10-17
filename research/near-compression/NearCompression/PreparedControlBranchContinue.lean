import NearCompression.PreparedControlBranchState
import NearCompression.PreparedControlTakenState

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2 NearSpecV3.Wasm

/-- Unified affordable br_if step: the caller need not classify the condition.
The actual Boolean AIR flag selects the proved taken or untaken interpreter
step; both preserve the function binding needed for subsequent fetches. -/
theorem prepared_control_setup_branch_continue (count : Nat) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedControlLiteralAir count) pub tr)
    (cfg : NearCfg) (bytes : ByteArray) (method : String) (ctx : CallCtx) (blockLevel : Bool)
    (eligible : PreparedRunCallEligible)
    (accepted : preparedControlSetupCheck cfg bytes method ctx pub blockLevel=some eligible)
    (r : Nat) (nonlast : r+1<tr.height 0) (active : tr.cell 0 r 41=0)
    (branch : tr.cell 0 r 606=1)
    (s : St) (f : Frame) (fs : List Frame) (sp : Nat) (root : Label)
    (state : PreparedControlState (tr.cell 0 r) s f fs sp root)
    (fn : f.fn=eligible.setup.methodIndex-eligible.setup.program.m.imports.size)
    (enough : preparedExecWord64 (tr.cell 0 r) 502≤s.gas.g) :
    ∃ s' f' sp',step cfg eligible.setup.program s=.cont s' ∧
      PreparedControlState (tr.cell 0 (r+1)) s' f' fs sp' root ∧
      f'.fn=f.fn ∧ tr.cell 0 (r+1) 41=0 ∧ tr.cell 0 (r+1) 42=0 := by
  by_cases zero : tr.cell 0 r 681=0
  · obtain ⟨_,s',run,next,done,failed⟩:=prepared_control_setup_untaken_state count tr pub holds
      cfg bytes method ctx blockLevel eligible accepted r nonlast active branch zero
      s f fs sp root state fn enough
    exact ⟨s',_,_,run,next,rfl,done,failed⟩
  · have bound:=prepared_control_literal_boolean tr 0 r pub
      (prepared_control_exec_local count tr pub holds) (by omega) 681 (by decide)
    have nonzero : (tr.cell 0 r 681).toNat≠0 := by
      intro eq
      apply zero
      apply Fp.ext
      exact eq
    have one : tr.cell 0 r 681=1 := by
      apply Fp.ext
      change (tr.cell 0 r 681).toNat=1
      omega
    obtain ⟨height,s',_,run,next,done,failed⟩:=prepared_control_setup_taken_state count tr pub holds
      cfg bytes method ctx blockLevel eligible accepted r nonlast active branch one
      s f fs sp root state fn enough
    exact ⟨s',_,height,run,next,rfl,done,failed⟩

end NearCompression
