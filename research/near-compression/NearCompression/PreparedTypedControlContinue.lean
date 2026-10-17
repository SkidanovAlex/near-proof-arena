import NearCompression.PreparedTypedBranchState
import NearCompression.PreparedTypedAuthenticatedControl
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2 NearSpecV3.Wasm
set_option maxRecDepth 65536
theorem prepared_typed_setup_branch_continue (codeCount count : Nat) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedTypedLiteralAir codeCount count) pub tr)
    (cfg : NearCfg) (bytes : ByteArray) (method : String) (ctx : CallCtx) (blockLevel : Bool)
    (eligible : PreparedRunCallEligible)
    (accepted : preparedTypedSetupCheck count cfg bytes method ctx pub blockLevel=some eligible)
    (r : Nat) (nonlast : r+1<tr.height 0) (active : tr.cell 0 r 41=0)
    (branch : tr.cell 0 r 606=1)
    (s : St) (f : Frame) (fs : List Frame) (sp : Nat) (root : Label)
    (state : PreparedTypedState (tr.cell 0 r) s f fs sp count root)
    (fn : f.fn=eligible.setup.methodIndex-eligible.setup.program.m.imports.size)
    (enough : preparedExecWord64 (tr.cell 0 r) 502≤s.gas.g) :
    ∃ s' f' sp',step cfg eligible.setup.program s=.cont s' ∧
      PreparedTypedState (tr.cell 0 (r+1)) s' f' fs sp' count root ∧
      f'.fn=f.fn ∧ tr.cell 0 (r+1) 41=0 ∧ tr.cell 0 (r+1) 42=0 := by
  obtain ⟨setup,func,checked⟩:=prepared_typed_setup_checked count cfg bytes method ctx pub blockLevel eligible accepted
  obtain ⟨_,op,fee,amount,targetValue,code,_,_,_,targetBound,_,target,fields⟩:=prepared_typed_authenticated_fetch codeCount count tr pub holds eligible.func _ checked r (by omega)
  obtain ⟨_,charge,bound⟩:=prepared_typed_authenticated_fee codeCount count tr pub holds eligible.func _ checked r (by omega)
  have tag:=fields 26 (by decide)
  change tr.cell 0 r 606=(if 5=op.tag then 1 else 0) at tag
  rw [branch] at tag
  have opEq : op=PreparedTypedInstruction.control .brIf := by
    cases op with
    | control old=>
      cases old with
      | block=>exact False.elim ((by decide : (1:Fp)≠0) tag)
      | brIf=>rfl
      | legacy old=>cases old <;> exact False.elim ((by decide : (1:Fp)≠0) tag)
    | «local» kind i=>cases kind <;> exact False.elim ((by decide : (1:Fp)≠0) tag)
    | constant64 v=>exact False.elim ((by decide : (1:Fp)≠0) tag)
    | add64=>exact False.elim ((by decide : (1:Fp)≠0) tag)
    | eqz64=>exact False.elim ((by decide : (1:Fp)≠0) tag)
  subst op
  rw [←state.pc] at code charge
  exact prepared_typed_branch_state count tr 0 r pub (prepared_typed_exec_local codeCount count tr pub holds)
    nonlast active branch cfg eligible.setup.program s f fs sp root state eligible.func
    (by rw [fn];exact func) code charge bound enough

end NearCompression
