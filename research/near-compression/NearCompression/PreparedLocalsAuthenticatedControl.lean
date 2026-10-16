import NearCompression.PreparedLocalsControlState
import NearCompression.PreparedLocalsControlDecode
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2 NearSpecV3.Wasm
set_option maxRecDepth 65536
theorem prepared_locals_setup_block_state (codeCount count : Nat) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedLocalsLiteralAir codeCount count) pub tr)
    (cfg : NearCfg) (bytes : ByteArray) (method : String) (ctx : CallCtx) (blockLevel : Bool)
    (eligible : PreparedRunCallEligible)
    (accepted : preparedLocalsSetupCheck count cfg bytes method ctx pub blockLevel=some eligible)
    (r : Nat) (nonlast : r+1<tr.height 0) (active : tr.cell 0 r 41=0) (block : tr.cell 0 r 605=1)
    (s : St) (f : Frame) (fs : List Frame) (sp : Nat) (root : Label)
    (state : PreparedLocalsState (tr.cell 0 r) s f fs sp count root)
    (fn : f.fn=eligible.setup.methodIndex-eligible.setup.program.m.imports.size)
    (enough : preparedExecWord64 (tr.cell 0 r) 502≤s.gas.g) :
    ∃ e s',eligible.func.endOf[f.pc]?=some e ∧
      step cfg eligible.setup.program s=.cont s' ∧
      PreparedLocalsState (tr.cell 0 (r+1)) s'
        {f with pc:=f.pc+1,labels:=[{target:=e+1,arity:=0,height:=sp,isLoop:=false},root]} fs sp count root ∧
      tr.cell 0 (r+1) 41=0 ∧ tr.cell 0 (r+1) 42=0 := by
  obtain ⟨setup,func,checked⟩:=prepared_locals_setup_checked count cfg bytes method ctx pub blockLevel eligible accepted
  obtain ⟨op,code,charge,bound,_,ops,_,target⟩:=prepared_locals_control_decode codeCount count tr pub holds eligible.func _ checked r (by omega) 4 (by decide) block
  have tag:=ops 4 (by decide)
  change tr.cell 0 r 605=(if 4=op.tag then 1 else 0) at tag
  rw [block] at tag
  have opEq : op=PreparedControlInstruction.block := by
    cases op with
    | block => rfl
    | brIf => exact False.elim ((by decide : (1:Fp)≠0) tag)
    | legacy old => cases old <;> exact False.elim ((by decide : (1:Fp)≠0) tag)
  subst op
  obtain ⟨e,endOf,targetEq⟩:=target rfl
  rw [←state.1.1.pc] at code charge endOf
  have run:=prepared_locals_block_state count tr 0 r pub (prepared_locals_exec_local codeCount count tr pub holds)
    nonlast active block cfg eligible.setup.program s f fs sp root state eligible.func
    (by rw [fn];exact func) code e _ endOf targetEq charge bound rfl enough
  obtain ⟨s',step,state',done,failed⟩:=run
  exact ⟨e,s',endOf,step,state',done,failed⟩

/-- Nested end with actual preparation and authenticated CODE provenance. -/
theorem prepared_locals_setup_nested_end_state (codeCount count : Nat) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedLocalsLiteralAir codeCount count) pub tr)
    (cfg : NearCfg) (bytes : ByteArray) (method : String) (ctx : CallCtx) (blockLevel : Bool)
    (eligible : PreparedRunCallEligible)
    (accepted : preparedLocalsSetupCheck count cfg bytes method ctx pub blockLevel=some eligible)
    (r : Nat) (nonlast : r+1<tr.height 0) (active : tr.cell 0 r 41=0)
    (endOp : tr.cell 0 r 469=1) (nested : tr.cell 0 r 639=1)
    (s : St) (f : Frame) (fs : List Frame) (sp : Nat) (root : Label)
    (state : PreparedLocalsState (tr.cell 0 r) s f fs sp count root)
    (fn : f.fn=eligible.setup.methodIndex-eligible.setup.program.m.imports.size)
    (enough : preparedExecWord64 (tr.cell 0 r) 502≤s.gas.g) :
    ∃ s',step cfg eligible.setup.program s=.cont s' ∧
      PreparedLocalsState (tr.cell 0 (r+1)) s'
        {f with pc:=f.pc+1,labels:=[root]} fs sp count root ∧
      tr.cell 0 (r+1) 41=0 ∧ tr.cell 0 (r+1) 42=0 := by
  obtain ⟨setup,func,checked⟩:=prepared_locals_setup_checked count cfg bytes method ctx pub blockLevel eligible accepted
  obtain ⟨op,code,charge,bound,_,ops,_,_⟩:=prepared_locals_control_decode codeCount count tr pub holds eligible.func _ checked r (by omega) 3 (by decide) endOp
  have tag:=ops 3 (by decide)
  change tr.cell 0 r 469=(if 3=op.tag then 1 else 0) at tag
  rw [endOp] at tag
  have opEq : op=PreparedControlInstruction.legacy .end_ := by
    cases op with
    | block => exact False.elim ((by decide : (1:Fp)≠0) tag)
    | brIf => exact False.elim ((by decide : (1:Fp)≠0) tag)
    | legacy old => cases old <;> first | rfl | exact False.elim ((by decide : (1:Fp)≠0) tag)
  subst op
  rw [←state.1.1.pc] at code charge
  exact prepared_locals_nested_end_state count tr 0 r pub (prepared_locals_exec_local codeCount count tr pub holds)
    nonlast active endOp nested cfg eligible.setup.program s f fs sp root state eligible.func
    (by rw [fn];exact func) code _ charge bound rfl enough

end NearCompression
