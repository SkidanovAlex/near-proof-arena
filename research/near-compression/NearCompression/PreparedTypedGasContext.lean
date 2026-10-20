import NearCompression.PreparedTypedEqzAuthenticated
import NearCompression.PreparedLocalsGasContext
import NearCompression.PreparedControlGasContext
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2 NearSpecV3.Wasm
private theorem setFrame_gas (s : St) (f : Frame) : (setFrame s f).gas=s.gas := by
  unfold setFrame
  split <;> rfl

private theorem popN_gas (s : St) : (popN s).2.gas=s.gas := by
  unfold popN popV
  split <;> grind

theorem prepared_typed_exec_gas (cfg : NearCfg) (p : Prepared) (s next : St)
    (f : Frame) (pf : PFunc) (op : PreparedTypedInstruction)
    (run : exec cfg p s f pf op.instr=.cont next) : next.gas=s.gas := by
  cases op with
  | control old => exact prepared_control_exec_gas cfg p s next f pf old run
  | «local» kind index =>
    cases kind <;> simp only [PreparedTypedInstruction.instr,PreparedLocalOp.instr,exec] at run
    all_goals cases run;exact setFrame_gas _ _
  | constant64 value=>
    simp only [PreparedTypedInstruction.instr,exec] at run
    cases run;exact setFrame_gas _ _
  | add64=>
    simp only [PreparedTypedInstruction.instr,exec,execNum,
      Nat.reduceLeDiff,Nat.reduceEqDiff,ite_false,ite_true,false_and,true_and,false_or,true_or,
      Nat.reduceSub,Num.binop] at run
    cases run
    rw [setFrame_gas]
    change (popN (popN s).2).2.gas=s.gas
    rw [popN_gas,popN_gas]
  | eqz64=>
    simp only [PreparedTypedInstruction.instr,exec,execNum,
      Nat.reduceLeDiff,Nat.reduceEqDiff,ite_false,ite_true,false_and,true_and,false_or,true_or] at run
    cases run
    rw [setFrame_gas]
    exact popN_gas s

theorem prepared_typed_setup_continue_context (codeCount count : Nat) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedTypedLiteralAir codeCount count) pub tr)
    (cfg : NearCfg) (bytes : ByteArray) (method : String) (ctx : CallCtx) (blockLevel : Bool)
    (eligible : PreparedRunCallEligible)
    (accepted : preparedTypedSetupCheck count cfg bytes method ctx pub blockLevel=some eligible)
    (r : Nat) (hr : r<tr.height 0)
    (s next : St) (f : Frame) (fs : List Frame) (sp : Nat) (root : Label)
    (state : PreparedTypedState (tr.cell 0 r) s f fs sp count root)
    (fn : f.fn=eligible.setup.methodIndex-eligible.setup.program.m.imports.size)
    (enough : preparedExecWord64 (tr.cell 0 r) 502≤s.gas.g)
    (context : PreparedWasmGasContext s)
    (run : step cfg eligible.setup.program s=.cont next) :
    next.gas={s.gas with g:=s.gas.g-preparedExecWord64 (tr.cell 0 r) 502} ∧
    PreparedWasmGasContext next := by
  obtain ⟨setup,func,checked⟩:=prepared_typed_setup_checked count cfg bytes method ctx pub blockLevel eligible accepted
  obtain ⟨_,op,fee,amount,target,code,_,_,_,_,_,_,_⟩:=prepared_typed_authenticated_fetch codeCount count tr pub holds eligible.func _ checked r hr
  obtain ⟨_,charge,bound⟩:=prepared_typed_authenticated_fee codeCount count tr pub holds eligible.func _ checked r hr
  rw [←state.pc] at code charge
  have charged:=prepared_wasm_step_charge cfg eligible.setup.program s f fs eligible.func op.instr
    (preparedExecWord64 (tr.cell 0 r) 502) state.frames (by rw [fn];exact func) code charge bound enough
  rw [charged] at run
  have gas:=prepared_typed_exec_gas cfg eligible.setup.program _ next f eligible.func op run
  refine ⟨gas,?_⟩
  unfold PreparedWasmGasContext
  rw [gas]
  rcases context with ⟨a,b,c,d,e⟩
  exact ⟨a,b,c,by change s.gas.g-_≤s.gas.prepaid-s.gas.burnt;omega,e⟩

end NearCompression
