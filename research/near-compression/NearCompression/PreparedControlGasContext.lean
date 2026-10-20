import NearCompression.PreparedControlAuthenticated
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2 NearSpecV3.Wasm

private theorem setFrame_gas (s : St) (f : Frame) : (setFrame s f).gas=s.gas := by
  unfold setFrame
  split <;> rfl

private theorem popN_gas (s : St) : (popN s).2.gas=s.gas := by
  unfold popN popV
  split <;> grind

private theorem return_gas (p : Prepared) (s next : St) (run : doReturn p s=.cont next) : next.gas=s.gas := by
  unfold doReturn at run
  split at run
  · cases run
  · split at run
    · cases run
    · split at run
      · cases run
      · cases run;rfl

private theorem branch_gas (p : Prepared) (s next : St) (f : Frame) (l : Nat)
    (run : doBr p s f l=.cont next) : next.gas=s.gas := by
  unfold doBr at run
  split at run
  · exact return_gas p s next run
  · split at run
    · cases run
    · cases run;exact setFrame_gas _ _

/-- These supported instructions perform no host call and do not mutate gas
inside exec. The theorem covers actual interpreter branches, not an assumed
record-update witness. -/
theorem prepared_control_exec_gas (cfg : NearCfg) (p : Prepared) (s next : St)
    (f : Frame) (pf : PFunc) (op : PreparedControlInstruction)
    (run : exec cfg p s f pf op.instr=.cont next) : next.gas=s.gas := by
  cases op with
  | block =>
    simp only [PreparedControlInstruction.instr,exec] at run
    split at run
    · cases run
    · cases run;exact setFrame_gas _ _
  | brIf =>
    simp only [PreparedControlInstruction.instr,exec] at run
    split at run
    · exact (branch_gas p (popN s).2 next f 0 run).trans (popN_gas s)
    · cases run;rw [setFrame_gas,popN_gas]
  | legacy old =>
    cases old with
    | constant value =>
      simp only [PreparedControlInstruction.instr,PreparedPublicInstruction.instr,exec] at run
      cases run;exact setFrame_gas _ _
    | drop =>
      simp only [PreparedControlInstruction.instr,PreparedPublicInstruction.instr,exec] at run
      cases run;exact setFrame_gas _ _
    | end_ =>
      simp only [PreparedControlInstruction.instr,PreparedPublicInstruction.instr,exec] at run
      split at run
      · exact return_gas p s next run
      · exact return_gas p s next run
      · cases run;exact setFrame_gas _ _
    | add =>
      simp only [PreparedControlInstruction.instr,PreparedPublicInstruction.instr,exec,execNum,
        Nat.reduceLeDiff,Nat.reduceEqDiff,ite_false,ite_true,false_and,true_and,false_or,true_or,
        Nat.reduceSub,Num.binop] at run
      cases run
      rw [setFrame_gas]
      change (popN (popN s).2).2.gas=s.gas
      rw [popN_gas,popN_gas]

/-- Authenticated affordable continuation has exactly the actual deferred
charge update and preserves the no-host synchronization invariant. -/
theorem prepared_control_setup_continue_context (count : Nat) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedControlLiteralAir count) pub tr)
    (cfg : NearCfg) (bytes : ByteArray) (method : String) (ctx : CallCtx) (blockLevel : Bool)
    (eligible : PreparedRunCallEligible)
    (accepted : preparedControlSetupCheck cfg bytes method ctx pub blockLevel=some eligible)
    (r : Nat) (hr : r<tr.height 0)
    (s next : St) (f : Frame) (fs : List Frame) (sp : Nat)
    (state : PreparedExecState (tr.cell 0 r) s f fs sp)
    (fn : f.fn=eligible.setup.methodIndex-eligible.setup.program.m.imports.size)
    (enough : preparedExecWord64 (tr.cell 0 r) 502≤s.gas.g)
    (context : PreparedWasmGasContext s)
    (run : step cfg eligible.setup.program s=.cont next) :
    next.gas={s.gas with g:=s.gas.g-preparedExecWord64 (tr.cell 0 r) 502} ∧
    PreparedWasmGasContext next := by
  obtain ⟨setup,func,checked⟩:=prepared_control_setup_checked cfg bytes method ctx pub blockLevel eligible accepted
  obtain ⟨_,op,code,charge,bound,_,_⟩:=prepared_control_authenticated_decode count tr pub holds eligible.func _ checked r hr
  rw [←state.pc] at code charge
  have charged:=prepared_wasm_step_charge cfg eligible.setup.program s f fs eligible.func op.instr
    (preparedExecWord64 (tr.cell 0 r) 502) state.frames (by rw [fn];exact func) code charge bound enough
  rw [charged] at run
  have gas:=prepared_control_exec_gas cfg eligible.setup.program _ next f eligible.func op run
  refine ⟨gas,?_⟩
  unfold PreparedWasmGasContext
  rw [gas]
  rcases context with ⟨a,b,c,d,e⟩
  exact ⟨a,b,c,by change s.gas.g-_≤s.gas.prepaid-s.gas.burnt;omega,e⟩

end NearCompression
