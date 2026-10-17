import NearCompression.PreparedLocalsPublicOutput
import NearCompression.PreparedLocalsRunCall
import NearCompression.PreparedLocalsFrameStack
set_option maxRecDepth 65536
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near NearSpecV3.Wasm

/-- The constructed control terminal witness matches its first DONE row.
Successful termination must be a root end, not a nested-end continuation. -/
theorem prepared_locals_witness_final_row (codeCount count : Nat) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedLocalsLiteralAir codeCount count) pub tr)
    (pf : PFunc) (fn : Nat) (checked : preparedLocalsCodeCheck count pf fn pub=true)
    (cfg : NearCfg) (p : Prepared) (root : Label) (w : PreparedLocalsTerminalWitness cfg p tr pf count root) :
    PreparedExecFinalRow (tr.cell 0 (w.row+1)) w.final w.error := by
  have localH:=prepared_locals_exec_local codeCount count tr pub holds
  have hr : w.row<tr.height 0 := by have h:=w.nonlast;omega
  obtain ⟨_,charge,bound⟩:=prepared_locals_authenticated_fee codeCount count tr pub holds pf fn checked w.row hr
  rw [←w.state.1.1.pc] at charge
  by_cases enough : preparedExecWord64 (tr.cell 0 w.row) 502≤w.before.gas.g
  · have enoughRow : preparedExecWord64 (tr.cell 0 w.row) 502≤preparedExecWord64 (tr.cell 0 w.row) 299 := by
      rw [←w.state.1.1.gas];exact enough
    obtain ⟨borrow,gasNext⟩:=prepared_control_gas_success _ tr 0 w.row pub (prepared_locals_gas_source count) localH w.nonlast w.active enoughRow
    have flags:=prepared_locals_terminal_flags count tr 0 w.row pub localH w.nonlast w.active
    have flagEq := flags.2.2
    rw [w.done,w.active,borrow] at flagEq
    have notZero : tr.cell 0 w.row 469≠0 := by
      intro z;rw [z] at flagEq
      have impossible : (1:Fp)=0:=by grind
      exact (by decide : (1:Fp)≠0) impossible
    have endBound:=prepared_locals_bits_boolean count tr 0 w.row pub localH hr 469 (by decide) (by decide)
    have isEnd : tr.cell 0 w.row 469=1 := by
      apply Fp.ext
      have nonzero : (tr.cell 0 w.row 469).toNat≠0 := by
        intro eq;apply notZero;apply Fp.ext;exact eq
      change (tr.cell 0 w.row 469).toNat=1
      omega
    have absent : tr.cell 0 w.row 639=0 := by rw [isEnd] at flagEq;grind
    obtain ⟨op,code,_,_,_,ops,_,_⟩:=prepared_locals_control_decode codeCount count tr pub holds pf fn checked w.row hr 3 (by decide) isEnd
    rw [←w.state.1.1.pc] at code
    have tag:=ops 3 (by decide)
    change tr.cell 0 w.row 469=(if 3=op.tag then 1 else 0) at tag
    rw [isEnd] at tag
    have opEq : op=PreparedControlInstruction.legacy .end_ := by
      cases op with
      | block => exact False.elim ((by decide : (1:Fp)≠0) tag)
      | brIf => exact False.elim ((by decide : (1:Fp)≠0) tag)
      | legacy old => cases old <;> first | rfl | exact False.elim ((by decide : (1:Fp)≠0) tag)
    subst op
    have stackQuiet:=prepared_locals_frame_stack count tr 0 w.row pub localH w.nonlast 3 (Or.inl rfl) isEnd
    obtain ⟨sp,hs,selected,nextSelected⟩:=prepared_locals_frame_sp count tr 0 w.row pub localH w.nonlast 3 (Or.inl rfl) isEnd
    have spQuiet (i : Nat) (hi : i<9) : tr.cell 0 (w.row+1) (32+i)=tr.cell 0 w.row (32+i) := by rw [selected i hi,nextSelected i hi]
    have empty:=prepared_locals_root_end_depth count tr 0 w.row pub localH hr w.active borrow isEnd absent w.sp w.state.1.1.depth w.state.1.1.selected
    have labels : w.frame.labels=[root] := by
      rcases w.state.1.2 with h|⟨_,_,one,_,_⟩
      · exact h.2
      · rw [absent] at one
        exact False.elim ((by decide : (0:Fp)≠1) one)
    have emptyStack : w.before.stack=#[] := by rw [w.state.1.1.stack,empty];rfl
    have actual:=prepared_wasm_end cfg p w.before w.frame pf (preparedExecWord64 (tr.cell 0 w.row) 502)
      w.state.1.1.frames w.func code (Or.inr ⟨root,labels⟩) emptyStack charge bound enough
    have terminal:=w.terminal
    rw [actual] at terminal
    cases errorEq:w.error with
    | some error => simp only [errorEq] at terminal;cases terminal
    | none =>
      simp only [errorEq] at terminal
      have rawEq:=Res.fin.inj terminal
      have syncEq:=w.synced
      rw [←rawEq,prepared_wasm_end_sync w.before pf _ w.context] at syncEq
      have finalEq:=Except.ok.inj syncEq
      refine ⟨w.done,(by simpa only [errorEq] using w.failed),?_,0,by decide,?_,?_⟩
      · have fast:=congrArg (fun s:St=>s.gas.g) finalEq
        change w.before.gas.g-preparedExecWord64 (tr.cell 0 w.row) 502=w.final.gas.g at fast
        exact fast.symm.trans (by rw [gasNext,←w.state.1.1.gas])
      · intro i hi
        rw [spQuiet i hi]
        simpa only [empty] using w.state.1.1.selected i hi
      · exact (congrArg (fun s:St=>s.stack) finalEq).symm
  · have insufficient : w.before.gas.g<preparedExecWord64 (tr.cell 0 w.row) 502:=by omega
    have rowInsufficient : preparedExecWord64 (tr.cell 0 w.row) 299<preparedExecWord64 (tr.cell 0 w.row) 502 := by
      rw [←w.state.1.1.gas];exact insufficient
    obtain ⟨borrow,frozen⟩:=prepared_control_gas_exhaustion _ tr 0 w.row pub (prepared_locals_gas_source count) localH w.nonlast rowInsufficient
    have success : preparedExecGasSuccess.eval tr 0 w.row pub=0 := by
      change _*((1:Fp)+ -tr.cell 0 w.row 430)=0
      rw [borrow];grind
    have quiet:=prepared_locals_quiet count tr 0 w.row pub localH w.nonlast success
    have spQuiet:=quiet.2.1
    obtain ⟨_,op,fee,amount,target,code,_,_,_,_,_,_,_⟩:=prepared_locals_authenticated_fetch codeCount count tr pub holds pf fn checked w.row hr
    rw [←w.state.1.1.pc] at code
    have actual:=prepared_wasm_exhaustion_trap cfg p w.before w.frame [] pf op.instr (preparedExecWord64 (tr.cell 0 w.row) 502)
      w.state.1.1.frames w.func code charge bound insufficient w.context
    have terminal:=w.terminal
    rw [actual] at terminal
    cases errorEq:w.error with
    | none => simp only [errorEq] at terminal;cases terminal
    | some error =>
      simp only [errorEq] at terminal
      have rawEq:=(Res.abort.inj terminal).1
      have syncEq:=w.synced
      rw [←rawEq,prepared_wasm_failure_sync w.before _ w.context] at syncEq
      have finalEq:=Except.ok.inj syncEq
      refine ⟨w.done,(by simpa only [errorEq] using w.failed),?_,w.sp,w.state.1.1.depth,?_,?_⟩
      · have fast:=congrArg (fun s:St=>s.gas.g) finalEq
        have retained : (preparedWasmFailureGas w.before (preparedExecWord64 (tr.cell 0 w.row) 502)).g=w.before.gas.g := by
          unfold preparedWasmFailureGas
          dsimp only
          split <;> rfl
        exact fast.symm.trans (retained.trans (w.state.1.1.gas.trans frozen.symm))
      · intro i hi;rw [spQuiet i hi];exact w.state.1.1.selected i hi
      · have stackEq : w.final.stack=w.before.stack := (congrArg (fun s:St=>s.stack) finalEq).symm
        rw [stackEq,w.state.1.1.stack]
        apply prepared_wasm_stack_congr
        intro i hi
        exact (quiet.2.2 i (by have h:=w.state.1.1.depth;omega)).symm

theorem prepared_locals_witness_published (codeCount count : Nat) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedLocalsLiteralAir codeCount count) pub tr) (counts : preparedExecBoundaryCountsCheck pub=true)
    (pf : PFunc) (fn : Nat) (checked : preparedLocalsCodeCheck count pf fn pub=true)
    (cfg : NearCfg) (p : Prepared) (root : Label) (w : PreparedLocalsTerminalWitness cfg p tr pf count root) :
    PreparedExecPublishedOutput pub w.final w.error := by
  exact prepared_locals_terminal_published codeCount count tr pub holds counts (w.row+1) w.nonlast w.final w.error
    (prepared_locals_witness_final_row codeCount count tr pub holds pf fn checked cfg p root w)

/-- Actual outer runCall and its authenticated public exit status, fast gas
and live i32 stack. Preparation remains an executable verifier-side check;
this is a single-function stack8/locals4/one-nested-void-block slice, not full Wasm. -/
theorem prepared_locals_public_run_call (codeCount count : Nat) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedLocalsLiteralAir codeCount count) pub tr)
    (cfg : NearCfg) (code : ByteArray) (method : String) (ctx : CallCtx)
    (blockLevel full : Bool) (eligible : PreparedRunCallEligible)
    (accepted : preparedLocalsRunCallCheck count cfg code method ctx pub blockLevel=some eligible)
    (fuel : Nat) (enoughFuel : tr.height 0≤fuel) :
    ∃ witness:PreparedLocalsTerminalWitness cfg eligible.setup.program tr eligible.func count (preparedControlRootLabel eligible.func),
      runCall cfg code method ctx fuel blockLevel full none=.done witness.final witness.error ∧
      PreparedExecPublishedOutput pub witness.final witness.error := by
  obtain ⟨codeCheck,entry⟩:=prepared_locals_run_call_checked count cfg code method ctx pub blockLevel eligible accepted
  obtain ⟨setup,fetch,checked⟩:=prepared_locals_setup_checked count cfg code method ctx pub blockLevel eligible codeCheck
  have counts : preparedExecBoundaryCountsCheck pub=true := by
    simp only [preparedExecEntryCheck,Bool.and_eq_true] at entry
    exact entry.1
  obtain ⟨w,actual⟩:=prepared_locals_run_call codeCount count tr pub holds cfg code method ctx blockLevel full eligible accepted fuel enoughFuel
  exact ⟨w,actual,prepared_locals_witness_published codeCount count tr pub holds counts eligible.func _ checked
    cfg eligible.setup.program (preparedControlRootLabel eligible.func) w⟩

end NearCompression
