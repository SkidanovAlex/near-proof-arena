import NearCompression.PreparedExecPublicOutput

set_option maxRecDepth 65536
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near NearSpecV3.Wasm

/-- The terminal witness produced by the literal execution induction binds
its actual synchronized interpreter result to the first DONE row. -/
theorem prepared_literal_witness_final_row (count : Nat) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedLiteralAir count) pub tr)
    (pf : PFunc) (fn : Nat) (checked : preparedCodeVariableCheck pf fn pub=true)
    (cfg : NearCfg) (p : Prepared) (w : PreparedExecTerminalWitness cfg p tr pf) :
    PreparedExecFinalRow (tr.cell 0 (w.row+1)) w.final w.error := by
  have localH:=prepared_exec_table_local _ _ _ count tr pub holds
  have hr : w.row<tr.height 0 := by have h:=w.nonlast;omega
  obtain ⟨op,code,ops⟩:=prepared_exec_authenticated_opcode _ _ _ count tr pub holds
    prepared_literal_code_order prepared_literal_code_inactive pf fn checked w.row hr
  by_cases enough : preparedExecWord64 (tr.cell 0 w.row) 502≤w.before.gas.g
  · have enoughRow : preparedExecWord64 (tr.cell 0 w.row) 502≤preparedExecWord64 (tr.cell 0 w.row) 299 := by
      rw [←w.state.gas];exact enough
    obtain ⟨borrow,gasNext⟩:=prepared_exec_gas_success _ tr 0 w.row pub prepared_literal_exec_gas localH
      w.nonlast w.active enoughRow
    have endTag : op.tag=3 := by
      by_cases notEnd : op.tag=3
      · exact notEnd
      · exfalso
        have tag:=ops 3 (by decide)
        have zero : tr.cell 0 w.row 469=0 := by simpa only [show ¬3=op.tag by omega,ite_false] using tag
        have flags:=prepared_exec_success_flags _ tr 0 w.row pub localH w.nonlast prepared_literal_exec_closure
          w.active borrow zero
        have impossible : (1:Fp)=0:=w.done.symm.trans flags.2.1
        exact (by decide : (1:Fp)≠0) impossible
    have isEnd : tr.cell 0 w.row 469=1 := by simpa only [endTag,ite_true] using ops 3 (by decide)
    have zeros : ∀ i,i<3 → tr.cell 0 w.row (466+i)=0 := by
      intro i hi
      simpa only [endTag,show ¬i=3 by omega,ite_false] using ops i (by omega)
    have advance : preparedExecPCAdvance.eval tr 0 w.row pub=0 := by
      change _*((1:Fp)+ -tr.cell 0 w.row 469)=0
      rw [isEnd];grind
    have quiet:=prepared_exec_quiet _ tr 0 w.row pub localH w.nonlast prepared_literal_exec_closure
      prepared_literal_exec_pc advance (by intro i hi;rw [zeros i hi];grind)
    obtain ⟨empty,actual,done,failed⟩:=prepared_exec_authenticated_end _ _ _ count tr pub holds
      prepared_literal_code_order prepared_literal_code_inactive prepared_literal_exec_closure
      prepared_literal_exec_gas prepared_literal_exec_end_guard pf fn checked w.row w.nonlast w.active isEnd
      cfg p w.before w.frame w.sp w.state w.func w.labels enough
    have terminal:=w.terminal
    rw [actual] at terminal
    cases errorEq:w.error with
    | some error => simp only [errorEq] at terminal;cases terminal
    | none =>
      simp only [errorEq] at terminal
      have rawEq:=Res.fin.inj terminal
      have syncEq:=w.synced
      rw [←rawEq] at syncEq
      have syncActual:=prepared_wasm_end_sync w.before pf (preparedExecWord64 (tr.cell 0 w.row) 502) w.context
      rw [gasNext,←w.state.gas] at syncEq
      rw [syncActual] at syncEq
      have finalEq:=Except.ok.inj syncEq
      refine ⟨done,?_,?_,0,by decide,?_,?_⟩
      · simpa only [errorEq,Option.isSome,Bool.false_eq_true,ite_false,ite_true] using failed
      · have fast:=congrArg (fun s:St=>s.gas.g) finalEq
        change w.before.gas.g-preparedExecWord64 (tr.cell 0 w.row) 502=w.final.gas.g at fast
        exact fast.symm.trans (by rw [gasNext,←w.state.gas])
      · intro i hi
        rw [quiet.2.1 i hi]
        simpa only [empty] using w.state.selected i hi
      · exact (congrArg (fun s:St=>s.stack) finalEq).symm
  · have insufficient : w.before.gas.g<preparedExecWord64 (tr.cell 0 w.row) 502:=by omega
    have rowInsufficient : preparedExecWord64 (tr.cell 0 w.row) 299<preparedExecWord64 (tr.cell 0 w.row) 502 := by
      rw [←w.state.gas];exact insufficient
    obtain ⟨borrow,frozen⟩:=prepared_exec_gas_exhaustion _ tr 0 w.row pub prepared_literal_exec_gas localH
      w.nonlast rowInsufficient
    have success : preparedExecGasSuccess.eval tr 0 w.row pub=0 := by
      change _*((1:Fp)+ -tr.cell 0 w.row 430)=0
      rw [borrow];grind
    have advance : preparedExecPCAdvance.eval tr 0 w.row pub=0 := by
      change preparedExecGasSuccess.eval tr 0 w.row pub*_=0
      rw [success];grind
    have quiet:=prepared_exec_quiet _ tr 0 w.row pub localH w.nonlast prepared_literal_exec_closure
      prepared_literal_exec_pc advance (by intro i hi;rw [success];grind)
    obtain ⟨actual,done,failed,gasNext⟩:=prepared_exec_authenticated_exhaustion _ _ _ count tr pub holds
      prepared_literal_code_order prepared_literal_code_inactive prepared_literal_exec_closure
      prepared_literal_exec_gas pf fn checked w.row w.nonlast w.active cfg p w.before w.frame [] w.sp
      w.state w.func w.context insufficient
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
      refine ⟨done,?_,?_,w.sp,w.state.depth,?_,?_⟩
      · simpa only [errorEq,Option.isSome,Bool.false_eq_true,ite_false,ite_true] using failed
      · have fast:=congrArg (fun s:St=>s.gas.g) finalEq
        have retained : (preparedWasmFailureGas w.before (preparedExecWord64 (tr.cell 0 w.row) 502)).g=w.before.gas.g := by
          unfold preparedWasmFailureGas
          dsimp only
          split <;> rfl
        exact fast.symm.trans (retained.trans gasNext.symm)
      · intro i hi;rw [quiet.2.1 i hi];exact w.state.selected i hi
      · have stackEq : w.final.stack=w.before.stack := (congrArg (fun s:St=>s.stack) finalEq).symm
        rw [stackEq,w.state.stack]
        apply prepared_wasm_stack_congr
        intro i hi
        exact (quiet.2.2 i (by have h:=w.state.depth;omega)).symm

/-- Full published exit binding follows from the source-constructed terminal
witness, without a caller-supplied final-row relation. -/
theorem prepared_literal_witness_published (count : Nat) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedLiteralAir count) pub tr) (counts : preparedExecBoundaryCountsCheck pub=true)
    (pf : PFunc) (fn : Nat) (checked : preparedCodeVariableCheck pf fn pub=true)
    (cfg : NearCfg) (p : Prepared) (w : PreparedExecTerminalWitness cfg p tr pf) :
    PreparedExecPublishedOutput pub w.final w.error := by
  exact prepared_literal_terminal_published count tr pub holds counts (w.row+1) w.nonlast w.final w.error
    (prepared_literal_witness_final_row count tr pub holds pf fn checked cfg p w)

/-- Actual outer runCall equals the authenticated public terminal status,
fast gas, and live i32 stack. Preparation remains an executable verifier-side
check, with one straight-line function and at most eight live stack values. -/
theorem prepared_literal_public_run_call (count : Nat) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedLiteralAir count) pub tr)
    (cfg : NearCfg) (code : ByteArray) (method : String) (ctx : CallCtx)
    (blockLevel full : Bool) (eligible : PreparedRunCallEligible)
    (accepted : preparedLiteralRunCallCheck cfg code method ctx pub blockLevel=some eligible)
    (fuel : Nat) (enoughFuel : tr.height 0≤fuel) :
    ∃ witness:PreparedExecTerminalWitness cfg eligible.setup.program tr eligible.func,
      runCall cfg code method ctx fuel blockLevel full none=.done witness.final witness.error ∧
      PreparedExecPublishedOutput pub witness.final witness.error := by
  obtain ⟨codeCheck,entry⟩:=prepared_literal_run_call_checked cfg code method ctx pub blockLevel eligible accepted
  obtain ⟨setup,fetch,checked⟩:=prepared_code_prepared_checked cfg code method ctx pub blockLevel eligible codeCheck
  have counts : preparedExecBoundaryCountsCheck pub=true := by
    simp only [preparedExecEntryCheck,Bool.and_eq_true] at entry
    exact entry.1
  obtain ⟨w,actual⟩:=prepared_literal_run_call count tr pub holds cfg code method ctx blockLevel full eligible accepted fuel enoughFuel
  exact ⟨w,actual,prepared_literal_witness_published count tr pub holds counts eligible.func _ checked cfg eligible.setup.program w⟩

end NearCompression
