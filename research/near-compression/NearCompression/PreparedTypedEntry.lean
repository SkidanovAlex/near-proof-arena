import NearCompression.PreparedTypedBoundary
import NearCompression.PreparedTypedInitialization
import NearCompression.PreparedTypedEqzAuthenticated
import NearCompression.PreparedControlEntry
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2 NearSpecV3.Wasm
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
private theorem initial_source : ∀count:Fin 5,∀i:Fin 32,
    (preparedTypedLiteralExec count)[1583+66*(4-count.val)+i.val]?=
      some (Expr.mul .isFirst (.add (.col i.val false) (.neg (.const 0)))) := by decide
private theorem done_source : ∀count:Fin 5,(preparedTypedLiteralExec count)[1616+66*(4-count.val)]?=some preparedLocalsLiteralExec0995 := by decide
private theorem sp_source : ∀count:Fin 5,(preparedTypedLiteralExec count)[1615+66*(4-count.val)]?=some preparedLocalsLiteralExec0994 := by decide
private theorem label_source : ∀count:Fin 5,(preparedTypedLiteralExec count)[1617+66*(4-count.val)]?=some preparedLocalsLiteralExec0996 := by decide

theorem prepared_typed_initial (count localCount : Nat) (hc : localCount≤4) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedTypedLiteralAir count localCount) pub tr) :
    preparedCodeExecPC (tr.cell 0 0)=0 ∧ tr.cell 0 0 41=0 ∧ tr.cell 0 0 639=0 ∧
    ∀ i,i<9 → tr.cell 0 0 (32+i)=if i=0 then 1 else 0 := by
  have localH:=prepared_typed_exec_local count localCount tr pub holds
  have positive : 0<tr.height 0:=Nat.two_pow_pos _
  have source:=initial_source
  have bits (i : Nat) (hi : i<32) : tr.cell 0 0 i=0 := by
    have h:=localH.constr 0 positive _ (List.mem_of_getElem? (source ⟨localCount,by omega⟩ ⟨i,hi⟩))
    change (1:Fp)*(tr.cell 0 0 i+ -(0:Fp))=0 at h
    grind
  have limb (base : Nat) (hb : base+16≤32) : preparedCodeLimb (tr.cell 0 0) base=0 := by
    simp (disch:=omega) only [preparedCodeLimb,instructionBitExpr,Expr.evalWith,instructionAddEnv,bits]
    simp only [←Fp.ofNat_def]
    grind
  have pc : preparedCodeExecPC (tr.cell 0 0)=0 := by
    unfold preparedCodeExecPC
    rw [limb 0 (by decide),limb 16 (by decide)]
    rfl
  have done:=localH.constr 0 positive _ (List.mem_of_getElem? (done_source ⟨localCount,by omega⟩))
  change (1:Fp)*(tr.cell 0 0 41+ -(0:Fp))=0 at done
  have sp:=localH.constr 0 positive _ (List.mem_of_getElem? (sp_source ⟨localCount,by omega⟩))
  change (1:Fp)*(tr.cell 0 0 32+ -(1:Fp))=0 at sp
  have first : tr.cell 0 0 32=1:=by grind
  obtain ⟨selected,hs,hot⟩:=prepared_typed_source_sp localCount hc tr 0 0 pub localH positive
  have eq : selected=0 := by
    have h:=hot 0 (by decide)
    change tr.cell 0 0 32=(if 0=selected then 1 else 0) at h
    rw [first] at h
    by_cases z:0=selected
    · omega
    · simp only [z,ite_false] at h
      exact False.elim ((by decide : (1:Fp)≠0) h)
  have label:=localH.constr 0 positive _ (List.mem_of_getElem? (label_source ⟨localCount,by omega⟩))
  change (1:Fp)*(tr.cell 0 0 639+ -(0:Fp))=0 at label
  exact ⟨pc,by grind,by grind,by simpa only [eq] using hot⟩


/-- Actual entry semantics establish the complete locals state relation at
row zero from executable code and prologue checks. -/
theorem prepared_typed_enter (count localCount : Nat) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedTypedLiteralAir count localCount) pub tr)
    (p : Prepared) (fi : Nat) (pf : PFunc) (host : St)
    (fetch : p.funcs[fi-p.m.imports.size]?=some pf)
    (codeCheck : preparedTypedCodeCheck localCount pf (fi-p.m.imports.size) pub=true)
    (accepted : preparedExecEntryCheck p fi pf host pub=true) :
    enter p (preparedWasmHostReset host) fi=.cont (preparedWasmEntryState p fi pf host) ∧
    PreparedTypedState (tr.cell 0 0) (preparedWasmEntryState p fi pf host)
      (preparedWasmEntryFrame p fi pf) [] 0 localCount (preparedControlRootLabel pf) ∧
    PreparedWasmGasContext (preparedWasmEntryState p fi pf host) ∧ tr.cell 0 0 41=0 ∧
    (preparedWasmEntryFrame p fi pf).fn=0 := by
  have checks:=accepted
  simp only [preparedExecEntryCheck,Bool.and_eq_true,decide_eq_true_eq] at checks
  obtain ⟨counts,index,budget,bound,enough,promises,limit,spent,prepaid,gas⟩:=checks
  have shape:=prepared_typed_code_shape localCount pf _ pub codeCheck
  obtain ⟨pc,active,label,hot⟩:=prepared_typed_initial count localCount shape.2.1 tr pub holds
  have gasRow:=prepared_typed_boundary_gas count localCount tr pub holds counts false 0 (Nat.two_pow_pos _) rfl
  refine ⟨prepared_wasm_enter p fi pf host fetch budget bound enough,?_,
    prepared_wasm_entry_gas p fi pf host promises limit spent prepaid,active,?_⟩
  · refine ⟨by decide,hot,rfl,pc.symm,rfl,?_,shape.2.1,
      prepared_typed_entry_frame localCount pf _ pub codeCheck tr 0
        (prepared_typed_exec_local count localCount tr pub holds) p fi,Or.inl ⟨label,rfl⟩⟩
    change host.gas.remaining-pf.prologueGas=preparedExecWord64 (tr.cell 0 0) 299
    exact gas.symm.trans gasRow.symm
  · change fi-p.m.imports.size=0
    omega

/-- Entry with prepare/link/load/resolve provenance from the actual checker. -/
theorem prepared_typed_setup_enter (count localCount : Nat) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedTypedLiteralAir count localCount) pub tr)
    (cfg : NearCfg) (bytes : ByteArray) (method : String) (ctx : CallCtx) (blockLevel : Bool)
    (eligible : PreparedRunCallEligible)
    (setupCheck : preparedTypedSetupCheck localCount cfg bytes method ctx pub blockLevel=some eligible)
    (entryCheck : preparedExecEntryCheck eligible.setup.program eligible.setup.methodIndex eligible.func eligible.setup.host pub=true) :
    enter eligible.setup.program (preparedWasmHostReset eligible.setup.host) eligible.setup.methodIndex=
      .cont (preparedWasmEntryState eligible.setup.program eligible.setup.methodIndex eligible.func eligible.setup.host) ∧
    PreparedTypedState (tr.cell 0 0)
      (preparedWasmEntryState eligible.setup.program eligible.setup.methodIndex eligible.func eligible.setup.host)
      (preparedWasmEntryFrame eligible.setup.program eligible.setup.methodIndex eligible.func)
      [] 0 localCount (preparedControlRootLabel eligible.func) ∧
    PreparedWasmGasContext (preparedWasmEntryState eligible.setup.program eligible.setup.methodIndex eligible.func eligible.setup.host) ∧
    tr.cell 0 0 41=0 ∧
    (preparedWasmEntryFrame eligible.setup.program eligible.setup.methodIndex eligible.func).fn=0 := by
  obtain ⟨_,fetch,code⟩:=prepared_typed_setup_checked localCount cfg bytes method ctx pub blockLevel eligible setupCheck
  exact prepared_typed_enter count localCount tr pub holds eligible.setup.program eligible.setup.methodIndex
    eligible.func eligible.setup.host fetch code entryCheck
end NearCompression
