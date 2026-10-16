import NearCompression.PreparedControlBoundary
import NearCompression.PreparedControlRun

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2 NearSpecV3.Wasm
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

def preparedControlRootLabel (pf : PFunc) : Label :=
  {target:=pf.code.size,arity:=pf.type.results.size,height:=0,isLoop:=false}

private theorem initial_source : ∀ i:Fin 32,preparedControlLiteralExec[688+i.val]'(by change _<870;omega)=
      Expr.mul .isFirst (.add (.col i.val false) (.neg (.const 0))) := by decide

theorem prepared_control_initial (count : Nat) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedControlLiteralAir count) pub tr) :
    preparedCodeExecPC (tr.cell 0 0)=0 ∧ tr.cell 0 0 41=0 ∧ tr.cell 0 0 639=0 ∧
    ∀ i,i<9 → tr.cell 0 0 (32+i)=if i=0 then 1 else 0 := by
  have localH:=prepared_control_exec_local count tr pub holds
  have positive : 0<tr.height 0:=Nat.two_pow_pos _
  have source:=initial_source
  have bits (i : Nat) (hi : i<32) : tr.cell 0 0 i=0 := by
    have member:=List.getElem_mem (l:=preparedControlLiteralExec) (n:=688+i) (by change _<870;omega)
    rw [source ⟨i,hi⟩] at member
    have h:=localH.constr 0 positive _ member
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
  have doneMember : preparedControlLiteralExec0721∈preparedControlLiteralExec :=
    List.getElem_mem (l:=preparedControlLiteralExec) (n:=721) (by decide)
  have done:=localH.constr 0 positive _ doneMember
  change (1:Fp)*(tr.cell 0 0 41+ -(0:Fp))=0 at done
  have spMember : preparedControlLiteralExec0720∈preparedControlLiteralExec :=
    List.getElem_mem (l:=preparedControlLiteralExec) (n:=720) (by decide)
  have sp:=localH.constr 0 positive _ spMember
  change (1:Fp)*(tr.cell 0 0 32+ -(1:Fp))=0 at sp
  have first : tr.cell 0 0 32=1:=by grind
  obtain ⟨selected,hs,hot⟩:=prepared_control_literal_onehot tr 0 0 pub localH positive
  have eq : selected=0 := by
    have h:=hot 0 (by decide)
    change tr.cell 0 0 32=(if 0=selected then 1 else 0) at h
    rw [first] at h
    by_cases z:0=selected
    · omega
    · simp only [z,ite_false] at h
      exact False.elim ((by decide : (1:Fp)≠0) h)
  have label:=localH.constr 0 positive preparedControlLiteralExec0722
    (List.getElem_mem (l:=preparedControlLiteralExec) (n:=722) (by decide))
  change (1:Fp)*(tr.cell 0 0 639+ -(0:Fp))=0 at label
  exact ⟨pc,by grind,by grind,by simpa only [eq] using hot⟩

/-- Executable header/prologue checks and actual entry semantics establish
row0's real-state relation. The profile selects defined function zero. -/
theorem prepared_control_enter (count : Nat) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedControlLiteralAir count) pub tr)
    (p : Prepared) (fi : Nat) (pf : PFunc) (host : St)
    (fetch : p.funcs[fi-p.m.imports.size]?=some pf)
    (accepted : preparedExecEntryCheck p fi pf host pub=true) :
    enter p (preparedWasmHostReset host) fi=.cont (preparedWasmEntryState p fi pf host) ∧
    PreparedControlState (tr.cell 0 0) (preparedWasmEntryState p fi pf host)
      (preparedWasmEntryFrame p fi pf) [] 0 (preparedControlRootLabel pf) ∧
    PreparedWasmGasContext (preparedWasmEntryState p fi pf host) ∧ tr.cell 0 0 41=0 ∧
    (preparedWasmEntryFrame p fi pf).fn=0 := by
  have checks:=accepted
  simp only [preparedExecEntryCheck,Bool.and_eq_true,decide_eq_true_eq] at checks
  obtain ⟨counts,index,budget,bound,enough,promises,limit,spent,prepaid,gas⟩:=checks
  obtain ⟨pc,active,label,hot⟩:=prepared_control_initial count tr pub holds
  have gasRow:=prepared_control_boundary_gas count tr pub holds counts false 0 (Nat.two_pow_pos _) rfl
  refine ⟨prepared_wasm_enter p fi pf host fetch budget bound enough,?_,
    prepared_wasm_entry_gas p fi pf host promises limit spent prepaid,active,?_⟩
  · refine ⟨⟨by decide,hot,rfl,pc.symm,rfl,?_⟩,Or.inl ⟨label,rfl⟩⟩
    change host.gas.remaining-pf.prologueGas=preparedExecWord64 (tr.cell 0 0) 299
    exact gas.symm.trans gasRow.symm
  · change fi-p.m.imports.size=0
    omega


/-- Actual callEntry from real setup and public entry-gas checking. No
initial state relation or initial gas equality is supplied by the caller. -/
theorem prepared_control_call_entry (count : Nat) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedControlLiteralAir count) pub tr)
    (cfg : NearCfg) (bytes : ByteArray) (method : String) (ctx : CallCtx) (blockLevel : Bool)
    (eligible : PreparedRunCallEligible)
    (accepted : preparedControlSetupCheck cfg bytes method ctx pub blockLevel=some eligible)
    (entryCheck : preparedExecEntryCheck eligible.setup.program eligible.setup.methodIndex eligible.func eligible.setup.host pub=true)
    (fuel : Nat) (enoughFuel : tr.height 0≤fuel) :
    ∃ witness:PreparedControlTerminalWitness cfg eligible.setup.program tr eligible.func (preparedControlRootLabel eligible.func),
      callEntry cfg eligible.setup.program fuel eligible.setup.host eligible.setup.methodIndex=.ok (witness.final,witness.error) := by
  obtain ⟨_,fetch,_⟩:=prepared_control_setup_checked cfg bytes method ctx pub blockLevel eligible accepted
  obtain ⟨entry,state,context,active,_⟩:=prepared_control_enter count tr pub holds eligible.setup.program
    eligible.setup.methodIndex eligible.func eligible.setup.host fetch entryCheck
  obtain ⟨witness,_,executed⟩:=prepared_control_execution_run count tr pub holds cfg bytes method ctx blockLevel eligible accepted
    fuel 0 (preparedWasmEntryState eligible.setup.program eligible.setup.methodIndex eligible.func eligible.setup.host)
    (preparedWasmEntryFrame eligible.setup.program eligible.setup.methodIndex eligible.func) 0
    (preparedControlRootLabel eligible.func) (Nat.two_pow_pos _) (by simpa using enoughFuel) active state rfl context
  refine ⟨witness,?_⟩
  change (match (match enter eligible.setup.program (preparedWasmHostReset eligible.setup.host) eligible.setup.methodIndex with
    | .cont s=>run cfg eligible.setup.program fuel s | r=>r) with
    | .fin s=>(sync s).map (·,none)
    | .abort s e=>(sync s).map (·,some e)
    | .unmodeled why=>.error why
    | .cont _=>.error "cont")=_
  simp only [entry]
  rw [executed]
  unfold PreparedControlTerminalWitness.result
  cases err:witness.error <;> simp only [witness.synced,Except.map]

end NearCompression
