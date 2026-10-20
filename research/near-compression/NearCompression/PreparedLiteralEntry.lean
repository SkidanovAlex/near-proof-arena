import NearCompression.PreparedExecBoundary
import NearCompression.PreparedLiteralRun

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2 NearSpecV3.Wasm
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

def preparedExecEntryCheck (p : Prepared) (fi : Nat) (pf : PFunc) (host : St) (pub : List Fp) : Bool :=
  preparedExecBoundaryCountsCheck pub && decide (
    fi=p.m.imports.size ∧ pf.stackCharge≤host.stackRem ∧ pf.prologueGas<u64Bound ∧
    pf.prologueGas≤host.gas.remaining ∧ host.gas.promises=0 ∧ host.gas.limit=host.gas.prepaid ∧
    host.gas.burnt≤host.gas.prepaid ∧ host.gas.prepaid≤maxGasBurnt ∧
    preparedExecPublicGas pub false=host.gas.remaining-pf.prologueGas)

private theorem initial_source : ∀ i:Fin 32,preparedLiteralExec[608+i.val]'(by change _<726;omega)=
      Expr.mul .isFirst (.add (.col i.val false) (.neg (.const 0))) := by decide

theorem prepared_literal_initial (count : Nat) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedLiteralAir count) pub tr) :
    preparedCodeExecPC (tr.cell 0 0)=0 ∧ tr.cell 0 0 41=0 ∧
    ∀ i,i<9 → tr.cell 0 0 (32+i)=if i=0 then 1 else 0 := by
  have localH:=prepared_exec_table_local _ _ _ count tr pub holds
  have positive : 0<tr.height 0:=Nat.two_pow_pos _
  have source:=initial_source
  have bits (i : Nat) (hi : i<32) : tr.cell 0 0 i=0 := by
    have member:=List.getElem_mem (l:=preparedLiteralExec) (n:=608+i) (by change _<726;omega)
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
  have doneMember : preparedLiteralExec0641∈preparedLiteralExec :=
    List.getElem_mem (l:=preparedLiteralExec) (n:=641) (by decide)
  have done:=localH.constr 0 positive _ doneMember
  change (1:Fp)*(tr.cell 0 0 41+ -(0:Fp))=0 at done
  have spMember : preparedLiteralExec0640∈preparedLiteralExec :=
    List.getElem_mem (l:=preparedLiteralExec) (n:=640) (by decide)
  have sp:=localH.constr 0 positive _ spMember
  change (1:Fp)*(tr.cell 0 0 32+ -(1:Fp))=0 at sp
  have first : tr.cell 0 0 32=1:=by grind
  obtain ⟨selected,hs,hot⟩:=prepared_exec_sp_onehot _ tr 0 0 pub localH positive prepared_literal_exec_closure
  have eq : selected=0 := by
    have h:=hot 0 (by decide)
    change tr.cell 0 0 32=(if 0=selected then 1 else 0) at h
    rw [first] at h
    by_cases z:0=selected
    · omega
    · simp only [z,ite_false] at h
      exact False.elim ((by decide : (1:Fp)≠0) h)
  exact ⟨pc,by grind,by simpa only [eq] using hot⟩

/-- Executable header/prologue checks and actual entry semantics establish
row0's real-state relation. The profile selects defined function zero. -/
theorem prepared_literal_enter (count : Nat) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedLiteralAir count) pub tr)
    (p : Prepared) (fi : Nat) (pf : PFunc) (host : St)
    (fetch : p.funcs[fi-p.m.imports.size]?=some pf)
    (accepted : preparedExecEntryCheck p fi pf host pub=true) :
    enter p (preparedWasmHostReset host) fi=.cont (preparedWasmEntryState p fi pf host) ∧
    PreparedExecState (tr.cell 0 0) (preparedWasmEntryState p fi pf host)
      (preparedWasmEntryFrame p fi pf) [] 0 ∧
    PreparedWasmGasContext (preparedWasmEntryState p fi pf host) ∧ tr.cell 0 0 41=0 ∧
    (preparedWasmEntryFrame p fi pf).fn=0 := by
  have checks:=accepted
  simp only [preparedExecEntryCheck,Bool.and_eq_true,decide_eq_true_eq] at checks
  obtain ⟨counts,index,budget,bound,enough,promises,limit,spent,prepaid,gas⟩:=checks
  obtain ⟨pc,active,hot⟩:=prepared_literal_initial count tr pub holds
  have gasRow:=prepared_literal_boundary_gas count tr pub holds counts false 0 (Nat.two_pow_pos _) rfl
  refine ⟨prepared_wasm_enter p fi pf host fetch budget bound enough,?_,
    prepared_wasm_entry_gas p fi pf host promises limit spent prepaid,active,?_⟩
  · refine ⟨by decide,hot,rfl,pc.symm,rfl,?_⟩
    change host.gas.remaining-pf.prologueGas=preparedExecWord64 (tr.cell 0 0) 299
    exact gas.symm.trans gasRow.symm
  · change fi-p.m.imports.size=0
    omega

/-- Actual callEntry, including prepared prologue and exit synchronization;
no supplied execution certificate or initial-row gas equation. -/
theorem prepared_literal_call_entry (count : Nat) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedLiteralAir count) pub tr)
    (cfg : NearCfg) (p : Prepared) (fi : Nat) (pf : PFunc) (host : St)
    (fetch : p.funcs[fi-p.m.imports.size]?=some pf)
    (checked : preparedCodeVariableCheck pf (fi-p.m.imports.size) pub=true)
    (accepted : preparedExecEntryCheck p fi pf host pub=true)
    (fuel : Nat) (enoughFuel : tr.height 0≤fuel) :
    ∃ witness:PreparedExecTerminalWitness cfg p tr pf,
      callEntry cfg p fuel host fi=.ok (witness.final,witness.error) := by
  obtain ⟨entry,state,context,active,_⟩:=prepared_literal_enter count tr pub holds p fi pf host fetch accepted
  obtain ⟨witness,_,executed⟩:=prepared_literal_execution_run count tr pub holds pf _ checked cfg p fuel 0
    (preparedWasmEntryState p fi pf host) (preparedWasmEntryFrame p fi pf) 0
    (Nat.two_pow_pos _) (by simpa using enoughFuel) active state fetch context
    (Or.inr ⟨_,rfl⟩)
  refine ⟨witness,?_⟩
  change (match (match enter p (preparedWasmHostReset host) fi with
    | .cont s=>run cfg p fuel s | r=>r) with
    | .fin s=>(sync s).map (·,none)
    | .abort s e=>(sync s).map (·,some e)
    | .unmodeled why=>.error why
    | .cont _=>.error "cont")=_
  simp only [entry]
  rw [executed]
  unfold PreparedExecTerminalWitness.result
  cases err:witness.error <;> simp only [witness.synced,Except.map]

end NearCompression
