import NearCompression.PreparedExecGas
import NearCompression.PreparedExecWasm

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2 NearSpecV3.Wasm

/-- Actual state interpretation with numeric PC32, stack8, and fast gas64.
No one-hot CODE position or bounded real PC is used. -/
structure PreparedExecState (row : Nat → Fp) (s : St) (f : Frame) (fs : List Frame) (sp : Nat) : Prop where
  depth : sp<9
  selected : ∀ i,i<9 → row (32+i)=if i=sp then 1 else 0
  frames : s.frames=f::fs
  pc : f.pc=preparedCodeExecPC row
  stack : s.stack=preparedWasmStack (preparedExecGhostRow row) sp
  gas : s.gas.g=preparedExecWord64 row 299

theorem prepared_exec_authenticated_opcode (ec cc boundary : List Expr) (count : Nat)
    (tr : Trace Fp) (pub : List Fp) (holds : HoldsP (preparedCodeBusAir ec cc boundary count) pub tr)
    (source : PreparedCodeOrderSource (preparedCodeDataTable cc))
    (inactive : ∀ i,i<25 → preparedCodeInactive (172+i)∈cc)
    (pf : PFunc) (fn : Nat) (checked : preparedCodeVariableCheck pf fn pub=true)
    (r : Nat) (hr : r<tr.height 0) :
    ∃ op:PreparedPublicInstruction,
      pf.code[preparedCodeExecPC (tr.cell 0 r)]?=some op.instr ∧
      ∀ i,i<4 → tr.cell 0 r (466+i)=if i=op.tag then 1 else 0 := by
  obtain ⟨_,op,fee,amount,code,_,_,_,_,fields⟩:=
    prepared_code_variable_fetch ec cc boundary count tr pub holds source inactive pf fn checked r hr
  refine ⟨op,code,?_⟩
  intro i hi
  have h:=fields (4+i) (by omega)
  have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3:=by omega
  rcases cases with z|z|z|z <;> subst i
  all_goals exact h

theorem prepared_exec_table_local (ec cc boundary : List Expr) (count : Nat)
    (tr : Trace Fp) (pub : List Fp) (holds : HoldsP (preparedCodeBusAir ec cc boundary count) pub tr) :
    TableLocal (preparedCodeExecTable ec boundary) tr 0 pub := by
  have ht : 0<(preparedCodeBusAir ec cc boundary count).tables.length := by change 0<2;decide
  exact ⟨(holds.logBound 0 ht).1,(holds.logBound 0 ht).2,holds.constr 0 ht,holds.bits 0 ht⟩

/-- Authenticated unbounded CODE, actual local execution constraints, and an
actual-state interpretation jointly imply the exact interpreter add step.
The new numeric PC and source gas updates agree with its resulting state. -/
theorem prepared_exec_authenticated_add (ec cc boundary : List Expr) (count : Nat)
    (tr : Trace Fp) (pub : List Fp) (holds : HoldsP (preparedCodeBusAir ec cc boundary count) pub tr)
    (codeSource : PreparedCodeOrderSource (preparedCodeDataTable cc))
    (inactive : ∀ i,i<25 → preparedCodeInactive (172+i)∈cc)
    (source : PreparedExecLocalSource (preparedCodeExecTable ec boundary))
    (gasSource : PreparedExecGasSource (preparedCodeExecTable ec boundary))
    (pf : PFunc) (fn : Nat) (checked : preparedCodeVariableCheck pf fn pub=true)
    (r : Nat) (nonlast : r+1<tr.height 0) (active : tr.cell 0 r 41=0) (isAdd : tr.cell 0 r 467=1)
    (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (fs : List Frame) (sp : Nat)
    (state : PreparedExecState (tr.cell 0 r) s f fs sp)
    (func : p.funcs[f.fn]?=some pf)
    (enough : preparedExecWord64 (tr.cell 0 r) 502≤s.gas.g) :
    step cfg p s=.cont {s with
      stack:=preparedWasmStack (preparedExecGhostNext (tr.cell 0 r) (tr.cell 0 (r+1)) (fun i=>pub.getD i 0)) (sp-1)
      frames:={f with pc:=preparedCodeExecPC (tr.cell 0 (r+1))}::fs
      gas:={s.gas with g:=preparedExecWord64 (tr.cell 0 (r+1)) 299}} := by
  have localH:=prepared_exec_table_local ec cc boundary count tr pub holds
  have hr : r<tr.height 0:=by omega
  obtain ⟨op,code,ops⟩:=prepared_exec_authenticated_opcode ec cc boundary count tr pub holds
    codeSource inactive pf fn checked r hr
  have tag:=ops 1 (by decide)
  rw [isAdd] at tag
  have opEq : op=PreparedPublicInstruction.add := by
    cases op <;> simp only [PreparedPublicInstruction.tag,Nat.reduceEqDiff,ite_false,ite_true] at tag ⊢
    all_goals first | rfl | exact False.elim ((by decide : (1:Fp)≠0) tag)
  subst op
  obtain ⟨_,charge,bounded⟩:=prepared_exec_authenticated_fee ec cc boundary count tr pub holds
    codeSource inactive pf fn checked r hr
  have enoughRow : preparedExecWord64 (tr.cell 0 r) 502≤preparedExecWord64 (tr.cell 0 r) 299 := by
    rw [←state.gas];exact enough
  obtain ⟨noBorrow,gasNext⟩:=prepared_exec_gas_success _ tr 0 r pub gasSource localH nonlast active enoughRow
  have endZero:=ops 3 (by decide)
  simp only [PreparedPublicInstruction.tag,Nat.reduceEqDiff,ite_false] at endZero
  have adv : preparedExecPCAdvance.eval tr 0 r pub=Fp.ofNat 1 := by
    change (((1:Fp)+ -tr.cell 0 r 41)*((1:Fp)+ -tr.cell 0 r 430))*((1:Fp)+ -tr.cell 0 r 469)=1
    rw [active,noBorrow,endZero];grind
  have pcNext:=prepared_exec_pc_transition _ tr 0 pub gasSource.pc localH r nonlast 1 (by decide) adv
  have run:=prepared_exec_table_wasm_add _ tr 0 r pub localH nonlast source active noBorrow ops
    cfg p s f fs pf sp (preparedExecWord64 (tr.cell 0 r) 502) state.depth state.selected
    state.frames state.stack func (by rw [state.pc];exact code)
    (by rw [state.pc];exact charge) bounded enough
  rw [run]
  rw [gasNext,←state.gas,pcNext,←state.pc]

end NearCompression
