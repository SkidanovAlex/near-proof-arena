import NearCompression.PreparedTypedAdd32State
import NearCompression.PreparedTypedEqzAuthenticated
import NearCompression.PreparedTypedProvenance
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2 NearSpecV3.Wasm
set_option maxRecDepth 65536
private theorem add32_tag (op : PreparedTypedInstruction) (eq : op.tag=1) : op=.control (.legacy .add) := by
  cases op with
  | control old =>
    cases old with
    | legacy old=>
      cases old with
      | constant v=>cases eq
      | add=>rfl
      | drop=>cases eq
      | end_=>cases eq
    | block=>cases eq
    | brIf=>cases eq
  | «local» kind i=>cases kind <;> cases eq
  | constant64 v=>cases eq
  | add64=>cases eq
  | eqz64=>cases eq

theorem prepared_typed_authenticated_add32 (codeCount count : Nat) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedTypedLiteralAir codeCount count) pub tr)
    (pf : PFunc) (fn : Nat) (checked : preparedTypedCodeCheck count pf fn pub=true)
    (r : Nat) (hr : r<tr.height 0) (opcode : tr.cell 0 r 467=1) :
    pf.code[preparedCodeExecPC (tr.cell 0 r)]?=some (.num 0x6A) := by
  obtain ⟨_,op,fee,amount,target,code,_,_,_,_,_,_,fields⟩:=
    prepared_typed_authenticated_fetch codeCount count tr pub holds pf fn checked r hr
  have h:=fields 5 (by decide)
  change tr.cell 0 r 467=(if 1=op.tag then (1:Fp) else 0) at h
  rw [opcode] at h
  have tag : op.tag=1 := by
    by_cases z:1=op.tag
    · exact z.symm
    · rw [ite_eq_right z] at h
      exact False.elim ((by decide : (1:Fp)≠0) h)
  rw [add32_tag op tag] at code
  exact code

/-- Actual prepare/link/load/resolve and natural CODE buses discharge the
instruction and charge premises of the complete i32.add successor theorem. -/
theorem prepared_typed_setup_add32_state (codeCount count : Nat)
    (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedTypedLiteralAir codeCount count) pub tr)
    (cfg : NearCfg) (bytes : ByteArray) (method : String) (ctx : CallCtx) (blockLevel : Bool)
    (eligible : PreparedRunCallEligible)
    (accepted : preparedTypedSetupCheck count cfg bytes method ctx pub blockLevel=some eligible)
    (r : Nat) (nonlast : r+1<tr.height 0) (active : tr.cell 0 r 41=0) (opcode : tr.cell 0 r 467=1)
    (s : St) (f : Frame) (fs : List Frame) (sp : Nat) (root : Label)
    (state : PreparedTypedState (tr.cell 0 r) s f fs sp count root)
    (fn : f.fn=eligible.setup.methodIndex-eligible.setup.program.m.imports.size)
    (enough : preparedExecWord64 (tr.cell 0 r) 502≤s.gas.g) :
    ∃s',step cfg eligible.setup.program s=.cont s' ∧
      PreparedTypedState (tr.cell 0 (r+1)) s' {f with pc:=f.pc+1} fs (sp-1) count root ∧
      tr.cell 0 (r+1) 41=0 ∧ tr.cell 0 (r+1) 42=0 := by
  obtain ⟨setup,func,checked⟩:=prepared_typed_setup_checked count cfg bytes method ctx pub blockLevel eligible accepted
  have code:=prepared_typed_authenticated_add32 codeCount count tr pub holds eligible.func _ checked r (by omega) opcode
  obtain ⟨_,charge,bound⟩:=prepared_typed_authenticated_fee codeCount count tr pub holds eligible.func _ checked r (by omega)
  rw [←state.pc] at code charge
  exact prepared_typed_add32_success_state count tr 0 r pub (prepared_typed_exec_local codeCount count tr pub holds)
    nonlast active opcode cfg eligible.setup.program s f fs sp root state eligible.func
    (by rw [fn];exact func) code charge bound enough
end NearCompression
