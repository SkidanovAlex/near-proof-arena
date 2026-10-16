import NearCompression.PreparedTypedConstState
import NearCompression.PreparedTypedEqzAuthenticated
import NearCompression.PreparedTypedProvenance
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2 NearSpecV3.Wasm
set_option maxRecDepth 65536
private theorem const_tag (op : PreparedTypedInstruction) (eq : op.tag=9) : ∃v,op=.constant64 v := by
  cases op with
  | control old =>
    cases old with
    | legacy old=>cases old <;> cases eq
    | block=>cases eq
    | brIf=>cases eq
  | «local» kind i=>cases kind <;> cases eq
  | constant64 v=>exact ⟨v,rfl⟩
  | add64=>cases eq
  | eqz64=>cases eq

theorem prepared_typed_authenticated_const (codeCount count : Nat) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedTypedLiteralAir codeCount count) pub tr)
    (pf : PFunc) (fn : Nat) (checked : preparedTypedCodeCheck count pf fn pub=true)
    (r : Nat) (hr : r<tr.height 0) (opcode : tr.cell 0 r 1280=1) :
    pf.code[preparedCodeExecPC (tr.cell 0 r)]?=some (.i64Const (UInt64.ofNat (preparedTypedImmediate (tr.cell 0 r)))) := by
  obtain ⟨_,op,fee,amount,target,code,_,_,_,_,_,_,fields⟩:=
    prepared_typed_authenticated_fetch codeCount count tr pub holds pf fn checked r hr
  have h:=fields 34 (by decide)
  change tr.cell 0 r 1280=(if 9=op.tag then (1:Fp) else 0) at h
  rw [opcode] at h
  have tag : op.tag=9 := by
    by_cases z:9=op.tag
    · exact z.symm
    · rw [ite_eq_right z] at h
      exact False.elim ((by decide : (1:Fp)≠0) h)
  obtain ⟨value,rfl⟩:=const_tag op tag
  have limbs (i : Nat) (hi : i<4) :
      (preparedTypedImmediateLimb (tr.cell 0 r) i).toNat=(value.toNat/65536^i)%65536 := by
    have h:=fields (if i<2 then 8+i else 30+i) (by split <;> omega)
    have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3:=by omega
    rcases cases with z|z|z|z <;> subst i
    all_goals change (preparedCodeBits _).eval tr 0 r pub=Fp.ofNat _ at h
    all_goals rw [prepared_code_bits_eval] at h
    all_goals simp only [Bool.false_eq_true,ite_false] at h
    all_goals change (preparedCodeLimb (tr.cell 0 r) _).toNat=_
    all_goals simp only [Nat.reduceLT,ite_true,ite_false,Nat.reduceMod,Nat.reduceMul,Nat.reduceAdd,Nat.add_zero] at h ⊢
    all_goals rw [h];exact prepared_code_digit_nat value.toNat _
  have imm : preparedTypedImmediate (tr.cell 0 r)=value.toNat := by
    unfold preparedTypedImmediate instructionAdd64Word
    rw [limbs 0 (by decide),limbs 1 (by decide),limbs 2 (by decide),limbs 3 (by decide)]
    exact prepared_code_digits64 value.toNat value.toNat_lt
  rw [imm]
  simpa only [PreparedTypedInstruction.instr,UInt64.ofNat_toNat] using code

/-- Actual prepare/link/load/resolve and natural CODE buses discharge the
instruction and charge premises of the complete i64.const successor theorem. -/
theorem prepared_typed_setup_const_state (codeCount count : Nat)
    (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedTypedLiteralAir codeCount count) pub tr)
    (cfg : NearCfg) (bytes : ByteArray) (method : String) (ctx : CallCtx) (blockLevel : Bool)
    (eligible : PreparedRunCallEligible)
    (accepted : preparedTypedSetupCheck count cfg bytes method ctx pub blockLevel=some eligible)
    (r : Nat) (nonlast : r+1<tr.height 0) (active : tr.cell 0 r 41=0) (opcode : tr.cell 0 r 1280=1)
    (s : St) (f : Frame) (fs : List Frame) (sp : Nat) (root : Label)
    (state : PreparedTypedState (tr.cell 0 r) s f fs sp count root)
    (fn : f.fn=eligible.setup.methodIndex-eligible.setup.program.m.imports.size)
    (enough : preparedExecWord64 (tr.cell 0 r) 502≤s.gas.g) :
    ∃s',step cfg eligible.setup.program s=.cont s' ∧
      PreparedTypedState (tr.cell 0 (r+1)) s' {f with pc:=f.pc+1} fs (sp+1) count root ∧
      tr.cell 0 (r+1) 41=0 ∧ tr.cell 0 (r+1) 42=0 := by
  obtain ⟨setup,func,checked⟩:=prepared_typed_setup_checked count cfg bytes method ctx pub blockLevel eligible accepted
  have code:=prepared_typed_authenticated_const codeCount count tr pub holds eligible.func _ checked r (by omega) opcode
  obtain ⟨_,charge,bound⟩:=prepared_typed_authenticated_fee codeCount count tr pub holds eligible.func _ checked r (by omega)
  rw [←state.pc] at code charge
  exact prepared_typed_const_success_state count tr 0 r pub (prepared_typed_exec_local codeCount count tr pub holds)
    nonlast active opcode cfg eligible.setup.program s f fs sp root state eligible.func
    (by rw [fn];exact func) code charge bound enough
end NearCompression
