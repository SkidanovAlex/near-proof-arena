import NearCompression.PreparedTypedLocalStoreState
import NearCompression.PreparedTypedEqzAuthenticated
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2 NearSpecV3.Wasm
set_option maxRecDepth 65536
private theorem set_tag (op : PreparedTypedInstruction) (eq : op.tag=7) : ∃i,op=.local .set i := by
  cases op with
  | control old =>
    cases old with
    | legacy old=>cases old <;> cases eq
    | block=>cases eq
    | brIf=>cases eq
  | «local» kind i=>cases kind <;> simp_all [PreparedTypedInstruction.tag]
  | constant64 v=>cases eq
  | add64=>cases eq
  | eqz64=>cases eq

theorem prepared_typed_authenticated_local_set (codeCount count : Nat) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedTypedLiteralAir codeCount count) pub tr)
    (pf : PFunc) (fn : Nat) (checked : preparedTypedCodeCheck count pf fn pub=true)
    (r : Nat) (hr : r<tr.height 0) (opcode : tr.cell 0 r 684=1) :
    pf.code[preparedCodeExecPC (tr.cell 0 r)]?=some (.localSet
      ((preparedCodeLimb (tr.cell 0 r) 470).toNat+65536*(preparedCodeLimb (tr.cell 0 r) 486).toNat)) := by
  obtain ⟨_,op,fee,amount,target,code,_,_,_,_,indices,_,fields⟩:=
    prepared_typed_authenticated_fetch codeCount count tr pub holds pf fn checked r hr
  have h:=fields 30 (by decide)
  change tr.cell 0 r 684=(if 7=op.tag then (1:Fp) else 0) at h
  rw [opcode] at h
  have tag : op.tag=7 := by
    by_cases z:7=op.tag
    · exact z.symm
    · rw [if_neg z] at h
      exact False.elim ((by decide : (1:Fp)≠0) h)
  obtain ⟨index,rfl⟩:=set_tag op tag
  have ib:=indices .set index rfl
  have shape:=prepared_typed_code_shape count pf fn pub checked
  have cb:=shape.2.1
  have countEq:=shape.2.2.1
  have bound:index<65536:=by omega
  have low:=fields 8 (by decide)
  have high:=fields 9 (by decide)
  change (preparedCodeBits 470).eval tr 0 r pub=Fp.ofNat ((index/65536^0)%65536) at low
  change (preparedCodeBits 486).eval tr 0 r pub=Fp.ofNat ((index/65536^1)%65536) at high
  rw [prepared_code_bits_eval] at low high
  simp only [Bool.false_eq_true,ite_false] at low high
  have lo:(preparedCodeLimb (tr.cell 0 r) 470).toNat=index := by
    rw [low,prepared_code_digit_nat]
    simp [Nat.mod_eq_of_lt bound]
  have hi:(preparedCodeLimb (tr.cell 0 r) 486).toNat=0 := by
    rw [high,prepared_code_digit_nat]
    simp [Nat.div_eq_of_lt bound]
  rw [lo,hi]
  simpa only [Nat.mul_zero,Nat.add_zero,PreparedTypedInstruction.instr,PreparedLocalOp.instr] using code

/-- Actual prepare/link/load/resolve and natural CODE buses discharge the
instruction and charge premises of the complete local-store successor theorem. -/
theorem prepared_typed_setup_local_set_state (codeCount count : Nat)
    (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedTypedLiteralAir codeCount count) pub tr)
    (cfg : NearCfg) (bytes : ByteArray) (method : String) (ctx : CallCtx) (blockLevel : Bool)
    (eligible : PreparedRunCallEligible)
    (accepted : preparedTypedSetupCheck count cfg bytes method ctx pub blockLevel=some eligible)
    (r : Nat) (nonlast : r+1<tr.height 0) (active : tr.cell 0 r 41=0) (opcode : tr.cell 0 r 684=1)
    (s : St) (f : Frame) (fs : List Frame) (sp : Nat) (root : Label)
    (state : PreparedTypedState (tr.cell 0 r) s f fs sp count root)
    (fn : f.fn=eligible.setup.methodIndex-eligible.setup.program.m.imports.size)
    (enough : preparedExecWord64 (tr.cell 0 r) 502≤s.gas.g) :
    ∃s',step cfg eligible.setup.program s=.cont s' ∧
      PreparedTypedState (tr.cell 0 (r+1)) s' {f with pc:=f.pc+1,locals:=f.locals.set! ((preparedCodeLimb (tr.cell 0 r) 470).toNat+65536*(preparedCodeLimb (tr.cell 0 r) 486).toNat) (preparedTypedStackValue (tr.cell 0 r) (sp-1))} fs (sp-1) count root ∧
      tr.cell 0 (r+1) 41=0 ∧ tr.cell 0 (r+1) 42=0 := by
  obtain ⟨setup,func,checked⟩:=prepared_typed_setup_checked count cfg bytes method ctx pub blockLevel eligible accepted
  have code:=prepared_typed_authenticated_local_set codeCount count tr pub holds eligible.func _ checked r (by omega) opcode
  obtain ⟨_,charge,bound⟩:=prepared_typed_authenticated_fee codeCount count tr pub holds eligible.func _ checked r (by omega)
  rw [←state.pc] at code charge
  exact prepared_typed_local_set_state count tr 0 r pub (prepared_typed_exec_local codeCount count tr pub holds)
    nonlast active opcode cfg eligible.setup.program s f fs sp root state eligible.func
    (by rw [fn];exact func) code charge bound enough

private theorem tee_tag (op : PreparedTypedInstruction) (eq : op.tag=8) : ∃i,op=.local .tee i := by
  cases op with
  | control old =>
    cases old with
    | legacy old=>cases old <;> cases eq
    | block=>cases eq
    | brIf=>cases eq
  | «local» kind i=>cases kind <;> simp_all [PreparedTypedInstruction.tag]
  | constant64 v=>cases eq
  | add64=>cases eq
  | eqz64=>cases eq

theorem prepared_typed_authenticated_local_tee (codeCount count : Nat) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedTypedLiteralAir codeCount count) pub tr)
    (pf : PFunc) (fn : Nat) (checked : preparedTypedCodeCheck count pf fn pub=true)
    (r : Nat) (hr : r<tr.height 0) (opcode : tr.cell 0 r 685=1) :
    pf.code[preparedCodeExecPC (tr.cell 0 r)]?=some (.localTee
      ((preparedCodeLimb (tr.cell 0 r) 470).toNat+65536*(preparedCodeLimb (tr.cell 0 r) 486).toNat)) := by
  obtain ⟨_,op,fee,amount,target,code,_,_,_,_,indices,_,fields⟩:=
    prepared_typed_authenticated_fetch codeCount count tr pub holds pf fn checked r hr
  have h:=fields 31 (by decide)
  change tr.cell 0 r 685=(if 8=op.tag then (1:Fp) else 0) at h
  rw [opcode] at h
  have tag : op.tag=8 := by
    by_cases z:8=op.tag
    · exact z.symm
    · rw [if_neg z] at h
      exact False.elim ((by decide : (1:Fp)≠0) h)
  obtain ⟨index,rfl⟩:=tee_tag op tag
  have ib:=indices .tee index rfl
  have shape:=prepared_typed_code_shape count pf fn pub checked
  have cb:=shape.2.1
  have countEq:=shape.2.2.1
  have bound:index<65536:=by omega
  have low:=fields 8 (by decide)
  have high:=fields 9 (by decide)
  change (preparedCodeBits 470).eval tr 0 r pub=Fp.ofNat ((index/65536^0)%65536) at low
  change (preparedCodeBits 486).eval tr 0 r pub=Fp.ofNat ((index/65536^1)%65536) at high
  rw [prepared_code_bits_eval] at low high
  simp only [Bool.false_eq_true,ite_false] at low high
  have lo:(preparedCodeLimb (tr.cell 0 r) 470).toNat=index := by
    rw [low,prepared_code_digit_nat]
    simp [Nat.mod_eq_of_lt bound]
  have hi:(preparedCodeLimb (tr.cell 0 r) 486).toNat=0 := by
    rw [high,prepared_code_digit_nat]
    simp [Nat.div_eq_of_lt bound]
  rw [lo,hi]
  simpa only [Nat.mul_zero,Nat.add_zero,PreparedTypedInstruction.instr,PreparedLocalOp.instr] using code

/-- Actual prepare/link/load/resolve and natural CODE buses discharge the
instruction and charge premises of the complete local-store successor theorem. -/
theorem prepared_typed_setup_local_tee_state (codeCount count : Nat)
    (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedTypedLiteralAir codeCount count) pub tr)
    (cfg : NearCfg) (bytes : ByteArray) (method : String) (ctx : CallCtx) (blockLevel : Bool)
    (eligible : PreparedRunCallEligible)
    (accepted : preparedTypedSetupCheck count cfg bytes method ctx pub blockLevel=some eligible)
    (r : Nat) (nonlast : r+1<tr.height 0) (active : tr.cell 0 r 41=0) (opcode : tr.cell 0 r 685=1)
    (s : St) (f : Frame) (fs : List Frame) (sp : Nat) (root : Label)
    (state : PreparedTypedState (tr.cell 0 r) s f fs sp count root)
    (fn : f.fn=eligible.setup.methodIndex-eligible.setup.program.m.imports.size)
    (enough : preparedExecWord64 (tr.cell 0 r) 502≤s.gas.g) :
    ∃s',step cfg eligible.setup.program s=.cont s' ∧
      PreparedTypedState (tr.cell 0 (r+1)) s' {f with pc:=f.pc+1,locals:=f.locals.set! ((preparedCodeLimb (tr.cell 0 r) 470).toNat+65536*(preparedCodeLimb (tr.cell 0 r) 486).toNat) (preparedTypedStackValue (tr.cell 0 r) (sp-1))} fs sp count root ∧
      tr.cell 0 (r+1) 41=0 ∧ tr.cell 0 (r+1) 42=0 := by
  obtain ⟨setup,func,checked⟩:=prepared_typed_setup_checked count cfg bytes method ctx pub blockLevel eligible accepted
  have code:=prepared_typed_authenticated_local_tee codeCount count tr pub holds eligible.func _ checked r (by omega) opcode
  obtain ⟨_,charge,bound⟩:=prepared_typed_authenticated_fee codeCount count tr pub holds eligible.func _ checked r (by omega)
  rw [←state.pc] at code charge
  exact prepared_typed_local_tee_state count tr 0 r pub (prepared_typed_exec_local codeCount count tr pub holds)
    nonlast active opcode cfg eligible.setup.program s f fs sp root state eligible.func
    (by rw [fn];exact func) code charge bound enough
end NearCompression
