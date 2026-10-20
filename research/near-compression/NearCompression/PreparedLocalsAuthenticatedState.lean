import NearCompression.PreparedLocalsSuccessState
import NearCompression.PreparedLocalsAuthenticated
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2 NearSpecV3.Wasm
set_option maxRecDepth 65536

private theorem local_instr_injective (op : PreparedLocalsInstruction) (kind : PreparedLocalOp) (index : Nat)
    (eq : op.instr=kind.instr index) : op=.local kind index := by
  cases op with
  | control old =>
    cases old with
    | legacy old => cases old <;> cases kind <;> cases eq
    | block => cases kind <;> cases eq
    | brIf => cases kind <;> cases eq
  | «local» k i => cases k <;> cases kind <;> cases eq <;> rfl

/-- Authenticated prepared code supplies every local opcode flag. -/
theorem prepared_locals_authenticated_flags (codeCount count : Nat)
    (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedLocalsLiteralAir codeCount count) pub tr)
    (pf : PFunc) (fn : Nat) (checked : preparedLocalsCodeCheck count pf fn pub=true)
    (r : Nat) (hr : r<tr.height 0) (kind : PreparedLocalOp) (index : Nat)
    (code : pf.code[preparedCodeExecPC (tr.cell 0 r)]?=some (kind.instr index)) :
    (∀i,i<4 → tr.cell 0 r (466+i)=0) ∧ tr.cell 0 r 605=0 ∧ tr.cell 0 r 606=0 ∧
    tr.cell 0 r 683=(if kind=.get then 1 else 0) ∧
    tr.cell 0 r 684=(if kind=.set then 1 else 0) ∧
    tr.cell 0 r 685=(if kind=.tee then 1 else 0) := by
  obtain ⟨_,op,fee,amount,target,actual,gas,charge,bound,tbound,valid,targetEq,fields⟩:=
    prepared_locals_authenticated_fetch codeCount count tr pub holds pf fn checked r hr
  have same:=local_instr_injective op kind index (Option.some.inj (actual.symm.trans code))
  have fields' := same ▸ fields
  clear fields
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro i hi
    have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
    rcases cases with eq|eq|eq|eq <;> subst i
    · have h:=fields' 4 (by decide);cases kind <;> exact h
    · have h:=fields' 5 (by decide);cases kind <;> exact h
    · have h:=fields' 6 (by decide);cases kind <;> exact h
    · have h:=fields' 7 (by decide);cases kind <;> exact h
  · have h:=fields' 25 (by decide);cases kind <;> exact h
  · have h:=fields' 26 (by decide);cases kind <;> exact h
  · have h:=fields' 29 (by decide);cases kind <;> exact h
  · have h:=fields' 30 (by decide);cases kind <;> exact h
  · have h:=fields' 31 (by decide);cases kind <;> exact h

/-- Real prepare/link/load/resolve provenance and natural bus authentication
close the local-instruction successor relation. No independent fee, immediate,
operand lookup, next-frame, or next-stack certificate is assumed. -/
theorem prepared_locals_setup_success_state (codeCount count : Nat)
    (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedLocalsLiteralAir codeCount count) pub tr)
    (cfg : NearCfg) (bytes : ByteArray) (method : String) (ctx : CallCtx) (blockLevel : Bool)
    (eligible : PreparedRunCallEligible)
    (accepted : preparedLocalsSetupCheck count cfg bytes method ctx pub blockLevel=some eligible)
    (r : Nat) (nonlast : r+1<tr.height 0) (active : tr.cell 0 r 41=0)
    (kind : PreparedLocalOp) (tag : tr.cell 0 r (677+preparedLocalsKindTag kind)=1)
    (s : St) (f : Frame) (fs : List Frame) (sp : Nat) (root : Label)
    (state : PreparedLocalsState (tr.cell 0 r) s f fs sp count root)
    (fn : f.fn=eligible.setup.methodIndex-eligible.setup.program.m.imports.size)
    (enough : preparedExecWord64 (tr.cell 0 r) 502≤s.gas.g) :
    ∃ s', step cfg eligible.setup.program s=.cont s' ∧
      PreparedLocalsState (tr.cell 0 (r+1)) s'
        {f with pc:=f.pc+1,locals:=preparedLocalsArray (tr.cell 0 (r+1)) count}
        fs (preparedLocalsNextDepth kind sp) count root ∧
      tr.cell 0 (r+1) 41=0 ∧ tr.cell 0 (r+1) 42=0 := by
  obtain ⟨setup,func,checked⟩:=prepared_locals_setup_checked count cfg bytes method ctx pub blockLevel eligible accepted
  obtain ⟨index,valid,code,selected⟩:=prepared_locals_authenticated_selected codeCount count tr pub holds
    eligible.func _ checked r (by omega) kind tag
  have flags:=prepared_locals_authenticated_flags codeCount count tr pub holds eligible.func _ checked r (by omega) kind index code
  obtain ⟨_,charge,bound⟩:=prepared_locals_authenticated_fee codeCount count tr pub holds eligible.func _ checked r (by omega)
  rw [←state.1.1.pc] at code charge
  exact prepared_locals_success_state kind count tr 0 r pub
    (prepared_locals_exec_local codeCount count tr pub holds) nonlast active
    flags.1 flags.2.1 flags.2.2.1 flags.2.2.2.1 flags.2.2.2.2.1 flags.2.2.2.2.2
    cfg eligible.setup.program s f fs sp index root state valid selected eligible.func
    (by rw [fn];exact func) code charge bound enough
end NearCompression
