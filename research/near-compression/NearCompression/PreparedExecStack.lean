import NearCompression.PreparedExecState

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2 NearSpecV3.Wasm

def preparedExecImmediate (row : Nat → Fp) : Nat :=
  (preparedCodeLimb row 470).toNat+65536*(preparedCodeLimb row 486).toNat

theorem prepared_exec_immediate_projection (row next pub : Nat → Fp) :
    preparedImmediateWord (preparedExecGhostRow row) (preparedExecGhostNext row next pub)
      (preparedExecGhostPub row next pub)=preparedExecImmediate row := by
  unfold preparedImmediateWord
  rw [←prepared_exec_lower_eval,←prepared_exec_lower_eval,
    prepared_exec_fetch_lower 4 (by decide),prepared_exec_fetch_lower 5 (by decide),
    prepared_exec_simplify_eval,prepared_exec_simplify_eval]
  simp only [Nat.reduceLT,ite_true,ite_false,Nat.reduceSub,Nat.reduceMul,Nat.reduceAdd]
  rw [prepared_bits_row_horner,prepared_bits_row_horner]
  rfl

theorem prepared_exec_authenticated_immediate (ec cc boundary : List Expr) (count : Nat)
    (tr : Trace Fp) (pub : List Fp) (holds : HoldsP (preparedCodeBusAir ec cc boundary count) pub tr)
    (source : PreparedCodeOrderSource (preparedCodeDataTable cc))
    (inactive : ∀ i,i<25 → preparedCodeInactive (172+i)∈cc)
    (pf : PFunc) (fn : Nat) (checked : preparedCodeVariableCheck pf fn pub=true)
    (r : Nat) (hr : r<tr.height 0) :
    ∃ op:PreparedPublicInstruction,
      pf.code[preparedCodeExecPC (tr.cell 0 r)]?=some op.instr ∧
      preparedExecImmediate (tr.cell 0 r)=op.immediate ∧
      ∀ i,i<4 → tr.cell 0 r (466+i)=if i=op.tag then 1 else 0 := by
  obtain ⟨_,op,fee,amount,code,_,_,_,_,fields⟩:=
    prepared_code_variable_fetch ec cc boundary count tr pub holds source inactive pf fn checked r hr
  refine ⟨op,code,?_,?_⟩
  · have lo:=fields 8 (by decide)
    have hi:=fields 9 (by decide)
    change (preparedCodeBits 470).eval tr 0 r pub=Fp.ofNat ((op.immediate/65536^0)%65536) at lo
    change (preparedCodeBits 486).eval tr 0 r pub=Fp.ofNat ((op.immediate/65536^1)%65536) at hi
    rw [prepared_code_bits_eval] at lo hi
    simp only [Bool.false_eq_true,ite_false] at lo hi
    unfold preparedExecImmediate
    rw [lo,hi,prepared_code_digit_nat,prepared_code_digit_nat]
    simp only [Nat.reducePow,Nat.div_one]
    apply prepared_code_digits32
    cases op with
    | constant v => exact v.toNat_lt
    | _ => decide
  · intro i hi
    have h:=fields (4+i) (by omega)
    have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3:=by omega
    rcases cases with z|z|z|z <;> subst i
    all_goals exact h

theorem prepared_exec_table_wasm_stack (push : Bool) (table : Table) (tr : Trace Fp) (t r : Nat)
    (pub : List Fp) (localH : TableLocal table tr t pub) (nonlast : r+1<tr.height t)
    (source : PreparedExecLocalSource table)
    (guard : PreparedExecHasSource table (preparedExecStackDepth push))
    (active : tr.cell t r 41=0) (noBorrow : tr.cell t r 430=0)
    (op : ∀ i,i<4 → tr.cell t r (466+i)=if i=(if push then 0 else 2) then 1 else 0)
    (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (fs : List Frame) (pf : PFunc)
    (sp amount : Nat) (hs : sp<9)
    (selected : ∀ i,i<9 → tr.cell t r (32+i)=if i=sp then 1 else 0)
    (frames : s.frames=f::fs)
    (stack : s.stack=preparedWasmStack (preparedExecGhostRow (tr.cell t r)) sp)
    (func : p.funcs[f.fn]?=some pf)
    (code : pf.code[f.pc]?=some (if push then .i32Const (UInt32.ofNat (preparedExecImmediate (tr.cell t r))) else .drop))
    (metadata : PreparedWasmCharge pf f.pc amount) (bounded : amount<u64Bound)
    (enough : amount≤s.gas.g) :
    step cfg p s=.cont {s with
      stack:=preparedWasmStack
        (preparedExecGhostNext (tr.cell t r) (tr.cell t (r+1)) (fun i=>pub.getD i 0)) (if push then sp+1 else sp-1)
      frames:={f with pc:=f.pc+1}::fs
      gas:={s.gas with g:=s.gas.g-amount}} := by
  have projection:=prepared_exec_table_projection table tr t r pub localH nonlast source
  apply prepared_exec_wasm_stack_local push _ _ _ projection.2
    (by simpa [preparedExecGhostRow] using active)
    (by simpa [preparedExecGhostRow] using noBorrow) ?_ ?_
    cfg p s f fs pf sp amount hs ?_ frames stack func ?_ metadata bounded enough
  · intro i hi
    rw [←prepared_exec_lower_eval,prepared_exec_fetch_lower i (by omega)]
    simp only [hi,ite_true,preparedExecSimplify,Expr.evalWith,preparedRowEnv]
    exact op i hi
  · exact (prepared_exec_lower_eval _ _ _ _).symm.trans
      (prepared_exec_source_eval table tr t r pub localH nonlast _ guard)
  · intro i hi
    simpa [preparedExecGhostRow,show ¬16+i<16 by omega,show ¬i+16<16 by omega,
      Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using selected i hi
  · rw [prepared_exec_immediate_projection]
    exact code

end NearCompression
