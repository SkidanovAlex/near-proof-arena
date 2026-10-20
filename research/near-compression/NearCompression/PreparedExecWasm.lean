import NearCompression.PreparedExecTransition
import NearCompression.PreparedWasmAddStep

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra NearSpecV3.Wasm ZkFormal.Near

/-- Reusable interpreter bridge without a one-hot or bounded real PC. Both
operands and all output words are derived from the inherited source equations.
Actual PFunc lookup and charge metadata can be supplied by authenticated CODE. -/
theorem prepared_exec_wasm_add_local (row next fields : Nat → Fp)
    (choices : preparedRowChoices row next fields 0 0)
    (transitions : PreparedAddTransitionHolds row next fields)
    (active : row 25=0) (noBorrow : row 414=0)
    (op : ∀ i,i<4 → (preparedFetchPython i).evalWith (preparedRowEnv row next fields 0 0)=if i=1 then 1 else 0)
    (depth : preparedAddDepthResidual.evalWith (preparedRowEnv row next fields 0 0)=0)
    (carries : ∀ i,i<2 → (preparedAddCarryPython i).evalWith (preparedRowEnv row next fields 0 0)=0)
    (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (fs : List Frame) (pf : PFunc)
    (sp amount : Nat) (hs : sp<9)
    (selected : ∀ i,i<9 → row (16+i)=if i=sp then 1 else 0)
    (frames : s.frames=f::fs) (stack : s.stack=preparedWasmStack row sp)
    (func : p.funcs[f.fn]?=some pf) (code : pf.code[f.pc]?=some (.num 0x6A))
    (metadata : PreparedWasmCharge pf f.pc amount) (bounded : amount<u64Bound)
    (enough : amount≤s.gas.g) :
    step cfg p s=.cont {s with
      stack:=preparedWasmStack next (sp-1)
      frames:={f with pc:=f.pc+1}::fs
      gas:={s.gas with g:=s.gas.g-amount}} := by
  have isAdd:=op 1 (by decide)
  simp only [ite_true] at isAdd
  obtain ⟨chosen,hc,he,hot,arithmetic⟩:=prepared_active_add_binop row next fields 0 0
    choices active noBorrow isAdd depth carries
  have eq : chosen=sp := by
    have h:=hot sp hs
    rw [selected sp hs] at h
    simp only [ite_true] at h
    by_cases eq:sp=chosen
    · omega
    · simp only [eq,ite_false] at h
      exact False.elim ((by decide : (1:Fp)≠0) h)
  subst chosen
  have success:=(prepared_success_advance row next fields active noBorrow op).1
  have words:=fun slot hslot=>prepared_add_stack_word_next row next fields transitions
    success op sp hs he hot slot hslot
  obtain ⟨n,rfl⟩:∃n,sp=n+2:=⟨sp-2,by omega⟩
  have minus : n+2-1=n+1:=by omega
  simp only [Nat.add_sub_cancel,minus] at arithmetic words ⊢
  have aNat : (UInt32.ofNat (preparedStackWord row n)).toNat=preparedStackWord row n :=
    Nat.mod_eq_of_lt (prepared_wasm_stack_word_bound row next fields choices n (by omega))
  have bNat : (UInt32.ofNat (preparedStackWord row (n+1))).toNat=preparedStackWord row (n+1) :=
    Nat.mod_eq_of_lt (prepared_wasm_stack_word_bound row next fields choices (n+1) (by omega))
  have lower : preparedWasmStack next n=preparedWasmStack row n := by
    apply prepared_wasm_stack_congr
    intro i hi
    simpa only [ite_eq_right (by omega : i≠n),ite_eq_right (by omega : i≠n+1)] using words i (by omega)
  have top:=words n (by omega)
  simp only [ite_true] at top
  have nextStack : preparedWasmStack next (n+1)=
      (preparedWasmStack row n).push (.i32 (UInt32.ofNat (preparedAddResultWord row))) := by
    simp only [preparedWasmStack,lower,top]
  let base : St := {s with
    stack:=preparedWasmStack row n
    gas:={s.gas with g:=s.gas.g-amount}}
  have stackShape : {s with gas:={s.gas with g:=s.gas.g-amount}}=
      pushV (pushV base (.i32 (UInt32.ofNat (preparedStackWord row n))))
        (.i32 (UInt32.ofNat (preparedStackWord row (n+1)))) := by
    simp only [base,pushV,stack,preparedWasmStack]
  have run:=prepared_wasm_step_charge cfg p s f fs pf _ amount frames func code metadata bounded enough
  have execAdd:=prepared_wasm_exec_add cfg p base f pf
    (UInt32.ofNat (preparedStackWord row n)) (UInt32.ofNat (preparedStackWord row (n+1)))
    (preparedAddResultWord row) (by rw [aNat,bNat];exact arithmetic)
  rw [run,stackShape,execAdd]
  simp only [pushI32,pushV,setFrame,base,frames,nextStack]

/-- Actual new EXEC TableLocal to actual prepared Wasm.step. There is no
CODE16 or real-PC bound. Prepared descriptor provenance supplies the explicit
PFunc/code/charge context; gas synchronization and next-SP certification remain
separate interfaces. -/
theorem prepared_exec_table_wasm_add (table : Table) (tr : Trace Fp) (t r : Nat)
    (pub : List Fp) (localH : TableLocal table tr t pub) (nonlast : r+1<tr.height t)
    (source : PreparedExecLocalSource table)
    (active : tr.cell t r 41=0) (noBorrow : tr.cell t r 430=0)
    (op : ∀ i,i<4 → tr.cell t r (466+i)=if i=1 then 1 else 0)
    (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (fs : List Frame) (pf : PFunc)
    (sp amount : Nat) (hs : sp<9)
    (selected : ∀ i,i<9 → tr.cell t r (32+i)=if i=sp then 1 else 0)
    (frames : s.frames=f::fs)
    (stack : s.stack=preparedWasmStack (preparedExecGhostRow (tr.cell t r)) sp)
    (func : p.funcs[f.fn]?=some pf) (code : pf.code[f.pc]?=some (.num 0x6A))
    (metadata : PreparedWasmCharge pf f.pc amount) (bounded : amount<u64Bound)
    (enough : amount≤s.gas.g) :
    step cfg p s=.cont {s with
      stack:=preparedWasmStack
        (preparedExecGhostNext (tr.cell t r) (tr.cell t (r+1)) (fun i=>pub.getD i 0)) (sp-1)
      frames:={f with pc:=f.pc+1}::fs
      gas:={s.gas with g:=s.gas.g-amount}} := by
  have projection:=prepared_exec_table_projection table tr t r pub localH nonlast source
  apply prepared_exec_wasm_add_local _ _ _ projection.1 projection.2
    (by simpa [preparedExecGhostRow] using active)
    (by simpa [preparedExecGhostRow] using noBorrow) ?_ ?_ ?_
    cfg p s f fs pf sp amount hs ?_ frames stack func code metadata bounded enough
  · intro i hi
    rw [←prepared_exec_lower_eval,prepared_exec_fetch_lower i (by omega)]
    have eq : preparedExecSimplify
        (if i<4 then Expr.col (466+i) false
         else if i<6 then preparedGasBits (470+16*(i-4))
         else preparedGasBits (502+16*(i-6)))=Expr.col (466+i) false := by
      simp only [hi,ite_true,preparedExecSimplify]
    rw [eq]
    exact op i hi
  · exact (prepared_exec_lower_eval _ _ _ _).symm.trans
      (prepared_exec_source_eval table tr t r pub localH nonlast _ source.addDepth)
  · intro i hi
    exact (prepared_exec_lower_eval _ _ _ _).symm.trans
      (prepared_exec_source_eval table tr t r pub localH nonlast _ (source.addCarry i hi))
  · intro i hi
    simpa [preparedExecGhostRow,show ¬16+i<16 by omega,show ¬i+16<16 by omega,
      Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using selected i hi

def preparedExecStackDepth (push : Bool) : Expr :=
  .mul preparedSuccessExpr (.mul (preparedFetchPython (if push then 0 else 2))
    (.col (if push then 24 else 16) false))

theorem prepared_exec_stack_depth (push : Bool) (row next fields : Nat → Fp)
    (success : preparedSuccessExpr.evalWith (preparedRowEnv row next fields 0 0)=1)
    (op : ∀ i,i<4 → (preparedFetchPython i).evalWith (preparedRowEnv row next fields 0 0)=if i=(if push then 0 else 2) then 1 else 0)
    (sp : Nat) (hs : sp<9) (selected : ∀ i,i<9 → row (16+i)=if i=sp then 1 else 0)
    (guard : (preparedExecStackDepth push).evalWith (preparedRowEnv row next fields 0 0)=0) :
    if push then sp<8 else 1≤sp := by
  cases push
  · have h:=selected 0 (by decide)
    have o2:=op 2 (by decide)
    simp only [Bool.false_eq_true,ite_false,ite_true] at o2
    change preparedSuccessExpr.evalWith (preparedRowEnv row next fields 0 0)*
      ((preparedFetchPython 2).evalWith (preparedRowEnv row next fields 0 0)*row 16)=0 at guard
    rw [success,o2] at guard
    have ne : sp≠0 := by
      intro z;subst sp
      simp only [Nat.add_zero,ite_true] at h
      rw [h] at guard
      grind
    simpa using (show 1≤sp by omega)
  · have o:=op 0 (by decide)
    simp only [ite_true] at o
    change preparedSuccessExpr.evalWith (preparedRowEnv row next fields 0 0)*
      ((preparedFetchPython 0).evalWith (preparedRowEnv row next fields 0 0)*row 24)=0 at guard
    rw [success,o] at guard
    have ne : sp≠8 := by
      intro z;subst sp
      have h:=selected 8 (by decide)
      simp only [Nat.reduceAdd,ite_true] at h
      rw [h] at guard
      grind
    simpa using (show sp<8 by omega)

/-- Const/drop actual interpreter steps use the same source-proved full stack
writes, with the depth guard checked rather than assumed. No real PC bound. -/
theorem prepared_exec_wasm_stack_local (push : Bool) (row next fields : Nat → Fp)
    (transitions : PreparedAddTransitionHolds row next fields)
    (active : row 25=0) (noBorrow : row 414=0)
    (op : ∀ i,i<4 → (preparedFetchPython i).evalWith (preparedRowEnv row next fields 0 0)=if i=(if push then 0 else 2) then 1 else 0)
    (guard : (preparedExecStackDepth push).evalWith (preparedRowEnv row next fields 0 0)=0)
    (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (fs : List Frame) (pf : PFunc)
    (sp amount : Nat) (hs : sp<9)
    (selected : ∀ i,i<9 → row (16+i)=if i=sp then 1 else 0)
    (frames : s.frames=f::fs) (stack : s.stack=preparedWasmStack row sp)
    (func : p.funcs[f.fn]?=some pf)
    (code : pf.code[f.pc]?=some (if push then .i32Const
      (UInt32.ofNat (preparedImmediateWord row next fields)) else .drop))
    (metadata : PreparedWasmCharge pf f.pc amount) (bounded : amount<u64Bound)
    (enough : amount≤s.gas.g) :
    step cfg p s=.cont {s with
      stack:=preparedWasmStack next (if push then sp+1 else sp-1)
      frames:={f with pc:=f.pc+1}::fs
      gas:={s.gas with g:=s.gas.g-amount}} := by
  have success : preparedSuccessExpr.evalWith (preparedRowEnv row next fields 0 0)=1 := by
    change ((1:Fp)+ -row 25)*((1:Fp)+ -row 414)=1
    rw [active,noBorrow];grind
  have depth:=prepared_exec_stack_depth push row next fields success op sp hs selected guard
  have words:=fun slot hslot=>prepared_stack_case_word_next push row next fields transitions
    success op sp hs selected slot hslot
  have stk:=prepared_wasm_stack_projection push row next fields sp hs depth words
  have run:=prepared_wasm_step_charge cfg p s f fs pf _ amount frames func code metadata bounded enough
  rw [run]
  cases push <;> simp only [Bool.false_eq_true,ite_false,ite_true] at stk ⊢
  · simp only [exec,popV,setFrame,frames,stk,stack]
  · simp only [exec,pushV,setFrame,frames,stk,stack]

end NearCompression
