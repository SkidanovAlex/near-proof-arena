import NearCompression.PreparedControlLegacyAdapter

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpecV3.Wasm

theorem prepared_control_legacy_add_next_sp (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal preparedControlLiteralExecTable tr t pub) (nonlast : r+1<tr.height t) (branchZero : tr.cell t r 606=0)
    (active : tr.cell t r 41=0) (noBorrow : tr.cell t r 430=0)
    (op : ∀ i,i<4 → tr.cell t r (466+i)=if i=1 then 1 else 0)
    (sp : Nat) (hs : sp<9) (selected : ∀ i,i<9 → tr.cell t r (32+i)=if i=sp then 1 else 0) :
    1≤sp ∧ sp-1<9 ∧ ∀ i,i<9 → tr.cell t (r+1) (32+i)=if i=sp-1 then 1 else 0 := by
  have projection:=prepared_control_legacy_projection tr t r pub localH nonlast branchZero
  obtain ⟨nsp,hn,hot⟩:=prepared_control_literal_onehot tr t (r+1) pub localH nonlast
  have opOld:=prepared_exec_opcode_projection (tr.cell t r) (tr.cell t (r+1)) (fun i=>pub.getD i 0) 1 op
  have activeOld : preparedExecGhostRow (tr.cell t r) 25=0 := active
  have noBorrowOld : preparedExecGhostRow (tr.cell t r) 414=0 := noBorrow
  have success:=(prepared_success_advance _ _ _ activeOld noBorrowOld opOld).1
  have current : ∀ i,i<9 → preparedExecGhostRow (tr.cell t r) (16+i)=if i=sp then 1 else 0 := by
    intro i hi
    simpa [preparedExecGhostRow,show ¬16+i<16 by omega,show ¬i+16<16 by omega,
      Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using selected i hi
  have following : ∀ i,i<9 → preparedExecGhostNext (tr.cell t r) (tr.cell t (r+1))
      (fun i=>pub.getD i 0) (16+i)=if i=nsp then 1 else 0 := by
    intro i hi
    rw [prepared_exec_ghost_next_column _ _ _ _ (by omega)]
    simpa [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using hot i hi
  have eq:=prepared_add_sp_next _ _ _ projection.2 success opOld sp nsp hs hn current following
  have ns : nsp=sp-1:=by omega
  exact ⟨by omega,by omega,by simpa only [ns] using hot⟩


theorem prepared_control_legacy_stack_next_sp (push : Bool) (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal preparedControlLiteralExecTable tr t pub) (nonlast : r+1<tr.height t) (branchZero : tr.cell t r 606=0)
    (active : tr.cell t r 41=0) (noBorrow : tr.cell t r 430=0)
    (op : ∀ i,i<4 → tr.cell t r (466+i)=if i=(if push then 0 else 2) then 1 else 0)
    (sp : Nat) (hs : sp<9) (selected : ∀ i,i<9 → tr.cell t r (32+i)=if i=sp then 1 else 0) :
    (if push then sp<8 else 1≤sp) ∧ (if push then sp+1 else sp-1)<9 ∧
    ∀ i,i<9 → tr.cell t (r+1) (32+i)=if i=(if push then sp+1 else sp-1) then 1 else 0 := by
  have projection:=prepared_control_legacy_projection tr t r pub localH nonlast branchZero
  obtain ⟨nsp,hn,hot⟩:=prepared_control_literal_onehot tr t (r+1) pub localH nonlast
  have opOld:=prepared_exec_opcode_projection (tr.cell t r) (tr.cell t (r+1))
    (fun i=>pub.getD i 0) (if push then 0 else 2) op
  have success : preparedSuccessExpr.evalWith (preparedRowEnv (preparedExecGhostRow (tr.cell t r))
      (preparedExecGhostNext (tr.cell t r) (tr.cell t (r+1)) (fun i=>pub.getD i 0))
      (preparedExecGhostPub (tr.cell t r) (tr.cell t (r+1)) (fun i=>pub.getD i 0)) 0 0)=1 := by
    change ((1:Fp)+ -tr.cell t r 41)*((1:Fp)+ -tr.cell t r 430)=1
    rw [active,noBorrow];grind
  have current : ∀ i,i<9 → preparedExecGhostRow (tr.cell t r) (16+i)=if i=sp then 1 else 0 := by
    intro i hi
    simpa [preparedExecGhostRow,show ¬16+i<16 by omega,show ¬i+16<16 by omega,
      Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using selected i hi
  have following : ∀ i,i<9 → preparedExecGhostNext (tr.cell t r) (tr.cell t (r+1))
      (fun i=>pub.getD i 0) (16+i)=if i=nsp then 1 else 0 := by
    intro i hi
    rw [prepared_exec_ghost_next_column _ _ _ _ (by omega)]
    simpa [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using hot i hi
  have eq:=prepared_stack_pointer_next push _ _ _ projection.2 success opOld sp nsp hs hn current following
  cases push <;> simp only [Bool.false_eq_true,ite_true,ite_false,Nat.add_zero] at eq ⊢
  · have ns:nsp=sp-1:=by omega
    exact ⟨by omega,by omega,by simpa only [ns] using hot⟩
  · exact ⟨by omega,by omega,by simpa only [eq] using hot⟩


theorem prepared_control_legacy_wasm_add (tr : Trace Fp) (t r : Nat)
    (pub : List Fp) (localH : TableLocal preparedControlLiteralExecTable tr t pub) (nonlast : r+1<tr.height t)
    (branchZero : tr.cell t r 606=0)
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
  have projection:=prepared_control_legacy_projection tr t r pub localH nonlast branchZero
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
      (prepared_control_legacy_source_eval tr t r pub localH nonlast branchZero _ prepared_control_legacy_add_depth_source)
  · intro i hi
    exact (prepared_exec_lower_eval _ _ _ _).symm.trans
      (prepared_control_legacy_source_eval tr t r pub localH nonlast branchZero _ (prepared_control_legacy_add_carry_source i hi))
  · intro i hi
    simpa [preparedExecGhostRow,show ¬16+i<16 by omega,show ¬i+16<16 by omega,
      Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using selected i hi


theorem prepared_control_legacy_wasm_stack (push : Bool) (tr : Trace Fp) (t r : Nat)
    (pub : List Fp) (localH : TableLocal preparedControlLiteralExecTable tr t pub) (nonlast : r+1<tr.height t)
    (branchZero : tr.cell t r 606=0)
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
  have projection:=prepared_control_legacy_projection tr t r pub localH nonlast branchZero
  apply prepared_exec_wasm_stack_local push _ _ _ projection.2
    (by simpa [preparedExecGhostRow] using active)
    (by simpa [preparedExecGhostRow] using noBorrow) ?_ ?_
    cfg p s f fs pf sp amount hs ?_ frames stack func ?_ metadata bounded enough
  · intro i hi
    rw [←prepared_exec_lower_eval,prepared_exec_fetch_lower i (by omega)]
    simp only [hi,ite_true,preparedExecSimplify,Expr.evalWith,preparedRowEnv]
    exact op i hi
  · exact (prepared_exec_lower_eval _ _ _ _).symm.trans
      (prepared_control_legacy_source_eval tr t r pub localH nonlast branchZero _ (prepared_control_legacy_stack_depth_source push))
  · intro i hi
    simpa [preparedExecGhostRow,show ¬16+i<16 by omega,show ¬i+16<16 by omega,
      Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using selected i hi
  · rw [prepared_exec_immediate_projection]
    exact code


theorem prepared_control_legacy_pc_label (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal preparedControlLiteralExecTable tr t pub) (nonlast : r+1<tr.height t)
    (active : tr.cell t r 41=0) (charged : tr.cell t r 430=0)
    (branchZero : tr.cell t r 606=0) (blockZero : tr.cell t r 605=0) (endZero : tr.cell t r 469=0) :
    preparedCodeExecPC (tr.cell t (r+1))=preparedCodeExecPC (tr.cell t r)+1 ∧
    tr.cell t (r+1) 41=0 ∧ tr.cell t (r+1) 42=0 ∧
    tr.cell t (r+1) 639=tr.cell t r 639 ∧
    (∀ i,i<9 → tr.cell t (r+1) (640+i)=tr.cell t r (640+i)) ∧
    preparedControlSavedTarget (tr.cell t (r+1))=preparedControlSavedTarget (tr.cell t r) := by
  have notTaken : preparedControlTaken.eval tr t r pub=0 := by
    change preparedExecGasSuccess.eval tr t r pub*(tr.cell t r 606*tr.cell t r 681)=0
    rw [branchZero];grind
  have advance : preparedControlAdvance.eval tr t r pub=Fp.ofNat 1 := by
    change (((1:Fp)+ -tr.cell t r 41)*((1:Fp)+ -tr.cell t r 430))*
      ((1:Fp)+ -(tr.cell t r 469*((1:Fp)+ -tr.cell t r 639)+tr.cell t r 606*tr.cell t r 681))=1
    rw [active,charged,endZero,branchZero];grind
  have status:=prepared_control_continue_status tr t r pub localH nonlast active charged (by rw [endZero];grind)
  have opened : preparedControlOpened.eval tr t r pub=0 := by
    change preparedExecGasSuccess.eval tr t r pub*tr.cell t r 605=0
    rw [blockZero];grind
  have keep : preparedControlKeep.eval tr t r pub=1 := by
    change (1:Fp)+ -(preparedControlOpened.eval tr t r pub+
      (preparedControlTaken.eval tr t r pub+preparedExecGasSuccess.eval tr t r pub*(tr.cell t r 469*tr.cell t r 639)))=1
    rw [opened,notTaken,endZero];grind
  have labels:=prepared_control_label_equations tr t r pub localH nonlast
  rw [opened,keep] at labels
  refine ⟨prepared_control_sequential_pc tr t r pub localH nonlast notTaken 1 (by decide) advance,
    status.2.1,status.2.2,by grind,?_,?_⟩
  · intro i hi;have h:=labels.2.1 i hi;grind
  · have low:=labels.2.2 0 (by decide)
    have high:=labels.2.2 1 (by decide)
    have l : preparedCodeLimb (tr.cell t (r+1)) 649=preparedCodeLimb (tr.cell t r) 649:=by simpa only [Nat.mul_zero,Nat.add_zero] using (show _=_ from by grind)
    have h : preparedCodeLimb (tr.cell t (r+1)) 665=preparedCodeLimb (tr.cell t r) 665:=by simpa only [Nat.mul_one,Nat.reduceAdd] using (show _=_ from by grind)
    unfold preparedControlSavedTarget
    rw [l,h]

end NearCompression
