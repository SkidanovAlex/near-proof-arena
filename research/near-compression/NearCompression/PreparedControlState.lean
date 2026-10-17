import NearCompression.PreparedControlFrameStack
import NearCompression.PreparedControlGas
import NearCompression.PreparedControlStep

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpecV3.Wasm

/-- The root function label is fixed across the bounded control slice. Only
one nested void block is represented; its height and target come from AIR. -/
def PreparedControlLabels (row : Nat → Fp) (f : Frame) (root : Label) : Prop :=
  (row 639=0 ∧ f.labels=[root]) ∨
  ∃ height,height<9 ∧ row 639=1 ∧
    (∀ i,i<9 → row (640+i)=if i=height then 1 else 0) ∧
    f.labels=[{target:=preparedControlSavedTarget row,arity:=0,height:=height,isLoop:=false},root]

def PreparedControlState (row : Nat → Fp) (s : St) (f : Frame)
    (fs : List Frame) (sp : Nat) (root : Label) : Prop :=
  PreparedExecState row s f fs sp ∧ PreparedControlLabels row f root

theorem prepared_control_stack_size (row : Nat → Fp) (n : Nat) :
    (preparedWasmStack row n).size=n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [preparedWasmStack,Array.size_push,ih]

/-- Actual block step and successor-state refinement. CODE, endOf and charge
premises are explicit provenance interfaces, not inferred from local rows. -/
theorem prepared_control_block_state (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal preparedControlLiteralExecTable tr t pub) (nonlast : r+1<tr.height t)
    (active : tr.cell t r 41=0) (block : tr.cell t r 605=1)
    (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (fs : List Frame)
    (sp : Nat) (root : Label) (state : PreparedControlState (tr.cell t r) s f fs sp root)
    (pf : PFunc) (func : p.funcs[f.fn]?=some pf)
    (code : pf.code[f.pc]?=some (.block none)) (e amount : Nat)
    (target : pf.endOf[f.pc]?=some e)
    (targetRow : (preparedCodeLimb (tr.cell t r) 607).toNat+65536*(preparedCodeLimb (tr.cell t r) 623).toNat=e+1)
    (charge : PreparedWasmCharge pf f.pc amount) (bounded : amount<u64Bound)
    (fee : preparedExecWord64 (tr.cell t r) 502=amount) (enough : amount≤s.gas.g) :
    ∃ s',step cfg p s=.cont s' ∧
      PreparedControlState (tr.cell t (r+1)) s'
        {f with pc:=f.pc+1,labels:=[{target:=e+1,arity:=0,height:=sp,isLoop:=false},root]} fs sp root ∧
      tr.cell t (r+1) 41=0 ∧ tr.cell t (r+1) 42=0 := by
  have enoughRow : preparedExecWord64 (tr.cell t r) 502≤preparedExecWord64 (tr.cell t r) 299 := by
    rw [fee,←state.1.gas];exact enough
  obtain ⟨charged,gas⟩:=prepared_control_gas_success _ tr t r pub prepared_control_literal_gas_source localH nonlast active enoughRow
  have projection:=prepared_control_block_label tr t r pub localH nonlast active charged block
  have labels : f.labels=[root] := by
    rcases state.2 with h|⟨height,_,present,_,_⟩
    · exact h.2
    · rw [projection.1] at present
      exact False.elim ((by decide : (0:Fp)≠1) present)
  obtain ⟨sp',bound,selected,nextSelected⟩:=prepared_control_frame_sp tr t r pub localH nonlast 4 (Or.inr rfl) block
  have eq : sp'=sp := by
    have a:=selected sp' bound
    have b:=state.1.selected sp' bound
    rw [if_pos rfl] at a
    rw [a] at b
    by_cases eq:sp'=sp
    · exact eq
    · simp only [eq,ite_false] at b
      exact False.elim ((by decide : (1:Fp)≠0) b)
  subst sp'
  have stack : preparedWasmStack (preparedExecGhostRow (tr.cell t (r+1))) sp=s.stack := by
    rw [state.1.stack]
    apply prepared_wasm_stack_congr
    intro i hi
    exact prepared_control_frame_stack tr t r pub localH nonlast 4 (Or.inr rfl) block i (by omega)
  have size : s.stack.size=sp := by rw [state.1.stack,prepared_control_stack_size]
  have saved : preparedControlSavedTarget (tr.cell t (r+1))=e+1 := by
    have l:=projection.2.2.2.1 0 (by decide)
    have h:=projection.2.2.2.1 1 (by decide)
    simp only [Nat.mul_zero,Nat.add_zero,Nat.mul_one,Nat.reduceAdd] at l h
    unfold preparedControlSavedTarget
    rw [l,h];exact targetRow
  have run:=prepared_control_step_block cfg p s f fs pf amount e state.1.frames func code target charge bounded enough
  rw [size,labels] at run
  let f' : Frame:={f with pc:=f.pc+1,labels:=[{target:=e+1,arity:=0,height:=sp,isLoop:=false},root]}
  let s' : St:={s with frames:=f'::fs,gas:={s.gas with g:=s.gas.g-amount}}
  have run' : step cfg p s=.cont s' := by
    simpa only [setFrame,state.1.frames] using run
  refine ⟨s',run',⟨?_,?_⟩,projection.2.2.2.2.2.1,projection.2.2.2.2.2.2⟩
  · refine ⟨state.1.depth,nextSelected,rfl,?_,stack.symm,?_⟩
    · change f.pc+1=preparedCodeExecPC (tr.cell t (r+1))
      rw [state.1.pc,projection.2.2.2.2.1]
    · change s.gas.g-amount=preparedExecWord64 (tr.cell t (r+1)) 299
      rw [gas,fee,state.1.gas]
  · right
    refine ⟨sp,state.1.depth,projection.2.1,?_,?_⟩
    · intro i hi
      rw [projection.2.2.1 i hi]
      exact state.1.selected i hi
    · change [{target:=e+1,arity:=0,height:=sp,isLoop:=false},root]=_
      rw [saved]

/-- Actual nested-end step. The root label remains, while AIR constrains
PC, stack, gas, label metadata, and continuing status of the successor. -/
theorem prepared_control_nested_end_state (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal preparedControlLiteralExecTable tr t pub) (nonlast : r+1<tr.height t)
    (active : tr.cell t r 41=0) (endOp : tr.cell t r 469=1) (nested : tr.cell t r 639=1)
    (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (fs : List Frame)
    (sp : Nat) (root : Label) (state : PreparedControlState (tr.cell t r) s f fs sp root)
    (pf : PFunc) (func : p.funcs[f.fn]?=some pf)
    (code : pf.code[f.pc]?=some .end_) (amount : Nat)
    (charge : PreparedWasmCharge pf f.pc amount) (bounded : amount<u64Bound)
    (fee : preparedExecWord64 (tr.cell t r) 502=amount) (enough : amount≤s.gas.g) :
    ∃ s',step cfg p s=.cont s' ∧
      PreparedControlState (tr.cell t (r+1)) s'
        {f with pc:=f.pc+1,labels:=[root]} fs sp root ∧
      tr.cell t (r+1) 41=0 ∧ tr.cell t (r+1) 42=0 := by
  have enoughRow : preparedExecWord64 (tr.cell t r) 502≤preparedExecWord64 (tr.cell t r) 299 := by
    rw [fee,←state.1.gas];exact enough
  obtain ⟨charged,gas⟩:=prepared_control_gas_success _ tr t r pub prepared_control_literal_gas_source localH nonlast active enoughRow
  have projection:=prepared_control_nested_end_label tr t r pub localH nonlast active charged endOp nested
  obtain ⟨lab,labels⟩ : ∃ lab,f.labels=[lab,root] := by
    rcases state.2 with h|⟨height,_,_,_,labels⟩
    · rw [nested] at h
      exact False.elim ((by decide : (1:Fp)≠0) h.1)
    · exact ⟨_,labels⟩
  obtain ⟨sp',bound,selected,nextSelected⟩:=prepared_control_frame_sp tr t r pub localH nonlast 3 (Or.inl rfl) endOp
  have eq : sp'=sp := by
    have a:=selected sp' bound
    have b:=state.1.selected sp' bound
    rw [if_pos rfl] at a
    rw [a] at b
    by_cases eq:sp'=sp
    · exact eq
    · simp only [eq,ite_false] at b
      exact False.elim ((by decide : (1:Fp)≠0) b)
  subst sp'
  have stack : preparedWasmStack (preparedExecGhostRow (tr.cell t (r+1))) sp=s.stack := by
    rw [state.1.stack]
    apply prepared_wasm_stack_congr
    intro i hi
    exact prepared_control_frame_stack tr t r pub localH nonlast 3 (Or.inl rfl) endOp i (by omega)
  have run:=prepared_control_step_nested_end cfg p s f fs pf amount lab root state.1.frames func code labels charge bounded enough
  let f' : Frame:={f with pc:=f.pc+1,labels:=[root]}
  let s' : St:={s with frames:=f'::fs,gas:={s.gas with g:=s.gas.g-amount}}
  have run' : step cfg p s=.cont s' := by
    simpa only [setFrame,state.1.frames] using run
  refine ⟨s',run',⟨?_,Or.inl ⟨projection.1,rfl⟩⟩,projection.2.2.2.2.1,projection.2.2.2.2.2⟩
  refine ⟨state.1.depth,nextSelected,rfl,?_,stack.symm,?_⟩
  · change f.pc+1=preparedCodeExecPC (tr.cell t (r+1))
    rw [state.1.pc,projection.2.2.2.1]
  · change s.gas.g-amount=preparedExecWord64 (tr.cell t (r+1)) 299
    rw [gas,fee,state.1.gas]

end NearCompression
