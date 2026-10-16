import NearCompression.PreparedLocalsArray
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpecV3.Wasm
set_option maxRecDepth 65536

private theorem ghost_bits (row : Nat→Fp) (n base : Nat) (high : 16≤base) :
    (instructionBitExpr base n).evalWith (instructionAddEnv (preparedExecGhostRow row))=
      (instructionBitExpr (base+16) n).evalWith (instructionAddEnv row) := by
  induction n generalizing base with
  | zero => rfl
  | succ n ih =>
    simp only [instructionBitExpr,Expr.evalWith,instructionAddEnv]
    have ghost : preparedExecGhostRow row base=row (base+16) := by
      simp only [preparedExecGhostRow,ite_eq_right (by omega : ¬base<16)]
    rw [ghost]
    have h := ih (base+1) (by omega)
    have e : base+1+16=base+16+1 := by omega
    rw [e] at h
    exact congrArg (fun x => row (base+16)+Fp.ofNat 2*x) h

theorem prepared_locals_stack_word (row : Nat→Fp) (slot : Nat) :
    preparedStackWord (preparedExecGhostRow row) slot=preparedLocalsStackWord row slot := by
  unfold preparedStackWord preparedLocalsStackWord preparedCodeLimb
  rw [ghost_bits row 16 (27+32*slot) (by omega),ghost_bits row 16 (27+32*slot+16) (by omega)]
  have lo : 27+32*slot+16=43+32*slot := by omega
  have hi : 27+32*slot+16+16=59+32*slot := by omega
  rw [hi,lo]

/-- Actual set/tee step, with successor locals obtained from literal AIR
constraints. Remaining next-row PC/SP/stack/gas consistency is not assumed or
claimed by this intermediate frame-write interface. -/
theorem prepared_locals_frame_write (tee : Bool) (count : Nat)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedLocalsLiteralExecTable count) tr t pub)
    (nonlast : r+1<tr.height t) (active : tr.cell t r 41=0) (charged : tr.cell t r 430=0)
    (writeOp : tr.cell t r 684+tr.cell t r 685=1)
    (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (fs : List Frame)
    (sp index amount : Nat) (root : Label)
    (state : PreparedLocalsState (tr.cell t r) s f fs sp count root)
    (positive : 0<sp) (valid : index<count)
    (selected : ∀j,j<4 → tr.cell t r (814+j)=if j=index then 1 else 0)
    (pf : PFunc) (func : p.funcs[f.fn]?=some pf)
    (code : pf.code[f.pc]?=some (if tee then .localTee index else .localSet index))
    (charge : PreparedWasmCharge pf f.pc amount) (bounded : amount<u64Bound) (enough : amount≤s.gas.g) :
    step cfg p s=.cont {s with
      stack:=if tee then s.stack else s.stack.pop
      frames:={f with pc:=f.pc+1,locals:=preparedLocalsArray (tr.cell t (r+1)) count}::fs
      gas:={s.gas with g:=s.gas.g-amount}} := by
  have update:=prepared_locals_array_write count state.2.1 tr t r pub localH nonlast active charged writeOp
    index sp valid state.1.1.depth positive selected state.1.1.selected
  rw [←state.2.2] at update
  obtain ⟨n,eq⟩:∃n,sp=n+1 := ⟨sp-1,by omega⟩
  subst sp
  simp only [Nat.add_sub_cancel] at update
  have stack : s.stack=(preparedWasmStack (preparedExecGhostRow (tr.cell t r)) n).push
      (.i32 (UInt32.ofNat (preparedLocalsStackWord (tr.cell t r) n))) := by
    rw [state.1.1.stack]
    simp only [preparedWasmStack,prepared_locals_stack_word]
  rw [prepared_wasm_step_charge cfg p s f fs pf _ amount state.1.1.frames func code charge bounded enough]
  cases tee
  · simp only [Bool.false_eq_true,ite_false]
    rw [prepared_locals_exec_set cfg p _ f pf index _ _ (show
      ({s with gas:={s.gas with g:=s.gas.g-amount}}:St).stack=_ from stack)]
    rw [←update]
    simp only [setFrame,state.1.1.frames,stack,Array.pop_push]
  · simp only [ite_true]
    rw [prepared_locals_exec_tee cfg p _ f pf index _ _ (show
      ({s with gas:={s.gas with g:=s.gas.g-amount}}:St).stack=_ from stack)]
    rw [←update]
    simp only [setFrame,state.1.1.frames]

/-- Nonwriting instructions, failure, and padding preserve the locals array
whenever their actual write selectors evaluate to zero. -/
theorem prepared_locals_array_preserved (count : Nat) (bounded : count≤4)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedLocalsLiteralExecTable count) tr t pub)
    (nonlast : r+1<tr.height t)
    (noWrite : ∀slot,slot<count → (preparedLocalsWrite slot).eval tr t r pub=0) :
    preparedLocalsArray (tr.cell t (r+1)) count=preparedLocalsArray (tr.cell t r) count := by
  unfold preparedLocalsArray
  apply congrArg List.toArray
  apply List.map_congr_left
  intro slot hslot
  have hs:=List.mem_range.mp hslot
  have low:=prepared_locals_limb_step count tr t r pub localH nonlast slot 0 (by omega) (by decide)
  have high:=prepared_locals_limb_step count tr t r pub localH nonlast slot 1 (by omega) (by decide)
  rw [noWrite slot hs] at low high
  simp only [Nat.mul_zero,Nat.add_zero,Nat.mul_one] at low high
  have lo : preparedCodeLimb (tr.cell t (r+1)) (686+32*slot)=preparedCodeLimb (tr.cell t r) (686+32*slot) := by grind
  have hi : preparedCodeLimb (tr.cell t (r+1)) (702+32*slot)=preparedCodeLimb (tr.cell t r) (702+32*slot) := by
    have eq : 686+32*slot+16=702+32*slot := by omega
    rw [eq] at high;grind
  simp only [preparedLocalsWord,lo,hi]
end NearCompression
