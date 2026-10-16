import NearCompression.PreparedStackCases
import NearCompression.InstructionAddStep

namespace NearCompression
open ZkFormal.Algebra ZkFormal.Air NearSpecV3.Wasm

/-- Bottom-to-top stack, with the same ordering as actual `pushV`. -/
def preparedWasmStack (row : Nat → Fp) : Nat → Array Val
  | 0 => #[]
  | n+1 => (preparedWasmStack row n).push (.i32 (UInt32.ofNat (preparedStackWord row n)))

/-- Interpretation of the bounded row inside an actual interpreter state.
The frame and untouched state fields are genuine Wasm values. This relation
restricts the entire live stack to the bounded i32 slice. -/
def PreparedWasmState (row : Nat → Fp) (pub : List Fp)
    (s : St) (f : Frame) (fs : List Frame) (pc sp : Nat) : Prop :=
  pc<16 ∧ sp<9 ∧
  (∀ i,i<16 → row i=if i=pc then 1 else 0) ∧
  (∀ i,i<9 → row (16+i)=if i=sp then 1 else 0) ∧
  s.frames=f::fs ∧ f.pc=pc ∧ s.stack=preparedWasmStack row sp ∧
  s.gas.g=preparedGasValue row pub

/-- Actual prepared range-charge metadata. An absent charge point has zero
AIR fee; a present point has its genuine constant fee and no linear term. -/
def PreparedWasmCharge (pf : PFunc) (pc amount : Nat) : Prop :=
  (pf.gas[pc]?=some none ∧ amount=0) ∨
  ∃ k fee,pf.gas[pc]?=some (some (k,fee)) ∧ fee.l=0 ∧ fee.c=amount

theorem prepared_wasm_stack_congr (row next : Nat → Fp) (n : Nat)
    (same : ∀ i,i<n → preparedStackWord next i=preparedStackWord row i) :
    preparedWasmStack next n=preparedWasmStack row n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [preparedWasmStack,ih (fun i hi => same i (by omega)),same n (by omega)]

theorem prepared_wasm_step_charge (cfg : NearCfg) (p : Prepared)
    (s : St) (f : Frame) (fs : List Frame) (pf : PFunc) (ins : Instr)
    (amount : Nat) (frames : s.frames=f::fs) (func : p.funcs[f.fn]?=some pf)
    (code : pf.code[f.pc]?=some ins) (metadata : PreparedWasmCharge pf f.pc amount)
    (bounded : amount<u64Bound) (enough : amount≤s.gas.g) :
    step cfg p s=exec cfg p {s with gas:={s.gas with g:=s.gas.g-amount}} f pf ins := by
  rcases metadata with ⟨gas,zero⟩ | ⟨k,fee,gas,linear,cost⟩
  · subst amount
    simp only [Nat.sub_zero]
    have unchanged : {s with gas := {s.gas with g := s.gas.g}} = s := rfl
    rw [unchanged]
    simp only [step,frames,func,code,gas]
  · have charged:=instruction_add32_charge_success s fee
      (if k=IK.linear then topCount s else 0)
      (by simpa only [linear,cost,Nat.mul_zero,Nat.zero_add] using bounded)
      (by simpa only [linear,cost,Nat.mul_zero,Nat.zero_add] using enough)
    simp only [linear,cost,Nat.mul_zero,Nat.zero_add] at charged
    simp only [step,frames,func,code,gas,charged]

/-- The const/drop projection already derived from the source table has actual
stack push/pop meaning; dead snapshot slots are excluded from the live stack. -/
theorem prepared_wasm_stack_projection (push : Bool) (row next pub : Nat → Fp)
    (sp : Nat) (hs : sp<9) (depth : if push then sp<8 else 1≤sp)
    (words : ∀ slot,slot<8 → preparedStackWord next slot=
      if push then (if slot=sp then preparedImmediateWord row next pub else preparedStackWord row slot)
      else (if slot+1=sp then 0 else preparedStackWord row slot)) :
    preparedWasmStack next (if push then sp+1 else sp-1)=
      if push then (preparedWasmStack row sp).push (.i32 (UInt32.ofNat (preparedImmediateWord row next pub)))
      else (preparedWasmStack row sp).pop := by
  cases push
  · simp only [Bool.false_eq_true,ite_false] at depth words ⊢
    obtain ⟨n,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (by omega : sp≠0)
    simp only [preparedWasmStack,Array.pop_push]
    apply prepared_wasm_stack_congr
    intro i hi
    simpa only [ite_eq_right (by omega : i+1≠n+1)] using words i (by omega)
  · simp only [ite_true] at depth words ⊢
    simp only [preparedWasmStack]
    rw [prepared_wasm_stack_congr row next sp (by
      intro i hi
      simpa only [ite_eq_right (by omega : i≠sp)] using words i (by omega))]
    rw [words sp depth,ite_eq_left rfl]

/-- Exact actual const/drop step from the AIR projection. The only execution
context premises bind real prepared code and its optional range-charge point.
No operand lookup or per-instruction gas model is assumed. -/
theorem prepared_wasm_const_drop (push : Bool) (row next : Nat → Fp) (pub : List Fp)
    (projection : PreparedStackProjection push row next (fun i => pub.getD i 0))
    (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (fs : List Frame) (pf : PFunc)
    (pc sp : Nat) (state : PreparedWasmState row pub s f fs pc sp)
    (func : p.funcs[f.fn]?=some pf)
    (code : pf.code[f.pc]?=some (if push then .i32Const (UInt32.ofNat (preparedImmediateWord row next (fun i => pub.getD i 0))) else .drop))
    (metadata : PreparedWasmCharge pf f.pc (preparedFeeValue row pub))
    (bounded : preparedFeeValue row pub<u64Bound)
    (enough : preparedFeeValue row pub≤preparedGasValue row pub)
    (gasNext : preparedGasValue next pub=preparedGasValue row pub-preparedFeeValue row pub) :
    ∃ s',step cfg p s=.cont s' ∧
      s' = { s with
        stack := preparedWasmStack next (if push then sp+1 else sp-1)
        frames := {f with pc:=pc+1}::fs
        gas := {s.gas with g:=preparedGasValue next pub} } ∧
      PreparedWasmState next pub s' {f with pc:=pc+1} fs (pc+1) (if push then sp+1 else sp-1) := by
  rcases state with ⟨hp,hs,currentPC,currentSP,frames,framePC,stack,gas⟩
  rcases projection with ⟨pc',sp',hp',hs',depth,cp,np,cs,ns,words⟩
  have eqpc : pc'=pc := by
    have h:=cp pc hp
    rw [currentPC pc hp] at h
    simp only [ite_true] at h
    by_cases eq : pc=pc'
    · exact eq.symm
    · simp only [eq,ite_false] at h
      exact False.elim ((by decide : (1 : Fp) ≠ 0) h)
  have eqsp : sp'=sp := by
    have h:=cs sp hs
    rw [currentSP sp hs] at h
    simp only [ite_true] at h
    by_cases eq : sp=sp'
    · exact eq.symm
    · simp only [eq,ite_false] at h
      exact False.elim ((by decide : (1 : Fp) ≠ 0) h)
  subst pc';subst sp'
  have stk:=prepared_wasm_stack_projection push row next (fun i=>pub.getD i 0) sp hs depth words
  have run:=prepared_wasm_step_charge cfg p s f fs pf _ (preparedFeeValue row pub)
    frames func code metadata bounded (by rw [gas];exact enough)
  let result : St := { s with
    stack := preparedWasmStack next (if push then sp+1 else sp-1)
    frames := {f with pc:=pc+1}::fs
    gas := {s.gas with g:=preparedGasValue next pub} }
  have execution : step cfg p s=.cont result := by
    rw [run]
    cases push <;> simp only [Bool.false_eq_true,ite_false,ite_true] at stk ⊢
    · simp only [exec,popV,setFrame,frames]
      simp only [result,Bool.false_eq_true,ite_false,ite_true,stk,stack,framePC,gas,gasNext]
    · simp only [exec,pushV,setFrame,frames]
      simp only [result,Bool.false_eq_true,ite_false,ite_true,stk,stack,framePC,gas,gasNext]
  refine ⟨result,execution,rfl,?_,?_,np,ns,rfl,rfl,rfl,rfl⟩
  · omega
  · cases push <;> simp only [Bool.false_eq_true,ite_false,ite_true] at depth ⊢ <;> omega

/-- Direct source-table-to-interpreter composition. Fee boundedness and the
operand/stack projection are discharged from actual local constraints and the
canonical public CODE limbs. Prepared-code provenance remains explicit. -/
theorem prepared_table_wasm_const_drop (push : Bool) (table : Table)
    (source : PreparedTerminalSource table)
    (prefixPart middle : List Expr) (dead : Nat → Nat → Expr)
    (transitionSource : table.constraints=preparedAddTransitionSource prefixPart middle dead)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : ZkFormal.Near.TableLocal table tr t pub) (nonlast : r+1<tr.height t)
    (active : tr.cell t r 25=0)
    (publicBounds : ∀ pc,pc<16 → ∀ limb,limb<4 → (pub.getD (56+10*pc+(6+limb)) 0).toNat<65536)
    (publicImmediates : ∀ pc,pc<16 → ∀ limb,limb<2 → (pub.getD (56+10*pc+(4+limb)) 0).toNat<65536)
    (publicOp : ∀ pc,pc<16 → tr.cell t r pc=1 → ∀ tag,tag<4 →
      pub.getD (56+10*pc+tag) 0=if tag=(if push then 0 else 2) then 1 else 0)
    (enoughGas : preparedFeeValue (tr.cell t r) pub≤preparedGasValue (tr.cell t r) pub)
    (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (fs : List Frame) (pf : PFunc)
    (pc sp : Nat) (state : PreparedWasmState (tr.cell t r) pub s f fs pc sp)
    (func : p.funcs[f.fn]?=some pf)
    (code : pf.code[f.pc]?=some (if push then .i32Const (UInt32.ofNat
      (preparedImmediateWord (tr.cell t r) (tr.cell t (r+1)) (fun i => pub.getD i 0))) else .drop))
    (metadata : PreparedWasmCharge pf f.pc (preparedFeeValue (tr.cell t r) pub)) :
    ∃ s',step cfg p s=.cont s' ∧
      s' = { s with
        stack := preparedWasmStack (tr.cell t (r+1)) (if push then sp+1 else sp-1)
        frames := {f with pc:=pc+1}::fs
        gas := {s.gas with g:=preparedGasValue (tr.cell t (r+1)) pub} } ∧
      PreparedWasmState (tr.cell t (r+1)) pub s' {f with pc:=pc+1} fs
        (pc+1) (if push then sp+1 else sp-1) := by
  have projected:=prepared_table_const_drop push table source prefixPart middle dead
    transitionSource tr t r pub localH nonlast active publicBounds publicImmediates publicOp enoughGas
  have choices:=prepared_table_row_choices table source.gasMiddle source.gasTail
    source.gasSource tr t r pub localH (by omega) (tr.cell t (r+1))
  have feeBounds:=prepared_gas_public_fee_bounds (tr.cell t r) (tr.cell t (r+1)) pub 0 0 choices publicBounds
  have bounded : preparedFeeValue (tr.cell t r) pub<u64Bound :=
    prepared_gas_word_bound _ feeBounds
  exact prepared_wasm_const_drop push _ _ pub projected.2.2.2.2.2 cfg p s f fs pf pc sp
    state func code metadata bounded enoughGas projected.2.2.2.1

end NearCompression
