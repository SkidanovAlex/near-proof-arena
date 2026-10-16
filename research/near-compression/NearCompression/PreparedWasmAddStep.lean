import NearCompression.PreparedWasmStep

namespace NearCompression
open ZkFormal.Algebra ZkFormal.Air NearSpecV3.Wasm

/-- Canonical unsigned interpretation of the actual Boolean stack columns. -/
theorem prepared_wasm_stack_word_bound (row next pub : Nat → Fp)
    (choices : preparedRowChoices row next pub 0 0) (slot : Nat) (hs : slot<8) :
    preparedStackWord row slot<4294967296 := by
  have lo:=prepared_stack_limb_bound row next pub 0 0 choices slot 0 hs (by decide)
  have hi:=prepared_stack_limb_bound row next pub 0 0 choices slot 1 hs (by decide)
  rw [prepared_stack_limb_eval] at lo hi
  simp only [Nat.mul_zero,Nat.add_zero,Nat.mul_one] at lo hi
  unfold preparedStackWord
  omega

/-- Actual Wasm operand order: the right operand is popped first. -/
theorem prepared_wasm_exec_add (cfg : NearCfg) (p : Prepared) (s : St)
    (f : Frame) (pf : PFunc) (a b : UInt32) (out : Nat)
    (arithmetic : Num.binop 32 0 a.toNat b.toNat=some out) :
    exec cfg p (pushV (pushV s (.i32 a)) (.i32 b)) f pf (.num 0x6A)=
      .cont (setFrame (pushI32 s out) {f with pc:=f.pc+1}) := by
  have numeric : execNum (pushV (pushV s (.i32 a)) (.i32 b)) 0x6A=
      .ok (pushI32 s out) := by
    simp [execNum,instruction_add32_pop_push,arithmetic,pure,Except.pure]
  simp only [exec,numeric]

def PreparedWasmAddProjection (row next : Nat → Fp) : Prop :=
  ∃ pc sp,pc<15 ∧ 2≤sp ∧ sp<9 ∧
    (∀ i,i<16 → row i=if i=pc then 1 else 0) ∧
    (∀ i,i<16 → next i=if i=pc+1 then 1 else 0) ∧
    (∀ i,i<9 → row (16+i)=if i=sp then 1 else 0) ∧
    (∀ i,i<9 → next (16+i)=if i=sp-1 then 1 else 0) ∧
    Num.binop 32 0 (preparedStackWord row (sp-2)) (preparedStackWord row (sp-1))=some (preparedAddResultWord row) ∧
    (∀ slot,slot<8 → preparedStackWord next slot=if slot=sp-2 then preparedAddResultWord row
      else if slot=sp-1 then 0 else preparedStackWord row slot)

/-- Exact real interpreter successor for an addition row. Canonical operand
bounds are derived from the row's Boolean constraints, not assumed lookups. -/
theorem prepared_wasm_add (row next : Nat → Fp) (pub : List Fp)
    (choices : preparedRowChoices row next (fun i=>pub.getD i 0) 0 0)
    (projection : PreparedWasmAddProjection row next)
    (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (fs : List Frame) (pf : PFunc)
    (pc sp : Nat) (state : PreparedWasmState row pub s f fs pc sp)
    (func : p.funcs[f.fn]?=some pf) (code : pf.code[f.pc]?=some (.num 0x6A))
    (metadata : PreparedWasmCharge pf f.pc (preparedFeeValue row pub))
    (bounded : preparedFeeValue row pub<u64Bound)
    (enough : preparedFeeValue row pub≤preparedGasValue row pub)
    (gasNext : preparedGasValue next pub=preparedGasValue row pub-preparedFeeValue row pub) :
    ∃ s',step cfg p s=.cont s' ∧
      s' = { s with
        stack := preparedWasmStack next (sp-1)
        frames := {f with pc:=pc+1}::fs
        gas := {s.gas with g:=preparedGasValue next pub} } ∧
      PreparedWasmState next pub s' {f with pc:=pc+1} fs (pc+1) (sp-1) := by
  rcases state with ⟨hp,hs,currentPC,currentSP,frames,framePC,stack,gas⟩
  rcases projection with ⟨pc',sp',hp',depth,hs',cp,np,cs,ns,arithmetic,words⟩
  have eqpc : pc'=pc := by
    have h:=cp pc hp
    rw [currentPC pc hp] at h
    simp only [ite_true] at h
    by_cases eq : pc=pc'
    · exact eq.symm
    · simp only [eq,ite_false] at h
      exact False.elim ((by decide : (1:Fp)≠0) h)
  have eqsp : sp'=sp := by
    have h:=cs sp hs
    rw [currentSP sp hs] at h
    simp only [ite_true] at h
    by_cases eq : sp=sp'
    · exact eq.symm
    · simp only [eq,ite_false] at h
      exact False.elim ((by decide : (1:Fp)≠0) h)
  subst pc';subst sp'
  obtain ⟨n,rfl⟩:∃ n,sp=n+2:=⟨sp-2,by omega⟩
  simp only [Nat.add_sub_cancel] at arithmetic words ns ⊢
  have minus : n+2-1=n+1 := by omega
  simp only [minus] at arithmetic words ns ⊢
  have aBound:=prepared_wasm_stack_word_bound row next _ choices n (by omega)
  have bBound:=prepared_wasm_stack_word_bound row next _ choices (n+1) (by omega)
  have aNat : (UInt32.ofNat (preparedStackWord row n)).toNat=preparedStackWord row n := by
    exact Nat.mod_eq_of_lt aBound
  have bNat : (UInt32.ofNat (preparedStackWord row (n+1))).toNat=preparedStackWord row (n+1) := by
    exact Nat.mod_eq_of_lt bBound
  have lower : preparedWasmStack next n=preparedWasmStack row n := by
    apply prepared_wasm_stack_congr
    intro i hi
    simpa only [ite_eq_right (by omega : i≠n),ite_eq_right (by omega : i≠n+1)] using words i (by omega)
  have top := words n (by omega)
  simp only [ite_true] at top
  have nextStack : preparedWasmStack next (n+1)=
      (preparedWasmStack row n).push (.i32 (UInt32.ofNat (preparedAddResultWord row))) := by
    simp only [preparedWasmStack,lower,top]
  let base : St := {s with
    stack := preparedWasmStack row n
    gas := {s.gas with g:=preparedGasValue next pub}}
  have stackShape : {s with gas:={s.gas with g:=s.gas.g-preparedFeeValue row pub}}=
      pushV (pushV base (.i32 (UInt32.ofNat (preparedStackWord row n))))
        (.i32 (UInt32.ofNat (preparedStackWord row (n+1)))) := by
    simp only [base,pushV,stack,preparedWasmStack,gas,gasNext]
  have run:=prepared_wasm_step_charge cfg p s f fs pf _ (preparedFeeValue row pub)
    frames func code metadata bounded (by rw [gas];exact enough)
  have execAdd:=prepared_wasm_exec_add cfg p base f pf
    (UInt32.ofNat (preparedStackWord row n)) (UInt32.ofNat (preparedStackWord row (n+1))) (preparedAddResultWord row)
    (by rw [aNat,bNat];exact arithmetic)
  let result : St := {s with
    stack := preparedWasmStack next (n+1)
    frames := {f with pc:=pc+1}::fs
    gas := {s.gas with g:=preparedGasValue next pub}}
  have execution : step cfg p s=.cont result := by
    rw [run,stackShape,execAdd]
    simp only [pushI32,pushV,setFrame,base,frames,result,nextStack,framePC]
  refine ⟨result,execution,rfl,?_,?_,np,ns,rfl,rfl,rfl,rfl⟩ <;> omega

/-- Full local AIR to actual Wasm addition. Prepared code and its charge table
are the remaining provenance premises; selected operands and fee bounds are
proved from the source constraints and canonical public CODE fields. -/
theorem prepared_table_wasm_add (table : Table)
    (gasMiddle gasTail prefixPart transitionMiddle : List Expr) (dead : Nat → Nat → Expr)
    (gasSource : table.constraints=preparedGasSourceConstraints gasMiddle gasTail)
    (transitionSource : table.constraints=preparedAddTransitionSource prefixPart transitionMiddle dead)
    (depthMember : preparedAddDepthSource∈table.constraints)
    (flagMembers : ∀ e∈[preparedFailureInvariantPython,preparedDoneStepPython,preparedFailureStepPython],e∈table.constraints)
    (carryMembers : ∀ i,i<2 → preparedAddCarryPython i∈table.constraints)
    (gasMembers : ∀ i,i<4 → preparedGasStepPython i∈table.constraints)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : ZkFormal.Near.TableLocal table tr t pub) (nonlast : r+1<tr.height t)
    (active : tr.cell t r 25=0)
    (publicBounds : ∀ pc,pc<16 → ∀ limb,limb<4 → (pub.getD (56+10*pc+(6+limb)) 0).toNat<65536)
    (publicAdd : ∀ pc,pc<16 → tr.cell t r pc=1 → ∀ tag,tag<4 →
      pub.getD (56+10*pc+tag) 0=if tag=1 then 1 else 0)
    (enoughGas : preparedFeeValue (tr.cell t r) pub≤preparedGasValue (tr.cell t r) pub)
    (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (fs : List Frame) (pf : PFunc)
    (pc sp : Nat) (state : PreparedWasmState (tr.cell t r) pub s f fs pc sp)
    (func : p.funcs[f.fn]?=some pf) (code : pf.code[f.pc]?=some (.num 0x6A))
    (metadata : PreparedWasmCharge pf f.pc (preparedFeeValue (tr.cell t r) pub)) :
    ∃ s',step cfg p s=.cont s' ∧
      s' = { s with
        stack := preparedWasmStack (tr.cell t (r+1)) (sp-1)
        frames := {f with pc:=pc+1}::fs
        gas := {s.gas with g:=preparedGasValue (tr.cell t (r+1)) pub} } ∧
      PreparedWasmState (tr.cell t (r+1)) pub s' {f with pc:=pc+1} fs (pc+1) (sp-1) := by
  have projected:=prepared_table_local_add table gasMiddle gasTail prefixPart transitionMiddle dead
    gasSource transitionSource depthMember flagMembers carryMembers gasMembers
    tr t r pub localH nonlast active publicBounds publicAdd enoughGas
  have choices:=prepared_table_row_choices table gasMiddle gasTail gasSource
    tr t r pub localH (by omega) (tr.cell t (r+1))
  have feeBounds:=prepared_gas_public_fee_bounds (tr.cell t r) (tr.cell t (r+1)) pub 0 0 choices publicBounds
  have bounded : preparedFeeValue (tr.cell t r) pub<u64Bound :=
    prepared_gas_word_bound _ feeBounds
  exact prepared_wasm_add _ _ pub choices projected.2.2.2.2 cfg p s f fs pf pc sp
    state func code metadata bounded enoughGas projected.2.2.2.1

end NearCompression
