import NearCompression.PreparedControlStep
import NearCompression.PreparedControlLiteral

set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpecV3.Wasm

def preparedControlBitSum (base : Nat) : Expr :=
  preparedBalancedSum (fun bit=>.col (base+bit) false) 5 0

def preparedControlCondition : Expr :=
  preparedBalancedSum (fun i=>.mul (.col (32+(i+1)) false) (preparedControlBitSum (43+32*i))) 3 0

def preparedControlConditionInverse : Expr :=
  .add (.mul preparedControlCondition (.col 682 false)) (.neg (.col 681 false))

def preparedControlConditionZero : Expr :=
  .add (.mul preparedControlCondition (.add (.const 1) (.neg (.col 681 false)))) (.neg (.const 0))

theorem prepared_control_bit_sum (row next pub : Nat → Fp) (first last : Fp) (base : Nat) :
    (preparedControlBitSum base).evalWith (preparedRowEnv row next pub first last)=
    preparedFieldSum 32 (fun i=>row (base+i)) := by
  simp only [preparedControlBitSum,preparedBalancedSum,preparedFieldSum,Expr.evalWith,
    preparedRowEnv,Nat.reducePow,Nat.reduceAdd,Nat.add_zero]
  grind

theorem prepared_control_condition_selected (row next pub : Nat → Fp) (first last : Fp)
    (sp : Nat) (hsp : sp<9) (positive : 0<sp)
    (selected : ∀ i,i<9 → row (32+i)=if i=sp then 1 else 0) :
    preparedControlCondition.evalWith (preparedRowEnv row next pub first last)=
    (preparedControlBitSum (43+32*(sp-1))).evalWith (preparedRowEnv row next pub first last) := by
  have cases : sp=1 ∨ sp=2 ∨ sp=3 ∨ sp=4 ∨ sp=5 ∨ sp=6 ∨ sp=7 ∨ sp=8 := by omega
  simp only [preparedControlCondition,preparedBalancedSum,Nat.reducePow,Nat.reduceAdd,Expr.evalWith,preparedRowEnv]
  have h1:=selected 1 (by decide)
  have h2:=selected 2 (by decide)
  have h3:=selected 3 (by decide)
  have h4:=selected 4 (by decide)
  have h5:=selected 5 (by decide)
  have h6:=selected 6 (by decide)
  have h7:=selected 7 (by decide)
  have h8:=selected 8 (by decide)
  rcases cases with h|h|h|h|h|h|h|h <;> subst sp
  all_goals simp only [Nat.reduceSub,Nat.reduceMul,Nat.reduceAdd,Nat.reduceEqDiff,ite_true,ite_false] at h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  all_goals rw [h1,h2,h3,h4,h5,h6,h7,h8]
  all_goals grind

theorem prepared_control_inverse_zero (q inverse flag : Fp)
    (product : q*inverse+ -flag=0) (zero : q*((1:Fp)+ -flag)+ -(0:Fp)=0) :
    flag=0 ↔ q=0 := by
  constructor <;> intro h <;> grind

theorem prepared_control_bit_sum_zero (row next pub : Nat → Fp) (first last : Fp) (base : Nat)
    (boolean : ∀ i,i<32 → (row (base+i)).toNat≤1) :
    (preparedControlBitSum base).evalWith (preparedRowEnv row next pub first last)=0 ↔
    ∀ i,i<32 → row (base+i)=0 := by
  rw [prepared_control_bit_sum]
  have bound:=prepared_sum_nat_bound 32 (fun i=>row (base+i)) (by decide) boolean
  constructor
  · intro zero i hi
    have nz:=congrArg Fp.toNat zero
    rw [bound.1] at nz
    apply Fp.ext
    exact prepared_nat_sum_zero 32 _ nz i hi
  · intro zero
    exact prepared_sum_zero 32 _ zero


/-- Bounded Boolean Horner reconstruction is zero exactly when all source
bits vanish; the no-wrap step uses actual Fp.toNat arithmetic. -/
theorem prepared_control_horner_zero (row : Nat → Fp) (n base : Nat) (hn : n≤16)
    (boolean : ∀ i,i<n → (row (base+i)).toNat≤1) :
    (instructionBitExpr base n).evalWith (instructionAddEnv row)=0 ↔
    ∀ i,i<n → row (base+i)=0 := by
  induction n generalizing base with
  | zero => exact ⟨by intro h i hi;omega,by intro h;rfl⟩
  | succ n ih =>
    have tailbits : ∀ i,i<n → (row (base+1+i)).toNat≤1 := by
      intro i hi
      simpa only [Nat.add_assoc,Nat.add_comm 1 i] using boolean (i+1) (by omega)
    have tail:=instruction_bit_expr_bound row n (base+1) (by omega) tailbits
    have hn2 : n≤16 := by omega
    have power : 2^n≤65536:=Nat.pow_le_pow_right (by decide) hn2
    have head:=boolean 0 (by omega)
    simp only [Nat.add_zero] at head
    have mulBound : 2*((instructionBitExpr (base+1) n).evalWith (instructionAddEnv row)).toNat<ZkFormal.Algebra.P := by
      unfold ZkFormal.Algebra.P;omega
    have sumBound : (row base).toNat+2*((instructionBitExpr (base+1) n).evalWith (instructionAddEnv row)).toNat<ZkFormal.Algebra.P := by
      unfold ZkFormal.Algebra.P;omega
    constructor
    · intro zero
      have nz:=congrArg Fp.toNat zero
      change (Fp.add (row base) (Fp.mul (Fp.ofNat 2) ((instructionBitExpr (base+1) n).evalWith (instructionAddEnv row)))).toNat=0 at nz
      simp only [Fp.toNat_add,Fp.toNat_mul,Fp.toNat_ofNat] at nz
      change ((row base).toNat+(2*((instructionBitExpr (base+1) n).evalWith (instructionAddEnv row)).toNat)%ZkFormal.Algebra.P)%ZkFormal.Algebra.P=0 at nz
      rw [Nat.mod_eq_of_lt mulBound,Nat.mod_eq_of_lt sumBound] at nz
      have hz : row base=0 := Fp.ext (by change (row base).toNat=0;omega)
      have tz : (instructionBitExpr (base+1) n).evalWith (instructionAddEnv row)=0 := Fp.ext (by change _=0;omega)
      have zeros:=(ih (base+1) (by omega) tailbits).mp tz
      intro i hi
      cases i with
      | zero=>simpa only [Nat.add_zero] using hz
      | succ i=>simpa only [Nat.add_assoc,Nat.add_comm 1 i] using zeros i (by omega)
    · intro zeros
      have hz:=zeros 0 (by omega)
      simp only [Nat.add_zero] at hz
      have tz:=(ih (base+1) (by omega) tailbits).mpr (by
        intro i hi
        simpa only [Nat.add_assoc,Nat.add_comm 1 i] using zeros (i+1) (by omega))
      change row base+Fp.ofNat 2*(instructionBitExpr (base+1) n).evalWith (instructionAddEnv row)=0
      rw [hz,tz];grind

theorem prepared_control_stack_word (row : Nat → Fp) (slot : Nat) :
    preparedExecStackWord row slot=(preparedCodeLimb row (43+32*slot)).toNat+
      65536*(preparedCodeLimb row (43+32*slot+16)).toNat := by
  simp only [preparedExecStackWord,preparedStackWord,preparedCodeLimb]
  rw [prepared_exec_ghost_bits _ 16 _ (by omega),prepared_exec_ghost_bits _ 16 _ (by omega)]
  rw [show 27+32*slot+16=43+32*slot by omega]

theorem prepared_control_stack_zero (row : Nat → Fp) (slot : Nat)
    (boolean : ∀ i,i<32 → (row (43+32*slot+i)).toNat≤1) :
    preparedExecStackWord row slot=0 ↔ ∀ i,i<32 → row (43+32*slot+i)=0 := by
  rw [prepared_control_stack_word]
  have low:=prepared_control_horner_zero row 16 (43+32*slot) (by decide) (fun i hi=>boolean i (by omega))
  have high:=prepared_control_horner_zero row 16 (43+32*slot+16) (by decide) (by
    intro i hi
    simpa only [Nat.add_assoc] using boolean (16+i) (by omega))
  change preparedCodeLimb row (43+32*slot)=0 ↔ _ at low
  change preparedCodeLimb row (43+32*slot+16)=0 ↔ _ at high
  constructor
  · intro zero
    have lo : preparedCodeLimb row (43+32*slot)=0 := Fp.ext (by change _=0;omega)
    have hi : preparedCodeLimb row (43+32*slot+16)=0 := Fp.ext (by change _=0;omega)
    intro i bound
    by_cases small:i<16
    · exact low.mp lo i small
    · have h:=high.mp hi (i-16) (by omega)
      simpa only [show 43+32*slot+16+(i-16)=43+32*slot+i by omega] using h
  · intro zero
    have lo:=low.mpr (fun i hi=>zero i (by omega))
    have hi:=high.mpr (by intro i hi;simpa only [Nat.add_assoc] using zero (16+i) (by omega))
    rw [lo,hi];rfl

structure PreparedControlConditionSource (table : Table) : Prop where
  boolean : ∀ i,i<682 → preparedGasBoolean i∈table.constraints
  inverse : preparedControlConditionInverse∈table.constraints
  zero : preparedControlConditionZero∈table.constraints

/-- Actual polynomial residuals determine the Boolean branch selector from
the selected, range-constrained stack word. No selected operand value is
supplied; only the stack-height one-hot relation is the reusable interface. -/
theorem prepared_control_condition_sound (table : Table) (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal table tr t pub) (hr : r<tr.height t) (source : PreparedControlConditionSource table)
    (sp : Nat) (hsp : sp<9) (positive : 0<sp)
    (selected : ∀ i,i<9 → tr.cell t r (32+i)=if i=sp then 1 else 0) :
    (tr.cell t r 681).toNat≤1 ∧
    (tr.cell t r 681=0 ↔ preparedExecStackWord (tr.cell t r) (sp-1)=0) := by
  have boolean (i : Nat) (hi : i<682) : (tr.cell t r i).toNat≤1 := by
    have h:=localH.constr r hr _ (source.boolean i hi)
    change (tr.cell t r i*(tr.cell t r i+ -(1:Fp)))+ -(0:Fp)=0 at h
    apply instruction_add_boolean_bound
    grind
  have inv:=localH.constr r hr _ source.inverse
  have annihilator:=localH.constr r hr _ source.zero
  let row:=tr.cell t r
  let next:=tr.cell t ((r+1)%tr.height t)
  let fields:=fun i=>pub.getD i 0
  let q:=preparedControlCondition.evalWith (preparedRowEnv row next fields 0 0)
  have inv' : q*row 682+ -row 681=0 := inv
  have zero' : q*((1:Fp)+ -row 681)+ -(0:Fp)=0 := annihilator
  have chosen:=prepared_control_condition_selected row next fields 0 0 sp hsp positive selected
  have bits : ∀ i,i<32 → (row (43+32*(sp-1)+i)).toNat≤1 := by
    intro i hi;exact boolean _ (by omega)
  refine ⟨boolean 681 (by decide),?_⟩
  change row 681=0 ↔ _
  rw [prepared_control_inverse_zero q (row 682) (row 681) inv' zero']
  change preparedControlCondition.evalWith (preparedRowEnv row next fields 0 0)=0 ↔ _
  rw [chosen,prepared_control_bit_sum_zero row next fields 0 0 _ bits]
  exact (prepared_control_stack_zero row (sp-1) bits).symm

private theorem control_boolean_at : ∀ i:Fin 682,
    preparedControlLiteralExec[i.val]'(by change _<870;omega)=preparedGasBoolean i.val := by decide

theorem prepared_control_literal_condition_source : PreparedControlConditionSource preparedControlLiteralExecTable := by
  refine ⟨?_,?_,?_⟩
  · intro i hi
    have h:=List.getElem_mem (l:=preparedControlLiteralExec) (n:=i) (by change _<870;omega)
    rw [control_boolean_at ⟨i,hi⟩] at h
    exact h
  · exact List.getElem_mem (l:=preparedControlLiteralExec) (n:=686) (by decide)
  · exact List.getElem_mem (l:=preparedControlLiteralExec) (n:=687) (by decide)

theorem prepared_control_literal_onehot (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal preparedControlLiteralExecTable tr t pub) (hr : r<tr.height t) :
    ∃ sp,sp<9 ∧ ∀ i,i<9 → tr.cell t r (32+i)=if i=sp then 1 else 0 := by
  apply prepared_onehot 9 32 (tr.cell t r) (by decide)
  · intro i hi
    have h:=localH.constr r hr _ (prepared_control_literal_condition_source.boolean (32+i) (by omega))
    change (tr.cell t r (32+i)*(tr.cell t r (32+i)+ -(1:Fp)))+ -(0:Fp)=0 at h
    apply instruction_add_boolean_bound
    grind
  · have member : preparedExecSPChoice∈preparedControlLiteralExecTable.constraints:=
      List.getElem_mem (l:=preparedControlLiteralExec) (n:=682) (by decide)
    have h:=localH.constr r hr _ member
    simp only [preparedExecSPChoice,preparedBalancedSum,Expr.eval,Expr.evalWith,rowEnv,
      Nat.reduceAdd,Nat.reducePow,Bool.false_eq_true,ite_false] at h
    simp only [preparedFieldSum,Nat.reduceAdd]
    try simp only [←Fp.ofNat_def] at h
    grind

/-- Literal source certificate removes the supplied stack-selector interface:
the actual row determines a unique live height, and any nonempty row's
condition selector agrees with its actual top i32 word. -/
theorem prepared_control_literal_condition (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal preparedControlLiteralExecTable tr t pub) (hr : r<tr.height t) :
    ∃ sp,sp<9 ∧ (∀ i,i<9 → tr.cell t r (32+i)=if i=sp then 1 else 0) ∧
      (0<sp → (tr.cell t r 681).toNat≤1 ∧
        (tr.cell t r 681=0 ↔ preparedExecStackWord (tr.cell t r) (sp-1)=0)) := by
  obtain ⟨sp,hs,selected⟩:=prepared_control_literal_onehot tr t r pub localH hr
  exact ⟨sp,hs,selected,fun positive=>prepared_control_condition_sound _ tr t r pub localH hr
    prepared_control_literal_condition_source sp hs positive selected⟩

end NearCompression
