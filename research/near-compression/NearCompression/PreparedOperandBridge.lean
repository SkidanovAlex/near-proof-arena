import NearCompression.PreparedFunctionRow
import NearCompression.PreparedGasBorrow

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra NearSpecV3.Wasm

def preparedOperandTermPython (left : Bool) (limb i : Nat) : Expr :=
  .mul (.col (16+(i+2)) false)
    (preparedGasBits (27+32*(if left then i else i+1)+16*limb))
def preparedOperandPython (left : Bool) (limb : Nat) : Expr :=
  let term := preparedOperandTermPython left limb
  .add (preparedBalancedSum term 2 0) (.add (.add (term 4) (term 5)) (term 6))
def preparedSuccessfulAdd : Expr :=
  .mul (.mul (.add (.const 1) (.neg (.col 25 false)))
    (.add (.const 1) (.neg (.col 414 false)))) (preparedFetchPython 1)
def preparedAddCarryPython (limb : Nat) : Expr :=
  .mul preparedSuccessfulAdd
    (.add (.add (.add (preparedOperandPython true limb) (preparedOperandPython false limb))
      (if limb=0 then .const 0 else .col 447 false))
      (.neg (.add (preparedGasBits (415+16*limb)) (.mul (.const 65536) (.col (447+limb) false)))))

theorem prepared_bits_row_horner (row next pub : Nat → Fp) (first last : Fp) (base : Nat) :
    (preparedGasBits base).evalWith (preparedRowEnv row next pub first last)=
    (instructionBitExpr base 16).evalWith (instructionAddEnv row) := by
  simp only [preparedGasBits,preparedGasSumTree,instructionBitExpr,Expr.evalWith,
    preparedRowEnv,instructionAddEnv,Nat.reduceAdd,Nat.reducePow,Nat.add_zero,Nat.add_assoc]
  simp only [←Fp.ofNat_def]
  grind

theorem prepared_operand_python_eval (row next pub : Nat → Fp) (first last : Fp)
    (left : Bool) (limb : Nat) :
    (preparedOperandPython left limb).evalWith (preparedRowEnv row next pub first last)=
    (preparedOperand left limb).evalWith (preparedRowEnv row next pub first last) := by
  have bit (slot : Nat) :
      (preparedGasBits (27+32*slot+16*limb)).evalWith (preparedRowEnv row next pub first last)=
      (preparedStackLimb slot limb).evalWith (preparedRowEnv row next pub first last) := by
    rw [prepared_bits_row_horner,prepared_stack_limb_eval]
  simp only [preparedOperandPython,preparedBalancedSum,preparedOperandTermPython,preparedOperand,
    preparedExprSum,Nat.reducePow,Nat.reduceAdd,Expr.evalWith]
  simp only [bit]
  change _ = _
  simp only [preparedRowEnv,←Fp.ofNat_def]
  grind

def preparedStackWord (row : Nat → Fp) (slot : Nat) : Nat :=
  ((instructionBitExpr (27+32*slot) 16).evalWith (instructionAddEnv row)).toNat +
    65536*((instructionBitExpr (27+32*slot+16) 16).evalWith (instructionAddEnv row)).toNat

def preparedAddResultWord (row : Nat → Fp) : Nat :=
  ((instructionBitExpr 415 16).evalWith (instructionAddEnv row)).toNat +
    65536*((instructionBitExpr 431 16).evalWith (instructionAddEnv row)).toNat

/-- Exact selected stack operands, with no lookup-equality premise. -/
theorem prepared_operand_python_selected (row next pub : Nat → Fp) (first last : Fp)
    (sp : Nat) (hsp : sp<9) (enough : 2≤sp)
    (onehot : ∀ i,i<9 → row (16+i)=if i=sp then 1 else 0)
    (left : Bool) (limb : Nat) :
    (preparedOperandPython left limb).evalWith (preparedRowEnv row next pub first last)=
    (instructionBitExpr (27+32*(if left then sp-2 else sp-1)+16*limb) 16).evalWith (instructionAddEnv row) := by
  rw [prepared_operand_python_eval,prepared_operand_selected row next pub first last sp hsp enough onehot,
    prepared_stack_limb_eval]


theorem prepared_add_pair_binop (a0 a1 b0 b1 o0 o1 c0 c1 : Fp)
    (ha0 : a0.toNat<65536) (ha1 : a1.toNat<65536)
    (hb0 : b0.toNat<65536) (hb1 : b1.toNat<65536)
    (ho0 : o0.toNat<65536) (ho1 : o1.toNat<65536)
    (hc0 : c0.toNat≤1) (hc1 : c1.toNat≤1)
    (e0 : a0+b0+0=o0+65536*c0) (e1 : a1+b1+c0=o1+65536*c1) :
    Num.binop 32 0 (a0.toNat+65536*a1.toNat) (b0.toNat+65536*b1.toNat)=some (o0.toNat+65536*o1.toNat) := by
  have h0:=instruction_add_limb_sound a0 b0 0 o0 c0 ha0 hb0 (by decide) ho0 hc0 e0
  have h1:=instruction_add_limb_sound a1 b1 c0 o1 c1 ha1 hb1 hc0 ho1 hc1 e1
  change a0.toNat+b0.toNat+0=o0.toNat+65536*c0.toNat at h0
  have total : a0.toNat+65536*a1.toNat+(b0.toNat+65536*b1.toNat)=
      o0.toNat+65536*o1.toNat+4294967296*c1.toNat := by omega
  have bound : o0.toNat+65536*o1.toNat<4294967296 := by omega
  simp only [Num.binop,total]
  congr 1
  change (o0.toNat+65536*o1.toNat+4294967296*c1.toNat)%4294967296=_
  simp only [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt bound]

/-- Successful active addition uses both selected stack words and wraps exactly
 as the actual Wasm numeric semantics. Stack writes/PC transitions are separate. -/
theorem prepared_active_add_binop (row next pub : Nat → Fp) (first last : Fp)
    (choices : preparedRowChoices row next pub first last)
    (active : row 25=0) (noBorrow : row 414=0)
    (isAdd : (preparedFetchPython 1).evalWith (preparedRowEnv row next pub first last)=1)
    (depth : preparedAddDepthResidual.evalWith (preparedRowEnv row next pub first last)=0)
    (carries : ∀ i,i<2 → (preparedAddCarryPython i).evalWith (preparedRowEnv row next pub first last)=0) :
    ∃ sp,sp<9 ∧ 2≤sp ∧ (∀ i,i<9 → row (16+i)=if i=sp then 1 else 0) ∧
      Num.binop 32 0 (preparedStackWord row (sp-2)) (preparedStackWord row (sp-1))=
        some (preparedAddResultWord row) := by
  obtain ⟨_,⟨sp,hsp,onehot⟩⟩ := prepared_row_pc_sp row next pub first last choices
  have enough := prepared_active_add_depth row next pub first last sp hsp onehot active noBorrow isAdd depth
  refine ⟨sp,hsp,enough,onehot,?_⟩
  let lhs := fun i => (instructionBitExpr (27+32*(sp-2)+16*i) 16).evalWith (instructionAddEnv row)
  let rhs := fun i => (instructionBitExpr (27+32*(sp-1)+16*i) 16).evalWith (instructionAddEnv row)
  let out := fun i => (instructionBitExpr (415+16*i) 16).evalWith (instructionAddEnv row)
  have gate : preparedSuccessfulAdd.evalWith (preparedRowEnv row next pub first last)=1 := by
    change ((1:Fp)+ -row 25)*((1:Fp)+ -row 414)*
      (preparedFetchPython 1).evalWith (preparedRowEnv row next pub first last)=1
    rw [active,noBorrow,isAdd]
    grind
  have equations (i : Nat) (hi : i<2) :
      lhs i+rhs i+(if i=0 then 0 else row 447)=out i+(65536:Fp)*row (447+i) := by
    have h := carries i hi
    change preparedSuccessfulAdd.evalWith (preparedRowEnv row next pub first last) *
      (((preparedOperandPython true i).evalWith (preparedRowEnv row next pub first last) +
        (preparedOperandPython false i).evalWith (preparedRowEnv row next pub first last) +
        (if i=0 then (.const 0 : Expr) else .col 447 false).evalWith (preparedRowEnv row next pub first last)) +
        -((preparedGasBits (415+16*i)).evalWith (preparedRowEnv row next pub first last)+
          (65536:Fp)*row (447+i)))=0 at h
    rw [gate,prepared_operand_python_selected row next pub first last sp hsp enough onehot,
      prepared_operand_python_selected row next pub first last sp hsp enough onehot,
      prepared_bits_row_horner] at h
    cases i with
    | zero =>
      change (1:Fp)*(lhs 0+rhs 0+0+ -(out 0+(65536:Fp)*row (447+0)))=0 at h
      try simp only [ite_true]
      grind
    | succ i =>
      have iz : i=0 := by omega
      subst i
      change (1:Fp)*(lhs 1+rhs 1+row 447+ -(out 1+(65536:Fp)*row (447+1)))=0 at h
      try simp only [Nat.one_ne_zero,ite_false]
      grind
  have lb (i : Nat) (hi : i<2) : (lhs i).toNat<65536 := by
    apply instruction_bit_expr_bound row 16 _ (by decide)
    intro k hk
    exact prepared_row_boolean row next pub first last choices _ (by omega)
  have rb (i : Nat) (hi : i<2) : (rhs i).toNat<65536 := by
    apply instruction_bit_expr_bound row 16 _ (by decide)
    intro k hk
    exact prepared_row_boolean row next pub first last choices _ (by omega)
  have ob (i : Nat) (hi : i<2) : (out i).toNat<65536 := by
    apply instruction_bit_expr_bound row 16 _ (by decide)
    intro k hk
    exact prepared_row_boolean row next pub first last choices _ (by omega)
  have cb0 := prepared_row_boolean row next pub first last choices 447 (by decide)
  have cb1 := prepared_row_boolean row next pub first last choices 448 (by decide)
  have result := prepared_add_pair_binop (lhs 0) (lhs 1) (rhs 0) (rhs 1) (out 0) (out 1) (row 447) (row 448)
    (lb 0 (by decide)) (lb 1 (by decide)) (rb 0 (by decide)) (rb 1 (by decide))
    (ob 0 (by decide)) (ob 1 (by decide)) cb0 cb1 (equations 0 (by decide)) (equations 1 (by decide))
  simpa only [lhs,rhs,out,preparedStackWord,preparedAddResultWord,Nat.mul_zero,Nat.add_zero,
    Nat.mul_one,Nat.reduceAdd,Nat.reduceMul] using result

end NearCompression
