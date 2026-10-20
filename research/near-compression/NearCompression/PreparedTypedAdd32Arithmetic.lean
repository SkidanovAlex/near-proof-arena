import NearCompression.PreparedTypedAddArithmetic
import NearCompression.PreparedTypedAdd32Operands
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpecV3.Wasm
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
private theorem equations_at : ∀count:Fin 5,∀limb:Fin 4,
    (preparedTypedLiteralExec count)[1731+66*(4-count.val)+limb.val+(limb.val-2)]?=
      some (preparedTypedAddEquation limb) := by decide
theorem prepared_typed_add32_field_equation (count : Nat) (hc : count≤4)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedTypedLiteralExecTable count) tr t pub) (hr : r<tr.height t)
    (active : tr.cell t r 41=0) (charged : tr.cell t r 430=0) (opcode : tr.cell t r 467=1)
    (sp : Nat) (hs : sp<9) (positive : 2≤sp)
    (hot : ∀i,i<9 → tr.cell t r (32+i)=if i=sp then 1 else 0)
    (limb : Nat) (hl : limb<2) :
    preparedTypedStackLimb (tr.cell t r) (sp-2) limb+preparedTypedStackLimb (tr.cell t r) (sp-1) limb+
      (if limb=0 then 0 else tr.cell t r (preparedTypedCarryCol (limb-1)))=
      preparedTypedResultLimb (tr.cell t r) limb+65536*tr.cell t r (preparedTypedCarryCol limb) := by
  have h:=localH.constr r hr _ (List.mem_of_getElem? (equations_at ⟨count,by omega⟩ ⟨limb,by omega⟩))
  have flag:=prepared_typed_opcode_selected count hc tr t r pub localH hr 1 (by decide) opcode 10 (by decide)
  change tr.cell t r 1281=0 at flag
  have a:=prepared_typed_add_selection tr t r pub sp 0 limb hs positive hot
  have b:=prepared_typed_add_selection tr t r pub sp 1 limb hs positive hot
  simp only [Nat.add_zero,show sp-2+1=sp-1 by omega] at a b
  have gate : (if limb<2 then (.add (.col 467 false) (.col 1281 false) : Expr) else .col 1281 false).eval tr t r pub=1 := by
    rw [ite_eq_left hl]
    simp only [Expr.eval,Expr.evalWith,rowEnv,Bool.false_eq_true,ite_false,flag,opcode] <;> grind
  change preparedExecGasSuccess.eval tr t r pub*_*_=0 at h
  change Expr.evalWith (rowEnv tr t r pub) (if limb<2 then (.add (.col 467 false) (.col 1281 false) : Expr) else .col 1281 false)=1 at gate
  rw [gate] at h
  change (((1:Fp)+ -tr.cell t r 41)*(1+ -tr.cell t r 430))*1*
    (((preparedTypedAddSelected 0 limb).eval tr t r pub+(preparedTypedAddSelected 1 limb).eval tr t r pub)+
      (if limb=0 then (.const 0 : Expr) else .col (preparedTypedCarryCol (limb-1)) false).eval tr t r pub+
      -((preparedCodeBits (preparedTypedResultBase limb)).eval tr t r pub+65536*tr.cell t r (preparedTypedCarryCol limb)))=0 at h
  rw [active,charged,a,b,prepared_code_bits_eval] at h
  by_cases z:limb=0
  all_goals simp only [z,ite_true,ite_false,Expr.eval,Expr.evalWith,rowEnv,Bool.false_eq_true,preparedTypedResultLimb] at h ⊢
  all_goals grind

set_option maxHeartbeats 200000 in
theorem prepared_typed_add32_nat_equation (count : Nat) (hc : count≤4)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedTypedLiteralExecTable count) tr t pub) (hr : r<tr.height t)
    (active : tr.cell t r 41=0) (charged : tr.cell t r 430=0) (opcode : tr.cell t r 467=1)
    (sp : Nat) (hs : sp<9) (positive : 2≤sp)
    (hot : ∀i,i<9 → tr.cell t r (32+i)=if i=sp then 1 else 0)
    (limb : Nat) (hl : limb<2) :
    (preparedTypedStackLimb (tr.cell t r) (sp-2) limb).toNat+(preparedTypedStackLimb (tr.cell t r) (sp-1) limb).toNat+
      (if limb=0 then 0 else (tr.cell t r (preparedTypedCarryCol (limb-1))).toNat)=
      (preparedTypedResultLimb (tr.cell t r) limb).toNat+65536*(tr.cell t r (preparedTypedCarryCol limb)).toNat := by
  have eq:=prepared_typed_add32_field_equation count hc tr t r pub localH hr active charged opcode sp hs positive hot limb hl
  have a:=prepared_typed_stack_limb_bound count hc tr t r pub localH hr (sp-2) limb (by omega) (by omega)
  have b:=prepared_typed_stack_limb_bound count hc tr t r pub localH hr (sp-1) limb (by omega) (by omega)
  have c:=prepared_typed_carry_bound count hc tr t r pub localH hr limb (by omega)
  have out:=prepared_typed_result_bound count hc tr t r pub localH hr limb (by omega)
  by_cases z:limb=0
  · subst limb
    simp only [ite_true] at eq ⊢
    exact instruction_add_limb_sound (preparedTypedStackLimb (tr.cell t r) (sp-2) 0)
      (preparedTypedStackLimb (tr.cell t r) (sp-1) 0) 0
      (preparedTypedResultLimb (tr.cell t r) 0) (tr.cell t r (preparedTypedCarryCol 0)) a b (by decide) out c eq
  · simp only [z,ite_false] at eq ⊢
    exact instruction_add_limb_sound (preparedTypedStackLimb (tr.cell t r) (sp-2) limb)
      (preparedTypedStackLimb (tr.cell t r) (sp-1) limb) (tr.cell t r (preparedTypedCarryCol (limb-1)))
      (preparedTypedResultLimb (tr.cell t r) limb) (tr.cell t r (preparedTypedCarryCol limb)) a b
      (prepared_typed_carry_bound count hc tr t r pub localH hr (limb-1) (by omega)) out c eq



def preparedTypedAdd32Upper (high : Nat) : Expr :=
  .mul (.mul preparedExecGasSuccess (.col 467 false))
    (.add (preparedCodeBits (preparedTypedResultBase (high+2))) (.neg (.const 0)))
private theorem upper_at : ∀count:Fin 5,∀high:Fin 2,
    (preparedTypedLiteralExec count)[1734+66*(4-count.val)+2*high.val]?=some (preparedTypedAdd32Upper high) := by decide

theorem prepared_typed_add32_upper_zero (count : Nat) (hc : count≤4)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedTypedLiteralExecTable count) tr t pub) (hr : r<tr.height t)
    (active : tr.cell t r 41=0) (charged : tr.cell t r 430=0) (opcode : tr.cell t r 467=1)
    (high : Nat) (hh : high<2) : preparedTypedResultLimb (tr.cell t r) (high+2)=0 := by
  have h:=localH.constr r hr _ (List.mem_of_getElem? (upper_at ⟨count,by omega⟩ ⟨high,hh⟩))
  change (((1:Fp)+ -tr.cell t r 41)*(1+ -tr.cell t r 430)*tr.cell t r 467)*
    ((preparedCodeBits (preparedTypedResultBase (high+2))).eval tr t r pub+ -0)=0 at h
  rw [active,charged,opcode,prepared_code_bits_eval] at h
  simp only [Bool.false_eq_true,ite_false] at h
  change preparedCodeLimb (tr.cell t r) (preparedTypedResultBase (high+2))=0
  grind

private theorem four_word_i32 (a : Nat→Fp) (bound : instructionAdd64Word a 0<4294967296) :
    instructionAdd64Word a 0=(a 0).toNat+65536*(a 1).toNat := by
  unfold instructionAdd64Word at bound ⊢
  simp only [Nat.reduceAdd] at bound ⊢
  omega

private theorem add32_word_binop (a b out carry : Nat→Fp)
    (ab : instructionAdd64Word a 0<4294967296) (bb : instructionAdd64Word b 0<4294967296)
    (e0 : (a 0).toNat+(b 0).toNat+0=(out 0).toNat+65536*(carry 0).toNat)
    (e1 : (a 1).toNat+(b 1).toNat+(carry 0).toNat=(out 1).toNat+65536*(carry 1).toNat)
    (b0 : (out 0).toNat<65536) (b1 : (out 1).toNat<65536) (z2 : out 2=0) (z3 : out 3=0) :
    Num.binop 32 0 (instructionAdd64Word a 0) (instructionAdd64Word b 0)=some (instructionAdd64Word out 0) := by
  have ow : instructionAdd64Word out 0=(out 0).toNat+65536*(out 1).toNat := by
    unfold instructionAdd64Word
    simp only [Nat.reduceAdd,z2,z3];rfl
  have total : instructionAdd64Word a 0+instructionAdd64Word b 0=
      instructionAdd64Word out 0+4294967296*(carry 1).toNat := by
    rw [four_word_i32 a ab,four_word_i32 b bb,ow];omega
  have bound : instructionAdd64Word out 0<4294967296 := by rw [ow];omega
  simp only [Num.binop,total]
  congr 1
  change (_+4294967296*_)%4294967296=_
  simp only [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt bound]

theorem prepared_typed_add32_binop (count : Nat) (hc : count≤4)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedTypedLiteralExecTable count) tr t pub) (hr : r<tr.height t)
    (active : tr.cell t r 41=0) (charged : tr.cell t r 430=0) (opcode : tr.cell t r 467=1)
    (sp : Nat) (hs : sp<9)
    (hot : ∀i,i<9 → tr.cell t r (32+i)=if i=sp then 1 else 0) :
    Num.binop 32 0 (preparedTypedStackWord (tr.cell t r) (sp-2)) (preparedTypedStackWord (tr.cell t r) (sp-1))=
      some (preparedTypedResultWord (tr.cell t r)) := by
  have operands:=prepared_typed_add32_operands count hc tr t r pub localH hr active charged opcode sp hs hot
  have a:=prepared_typed_stack_i32_bound count hc tr t r pub localH hr (sp-2) (by omega) operands.2.1
  have b:=prepared_typed_stack_i32_bound count hc tr t r pub localH hr (sp-1) (by omega) operands.2.2
  have eq (i : Nat) (hi : i<2):=prepared_typed_add32_nat_equation count hc tr t r pub localH hr active charged opcode sp hs operands.1 hot i hi
  have e0:=eq 0 (by decide);have e1:=eq 1 (by decide)
  simp only [Nat.reduceEqDiff,ite_true,ite_false,Nat.reduceSub] at e0 e1
  exact add32_word_binop
    (preparedTypedStackLimb (tr.cell t r) (sp-2)) (preparedTypedStackLimb (tr.cell t r) (sp-1))
    (preparedTypedResultLimb (tr.cell t r)) (fun i=>tr.cell t r (preparedTypedCarryCol i)) a b e0 e1
    (prepared_typed_result_bound count hc tr t r pub localH hr 0 (by decide))
    (prepared_typed_result_bound count hc tr t r pub localH hr 1 (by decide))
    (prepared_typed_add32_upper_zero count hc tr t r pub localH hr active charged opcode 0 (by decide))
    (prepared_typed_add32_upper_zero count hc tr t r pub localH hr active charged opcode 1 (by decide))

end NearCompression
