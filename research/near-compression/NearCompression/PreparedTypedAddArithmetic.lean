import NearCompression.PreparedTypedAddOperands
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpecV3.Wasm
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

def preparedTypedAddSelected (offset limb : Nat) : Expr :=
  preparedTypedSevenSum (fun i=>.mul (.col (34+i) false)
    (preparedCodeBits (preparedTypedStackBase (i+offset) limb)))
def preparedTypedResultBase (limb : Nat) : Nat := (if limb<2 then 431 else 1246)+16*(limb%2)
def preparedTypedResultLimb (row : Nat→Fp) (limb : Nat) : Fp := preparedCodeLimb row (preparedTypedResultBase limb)
def preparedTypedResultWord (row : Nat→Fp) : Nat := instructionAdd64Word (preparedTypedResultLimb row) 0
def preparedTypedCarryCol (limb : Nat) : Nat := (if limb<2 then 463 else 1278)+(limb%2)
def preparedTypedAddEquation (limb : Nat) : Expr :=
  .mul (.mul preparedExecGasSuccess (if limb<2 then .add (.col 467 false) (.col 1281 false) else .col 1281 false))
    (.add (.add (.add (preparedTypedAddSelected 0 limb) (preparedTypedAddSelected 1 limb))
      (if limb=0 then .const 0 else .col (preparedTypedCarryCol (limb-1)) false))
      (.neg (.add (preparedCodeBits (preparedTypedResultBase limb))
        (.mul (.const 65536) (.col (preparedTypedCarryCol limb) false)))))
private theorem equations_at : ∀count:Fin 5,∀limb:Fin 4,
    (preparedTypedLiteralExec count)[1731+66*(4-count.val)+limb.val+(limb.val-2)]?=
      some (preparedTypedAddEquation limb) := by decide

theorem prepared_typed_add_selection (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (sp offset limb : Nat) (hs : sp<9) (positive : 2≤sp)
    (hot : ∀i,i<9 → tr.cell t r (32+i)=if i=sp then 1 else 0) :
    (preparedTypedAddSelected offset limb).eval tr t r pub=
      preparedTypedStackLimb (tr.cell t r) (sp-2+offset) limb := by
  let word (i : Nat):=(preparedCodeBits (preparedTypedStackBase (i+offset) limb)).eval tr t r pub
  change ((tr.cell t r 34*word 0+tr.cell t r 35*word 1)+(tr.cell t r 36*word 2+tr.cell t r 37*word 3))+
    ((tr.cell t r 38*word 4+tr.cell t r 39*word 5)+tr.cell t r 40*word 6)=_
  have h2:=hot 2 (by decide);have h3:=hot 3 (by decide);have h4:=hot 4 (by decide)
  have h5:=hot 5 (by decide);have h6:=hot 6 (by decide)
  have h7:=hot 7 (by decide);have h8:=hot 8 (by decide)
  rw [h2,h3,h4,h5,h6,h7,h8]
  have choices : sp=2 ∨ sp=3 ∨ sp=4 ∨ sp=5 ∨ sp=6 ∨ sp=7 ∨ sp=8:=by omega
  rcases choices with z|z|z|z|z|z|z <;> subst sp
  all_goals simp only [Nat.reduceEqDiff,ite_true,ite_false,Nat.reduceSub]
  all_goals simp only [word,prepared_code_bits_eval,Bool.false_eq_true,ite_false,preparedTypedStackLimb]
  all_goals grind

theorem prepared_typed_add_field_equation (count : Nat) (hc : count≤4)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedTypedLiteralExecTable count) tr t pub) (hr : r<tr.height t)
    (active : tr.cell t r 41=0) (charged : tr.cell t r 430=0) (opcode : tr.cell t r 1281=1)
    (sp : Nat) (hs : sp<9) (positive : 2≤sp)
    (hot : ∀i,i<9 → tr.cell t r (32+i)=if i=sp then 1 else 0)
    (limb : Nat) (hl : limb<4) :
    preparedTypedStackLimb (tr.cell t r) (sp-2) limb+preparedTypedStackLimb (tr.cell t r) (sp-1) limb+
      (if limb=0 then 0 else tr.cell t r (preparedTypedCarryCol (limb-1)))=
      preparedTypedResultLimb (tr.cell t r) limb+65536*tr.cell t r (preparedTypedCarryCol limb) := by
  have h:=localH.constr r hr _ (List.mem_of_getElem? (equations_at ⟨count,by omega⟩ ⟨limb,hl⟩))
  have flag:=prepared_typed_opcode_selected count hc tr t r pub localH hr 10 (by decide) opcode 1 (by decide)
  change tr.cell t r 467=0 at flag
  have a:=prepared_typed_add_selection tr t r pub sp 0 limb hs positive hot
  have b:=prepared_typed_add_selection tr t r pub sp 1 limb hs positive hot
  simp only [Nat.add_zero,show sp-2+1=sp-1 by omega] at a b
  have gate : (if limb<2 then (.add (.col 467 false) (.col 1281 false) : Expr) else .col 1281 false).eval tr t r pub=1 := by
    split <;> simp only [Expr.eval,Expr.evalWith,rowEnv,Bool.false_eq_true,ite_false,flag,opcode] <;> grind
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

theorem prepared_typed_result_bound (count : Nat) (hc : count≤4)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedTypedLiteralExecTable count) tr t pub) (hr : r<tr.height t)
    (limb : Nat) (_hl : limb<4) : (preparedTypedResultLimb (tr.cell t r) limb).toNat<65536 := by
  apply prepared_typed_source_limb count hc tr t r pub localH hr
  · unfold preparedTypedResultBase;split <;> omega
  · intro i hi;unfold preparedTypedResultBase;split <;> constructor <;> omega

theorem prepared_typed_carry_bound (count : Nat) (hc : count≤4)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedTypedLiteralExecTable count) tr t pub) (hr : r<tr.height t)
    (limb : Nat) (_hl : limb<4) : (tr.cell t r (preparedTypedCarryCol limb)).toNat≤1 := by
  apply prepared_typed_source_boolean count hc tr t r pub localH hr
  all_goals unfold preparedTypedCarryCol;split <;> omega

set_option maxHeartbeats 200000 in
theorem prepared_typed_add_nat_equation (count : Nat) (hc : count≤4)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedTypedLiteralExecTable count) tr t pub) (hr : r<tr.height t)
    (active : tr.cell t r 41=0) (charged : tr.cell t r 430=0) (opcode : tr.cell t r 1281=1)
    (sp : Nat) (hs : sp<9) (positive : 2≤sp)
    (hot : ∀i,i<9 → tr.cell t r (32+i)=if i=sp then 1 else 0)
    (limb : Nat) (hl : limb<4) :
    (preparedTypedStackLimb (tr.cell t r) (sp-2) limb).toNat+(preparedTypedStackLimb (tr.cell t r) (sp-1) limb).toNat+
      (if limb=0 then 0 else (tr.cell t r (preparedTypedCarryCol (limb-1))).toNat)=
      (preparedTypedResultLimb (tr.cell t r) limb).toNat+65536*(tr.cell t r (preparedTypedCarryCol limb)).toNat := by
  have eq:=prepared_typed_add_field_equation count hc tr t r pub localH hr active charged opcode sp hs positive hot limb hl
  have a:=prepared_typed_stack_limb_bound count hc tr t r pub localH hr (sp-2) limb (by omega) hl
  have b:=prepared_typed_stack_limb_bound count hc tr t r pub localH hr (sp-1) limb (by omega) hl
  have c:=prepared_typed_carry_bound count hc tr t r pub localH hr limb hl
  have out:=prepared_typed_result_bound count hc tr t r pub localH hr limb hl
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

private theorem prepared_typed_four_limb_binop (a b out carry : Nat→Fp)
    (e0 : (a 0).toNat+(b 0).toNat+0=(out 0).toNat+65536*(carry 0).toNat)
    (e1 : (a 1).toNat+(b 1).toNat+(carry 0).toNat=(out 1).toNat+65536*(carry 1).toNat)
    (e2 : (a 2).toNat+(b 2).toNat+(carry 1).toNat=(out 2).toNat+65536*(carry 2).toNat)
    (e3 : (a 3).toNat+(b 3).toNat+(carry 2).toNat=(out 3).toNat+65536*(carry 3).toNat)
    (b0 : (out 0).toNat<65536) (b1 : (out 1).toNat<65536)
    (b2 : (out 2).toNat<65536) (b3 : (out 3).toNat<65536) :
    Num.binop 64 0 (instructionAdd64Word a 0) (instructionAdd64Word b 0)=some (instructionAdd64Word out 0) := by
  have total : instructionAdd64Word a 0+instructionAdd64Word b 0=
      instructionAdd64Word out 0+18446744073709551616*(carry 3).toNat := by
    unfold instructionAdd64Word;simp only [Nat.reduceAdd];omega
  have bound : instructionAdd64Word out 0<18446744073709551616 := by
    unfold instructionAdd64Word;simp only [Nat.reduceAdd];omega
  simp only [Num.binop,total]
  congr 1
  change (_+18446744073709551616*_)%18446744073709551616=_
  simp only [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt bound]

set_option maxHeartbeats 200000 in
theorem prepared_typed_add_binop (count : Nat) (hc : count≤4)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedTypedLiteralExecTable count) tr t pub) (hr : r<tr.height t)
    (active : tr.cell t r 41=0) (charged : tr.cell t r 430=0) (opcode : tr.cell t r 1281=1)
    (sp : Nat) (hs : sp<9) (positive : 2≤sp)
    (hot : ∀i,i<9 → tr.cell t r (32+i)=if i=sp then 1 else 0) :
    Num.binop 64 0 (preparedTypedStackWord (tr.cell t r) (sp-2)) (preparedTypedStackWord (tr.cell t r) (sp-1))=
      some (preparedTypedResultWord (tr.cell t r)) := by
  have eq (i : Nat) (hi : i<4):=prepared_typed_add_nat_equation count hc tr t r pub localH hr active charged opcode sp hs positive hot i hi
  have e0:=eq 0 (by decide);have e1:=eq 1 (by decide);have e2:=eq 2 (by decide);have e3:=eq 3 (by decide)
  have b (i : Nat) (hi : i<4):=prepared_typed_result_bound count hc tr t r pub localH hr i hi
  have b0:=b 0 (by decide);have b1:=b 1 (by decide);have b2:=b 2 (by decide);have b3:=b 3 (by decide)
  simp only [Nat.reduceEqDiff,ite_true,ite_false,Nat.reduceSub] at e0 e1 e2 e3
  exact prepared_typed_four_limb_binop
    (preparedTypedStackLimb (tr.cell t r) (sp-2)) (preparedTypedStackLimb (tr.cell t r) (sp-1))
    (preparedTypedResultLimb (tr.cell t r)) (fun i=>tr.cell t r (preparedTypedCarryCol i))
    e0 e1 e2 e3 b0 b1 b2 b3
end NearCompression
