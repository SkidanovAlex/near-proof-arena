import NearCompression.PreparedTypedAddOperands
import NearCompression.PreparedTypedEqzGuard
import NearCompression.PreparedTypedOpcode
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpecV3.Wasm
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

def preparedTypedI32TopGuard : Expr :=
  .mul (.mul preparedExecGasSuccess (.add (.col 467 false) (.col 606 false)))
    (.add preparedTypedSelectedType (.neg (.const 0)))
def preparedTypedI32SecondGuard : Expr :=
  .mul (.mul preparedExecGasSuccess (.col 467 false))
    (.add preparedTypedSecondType (.neg (.const 0)))
def preparedTypedAddUnderflow : Expr :=
  .add (.mul preparedExecGasSuccess (.mul (.add (.col 467 false) (.col 1281 false))
    (.add (.col 32 false) (.col 33 false)))) (.neg (.const 0))
private theorem underflow_at : ∀count:Fin 5,
    (preparedTypedLiteralExec count)[1663+66*(4-count.val)]?=some preparedTypedAddUnderflow := by decide
private theorem guards_at : ∀count:Fin 5,
    (preparedTypedLiteralExec count)[1559+66*(4-count.val)]?=some preparedTypedI32TopGuard ∧
    (preparedTypedLiteralExec count)[1560+66*(4-count.val)]?=some preparedTypedI32SecondGuard := by decide

theorem prepared_typed_add32_selected_types (count : Nat) (hc : count≤4)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedTypedLiteralExecTable count) tr t pub) (hr : r<tr.height t)
    (active : tr.cell t r 41=0) (charged : tr.cell t r 430=0) (opcode : tr.cell t r 467=1) :
    preparedTypedSelectedType.eval tr t r pub=0 ∧ preparedTypedSecondType.eval tr t r pub=0 := by
  have a:=localH.constr r hr _ (List.mem_of_getElem? (guards_at ⟨count,by omega⟩).1)
  have b:=localH.constr r hr _ (List.mem_of_getElem? (guards_at ⟨count,by omega⟩).2)
  have flag:=prepared_typed_opcode_selected count hc tr t r pub localH hr 1 (by decide) opcode 5 (by decide)
  change tr.cell t r 606=0 at flag
  change (((1:Fp)+ -tr.cell t r 41)*(1+ -tr.cell t r 430)*(tr.cell t r 467+tr.cell t r 606))*
    (preparedTypedSelectedType.eval tr t r pub+ -0)=0 at a
  change (((1:Fp)+ -tr.cell t r 41)*(1+ -tr.cell t r 430)*tr.cell t r 467)*
    (preparedTypedSecondType.eval tr t r pub+ -0)=0 at b
  rw [active,charged,opcode,flag] at a
  rw [active,charged,opcode] at b
  constructor <;> grind

theorem prepared_typed_add32_operands (count : Nat) (hc : count≤4)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedTypedLiteralExecTable count) tr t pub) (hr : r<tr.height t)
    (active : tr.cell t r 41=0) (charged : tr.cell t r 430=0) (opcode : tr.cell t r 467=1)
    (sp : Nat) (hs : sp<9) (hot : ∀i,i<9 → tr.cell t r (32+i)=if i=sp then 1 else 0) :
    2≤sp ∧ tr.cell t r (1074+(sp-2))=0 ∧ tr.cell t r (1074+(sp-1))=0 := by
  obtain ⟨a,b⟩:=prepared_typed_add32_selected_types count hc tr t r pub localH hr active charged opcode
  change ((tr.cell t r 33*tr.cell t r 1074+tr.cell t r 34*tr.cell t r 1075)+
    (tr.cell t r 35*tr.cell t r 1076+tr.cell t r 36*tr.cell t r 1077))+
    ((tr.cell t r 37*tr.cell t r 1078+tr.cell t r 38*tr.cell t r 1079)+
    (tr.cell t r 39*tr.cell t r 1080+tr.cell t r 40*tr.cell t r 1081))=0 at a
  change ((tr.cell t r 34*tr.cell t r 1074+tr.cell t r 35*tr.cell t r 1075)+
    (tr.cell t r 36*tr.cell t r 1076+tr.cell t r 37*tr.cell t r 1077))+
    ((tr.cell t r 38*tr.cell t r 1078+tr.cell t r 39*tr.cell t r 1079)+tr.cell t r 40*tr.cell t r 1080)=0 at b
  have under:=localH.constr r hr _ (List.mem_of_getElem? (underflow_at ⟨count,by omega⟩))
  have other:=prepared_typed_opcode_selected count hc tr t r pub localH hr 1 (by decide) opcode 10 (by decide)
  change tr.cell t r 1281=0 at other
  change ((1:Fp)+ -tr.cell t r 41)*(1+ -tr.cell t r 430)*((tr.cell t r 467+tr.cell t r 1281)*(tr.cell t r 32+tr.cell t r 33))+ -0=0 at under
  rw [active,charged,opcode,other,hot 0 (by decide),hot 1 (by decide)] at under
  have h1:=hot 1 (by decide);have h2:=hot 2 (by decide)
  have h3:=hot 3 (by decide);have h4:=hot 4 (by decide)
  have h5:=hot 5 (by decide);have h6:=hot 6 (by decide)
  have h7:=hot 7 (by decide);have h8:=hot 8 (by decide)
  rw [h1,h2,h3,h4,h5,h6,h7,h8] at a
  rw [h2,h3,h4,h5,h6,h7,h8] at b
  have choices : sp=0 ∨ sp=1 ∨ sp=2 ∨ sp=3 ∨ sp=4 ∨ sp=5 ∨ sp=6 ∨ sp=7 ∨ sp=8:=by omega
  rcases choices with z|z|z|z|z|z|z|z|z <;> subst sp
  all_goals simp only [Nat.reduceEqDiff,ite_true,ite_false] at a b under
  all_goals simp only [Nat.reduceSub,Nat.reduceAdd]
  all_goals grind
end NearCompression
