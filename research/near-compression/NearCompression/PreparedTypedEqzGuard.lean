import NearCompression.PreparedTypedEqzSource
import NearCompression.PreparedTypedStackValues
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpecV3.Wasm
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

def preparedTypedSelectedType : Expr :=
  preparedBalancedSum (fun i=>.mul (.col (33+i) false) (.col (1074+i) false)) 3 0
def preparedTypedI64TopGuard : Expr :=
  .mul (.mul preparedExecGasSuccess (.add (.col 1281 false) (.col 1282 false)))
    (.add preparedTypedSelectedType (.neg (.const 1)))
private theorem guard_at : ∀count:Fin 5,
    (preparedTypedLiteralExec count)[1561+66*(4-count.val)]?=some preparedTypedI64TopGuard := by decide

theorem prepared_typed_eqz_selected_type (count : Nat) (hc : count≤4)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedTypedLiteralExecTable count) tr t pub) (hr : r<tr.height t)
    (active : tr.cell t r 41=0) (charged : tr.cell t r 430=0) (opcode : tr.cell t r 1282=1) :
    preparedTypedSelectedType.eval tr t r pub=1 := by
  have h:=localH.constr r hr _ (List.mem_of_getElem? (guard_at ⟨count,by omega⟩))
  have b:=prepared_typed_source_boolean count hc tr t r pub localH hr 1281 (by decide) (by decide) (by decide)
  have alternatives : tr.cell t r 1281=0 ∨ tr.cell t r 1281=1 := by
    have cases : (tr.cell t r 1281).toNat=0 ∨ (tr.cell t r 1281).toNat=1:=by omega
    rcases cases with z|z
    · exact Or.inl (Fp.ext z)
    · exact Or.inr (Fp.ext z)
  change (((1:Fp)+ -tr.cell t r 41)*(1+ -tr.cell t r 430)*(tr.cell t r 1281+tr.cell t r 1282))*
    (preparedTypedSelectedType.eval tr t r pub+ -1)=0 at h
  rw [active,charged,opcode] at h
  have two : (1:Fp)+1≠0 := by decide
  rcases alternatives with z|z <;> rw [z] at h <;> grind

/-- Successful eqz derives a nonempty selected i64 operand from the literal
source; neither a positive depth nor an operand lookup is supplied. -/
theorem prepared_typed_eqz_operand (count : Nat) (hc : count≤4)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedTypedLiteralExecTable count) tr t pub) (hr : r<tr.height t)
    (active : tr.cell t r 41=0) (charged : tr.cell t r 430=0) (opcode : tr.cell t r 1282=1) :
    ∃sp,sp<9 ∧ 0<sp ∧
      (∀i,i<9 → tr.cell t r (32+i)=if i=sp then 1 else 0) ∧
      tr.cell t r (1074+(sp-1))=1 ∧
      tr.cell t r 1284=(if preparedTypedStackWord (tr.cell t r) (sp-1)=0 then 1 else 0) := by
  obtain ⟨sp,hs,hot⟩:=prepared_typed_source_sp count hc tr t r pub localH hr
  have typ:=prepared_typed_eqz_selected_type count hc tr t r pub localH hr active charged opcode
  change ((tr.cell t r 33*tr.cell t r 1074+tr.cell t r 34*tr.cell t r 1075)+
    (tr.cell t r 35*tr.cell t r 1076+tr.cell t r 36*tr.cell t r 1077))+
    ((tr.cell t r 37*tr.cell t r 1078+tr.cell t r 38*tr.cell t r 1079)+
    (tr.cell t r 39*tr.cell t r 1080+tr.cell t r 40*tr.cell t r 1081))=1 at typ
  have h1:=hot 1 (by decide);have h2:=hot 2 (by decide)
  have h3:=hot 3 (by decide);have h4:=hot 4 (by decide)
  have h5:=hot 5 (by decide);have h6:=hot 6 (by decide)
  have h7:=hot 7 (by decide);have h8:=hot 8 (by decide)
  rw [h1,h2,h3,h4,h5,h6,h7,h8] at typ
  have positive : 0<sp := by
    by_cases z:sp=0
    · subst sp; simp only [Nat.reduceEqDiff,ite_false] at typ; grind
    · omega
  have selected : tr.cell t r (1074+(sp-1))=1 := by
    have choices : sp=1 ∨ sp=2 ∨ sp=3 ∨ sp=4 ∨ sp=5 ∨ sp=6 ∨ sp=7 ∨ sp=8:=by omega
    rcases choices with z|z|z|z|z|z|z|z <;> subst sp
    all_goals simp only [Nat.reduceEqDiff,ite_true,ite_false] at typ
    all_goals grind
  exact ⟨sp,hs,positive,hot,selected,prepared_typed_source_eqz count hc tr t r pub localH hr sp hs positive hot⟩
end NearCompression
