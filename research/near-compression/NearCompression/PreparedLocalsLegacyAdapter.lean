import NearCompression.PreparedLocalsUpdate
import NearCompression.PreparedControlLegacyAdapter
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpecV3.Wasm
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Specialize only current-row local/branch flags and the const flag. The
const specialization removes the extra gated get/const data multiplexer. -/
def preparedLocalsLegacySpecialize (isConst : Bool) : Expr → Expr
  | .col c false => if c=466 then .const (if isConst then 1 else 0)
    else if c=606 ∨ c=683 ∨ c=684 ∨ c=685 then .const 0 else .col c false
  | .add a b=>.add (preparedLocalsLegacySpecialize isConst a) (preparedLocalsLegacySpecialize isConst b)
  | .mul a b=>.mul (preparedLocalsLegacySpecialize isConst a) (preparedLocalsLegacySpecialize isConst b)
  | .neg a=>.neg (preparedLocalsLegacySpecialize isConst a)
  | e=>e

theorem prepared_locals_legacy_specialize_eval (isConst : Bool) (e : Expr) (env : Env Fp)
    (flag : env.col 466 false=env.ofNat (if isConst then 1 else 0))
    (zeros : ∀c,c=606 ∨ c=683 ∨ c=684 ∨ c=685 → env.col c false=env.ofNat 0) :
    (preparedLocalsLegacySpecialize isConst e).evalWith env=e.evalWith env := by
  induction e with
  | col c next =>
    cases next
    · by_cases eq:c=466
      · subst c;simpa only [preparedLocalsLegacySpecialize,ite_true,Expr.evalWith] using flag.symm
      · by_cases z:c=606 ∨ c=683 ∨ c=684 ∨ c=685
        · simpa only [preparedLocalsLegacySpecialize,eq,z,ite_true,ite_false,Expr.evalWith] using (zeros c z).symm
        · simp only [preparedLocalsLegacySpecialize,eq,z,ite_false]
    · rfl
  | add a b ha hb => simp only [preparedLocalsLegacySpecialize,Expr.evalWith,ha,hb]
  | mul a b ha hb => simp only [preparedLocalsLegacySpecialize,Expr.evalWith,ha,hb]
  | neg a ha => simp only [preparedLocalsLegacySpecialize,Expr.evalWith,ha]
  | const _ | pub _ | isFirst | isLast | isTransition => rfl

def PreparedLocalsLegacySource (isConst : Bool) (e : Expr) : Prop :=
  ∃original,original∈preparedLocalsLiteralExecBase ∧ preparedNoFirst original ∧
    preparedExecSimplify (preparedLocalsLegacySpecialize isConst original)=
      preparedExecSimplify (preparedLocalsLegacySpecialize isConst (preparedExecLower e))

theorem prepared_locals_legacy_source_eval (isConst : Bool) (count : Nat)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedLocalsLiteralExecTable count) tr t pub) (nonlast : r+1<tr.height t)
    (flag : tr.cell t r 466=if isConst then 1 else 0)
    (zeros : ∀c,c=606 ∨ c=683 ∨ c=684 ∨ c=685 → tr.cell t r c=0)
    (e : Expr) (source : PreparedLocalsLegacySource isConst e) :
    (preparedExecLower e).evalWith
      (preparedRowEnv (tr.cell t r) (tr.cell t (r+1)) (fun i=>pub.getD i 0) 0 0)=0 := by
  obtain ⟨original,member,noFirst,eq⟩:=source
  have flag' : (preparedRowEnv (tr.cell t r) (tr.cell t (r+1)) (fun i=>pub.getD i 0) 0 0).col 466 false=
      Fp.ofNat (if isConst then 1 else 0) := by cases isConst <;> exact flag
  have result:=congrArg (fun e=>e.evalWith (preparedRowEnv (tr.cell t r) (tr.cell t (r+1)) (fun i=>pub.getD i 0) 0 0)) eq
  rw [prepared_exec_simplify_eval,prepared_exec_simplify_eval,
    prepared_locals_legacy_specialize_eval _ _ _ flag' zeros,
    prepared_locals_legacy_specialize_eval _ _ _ flag' zeros] at result
  rw [←result]
  exact prepared_table_nonlast_eval _ tr t r pub localH nonlast original
    (prepared_locals_base_member count original member) noFirst

private def noFirstDec : (e : Expr) → Decidable (preparedNoFirst e)
  | .isFirst=>isFalse id
  | .add a b | .mul a b=>
    letI := noFirstDec a
    letI := noFirstDec b
    inferInstanceAs (Decidable (preparedNoFirst a ∧ preparedNoFirst b))
  | .neg a=>noFirstDec a
  | .const _ | .col _ _ | .pub _ | .isLast | .isTransition=>isTrue True.intro
attribute [local instance] noFirstDec

private theorem source_at (isConst : Bool) (i : Nat) (hi : i<1144) (e : Expr)
    (shape : preparedNoFirst (preparedLocalsLiteralExecBase[i]'hi) ∧
      preparedExecSimplify (preparedLocalsLegacySpecialize isConst (preparedLocalsLiteralExecBase[i]'hi))=
        preparedExecSimplify (preparedLocalsLegacySpecialize isConst (preparedExecLower e))) :
    PreparedLocalsLegacySource isConst e := ⟨_,List.getElem_mem hi,shape.1,shape.2⟩

theorem prepared_locals_legacy_sp_source (isConst : Bool) : PreparedLocalsLegacySource isConst preparedSPStepPython := by
  cases isConst <;> exact source_at _ 1040 (by decide) _ (by decide)

theorem prepared_locals_legacy_stack_source (isConst : Bool) : ∀ slot,slot<8 → ∀ limb,limb<2 →
    PreparedLocalsLegacySource isConst (preparedStackStepPython slot limb) := by
  have all : ∀ flag:Bool,∀ slot:Fin 8,∀ limb:Fin 2,
      preparedNoFirst (preparedLocalsLiteralExecBase[1113+4*slot.val+2*limb.val]'(by change _<1144;omega)) ∧
      preparedExecSimplify (preparedLocalsLegacySpecialize flag (preparedLocalsLiteralExecBase[1113+4*slot.val+2*limb.val]'(by change _<1144;omega)))=
        preparedExecSimplify (preparedLocalsLegacySpecialize flag (preparedExecLower (preparedStackStepPython slot.val limb.val))) := by decide
  intro slot hs limb hi
  exact source_at isConst (1113+4*slot+2*limb) (by omega) _ (all isConst ⟨slot,hs⟩ ⟨limb,hi⟩)

theorem prepared_locals_legacy_choice_source (isConst : Bool) : PreparedLocalsLegacySource isConst preparedSPResidualPython := by
  cases isConst <;> exact source_at _ 817 (by decide) _ (by decide)

theorem prepared_locals_legacy_add_depth_source (isConst : Bool) : PreparedLocalsLegacySource isConst preparedAddDepthResidual := by
  cases isConst <;> exact source_at _ 1042 (by decide) _ (by decide)

theorem prepared_locals_legacy_add_carry_source (isConst : Bool) : ∀ i,i<2 → PreparedLocalsLegacySource isConst (preparedAddCarryPython i) := by
  have all : ∀ flag:Bool,∀ i:Fin 2,preparedNoFirst (preparedLocalsLiteralExecBase[1110+i.val]'(by change _<1144;omega)) ∧
      preparedExecSimplify (preparedLocalsLegacySpecialize flag (preparedLocalsLiteralExecBase[1110+i.val]'(by change _<1144;omega)))=
        preparedExecSimplify (preparedLocalsLegacySpecialize flag (preparedExecLower (preparedAddCarryPython i.val))) := by decide
  intro i hi
  exact source_at isConst (1110+i) (by omega) _ (all isConst ⟨i,hi⟩)

theorem prepared_locals_legacy_stack_depth_source (isConst push : Bool) :
    PreparedLocalsLegacySource isConst (preparedExecStackDepth push) := by
  cases isConst <;> cases push
  · exact source_at _ 1043 (by decide) _ (by decide)
  · exact source_at _ 1041 (by decide) _ (by decide)
  · exact source_at _ 1043 (by decide) _ (by decide)
  · exact source_at _ 1041 (by decide) _ (by decide)

theorem prepared_locals_legacy_projection (isConst : Bool) (count : Nat)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedLocalsLiteralExecTable count) tr t pub) (nonlast : r+1<tr.height t)
    (flag : tr.cell t r 466=if isConst then 1 else 0)
    (zeros : ∀c,c=606 ∨ c=683 ∨ c=684 ∨ c=685 → tr.cell t r c=0) :
    let row:=preparedExecGhostRow (tr.cell t r)
    let next:=preparedExecGhostNext (tr.cell t r) (tr.cell t (r+1)) (fun i=>pub.getD i 0)
    let fields:=preparedExecGhostPub (tr.cell t r) (tr.cell t (r+1)) (fun i=>pub.getD i 0)
    preparedRowChoices row next fields 0 0 ∧ PreparedAddTransitionHolds row next fields := by
  constructor
  · apply prepared_exec_python_choices
    · intro i hi
      have hb:=prepared_locals_bits_boolean count tr t r pub localH (by omega) i (by omega) (by omega)
      have cases : tr.cell t r i=0 ∨ tr.cell t r i=1 := by
        by_cases h: (tr.cell t r i).toNat=0
        · exact Or.inl (Fp.ext h)
        · exact Or.inr (Fp.ext (by change _=1;omega))
      rcases cases with h|h <;> rw [h] <;> decide
    · exact prepared_locals_legacy_source_eval isConst count tr t r pub localH nonlast flag zeros _ (prepared_locals_legacy_choice_source isConst)
  · exact prepared_exec_transition_holds _ _ _
      (prepared_locals_legacy_source_eval isConst count tr t r pub localH nonlast flag zeros _ (prepared_locals_legacy_sp_source isConst))
      (fun slot hs limb hi=>prepared_locals_legacy_source_eval isConst count tr t r pub localH nonlast flag zeros _
        (prepared_locals_legacy_stack_source isConst slot hs limb hi))
end NearCompression
