import NearCompression.PreparedControlAuthenticated
import NearCompression.PreparedControlStack

set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpecV3.Wasm

/-- Specialize the current conditional-branch selector only. No next-row
selector or other opcode is silently removed. -/
def preparedControlNoBranch : Expr → Expr
  | .col c false => if c=606 then .const 0 else .col c false
  | .add a b => .add (preparedControlNoBranch a) (preparedControlNoBranch b)
  | .mul a b => .mul (preparedControlNoBranch a) (preparedControlNoBranch b)
  | .neg a => .neg (preparedControlNoBranch a)
  | e => e

theorem prepared_control_no_branch_eval (e : Expr) (env : Env Fp) (zero : env.col 606 false=env.ofNat 0) :
    (preparedControlNoBranch e).evalWith env=e.evalWith env := by
  induction e with
  | col c next =>
    cases next
    · by_cases eq:c=606
      · subst c;simpa only [preparedControlNoBranch,ite_true,Expr.evalWith] using zero.symm
      · simp only [preparedControlNoBranch,eq,ite_false]
    · rfl
  | add a b ha hb => simp only [preparedControlNoBranch,Expr.evalWith,ha,hb]
  | mul a b ha hb => simp only [preparedControlNoBranch,Expr.evalWith,ha,hb]
  | neg a ha => simp only [preparedControlNoBranch,Expr.evalWith,ha]
  | const _ | pub _ | isFirst | isLast | isTransition => rfl

def PreparedControlLegacySource (e : Expr) : Prop :=
  ∃ original,original∈preparedControlLiteralExecTable.constraints ∧ preparedNoFirst original ∧
    preparedExecSimplify (preparedControlNoBranch original)=preparedExecLower e

theorem prepared_control_legacy_source_eval (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal preparedControlLiteralExecTable tr t pub) (nonlast : r+1<tr.height t)
    (branchZero : tr.cell t r 606=0) (e : Expr) (source : PreparedControlLegacySource e) :
    (preparedExecLower e).evalWith
      (preparedRowEnv (tr.cell t r) (tr.cell t (r+1)) (fun i=>pub.getD i 0) 0 0)=0 := by
  obtain ⟨original,member,noFirst,eq⟩:=source
  rw [←eq,prepared_exec_simplify_eval,prepared_control_no_branch_eval _ _ branchZero]
  exact prepared_table_nonlast_eval _ tr t r pub localH nonlast original member noFirst

private def noFirstDec : (e : Expr) → Decidable (preparedNoFirst e)
  | .isFirst => isFalse id
  | .add a b | .mul a b =>
    letI := noFirstDec a
    letI := noFirstDec b
    inferInstanceAs (Decidable (preparedNoFirst a ∧ preparedNoFirst b))
  | .neg a => noFirstDec a
  | .const _ | .col _ _ | .pub _ | .isLast | .isTransition => isTrue True.intro
attribute [local instance] noFirstDec

private theorem source_at (i : Nat) (hi : i<870) (e : Expr)
    (shape : preparedNoFirst (preparedControlLiteralExec[i]'hi) ∧
      preparedExecSimplify (preparedControlNoBranch (preparedControlLiteralExec[i]'hi))=preparedExecLower e) :
    PreparedControlLegacySource e :=
  ⟨_,List.getElem_mem hi,shape.1,shape.2⟩

theorem prepared_control_legacy_sp_source : PreparedControlLegacySource preparedSPStepPython :=
  source_at 766 (by decide) _ (by decide)

theorem prepared_control_legacy_stack_source : ∀ slot,slot<8 → ∀ limb,limb<2 →
    PreparedControlLegacySource (preparedStackStepPython slot limb) := by
  have all : ∀ slot:Fin 8,∀ limb:Fin 2,
      preparedNoFirst (preparedControlLiteralExec[839+4*slot.val+2*limb.val]'(by change _<870;omega)) ∧
      preparedExecSimplify (preparedControlNoBranch (preparedControlLiteralExec[839+4*slot.val+2*limb.val]'(by change _<870;omega)))=
        preparedExecLower (preparedStackStepPython slot.val limb.val) := by decide
  intro slot hs limb hi
  exact source_at (839+4*slot+2*limb) (by omega) _ (all ⟨slot,hs⟩ ⟨limb,hi⟩)

theorem prepared_control_legacy_choice_source : PreparedControlLegacySource preparedSPResidualPython :=
  source_at 682 (by decide) _ (by decide)

theorem prepared_control_legacy_add_depth_source : PreparedControlLegacySource preparedAddDepthResidual :=
  source_at 768 (by decide) _ (by decide)

theorem prepared_control_legacy_add_carry_source : ∀ i,i<2 → PreparedControlLegacySource (preparedAddCarryPython i) := by
  have all : ∀ i:Fin 2,preparedNoFirst (preparedControlLiteralExec[836+i.val]'(by change _<870;omega)) ∧
      preparedExecSimplify (preparedControlNoBranch (preparedControlLiteralExec[836+i.val]'(by change _<870;omega)))=
        preparedExecLower (preparedAddCarryPython i.val) := by decide
  intro i hi
  exact source_at (836+i) (by omega) _ (all ⟨i,hi⟩)

theorem prepared_control_legacy_stack_depth_source (push : Bool) :
    PreparedControlLegacySource (preparedExecStackDepth push) := by
  cases push
  · exact source_at 769 (by decide) _ (by decide)
  · exact source_at 767 (by decide) _ (by decide)

/-- Actual control-table constraints imply the reusable local arithmetic and
stack transition interface whenever current BRIF is zero. This is semantic
specialization, not an old-table membership assertion. -/
theorem prepared_control_legacy_projection (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal preparedControlLiteralExecTable tr t pub) (nonlast : r+1<tr.height t)
    (branchZero : tr.cell t r 606=0) :
    let row:=preparedExecGhostRow (tr.cell t r)
    let next:=preparedExecGhostNext (tr.cell t r) (tr.cell t (r+1)) (fun i=>pub.getD i 0)
    let fields:=preparedExecGhostPub (tr.cell t r) (tr.cell t (r+1)) (fun i=>pub.getD i 0)
    preparedRowChoices row next fields 0 0 ∧ PreparedAddTransitionHolds row next fields := by
  constructor
  · apply prepared_exec_python_choices
    · intro i hi
      have h:=localH.constr r (by omega) _ (prepared_control_literal_condition_source.boolean i (by omega))
      change tr.cell t r i*(tr.cell t r i+ -(1:Fp))+ -(0:Fp)=0 at h
      grind
    · exact prepared_control_legacy_source_eval tr t r pub localH nonlast branchZero _ prepared_control_legacy_choice_source
  · exact prepared_exec_transition_holds _ _ _
      (prepared_control_legacy_source_eval tr t r pub localH nonlast branchZero _ prepared_control_legacy_sp_source)
      (fun slot hs limb hi=>prepared_control_legacy_source_eval tr t r pub localH nonlast branchZero _
        (prepared_control_legacy_stack_source slot hs limb hi))

end NearCompression
