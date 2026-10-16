import NearCompression.PreparedLiteral
import NearCompression.PreparedExecTerminal
import NearCompression.PreparedExecStackClosure

namespace NearCompression
open ZkFormal.Air
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000

private def noFirstDec : (e : Expr) → Decidable (preparedNoFirst e)
  | .isFirst => isFalse id
  | .add a b | .mul a b =>
    letI := noFirstDec a
    letI := noFirstDec b
    inferInstanceAs (Decidable (preparedNoFirst a ∧ preparedNoFirst b))
  | .neg a => noFirstDec a
  | .const _ | .col _ _ | .pub _ | .isLast | .isTransition => isTrue True.intro
attribute [local instance] noFirstDec

private theorem exec_member (i : Nat) (hi : i<726) (e : Expr)
    (eq : preparedLiteralExec[i]'hi=e) : e∈preparedLiteralExec := by
  rw [←eq]
  exact List.getElem_mem hi
private theorem code_member (i : Nat) (hi : i<473) (e : Expr)
    (eq : preparedLiteralCode[i]'hi=e) : e∈preparedLiteralCode := by
  rw [←eq]
  exact List.getElem_mem hi

private theorem exec_source (i : Nat) (hi : i<726) (e : Expr)
    (shape : preparedNoFirst (preparedLiteralExec[i]'hi) ∧
      preparedExecSimplify (preparedLiteralExec[i]'hi)=preparedExecLower e) :
    PreparedExecHasSource (preparedCodeExecTable preparedLiteralExec preparedLiteralBoundary) e := by
  exact ⟨_,List.getElem_mem hi,shape.1,shape.2⟩

theorem prepared_literal_exec_boolean :
    ∀ i,i<605 → preparedGasBoolean i∈preparedLiteralExec := by
  have all : ∀ i:Fin 605,preparedLiteralExec[i.val]'(by change _<726;omega)=preparedGasBoolean i.val := by decide
  intro i hi
  exact exec_member i (by omega) _ (all ⟨i,hi⟩)

theorem prepared_literal_code_boolean :
    ∀ i,i<198 → preparedGasBoolean i∈preparedLiteralCode := by
  have all : ∀ i:Fin 198,preparedLiteralCode[i.val]'(by change _<473;omega)=preparedGasBoolean i.val := by decide
  intro i hi
  exact code_member i (by omega) _ (all ⟨i,hi⟩)

theorem prepared_literal_code_order :
    PreparedCodeOrderSource (preparedCodeDataTable preparedLiteralCode) := by
  refine ⟨prepared_literal_code_boolean,?_,?_,?_,?_⟩
  · have all : ∀ i:Fin 32,preparedLiteralCode[199+2*i.val]'(by change _<473;omega)=preparedCodeFirstPC i.val := by decide
    intro i hi
    exact code_member (199+2*i) (by omega) _ (all ⟨i,hi⟩)
  · exact code_member 263 (by decide) _ rfl
  · exact code_member 264 (by decide) _ rfl
  · exact code_member 265 (by decide) _ rfl

theorem prepared_literal_code_inactive :
    ∀ i,i<25 → preparedCodeInactive (172+i)∈preparedLiteralCode := by
  have all : ∀ i:Fin 25,preparedLiteralCode[437+i.val]'(by change _<473;omega)=preparedCodeInactive (172+i.val) := by decide
  intro i hi
  exact code_member (437+i) (by omega) _ (all ⟨i,hi⟩)

theorem prepared_literal_exec_pc :
    PreparedExecPCSource (preparedCodeExecTable preparedLiteralExec preparedLiteralBoundary) := by
  exact ⟨prepared_literal_exec_boolean,exec_member 649 (by decide) _ rfl,
    exec_member 650 (by decide) _ rfl⟩

theorem prepared_literal_exec_gas :
    PreparedExecGasSource (preparedCodeExecTable preparedLiteralExec preparedLiteralBoundary) := by
  refine ⟨prepared_literal_exec_pc,?_,?_⟩
  · have all : ∀ i:Fin 4,preparedLiteralExec[643+i.val]'(by change _<726;omega)=preparedExecGasSubtract i.val := by decide
    intro i hi
    exact exec_member (643+i) (by omega) _ (all ⟨i,hi⟩)
  · have all : ∀ i:Fin 4,preparedLiteralExec[688+i.val]'(by change _<726;omega)=preparedExecGasUpdate i.val := by decide
    intro i hi
    exact exec_member (688+i) (by omega) _ (all ⟨i,hi⟩)

theorem prepared_literal_exec_local :
    PreparedExecLocalSource (preparedCodeExecTable preparedLiteralExec preparedLiteralBoundary) := by
  refine ⟨prepared_literal_exec_boolean,?_,?_,?_,?_,?_⟩
  · exact exec_source 605 (by decide) _ (by decide)
  · exact exec_source 683 (by decide) _ (by decide)
  · have all : ∀ slot:Fin 8,∀ limb:Fin 2,
        preparedNoFirst (preparedLiteralExec[695+4*slot.val+2*limb.val]'(by change _<726;omega)) ∧
        preparedExecSimplify (preparedLiteralExec[695+4*slot.val+2*limb.val]'(by change _<726;omega))=
          preparedExecLower (preparedStackStepPython slot.val limb.val) := by decide
    intro slot hs limb hl
    exact exec_source _ (by omega) _ (all ⟨slot,hs⟩ ⟨limb,hl⟩)
  · exact exec_source 685 (by decide) _ (by decide)
  · have all : ∀ i:Fin 2,preparedNoFirst (preparedLiteralExec[692+i.val]'(by change _<726;omega)) ∧
        preparedExecSimplify (preparedLiteralExec[692+i.val]'(by change _<726;omega))=
          preparedExecLower (preparedAddCarryPython i.val) := by decide
    intro i hi
    exact exec_source _ (by omega) _ (all ⟨i,hi⟩)

theorem prepared_literal_exec_closure :
    PreparedExecClosureSource (preparedCodeExecTable preparedLiteralExec preparedLiteralBoundary) := by
  exact ⟨prepared_literal_exec_local,exec_member 605 (by decide) _ rfl,
    exec_source 606 (by decide) _ (by decide),exec_source 647 (by decide) _ (by decide),
    exec_source 648 (by decide) _ (by decide)⟩

theorem prepared_literal_exec_stack_guard (push : Bool) :
    PreparedExecHasSource (preparedCodeExecTable preparedLiteralExec preparedLiteralBoundary)
      (preparedExecStackDepth push) := by
  cases push
  · exact exec_source 686 (by decide) _ (by decide)
  · exact exec_source 684 (by decide) _ (by decide)

theorem prepared_literal_exec_end_guard :
    PreparedExecHasSource (preparedCodeExecTable preparedLiteralExec preparedLiteralBoundary) preparedEndDepthPython := by
  exact exec_source 687 (by decide) _ (by decide)

end NearCompression
