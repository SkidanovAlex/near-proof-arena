import NearCompression.CodeSwitchFunctional

/-! Honest arithmetic composition of fold blocks and constraint injection.
Query/OOD honesty is an explicit premise, not inferred from authentication.
No malicious-source extraction or protocol soundness is claimed. -/
namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

structure SwitchArithmeticStage (K : Type) where
  challenges : List K
  constraints : List (SwitchConstraint K)
  terminalSize : Nat

def switchStageNext (xs : List (K × K)) (stage : SwitchArithmeticStage K) : List (K × K) × K :=
  let folded:=affineFoldFinal xs stage.challenges
  switchInjectAll folded (affineFoldDot folded) stage.constraints

def switchStageHonest (xs : List (K × K)) (stage : SwitchArithmeticStage K) : Prop :=
  xs.length=stage.terminalSize*2^stage.challenges.length ∧
  ∀ c ∈ stage.constraints,c.answer=(Poly.mk ((affineFoldFinal xs stage.challenges).map Prod.fst)).eval c.point

def switchStageRun [DecidableEq K] (xs : List (K × K)) (claim : K)
    (stage : SwitchArithmeticStage K) : Option (List (K × K) × K) :=
  match whirRunArithmetic claim (affineFoldRounds xs stage.challenges) with
  | none => none
  | some foldedClaim => some (switchInjectAll (affineFoldFinal xs stage.challenges) foldedClaim stage.constraints)

theorem switch_inject_all_coefficients (xs : List (K × K)) (claim : K)
    (constraints : List (SwitchConstraint K)) :
    (switchInjectAll xs claim constraints).1.map Prod.fst=xs.map Prod.fst := by
  induction constraints generalizing xs claim with
  | nil => rfl
  | cons c rest ih =>
    simp only [switchInjectAll]
    rw [ih,switch_inject_coefficients]

/-- Generated sumcheck rounds plus true evaluation constraints preserve the
continuing functional and exact terminal degree shape. -/
theorem switch_stage_honest [DecidableEq K] (xs : List (K × K))
    (stage : SwitchArithmeticStage K) (honest : switchStageHonest xs stage) :
    switchStageRun xs (affineFoldDot xs) stage=some (switchStageNext xs stage) ∧
    affineFoldDot (switchStageNext xs stage).1=(switchStageNext xs stage).2 ∧
    (switchStageNext xs stage).1.length=stage.terminalSize := by
  have folded:=repeated_affine_honest stage.challenges xs stage.terminalSize honest.1
  refine ⟨?_,?_,?_⟩
  · unfold switchStageRun
    rw [folded.1]
    rfl
  · exact switch_inject_all_honest _ _ stage.constraints rfl honest.2
  · have preserved:=congrArg List.length (switch_inject_all_coefficients
        (affineFoldFinal xs stage.challenges) (affineFoldDot (affineFoldFinal xs stage.challenges)) stage.constraints)
    simp only [List.length_map] at preserved
    exact preserved.trans folded.2

def switchChainNext (xs : List (K × K)) : List (SwitchArithmeticStage K) → List (K × K) × K
  | [] => (xs,affineFoldDot xs)
  | s::rest => switchChainNext (switchStageNext xs s).1 rest

def switchChainHonest (xs : List (K × K)) : List (SwitchArithmeticStage K) → Prop
  | [] => True
  | s::rest => switchStageHonest xs s ∧ switchChainHonest (switchStageNext xs s).1 rest

def switchChainRun [DecidableEq K] (xs : List (K × K)) (claim : K) :
    List (SwitchArithmeticStage K) → Option (List (K × K) × K)
  | [] => some (xs,claim)
  | s::rest => match switchStageRun xs claim s with
      | none => none
      | some next => switchChainRun next.1 next.2 rest

/-- Every stage consumes the previous stage's updated weights and claim;
there is no reset to the original functional between code switches. -/
theorem switch_chain_honest [DecidableEq K] (xs : List (K × K))
    (stages : List (SwitchArithmeticStage K)) (honest : switchChainHonest xs stages) :
    switchChainRun xs (affineFoldDot xs) stages=some (switchChainNext xs stages) ∧
    affineFoldDot (switchChainNext xs stages).1=(switchChainNext xs stages).2 := by
  induction stages generalizing xs with
  | nil => exact ⟨rfl,rfl⟩
  | cons s rest ih =>
    have step:=switch_stage_honest xs s honest.1
    have tail:=ih (switchStageNext xs s).1 honest.2
    constructor
    · simp only [switchChainRun,step.1]
      rw [←step.2.1]
      exact tail.1
    · exact tail.2
end NearCompression
