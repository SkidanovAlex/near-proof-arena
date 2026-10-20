import NearCompression.AIRExpressionCheck
import NearCompression.AIRProgramAccumulation
namespace NearCompression
open Lean.Grind ZkFormal.Air

structure AIRAccumulatorStep where
  residual : Nat
  coefficient : Nat
  product : Nat
  next : Nat

def airAccumulatorCheck {K : Type} [Field K] [DecidableEq K]
    (program : List (TerminalInstruction K)) (mixing : K) :
    K → Nat → List AIRAccumulatorStep → Nat → Bool
  | _,start,[],finish => decide (start=finish)
  | power,start,s::rest,finish =>
    decide (start<program.length ∧ s.residual<program.length ∧ s.coefficient<program.length ∧
      s.product<program.length ∧ s.next<program.length ∧
      program.getD s.coefficient terminalDefaultInstruction=⟨.constant,0,0,power⟩ ∧
      program.getD s.product terminalDefaultInstruction=⟨.mul,s.coefficient,s.residual,0⟩ ∧
      program.getD s.next terminalDefaultInstruction=⟨.add,start,s.product,0⟩) &&
    airAccumulatorCheck program mixing (power*mixing) s.next rest finish

theorem air_accumulator_checked {K : Type} [Field K] [DecidableEq K]
    (program : List (TerminalInstruction K)) (mixing power : K)
    (start finish : Nat) (steps : List AIRAccumulatorStep)
    (h : airAccumulatorCheck program mixing power start steps finish=true) :
    AIRAccumulatorRoute (fun i => program.getD i terminalDefaultInstruction) start
      (airMixResiduals mixing power (steps.map (fun s => s.residual))) finish := by
  induction steps generalizing power start with
  | nil =>
    simp only [airAccumulatorCheck,decide_eq_true_eq] at h
    subst finish
    exact .empty start
  | cons s rest ih =>
    simp only [airAccumulatorCheck,Bool.and_eq_true,decide_eq_true_eq] at h
    obtain ⟨⟨_,_,_,_,_,hc,hp,hn⟩,tail⟩ := h
    exact .step hc hp hn (ih (power*mixing) s.next tail)

def airWeightedProgramCheck {K : Type} [Field K] [DecidableEq K]
    (program : List (TerminalInstruction K)) (mixing : K) (residuals : List Nat)
    (zeroReg total output : Nat) (steps : List AIRAccumulatorStep) : Bool :=
  decide (zeroReg<program.length ∧ output<program.length ∧ output+1=program.length ∧
    program.getD zeroReg terminalDefaultInstruction=⟨.constant,0,0,0⟩ ∧
    program.getD output terminalDefaultInstruction=⟨.add,total,zeroReg,0⟩ ∧
    steps.map (fun s => s.residual)=residuals) &&
  airAccumulatorCheck program mixing 1 zeroReg steps total

theorem air_weighted_program_checked {K : Type} [Field K] [DecidableEq K]
    (env : TerminalProgramEnvironment K) (program : List (TerminalInstruction K))
    (mixing : K) (residuals : List Nat) (zeroReg total output : Nat) (steps : List AIRAccumulatorStep)
    (acyclic : terminalAcyclicCheck 0 (program.map (terminalProgramNode env))=true)
    (h : airWeightedProgramCheck program mixing residuals zeroReg total output steps=true) :
    terminalProgramRun env 0 (fun _ => 0) program output=
      airMixValue (terminalProgramRun env 0 (fun _ => 0) program) mixing 1 residuals := by
  simp only [airWeightedProgramCheck,Bool.and_eq_true,decide_eq_true_eq] at h
  obtain ⟨⟨_,_,_,zeroNode,finish,order⟩,check⟩ := h
  have route := air_accumulator_checked program mixing 1 zeroReg total steps check
  rw [order] at route
  exact air_program_weighted_finish env program (terminal_acyclic_checked _ 0 acyclic)
    mixing residuals zeroReg total output zeroNode route finish

def airExpressionMixValue {K : Type} [Field K]
    (env : TerminalProgramEnvironment K) (pubValues : List K) (mixing : K) : K → List (Expr × Nat) → K
  | _,[] => 0
  | power,(expr,_)::rest => power*expr.evalWith (airProgramEnv env pubValues)+
      airExpressionMixValue env pubValues mixing (power*mixing) rest

theorem air_expression_mix_checked {K : Type} [Field K] [DecidableEq K]
    (env : TerminalProgramEnvironment K) (program : List (TerminalInstruction K))
    (pubValues : List K) (width : Nat) (mixing power : K) (residuals : List (Expr × Nat))
    (acyclic : terminalAcyclicCheck 0 (program.map (terminalProgramNode env))=true)
    (checked : residuals.all (fun r => airExpressionCheck program pubValues width r.1 r.2)=true) :
    airMixValue (terminalProgramRun env 0 (fun _ => 0) program) mixing power (residuals.map Prod.snd)=
      airExpressionMixValue env pubValues mixing power residuals := by
  induction residuals generalizing power with
  | nil => rfl
  | cons r rest ih =>
    simp only [List.all_cons,Bool.and_eq_true] at checked
    simp only [List.map_cons,airMixValue,airExpressionMixValue]
    rw [air_expression_checked_execution env program pubValues width r.1 r.2 acyclic checked.1,
      ih (power*mixing) checked.2]

/-- Both expression meaning and exact ordered accumulation are checked. This
covers residuals represented as AIR Expr; auxiliary bus formulas require their
own meaning proof before they can be included in an analogous full-table result. -/
theorem air_weighted_expressions_checked {K : Type} [Field K] [DecidableEq K]
    (env : TerminalProgramEnvironment K) (program : List (TerminalInstruction K))
    (pubValues : List K) (width : Nat) (mixing : K) (residuals : List (Expr × Nat))
    (zeroReg total output : Nat) (steps : List AIRAccumulatorStep)
    (acyclic : terminalAcyclicCheck 0 (program.map (terminalProgramNode env))=true)
    (expressions : residuals.all (fun r => airExpressionCheck program pubValues width r.1 r.2)=true)
    (accumulation : airWeightedProgramCheck program mixing (residuals.map Prod.snd) zeroReg total output steps=true) :
    terminalProgramRun env 0 (fun _ => 0) program output=
      airExpressionMixValue env pubValues mixing 1 residuals := by
  rw [air_weighted_program_checked env program mixing _ zeroReg total output steps acyclic accumulation]
  exact air_expression_mix_checked env program pubValues width mixing 1 residuals acyclic expressions

theorem air_weighted_expressions_compiled {K : Type} [Field K] [DecidableEq K]
    (nodes : List (TerminalDAGNode K)) (inputs : Nat → K) (table : TerminalCompiledTable K)
    (pubValues : List K) (width : Nat) (mixing : K) (residuals : List (Expr × Nat))
    (zeroReg total : Nat) (steps : List AIRAccumulatorStep)
    (acyclic : terminalAcyclicCheck 0 nodes=true)
    (tableCheck : terminalCompiledTableCheck nodes inputs table=true)
    (expressions : residuals.all (fun r => airExpressionCheck table.program pubValues width r.1 r.2)=true)
    (accumulation : airWeightedProgramCheck table.program mixing (residuals.map Prod.snd)
      zeroReg total table.sourceRoot steps=true) :
    terminalDAGRun inputs 0 (fun _ => 0) nodes table.entry.root=
      airExpressionMixValue table.environment pubValues mixing 1 residuals := by
  rw [terminal_compiled_table_checked nodes inputs table acyclic tableCheck]
  simp only [terminalCompiledTableCheck,Bool.and_eq_true] at tableCheck
  exact air_weighted_expressions_checked table.environment table.program pubValues width mixing
    residuals zeroReg total table.sourceRoot steps tableCheck.1 expressions accumulation

private def accumulationSmokeProgram : List (TerminalInstruction Rat) :=
  [⟨.constant,0,0,0⟩,⟨.current,0,0,0⟩,⟨.next,0,0,0⟩,⟨.constant,0,0,1⟩,
   ⟨.mul,3,1,0⟩,⟨.add,0,4,0⟩,⟨.constant,0,0,7⟩,⟨.mul,6,2,0⟩,
   ⟨.add,5,7,0⟩,⟨.add,8,0,0⟩]
private def accumulationSmokeSteps : List AIRAccumulatorStep := [⟨1,3,4,5⟩,⟨2,6,7,8⟩]

theorem air_accumulator_check_regressions :
    airWeightedProgramCheck accumulationSmokeProgram 7 [1,2] 0 8 9 accumulationSmokeSteps=true ∧
    airWeightedProgramCheck accumulationSmokeProgram 8 [1,2] 0 8 9 accumulationSmokeSteps=false ∧
    airWeightedProgramCheck accumulationSmokeProgram 7 [2,1] 0 8 9 accumulationSmokeSteps=false ∧
    airWeightedProgramCheck accumulationSmokeProgram 7 [1,2] 0 8 8 accumulationSmokeSteps=false ∧
    airWeightedProgramCheck accumulationSmokeProgram 7 [1,2] 0 8 9
      [⟨1,3,4,5⟩,⟨2,3,7,8⟩]=false ∧
    airWeightedProgramCheck accumulationSmokeProgram 7 [1,2] 0 8 9
      [⟨1,3,4,5⟩,⟨99,6,7,8⟩]=false ∧
    airWeightedProgramCheck accumulationSmokeProgram 7 [1,2] 0 8 9 []=false ∧
    airWeightedProgramCheck [⟨.constant,0,0,(0:Rat)⟩,⟨.add,0,0,0⟩] 0 [] 0 0 1 []=true := by decide +kernel

end NearCompression
