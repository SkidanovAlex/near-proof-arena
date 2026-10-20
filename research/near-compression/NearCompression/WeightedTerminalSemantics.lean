import NearCompression.AIRProgramAccumulation
import NearCompression.BusProgramFormulas
import NearCompression.TerminalRebuildCertificate
namespace NearCompression
open Lean.Grind ZkFormal.Air
variable {K : Type} [Field K]

/-- Ordered, shape-exact residual/register alignment. No zip truncation. -/
inductive ResidualRoutes {A : Type} (route : A → Nat → Prop) : List A → List Nat → Prop where
  | empty : ResidualRoutes route [] []
  | cons {a i rest indices} : route a i → ResidualRoutes route rest indices →
      ResidualRoutes route (a::rest) (i::indices)

def terminalMixValues (mixing power : K) : List K → K
  | [] => 0
  | value::rest => power*value+terminalMixValues mixing (power*mixing) rest

def terminalSourceAuxValues (env : TerminalProgramEnvironment K) (pubValues : List K)
    (source : List Expr) (auxiliary : List (BusProgramFormula K)) : List K :=
  source.map (fun e => e.evalWith (airProgramEnv env pubValues))++
    auxiliary.map (busProgramFormulaValue env)

theorem terminal_mix_register_values (registers : Nat → K) (mixing power : K) (indices : List Nat) :
    airMixValue registers mixing power indices=terminalMixValues mixing power (indices.map registers) := by
  induction indices generalizing power with
  | nil => rfl
  | cons i rest ih => simp only [airMixValue,terminalMixValues,List.map_cons,ih]

omit [Field K] in
theorem residual_routes_values {A : Type} (route : A → Nat → Prop) (value : A → K)
    (registers : Nat → K) (correct : ∀ a i,route a i → registers i=value a)
    (expressions : List A) (indices : List Nat) (routes : ResidualRoutes route expressions indices) :
    indices.map registers=expressions.map value := by
  induction routes with
  | empty => rfl
  | cons h rest ih => simp only [List.map_cons,correct _ _ h,ih]

/-- Exact compiler semantics for the mixed residual at arbitrary field-valued
terminal inputs. This is an equality, not an inference from mixed value zero
to every residual zero. Current/next and selectors need not be Boolean here. -/
theorem source_aux_program_value (env : TerminalProgramEnvironment K) (pubValues : List K)
    (program : List (TerminalInstruction K))
    (acyclic : TerminalDAGAcyclic 0 (program.map (terminalProgramNode env)))
    (source : List Expr) (auxiliary : List (BusProgramFormula K)) (sourceRegs auxRegs : List Nat)
    (sourceRoutes : ResidualRoutes (AIRProgramRoute (fun i => program.getD i terminalDefaultInstruction) pubValues) source sourceRegs)
    (auxRoutes : ResidualRoutes (BusProgramFormulaRoute (fun i => program.getD i terminalDefaultInstruction)) auxiliary auxRegs)
    (mixing : K) (zeroReg total output : Nat)
    (zeroNode : program.getD zeroReg terminalDefaultInstruction=⟨.constant,0,0,0⟩)
    (accumulate : AIRAccumulatorRoute (fun i => program.getD i terminalDefaultInstruction)
      zeroReg (airMixResiduals mixing 1 (sourceRegs++auxRegs)) total)
    (finish : program.getD output terminalDefaultInstruction=⟨.add,total,zeroReg,0⟩) :
    terminalProgramRun env 0 (fun _ => 0) program output=
      terminalMixValues mixing 1 (terminalSourceAuxValues env pubValues source auxiliary) := by
  rw [air_program_weighted_finish env program acyclic mixing (sourceRegs++auxRegs) zeroReg total output zeroNode accumulate finish]
  rw [terminal_mix_register_values,List.map_append]
  have hs := residual_routes_values _ _ _ (air_program_executed_value env pubValues program acyclic)
    source sourceRegs sourceRoutes
  have ha := residual_routes_values _ _ _ (bus_program_formula_executed env program acyclic)
    auxiliary auxRegs auxRoutes
  rw [hs,ha]
  rfl

/-- The actual terminal compiler multiplies by its caller-derived row equality
weight after rebuilding. Both target nodes and multiplication are certified.
No nonzero weight condition is needed, including when the weight is zero. -/
theorem source_aux_terminal_weighted_value (env : TerminalProgramEnvironment K) (pubValues : List K)
    (program : List (TerminalInstruction K)) (nodes : List (TerminalDAGNode K)) (inputs : Nat → K)
    (sourceAcyclic : TerminalDAGAcyclic 0 (program.map (terminalProgramNode env)))
    (targetAcyclic : TerminalDAGAcyclic 0 nodes)
    (source : List Expr) (auxiliary : List (BusProgramFormula K)) (sourceRegs auxRegs : List Nat)
    (sourceRoutes : ResidualRoutes (AIRProgramRoute (fun i => program.getD i terminalDefaultInstruction) pubValues) source sourceRegs)
    (auxRoutes : ResidualRoutes (BusProgramFormulaRoute (fun i => program.getD i terminalDefaultInstruction)) auxiliary auxRegs)
    (mixing weight : K) (zeroReg total output rebuilt weightNode terminal : Nat)
    (zeroNode : program.getD zeroReg terminalDefaultInstruction=⟨.constant,0,0,0⟩)
    (accumulate : AIRAccumulatorRoute (fun i => program.getD i terminalDefaultInstruction)
      zeroReg (airMixResiduals mixing 1 (sourceRegs++auxRegs)) total)
    (finish : program.getD output terminalDefaultInstruction=⟨.add,total,zeroReg,0⟩)
    (rebuild : TerminalRebuildRoute
      (fun i => (program.map (terminalProgramNode env)).getD i (.constant 0))
      (fun i => nodes.getD i (.constant 0)) inputs output rebuilt)
    (weightLiteral : nodes.getD weightNode (.constant 0)=.constant weight)
    (multiply : TerminalArithmeticRoute (fun i => nodes.getD i (.constant 0)) .mul rebuilt weightNode terminal) :
    terminalDAGRun inputs 0 (fun _ => 0) nodes terminal=
      weight*terminalMixValues mixing 1 (terminalSourceAuxValues env pubValues source auxiliary) := by
  have hm := terminal_arithmetic_executed inputs nodes targetAcyclic .mul rebuilt weightNode terminal multiply
  have hr := terminal_program_rebuilt_value env program nodes inputs sourceAcyclic targetAcyclic output rebuilt rebuild
  have hw := terminal_dag_total_equations inputs nodes targetAcyclic weightNode
  simp only [weightLiteral,terminalNodeValue] at hw
  have hp := source_aux_program_value env pubValues program sourceAcyclic source auxiliary sourceRegs auxRegs
    sourceRoutes auxRoutes mixing zeroReg total output zeroNode accumulate finish
  rw [hr,hp,hw] at hm
  simp only [gkrGateValue] at hm
  grind
end NearCompression
