import NearCompression.AIRProgramLowering
import NearCompression.BusAuxiliarySemantics
namespace NearCompression
open Lean.Grind
variable {K : Type} [Field K]

/-- Auxiliary arithmetic needs arbitrary extension-valued constants, unlike
source Expr.const's natural constants. These are exact ABI operations. -/
inductive BusProgramFormula (K : Type) where
  | literal (value : K)
  | current (column : Nat)
  | next (column : Nat)
  | first | last | transition
  | add (a b : BusProgramFormula K)
  | sub (a b : BusProgramFormula K)
  | mul (a b : BusProgramFormula K)

def busProgramFormulaValue (env : TerminalProgramEnvironment K) : BusProgramFormula K → K
  | .literal value => value
  | .current column => env.current column
  | .next column => env.next column
  | .first => env.first | .last => env.last | .transition => env.transition
  | .add a b => busProgramFormulaValue env a+busProgramFormulaValue env b
  | .sub a b => busProgramFormulaValue env a-busProgramFormulaValue env b
  | .mul a b => busProgramFormulaValue env a*busProgramFormulaValue env b

inductive BusProgramFormulaRoute (program : Nat → TerminalInstruction K) : BusProgramFormula K → Nat → Prop where
  | literal {value i} : program i=⟨.constant,0,0,value⟩ → BusProgramFormulaRoute program (.literal value) i
  | current {c i} : program i=⟨.current,c,0,0⟩ → BusProgramFormulaRoute program (.current c) i
  | next {c i} : program i=⟨.next,c,0,0⟩ → BusProgramFormulaRoute program (.next c) i
  | first {i} : program i=⟨.first,0,0,0⟩ → BusProgramFormulaRoute program .first i
  | last {i} : program i=⟨.last,0,0,0⟩ → BusProgramFormulaRoute program .last i
  | transition {i} : program i=⟨.transition,0,0,0⟩ → BusProgramFormulaRoute program .transition i
  | add {a b x y i} : BusProgramFormulaRoute program a x → BusProgramFormulaRoute program b y →
      program i=⟨.add,x,y,0⟩ → BusProgramFormulaRoute program (.add a b) i
  | sub {a b x y i} : BusProgramFormulaRoute program a x → BusProgramFormulaRoute program b y →
      program i=⟨.sub,x,y,0⟩ → BusProgramFormulaRoute program (.sub a b) i
  | mul {a b x y i} : BusProgramFormulaRoute program a x → BusProgramFormulaRoute program b y →
      program i=⟨.mul,x,y,0⟩ → BusProgramFormulaRoute program (.mul a b) i

theorem bus_program_formula_route_value (env : TerminalProgramEnvironment K)
    (program : Nat → TerminalInstruction K) (registers : Nat → K)
    (equations : ∀ i,registers i=terminalProgramInstructionValue env registers (program i))
    (e : BusProgramFormula K) (i : Nat) (route : BusProgramFormulaRoute program e i) :
    registers i=busProgramFormulaValue env e := by
  induction route with
  | @literal value i h | @current value i h | @next value i h =>
    have eq := equations i
    simpa only [h,terminalProgramInstructionValue,busProgramFormulaValue] using eq
  | @first i h | @last i h | @transition i h =>
    have eq := equations i
    simpa only [h,terminalProgramInstructionValue,busProgramFormulaValue] using eq
  | @add a b x y i ra rb h ha hb | @sub a b x y i ra rb h ha hb | @mul a b x y i ra rb h ha hb =>
    have eq := equations i
    simpa only [h,terminalProgramInstructionValue,busProgramFormulaValue,ha,hb] using eq

theorem bus_program_formula_executed (env : TerminalProgramEnvironment K)
    (program : List (TerminalInstruction K))
    (acyclic : TerminalDAGAcyclic 0 (program.map (terminalProgramNode env)))
    (e : BusProgramFormula K) (i : Nat)
    (route : BusProgramFormulaRoute (fun j => program.getD j terminalDefaultInstruction) e i) :
    terminalProgramRun env 0 (fun _ => 0) program i=busProgramFormulaValue env e :=
  bus_program_formula_route_value env _ _ (terminal_program_total_equations env program acyclic) e i route

def busSquareFormula (previous current : BusProgramFormula K) : BusProgramFormula K :=
  .sub current (.mul previous previous)

def busProductFormula (bit power previous current : BusProgramFormula K) : BusProgramFormula K :=
  .sub current (.mul previous (.add (.literal 1) (.mul bit (.sub power (.literal 1)))))

def busBoundaryFormulas (a an factor : BusProgramFormula K) (final : K) : List (BusProgramFormula K) :=
  [.mul .first (.sub a (.literal 1)),
   .mul .transition (.sub an (.mul a factor)),
   .mul .last (.sub (.mul a factor) (.literal final))]

theorem bus_square_formula_value (env : TerminalProgramEnvironment K) (previous current : BusProgramFormula K) :
    busProgramFormulaValue env (busSquareFormula previous current)=
      busProgramFormulaValue env current-busProgramFormulaValue env previous*busProgramFormulaValue env previous := rfl

theorem bus_product_formula_value (env : TerminalProgramEnvironment K)
    (bit power previous current : BusProgramFormula K) :
    busProgramFormulaValue env (busProductFormula bit power previous current)=
      busProgramFormulaValue env current-busProgramFormulaValue env previous*
        busBitSelect (busProgramFormulaValue env bit) (busProgramFormulaValue env power) := rfl

theorem bus_boundary_formulas_value (env : TerminalProgramEnvironment K)
    (a an factor : BusProgramFormula K) (final : K) :
    (busBoundaryFormulas a an factor final).map (busProgramFormulaValue env)=
      [env.first*(busProgramFormulaValue env a-1),
       env.transition*(busProgramFormulaValue env an-busProgramFormulaValue env a*busProgramFormulaValue env factor),
       env.last*(busProgramFormulaValue env a*busProgramFormulaValue env factor-final)] := rfl
end NearCompression
