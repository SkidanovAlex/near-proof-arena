import NearCompression.TerminalDAGTotalSemantics
namespace NearCompression
open Lean.Grind
variable {K : Type} [Field K]

/-- Exact simplifications in compile_terminal.op. Constant-folding records the
actual field operation; all other shortcuts record their zero/one nodes. -/
inductive TerminalArithmeticRoute (nodes : Nat → TerminalDAGNode K) : GKRBinaryOp → Nat → Nat → Nat → Prop where
  | direct {op x y z} : nodes z=.binary op x y → TerminalArithmeticRoute nodes op x y z
  | constant {op x y z a b} : nodes x=.constant a → nodes y=.constant b →
      nodes z=.constant (gkrGateValue op a b) → TerminalArithmeticRoute nodes op x y z
  | addZeroLeft {x y} : nodes x=.constant 0 → TerminalArithmeticRoute nodes .add x y y
  | addZeroRight {x y} : nodes y=.constant 0 → TerminalArithmeticRoute nodes .add x y x
  | subZeroRight {x y} : nodes y=.constant 0 → TerminalArithmeticRoute nodes .sub x y x
  | subSame {x z} : nodes z=.constant 0 → TerminalArithmeticRoute nodes .sub x x z
  | mulZeroLeft {x y} : nodes x=.constant 0 → TerminalArithmeticRoute nodes .mul x y x
  | mulZeroRight {x y} : nodes y=.constant 0 → TerminalArithmeticRoute nodes .mul x y y
  | mulOneLeft {x y} : nodes x=.constant 1 → TerminalArithmeticRoute nodes .mul x y y
  | mulOneRight {x y} : nodes y=.constant 1 → TerminalArithmeticRoute nodes .mul x y x

theorem terminal_arithmetic_route_value (nodes : Nat → TerminalDAGNode K)
    (inputs values : Nat → K)
    (equations : ∀ i,values i=terminalNodeValue inputs values (nodes i))
    (op : GKRBinaryOp) (x y z : Nat) (route : TerminalArithmeticRoute nodes op x y z) :
    values z=gkrGateValue op (values x) (values y) := by
  have hx := equations x
  have hy := equations y
  have hz := equations z
  clear equations
  cases route <;> simp_all only [terminalNodeValue,gkrGateValue] <;> grind

/-- Instantiation with the independently executed emitted DAG removes any
assumed node-value equations from the optimization correctness statement. -/
theorem terminal_arithmetic_executed (inputs : Nat → K) (nodes : List (TerminalDAGNode K))
    (acyclic : TerminalDAGAcyclic 0 nodes) (op : GKRBinaryOp) (x y z : Nat)
    (route : TerminalArithmeticRoute (fun i => nodes.getD i (.constant 0)) op x y z) :
    terminalDAGRun inputs 0 (fun _ => 0) nodes z=
      gkrGateValue op (terminalDAGRun inputs 0 (fun _ => 0) nodes x)
        (terminalDAGRun inputs 0 (fun _ => 0) nodes y) :=
  terminal_arithmetic_route_value _ inputs _ (terminal_dag_total_equations inputs nodes acyclic) op x y z route
end NearCompression
