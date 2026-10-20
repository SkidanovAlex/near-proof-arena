import NearCompression.TerminalProgramSemantics
import ZkFormal.Air.Basic
namespace NearCompression
open Lean.Grind ZkFormal.Air
variable {K : Type} [Field K]

def airProgramEnv (env : TerminalProgramEnvironment K) (pubValues : List K) : Env K where
  ofNat := fun n => (@Nat.cast K Semiring.natCast n)
  add := (·+·)
  mul := (·*·)
  neg := Neg.neg
  col := fun c nx => if nx then env.next c else env.current c
  pub := fun i => pubValues.getD i 0
  isFirst := env.first
  isLast := env.last
  isTransition := env.transition

/-- Exact Program.emit register shapes, including unused zero words. A register
can be shared by multiple certificates, as in the actual hash-consing cache. -/
inductive AIRProgramRoute (program : Nat → TerminalInstruction K) (pubValues : List K) : Expr → Nat → Prop where
  | constant {n i : Nat} : program i=⟨.constant,0,0,(@Nat.cast K Semiring.natCast n)⟩ → AIRProgramRoute program pubValues (.const n) i
  | publicValue {p i} : program i=⟨.constant,0,0,pubValues.getD p 0⟩ → AIRProgramRoute program pubValues (.pub p) i
  | current {c i} : program i=⟨.current,c,0,0⟩ → AIRProgramRoute program pubValues (.col c false) i
  | next {c i} : program i=⟨.next,c,0,0⟩ → AIRProgramRoute program pubValues (.col c true) i
  | first {i} : program i=⟨.first,0,0,0⟩ → AIRProgramRoute program pubValues .isFirst i
  | last {i} : program i=⟨.last,0,0,0⟩ → AIRProgramRoute program pubValues .isLast i
  | transition {i} : program i=⟨.transition,0,0,0⟩ → AIRProgramRoute program pubValues .isTransition i
  | add {a b x y i} : AIRProgramRoute program pubValues a x → AIRProgramRoute program pubValues b y →
      program i=⟨.add,x,y,0⟩ → AIRProgramRoute program pubValues (.add a b) i
  | mul {a b x y i} : AIRProgramRoute program pubValues a x → AIRProgramRoute program pubValues b y →
      program i=⟨.mul,x,y,0⟩ → AIRProgramRoute program pubValues (.mul a b) i
  | neg {a x zeroReg i} : AIRProgramRoute program pubValues a x →
      program zeroReg=⟨.constant,0,0,0⟩ → program i=⟨.sub,zeroReg,x,0⟩ → AIRProgramRoute program pubValues (.neg a) i

theorem air_program_route_value (env : TerminalProgramEnvironment K) (pubValues : List K)
    (program : Nat → TerminalInstruction K) (registers : Nat → K)
    (equations : ∀ i,registers i=terminalProgramInstructionValue env registers (program i))
    (e : Expr) (i : Nat) (route : AIRProgramRoute program pubValues e i) :
    registers i=e.evalWith (airProgramEnv env pubValues) := by
  induction route with
  | @constant n i h | @publicValue n i h =>
    have eq := equations i
    simpa only [h,terminalProgramInstructionValue,Expr.evalWith,airProgramEnv] using eq
  | @current c i h | @next c i h =>
    have eq := equations i
    simpa only [h,terminalProgramInstructionValue,Expr.evalWith,airProgramEnv,Bool.false_eq_true,ite_false,ite_true] using eq
  | @first i h | @last i h | @transition i h =>
    have eq := equations i
    simpa only [h,terminalProgramInstructionValue,Expr.evalWith,airProgramEnv] using eq
  | @add a b x y i ra rb h ha hb | @mul a b x y i ra rb h ha hb =>
    have eq := equations i
    simpa only [h,terminalProgramInstructionValue,Expr.evalWith,airProgramEnv,ha,hb] using eq
  | @neg a x zeroReg i ra hz hi ha =>
    have z := equations zeroReg
    have eq := equations i
    simp only [hz,terminalProgramInstructionValue] at z
    simp only [hi,terminalProgramInstructionValue,z,ha] at eq
    change registers i= -a.evalWith (airProgramEnv env pubValues)
    grind

def terminalDefaultInstruction : TerminalInstruction K := ⟨.constant,0,0,0⟩

theorem terminal_program_total_equations (env : TerminalProgramEnvironment K)
    (program : List (TerminalInstruction K))
    (acyclic : TerminalDAGAcyclic 0 (program.map (terminalProgramNode env))) (i : Nat) :
    terminalProgramRun env 0 (fun _ => 0) program i=
      terminalProgramInstructionValue env (terminalProgramRun env 0 (fun _ => 0) program)
        (program.getD i terminalDefaultInstruction) := by
  by_cases bound : i<program.length
  · have h := terminal_program_register_equation env program acyclic i bound
    simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem bound,Option.getD_some] using h
  · have later := terminal_dag_preserves_later (fun _ => (0:K)) (fun _ => 0)
      (program.map (terminalProgramNode env)) 0 i (by simp only [List.length_map]; omega)
    rw [terminal_program_run_lower]
    rw [later]
    simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none (by omega : program.length≤i),
      terminalDefaultInstruction,terminalProgramInstructionValue]

/-- Actual acyclic ABI execution agrees with the full source Expr AST. Current
and next are independent supplied values; this theorem does not assert AIR
satisfaction or identify a non-Boolean point with a concrete trace row. -/
theorem air_program_executed_value (env : TerminalProgramEnvironment K) (pubValues : List K)
    (program : List (TerminalInstruction K))
    (acyclic : TerminalDAGAcyclic 0 (program.map (terminalProgramNode env)))
    (e : Expr) (i : Nat)
    (route : AIRProgramRoute (fun j => program.getD j terminalDefaultInstruction) pubValues e i) :
    terminalProgramRun env 0 (fun _ => 0) program i=e.evalWith (airProgramEnv env pubValues) :=
  air_program_route_value env pubValues _ _ (terminal_program_total_equations env program acyclic) e i route
end NearCompression
