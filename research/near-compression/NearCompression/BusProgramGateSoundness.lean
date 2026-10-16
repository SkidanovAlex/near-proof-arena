import NearCompression.BusProgramFormulas
namespace NearCompression
open Lean.Grind
variable {K : Type} [Field K]

/-- Square residuals and product residuals are separate ordered lists, exactly
as in compile_weighted (all squares precede all product links per interaction). -/
inductive BusProgramChainRoute (program : Nat → TerminalInstruction K) :
    BusProgramFormula K → BusProgramFormula K → List (BusProgramFormula K) →
    List (BusProgramFormula K) → List (BusProgramFormula K) → List Nat → List Nat → Prop where
  | empty (power accumulator) : BusProgramChainRoute program power accumulator [] [] [] [] []
  | step {power accumulator bit rest nextPower nextProduct powers products squareReg productReg squares productRegs} :
      BusProgramFormulaRoute program (busSquareFormula power nextPower) squareReg →
      BusProgramFormulaRoute program (busProductFormula bit nextPower accumulator nextProduct) productReg →
      BusProgramChainRoute program nextPower nextProduct rest powers products squares productRegs →
      BusProgramChainRoute program power accumulator (bit::rest) (nextPower::powers) (nextProduct::products)
        (squareReg::squares) (productReg::productRegs)

theorem bus_program_chain_zero (env : TerminalProgramEnvironment K)
    (program : Nat → TerminalInstruction K) (registers : Nat → K)
    (equations : ∀ i,registers i=terminalProgramInstructionValue env registers (program i))
    (power accumulator : BusProgramFormula K) (bits powers products : List (BusProgramFormula K))
    (squares productRegs : List Nat)
    (route : BusProgramChainRoute program power accumulator bits powers products squares productRegs) :
    (∀ i∈squares,registers i=0) → (∀ i∈productRegs,registers i=0) →
    BusAuxChainHolds (busProgramFormulaValue env power) (busProgramFormulaValue env accumulator)
      (bits.map (busProgramFormulaValue env)) (powers.map (busProgramFormulaValue env))
      (products.map (busProgramFormulaValue env)) := by
  induction route with
  | empty power accumulator => intro hs hp; exact .empty _ _
  | @step power accumulator bit rest nextPower nextProduct powers products squareReg productReg squares productRegs rs rp route ih =>
    intro hs hp
    have square := bus_program_formula_route_value env program registers equations _ _ rs
    have product := bus_program_formula_route_value env program registers equations _ _ rp
    rw [hs squareReg (by simp),bus_square_formula_value] at square
    rw [hp productReg (by simp),bus_product_formula_value] at product
    exact .step square.symm product.symm (ih
      (fun i hi => hs i (by simp [hi])) (fun i hi => hp i (by simp [hi])))

/-- Specialization to actual ABI execution; only the selected residual registers
are assumed zero, not the auxiliary chain equations or its claimed factor. -/
theorem bus_executed_chain_zero (env : TerminalProgramEnvironment K)
    (program : List (TerminalInstruction K))
    (acyclic : TerminalDAGAcyclic 0 (program.map (terminalProgramNode env)))
    (power accumulator : BusProgramFormula K) (bits powers products : List (BusProgramFormula K))
    (squares productRegs : List Nat)
    (route : BusProgramChainRoute (fun i => program.getD i terminalDefaultInstruction)
      power accumulator bits powers products squares productRegs)
    (squareZero : ∀ i∈squares,terminalProgramRun env 0 (fun _ => 0) program i=0)
    (productZero : ∀ i∈productRegs,terminalProgramRun env 0 (fun _ => 0) program i=0) :
    BusAuxChainHolds (busProgramFormulaValue env power) (busProgramFormulaValue env accumulator)
      (bits.map (busProgramFormulaValue env)) (powers.map (busProgramFormulaValue env))
      (products.map (busProgramFormulaValue env)) :=
  bus_program_chain_zero env _ _ (terminal_program_total_equations env program acyclic)
    power accumulator bits powers products squares productRegs route squareZero productZero

/-- These are precisely the first/link/last hypotheses consumed by
 generic_bus_product_of_gates, once supplied for all Boolean trace rows. -/
theorem bus_executed_boundary_zero (env : TerminalProgramEnvironment K)
    (program : List (TerminalInstruction K))
    (acyclic : TerminalDAGAcyclic 0 (program.map (terminalProgramNode env)))
    (a an factor : BusProgramFormula K) (final : K) (firstReg linkReg lastReg : Nat)
    (firstRoute : BusProgramFormulaRoute (fun i => program.getD i terminalDefaultInstruction)
      (.mul .first (.sub a (.literal 1))) firstReg)
    (linkRoute : BusProgramFormulaRoute (fun i => program.getD i terminalDefaultInstruction)
      (.mul .transition (.sub an (.mul a factor))) linkReg)
    (lastRoute : BusProgramFormulaRoute (fun i => program.getD i terminalDefaultInstruction)
      (.mul .last (.sub (.mul a factor) (.literal final))) lastReg)
    (firstZero : terminalProgramRun env 0 (fun _ => 0) program firstReg=0)
    (linkZero : terminalProgramRun env 0 (fun _ => 0) program linkReg=0)
    (lastZero : terminalProgramRun env 0 (fun _ => 0) program lastReg=0) :
    env.first*(busProgramFormulaValue env a-1)=0 ∧
    env.transition*(busProgramFormulaValue env an-busProgramFormulaValue env a*busProgramFormulaValue env factor)=0 ∧
    env.last*(busProgramFormulaValue env a*busProgramFormulaValue env factor-final)=0 := by
  have first := bus_program_formula_executed env program acyclic _ _ firstRoute
  have link := bus_program_formula_executed env program acyclic _ _ linkRoute
  have last := bus_program_formula_executed env program acyclic _ _ lastRoute
  rw [firstZero] at first
  rw [linkZero] at link
  rw [lastZero] at last
  exact ⟨first.symm,link.symm,last.symm⟩
end NearCompression
