import NearCompression.AIRProgramLowering
namespace NearCompression
open Lean.Grind
variable {K : Type} [Field K]

/-- Literal total := plus(total,times(constant(weight),residual)) register
updates in compile_weighted. Residual registers can come from AIR or bus gates. -/
inductive AIRAccumulatorRoute (program : Nat → TerminalInstruction K) :
    Nat → List (Nat × K) → Nat → Prop where
  | empty (start) : AIRAccumulatorRoute program start [] start
  | step {start residual coefficient product next finish weight rest} :
      program coefficient=⟨.constant,0,0,weight⟩ →
      program product=⟨.mul,coefficient,residual,0⟩ →
      program next=⟨.add,start,product,0⟩ →
      AIRAccumulatorRoute program next rest finish →
      AIRAccumulatorRoute program start ((residual,weight)::rest) finish

def airResidualWeightedValue (registers : Nat → K) : List (Nat × K) → K
  | [] => 0
  | (r,w)::rest => w*registers r+airResidualWeightedValue registers rest

theorem air_accumulator_route_value (env : TerminalProgramEnvironment K)
    (program : Nat → TerminalInstruction K) (registers : Nat → K)
    (equations : ∀ i,registers i=terminalProgramInstructionValue env registers (program i))
    (start finish : Nat) (residuals : List (Nat × K))
    (route : AIRAccumulatorRoute program start residuals finish) :
    registers finish=registers start+airResidualWeightedValue registers residuals := by
  induction route with
  | empty start => simp only [airResidualWeightedValue]; grind
  | @step start residual coefficient product next finish weight rest hc hp hn route ih =>
    have c := equations coefficient
    have p := equations product
    have n := equations next
    simp only [hc,terminalProgramInstructionValue] at c
    simp only [hp,terminalProgramInstructionValue,c] at p
    simp only [hn,terminalProgramInstructionValue,p] at n
    simp only [airResidualWeightedValue]
    rw [ih,n]
    grind

def airMixResiduals (mixing power : K) : List Nat → List (Nat × K)
  | [] => []
  | r::rest => (r,power)::airMixResiduals mixing (power*mixing) rest

/-- Exact ordered power mixing, including power zero and zero mixing. -/
def airMixValue (registers : Nat → K) (mixing power : K) : List Nat → K
  | [] => 0
  | r::rest => power*registers r+airMixValue registers mixing (power*mixing) rest

theorem air_mix_residuals_value (registers : Nat → K) (mixing power : K) (residuals : List Nat) :
    airResidualWeightedValue registers (airMixResiduals mixing power residuals)=
      airMixValue registers mixing power residuals := by
  induction residuals generalizing power with
  | nil => rfl
  | cons r rest ih => simp only [airMixResiduals,airResidualWeightedValue,airMixValue,ih]

/-- The final ABI register is an explicit add(total,zero), even when emission
reuses a cached earlier register. This theorem includes that finishing copy. -/
theorem air_program_weighted_finish (env : TerminalProgramEnvironment K)
    (program : List (TerminalInstruction K))
    (acyclic : TerminalDAGAcyclic 0 (program.map (terminalProgramNode env)))
    (mixing : K) (residuals : List Nat) (zeroReg total output : Nat)
    (zeroNode : program.getD zeroReg terminalDefaultInstruction=⟨.constant,0,0,0⟩)
    (route : AIRAccumulatorRoute (fun i => program.getD i terminalDefaultInstruction)
      zeroReg (airMixResiduals mixing 1 residuals) total)
    (finish : program.getD output terminalDefaultInstruction=⟨.add,total,zeroReg,0⟩) :
    terminalProgramRun env 0 (fun _ => 0) program output=
      airMixValue (terminalProgramRun env 0 (fun _ => 0) program) mixing 1 residuals := by
  let registers := terminalProgramRun env 0 (fun _ => 0) program
  have equations := terminal_program_total_equations env program acyclic
  have initial := equations zeroReg
  have ending := equations output
  simp only [zeroNode,terminalProgramInstructionValue] at initial
  simp only [finish,terminalProgramInstructionValue,initial] at ending
  have accum := air_accumulator_route_value env _ registers equations zeroReg total _ route
  rw [air_mix_residuals_value] at accum
  dsimp only [registers] at accum
  rw [initial] at accum
  grind
end NearCompression
