import NearCompression.TerminalStoredBundleCheck
import NearCompression.TerminalRebuildCertificate
namespace NearCompression

deriving instance DecidableEq for TerminalDAGNode

/-- Finite witness for the exact arithmetic shortcuts used by the terminal
compiler. Constant folding carries both operands, checked against the DAG. -/
inductive TerminalArithmeticWitness (K : Type) where
  | direct
  | constant (left right : K)
  | addZeroLeft | addZeroRight | subZeroRight | subSame
  | mulZeroLeft | mulZeroRight | mulOneLeft | mulOneRight

def terminalArithmeticWitnessCheck {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    (nodes : Nat → TerminalDAGNode K) (op : GKRBinaryOp) (x y z : Nat) :
    TerminalArithmeticWitness K → Bool
  | .direct => decide (nodes z=.binary op x y)
  | .constant a b => decide (nodes x=.constant a ∧ nodes y=.constant b ∧
      nodes z=.constant (gkrGateValue op a b))
  | .addZeroLeft => decide (op=.add ∧ nodes x=.constant 0 ∧ z=y)
  | .addZeroRight => decide (op=.add ∧ nodes y=.constant 0 ∧ z=x)
  | .subZeroRight => decide (op=.sub ∧ nodes y=.constant 0 ∧ z=x)
  | .subSame => decide (op=.sub ∧ x=y ∧ nodes z=.constant 0)
  | .mulZeroLeft => decide (op=.mul ∧ nodes x=.constant 0 ∧ z=x)
  | .mulZeroRight => decide (op=.mul ∧ nodes y=.constant 0 ∧ z=y)
  | .mulOneLeft => decide (op=.mul ∧ nodes x=.constant 1 ∧ z=y)
  | .mulOneRight => decide (op=.mul ∧ nodes y=.constant 1 ∧ z=x)

theorem terminal_arithmetic_witness_checked {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    (nodes : Nat → TerminalDAGNode K) (op : GKRBinaryOp) (x y z : Nat)
    (witness : TerminalArithmeticWitness K)
    (checked : terminalArithmeticWitnessCheck nodes op x y z witness=true) :
    TerminalArithmeticRoute nodes op x y z := by
  cases witness <;> simp only [terminalArithmeticWitnessCheck,decide_eq_true_eq] at checked
  · exact .direct checked
  · exact .constant checked.1 checked.2.1 checked.2.2
  · obtain ⟨rfl,h,rfl⟩ := checked; exact .addZeroLeft h
  · obtain ⟨rfl,h,rfl⟩ := checked; exact .addZeroRight h
  · obtain ⟨rfl,h,rfl⟩ := checked; exact .subZeroRight h
  · obtain ⟨rfl,rfl,h⟩ := checked; exact .subSame h
  · obtain ⟨rfl,h,rfl⟩ := checked; exact .mulZeroLeft h
  · obtain ⟨rfl,h,rfl⟩ := checked; exact .mulZeroRight h
  · obtain ⟨rfl,h,rfl⟩ := checked; exact .mulOneLeft h
  · obtain ⟨rfl,h,rfl⟩ := checked; exact .mulOneRight h

/-- Finite bounds prevent default nodes from manufacturing shortcut evidence. -/
def terminalStoredArithmeticCheck {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    (nodes : List (TerminalDAGNode K)) (op : GKRBinaryOp) (x y z : Nat)
    (witness : TerminalArithmeticWitness K) : Bool :=
  decide (x<nodes.length ∧ y<nodes.length ∧ z<nodes.length) &&
    terminalArithmeticWitnessCheck (fun i => nodes.getD i (.constant 0)) op x y z witness

theorem terminal_stored_arithmetic_checked {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    (nodes : List (TerminalDAGNode K)) (op : GKRBinaryOp) (x y z : Nat)
    (witness : TerminalArithmeticWitness K)
    (checked : terminalStoredArithmeticCheck nodes op x y z witness=true) :
    (x<nodes.length ∧ y<nodes.length ∧ z<nodes.length) ∧
    TerminalArithmeticRoute (fun i => nodes.getD i (.constant 0)) op x y z := by
  simp only [terminalStoredArithmeticCheck,Bool.and_eq_true,decide_eq_true_eq] at checked
  exact ⟨checked.1,terminal_arithmetic_witness_checked _ op x y z witness checked.2⟩

/-- Source reconstruction composes with the checked finite circuit. The source
acyclicity check and bundle check replace their structural premises; leaf
bindings and reconstruction provenance remain explicit in `rebuild`. -/
theorem terminal_program_checked_bundle_value {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    (env : TerminalProgramEnvironment K) (program : List (TerminalInstruction K))
    (nodes : List (TerminalDAGNode K)) (inputs constants : Nat → K)
    (sourceRoot targetRoot capacity : Nat) (live positions : List Nat)
    (zeroSlot : Nat) (stages : List TerminalStoredPlan) (outputSlot : Nat)
    (sourceChecked : terminalAcyclicCheck 0 (program.map (terminalProgramNode env))=true)
    (bundleChecked : terminalStoredBundleCheck nodes capacity constants live positions zeroSlot stages targetRoot outputSlot=true)
    (rebuild : TerminalRebuildRoute
      (fun i => (program.map (terminalProgramNode env)).getD i (.constant 0))
      (fun i => nodes.getD i (.constant 0)) inputs sourceRoot targetRoot) :
    gkrFiniteCircuit (terminalInitialValues capacity inputs constants) (stages.map (fun s => s.gates)) outputSlot=
      terminalProgramRun env 0 (fun _ => 0) program sourceRoot := by
  rw [terminal_checked_bundle_root inputs constants nodes capacity live positions zeroSlot stages targetRoot outputSlot bundleChecked]
  have targetChecked : terminalAcyclicCheck 0 nodes=true := by
    simp only [terminalStoredBundleCheck,Bool.and_eq_true] at bundleChecked
    exact bundleChecked.1.1.1
  exact terminal_program_rebuilt_value env program nodes inputs
    (terminal_acyclic_checked _ 0 sourceChecked) (terminal_acyclic_checked nodes 0 targetChecked)
    sourceRoot targetRoot rebuild

private def arithmeticSmokeNodes : List (TerminalDAGNode Rat) :=
  [.constant 0,.constant 1,.input 0,.input 1,.constant 2,.constant 3,
   .constant 5,.constant (-1),.constant 6,.binary .add 2 3,
   .binary .sub 2 3,.binary .mul 2 3,.constant 17]

private def arithmeticSmokeCases : List (GKRBinaryOp × Nat × Nat × Nat × TerminalArithmeticWitness Rat) :=
  [(.add,2,3,9,.direct),(.sub,2,3,10,.direct),(.mul,2,3,11,.direct),
   (.add,4,5,6,.constant 2 3),(.sub,4,5,7,.constant 2 3),(.mul,4,5,8,.constant 2 3),
   (.add,0,2,2,.addZeroLeft),(.add,2,0,2,.addZeroRight),
   (.sub,2,0,2,.subZeroRight),(.sub,2,2,0,.subSame),
   (.mul,0,2,0,.mulZeroLeft),(.mul,2,0,0,.mulZeroRight),
   (.mul,1,2,2,.mulOneLeft),(.mul,2,1,2,.mulOneRight)]

/-- All ten witness constructors, including all three constant-fold operations,
are kernel-evaluated. Every case rejects substitution of a wrong result.
Missing nodes and forged constant operands are also rejected. -/
theorem terminal_arithmetic_check_regressions :
    arithmeticSmokeCases.all (fun (op,x,y,z,w) =>
      terminalStoredArithmeticCheck arithmeticSmokeNodes op x y z w)=true ∧
    arithmeticSmokeCases.all (fun (op,x,y,_,w) =>
      !terminalStoredArithmeticCheck arithmeticSmokeNodes op x y 12 w)=true ∧
    terminalStoredArithmeticCheck arithmeticSmokeNodes .add 99 2 2 .addZeroLeft=false ∧
    terminalStoredArithmeticCheck arithmeticSmokeNodes .add 4 5 6 (.constant 1 4)=false ∧
    terminalStoredArithmeticCheck arithmeticSmokeNodes .mul 0 2 2 .addZeroLeft=false := by decide +kernel

end NearCompression
