import NearCompression.ExpandedBusFingerprint
import NearCompression.BusFormulaCheck
namespace NearCompression
open Lean.Grind

/-- Check the expanded expression directly against the instruction route.
No caller-supplied expression can replace the canonical expansion. -/
def expandedBusFingerprintCheck {K : Type} [Field K] [DecidableEq K]
    (program : List (TerminalInstruction K)) (width : Nat)
    (alpha tag : K) (message : List (BusProgramFormula K)) (root : Nat) : Bool :=
  busFormulaCheck program width (expandedBusTagged alpha tag 1 (.literal 0) message) root

/-- Every accepted acyclic instruction route computes the canonical Horner
fingerprint in every environment, not just the captured test environment.
Authentication of alpha, tag, and message remains a caller obligation. -/
theorem expanded_bus_fingerprint_checked_execution {K : Type} [Field K] [DecidableEq K]
    (env : TerminalProgramEnvironment K) (program : List (TerminalInstruction K))
    (width : Nat) (alpha tag : K) (message : List (BusProgramFormula K)) (root : Nat)
    (acyclic : terminalAcyclicCheck 0 (program.map (terminalProgramNode env))=true)
    (checked : expandedBusFingerprintCheck program width alpha tag message root=true) :
    terminalProgramRun env 0 (fun _ => 0) program root=
      busProgramFormulaValue env (busTaggedFormula alpha tag message) := by
  rw [bus_formula_checked_execution env program width
    (expandedBusTagged alpha tag 1 (.literal 0) message) root acyclic checked]
  exact expanded_bus_fingerprint_value env alpha tag message

private def expandedSmokeProgram : List (TerminalInstruction Rat) :=
  [⟨.constant,0,0,0⟩,⟨.current,0,0,0⟩,⟨.constant,0,0,1⟩,
   ⟨.mul,1,2,0⟩,⟨.add,0,3,0⟩,⟨.constant,0,0,6⟩,⟨.add,4,5,0⟩]

/-- Reject wrong tags/challenges, messages, roots, and column coverage even
when a program could agree at a particular sampled environment. -/
theorem expanded_bus_fingerprint_check_regressions :
    expandedBusFingerprintCheck expandedSmokeProgram 1 2 3 [.current 0] 6=true ∧
    expandedBusFingerprintCheck expandedSmokeProgram 1 2 4 [.current 0] 6=false ∧
    expandedBusFingerprintCheck expandedSmokeProgram 1 3 3 [.current 0] 6=false ∧
    expandedBusFingerprintCheck expandedSmokeProgram 1 2 3 [.next 0] 6=false ∧
    expandedBusFingerprintCheck expandedSmokeProgram 1 2 3 [.current 0] 4=false ∧
    expandedBusFingerprintCheck expandedSmokeProgram 0 2 3 [.current 0] 6=false := by
  decide +kernel

end NearCompression
