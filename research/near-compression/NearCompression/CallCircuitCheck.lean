import NearCompression.CallCircuitRoute
import NearCompression.TerminalBalanceCheck
namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K] [DecidableEq K]

structure CallCircuitCertificate (K : Type) where
  constants : List Nat
  products : List Nat
  balance : TerminalBalanceCertificate K
  claimNode : Nat

/-- Only structural checks: the expected coefficients and claim are supplied
by the caller, not read from the certificate. Exact support is recomputed. -/
def callCircuitCheck (nodes : List (TerminalDAGNode K)) (capacity : Nat)
    (coeff : Nat→K) (claim : K) (root : Nat) (cert : CallCircuitCertificate K) : Bool :=
  let active:=(List.range capacity).filter (fun i=>decide (coeff i≠0))
  terminalAcyclicCheck 0 nodes &&
  active.all (fun i=>decide (
    i<nodes.length ∧ cert.constants.getD i 0<nodes.length ∧ cert.products.getD i 0<nodes.length ∧
    nodes.getD i (.constant 0)=.input i ∧
    nodes.getD (cert.constants.getD i 0) (.constant 0)=.constant (coeff i) ∧
    nodes.getD (cert.products.getD i 0) (.constant 0)=.binary .mul i (cert.constants.getD i 0))) &&
  decide (cert.balance.terms=active.map (fun i=>(cert.products.getD i 0,true)) ∧
    cert.claimNode<nodes.length ∧ root<nodes.length ∧
    nodes.getD cert.claimNode (.constant 0)=.constant claim ∧
    nodes.getD root (.constant 0)=.binary .sub cert.balance.result cert.claimNode) &&
  terminalBalanceCheck nodes cert.balance

theorem call_circuit_checked_route (nodes : List (TerminalDAGNode K)) (capacity : Nat)
    (coeff : Nat→K) (claim : K) (root : Nat) (cert : CallCircuitCertificate K)
    (checked : callCircuitCheck nodes capacity coeff claim root cert=true) :
    TerminalDAGAcyclic 0 nodes ∧
    Nonempty (CallCircuitRoute (fun i=>nodes.getD i (.constant 0)) capacity coeff claim root) := by
  simp only [callCircuitCheck,Bool.and_eq_true,decide_eq_true_eq] at checked
  obtain ⟨⟨⟨acyclic,leaves⟩,output⟩,balance⟩:=checked
  have each : ∀ i∈callActiveSlots capacity coeff,
      nodes.getD i (.constant 0)=.input i ∧
      nodes.getD (cert.constants.getD i 0) (.constant 0)=.constant (coeff i) ∧
      nodes.getD (cert.products.getD i 0) (.constant 0)=.binary .mul i (cert.constants.getD i 0) := by
    intro i hi
    have h:=List.all_eq_true.mp leaves i (by simpa [callActiveSlots] using hi)
    simp only [decide_eq_true_eq] at h
    exact h.2.2.2
  refine ⟨terminal_acyclic_checked nodes 0 acyclic,⟨{
    constantNode:=fun i=>cert.constants.getD i 0
    productNode:=fun i=>cert.products.getD i 0
    sumNode:=cert.balance.result
    claimNode:=cert.claimNode
    inputs:=fun i hi=>(each i hi).1
    constants:=fun i hi=>(each i hi).2.1
    products:=fun i hi=>(each i hi).2.2
    balance:=?_
    claimValue:=output.2.2.2.1
    output:=output.2.2.2.2 }⟩⟩
  have route:=terminal_balance_checked nodes cert.balance balance
  rw [output.1] at route
  simpa [callActiveSlots] using route

/-- Accepted certificates establish the actual DAG functional for ALL private
inputs; this is stronger than evaluating selected regression vectors. -/
theorem call_circuit_checked_functional (nodes : List (TerminalDAGNode K)) (capacity : Nat)
    (coeff v : Nat→K) (claim : K) (root : Nat) (cert : CallCircuitCertificate K)
    (checked : callCircuitCheck nodes capacity coeff claim root cert=true) :
    terminalDAGRun v 0 (fun _=>0) nodes root=
      ((List.range capacity).map (fun i=>coeff i*v i)).sum-claim := by
  obtain ⟨acyclic,⟨route⟩⟩:=call_circuit_checked_route nodes capacity coeff claim root cert checked
  exact call_circuit_functional nodes acyclic capacity coeff v claim root route

/-- Both independent structural checkers compose at the executed DAG root. -/
theorem call_layered_checked_functional (nodes : List (TerminalDAGNode K)) (capacity : Nat)
    (coeff v constants : Nat→K) (claim : K) (root : Nat) (cert : CallCircuitCertificate K)
    (live positions : List Nat) (zeroSlot : Nat) (stages : List TerminalStoredPlan) (outputSlot : Nat)
    (checked : callCircuitCheck nodes capacity coeff claim root cert=true)
    (layered : terminalStoredBundleCheck nodes capacity constants live positions zeroSlot stages root outputSlot=true) :
    gkrFiniteCircuit (terminalInitialValues capacity v constants) (stages.map (fun s=>s.gates)) outputSlot=
      ((List.range capacity).map (fun i=>coeff i*v i)).sum-claim := by
  rw [terminal_checked_bundle_root v constants nodes capacity live positions zeroSlot stages root outputSlot layered]
  exact call_circuit_checked_functional nodes capacity coeff v claim root cert checked
end NearCompression
