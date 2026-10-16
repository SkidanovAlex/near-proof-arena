import NearCompression.CallArrayCompilation
import NearCompression.TerminalDAGBalance
namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]
noncomputable section
local instance : DecidableEq K := Classical.typeDecidableEq K

/-- Exact sparse support, so a certificate cannot omit a nonzero coefficient. -/
noncomputable def callActiveSlots (capacity : Nat) (coeff : Nat→K) : List Nat :=
  (List.range capacity).filter (fun i=>decide (coeff i≠0))

/-- Structural certificate for compile_layout: input-times-constant leaves,
the balanced addition tree, and the final subtraction of the compiled claim. -/
structure CallCircuitRoute (nodes : Nat→TerminalDAGNode K) (capacity : Nat)
    (coeff : Nat→K) (claim : K) (root : Nat) where
  constantNode : Nat→Nat
  productNode : Nat→Nat
  sumNode : Nat
  claimNode : Nat
  inputs : ∀ i∈callActiveSlots capacity coeff,nodes i=.input i
  constants : ∀ i∈callActiveSlots capacity coeff,nodes (constantNode i)=.constant (coeff i)
  products : ∀ i∈callActiveSlots capacity coeff,nodes (productNode i)=.binary .mul i (constantNode i)
  balance : TerminalBalanceRoute nodes ((callActiveSlots capacity coeff).map (fun i=>(productNode i,true))) sumNode
  claimValue : nodes claimNode=.constant claim
  output : nodes root=.binary .sub sumNode claimNode

private theorem filtered_sum (indices : List Nat) (coeff v : Nat→K) :
    ((indices.filter (fun i=>decide (coeff i≠0))).map (fun i=>coeff i*v i)).sum=
      (indices.map (fun i=>coeff i*v i)).sum := by
  induction indices with
  | nil => rfl
  | cons i rest ih =>
    by_cases zero : coeff i=0
    · simp only [List.filter_cons,zero,ne_eq,not_true_eq_false,decide_false,Bool.false_eq_true,
        ite_false,List.map_cons,List.sum_cons,ih]
      grind
    · simp only [List.filter_cons,zero,ne_eq,not_false_eq_true,decide_true,ite_true,
        List.map_cons,List.sum_cons,ih]

/-- Derived from actual DAG execution and a structural route, not an assumed
root-value equality. Zero coefficients may be eliminated without changing it. -/
theorem call_circuit_functional (nodes : List (TerminalDAGNode K))
    (acyclic : TerminalDAGAcyclic 0 nodes) (capacity : Nat) (coeff v : Nat→K)
    (claim : K) (root : Nat)
    (route : CallCircuitRoute (fun i=>nodes.getD i (.constant 0)) capacity coeff claim root) :
    terminalDAGRun v 0 (fun _=>0) nodes root=
      ((List.range capacity).map (fun i=>coeff i*v i)).sum-claim := by
  let values:=terminalDAGRun v 0 (fun _=>0) nodes
  have equations:=terminal_dag_total_equations v nodes acyclic
  have leaves : ∀ i∈callActiveSlots capacity coeff,values (route.productNode i)=coeff i*v i := by
    intro i hi
    have prod:=equations (route.productNode i)
    have input:=equations i
    have constant:=equations (route.constantNode i)
    rw [route.products i hi] at prod
    rw [route.inputs i hi] at input
    rw [route.constants i hi] at constant
    simp only [terminalNodeValue,gkrGateValue] at prod input constant
    dsimp only [values]
    grind only
  have sum:=terminal_balance_route_value v values _ equations _ _ route.balance
  have mapped : ((callActiveSlots capacity coeff).map (fun i=>
      terminalSignedValue (values (route.productNode i),true)))=
      (callActiveSlots capacity coeff).map (fun i=>coeff i*v i) := by
    apply List.map_congr_left
    intro i hi
    simp only [terminalSignedValue,ite_true,leaves i hi]
  simp only [terminalRegisterSignedSum,List.map_map,Function.comp_def] at sum
  rw [mapped] at sum
  have sparse:=filtered_sum (List.range capacity) coeff v
  have c:=equations route.claimNode
  have out:=equations root
  rw [route.claimValue] at c
  rw [route.output] at out
  simp only [terminalNodeValue,gkrGateValue] at c out
  change values root=_
  change values route.claimNode=claim at c
  change values root=values route.sumNode-values route.claimNode at out
  rw [out,c,sum]
  exact congrArg (fun x=>x-claim) sparse

/-- Composition with the exact sequential coefficient accumulator. -/
theorem call_circuit_residual_sum (nodes : List (TerminalDAGNode K))
    (acyclic : TerminalDAGAcyclic 0 nodes) (capacity : Nat)
    (equations : List (K × CallBatchEquation K)) (v : Nat→K) (root : Nat)
    (bounds : ∀ e∈callCompiledEntries equations,e.1<capacity)
    (route : CallCircuitRoute (fun i=>nodes.getD i (.constant 0)) capacity
      (fun i=>(callArrayRun equations (Array.replicate capacity 0,0)).1.getD i 0)
      (callArrayRun equations (Array.replicate capacity 0,0)).2 root) :
    terminalDAGRun v 0 (fun _=>0) nodes root=
      (equations.map (fun pair=>pair.1*pair.2.residual v)).sum := by
  rw [call_circuit_functional nodes acyclic capacity _ v _ root route]
  exact call_array_functional capacity equations v bounds
end
end NearCompression
