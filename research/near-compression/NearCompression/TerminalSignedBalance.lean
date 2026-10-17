import NearCompression.GKRLayerTransition

/-! Value-level semantics of compile_terminal.balanced. True represents sign +1,
false sign -1. DAG cache/node placement remains a separate refinement. -/
namespace NearCompression
open Lean.Grind
variable {K : Type} [Field K]

def terminalSignedValue (t : K × Bool) : K := if t.2 then t.1 else -t.1

def terminalSignedJoin (a b : K × Bool) : K × Bool :=
  if a.2=b.2 then (a.1+b.1,a.2)
  else if a.2 then (a.1-b.1,true) else (b.1-a.1,true)

def terminalSignedPass : List (K × Bool) → List (K × Bool)
  | [] => []
  | [a] => [a]
  | a::b::rest => terminalSignedJoin a b::terminalSignedPass rest

theorem terminal_signed_join (a b : K × Bool) :
    terminalSignedValue (terminalSignedJoin a b)=terminalSignedValue a+terminalSignedValue b := by
  rcases a with ⟨x,s⟩
  rcases b with ⟨y,t⟩
  cases s <;> cases t <;> simp [terminalSignedJoin,terminalSignedValue] <;> grind

theorem terminal_signed_pass_sum (terms : List (K × Bool)) :
    ((terminalSignedPass terms).map terminalSignedValue).sum=(terms.map terminalSignedValue).sum := by
  induction terms using terminalSignedPass.induct with
  | case1 => rfl
  | case2 a => rfl
  | case3 a b rest ih =>
    simp only [terminalSignedPass,List.map_cons,List.sum_cons,terminal_signed_join,ih]
    grind

theorem terminal_signed_pass_length (terms : List (K × Bool)) :
    (terminalSignedPass terms).length≤terms.length := by
  induction terms using terminalSignedPass.induct with
  | case1 => exact Nat.le_refl _
  | case2 a => exact Nat.le_refl _
  | case3 a b rest ih => simp only [terminalSignedPass,List.length_cons]; omega

/-- Complete while-loop semantics; odd final terms pass through unchanged. -/
def terminalSignedBalance (terms : List (K × Bool)) : K :=
  match terms with
  | [] => 0
  | [a] => terminalSignedValue a
  | a::b::rest => terminalSignedBalance (terminalSignedPass (a::b::rest))
termination_by terms.length
decreasing_by
  simp only [terminalSignedPass,List.length_cons]
  have bound := terminal_signed_pass_length rest
  omega

theorem terminal_signed_balance_sum (terms : List (K × Bool)) :
    terminalSignedBalance terms=(terms.map terminalSignedValue).sum := by
  induction terms using terminalSignedBalance.induct with
  | case1 => simp [terminalSignedBalance]
  | case2 a => simp only [terminalSignedBalance,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]; grind
  | case3 a b rest ih =>
    rw [terminalSignedBalance,ih,terminal_signed_pass_sum]

/-- The terminal compiler batches output minus claimed value with successive
rho powers; an exact zero circuit output is this explicit residual equation. -/
def terminalResidualTerms (rho power : K) : List (K × K) → List (K × Bool)
  | [] => []
  | (output,claim)::rest => (power*(output-claim),true)::terminalResidualTerms rho (power*rho) rest

def terminalResidualValue (rho power : K) : List (K × K) → K
  | [] => 0
  | (output,claim)::rest => power*(output-claim)+terminalResidualValue rho (power*rho) rest

theorem terminal_residual_balance (rho power : K) (outputs : List (K × K)) :
    terminalSignedBalance (terminalResidualTerms rho power outputs)=terminalResidualValue rho power outputs := by
  rw [terminal_signed_balance_sum]
  induction outputs generalizing power with
  | nil => rfl
  | cons pair rest ih =>
    simp only [terminalResidualTerms,List.map_cons,List.sum_cons,terminalSignedValue,ite_true,
      terminalResidualValue,ih]
end NearCompression
