import NearCompression.OneFoldScalarComposition

/-! Honest repeated affine folding of coefficient/weight vectors. Adjacent
entries carry (coefficient,weight); both coordinates use a+r*(b-a). Exact
power-of-two shapes prevent the Python zip fold from dropping odd tails.
No commitment, proximity or Fiat--Shamir soundness is claimed. -/
set_option autoImplicit false
namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

def affineFoldDot : List (K×K) → K
  | [] => 0
  | a::xs => a.1*a.2+affineFoldDot xs

def affineFoldVector (r : K) : List (K×K) → List (K×K)
  | [] => []
  | [_] => []
  | a::b::xs => (a.1+r*(b.1-a.1),a.2+r*(b.2-a.2))::affineFoldVector r xs

def affineFoldQuadratic : List (K×K) → WhirQuadratic K
  | [] => ⟨0,0,0⟩
  | [_] => ⟨0,0,0⟩
  | a::b::xs =>
    let q:=affineFoldQuadratic xs
    ⟨a.1*a.2+q.c0,(b.1-a.1)*a.2+a.1*(b.2-a.2)+q.c1,(b.1-a.1)*(b.2-a.2)+q.c2⟩

theorem affine_fold_shape (r : K) : ∀ xs : List (K×K),xs.length%2=0 →
    2*(affineFoldVector r xs).length=xs.length
  | [],_ => rfl
  | [_],h => by simp at h
  | a::b::xs,h => by
    have even : xs.length%2=0 := by simp only [List.length_cons] at h; omega
    have ih:=affine_fold_shape r xs even
    simp only [affineFoldVector,List.length_cons]
    omega

theorem affine_fold_quadratic_eval (r : K) : ∀ xs : List (K×K),
    (affineFoldQuadratic xs).eval r=affineFoldDot (affineFoldVector r xs)
  | [] => by simp only [affineFoldQuadratic,WhirQuadratic.eval,affineFoldVector,affineFoldDot]; grind
  | [_] => by simp only [affineFoldQuadratic,WhirQuadratic.eval,affineFoldVector,affineFoldDot]; grind
  | a::b::xs => by
    have ih:=affine_fold_quadratic_eval r xs
    simp only [affineFoldQuadratic,WhirQuadratic.eval,affineFoldVector,affineFoldDot] at ih ⊢
    grind

theorem affine_fold_quadratic_endpoints : ∀ xs : List (K×K),xs.length%2=0 →
    (affineFoldQuadratic xs).endpoints=affineFoldDot xs
  | [],_ => by simp only [affineFoldQuadratic,WhirQuadratic.endpoints,WhirQuadratic.eval,affineFoldDot]; grind
  | [_],h => by simp at h
  | a::b::xs,h => by
    have even : xs.length%2=0 := by simp only [List.length_cons] at h; omega
    have ih:=affine_fold_quadratic_endpoints xs even
    simp only [affineFoldQuadratic,WhirQuadratic.endpoints,WhirQuadratic.eval,affineFoldDot] at ih ⊢
    grind

def affineFoldFinal (xs : List (K×K)) : List K → List (K×K)
  | [] => xs
  | r::rs => affineFoldFinal (affineFoldVector r xs) rs

def affineFoldRounds (xs : List (K×K)) : List K → List (WhirArithmeticRound K)
  | [] => []
  | r::rs => {polynomial:=affineFoldQuadratic xs,challenge:=r,addition:=0}::
      affineFoldRounds (affineFoldVector r xs) rs

theorem affine_fold_next_shape (xs : List (K×K)) (r : K) (n terminalSize : Nat)
    (shape : xs.length=terminalSize*2^(n+1)) :
    (affineFoldVector r xs).length=terminalSize*2^n := by
  have even : xs.length%2=0 := by simp [shape,Nat.pow_succ,←Nat.mul_assoc]
  have h:=affine_fold_shape r xs even
  rw [Nat.pow_succ,←Nat.mul_assoc] at shape
  omega

/-- Actual endpoint/evaluation checks succeed for every honestly constructed
round, preserving the coefficient/weight dot claim through arbitrary depth. -/
theorem repeated_affine_honest [DecidableEq K] (challenges : List K)
    (xs : List (K×K)) (terminalSize : Nat)
    (shape : xs.length=terminalSize*2^challenges.length) :
    whirRunArithmetic (affineFoldDot xs) (affineFoldRounds xs challenges)=
      some (affineFoldDot (affineFoldFinal xs challenges)) ∧
    (affineFoldFinal xs challenges).length=terminalSize := by
  induction challenges generalizing xs with
  | nil =>
    simp only [List.length_nil,Nat.pow_zero,Nat.mul_one] at shape
    exact ⟨rfl,shape⟩
  | cons r rs ih =>
    have next:=affine_fold_next_shape xs r rs.length terminalSize shape
    have rest:=ih (affineFoldVector r xs) next
    have even : xs.length%2=0 := by
      simp only [List.length_cons,Nat.pow_succ,←Nat.mul_assoc] at shape
      omega
    constructor
    · simp only [affineFoldRounds,affineFoldFinal,whirRunArithmetic,
        affine_fold_quadratic_endpoints xs even,ite_true,affine_fold_quadratic_eval]
      have zero : affineFoldDot (affineFoldVector r xs)+(0:K)=affineFoldDot (affineFoldVector r xs) := by grind
      rw [zero]
      exact rest.1
    · exact rest.2

/-- The generated arithmetic ledger uses exactly the supplied challenges. -/
theorem affine_fold_round_challenges (xs : List (K×K)) (challenges : List K) :
    (affineFoldRounds xs challenges).map WhirArithmeticRound.challenge=challenges := by
  induction challenges generalizing xs with
  | nil => rfl
  | cons r rs ih => simp only [affineFoldRounds,List.map_cons,ih]
private theorem affine_residual_tail (a : K) (cs ws : List K) (offset : Nat) :
    scalarRSResidualFrom (Poly.mk (a::cs)) (offset+1) ws=
      scalarRSResidualFrom (Poly.mk cs) offset ws := by
  induction ws generalizing offset with
  | nil => rfl
  | cons w ws ih => simp only [scalarRSResidualFrom,Poly.coeff,List.getD_cons_succ,ih]

private theorem affine_residual_cons (a w : K) (cs ws : List K) :
    scalarRSResidual (w::ws) (Poly.mk (a::cs))=w*a+scalarRSResidual ws (Poly.mk cs) := by
  unfold scalarRSResidual
  rw [scalarRSResidualFrom,affine_residual_tail a cs ws 0]
  rfl

/-- The state dot product is the terminal's actual coefficient functional. -/
theorem affine_fold_terminal_dot (xs : List (K×K)) :
    scalarRSResidual (xs.map Prod.snd) (Poly.mk (xs.map Prod.fst))=affineFoldDot xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [List.map_cons,affine_residual_cons,affineFoldDot,ih]; grind

theorem repeated_affine_ledger [DecidableEq K] (challenges : List K)
    (xs : List (K×K)) (terminalSize : Nat)
    (shape : xs.length=terminalSize*2^challenges.length) :
    affineFoldDot (affineFoldFinal xs challenges)=
      affineFoldDot xs+whirRoundLedger (affineFoldRounds xs challenges) :=
  whir_run_arithmetic_ledger _ _ _ (repeated_affine_honest challenges xs terminalSize shape).1

/-- Honest arbitrary-depth folding reaches an exactly sized terminal vector,
whose full-oracle reconstruction and residual equality both pass. This is
completeness, not extraction of a malicious committed source polynomial. -/
theorem repeated_affine_terminal {Digest : Type} [DecidableEq K] [DecidableEq Digest]
    (root : List (List (K×K)) → Digest) (anchors challenges : List K)
    (xs : List (K×K)) (terminalSize : Nat)
    (shape : xs.length=terminalSize*2^challenges.length) :
    let final := affineFoldFinal xs challenges
    whirRunArithmetic (affineFoldDot xs) (affineFoldRounds xs challenges)=some (affineFoldDot final) ∧
    reconstructedRSChecks root terminalSize 1 [final.map Prod.fst] [final.map Prod.snd]
      anchors (reconstructedRSLeaves [final.map Prod.fst] anchors) (affineFoldDot final)=true := by
  have honest := repeated_affine_honest challenges xs terminalSize shape
  refine ⟨honest.1,?_⟩
  simp only [reconstructedRSChecks,reconstructedRSShape,List.length_cons,List.length_nil,
    List.length_map,honest.2,List.all_cons,List.all_nil,decide_true,Bool.true_and,Bool.and_true]
  change decide (scalarRSResidual ((affineFoldFinal xs challenges).map Prod.snd)
    (Poly.mk ((affineFoldFinal xs challenges).map Prod.fst))+0=
      affineFoldDot (affineFoldFinal xs challenges))=true
  apply _root_.decide_eq_true
  rw [affine_fold_terminal_dot]
  grind
/-- Literal separate-vector fold used for both cs and ws in Python. -/
def affineFoldValues (r : K) : List K → List K
  | [] => []
  | [_] => []
  | a::b::xs => (a+r*(b-a))::affineFoldValues r xs

theorem affine_fold_coordinates (r : K) : ∀ xs : List (K×K),
    (affineFoldVector r xs).map Prod.fst=affineFoldValues r (xs.map Prod.fst) ∧
    (affineFoldVector r xs).map Prod.snd=affineFoldValues r (xs.map Prod.snd)
  | [] => ⟨rfl,rfl⟩
  | [_] => ⟨rfl,rfl⟩
  | a::b::xs => by
    have ih:=affine_fold_coordinates r xs
    simp only [affineFoldVector,affineFoldValues,List.map_cons,ih.1,ih.2]
    exact ⟨True.intro,True.intro⟩
end NearCompression
