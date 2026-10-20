import NearCompression.WHIRRoundRecurrence
import NearCompression.ScalarRSReconstructedTerminal

/-! Honest arithmetic composition for pq384_one_fold.py. Coefficients are
Boolean-table values in this sumcheck: their fold is (1-r)*even+r*odd, not the
monomial contraction even+r*odd. Query authentication, proximity soundness,
Fiat--Shamir and QROM security are not established by these identities. -/
set_option autoImplicit false
namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

structure OneFoldTerm (K : Type) where
  even : K
  odd : K
  weight : K

def oneFoldValue (r : K) (t : OneFoldTerm K) : K := t.even+r*(t.odd-t.even)
def oneFoldScale (z r : K) : K := 1+r*(z-1)

def oneFoldQuadratic (z : K) : List (OneFoldTerm K) → WhirQuadratic K
  | [] => ⟨0,0,0⟩
  | t::ts =>
    let rest := oneFoldQuadratic z ts
    let delta := t.odd-t.even
    let dw := (z-1)*t.weight
    ⟨t.even*t.weight+rest.c0,delta*t.weight+t.even*dw+rest.c1,delta*dw+rest.c2⟩

def oneFoldSourceClaim (z : K) : List (OneFoldTerm K) → K
  | [] => 0
  | t::ts => t.even*t.weight+z*t.odd*t.weight+oneFoldSourceClaim z ts

def oneFoldTerminalClaim (z r : K) : List (OneFoldTerm K) → K
  | [] => 0
  | t::ts => oneFoldValue r t*(oneFoldScale z r*t.weight)+oneFoldTerminalClaim z r ts

theorem one_fold_quadratic_eval (terms : List (OneFoldTerm K)) (z r : K) :
    (oneFoldQuadratic z terms).eval r=oneFoldTerminalClaim z r terms := by
  induction terms with
  | nil => simp only [oneFoldQuadratic,WhirQuadratic.eval,oneFoldTerminalClaim]; grind
  | cons t ts ih =>
    simp only [oneFoldQuadratic,WhirQuadratic.eval,oneFoldTerminalClaim,oneFoldValue,oneFoldScale] at ih ⊢
    grind

theorem one_fold_quadratic_endpoints (terms : List (OneFoldTerm K)) (z : K) :
    (oneFoldQuadratic z terms).endpoints=oneFoldSourceClaim z terms := by
  induction terms with
  | nil => simp only [oneFoldQuadratic,WhirQuadratic.endpoints,WhirQuadratic.eval,oneFoldSourceClaim]; grind
  | cons t ts ih =>
    simp only [oneFoldQuadratic,WhirQuadratic.endpoints,WhirQuadratic.eval,oneFoldSourceClaim] at ih ⊢
    grind

/-- The concrete endpoint test succeeds for honest coefficients; its resulting
claim is exactly the terminal residual computed with scaled tail weights. -/
theorem one_fold_honest_round [DecidableEq K] (terms : List (OneFoldTerm K)) (z r : K) :
    whirRunArithmetic (oneFoldSourceClaim z terms)
      [{polynomial:=oneFoldQuadratic z terms,challenge:=r,addition:=0}]=
      some (oneFoldTerminalClaim z r terms) := by
  simp only [whirRunArithmetic,one_fold_quadratic_endpoints,ite_true,one_fold_quadratic_eval]
  congr 1
  grind

def oneFoldSourceCoefficients (terms : List (OneFoldTerm K)) : List K :=
  terms.flatMap (fun t => [t.even,t.odd])
def oneFoldCoefficients (r : K) (terms : List (OneFoldTerm K)) : List K :=
  terms.map (oneFoldValue r)
def oneFoldWeights (z r : K) (terms : List (OneFoldTerm K)) : List K :=
  terms.map (fun t => oneFoldScale z r*t.weight)

/-- Univariate polynomial represented by the affine coefficient fold. -/
theorem one_fold_polynomial (terms : List (OneFoldTerm K)) (r x : K) :
    (Poly.mk (oneFoldCoefficients r terms)).eval x =
    (1-r)*(Poly.mk (monomialEvenCoefficients (oneFoldSourceCoefficients terms))).eval x+
      r*(Poly.mk (monomialOddCoefficients (oneFoldSourceCoefficients terms))).eval x := by
  induction terms with
  | nil =>
    simp only [oneFoldCoefficients,oneFoldSourceCoefficients,List.map_nil,List.flatMap_nil,
      monomialEvenCoefficients,monomialOddCoefficients,Poly.eval,Poly.evalL]
    grind
  | cons t ts ih =>
    simp only [oneFoldCoefficients,oneFoldSourceCoefficients,List.map_cons,List.flatMap_cons,List.cons_append,
      List.nil_append,monomialEvenCoefficients,monomialOddCoefficients,Poly.eval,Poly.evalL,oneFoldValue] at ih ⊢
    grind

/-- Scalar f(x),f(-x) query decode followed by the exact affine fold equals
the folded terminal polynomial at x², under the necessary nonzero divisors. -/
theorem one_fold_scalar_pair (terms : List (OneFoldTerm K)) (r x : K)
    (h2 : (2:K)≠0) (hx : x≠0) :
    let eo := rsPairDecode x
      ((Poly.mk (oneFoldSourceCoefficients terms)).eval x,
       (Poly.mk (oneFoldSourceCoefficients terms)).eval (-x))
    eo.1+r*(eo.2-eo.1)=(Poly.mk (oneFoldCoefficients r terms)).eval (x*x) := by
  dsimp only
  rw [rs_polynomial_pair_decode _ x h2 hx,one_fold_polynomial]
  grind

private theorem residual_tail (a : K) (cs ws : List K) (offset : Nat) :
    scalarRSResidualFrom (Poly.mk (a::cs)) (offset+1) ws=
      scalarRSResidualFrom (Poly.mk cs) offset ws := by
  induction ws generalizing offset with
  | nil => rfl
  | cons w ws ih =>
    simp only [scalarRSResidualFrom,Poly.coeff,List.getD_cons_succ,ih]

private theorem residual_cons (a w : K) (cs ws : List K) :
    scalarRSResidual (w::ws) (Poly.mk (a::cs))=w*a+scalarRSResidual ws (Poly.mk cs) := by
  unfold scalarRSResidual
  rw [scalarRSResidualFrom,residual_tail a cs ws 0]
  rfl

/-- Low-coordinate monomial weights are interleaved [w,z*w] for each
adjacent source coefficient pair; the tail weights are fixed protocol input. -/
def oneFoldSourceWeights (z : K) (terms : List (OneFoldTerm K)) : List K :=
  terms.flatMap (fun t => [t.weight,z*t.weight])

theorem one_fold_source_residual (terms : List (OneFoldTerm K)) (z : K) :
    scalarRSResidual (oneFoldSourceWeights z terms) (Poly.mk (oneFoldSourceCoefficients terms))=
      oneFoldSourceClaim z terms := by
  induction terms with
  | nil => rfl
  | cons t ts ih =>
    simp only [oneFoldSourceWeights,oneFoldSourceCoefficients,List.flatMap_cons,List.cons_append,
      List.nil_append,residual_cons,oneFoldSourceClaim] at ih ⊢
    grind

theorem one_fold_shapes (terms : List (OneFoldTerm K)) (z r : K) :
    (oneFoldSourceCoefficients terms).length=2*terms.length ∧
    (oneFoldCoefficients r terms).length=terms.length ∧
    (oneFoldWeights z r terms).length=terms.length := by
  refine ⟨?_,by simp [oneFoldCoefficients],by simp [oneFoldWeights]⟩
  induction terms with
  | nil => rfl
  | cons t ts ih =>
    simp only [oneFoldSourceCoefficients,List.flatMap_cons,List.length_append,List.length_cons,List.length_nil] at ih ⊢
    omega

/-- The terminal's externally fixed coefficient linear functional is exactly
the sumcheck evaluation, with no evaluation/monomial basis conflation. -/
theorem one_fold_terminal_residual (terms : List (OneFoldTerm K)) (z r : K) :
    scalarRSResidual (oneFoldWeights z r terms) (Poly.mk (oneFoldCoefficients r terms))=
      (oneFoldQuadratic z terms).eval r := by
  rw [one_fold_quadratic_eval]
  induction terms with
  | nil => rfl
  | cons t ts ih =>
    simp only [oneFoldWeights,oneFoldCoefficients,List.map_cons,residual_cons,oneFoldTerminalClaim] at ih ⊢
    grind

/-- Honest terminal reconstruction passes the concrete root/shape/residual
checker for any fixed tree-root interface. No tree binding is needed for this
completeness direction, nor does it give adversarial soundness. -/
theorem one_fold_honest_terminal {Digest : Type} [DecidableEq K] [DecidableEq Digest]
    (root : List (List (K×K)) → Digest) (anchors : List K)
    (terms : List (OneFoldTerm K)) (z r : K) :
    reconstructedRSChecks root terms.length 1 [oneFoldCoefficients r terms] [oneFoldWeights z r terms]
      anchors (reconstructedRSLeaves [oneFoldCoefficients r terms] anchors)
      ((oneFoldQuadratic z terms).eval r)=true := by
  simp only [reconstructedRSChecks,reconstructedRSShape,oneFoldCoefficients,oneFoldWeights,
    List.length_cons,List.length_nil,List.length_map,List.all_cons,List.all_nil,
    decide_true,Bool.true_and,Bool.and_true]
  have residual := one_fold_terminal_residual terms z r
  change decide (scalarRSResidual (oneFoldWeights z r terms) (Poly.mk (oneFoldCoefficients r terms))+0=
    (oneFoldQuadratic z terms).eval r)=true
  apply _root_.decide_eq_true
  rw [residual]
  grind
end NearCompression
