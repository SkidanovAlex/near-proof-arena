import NearCompression.GKRRowSlotSpanning
import NearCompression.InstructionSumcheckSoundness

namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

def gkrSetCoordinate (point : Nat → K) (coordinate : Nat) (value : K) : Nat → K :=
  fun i => if i=coordinate then value else point i

/-- Every equality-basis coordinate is affine, including coordinates outside
the declared dimension (where it is constant). No Boolean-input assumption. -/
theorem row_equality_coordinate_affine (n : Nat) (point : Nat → K)
    (coordinate index : Nat) (r : K) :
    rowEqualityWeight n (gkrSetCoordinate point coordinate r) index=
      (1-r)*rowEqualityWeight n (gkrSetCoordinate point coordinate 0) index+
      r*rowEqualityWeight n (gkrSetCoordinate point coordinate 1) index := by
  induction n generalizing point coordinate index with
  | zero => simp only [rowEqualityWeight]; grind
  | succ n ih =>
    cases coordinate with
    | zero =>
      simp only [rowEqualityWeight,gkrSetCoordinate,ite_true]
      split <;> grind
    | succ coordinate =>
      have head : ∀ v : K,gkrSetCoordinate point (coordinate+1) v 0=point 0 := by
        intro v; simp [gkrSetCoordinate]
      have tail : ∀ v : K,(fun j => gkrSetCoordinate point (coordinate+1) v (j+1))=
          gkrSetCoordinate (fun j => point (j+1)) coordinate v := by
        intro v; funext j; simp [gkrSetCoordinate]
      simp only [rowEqualityWeight,head,tail]
      rw [ih]
      grind

/-- Interpolating any fixed table has individual degree at most one in each
point coordinate. Used for both final GKR eq weights and PCS weight MLEs. -/
theorem row_mle_coordinate_affine (n : Nat) (values point : Nat → K)
    (coordinate : Nat) (r : K) :
    genericRowMLE n values (gkrSetCoordinate point coordinate r)=
      (1-r)*genericRowMLE n values (gkrSetCoordinate point coordinate 0)+
      r*genericRowMLE n values (gkrSetCoordinate point coordinate 1) := by
  rw [←row_equality_dot,←row_equality_dot,←row_equality_dot]
  unfold cubeSum
  have affine := row_equality_coordinate_affine n point coordinate
  induction List.range (2^n) with
  | nil => simp; grind
  | cons i rest ih => simp only [List.map_cons,List.sum_cons,affine i r,ih]; grind

/-- Concrete degree certificate for any established affine coordinate identity.
This constructs the degree<2 polynomial rather than only naming a degree. -/
theorem affine_coordinate_polynomial (f : K → K)
    (affine : ∀ r,f r=(1-r)*f 0+r*f 1) :
    ∃ polynomial : Poly K,polynomial.DegLt 2 ∧ ∀ r,polynomial.eval r=f r := by
  refine ⟨Poly.C (f 0)+Poly.X*(Poly.C (f 1)-Poly.C (f 0)),?_,?_⟩
  · apply Poly.degLt_add
    · exact (Poly.degLt_length _).mono (by change 1≤2; decide)
    · exact Poly.degLt_mul (Poly.degLt_length Poly.X)
        (Poly.degLt_sub (Poly.degLt_length (Poly.C (f 1))) (Poly.degLt_length (Poly.C (f 0))))
  · intro r
    rw [affine r]
    simp only [Poly.eval_add,Poly.eval_mul,Poly.eval_sub,Poly.eval_C,Poly.eval_X]
    grind


private theorem upper_zeta_family_affine (n : Nat) (f : K → Nat → K)
    (affine : ∀ i r,f r i=(1-r)*f 0 i+r*f 1 i) (index : Nat) (r : K) :
    upperZeta n (f r) index=(1-r)*upperZeta n (f 0) index+r*upperZeta n (f 1) index := by
  induction n generalizing f index with
  | zero => exact affine 0 r
  | succ n ih =>
    simp only [upperZeta]
    split
    · apply ih
      intro i t
      rw [affine (2*i) t,affine (2*i+1) t]
      grind
    · apply ih
      intro i t
      exact affine (2*i+1) t

/-- The actual universal coefficient weight has individual degree at most
one in every rowpoint coordinate, including its cyclic-next contribution. -/
theorem gkr_weight_row_coordinate_affine (n p : Nat) (rowpoint left right : Nat → K)
    (gamma : K) (coordinate index : Nat) (r : K) :
    gkrUniversalTableWeight n p (gkrSetCoordinate rowpoint coordinate r) left right gamma index=
      (1-r)*gkrUniversalTableWeight n p (gkrSetCoordinate rowpoint coordinate 0) left right gamma index+
      r*gkrUniversalTableWeight n p (gkrSetCoordinate rowpoint coordinate 1) left right gamma index := by
  have current := upper_zeta_family_affine n
    (fun t => rowEqualityWeight n (gkrSetCoordinate rowpoint coordinate t))
    (fun i t => row_equality_coordinate_affine n rowpoint coordinate i t) (index%2^n) r
  have next := upper_zeta_family_affine n
    (fun t => cyclicRowWeight n (gkrSetCoordinate rowpoint coordinate t))
    (fun i t => row_equality_coordinate_affine n rowpoint coordinate _ t) (index%2^n) r
  simp only [gkrUniversalTableWeight,packedDualWeight]
  rw [current,next]
  grind

/-- Left/right GKR points enter the coefficient weights only through the
specified equality basis, not through the prover's sumcheck messages. -/
theorem gkr_weight_left_coordinate_affine (n p : Nat) (rowpoint left right : Nat → K)
    (gamma : K) (coordinate index : Nat) (r : K) :
    gkrUniversalTableWeight n p rowpoint (gkrSetCoordinate left coordinate r) right gamma index=
      (1-r)*gkrUniversalTableWeight n p rowpoint (gkrSetCoordinate left coordinate 0) right gamma index+
      r*gkrUniversalTableWeight n p rowpoint (gkrSetCoordinate left coordinate 1) right gamma index := by
  have affine : ∀ i t,
      rowEqualityWeight (p+1) (gkrSetCoordinate left coordinate t) i+gamma*rowEqualityWeight (p+1) right i=
      (1-t)*(rowEqualityWeight (p+1) (gkrSetCoordinate left coordinate 0) i+gamma*rowEqualityWeight (p+1) right i)+
      t*(rowEqualityWeight (p+1) (gkrSetCoordinate left coordinate 1) i+gamma*rowEqualityWeight (p+1) right i) := by
    intro i t
    rw [row_equality_coordinate_affine (p+1) left coordinate i t]
    grind
  have a := upper_zeta_family_affine p _ affine (index/2^n) r
  have b := upper_zeta_family_affine p _ (fun i t => affine (i+2^p) t) (index/2^n) r
  simp only [gkrUniversalTableWeight,packedDualWeight]
  rw [a,b]
  grind

theorem gkr_weight_right_coordinate_affine (n p : Nat) (rowpoint left right : Nat → K)
    (gamma : K) (coordinate index : Nat) (r : K) :
    gkrUniversalTableWeight n p rowpoint left (gkrSetCoordinate right coordinate r) gamma index=
      (1-r)*gkrUniversalTableWeight n p rowpoint left (gkrSetCoordinate right coordinate 0) gamma index+
      r*gkrUniversalTableWeight n p rowpoint left (gkrSetCoordinate right coordinate 1) gamma index := by
  have affine : ∀ i t,
      rowEqualityWeight (p+1) left i+gamma*rowEqualityWeight (p+1) (gkrSetCoordinate right coordinate t) i=
      (1-t)*(rowEqualityWeight (p+1) left i+gamma*rowEqualityWeight (p+1) (gkrSetCoordinate right coordinate 0) i)+
      t*(rowEqualityWeight (p+1) left i+gamma*rowEqualityWeight (p+1) (gkrSetCoordinate right coordinate 1) i) := by
    intro i t
    rw [row_equality_coordinate_affine (p+1) right coordinate i t]
    grind
  have a := upper_zeta_family_affine p _ affine (index/2^n) r
  have b := upper_zeta_family_affine p _ (fun i t => affine (i+2^p) t) (index/2^n) r
  simp only [gkrUniversalTableWeight,packedDualWeight]
  rw [a,b]
  grind

theorem gkr_weight_gamma_affine (n p : Nat) (rowpoint left right : Nat → K)
    (index : Nat) (r : K) :
    gkrUniversalTableWeight n p rowpoint left right r index=
      (1-r)*gkrUniversalTableWeight n p rowpoint left right 0 index+
      r*gkrUniversalTableWeight n p rowpoint left right 1 index := by
  have affine : ∀ i t,
      rowEqualityWeight (p+1) left i+t*rowEqualityWeight (p+1) right i=
      (1-t)*(rowEqualityWeight (p+1) left i+0*rowEqualityWeight (p+1) right i)+
      t*(rowEqualityWeight (p+1) left i+1*rowEqualityWeight (p+1) right i) := by
    intro i t
    grind
  have a := upper_zeta_family_affine p _ affine (index/2^n) r
  have b := upper_zeta_family_affine p _ (fun i t => affine (i+2^p) t) (index/2^n) r
  simp only [gkrUniversalTableWeight,packedDualWeight]
  rw [a,b]
  grind


private theorem mle_family_affine (n : Nat) (f : K → Nat → K) (point : Nat → K)
    (affine : ∀ i r,f r i=(1-r)*f 0 i+r*f 1 i) (r : K) :
    genericRowMLE n (f r) point=(1-r)*genericRowMLE n (f 0) point+r*genericRowMLE n (f 1) point := by
  have same : f r=(fun i => (1-r)*f 0 i+r*f 1 i) := funext (fun i => affine i r)
  rw [same,generic_row_mle_add,generic_row_mle_scale,generic_row_mle_scale]

inductive GKRWeightAxis where
  | row | left | right | gamma | pcs

def gkrUniversalBeta (n p : Nat) (rowpoint left right u : Nat → K) (gamma : K) : K :=
  genericRowMLE (n+p) (gkrUniversalTableWeight n p rowpoint left right gamma) u

def gkrBetaCoordinate (axis : GKRWeightAxis) (n p : Nat)
    (rowpoint left right u : Nat → K) (gamma : K) (coordinate : Nat) (r : K) : K :=
  match axis with
  | .row => gkrUniversalBeta n p (gkrSetCoordinate rowpoint coordinate r) left right u gamma
  | .left => gkrUniversalBeta n p rowpoint (gkrSetCoordinate left coordinate r) right u gamma
  | .right => gkrUniversalBeta n p rowpoint left (gkrSetCoordinate right coordinate r) u gamma
  | .gamma => gkrUniversalBeta n p rowpoint left right u r
  | .pcs => gkrUniversalBeta n p rowpoint left right (gkrSetCoordinate u coordinate r) gamma

/-- The actual source-batching beta has individual degree <2 in each of the
joint rowpoint/GKR/PCS variables. Variable blocks are distinct; identifying
coordinates across blocks would not be covered by this theorem. -/
theorem gkr_beta_coordinate_affine (axis : GKRWeightAxis) (n p : Nat)
    (rowpoint left right u : Nat → K) (gamma : K) (coordinate : Nat) (r : K) :
    gkrBetaCoordinate axis n p rowpoint left right u gamma coordinate r=
      (1-r)*gkrBetaCoordinate axis n p rowpoint left right u gamma coordinate 0+
      r*gkrBetaCoordinate axis n p rowpoint left right u gamma coordinate 1 := by
  cases axis with
  | row =>
    exact mle_family_affine (n+p) _ u
      (fun i t => gkr_weight_row_coordinate_affine n p rowpoint left right gamma coordinate i t) r
  | left =>
    exact mle_family_affine (n+p) _ u
      (fun i t => gkr_weight_left_coordinate_affine n p rowpoint left right gamma coordinate i t) r
  | right =>
    exact mle_family_affine (n+p) _ u
      (fun i t => gkr_weight_right_coordinate_affine n p rowpoint left right gamma coordinate i t) r
  | gamma =>
    exact mle_family_affine (n+p) _ u
      (fun i t => gkr_weight_gamma_affine n p rowpoint left right i t) r
  | pcs => exact row_mle_coordinate_affine (n+p) _ u coordinate r

theorem gkr_beta_coordinate_degree (axis : GKRWeightAxis) (n p : Nat)
    (rowpoint left right u : Nat → K) (gamma : K) (coordinate : Nat) :
    ∃ polynomial : Poly K,polynomial.DegLt 2 ∧
      ∀ r,polynomial.eval r=gkrBetaCoordinate axis n p rowpoint left right u gamma coordinate r := by
  apply affine_coordinate_polynomial
  exact gkr_beta_coordinate_affine axis n p rowpoint left right u gamma coordinate

end NearCompression
