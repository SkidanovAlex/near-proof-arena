import NearCompression.FiniteRSUniqueDecoding
import NearCompression.SparseLiftPolynomial
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]
def rotateCoefficients (z : K) : List K → List K
  | [] => []
  | a::as => a :: Poly.scaleL z (rotateCoefficients z as)
def rotatePolynomial (z : K) (p : Poly K) : Poly K :=
  Poly.mk (rotateCoefficients z p.coeffs)
private theorem rotate_get (z : K) (cs : List K) (i : Nat) :
    (rotateCoefficients z cs).getD i 0=z^i*cs.getD i 0 := by
  induction cs generalizing i with
  | nil => simp [rotateCoefficients,List.getD] <;> grind
  | cons a as ih =>
    cases i with
    | zero => simp [rotateCoefficients,List.getD] <;> grind
    | succ i =>
      change (Poly.scaleL z (rotateCoefficients z as)).getD i 0=_
      rw [Poly.getD_scaleL,ih]
      simp only [List.getD_cons_succ]
      grind
private theorem rotate_eval (z x : K) (cs : List K) :
    Poly.evalL x (rotateCoefficients z cs)=Poly.evalL (z*x) cs := by
  induction cs with
  | nil => rfl
  | cons a as ih =>
    simp only [rotateCoefficients,Poly.evalL_cons,Poly.evalL_scaleL,ih]
    grind
theorem rotate_polynomial_coeff (z : K) (p : Poly K) (i : Nat) :
    (rotatePolynomial z p).coeff i=z^i*p.coeff i := rotate_get z p.coeffs i
theorem rotate_polynomial_eval (z : K) (p : Poly K) (x : K) :
    (rotatePolynomial z p).eval x=p.eval (z*x) := rotate_eval z x p.coeffs
theorem rotate_polynomial_degree (z : K) (p : Poly K) (D : Nat)
    (degree : p.DegLt D) : (rotatePolynomial z p).DegLt D := by
  intro i hi
  rw [rotate_polynomial_coeff,degree i hi]
  grind
/-- Exact symmetry of a branch power projection, for an arbitrary source. -/
theorem power_projected_source_symmetry (source : K → K) (z : K) (L : Nat)
    (period : z^L=1) (x : K) : source ((z*x)^L)=source (x^L) := by
  have product : (z*x)^L=z^L*x^L := by
    clear period
    induction L with
    | zero => grind
    | succ n ih => grind
  rw [product,period]
  congr 1
  grind

/-- Arbitrary received word; exact orbit symmetry and a finite-domain
permutation certificate suffice. No honest-source assumption. -/
theorem projected_source_rotation (domain : List K) (distinct : domain.Nodup)
    (z : K) (closed : (domain.map (fun x => z*x)).Perm domain)
    (received : K → K) (symmetric : ∀ x,received (z*x)=received x)
    (p : Poly K) (D radius : Nat) (degree : p.DegLt D)
    (close : finiteRSMismatches domain received p.eval≤radius)
    (separation : radius+radius+D≤domain.length) :
    ∀ i,(z^i-1)*p.coeff i=0 := by
  classical
  have rotatedClose : finiteRSMismatches domain received (rotatePolynomial z p).eval≤radius := by
    have equality : finiteRSMismatches domain received (rotatePolynomial z p).eval=
        finiteRSMismatches (domain.map (fun x => z*x)) received p.eval := by
      simp only [finiteRSMismatches,count,List.countP_map]
      congr 1
      funext x
      simp only [Function.comp_apply,rotate_polynomial_eval,symmetric]
    rw [equality]
    have perm := closed.countP_eq (fun x => @decide (received x ≠ p.eval x) (Classical.propDecidable _))
    unfold finiteRSMismatches count at close ⊢
    have eq : finiteRSMismatches (domain.map (fun x => z*x)) received p.eval = finiteRSMismatches domain received p.eval := by
      simpa only [finiteRSMismatches,count] using perm
    exact Nat.le_trans (Nat.le_of_eq eq) close
  have same := finite_rs_unique_candidate domain distinct received (rotatePolynomial z p) p
    D radius radius (rotate_polynomial_degree z p D degree) degree rotatedClose close separation
  intro i
  have h := same i
  rw [Poly.coeff_sub,rotate_polynomial_coeff] at h
  grind
/-- Exact root order gives the sparse-image coefficient condition. -/
theorem projected_source_sparse_coefficients (domain : List K) (distinct : domain.Nodup)
    (z : K) (L : Nat) (order : ∀ i,¬L∣i → z^i≠1)
    (closed : (domain.map (fun x => z*x)).Perm domain)
    (received : K → K) (symmetric : ∀ x,received (z*x)=received x)
    (p : Poly K) (D radius : Nat) (degree : p.DegLt D)
    (close : finiteRSMismatches domain received p.eval≤radius)
    (separation : radius+radius+D≤domain.length) :
    ∀ i,¬L∣i → p.coeff i=0 := by
  intro i hi
  have h := projected_source_rotation domain distinct z closed received symmetric p D radius degree close separation i
  have nz := order i hi
  grind

def recoverProjectedPolynomial (L d : Nat) (p : Poly K) : Poly K :=
  Poly.mk ((List.range d).map (fun i => p.coeff (L*i)))

theorem recovered_projected_degree (L d : Nat) (p : Poly K) :
    (recoverProjectedPolynomial L d p).DegLt d := by
  have h := Poly.degLt_length (recoverProjectedPolynomial L d p)
  simpa only [recoverProjectedPolynomial,List.length_map,List.length_range] using h

/-- Exact inverse coefficient storage, including all out-of-range indices.
The original degree is d, not the common-domain degree L*d. -/
theorem recovered_projected_coefficients (L d : Nat) (_positive : 0<L)
    (p : Poly K) (degree : p.DegLt (L*d))
    (sparse : ∀ i,¬L∣i → p.coeff i=0) (i : Nat) :
    p.coeff i=if L∣i then (recoverProjectedPolynomial L d p).coeff (i/L) else 0 := by
  classical
  by_cases divides : L∣i
  · simp only [divides,ite_true]
    have index : L*(i/L)=i := Nat.mul_div_cancel' divides
    by_cases bound : i/L<d
    · simp only [recoverProjectedPolynomial,Poly.coeff]
      simp [List.getD,bound,index]
    · have high : L*d≤i := by
        have h := Nat.mul_le_mul_left L (show d≤i/L by omega)
        rw [index] at h
        exact h
      rw [degree i high]
      exact (Poly.getD_ge_length _ _ (by simp [recoverProjectedPolynomial]; omega)).symm
  · simp only [divides,ite_false]
    exact sparse i divides

end NearCompression
