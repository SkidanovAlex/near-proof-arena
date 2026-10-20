import NearCompression.InstructionSumcheckSoundness

/-! Finite-domain Reed--Solomon distance and unique decoding. The received
word is arbitrary. Uniqueness is coefficientwise, allowing trailing zeroes
in polynomial lists. No decoder algorithm or correlated-agreement theorem. -/
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

noncomputable def finiteRSMismatches (domain : List K) (a b : K → K) : Nat :=
  count domain (fun x => a x ≠ b x)

omit [Field K] in
theorem finite_rs_agreement_partition (domain : List K) (a b : K → K) :
    count domain (fun x => a x=b x)+finiteRSMismatches domain a b=domain.length := by
  classical
  induction domain with
  | nil => rfl
  | cons x xs ih =>
    simp only [finiteRSMismatches,count,List.countP_cons,List.length_cons] at ih ⊢
    by_cases h : a x=b x <;> simp_all <;> omega

omit [Field K] in
theorem finite_rs_mismatch_symm (domain : List K) (a b : K → K) :
    finiteRSMismatches domain a b=finiteRSMismatches domain b a := by
  have pred : (fun x => a x ≠ b x)=(fun x => b x ≠ a x) := by
    funext x
    apply propext
    exact ne_comm
  unfold finiteRSMismatches
  rw [pred]

omit [Field K] in
theorem finite_rs_mismatch_triangle (domain : List K) (a b c : K → K) :
    finiteRSMismatches domain a c ≤
      finiteRSMismatches domain a b+finiteRSMismatches domain b c := by
  classical
  induction domain with
  | nil => simp [finiteRSMismatches,count]
  | cons x xs ih =>
    simp only [finiteRSMismatches,count,List.countP_cons] at ih ⊢
    by_cases ab : a x=b x <;> by_cases bc : b x=c x <;>
      by_cases ac : a x=c x <;> simp_all <;> omega

/-- Degree strictly below D means at most D-1 agreements for distinct
polynomials. The +1 form remains honest even at D=0. -/
theorem finite_rs_distinct_agreement (domain : List K) (distinct : domain.Nodup)
    (a b : Poly K) (D : Nat) (ha : a.DegLt D) (hb : b.DegLt D)
    (different : ¬(a-b).IsZero) :
    count domain (fun x => a.eval x=b.eval x)+1≤D := by
  have roots := PolyRoots.cardRootsLe_of polyEval polyDeg quotFacts isZeroEval
    K (a-b) D domain different (Poly.degLt_sub ha hb) distinct
  have subset : count domain (fun x => a.eval x=b.eval x)≤
      count domain (fun x => (a-b).eval x=0) := by
    apply count_mono
    intro x eq
    rw [Poly.eval_sub,eq]
    grind
  omega

theorem finite_rs_minimum_distance (domain : List K) (distinct : domain.Nodup)
    (a b : Poly K) (D : Nat) (ha : a.DegLt D) (hb : b.DegLt D)
    (different : ¬(a-b).IsZero) :
    domain.length+1≤D+finiteRSMismatches domain a.eval b.eval := by
  have agree := finite_rs_distinct_agreement domain distinct a b D ha hb different
  have partition := finite_rs_agreement_partition domain a.eval b.eval
  omega

theorem finite_rs_minimum_distance_sub (domain : List K) (distinct : domain.Nodup)
    (a b : Poly K) (D : Nat) (ha : a.DegLt D) (hb : b.DegLt D)
    (fits : D≤domain.length) (different : ¬(a-b).IsZero) :
    domain.length-D+1≤finiteRSMismatches domain a.eval b.eval := by
  have bound := finite_rs_minimum_distance domain distinct a b D ha hb different
  omega

/-- Unequal radii, with integer arithmetic avoiding any fractional distance
rounding. The received word need not be a polynomial. -/
theorem finite_rs_unique_candidate (domain : List K) (distinct : domain.Nodup)
    (received : K → K) (a b : Poly K) (D radiusA radiusB : Nat)
    (ha : a.DegLt D) (hb : b.DegLt D)
    (closeA : finiteRSMismatches domain received a.eval≤radiusA)
    (closeB : finiteRSMismatches domain received b.eval≤radiusB)
    (separation : radiusA+radiusB+D≤domain.length) :
    (a-b).IsZero := by
  classical
  apply Classical.byContradiction
  intro different
  have distance := finite_rs_minimum_distance domain distinct a b D ha hb different
  have triangle := finite_rs_mismatch_triangle domain a.eval received b.eval
  rw [finite_rs_mismatch_symm domain a.eval received] at triangle
  omega

/-- Standard unique-decoding radius condition 2*r < N-D+1. -/
theorem finite_rs_unique_radius (domain : List K) (distinct : domain.Nodup)
    (received : K → K) (a b : Poly K) (D radius : Nat)
    (ha : a.DegLt D) (hb : b.DegLt D) (fits : D≤domain.length)
    (closeA : finiteRSMismatches domain received a.eval≤radius)
    (closeB : finiteRSMismatches domain received b.eval≤radius)
    (separation : 2*radius<domain.length-D+1) :
    (∀ i,a.coeff i=b.coeff i) ∧ (∀ x,a.eval x=b.eval x) := by
  have zero := finite_rs_unique_candidate domain distinct received a b D radius radius ha hb
    closeA closeB (by omega)
  constructor
  · intro i
    have eq := zero i
    rw [Poly.coeff_sub] at eq
    grind
  · intro x
    have eq := Poly.eval_of_isZero zero x
    rw [Poly.eval_sub] at eq
    grind

end NearCompression
