import NearCompression.TwoLaneReconstruction
import NearCompression.GenericRSPairRepresentation

/-! Two-challenge affine reconstruction of arbitrary RS pair oracles.
The error-radius loss is explicit. Weighted constraints are quadratic, not
fixed linear claims, so the earlier linear residual reconstruction is not used. -/
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

def affineRecoveredEven (a b : K) (pa pb : Poly K) : Poly K :=
  twoLaneRecoveredZero a b pa pb

def affineRecoveredOdd (a b : K) (pa pb : Poly K) : Poly K :=
  affineRecoveredEven a b pa pb+twoLaneRecoveredOne a b pa pb

def arbitraryRSPairFold (oracle : K → K) (r x : K) : K :=
  let eo := rsPairDecode x (oracle x,oracle (-x))
  (1-r)*eo.1+r*eo.2

theorem affine_reconstruction_degree (a b : K) (pa pb : Poly K) (D : Nat)
    (ha : pa.DegLt D) (hb : pb.DegLt D) :
    (affineRecoveredEven a b pa pb).DegLt D ∧
    (affineRecoveredOdd a b pa pb).DegLt D := by
  have h := two_lane_reconstruction_degree a b pa pb D ha hb
  exact ⟨h.1,Poly.degLt_add h.1 h.2⟩

/-- Both affine-fold candidates agree at x², hence the reconstructed pair
matches BOTH authenticated source locations x and -x. -/
theorem affine_reconstruction_source_pair (oracle : K → K) (a b : K) (different : a≠b)
    (pa pb : Poly K) (x : K) (h2 : (2:K)≠0) (hx : x≠0)
    (atA : pa.eval (x*x)=arbitraryRSPairFold oracle a x)
    (atB : pb.eval (x*x)=arbitraryRSPairFold oracle b x) :
    rsPairEncode x ((affineRecoveredEven a b pa pb).eval (x*x),
      (affineRecoveredOdd a b pa pb).eval (x*x))=(oracle x,oracle (-x)) := by
  let eo := rsPairDecode x (oracle x,oracle (-x))
  have aa : pa.eval (x*x)=eo.1+a*(eo.2-eo.1) := by
    change pa.eval (x*x)=(1-a)*eo.1+a*eo.2 at atA
    grind
  have bb : pb.eval (x*x)=eo.1+b*(eo.2-eo.1) := by
    change pb.eval (x*x)=(1-b)*eo.1+b*eo.2 at atB
    grind
  obtain ⟨even,slope⟩ := two_lane_reconstruction_point a b eo.1 (eo.2-eo.1)
    different pa pb (x*x) aa bb
  have odd : (affineRecoveredOdd a b pa pb).eval (x*x)=eo.2 := by
    simp only [affineRecoveredOdd,affineRecoveredEven,Poly.eval_add,even,slope]
    grind
  change rsPairEncode x ((affineRecoveredEven a b pa pb).eval (x*x),
    (affineRecoveredOdd a b pa pb).eval (x*x))=_
  rw [odd]
  change rsPairEncode x ((twoLaneRecoveredZero a b pa pb).eval (x*x),eo.2)=_
  rw [even]
  exact rs_pair_encode_decode x h2 hx _

/-- A pair counts as one error even if both source locations are wrong. -/
theorem affine_reconstruction_pair_errors (representatives : List K) (oracle : K → K)
    (a b : K) (different : a≠b) (pa pb : Poly K) (h2 : (2:K)≠0)
    (nonzero : ∀ x∈representatives,x≠0) :
    count representatives (fun x =>
      rsPairEncode x ((affineRecoveredEven a b pa pb).eval (x*x),
        (affineRecoveredOdd a b pa pb).eval (x*x))≠(oracle x,oracle (-x))) ≤
    count representatives (fun x => pa.eval (x*x)≠arbitraryRSPairFold oracle a x)+
    count representatives (fun x => pb.eval (x*x)≠arbitraryRSPairFold oracle b x) := by
  classical
  induction representatives with
  | nil => simp [count]
  | cons x xs ih =>
    have h := ih (fun y hy => nonzero y (by simp [hy]))
    have point := affine_reconstruction_source_pair oracle a b different pa pb x h2
      (nonzero x (by simp))
    simp only [count,List.countP_cons] at h ⊢
    by_cases ha : pa.eval (x*x)=arbitraryRSPairFold oracle a x <;>
      by_cases hb : pb.eval (x*x)=arbitraryRSPairFold oracle b x <;>
      by_cases hp : rsPairEncode x ((affineRecoveredEven a b pa pb).eval (x*x),
        (affineRecoveredOdd a b pa pb).eval (x*x))=(oracle x,oracle (-x)) <;>
      simp_all <;> omega

/-- The exact weighted fold residual is quadratic in r, including zero
weight factors. E and O are residuals against the common remaining weights. -/
def affineWeightedResidual (w0 w1 E O r : K) : K :=
  ((1-r)*w0+r*w1)*((1-r)*E+r*O)

theorem affine_weighted_residual_quadratic (w0 w1 E O r : K) :
    affineWeightedResidual w0 w1 E O r =
      w0*E+r*(w0*(O-E)+(w1-w0)*E)+r*r*((w1-w0)*(O-E)) := by
  unfold affineWeightedResidual
  grind

theorem affine_weighted_residual_endpoints (w0 w1 E O : K) :
    affineWeightedResidual w0 w1 E O 0+affineWeightedResidual w0 w1 E O 1=
      w0*E+w1*O := by
  unfold affineWeightedResidual
  grind

theorem affine_weighted_residual_actual (weights : List K) (even odd : Poly K)
    (w0 w1 r : K) :
    ((1-r)*w0+r*w1)*scalarRSResidual weights
      (Poly.smul (1-r) even+Poly.smul r odd)=
    affineWeightedResidual w0 w1 (scalarRSResidual weights even)
      (scalarRSResidual weights odd) r := by
  rw [scalar_rs_residual_add,scalar_rs_residual_scale,scalar_rs_residual_scale]
  rfl

/-- Passing from canonical pairs to the full x,-x domain costs at most two
errors per bad pair. Distinctness is a later domain-geometry obligation. -/
theorem full_domain_errors_le_twice_pair_errors (reps : List K) (source candidate : K → K) :
    finiteRSMismatches (reps.flatMap (fun x => [x,-x])) source candidate ≤
      2*count reps (fun x => (source x,source (-x))≠(candidate x,candidate (-x))) := by
  classical
  induction reps with
  | nil => simp [finiteRSMismatches,count]
  | cons x xs ih =>
    simp only [List.flatMap_cons,List.cons_append,List.nil_append,
      finiteRSMismatches,count,List.countP_cons] at ih ⊢
    by_cases hp : source x=candidate x <;> by_cases hm : source (-x)=candidate (-x) <;>
      simp_all <;> omega

/-- Two challenge agreements cannot certify the weighted residual quadratic.
The zero source has actual residual zero; q(r)=r(r-2) agrees at 0 and 2,
yet its sumcheck endpoint sum is -1. When 2≠0 these challenges are distinct. -/
theorem two_weighted_challenges_insufficient (w0 w1 : K) :
    let q := fun r : K => r*(r-2)
    q 0=affineWeightedResidual w0 w1 0 0 0 ∧
    q 2=affineWeightedResidual w0 w1 0 0 2 ∧ q 0+q 1≠0 := by
  dsimp only
  unfold affineWeightedResidual
  constructor
  · grind
  constructor <;> grind

end NearCompression
