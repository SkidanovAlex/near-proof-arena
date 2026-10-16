import NearCompression.RateShiftCandidateList
import NearCompression.RateShiftWeightAccumulator
import NearCompression.GeneralCheckedFold
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

/-- Exactly D coefficients, including explicit trailing zeroes. -/
def rateShiftNormalize (D : Nat) (p : Poly K) : Poly K :=
  Poly.mk ((List.range D).map p.coeff)

theorem rate_shift_normalize_length (D : Nat) (p : Poly K) :
    (rateShiftNormalize D p).coeffs.length=D := by simp [rateShiftNormalize]

theorem rate_shift_normalize_coeff (D : Nat) (p : Poly K) (degree : p.DegLt D) :
    ∀ i,(rateShiftNormalize D p).coeff i=p.coeff i := by
  intro i
  by_cases h : i<D
  · simp [rateShiftNormalize,Poly.coeff,List.getD,h]
  · rw [degree i (by omega)]
    simp [rateShiftNormalize,Poly.coeff,List.getD,h]

theorem rate_shift_normalize_eval (D : Nat) (p : Poly K) (degree : p.DegLt D) (x : K) :
    (rateShiftNormalize D p).eval x=p.eval x := by
  have zero : (rateShiftNormalize D p-p).IsZero := by
    intro i
    rw [Poly.coeff_sub,rate_shift_normalize_coeff D p degree]
    grind
  have h:=Poly.eval_of_isZero zero x
  rw [Poly.eval_sub] at h
  grind

/-- A continuation candidate becomes an element of the fixed prechallenge
list, with its actual accumulated functional intact. No candidate existence
is inferred from acceptance here; the adaptive continuation theorem bounds
failure of that separate reduction. -/
theorem rate_shift_continuation_candidate (domain : List K) (distinct : domain.Nodup)
    (received : K→K) (D T radius : Nat)
    (radiusFits : domain.length≤T+radius) (unique : 2*radius+D≤domain.length)
    (weights points values : List K) (claim gamma : K)
    (weightSize : D≤weights.length) (candidate : Poly K) (degree : candidate.DegLt D)
    (agreement : T≤count domain (fun x=>received x=candidate.eval x))
    (functional : scalarRSResidual (rateShiftAccumulateWeights weights gamma gamma points) candidate=
      rateShiftAccumulatedClaim claim values gamma) :
    ∃ normalized∈rateShiftUniqueList domain received D radius,
      (∀ i,normalized.coeff i=candidate.coeff i) ∧
      rateShiftAccumulatedFunctional weights points gamma normalized=rateShiftAccumulatedClaim claim values gamma := by
  let normalized:=rateShiftNormalize D candidate
  have coeffs:=rate_shift_normalize_coeff D candidate degree
  have evals : normalized.eval=candidate.eval := by
    funext x;exact rate_shift_normalize_eval D candidate degree x
  have partition:=finite_rs_agreement_partition domain received candidate.eval
  have close : RateShiftCloseCandidate domain received D radius normalized := by
    constructor
    · exact rate_shift_normalize_length D candidate
    · rw [evals];omega
  refine ⟨normalized,rate_shift_unique_list_complete domain distinct received D radius unique normalized close,coeffs,?_⟩
  rw [←rate_shift_accumulated_weights_functional weights points gamma normalized
    (by rw [rate_shift_normalize_length];exact weightSize)]
  rw [scalar_rs_residual_congr normalized candidate _ coeffs]
  exact functional
private theorem unit_mass_bound {A : Type} (domain : List A) (weight : A→Nat)
    (event : A→Prop) (cap : ∀ x∈domain,weight x≤1) :
    consistencyMass domain weight event≤count domain event := by
  classical
  induction domain with
  | nil => simp [consistencyMass,count]
  | cons x xs ih =>
    have head:=cap x (by simp)
    have tail:=ih (fun y hy=>cap y (by simp [hy]))
    simp only [consistencyMass,count,List.map_cons,List.sum_cons,List.countP_cons] at tail ⊢
    by_cases h : event x <;> simp_all <;> omega

/-- The actual indexed continuation candidate supplies the agreement and
functional premises, with an explicit fixed received-oracle binding. -/
theorem rate_shift_indexed_candidate (N D T radius : Nat) (sizes degrees : Nat→Nat)
    (roots challenges : Nat→K) (oracles : Nat→Nat→K)
    (allWeights : Nat→List K) (claims : Nat→K)
    (sizeInitial : sizes 0=N) (degreeInitial : degrees 0=D)
    (received : K→K) (binding : ∀ i<N,oracles 0 i=received (roots 0^i))
    (domainDistinct : ((List.range N).map (fun i=>roots 0^i)).Nodup)
    (radiusFits : N≤T+radius) (unique : 2*radius+D≤N)
    (weights points values : List K) (claim gamma : K) (weightSize : D≤weights.length)
    (initialWeights : allWeights 0=rateShiftAccumulateWeights weights gamma gamma points)
    (initialClaim : claims 0=rateShiftAccumulatedClaim claim values gamma)
    (candidate : indexedChainCandidate N sizes degrees roots challenges oracles allWeights claims T 0) :
    ∃ normalized∈rateShiftUniqueList ((List.range N).map (fun i=>roots 0^i)) received D radius,
      rateShiftAccumulatedFunctional weights points gamma normalized=rateShiftAccumulatedClaim claim values gamma := by
  obtain ⟨p,degree,functional,mass⟩:=candidate
  have cap : ∀ y∈List.range N,globalChainWeight (List.range N) sizes
      (globalRSChainCheck sizes roots challenges oracles) 0 y≤1 := by
    intro y hy
    exact global_chain_weight_cap N sizes _ 0 sizeInitial (by intro j hj;omega) y
      (by rw [sizeInitial];exact List.mem_range.mp hy)
  rw [sizeInitial] at mass
  have agree:=Nat.le_trans mass (unit_mass_bound _ _ _ cap)
  have transport : count (List.range N) (fun y=>oracles 0 y=p.eval (roots 0^y))=
      count ((List.range N).map (fun i=>roots 0^i)) (fun x=>received x=p.eval x) := by
    classical
    simp only [count,List.countP_map,Function.comp_def]
    apply List.countP_congr
    intro y hy
    simp only [decide_eq_true_eq]
    rw [binding y (List.mem_range.mp hy)]
  rw [transport] at agree
  rw [initialWeights,initialClaim] at functional
  obtain ⟨normalized,member,_,equal⟩:=rate_shift_continuation_candidate
    ((List.range N).map (fun i=>roots 0^i)) domainDistinct received D T radius
    (by simpa using radiusFits) (by simpa using unique) weights points values claim gamma weightSize
    p (by simpa only [degreeInitial] using degree) agree functional
  exact ⟨normalized,member,equal⟩

end NearCompression
