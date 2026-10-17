import NearCompression.AffineFoldReconstruction
import NearCompression.FiniteRSUniqueDecoding
import NearCompression.WeightedConsistencyTransfer
import NearCompression.SharedCurveConcentration

/-! Shared-curve reconstruction in a stricter weighted unique-decoding regime.
Three successful candidates must lie on the same affine polynomial curve if
3*T > 2*totalWeight + B*(D-1). No list-decoding/concentration axiom is used. -/
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

private theorem weighted_triple_intersection {A : Type} (domain : List A)
    (weight : A → Nat) (p q r : A → Prop) :
    consistencyMass domain weight p+consistencyMass domain weight q+consistencyMass domain weight r ≤
      2*(domain.map weight).sum+consistencyMass domain weight (fun x => p x ∧ q x ∧ r x) := by
  classical
  induction domain with
  | nil => simp [consistencyMass]
  | cons x xs ih =>
    simp only [consistencyMass,List.map_cons,List.sum_cons] at ih ⊢
    by_cases hp : p x <;> by_cases hq : q x <;> by_cases hr : r x <;> simp_all <;> omega

private theorem weighted_mass_count_bound {A : Type} (domain : List A)
    (weight : A → Nat) (event : A → Prop) (B : Nat)
    (bounded : ∀ x∈domain,weight x≤B) :
    consistencyMass domain weight event≤B*count domain event := by
  classical
  induction domain with
  | nil => simp [consistencyMass,count]
  | cons x xs ih =>
    have tail := ih (fun y hy => bounded y (by simp [hy]))
    have head := bounded x (by simp)
    simp only [consistencyMass,count,List.map_cons,List.sum_cons,List.countP_cons] at tail ⊢
    by_cases h : event x <;> simp_all <;> grind

/-- A weighted version of the actual RS agreement bound. -/
theorem weighted_distinct_polynomial_agreement (domain : List K) (distinct : domain.Nodup)
    (weight : K → Nat) (B D : Nat) (bounded : ∀ x∈domain,weight x≤B)
    (p q : Poly K) (dp : p.DegLt D) (dq : q.DegLt D) (different : ¬(p-q).IsZero) :
    consistencyMass domain weight (fun x => p.eval x=q.eval x)≤B*(D-1) := by
  have roots := finite_rs_distinct_agreement domain distinct p q D dp dq different
  have weighted := weighted_mass_count_bound domain weight (fun x => p.eval x=q.eval x) B bounded
  have rootBound : count domain (fun x => p.eval x=q.eval x)≤D-1 := by omega
  exact Nat.le_trans weighted (Nat.mul_le_mul_left B rootBound)

def recoveredAffineCurve (a b : K) (pa pb : Poly K) (r : K) : Poly K :=
  Poly.smul (1-r) (affineRecoveredEven a b pa pb)+Poly.smul r (affineRecoveredOdd a b pa pb)

theorem recovered_affine_curve_degree (a b : K) (pa pb : Poly K) (r : K) (D : Nat)
    (da : pa.DegLt D) (db : pb.DegLt D) : (recoveredAffineCurve a b pa pb r).DegLt D := by
  have h := affine_reconstruction_degree a b pa pb D da db
  exact Poly.degLt_add (Poly.degLt_smul _ h.1) (Poly.degLt_smul _ h.2)

private theorem recovered_affine_curve_point (a b r e o : K) (different : a≠b)
    (pa pb : Poly K) (x : K)
    (ha : pa.eval x=(1-a)*e+a*o) (hb : pb.eval x=(1-b)*e+b*o) :
    (recoveredAffineCurve a b pa pb r).eval x=(1-r)*e+r*o := by
  have aa : pa.eval x=e+a*(o-e) := by grind
  have bb : pb.eval x=e+b*(o-e) := by grind
  obtain ⟨even,slope⟩ := two_lane_reconstruction_point a b e (o-e) different pa pb x aa bb
  simp only [recoveredAffineCurve,affineRecoveredOdd,affineRecoveredEven,
    Poly.eval_add,Poly.eval_smul,even,slope]
  grind

/-- The first two candidate polynomials fix a curve before considering the
third. Source functions are completely arbitrary; the third candidate may be
chosen adaptively. Weighted agreement at three challenges pins that candidate
to the reconstructed curve under the explicit separation inequality. -/
theorem weighted_three_candidate_curve (domain : List K) (distinct : domain.Nodup)
    (weight : K → Nat) (B D T : Nat) (bounded : ∀ x∈domain,weight x≤B)
    (sourceEven sourceOdd : K → K) (a b r : K) (different : a≠b)
    (pa pb pr : Poly K) (da : pa.DegLt D) (db : pb.DegLt D) (dr : pr.DegLt D)
    (agreeA : T≤consistencyMass domain weight
      (fun x => pa.eval x=(1-a)*sourceEven x+a*sourceOdd x))
    (agreeB : T≤consistencyMass domain weight
      (fun x => pb.eval x=(1-b)*sourceEven x+b*sourceOdd x))
    (agreeR : T≤consistencyMass domain weight
      (fun x => pr.eval x=(1-r)*sourceEven x+r*sourceOdd x))
    (separation : 2*(domain.map weight).sum+B*(D-1)<3*T) :
    (pr-recoveredAffineCurve a b pa pb r).IsZero := by
  classical
  apply Classical.byContradiction
  intro differentPolynomial
  have triple := weighted_triple_intersection domain weight
    (fun x => pa.eval x=(1-a)*sourceEven x+a*sourceOdd x)
    (fun x => pb.eval x=(1-b)*sourceEven x+b*sourceOdd x)
    (fun x => pr.eval x=(1-r)*sourceEven x+r*sourceOdd x)
  have subset := consistency_mass_mono domain weight
    (fun x => pa.eval x=(1-a)*sourceEven x+a*sourceOdd x ∧
      pb.eval x=(1-b)*sourceEven x+b*sourceOdd x ∧
      pr.eval x=(1-r)*sourceEven x+r*sourceOdd x)
    (fun x => pr.eval x=(recoveredAffineCurve a b pa pb r).eval x) (by
      intro x hx h
      exact h.2.2.trans (recovered_affine_curve_point a b r (sourceEven x) (sourceOdd x)
        different pa pb x h.1 h.2.1).symm)
  have roots := weighted_distinct_polynomial_agreement domain distinct weight B D bounded
    pr (recoveredAffineCurve a b pa pb r) dr (recovered_affine_curve_degree a b pa pb r D da db)
    differentPolynomial
  omega

/-- An unconditional weighted extraction theorem in the stricter separation
regime. The adaptive candidate function is unrestricted. Its successful
challenge list supplies two reconstruction points and enough concentration
points. No imported list-decoding theorem or unspecified constant is used. -/
theorem weighted_unique_regime_extraction (domain : List K) (domainDistinct : domain.Nodup)
    (weight : K → Nat) (B D T : Nat) (bounded : ∀ x∈domain,weight x≤B)
    (sourceEven sourceOdd : K → K) (sample : List K) (sampleDistinct : sample.Nodup)
    (many : domain.length<sample.length) (three : 3≤sample.length)
    (decoded : K → Poly K) (weights : List K) (w0 w1 : K) (sent : Poly K)
    (sentDegree : sent.DegLt 3)
    (degrees : ∀ r∈sample,(decoded r).DegLt D)
    (agreements : ∀ r∈sample,T≤consistencyMass domain weight
      (fun x => (decoded r).eval x=(1-r)*sourceEven x+r*sourceOdd x))
    (residuals : ∀ r∈sample,((1-r)*w0+r*w1)*scalarRSResidual weights (decoded r)=sent.eval r)
    (separation : 2*(domain.map weight).sum+B*(D-1)<3*T) :
    ∃ even odd : Poly K,even.DegLt D ∧ odd.DegLt D ∧
      T≤consistencyMass domain weight
        (fun x => sourceEven x=even.eval x ∧ sourceOdd x=odd.eval x) ∧
      (sent-weightedFoldResidualPolynomial w0 w1
        (scalarRSResidual weights even) (scalarRSResidual weights odd)).IsZero := by
  classical
  cases sample with
  | nil => simp at three
  | cons a rest => cases rest with
    | nil => simp at three
    | cons b rest =>
      let sample := a::b::rest
      have ha : a∈sample := by simp [sample]
      have hb : b∈sample := by simp [sample]
      have different : a≠b := by
        have h := (List.nodup_cons.mp sampleDistinct).1
        intro eq
        exact h (by simp [eq])
      let even := affineRecoveredEven a b (decoded a) (decoded b)
      let odd := affineRecoveredOdd a b (decoded a) (decoded b)
      have curveDegrees := affine_reconstruction_degree a b (decoded a) (decoded b) D
        (degrees a ha) (degrees b hb)
      have onCurve (r : K) (hr : r∈sample) :
          (decoded r-recoveredAffineCurve a b (decoded a) (decoded b) r).IsZero :=
        weighted_three_candidate_curve domain domainDistinct weight B D T bounded sourceEven sourceOdd
          a b r different (decoded a) (decoded b) (decoded r)
          (degrees a ha) (degrees b hb) (degrees r hr)
          (agreements a ha) (agreements b hb) (agreements r hr) separation
      have evalEqual (r : K) (hr : r∈sample) (x : K) :
          (decoded r).eval x=(recoveredAffineCurve a b (decoded a) (decoded b) r).eval x := by
        have eq := Poly.eval_of_isZero (onCurve r hr) x
        rw [Poly.eval_sub] at eq
        grind
      have residualEqual (r : K) (hr : r∈sample) :
          scalarRSResidual weights (decoded r)=
          scalarRSResidual weights (recoveredAffineCurve a b (decoded a) (decoded b) r) := by
        apply scalar_rs_residual_congr
        intro i
        have eq := onCurve r hr i
        change (decoded r-recoveredAffineCurve a b (decoded a) (decoded b) r).coeff i=0 at eq
        rw [Poly.coeff_sub] at eq
        grind
      have extracted := shared_polynomial_curve_extraction domain weight sourceEven sourceOdd id
        even odd sent weights w0 w1 T sample sampleDistinct many three sentDegree
        (by
          intro r hr
          apply Nat.le_trans (agreements r hr)
          apply consistency_mass_mono
          intro x hx eq
          rw [evalEqual r hr x] at eq
          simpa only [recoveredAffineCurve,Poly.eval_add,Poly.eval_smul,even,odd,id_eq] using eq.symm)
        (by
          intro r hr
          change ((1-r)*w0+r*w1)*scalarRSResidual weights
            (recoveredAffineCurve a b (decoded a) (decoded b) r)=sent.eval r
          rw [←residualEqual r hr]
          exact residuals r hr)
      exact ⟨even,odd,curveDegrees.1,curveDegrees.2,extracted.1,extracted.2⟩

end NearCompression
