import NearCompression.WeightedThreeCandidate
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

/-- Literal adjacent-weight affine fold after splitting even/odd positions. -/
def generalFoldWeights (evenWeights oddWeights : List K) (r : K) : List K :=
  List.zipWith (fun a b=>(1-r)*a+r*b) evenWeights oddWeights

theorem general_fold_weights_functional (ew ow : List K) (r : K) (p : Poly K)
    (shape : ew.length=ow.length) :
    scalarRSResidual (generalFoldWeights ew ow r) p=
      (1-r)*scalarRSResidual ew p+r*scalarRSResidual ow p := by
  unfold scalarRSResidual generalFoldWeights
  generalize 0=offset
  induction ew generalizing ow offset with
  | nil => cases ow <;> simp_all [scalarRSResidualFrom] <;> grind
  | cons a ew ih =>
    cases ow with
    | nil => simp at shape
    | cons b ow =>
      simp only [List.zipWith_cons_cons,scalarRSResidualFrom]
      rw [ih ow (by simpa using shape)]
      grind

/-- Quadratic for folding both coefficient and arbitrary weight vectors. -/
def generalFoldResidualPolynomial (evenWeights oddWeights : List K) (even odd : Poly K) : Poly K :=
  let a:=scalarRSResidual evenWeights even
  let b:=scalarRSResidual evenWeights odd
  let c:=scalarRSResidual oddWeights even
  let d:=scalarRSResidual oddWeights odd
  Poly.mk [a,b+c-2*a,a-b-c+d]

theorem general_fold_residual_eval (ew ow : List K) (even odd : Poly K) (r : K) :
    (generalFoldResidualPolynomial ew ow even odd).eval r=
      (1-r)*scalarRSResidual ew (Poly.smul (1-r) even+Poly.smul r odd)+
      r*scalarRSResidual ow (Poly.smul (1-r) even+Poly.smul r odd) := by
  simp only [generalFoldResidualPolynomial,Poly.eval,Poly.evalL,
    scalar_rs_residual_add,scalar_rs_residual_scale]
  grind

/-- Endpoint sum is the original interleaved coefficient/weight functional. -/
theorem general_fold_residual_endpoints (ew ow : List K) (even odd : Poly K) :
    (generalFoldResidualPolynomial ew ow even odd).eval 0+
      (generalFoldResidualPolynomial ew ow even odd).eval 1=
      scalarRSResidual ew even+scalarRSResidual ow odd := by
  simp only [generalFoldResidualPolynomial,Poly.eval,Poly.evalL]
  grind

theorem general_shared_curve_extraction {A : Type} (domain : List A)
    (weight : A → Nat) (sourceEven sourceOdd point : A → K)
    (even odd sent : Poly K) (evenWeights oddWeights : List K) (threshold : Nat)
    (sample : List K) (distinct : sample.Nodup)
    (many : domain.length<sample.length) (three : 3≤sample.length)
    (sentDegree : sent.DegLt 3)
    (agreement : ∀ r∈sample,threshold≤consistencyMass domain weight
      (fun x => (1-r)*sourceEven x+r*sourceOdd x=
        (1-r)*even.eval (point x)+r*odd.eval (point x)))
    (residual : ∀ r∈sample,(1-r)*scalarRSResidual evenWeights (Poly.smul (1-r) even+Poly.smul r odd)+
      r*scalarRSResidual oddWeights (Poly.smul (1-r) even+Poly.smul r odd)=sent.eval r) :
    threshold≤consistencyMass domain weight
      (fun x => sourceEven x=even.eval (point x) ∧ sourceOdd x=odd.eval (point x)) ∧
    (sent-generalFoldResidualPolynomial evenWeights oddWeights even odd).IsZero := by
  classical
  constructor
  · apply shared_curve_joint_agreement domain weight sourceEven sourceOdd
      (fun x => even.eval (point x)) (fun x => odd.eval (point x)) threshold sample distinct
    have all : count sample (fun r => threshold≤consistencyMass domain weight
        (fun x => (1-r)*sourceEven x+r*sourceOdd x=
          (1-r)*even.eval (point x)+r*odd.eval (point x)))=sample.length := by
      unfold count
      apply List.countP_eq_length.mpr
      intro r hr
      exact @_root_.decide_eq_true _ (Classical.propDecidable _) (agreement r hr)
    rw [all]
    exact many
  · apply PolyRoots.eqZeroOfRoots_of polyEval polyDeg quotFacts isZeroEval K
      (sent-generalFoldResidualPolynomial evenWeights oddWeights even odd) 3 sample
    · exact Poly.degLt_sub sentDegree (Poly.degLt_length _)
    · exact distinct
    · exact three
    · intro r hr
      rw [Poly.eval_sub,general_fold_residual_eval]
      have value := residual r hr
      grind

/-- Adaptive candidate extraction for unrestricted public even/odd weights.
No tensor factorization, commitment extraction or rate-shift transfer premise. -/
theorem general_weighted_unique_extraction (domain : List K) (domainDistinct : domain.Nodup)
    (weight : K → Nat) (B D T : Nat) (bounded : ∀ x∈domain,weight x≤B)
    (sourceEven sourceOdd : K → K) (sample : List K) (sampleDistinct : sample.Nodup)
    (many : domain.length<sample.length) (three : 3≤sample.length)
    (decoded : K → Poly K) (evenWeights oddWeights : List K) (sent : Poly K)
    (sentDegree : sent.DegLt 3)
    (degrees : ∀ r∈sample,(decoded r).DegLt D)
    (agreements : ∀ r∈sample,T≤consistencyMass domain weight
      (fun x => (decoded r).eval x=(1-r)*sourceEven x+r*sourceOdd x))
    (residuals : ∀ r∈sample,(1-r)*scalarRSResidual evenWeights (decoded r)+r*scalarRSResidual oddWeights (decoded r)=sent.eval r)
    (separation : 2*(domain.map weight).sum+B*(D-1)<3*T) :
    ∃ even odd : Poly K,even.DegLt D ∧ odd.DegLt D ∧
      T≤consistencyMass domain weight
        (fun x => sourceEven x=even.eval x ∧ sourceOdd x=odd.eval x) ∧
      (sent-generalFoldResidualPolynomial evenWeights oddWeights even odd).IsZero := by
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
      have residualEqual (weights : List K) (r : K) (hr : r∈sample) :
          scalarRSResidual weights (decoded r)=
          scalarRSResidual weights (recoveredAffineCurve a b (decoded a) (decoded b) r) := by
        apply scalar_rs_residual_congr
        intro i
        have eq := onCurve r hr i
        change (decoded r-recoveredAffineCurve a b (decoded a) (decoded b) r).coeff i=0 at eq
        rw [Poly.coeff_sub] at eq
        grind
      have extracted := general_shared_curve_extraction domain weight sourceEven sourceOdd id
        even odd sent evenWeights oddWeights T sample sampleDistinct many three sentDegree
        (by
          intro r hr
          apply Nat.le_trans (agreements r hr)
          apply consistency_mass_mono
          intro x hx eq
          rw [evalEqual r hr x] at eq
          simpa only [recoveredAffineCurve,Poly.eval_add,Poly.eval_smul,even,odd,id_eq] using eq.symm)
        (by
          intro r hr
          change (1-r)*scalarRSResidual evenWeights (recoveredAffineCurve a b (decoded a) (decoded b) r)+
            r*scalarRSResidual oddWeights (recoveredAffineCurve a b (decoded a) (decoded b) r)=sent.eval r
          rw [←residualEqual evenWeights r hr,←residualEqual oddWeights r hr]
          exact residuals r hr)
      exact ⟨even,odd,curveDegrees.1,curveDegrees.2,extracted.1,extracted.2⟩

noncomputable def generalWeightedCurveSuccess (domain : List K) (weight : K → Nat)
    (sourceEven sourceOdd : K → K) (D T : Nat) (evenWeights oddWeights : List K) (sent : Poly K) (r : K) : Prop :=
  ∃ p : Poly K,p.DegLt D ∧ T≤consistencyMass domain weight
    (fun x => p.eval x=(1-r)*sourceEven x+r*sourceOdd x) ∧
    (1-r)*scalarRSResidual evenWeights p+r*scalarRSResidual oddWeights p=sent.eval r

/-- Actual existential-candidate concentration, in the stricter weighted
unique-decoding regime. The candidate existential is INSIDE the challenge
count. The resulting curve and quadratic identity are constructed, not assumed. -/
theorem general_weighted_extraction_count (domain sample : List K)
    (domainDistinct : domain.Nodup) (sampleDistinct : sample.Nodup)
    (weight : K → Nat) (B D T : Nat) (bounded : ∀ x∈domain,weight x≤B)
    (sourceEven sourceOdd : K → K) (evenWeights oddWeights : List K)
    (sent : Poly K) (sentDegree : sent.DegLt 3)
    (separation : 2*(domain.map weight).sum+B*(D-1)<3*T)
    (many : max domain.length 2<count sample
      (generalWeightedCurveSuccess domain weight sourceEven sourceOdd D T evenWeights oddWeights sent)) :
    ∃ even odd : Poly K,even.DegLt D ∧ odd.DegLt D ∧
      T≤consistencyMass domain weight
        (fun x => sourceEven x=even.eval x ∧ sourceOdd x=odd.eval x) ∧
      (sent-generalFoldResidualPolynomial evenWeights oddWeights even odd).IsZero := by
  classical
  let success := generalWeightedCurveSuccess domain weight sourceEven sourceOdd D T evenWeights oddWeights sent
  let good := sample.filter (fun r => decide (success r))
  have goodDistinct : good.Nodup := List.Sublist.nodup List.filter_sublist sampleDistinct
  have goodLength : good.length=count sample success := List.countP_eq_length_filter.symm
  have goodSuccess : ∀ r∈good,success r := by
    intro r hr
    exact of_decide_eq_true (List.mem_filter.mp hr).2
  let decoded : K → Poly K := fun r => if h : success r then Classical.choose h else Poly.zero
  have decodedCorrect : ∀ r∈good,(decoded r).DegLt D ∧
      T≤consistencyMass domain weight
        (fun x => (decoded r).eval x=(1-r)*sourceEven x+r*sourceOdd x) ∧
      (1-r)*scalarRSResidual evenWeights (decoded r)+r*scalarRSResidual oddWeights (decoded r)=sent.eval r := by
    intro r hr
    have h := goodSuccess r hr
    have spec := Classical.choose_spec h
    simpa only [decoded,dite_eq_left h] using spec
  apply general_weighted_unique_extraction domain domainDistinct weight B D T bounded
    sourceEven sourceOdd good goodDistinct
    (by rw [goodLength]; exact Nat.lt_of_le_of_lt (Nat.le_max_left _ _) many)
    (by
      rw [goodLength]
      change 3≤count sample (generalWeightedCurveSuccess domain weight sourceEven sourceOdd D T evenWeights oddWeights sent)
      have h := Nat.le_max_right domain.length 2
      omega)
    decoded evenWeights oddWeights sent sentDegree
  · intro r hr; exact (decodedCorrect r hr).1
  · intro r hr; exact (decodedCorrect r hr).2.1
  · intro r hr; exact (decodedCorrect r hr).2.2
  · exact separation

/-- Explicit challenge-count error in this regime; no cryptographic premise. -/
theorem general_weighted_extraction_bad_count (domain sample : List K)
    (domainDistinct : domain.Nodup) (sampleDistinct : sample.Nodup)
    (weight : K → Nat) (B D T : Nat) (bounded : ∀ x∈domain,weight x≤B)
    (sourceEven sourceOdd : K → K) (evenWeights oddWeights : List K)
    (sent : Poly K) (sentDegree : sent.DegLt 3)
    (separation : 2*(domain.map weight).sum+B*(D-1)<3*T)
    (noOutcome : ¬∃ even odd : Poly K,even.DegLt D ∧ odd.DegLt D ∧
      T≤consistencyMass domain weight
        (fun x => sourceEven x=even.eval x ∧ sourceOdd x=odd.eval x) ∧
      (sent-generalFoldResidualPolynomial evenWeights oddWeights even odd).IsZero) :
    count sample (generalWeightedCurveSuccess domain weight sourceEven sourceOdd D T evenWeights oddWeights sent)
      ≤max domain.length 2 := by
  have impossible : ¬max domain.length 2<count sample
      (generalWeightedCurveSuccess domain weight sourceEven sourceOdd D T evenWeights oddWeights sent) := by
    intro many
    exact noOutcome (general_weighted_extraction_count domain sample domainDistinct sampleDistinct
      weight B D T bounded sourceEven sourceOdd evenWeights oddWeights sent sentDegree separation many)
  omega

end NearCompression
