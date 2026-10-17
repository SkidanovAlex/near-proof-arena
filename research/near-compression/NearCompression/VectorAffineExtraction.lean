import NearCompression.WeightedThreeCandidate

/-! Affine extraction for arbitrary vectors of source words. The RS polynomial
degree, weighted threshold and weight cap do not grow with vector dimension.
No residual, commitment, sampler or shared AIR-witness claim is made here. -/
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K I : Type} [Field K]

/-- Joint vector concentration by choosing, at each nonjoint domain point, one
fixed discrepant coordinate. The choice is before the scalar challenge. -/
theorem vector_shared_curve_joint_agreement (domain : List K) (weight : K → Nat)
    (sourceEven sourceOdd candidateEven candidateOdd : K → I → K)
    (T : Nat) (sample : List K) (distinct : sample.Nodup)
    (many : domain.length<count sample (fun r => T≤consistencyMass domain weight
      (fun x => ∀ i,(1-r)*sourceEven x i+r*sourceOdd x i=
        (1-r)*candidateEven x i+r*candidateOdd x i))) :
    T≤consistencyMass domain weight
      (fun x => ∀ i,sourceEven x i=candidateEven x i ∧ sourceOdd x i=candidateOdd x i) := by
  classical
  let differs (x : K) := ∃ i,¬(sourceEven x i=candidateEven x i ∧ sourceOdd x i=candidateOdd x i)
  let select (f : K → I → K) (x : K) : K := if h : differs x then f x (Classical.choose h) else 0
  have scalarJoint (x : K) :
      (select sourceEven x=select candidateEven x ∧ select sourceOdd x=select candidateOdd x) ↔
      ∀ i,sourceEven x i=candidateEven x i ∧ sourceOdd x i=candidateOdd x i := by
    by_cases h : differs x
    · simp only [select,dite_eq_left h]
      constructor
      · intro equal
        exact False.elim (Classical.choose_spec h equal)
      · intro equal
        exact equal (Classical.choose h)
    · simp only [select,dite_eq_right h]
      constructor
      · intro _ i
        apply Classical.byContradiction
        intro different
        exact h ⟨i,different⟩
      · intro _
        trivial
  have subset : count sample (fun r => T≤consistencyMass domain weight
      (fun x => ∀ i,(1-r)*sourceEven x i+r*sourceOdd x i=
        (1-r)*candidateEven x i+r*candidateOdd x i))≤
      count sample (fun r => T≤consistencyMass domain weight
      (fun x => (1-r)*select sourceEven x+r*select sourceOdd x=
        (1-r)*select candidateEven x+r*select candidateOdd x)) := by
    apply count_mono
    intro r success
    apply Nat.le_trans success
    apply consistency_mass_mono
    intro x hx equal
    by_cases h : differs x
    · simpa only [select,dite_eq_left h] using equal (Classical.choose h)
    · simp only [select,dite_eq_right h]
  have scalar := shared_curve_joint_agreement domain weight (select sourceEven) (select sourceOdd)
    (select candidateEven) (select candidateOdd) T sample distinct (by omega)
  apply Nat.le_trans scalar
  apply consistency_mass_mono
  intro x hx equal
  exact (scalarJoint x).mp equal

/-- Adaptive vector candidates at sufficiently many challenges reconstruct a
SINGLE jointly close pair of polynomial vectors. No scalar or coordinatewise
closeness of an initially fixed polynomial vector is assumed. -/
theorem vector_affine_extraction (domain sample : List K)
    (domainDistinct : domain.Nodup) (sampleDistinct : sample.Nodup)
    (weight : K → Nat) (B D T : Nat) (bounded : ∀ x∈domain,weight x≤B)
    (sourceEven sourceOdd : K → I → K)
    (decoded : K → I → Poly K)
    (degrees : ∀ r∈sample,∀ i,(decoded r i).DegLt D)
    (agreements : ∀ r∈sample,T≤consistencyMass domain weight
      (fun x => ∀ i,(decoded r i).eval x=(1-r)*sourceEven x i+r*sourceOdd x i))
    (many : max domain.length 2<sample.length)
    (separation : 2*(domain.map weight).sum+B*(D-1)<3*T) :
    ∃ even odd : I → Poly K,(∀ i,(even i).DegLt D ∧ (odd i).DegLt D) ∧
      T≤consistencyMass domain weight
        (fun x => ∀ i,sourceEven x i=(even i).eval x ∧ sourceOdd x i=(odd i).eval x) := by
  classical
  cases sample with
  | nil => simp at many
  | cons a rest => cases rest with
    | nil => simp at many
    | cons b rest =>
      let sample := a::b::rest
      change max domain.length 2<sample.length at many
      have ha : a∈sample := by simp [sample]
      have hb : b∈sample := by simp [sample]
      have different : a≠b := by
        have h := (List.nodup_cons.mp sampleDistinct).1
        intro eq
        exact h (by simp [eq])
      let even := fun i => affineRecoveredEven a b (decoded a i) (decoded b i)
      let odd := fun i => affineRecoveredOdd a b (decoded a i) (decoded b i)
      have ds : ∀ i,(even i).DegLt D ∧ (odd i).DegLt D := fun i =>
        affine_reconstruction_degree a b (decoded a i) (decoded b i) D (degrees a ha i) (degrees b hb i)
      have scalarAgree (r : K) (hr : r∈sample) (i : I) :
          T≤consistencyMass domain weight
            (fun x => (decoded r i).eval x=(1-r)*sourceEven x i+r*sourceOdd x i) := by
        apply Nat.le_trans (agreements r hr)
        apply consistency_mass_mono
        intro x hx equal
        exact equal i
      have curve (r : K) (hr : r∈sample) (i : I) :
          (decoded r i-recoveredAffineCurve a b (decoded a i) (decoded b i) r).IsZero :=
        weighted_three_candidate_curve domain domainDistinct weight B D T bounded
          (fun x => sourceEven x i) (fun x => sourceOdd x i) a b r different
          (decoded a i) (decoded b i) (decoded r i) (degrees a ha i) (degrees b hb i) (degrees r hr i)
          (scalarAgree a ha i) (scalarAgree b hb i) (scalarAgree r hr i) separation
      have onCurve (r : K) (hr : r∈sample) (i : I) (x : K) :
          (decoded r i).eval x=(1-r)*(even i).eval x+r*(odd i).eval x := by
        have equal := Poly.eval_of_isZero (curve r hr i) x
        simp only [Poly.eval_sub,recoveredAffineCurve,Poly.eval_add,Poly.eval_smul] at equal
        change (decoded r i).eval x-( (1-r)*(even i).eval x+r*(odd i).eval x)=0 at equal
        grind
      refine ⟨even,odd,ds,?_⟩
      apply vector_shared_curve_joint_agreement domain weight sourceEven sourceOdd
        (fun x i => (even i).eval x) (fun x i => (odd i).eval x) T sample sampleDistinct
      have all : count sample (fun r => T≤consistencyMass domain weight
          (fun x => ∀ i,(1-r)*sourceEven x i+r*sourceOdd x i=
            (1-r)*(even i).eval x+r*(odd i).eval x))=sample.length := by
        unfold count
        apply List.countP_eq_length.mpr
        intro r hr
        apply @_root_.decide_eq_true _ (Classical.propDecidable _)
        apply Nat.le_trans (agreements r hr)
        apply consistency_mass_mono
        intro x hx equal i
        exact (equal i).symm.trans (onCurve r hr i x)
      rw [all]
      have lower := Nat.le_max_left domain.length 2
      omega

noncomputable def vectorAffineSuccess (domain : List K) (weight : K → Nat)
    (sourceEven sourceOdd : K → I → K) (D T : Nat) (r : K) : Prop :=
  ∃ candidate : I → Poly K,(∀ i,(candidate i).DegLt D) ∧
    T≤consistencyMass domain weight (fun x => ∀ i,
      (candidate i).eval x=(1-r)*sourceEven x i+r*sourceOdd x i)

/-- Explicit finite conditional bad-count contract for one tensor coordinate.
The existential candidate is INSIDE the challenge predicate. -/
theorem vector_affine_bad_count (domain sample : List K)
    (domainDistinct : domain.Nodup) (sampleDistinct : sample.Nodup)
    (weight : K → Nat) (B D T : Nat) (bounded : ∀ x∈domain,weight x≤B)
    (sourceEven sourceOdd : K → I → K)
    (separation : 2*(domain.map weight).sum+B*(D-1)<3*T)
    (noPair : ¬∃ even odd : I → Poly K,(∀ i,(even i).DegLt D ∧ (odd i).DegLt D) ∧
      T≤consistencyMass domain weight
        (fun x => ∀ i,sourceEven x i=(even i).eval x ∧ sourceOdd x i=(odd i).eval x)) :
    count sample (vectorAffineSuccess domain weight sourceEven sourceOdd D T)≤max domain.length 2 := by
  classical
  apply Nat.le_of_not_gt
  intro many
  let success := vectorAffineSuccess domain weight sourceEven sourceOdd D T
  let good := sample.filter (fun r => decide (success r))
  have goodDistinct : good.Nodup := List.Sublist.nodup List.filter_sublist sampleDistinct
  have goodLength : good.length=count sample success := List.countP_eq_length_filter.symm
  have goodSuccess : ∀ r∈good,success r := by
    intro r hr
    exact @_root_.of_decide_eq_true _ (Classical.propDecidable _) (List.mem_filter.mp hr).2
  let decoded : K → I → Poly K := fun r => if h : success r then Classical.choose h else fun _ => Poly.zero
  have correct : ∀ r∈good,(∀ i,(decoded r i).DegLt D) ∧
      T≤consistencyMass domain weight
        (fun x => ∀ i,(decoded r i).eval x=(1-r)*sourceEven x i+r*sourceOdd x i) := by
    intro r hr
    have h := goodSuccess r hr
    have spec := Classical.choose_spec h
    simpa only [decoded,dite_eq_left h] using spec
  exact noPair (vector_affine_extraction domain good domainDistinct goodDistinct weight B D T bounded
    sourceEven sourceOdd decoded (fun r hr => (correct r hr).1) (fun r hr => (correct r hr).2)
    (by rw [goodLength]; exact many) separation)

end NearCompression
