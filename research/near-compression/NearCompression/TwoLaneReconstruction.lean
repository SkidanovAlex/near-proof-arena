import NearCompression.UniqueBatchCandidates

/-! Explicit two-challenge reconstruction for arbitrary two-lane oracles.
No initial close-polynomial tuple is assumed. Each challenge supplies its own
candidate; the reconstructed pair agrees wherever both candidates agree. -/
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

def twoLaneRecoveredOne (a b : K) (pa pb : Poly K) : Poly K :=
  Poly.smul (b-a)⁻¹ (pb-pa)

def twoLaneRecoveredZero (a b : K) (pa pb : Poly K) : Poly K :=
  pa-Poly.smul a (twoLaneRecoveredOne a b pa pb)

theorem two_lane_reconstruction_point (a b u v : K) (different : a≠b)
    (pa pb : Poly K) (x : K) (atA : pa.eval x=u+a*v) (atB : pb.eval x=u+b*v) :
    (twoLaneRecoveredZero a b pa pb).eval x=u ∧
    (twoLaneRecoveredOne a b pa pb).eval x=v := by
  have nz : b-a≠0 := by grind
  have inv := Field.inv_mul_cancel nz
  simp only [twoLaneRecoveredZero,twoLaneRecoveredOne,Poly.eval_sub,Poly.eval_smul,atA,atB]
  constructor <;> grind

theorem two_lane_reconstruction_degree (a b : K) (pa pb : Poly K) (D : Nat)
    (ha : pa.DegLt D) (hb : pb.DegLt D) :
    (twoLaneRecoveredZero a b pa pb).DegLt D ∧
    (twoLaneRecoveredOne a b pa pb).DegLt D := by
  have one := Poly.degLt_smul (b-a)⁻¹ (Poly.degLt_sub hb ha)
  exact ⟨Poly.degLt_sub ha (Poly.degLt_smul a one),one⟩

theorem two_lane_reconstruction_residual (a b : K) (different : a≠b)
    (pa pb : Poly K) (weights : List K) (c0 c1 : K)
    (atA : scalarRSResidual weights pa=c0+a*c1)
    (atB : scalarRSResidual weights pb=c0+b*c1) :
    scalarRSResidual weights (twoLaneRecoveredZero a b pa pb)=c0 ∧
    scalarRSResidual weights (twoLaneRecoveredOne a b pa pb)=c1 := by
  have sub (p q : Poly K) : scalarRSResidual weights (p-q)=
      scalarRSResidual weights p-scalarRSResidual weights q := by
    clear atA atB
    unfold scalarRSResidual
    generalize 0 = offset
    induction weights generalizing offset with
    | nil => simp only [scalarRSResidualFrom]; grind
    | cons w ws ih => simp only [scalarRSResidualFrom,Poly.coeff_sub,ih]; grind
  have nz : b-a≠0 := by grind
  have inv := Field.inv_mul_cancel nz
  simp only [twoLaneRecoveredZero,twoLaneRecoveredOne,sub,scalar_rs_residual_scale,atA,atB]
  constructor <;> grind

/-- Joint errors are contained in the union of the two scalar error sets.
Domain distinctness is unnecessary for this reconstruction step. -/
theorem two_lane_reconstruction_distance (domain : List K) (f g : K → K)
    (a b : K) (different : a≠b) (pa pb : Poly K) :
    count domain (jointLaneMismatch [f,g]
      [twoLaneRecoveredZero a b pa pb,twoLaneRecoveredOne a b pa pb]) ≤
    finiteRSMismatches domain (fun x => f x+a*g x) pa.eval +
    finiteRSMismatches domain (fun x => f x+b*g x) pb.eval := by
  classical
  induction domain with
  | nil => simp [count,finiteRSMismatches]
  | cons x xs ih =>
    have point : f x+a*g x=pa.eval x → f x+b*g x=pb.eval x →
        ¬jointLaneMismatch [f,g]
          [twoLaneRecoveredZero a b pa pb,twoLaneRecoveredOne a b pa pb] x := by
      intro ha hb
      obtain ⟨h0,h1⟩ := two_lane_reconstruction_point a b (f x) (g x) different pa pb x ha.symm hb.symm
      simp [jointLaneMismatch,h0,h1]
    simp only [count,finiteRSMismatches,List.countP_cons] at ih ⊢
    by_cases ha : f x+a*g x=pa.eval x <;>
      by_cases hb : f x+b*g x=pb.eval x <;>
      by_cases hj : jointLaneMismatch [f,g]
        [twoLaneRecoveredZero a b pa pb,twoLaneRecoveredOne a b pa pb] x <;>
      simp_all <;> omega

/-- Two distinct successful scalar challenges construct a jointly-close tuple
with both original residual claims. Radii add; no unique-decoding premise. -/
theorem two_lane_candidates_reconstruct (domain : List K) (f g : K → K)
    (a b : K) (different : a≠b) (pa pb : Poly K) (weights : List K)
    (c0 c1 : K) (D ra rb : Nat) (ha : pa.DegLt D) (hb : pb.DegLt D)
    (closeA : finiteRSMismatches domain (fun x => f x+a*g x) pa.eval≤ra)
    (closeB : finiteRSMismatches domain (fun x => f x+b*g x) pb.eval≤rb)
    (claimA : scalarRSResidual weights pa=c0+a*c1)
    (claimB : scalarRSResidual weights pb=c0+b*c1) :
    ∃ p0 p1 : Poly K, p0.DegLt D ∧ p1.DegLt D ∧
      count domain (jointLaneMismatch [f,g] [p0,p1])≤ra+rb ∧
      scalarRSResidual weights p0=c0 ∧ scalarRSResidual weights p1=c1 := by
  refine ⟨twoLaneRecoveredZero a b pa pb,twoLaneRecoveredOne a b pa pb,?_,?_,?_,?_,?_⟩
  · exact (two_lane_reconstruction_degree a b pa pb D ha hb).1
  · exact (two_lane_reconstruction_degree a b pa pb D ha hb).2
  · have h := two_lane_reconstruction_distance domain f g a b different pa pb
    omega
  · exact (two_lane_reconstruction_residual a b different pa pb weights c0 c1 claimA claimB).1
  · exact (two_lane_reconstruction_residual a b different pa pb weights c0 c1 claimA claimB).2

private theorem count_at_most_one {A : Type} (sample : List A) (distinct : sample.Nodup)
    (event : A → Prop) (unique : ∀ a∈sample,∀ b∈sample,event a → event b → a=b) :
    count sample event≤1 := by
  classical
  induction sample with
  | nil => simp [count]
  | cons a rest ih =>
    have nd := List.nodup_cons.mp distinct
    by_cases ha : event a
    · have empty : count rest event=0 := by
        have h : count rest event≤count rest (fun _ => False) := by
          apply count_mono_mem
          intro b member hb
          have eq := unique a (by simp) b (by simp [member]) ha hb
          exact nd.1 (eq ▸ member)
        simpa [count] using h
      simp only [count,List.countP_cons] at empty ⊢
      simp only [ha,decide_true,ite_true]
      omega
    · have h := ih nd.2 (fun b hb c hc => unique b (by simp [hb]) c (by simp [hc]))
      simpa [count,List.countP_cons,ha] using h

/-- Far-source correlated agreement for TWO lanes, with explicit radius
expansion: if no claim-compatible tuple lies within 2*r jointly, at most one
challenge has a claim-compatible scalar candidate within r. -/
theorem two_lane_far_bad_count (domain sample : List K) (distinct : sample.Nodup)
    (f g : K → K) (weights : List K) (c0 c1 : K) (D r : Nat)
    (far : ¬∃ p0 p1 : Poly K,p0.DegLt D ∧ p1.DegLt D ∧
      count domain (jointLaneMismatch [f,g] [p0,p1])≤r+r ∧
      scalarRSResidual weights p0=c0 ∧ scalarRSResidual weights p1=c1) :
    count sample (fun a => ∃ p : Poly K,p.DegLt D ∧
      finiteRSMismatches domain (fun x => f x+a*g x) p.eval≤r ∧
      scalarRSResidual weights p=c0+a*c1)≤1 := by
  apply count_at_most_one sample distinct
  intro a ha b hb ca cb
  apply Classical.byContradiction
  intro different
  obtain ⟨pa,da,closeA,claimA⟩ := ca
  obtain ⟨pb,db,closeB,claimB⟩ := cb
  exact far (two_lane_candidates_reconstruct domain f g a b different pa pb weights
    c0 c1 D r r da db closeA closeB claimA claimB)

end NearCompression
