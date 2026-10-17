import NearCompression.WeightedJohnsonList
import NearCompression.FiniteRSJohnsonCandidates

/-! A fixed complete mathematical family of jointly agreeing curve pairs.
Enumeration is not a practical decoder and does not prove correlated transfer. -/
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]
attribute [local instance] Classical.propDecidable

noncomputable def weightedCurveCandidates (alphabet domain : List K) (weight : K → Nat)
    (sourceEven sourceOdd : K → K) (D T : Nat) : List (Poly K × Poly K) :=
  let all := johnsonCandidateList alphabet [] (fun _ => 0) D 0
  (all.flatMap (fun a => all.map (fun b => (a,b)))).filter (fun pair => decide
    (T≤consistencyMass domain weight
      (fun x => sourceEven x=pair.1.eval x ∧ sourceOdd x=pair.2.eval x)))

theorem weighted_curve_candidates_sound (alphabet domain : List K) (weight : K → Nat)
    (sourceEven sourceOdd : K → K) (D T : Nat) (pair : Poly K × Poly K)
    (member : pair∈weightedCurveCandidates alphabet domain weight sourceEven sourceOdd D T) :
    pair.1.DegLt D ∧ pair.2.DegLt D ∧ T≤consistencyMass domain weight
      (fun x => sourceEven x=pair.1.eval x ∧ sourceOdd x=pair.2.eval x) := by
  obtain ⟨mem,close⟩ := List.mem_filter.mp member
  obtain ⟨a,ha,mapped⟩ := List.mem_flatMap.mp mem
  obtain ⟨b,hb,equal⟩ := List.mem_map.mp mapped
  subst pair
  have da := (johnson_candidate_list_sound alphabet [] (fun _ => (0:K)) D 0 a ha).1
  have db := (johnson_candidate_list_sound alphabet [] (fun _ => (0:K)) D 0 b hb).1
  exact ⟨by simpa only [da] using Poly.degLt_length a,
    by simpa only [db] using Poly.degLt_length b,of_decide_eq_true close⟩

/-- Completeness is for joint source agreement already established before the
fold challenge. It does not infer joint agreement from one folded candidate. -/
theorem weighted_curve_candidates_complete (alphabet domain : List K)
    (complete : ∀ a,a∈alphabet) (weight : K → Nat) (sourceEven sourceOdd : K → K)
    (D T : Nat) (a b : Poly K) (da : a.DegLt D) (db : b.DegLt D)
    (close : T≤consistencyMass domain weight
      (fun x => sourceEven x=a.eval x ∧ sourceOdd x=b.eval x)) :
    (rateShiftNormalize D a,rateShiftNormalize D b)∈
      weightedCurveCandidates alphabet domain weight sourceEven sourceOdd D T := by
  apply List.mem_filter.mpr
  constructor
  · apply List.mem_flatMap.mpr
    refine ⟨rateShiftNormalize D a,?_,?_⟩
    · exact johnson_candidate_list_complete alphabet [] complete (fun _ => 0) D 0 a da (Nat.zero_le _)
    · apply List.mem_map.mpr
      exact ⟨rateShiftNormalize D b,
        johnson_candidate_list_complete alphabet [] complete (fun _ => 0) D 0 b db (Nat.zero_le _),rfl⟩
  · apply _root_.decide_eq_true
    simpa only [rate_shift_normalize_eval D a da,rate_shift_normalize_eval D b db] using close

theorem weighted_curve_candidates_distinct (alphabet domain : List K) (weight : K → Nat)
    (sourceEven sourceOdd : K → K) (D T : Nat) :
    (weightedCurveCandidates alphabet domain weight sourceEven sourceOdd D T).Pairwise
      (fun a b => ¬(a.1-b.1).IsZero ∨ ¬(a.2-b.2).IsZero) := by
  unfold weightedCurveCandidates
  apply List.Pairwise.filter
  apply List.pairwise_flatMap.mpr
  have distinct := johnson_candidate_list_distinct alphabet [] (fun _ => (0:K)) D 0
  constructor
  · intro a ha
    apply List.pairwise_map.mpr
    exact distinct.imp (fun h => Or.inr h)
  · apply List.Pairwise.imp_of_mem ?_ distinct
    intro a b ha hb ne x hx y hy
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hx
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hy
    exact Or.inl ne

/-- Weighted Johnson size for the constructed family, not a supplied list. -/
theorem weighted_curve_candidates_gap_bound (alphabet domain : List K)
    (distinct : domain.Nodup) (weight : K → Nat) (B D T : Nat)
    (bounded : ∀ x∈domain,weight x≤B) (sourceEven sourceOdd : K → K)
    (gap : (domain.map weight).sum*(B*(D-1))≤T*T) :
    (weightedCurveCandidates alphabet domain weight sourceEven sourceOdd D T).length*
      (T*T-(domain.map weight).sum*(B*(D-1)))≤
      (domain.map weight).sum*(domain.map weight).sum := by
  apply weighted_curve_johnson_gap_bound domain distinct weight B D T bounded
    _ sourceEven sourceOdd
  · intro pair hp
    have h := weighted_curve_candidates_sound alphabet domain weight sourceEven sourceOdd D T pair hp
    exact ⟨h.1,h.2.1⟩
  · intro pair hp
    exact (weighted_curve_candidates_sound alphabet domain weight sourceEven sourceOdd D T pair hp).2.2
  · exact weighted_curve_candidates_distinct alphabet domain weight sourceEven sourceOdd D T
  · exact gap

end NearCompression
