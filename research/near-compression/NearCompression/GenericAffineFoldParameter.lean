import NearCompression.InstructionSumcheckSoundness

/-! Exact change of parameters between affine coefficient folding and
monomial folding. The excluded points and scale are explicit. This does not
establish applicability of a proximity theorem or a Fiat--Shamir theorem. -/
namespace NearCompression
open Lean.Grind ArenaCore.Security
variable {K : Type} [Field K]

def affineFoldParameter (r : K) : K := r/(1-r)
def affineFoldParameterInverse (a : K) : K := a/(1+a)

theorem affine_fold_parameter_exclusion (r : K) (hr : r ≠ 1) :
    affineFoldParameter r ≠ -1 := by
  unfold affineFoldParameter
  grind

theorem affine_fold_inverse_exclusion (a : K) (ha : a ≠ -1) :
    affineFoldParameterInverse a ≠ 1 := by
  unfold affineFoldParameterInverse
  grind

theorem affine_fold_inverse_forward (r : K) (hr : r ≠ 1) :
    affineFoldParameterInverse (affineFoldParameter r)=r := by
  unfold affineFoldParameterInverse affineFoldParameter
  grind

theorem affine_fold_forward_inverse (a : K) (ha : a ≠ -1) :
    affineFoldParameter (affineFoldParameterInverse a)=a := by
  unfold affineFoldParameterInverse affineFoldParameter
  grind

theorem affine_fold_parameter_injective (r s : K) (hr : r ≠ 1) (hs : s ≠ 1)
    (same : affineFoldParameter r=affineFoldParameter s) : r=s := by
  have eq := congrArg affineFoldParameterInverse same
  rw [affine_fold_inverse_forward r hr,affine_fold_inverse_forward s hs] at eq
  exact eq

/-- A literal bijection of punctured fields; no finite-field size is assumed. -/
def affineFoldParameterMap (r : {r : K // r ≠ 1}) : {a : K // a ≠ -1} :=
  ⟨affineFoldParameter r.val,affine_fold_parameter_exclusion r.val r.property⟩

def affineFoldParameterInverseMap (a : {a : K // a ≠ -1}) : {r : K // r ≠ 1} :=
  ⟨affineFoldParameterInverse a.val,affine_fold_inverse_exclusion a.val a.property⟩

theorem affine_fold_subtype_left_inverse (r : {r : K // r ≠ 1}) :
    affineFoldParameterInverseMap (affineFoldParameterMap r)=r := by
  apply Subtype.ext
  exact affine_fold_inverse_forward r.val r.property

theorem affine_fold_subtype_right_inverse (a : {a : K // a ≠ -1}) :
    affineFoldParameterMap (affineFoldParameterInverseMap a)=a := by
  apply Subtype.ext
  exact affine_fold_forward_inverse a.val a.property

theorem affine_fold_monomial_scale (r e o : K) (hr : r ≠ 1) :
    (1-r)*e+r*o=(1-r)*(e+affineFoldParameter r*o) := by
  unfold affineFoldParameter
  grind

theorem affine_fold_scaled_equality (r e o e' o' : K) (hr : r ≠ 1) :
    ((1-r)*e+r*o=(1-r)*e'+r*o') ↔
      e+affineFoldParameter r*o=e'+affineFoldParameter r*o' := by
  rw [affine_fold_monomial_scale r e o hr,affine_fold_monomial_scale r e' o' hr]
  have scale : 1-r ≠ 0 := by grind
  grind

theorem affine_fold_exceptional (e o : K) : (1-(1:K))*e+(1:K)*o=o := by grind

theorem affine_fold_sample_exclusion (sample : List K)
    (excluded : ∀ r ∈ sample, r ≠ 1) :
    ∀ a ∈ sample.map affineFoldParameter, a ≠ -1 := by
  intro a member
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp member
  exact affine_fold_parameter_exclusion r (excluded r hr)

theorem affine_fold_sample_nodup (sample : List K) (distinct : sample.Nodup)
    (excluded : ∀ r ∈ sample, r ≠ 1) : (sample.map affineFoldParameter).Nodup := by
  induction sample with
  | nil => simp
  | cons r rest ih =>
    simp only [List.nodup_cons] at distinct
    simp only [List.map_cons,List.nodup_cons]
    constructor
    · intro member
      obtain ⟨s,hs,same⟩ := List.mem_map.mp member
      have eq := affine_fold_parameter_injective s r
        (excluded s (List.mem_cons_of_mem _ hs)) (excluded r (List.mem_cons_self ..)) same
      exact distinct.1 (eq ▸ hs)
    · exact ih distinct.2 (fun s hs => excluded s (List.mem_cons_of_mem _ hs))

/-- Exact transport of any bad-event predicate across the sample bijection.
The counting identity itself also holds for lists containing repetitions. -/
theorem affine_fold_bad_count_transport (sample : List K) (bad : K → Prop) :
    count sample (fun r => bad (affineFoldParameter r)) =
      count (sample.map affineFoldParameter) bad := by
  classical
  simp only [count,List.countP_map,Function.comp_def]

theorem affine_fold_equality_count_transport (sample : List K)
    (excluded : ∀ r ∈ sample, r ≠ 1) (e o e' o' : K) :
    count sample (fun r => (1-r)*e+r*o=(1-r)*e'+r*o') =
      count (sample.map affineFoldParameter) (fun a => e+a*o=e'+a*o') := by
  classical
  simp only [count,List.countP_map,Function.comp_def]
  apply List.countP_congr
  intro r hr
  simpa only [decide_eq_true_eq] using affine_fold_scaled_equality r e o e' o' (excluded r hr)

end NearCompression
