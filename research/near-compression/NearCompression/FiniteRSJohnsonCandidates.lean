import NearCompression.FiniteRSJohnsonList
import NearCompression.RateShiftContinuationCandidate
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]
attribute [local instance] Classical.propDecidable

private noncomputable def distinctList {A : Type} : List A→List A
  | []=>[]
  | a::rest=>if a∈rest then distinctList rest else a::distinctList rest

private theorem distinct_mem {A : Type} (xs : List A) (a : A) : a∈distinctList xs ↔ a∈xs := by
  classical
  induction xs with
  | nil=>simp [distinctList]
  | cons b rest ih=>
    simp only [distinctList]
    split <;> simp_all

private theorem distinct_nodup {A : Type} (xs : List A) : (distinctList xs).Nodup := by
  classical
  induction xs with
  | nil=>simp [distinctList]
  | cons a rest ih=>
    simp only [distinctList]
    split
    · exact ih
    · simp_all [List.nodup_cons,distinct_mem]

private theorem tuple_length {A : Type} (alphabet : List A) (n : Nat) :
    ∀ xs∈uniformTuples alphabet n,xs.length=n := by
  induction n with
  | zero=>intro xs hx;simpa [uniformTuples] using hx
  | succ n ih=>
    intro xs hx
    simp only [uniformTuples,List.mem_flatMap,List.mem_map] at hx
    obtain ⟨a,ha,rest,hr,rfl⟩:=hx
    simp [ih rest hr]

private theorem tuple_complete {A : Type} (alphabet : List A) (complete : ∀ a,a∈alphabet) (xs : List A) :
    xs∈uniformTuples alphabet xs.length := by
  induction xs with
  | nil=>simp [uniformTuples]
  | cons a rest ih=>
    simp only [List.length_cons,uniformTuples,List.mem_flatMap,List.mem_map]
    exact ⟨a,complete a,rest,ih,rfl⟩

/-- Exhaustive mathematical list, fixed before challenges. This is not an
algorithm proposed for the prover: enumeration has |alphabet|^D entries. -/
noncomputable def johnsonCandidateList (alphabet domain : List K) (received : K→K) (D T : Nat) : List (Poly K) := by
  classical
  exact distinctList (((uniformTuples alphabet D).map Poly.mk).filter
    (fun p=>decide (T≤count domain (fun x=>p.eval x=received x))))

theorem johnson_candidate_list_sound (alphabet domain : List K) (received : K→K) (D T : Nat)
    (p : Poly K) (member : p∈johnsonCandidateList alphabet domain received D T) :
    p.coeffs.length=D ∧ T≤count domain (fun x=>p.eval x=received x) := by
  classical
  unfold johnsonCandidateList at member
  rw [distinct_mem] at member
  obtain ⟨mapped,close⟩:=List.mem_filter.mp member
  obtain ⟨cs,hcs,equal⟩:=List.mem_map.mp mapped
  subst p
  exact ⟨tuple_length alphabet D cs hcs,of_decide_eq_true close⟩

/-- All degree-bounded candidates appear after canonical padding. The list
has no dependence on the challenge or a postchallenge selected candidate. -/
theorem johnson_candidate_list_complete (alphabet domain : List K) (complete : ∀ a,a∈alphabet)
    (received : K→K) (D T : Nat) (p : Poly K) (degree : p.DegLt D)
    (close : T≤count domain (fun x=>p.eval x=received x)) :
    rateShiftNormalize D p∈johnsonCandidateList alphabet domain received D T := by
  classical
  unfold johnsonCandidateList
  rw [distinct_mem]
  apply List.mem_filter.mpr
  constructor
  · apply List.mem_map.mpr
    refine ⟨(rateShiftNormalize D p).coeffs,?_,rfl⟩
    have mem:=tuple_complete alphabet complete (rateShiftNormalize D p).coeffs
    simpa only [rate_shift_normalize_length] using mem
  · apply _root_.decide_eq_true
    simpa only [rate_shift_normalize_eval D p degree] using close

private theorem normalized_equal (a b : Poly K) (D : Nat)
    (ha : a.coeffs.length=D) (hb : b.coeffs.length=D) (zero : (a-b).IsZero) : a=b := by
  have coeffs : a.coeffs=b.coeffs := by
    apply List.ext_getElem (ha.trans hb.symm)
    intro i hi hj
    have h:=zero i
    change (a-b).coeff i=0 at h
    rw [Poly.coeff_sub,Poly.coeff_def,Poly.coeff_def] at h
    simp only [List.getD,List.getElem?_eq_getElem hi,List.getElem?_eq_getElem hj,Option.getD_some] at h
    grind
  cases a;cases b
  simp_all

theorem johnson_candidate_list_distinct (alphabet domain : List K) (received : K→K) (D T : Nat) :
    (johnsonCandidateList alphabet domain received D T).Pairwise (fun a b=>¬(a-b).IsZero) := by
  classical
  have unique : (johnsonCandidateList alphabet domain received D T).Nodup := distinct_nodup _
  apply List.Pairwise.imp_of_mem ?_ (List.nodup_iff_pairwise_ne.mp unique)
  intro a b ha hb different zero
  exact different (normalized_equal a b D
    (johnson_candidate_list_sound alphabet domain received D T a ha).1
    (johnson_candidate_list_sound alphabet domain received D T b hb).1 zero)

/-- Explicit size bound for the constructed list, not a supplied family.
Completeness additionally uses the field alphabet covering every element. -/
theorem johnson_candidate_list_gap_bound (alphabet domain : List K) (distinct : domain.Nodup)
    (received : K→K) (D T : Nat) (gap : domain.length*(D-1)≤T*T) :
    (johnsonCandidateList alphabet domain received D T).length*(T*T-domain.length*(D-1))≤
      domain.length*domain.length := by
  apply finite_rs_johnson_gap_bound domain distinct _ received D T
  · intro p hp
    have shape:=(johnson_candidate_list_sound alphabet domain received D T p hp).1
    simpa only [shape] using Poly.degLt_length p
  · intro p hp
    exact (johnson_candidate_list_sound alphabet domain received D T p hp).2
  · exact johnson_candidate_list_distinct alphabet domain received D T
  · exact gap
end NearCompression
