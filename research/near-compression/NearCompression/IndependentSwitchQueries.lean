import NearCompression.IndependentMixingContinuation
import NearCompression.RateShiftQueryTransfer

/-! Joint source-query / independent-mixing experiment. The child candidate
family and folded source oracle precede queries. Source no-close transfer and
continuation extraction remain external. -/
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

def switchQueryTemplates {I : Type} (point source : I→K) (z y : K) (queries : List I) : List (K × K) :=
  (z,y)::queries.map (fun i=>(point i,source i))

/-- A candidate with no false injected constraint satisfies the old claim
and every sampled source equation. The OOD equation is retained as well. -/
theorem switch_query_unmixed {I : Type} (point source : I→K) (z y claim : K)
    (queries : List I) (xs : List (K × K))
    (correct : ¬SwitchCandidateWrong xs claim (switchQueryTemplates point source z y queries)) :
    affineFoldDot xs=claim ∧ (Poly.mk (xs.map Prod.fst)).eval z=y ∧
      allQueriesPass (fun i=>(Poly.mk (xs.map Prod.fst)).eval (point i)=source i) queries := by
  have old : affineFoldDot xs=claim := by
    apply Classical.byContradiction
    intro h
    exact correct (Or.inl h)
  have equations : ∀ e∈switchQueryTemplates point source z y queries,
      (Poly.mk (xs.map Prod.fst)).eval e.1=e.2 := by
    intro e he
    apply Classical.byContradiction
    intro h
    exact correct (Or.inr ⟨e,he,Ne.symm h⟩)
  refine ⟨old,equations (z,y) (by simp [switchQueryTemplates]),?_⟩
  intro i hi
  exact equations (point i,source i) (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨i,hi,rfl⟩))

/-- Source-query failure event for a fixed candidate family, with no
assumption on the OOD point location. -/
theorem switch_query_correct_family_count {I : Type} (seeds : List I) (q T : Nat)
    (family : List (List (K × K))) (point source : I→K) (z y claim : K)
    (noClose : ∀ xs∈family,affineFoldDot xs=claim→
      count seeds (fun i=>(Poly.mk (xs.map Prod.fst)).eval (point i)=source i)<T) :
    count (uniformTuples seeds q) (fun qs=>∃ xs∈family,
      ¬SwitchCandidateWrong xs claim (switchQueryTemplates point source z y qs))≤
      family.length*(T-1)^q := by
  apply finite_candidate_union_count
  intro xs hx
  classical
  by_cases old : affineFoldDot xs=claim
  · have few:=noClose xs hx old
    have subset : count (uniformTuples seeds q)
        (fun qs=>¬SwitchCandidateWrong xs claim (switchQueryTemplates point source z y qs))≤
        count (uniformTuples seeds q)
          (allQueriesPass (fun i=>(Poly.mk (xs.map Prod.fst)).eval (point i)=source i)) := by
      apply count_mono
      intro qs h
      exact (switch_query_unmixed point source z y claim qs xs h).2.2
    rw [independent_query_count] at subset
    exact Nat.le_trans subset (Nat.pow_le_pow_left (by omega) q)
  · have empty : count (uniformTuples seeds q)
        (fun qs=>¬SwitchCandidateWrong xs claim (switchQueryTemplates point source z y qs))≤
        count (uniformTuples seeds q) (fun _=>False) := by
      apply count_mono
      intro qs h
      exact old (switch_query_unmixed point source z y claim qs xs h).1
    simpa [count] using Nat.le_trans empty (show count (uniformTuples seeds q) (fun _=>False)≤(T-1)^q by simp [count])

private theorem tuple_length {A : Type} (sample : List A) (n : Nat) :
    ∀ xs∈uniformTuples sample n,xs.length=n := by
  induction n with
  | zero => intro xs hx;simpa [uniformTuples] using hx
  | succ n ih =>
    intro xs hx
    simp only [uniformTuples,List.mem_flatMap,List.mem_map] at hx
    obtain ⟨a,ha,rest,hr,rfl⟩:=hx
    simp [ih rest hr]

private theorem conditional_sum {A B : Type} (outer : List A) (inner : List B)
    (bad : A→Prop) (accept : A→B→Prop) (limit : Nat)
    (good : ∀ a∈outer,¬bad a→count inner (accept a)≤limit) :
    (outer.map (fun a=>count inner (accept a))).sum≤
      count outer bad*inner.length+outer.length*limit := by
  classical
  induction outer with
  | nil => simp [count]
  | cons a rest ih =>
    have tail:=ih (fun b hb=>good b (by simp [hb]))
    have head:=good a (by simp)
    have maximum : count inner (accept a)≤inner.length := List.countP_le_length
    simp only [List.map_cons,List.sum_cons,count,List.countP_cons,List.length_cons] at tail head ⊢
    by_cases h : bad a <;> simp_all <;> grind

/-- Exact joint query-then-mixer experiment. After division by the experiment
size (when nonzero), the bound is L*((T-1)/|seeds|)^q + L/|sample|.
Selection can depend on both draws but stays inside a prequery fixed family.
This proves neither source no-close nor extraction from a child commitment. -/
theorem switch_query_mixing_joint_count {I : Type} (seeds : List I) (q T : Nat)
    (family : List (List (K × K))) (point source : I→K) (z y claim : K)
    (sample : List K) (distinct : sample.Nodup)
    (noClose : ∀ xs∈family,affineFoldDot xs=claim→
      count seeds (fun i=>(Poly.mk (xs.map Prod.fst)).eval (point i)=source i)<T) :
    count ((uniformTuples seeds q).flatMap (fun qs=>
      (uniformTuples sample (q+1)).map (fun rs=>(qs,rs))))
      (fun pair=>∃ xs∈family,
        SwitchMixedAccept xs claim (switchQueryTemplates point source z y pair.1) pair.2)≤
      family.length*(T-1)^q*sample.length^(q+1)+
        seeds.length^q*(family.length*sample.length^q) := by
  classical
  let outer:=uniformTuples seeds q
  let inner:=uniformTuples sample (q+1)
  let bad:=fun qs=>∃ xs∈family,¬SwitchCandidateWrong xs claim (switchQueryTemplates point source z y qs)
  let accept:=fun qs rs=>∃ xs∈family,SwitchMixedAccept xs claim (switchQueryTemplates point source z y qs) rs
  have good : ∀ qs∈outer,¬bad qs→count inner (accept qs)≤family.length*sample.length^q := by
    intro qs hqs notBad
    have len:=tuple_length seeds q qs hqs
    have shape : (switchQueryTemplates point source z y qs).length=q+1 := by simp [switchQueryTemplates,len]
    have mixing:=switch_candidate_family_mixing_count family claim
      (switchQueryTemplates point source z y qs) sample distinct
    rw [shape] at mixing
    apply Nat.le_trans ?_ (by simpa using mixing)
    apply count_mono
    intro rs h
    obtain ⟨xs,hx,accepted⟩:=h
    have wrong : SwitchCandidateWrong xs claim (switchQueryTemplates point source z y qs) := by
      apply Classical.byContradiction
      intro correct
      exact notBad ⟨xs,hx,correct⟩
    exact ⟨xs,hx,wrong,accepted⟩
  have total:=conditional_sum outer inner bad accept _ good
  have queries:=switch_query_correct_family_count seeds q T family point source z y claim noClose
  have scaled:=Nat.mul_le_mul_right inner.length queries
  have olen : outer.length=seeds.length^q := uniform_tuples_length seeds q
  have ilen : inner.length=sample.length^(q+1) := uniform_tuples_length sample (q+1)
  have bound : (outer.map (fun qs=>count inner (accept qs))).sum≤
      family.length*(T-1)^q*sample.length^(q+1)+seeds.length^q*(family.length*sample.length^q) := by
    change count outer bad*inner.length≤_ at scaled
    rw [olen,ilen] at total
    rw [ilen] at scaled
    omega
  simpa only [count,List.countP_flatMap,List.countP_map,Function.comp_def,outer,inner,accept] using bound
end NearCompression
