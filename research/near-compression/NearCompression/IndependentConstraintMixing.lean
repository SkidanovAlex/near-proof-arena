import NearCompression.CodeSwitchFunctional
import NearCompression.IndependentQueryBudget
import NearCompression.FiniteBatchCandidates

/-! Sharp counting bound for independently sampled constraint mixers.
All residual coefficients are fixed before the mixer tuple is drawn. -/
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

def switchLinearResidual : List K → List K → K
  | d::ds,r::rs => r*d+switchLinearResidual ds rs
  | _,_ => 0

private theorem nat_sum_add {A : Type} (xs : List A) (f g : A→Nat) :
    (xs.map (fun x=>f x+g x)).sum=(xs.map f).sum+(xs.map g).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons,List.sum_cons,ih];omega

private theorem nat_sum_const {A : Type} (xs : List A) (n : Nat) :
    (xs.map (fun _=>n)).sum=xs.length*n := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons,List.sum_cons,List.length_cons,ih];grind

private theorem nat_sum_swap {A B : Type} (xs : List A) (ys : List B) (f : A→B→Nat) :
    (xs.map (fun x=>(ys.map (f x)).sum)).sum=
      (ys.map (fun y=>(xs.map (fun x=>f x y)).sum)).sum := by
  induction xs with
  | nil => simp only [List.map_nil,List.sum_nil];rw [nat_sum_const];simp
  | cons x xs ih =>
    simp only [List.map_cons,List.sum_cons]
    rw [nat_sum_add,ih]

private theorem count_as_sum {A : Type} (xs : List A) (event : A→Prop) [DecidablePred event] :
    count xs event=(xs.map (fun x=>if event x then 1 else 0)).sum := by
  classical
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [count,List.countP_cons,List.map_cons,List.sum_cons] at ih ⊢
    by_cases h : event x <;> simp_all <;> omega

private theorem nat_sum_bound {A : Type} (xs : List A) (f : A→Nat) (limit : Nat)
    (bound : ∀ x∈xs,f x≤limit) : (xs.map f).sum≤xs.length*limit := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have head:=bound x (List.mem_cons_self ..)
    have tail:=ih (fun y hy=>bound y (List.mem_cons_of_mem _ hy))
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    grind

private theorem unique_count {A : Type} (sample : List A) (distinct : sample.Nodup)
    (event : A→Prop) (unique : ∀ a∈sample,∀ b∈sample,event a→event b→a=b) :
    count sample event≤1 := by
  classical
  induction sample with
  | nil => simp [count]
  | cons a rest ih =>
    have nd:=List.nodup_cons.mp distinct
    by_cases ha : event a
    · have empty : count rest event=0 := by
        have h : count rest event≤count rest (fun _=>False) := by
          apply count_mono_mem
          intro b hb he
          have same:=unique a (by simp) b (by simp [hb]) ha he
          exact nd.1 (same ▸ hb)
        simpa [count] using h
      simp only [count,List.countP_cons] at empty ⊢
      simp only [ha,decide_true,ite_true]
      omega
    · have h:=ih nd.2 (fun b hb c hc=>unique b (by simp [hb]) c (by simp [hc]))
      simpa [count,List.countP_cons,ha] using h

/-- One wrong residual anywhere in the vector costs at most1/|sample| under
independent uniform draws, rather than the power-batching degree/|sample|.
The statement counts finite experiments and includes an empty sample. -/
theorem switch_independent_mixing_count (sample : List K) (distinct : sample.Nodup)
    (deltas : List K) (wrong : ∃ d∈deltas,d≠0) (offset : K) :
    count (uniformTuples sample deltas.length)
      (fun mixers=>offset+switchLinearResidual deltas mixers=0)≤sample.length^(deltas.length-1) := by
  classical
  induction deltas generalizing offset with
  | nil => simp at wrong
  | cons d ds ih =>
    simp only [List.length_cons,uniformTuples,count,List.countP_flatMap,List.countP_map,Function.comp_def,switchLinearResidual]
    change (sample.map (fun r=>count (uniformTuples sample ds.length)
      (fun rs=>offset+(r*d+switchLinearResidual ds rs)=0))).sum≤sample.length^ds.length
    by_cases hd : d=0
    · have tailWrong : ∃ e∈ds,e≠0 := by simpa [hd] using wrong
      have nonempty : 0<ds.length := by cases ds <;> simp_all
      have bound : ∀ r∈sample,count (uniformTuples sample ds.length)
          (fun rs=>offset+(r*d+switchLinearResidual ds rs)=0)≤sample.length^(ds.length-1) := by
        intro r hr
        have same : (fun rs=>offset+(r*d+switchLinearResidual ds rs)=0)=
            (fun rs=>offset+switchLinearResidual ds rs=0) := by funext rs;rw [hd];apply propext;grind
        rw [same]
        exact ih tailWrong offset
      have total:=nat_sum_bound sample _ _ bound
      have power : sample.length*sample.length^(ds.length-1)=sample.length^ds.length := by
        rw [←Nat.pow_succ'];congr 1;omega
      exact power ▸ total
    · simp only [count_as_sum]
      rw [nat_sum_swap]
      have bound : ∀ rs∈uniformTuples sample ds.length,
          (sample.map (fun r=>if offset+(r*d+switchLinearResidual ds rs)=0 then 1 else 0)).sum≤1 := by
        intro rs hrs
        rw [←count_as_sum]
        apply unique_count sample distinct
        intro a ha b hb ea eb
        grind
      have total:=nat_sum_bound (uniformTuples sample ds.length) _ 1 bound
      simpa [uniform_tuples_length] using total

/-- Templates are fixed (point,answer) pairs; mixers are sampled separately. -/
def switchBindConstraints : List (K × K) → List K → List (SwitchConstraint K)
  | (point,answer)::rest,r::rs => ⟨point,answer,r⟩::switchBindConstraints rest rs
  | _,_ => []

def switchTemplateDeltas (cs : List K) (templates : List (K × K)) : List K :=
  templates.map (fun e=>(Poly.mk cs).eval e.1-e.2)

theorem switch_bound_residual (cs : List K) (templates : List (K × K)) (mixers : List K) :
    switchResidualSum cs (switchBindConstraints templates mixers)=
      switchLinearResidual (switchTemplateDeltas cs templates) mixers := by
  induction templates generalizing mixers with
  | nil => cases mixers <;> rfl
  | cons e rest ih =>
    cases mixers with
    | nil => rfl
    | cons r rs => simp only [switchBindConstraints,switchResidualSum,switchTemplateDeltas,List.map_cons,switchLinearResidual];rw [ih];rfl

theorem switch_injection_tuple_residual (xs : List (K × K)) (claim : K)
    (templates : List (K × K)) (mixers : List K) :
    affineFoldDot (switchInjectAll xs claim (switchBindConstraints templates mixers)).1-
      (switchInjectAll xs claim (switchBindConstraints templates mixers)).2=
      affineFoldDot xs-claim+switchLinearResidual (switchTemplateDeltas (xs.map Prod.fst) templates) mixers := by
  rw [switch_inject_all_residual,switch_bound_residual]

private theorem linear_all_zero (ds rs : List K) (zero : ∀ d∈ds,d=0) :
    switchLinearResidual ds rs=0 := by
  induction ds generalizing rs with
  | nil => cases rs <;> rfl
  | cons d ds ih =>
    cases rs with
    | nil => rfl
    | cons r rs =>
      have hd:=zero d (List.mem_cons_self ..)
      have tail:=ih rs (fun e he=>zero e (List.mem_cons_of_mem _ he))
      simp only [switchLinearResidual,hd,tail];grind

def SwitchCandidateWrong (xs : List (K × K)) (claim : K) (templates : List (K × K)) : Prop :=
  affineFoldDot xs≠claim ∨ ∃ e∈templates,e.2≠(Poly.mk (xs.map Prod.fst)).eval e.1

def SwitchMixedAccept (xs : List (K × K)) (claim : K)
    (templates : List (K × K)) (mixers : List K) : Prop :=
  affineFoldDot (switchInjectAll xs claim (switchBindConstraints templates mixers)).1=
    (switchInjectAll xs claim (switchBindConstraints templates mixers)).2

/-- Actual injection acceptance for a fixed false candidate, under ideal
independent sampling. The prior claim may also be false. -/
theorem switch_fixed_candidate_mixing_count (xs : List (K × K)) (claim : K)
    (templates : List (K × K)) (sample : List K) (distinct : sample.Nodup)
    (wrong : SwitchCandidateWrong xs claim templates) :
    count (uniformTuples sample templates.length) (SwitchMixedAccept xs claim templates)≤
      sample.length^(templates.length-1) := by
  classical
  let ds:=switchTemplateDeltas (xs.map Prod.fst) templates
  have accepted : ∀ rs,SwitchMixedAccept xs claim templates rs→affineFoldDot xs-claim+switchLinearResidual ds rs=0 := by
    intro rs accept
    have identity:=switch_injection_tuple_residual xs claim templates rs
    change affineFoldDot (switchInjectAll xs claim (switchBindConstraints templates rs)).1=
      (switchInjectAll xs claim (switchBindConstraints templates rs)).2 at accept
    rw [accept] at identity
    dsimp only [ds]
    grind
  by_cases nonzero : ∃ d∈ds,d≠0
  · have bound:=switch_independent_mixing_count sample distinct ds nonzero (affineFoldDot xs-claim)
    have shape : ds.length=templates.length := by simp [ds,switchTemplateDeltas]
    rw [shape] at bound
    apply Nat.le_trans ?_ bound
    apply count_mono
    exact accepted
  · have zero : ∀ d∈ds,d=0 := by grind
    have oldWrong : affineFoldDot xs≠claim := by
      rcases wrong with old | ⟨e,he,err⟩
      · exact old
      · have dz:=zero ((Poly.mk (xs.map Prod.fst)).eval e.1-e.2) (List.mem_map.mpr ⟨e,he,rfl⟩)
        grind
    have empty : count (uniformTuples sample templates.length) (SwitchMixedAccept xs claim templates)≤
        count (uniformTuples sample templates.length) (fun _=>False) := by
      apply count_mono
      intro rs accept
      have h:=accepted rs accept
      rw [linear_all_zero ds rs zero] at h
      grind
    simpa [count] using Nat.le_trans empty (show count (uniformTuples sample templates.length) (fun _=>False)≤sample.length^(templates.length-1) by simp [count])

/-- Candidate selection may depend on mixers, but only inside this fixed
prechallenge family. Obtaining and bounding that family is still external. -/
theorem switch_candidate_family_mixing_count (family : List (List (K × K))) (claim : K)
    (templates : List (K × K)) (sample : List K) (distinct : sample.Nodup) :
    count (uniformTuples sample templates.length) (fun mixers=>∃ xs∈family,
      SwitchCandidateWrong xs claim templates ∧ SwitchMixedAccept xs claim templates mixers)≤
      family.length*sample.length^(templates.length-1) := by
  apply finite_candidate_union_count
  intro xs hx
  classical
  by_cases wrong : SwitchCandidateWrong xs claim templates
  · apply Nat.le_trans ?_ (switch_fixed_candidate_mixing_count xs claim templates sample distinct wrong)
    apply count_mono
    intro rs h
    exact h.2
  · simp [wrong,count]
/-- Denominator-free form of the L/|sample| bound for a nonempty list of
constraints. It assumes a fixed family and ideal independent draws only. -/
theorem switch_candidate_family_mixing_scaled (family : List (List (K × K))) (claim : K)
    (templates : List (K × K)) (sample : List K) (distinct : sample.Nodup)
    (nonempty : 0<templates.length) :
    count (uniformTuples sample templates.length) (fun mixers=>∃ xs∈family,
      SwitchCandidateWrong xs claim templates ∧ SwitchMixedAccept xs claim templates mixers)*sample.length≤
      family.length*sample.length^templates.length := by
  have bound:=Nat.mul_le_mul_right sample.length
    (switch_candidate_family_mixing_count family claim templates sample distinct)
  have power : sample.length^(templates.length-1)*sample.length=sample.length^templates.length := by
    rw [←Nat.pow_succ];congr 1;omega
  simpa only [Nat.mul_assoc,power] using bound
end NearCompression
