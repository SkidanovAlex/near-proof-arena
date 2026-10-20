import NearCompression.VectorAffineExtraction
import NearCompression.IndependentQueryBudget

/-! Finite tensor-grid extraction for arbitrary received vector words. A
single joint low-degree polynomial tensor is the parent predicate. A full
challenge tuple is successful when its fully contracted source has an adaptive
low-degree vector candidate. The bound is proved by an explicit recurrence;
there is no assumed decoder, shared curve, or per-coordinate error premise. -/
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K I : Type} [Field K]

def TensorCube : Nat → Type
  | 0 => Unit
  | n+1 => Bool × TensorCube n

def tensorContract (n : Nat) (source : K → TensorCube (n+1) → I → K) (r : K) :
    K → TensorCube n → I → K := fun x b i => (1-r)*source x (false,b) i+r*source x (true,b) i

def tensorEvaluate : (n : Nat) → (K → TensorCube n → I → K) → List K → K → I → K
  | 0,source,_ => fun x i => source x () i
  | _+1,_,[] => fun _ _ => 0
  | n+1,source,r::rs => tensorEvaluate n (tensorContract n source r) rs

noncomputable def tensorRepresentative (domain : List K) (weight : K → Nat)
    (D T n : Nat) (source : K → TensorCube n → I → K) : Prop :=
  ∃ candidate : TensorCube n → I → Poly K,
    (∀ b i,(candidate b i).DegLt D) ∧ T≤consistencyMass domain weight
      (fun x => ∀ b i,source x b i=(candidate b i).eval x)

noncomputable def tensorTerminalSuccess (domain : List K) (weight : K → Nat)
    (D T n : Nat) (source : K → TensorCube n → I → K) (point : List K) : Prop :=
  ∃ candidate : I → Poly K,(∀ i,(candidate i).DegLt D) ∧
    T≤consistencyMass domain weight (fun x => ∀ i,tensorEvaluate n source point x i=(candidate i).eval x)

/-- One coordinate's good-child count is bounded without assuming existence
of a common parent tensor. Extraction constructs that parent if the bound fails. -/
theorem tensor_child_count (domain sample : List K)
    (domainDistinct : domain.Nodup) (sampleDistinct : sample.Nodup)
    (weight : K → Nat) (B D T n : Nat) (bounded : ∀ x∈domain,weight x≤B)
    (source : K → TensorCube (n+1) → I → K)
    (separation : 2*(domain.map weight).sum+B*(D-1)<3*T)
    (noParent : ¬tensorRepresentative domain weight D T (n+1) source) :
    count sample (fun r => tensorRepresentative domain weight D T n (tensorContract n source r))≤max domain.length 2 := by
  classical
  let even : K → (TensorCube n × I) → K := fun x bi => source x (false,bi.1) bi.2
  let odd : K → (TensorCube n × I) → K := fun x bi => source x (true,bi.1) bi.2
  have noPair : ¬∃ p q : (TensorCube n × I) → Poly K,
      (∀ i,(p i).DegLt D ∧ (q i).DegLt D) ∧
      T≤consistencyMass domain weight
        (fun x => ∀ i,even x i=(p i).eval x ∧ odd x i=(q i).eval x) := by
    rintro ⟨p,q,degree,agree⟩
    apply noParent
    let parent : TensorCube (n+1) → I → Poly K := fun bi i => if bi.1 then q (bi.2,i) else p (bi.2,i)
    refine ⟨parent,?_,?_⟩
    · intro bi i
      cases bi with
      | mk bit b => cases bit <;> simp only [parent,Bool.false_eq_true,ite_false,ite_true] <;>
        first | exact (degree (b,i)).1 | exact (degree (b,i)).2
    · apply Nat.le_trans agree
      apply consistency_mass_mono
      intro x hx equal bi i
      cases bi with
      | mk bit b =>
        cases bit with
        | false => simpa [even,parent] using (equal (b,i)).1
        | true => simpa [odd,parent] using (equal (b,i)).2
  have bound := vector_affine_bad_count domain sample domainDistinct sampleDistinct weight B D T bounded
    even odd separation noPair
  apply Nat.le_trans _ bound
  apply count_mono
  intro r h
  obtain ⟨candidate,degree,agree⟩ := h
  refine ⟨(fun bi => candidate bi.1 bi.2),(fun bi => degree bi.1 bi.2),?_⟩
  apply Nat.le_trans agree
  apply consistency_mass_mono
  intro x hx equal bi
  exact (equal bi.1 bi.2).symm

/-- Explicit recurrence: bad first coordinates cost e*|S|^n; every remaining
first coordinate costs at most the n-coordinate bound. -/
def tensorBadBound (sampleSize error : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => error*sampleSize^n+sampleSize*tensorBadBound sampleSize error n

private theorem sum_two_case_bound {A : Type} (xs : List A) (event : A → Prop)
    (value : A → Nat) (large small : Nat)
    (yes : ∀ x∈xs,event x → value x≤large)
    (no : ∀ x∈xs,¬event x → value x≤small) :
    (xs.map value).sum≤count xs event*large+xs.length*small := by
  classical
  induction xs with
  | nil => simp [count]
  | cons x xs ih =>
    have tail := ih (fun y hy => yes y (by simp [hy])) (fun y hy => no y (by simp [hy]))
    have headYes := yes x (by simp)
    have headNo := no x (by simp)
    simp only [List.map_cons,List.sum_cons,count,List.countP_cons,List.length_cons] at tail ⊢
    by_cases h : event x <;> simp_all <;> grind

/-- Far-source tensor extraction with existential adaptive candidates. The
SAME source tensor is fixed before all coordinates. The conclusion does not
assume successful candidates at different points were consistent. -/
theorem tensor_far_success_count (domain sample : List K)
    (domainDistinct : domain.Nodup) (sampleDistinct : sample.Nodup)
    (weight : K → Nat) (B D T : Nat) (bounded : ∀ x∈domain,weight x≤B)
    (separation : 2*(domain.map weight).sum+B*(D-1)<3*T)
    (n : Nat) (source : K → TensorCube n → I → K)
    (noRepresentative : ¬tensorRepresentative domain weight D T n source) :
    count (uniformTuples sample n) (tensorTerminalSuccess domain weight D T n source)≤
      tensorBadBound sample.length (max domain.length 2) n := by
  classical
  induction n with
  | zero =>
    have absent : ¬tensorTerminalSuccess domain weight D T 0 source [] := by
      rintro ⟨candidate,degree,agree⟩
      apply noRepresentative
      refine ⟨(fun _ i => candidate i),(fun _ i => degree i),?_⟩
      apply Nat.le_trans agree
      apply consistency_mass_mono
      intro x hx equal b i
      cases b
      exact equal i
    simp [uniformTuples,count,absent,tensorBadBound]
  | succ n ih =>
    let event : K → Prop := fun r => tensorRepresentative domain weight D T n (tensorContract n source r)
    let value : K → Nat := fun r => count (uniformTuples sample n)
      (tensorTerminalSuccess domain weight D T n (tensorContract n source r))
    have tailBound : ∀ r∈sample,¬event r → value r≤tensorBadBound sample.length (max domain.length 2) n := by
      intro r hr absent
      exact ih (tensorContract n source r) absent
    have maximum : ∀ r∈sample,event r → value r≤sample.length^n := by
      intro r hr he
      have bound : value r≤(uniformTuples sample n).length := List.countP_le_length
      simpa [uniform_tuples_length] using bound
    have total := sum_two_case_bound sample event value (sample.length^n)
      (tensorBadBound sample.length (max domain.length 2) n) maximum tailBound
    have first := tensor_child_count domain sample domainDistinct sampleDistinct weight B D T n bounded
      source separation noRepresentative
    have scaled := Nat.mul_le_mul_right (sample.length^n) first
    have exactCount : count (uniformTuples sample (n+1))
        (tensorTerminalSuccess domain weight D T (n+1) source)=(sample.map value).sum := by
      simp only [uniformTuples,count,List.countP_flatMap,List.countP_map,Function.comp_def]
      rfl
    rw [exactCount]
    unfold tensorBadBound
    change count sample event*sample.length^n≤max domain.length 2*sample.length^n at scaled
    omega

/-- Closed form for the exact recurrence; zero coordinates has zero error. -/
theorem tensor_bad_bound_closed (sampleSize error n : Nat) :
    tensorBadBound sampleSize error n=n*error*sampleSize^(n-1) := by
  induction n with
  | zero => simp [tensorBadBound]
  | succ n ih =>
    rw [tensorBadBound,ih]
    cases n with
    | zero => simp
    | succ n =>
      clear ih
      simp only [Nat.add_sub_cancel,Nat.pow_succ]
      grind

end NearCompression
