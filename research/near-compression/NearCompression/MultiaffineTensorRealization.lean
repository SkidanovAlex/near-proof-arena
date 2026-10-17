import NearCompression.GKRWeightCoordinateDegree
import NearCompression.VectorTensorExtraction

namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

def tensorCubeValues : (n : Nat) → TensorCube n → List K
  | 0,_ => []
  | n+1,(bit,rest) => (if bit then 1 else 0)::tensorCubeValues n rest

theorem tensor_cube_values_length (n : Nat) (b : TensorCube n) :
    (tensorCubeValues (K:=K) n b).length=n := by
  induction n with
  | zero => rfl
  | succ n ih => cases b with | mk bit rest => simp [tensorCubeValues,ih]

def ListMultiaffine (n : Nat) (f : List K → K) : Prop :=
  ∀ pre suffix,pre.length+1+suffix.length=n → ∀ r,
    f (pre++r::suffix)=(1-r)*f (pre++0::suffix)+r*f (pre++1::suffix)

/-- Exact Boolean tensor realization, proved from coordinate identities.
The scalar function may depend on a fixed arbitrary received oracle at x. -/
theorem multiaffine_tensor_realization (n : Nat) (f : K → List K → K)
    (affine : ∀ x,ListMultiaffine n (f x))
    (point : List K) (shape : point.length=n) (x : K) :
    tensorEvaluate n (fun y b (_ : Unit) => f y (tensorCubeValues n b)) point x ()=f x point := by
  induction n generalizing f point with
  | zero =>
    have empty : point=[] := List.eq_nil_of_length_eq_zero shape
    subst point
    rfl
  | succ n ih =>
    cases point with
    | nil => simp at shape
    | cons r rest =>
      have tail : rest.length=n := by simpa using shape
      have next : ∀ y,ListMultiaffine n (fun ps => f y (r::ps)) := by
        intro y pre suffix length t
        have h := affine y (r::pre) suffix (by simp; omega) t
        exact h
      have contract : tensorContract n (fun y b (_ : Unit) => f y (tensorCubeValues (n+1) b)) r=
          (fun y b (_ : Unit) => f y (r::tensorCubeValues n b)) := by
        funext y b uidx
        have h := affine y [] (tensorCubeValues n b) (by simp [tensor_cube_values_length,Nat.add_comm]) r
        simpa only [tensorContract,tensorCubeValues,List.nil_append,Bool.false_eq_true,ite_false,ite_true] using h.symm
      rw [tensorEvaluate,contract]
      exact ih (fun y ps => f y (r::ps)) next rest tail

/-- Updating one list coordinate has exactly the point-update semantics used
by the concrete GKR coordinate-degree certificates. -/
theorem gkr_list_insert_coordinate (pre suffix : List K) (old r : K) :
    gkrSetCoordinate (fun i => (pre++old::suffix).getD i 0) pre.length r=
      (fun i => (pre++r::suffix).getD i 0) := by
  funext i
  induction pre generalizing i with
  | nil => cases i <;> simp [gkrSetCoordinate]
  | cons a pre ih =>
    cases i with
    | zero => simp [gkrSetCoordinate]
    | succ i => simpa [gkrSetCoordinate,List.getD_cons_succ] using ih i

/-- A fixed-dimensional coordinate-affine point function realizes a list
multiaffine family without assuming its Boolean interpolation is correct. -/
theorem point_affine_list_multiaffine (n : Nat) (f : (Nat → K) → K)
    (affine : ∀ point coordinate,coordinate<n → ∀ r,
      f (gkrSetCoordinate point coordinate r)=
        (1-r)*f (gkrSetCoordinate point coordinate 0)+r*f (gkrSetCoordinate point coordinate 1)) :
    ListMultiaffine n (fun ps => f (fun i => ps.getD i 0)) := by
  intro pre suffix length r
  have h := affine (fun i => (pre++(0:K)::suffix).getD i 0) pre.length (by omega) r
  simp only [gkr_list_insert_coordinate] at h
  exact h

/-- Candidate event for the concrete scalar function is literally the tensor
terminal event. Candidates may be adaptive, but f itself precedes sampling. -/
theorem multiaffine_candidate_far_count (domain sample : List K)
    (domainDistinct : domain.Nodup) (sampleDistinct : sample.Nodup)
    (weight : K → Nat) (B D T n : Nat) (bounded : ∀ x∈domain,weight x≤B)
    (separation : 2*(domain.map weight).sum+B*(D-1)<3*T)
    (f : K → List K → K) (affine : ∀ x,ListMultiaffine n (f x))
    (far : ¬tensorRepresentative domain weight D T n
      (fun x b (_ : Unit) => f x (tensorCubeValues n b))) :
    count (uniformTuples sample n) (fun point => ∃ candidate : Poly K,
      candidate.DegLt D ∧ T≤consistencyMass domain weight (fun x => f x point=candidate.eval x)) ≤
      n*max domain.length 2*sample.length^(n-1) := by
  classical
  have bound := tensor_far_success_count domain sample domainDistinct sampleDistinct weight B D T
    bounded separation n (fun x b (_ : Unit) => f x (tensorCubeValues n b)) far
  rw [tensor_bad_bound_closed] at bound
  apply Nat.le_trans _ bound
  apply count_mono_mem
  intro point member accepted
  obtain ⟨candidate,degree,agree⟩ := accepted
  refine ⟨(fun _ => candidate),(fun _ => degree),?_⟩
  apply Nat.le_trans agree
  apply consistency_mass_mono
  intro x hx equal uidx
  cases uidx
  rw [multiaffine_tensor_realization n f affine point ?_ x]
  · exact equal
  · have lengths : ∀ d : Nat,∀ ps∈uniformTuples sample d,ps.length=d := by
      intro d
      induction d with
      | zero => simp [uniformTuples]
      | succ d ih =>
        intro ps hp
        simp only [uniformTuples,List.mem_flatMap,List.mem_map] at hp
        obtain ⟨r,hr,tail,ht,rfl⟩ := hp
        simp [ih tail ht]
    exact lengths n point member

end NearCompression
