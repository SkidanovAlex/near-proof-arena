import NearCompression.WeightedVirtualInitial

/-! A precise obstruction to unconditional joint-tuple extraction for the
actual arbitrary functional-coefficient batching interface. Identical lane
functionals have a common kernel. This does NOT assert a false-statement attack:
the cancelling aggregate has a true zero claim. It refutes deriving joint
source proximity from scalar virtual proximity without another hypothesis. -/
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

/-- Concrete family used by the executable counterexample. -/
def kernelMonomial (D : Nat) : Poly K := Poly.mk (List.replicate D 0 ++ [1])

theorem kernel_monomial_degree (D : Nat) : (kernelMonomial (K:=K) D).DegLt (D+1) := by
  simpa [kernelMonomial] using Poly.degLt_length (kernelMonomial (K:=K) D)

theorem kernel_monomial_leading (D : Nat) : (kernelMonomial (K:=K) D).coeff D=1 := by
  simp [kernelMonomial,Poly.coeff,List.getD]

/-- Identical lane functionals can occur for every reduction challenge u.
No value or distribution of their shared coefficient repairs cancellation. -/
theorem structured_batch_kernel (beta : K) (source : K → K) (x : K) :
    weightedVirtualOracle [beta,beta] [source,fun y => -(source y)] x=0 := by
  simp only [weightedVirtualOracle,List.map_cons,List.map_nil,weightedLaneValues]
  grind

/-- A degree-D received oracle is far from every degree-strictly-less-than-D
candidate. Distinct domain points are essential. -/
theorem exact_degree_far_from_lower (domain : List K) (distinct : domain.Nodup)
    (h p : Poly K) (D : Nat) (hDegree : h.DegLt (D+1)) (leading : h.coeff D≠0)
    (pDegree : p.DegLt D) :
    domain.length≤D+finiteRSMismatches domain h.eval p.eval := by
  have different : ¬(h-p).IsZero := by
    intro zero
    have atD := zero D
    rw [Poly.coeff_sub,pDegree D (Nat.le_refl _)] at atD
    apply leading
    grind
  have pBound : p.DegLt (D+1) := fun i hi => pDegree i (by omega)
  have distance := finite_rs_minimum_distance domain distinct h p (D+1) hDegree pBound different
  omega

/-- The two cancelling lanes can be jointly far from EVERY low-degree tuple.
One high-degree lane already suffices to lower-bound joint mismatch. -/
theorem structured_kernel_joint_distance (domain : List K) (distinct : domain.Nodup)
    (h p q : Poly K) (D : Nat) (hDegree : h.DegLt (D+1)) (leading : h.coeff D≠0)
    (pDegree : p.DegLt D) :
    domain.length≤D+count domain
      (jointLaneMismatch [h.eval,fun x => -(h.eval x)] [p,q]) := by
  have distance := exact_degree_far_from_lower domain distinct h p D hDegree leading pDegree
  have subset : finiteRSMismatches domain h.eval p.eval≤count domain
      (jointLaneMismatch [h.eval,fun x => -(h.eval x)] [p,q]) := by
    apply count_mono
    intro x mismatch same
    apply mismatch
    exact (List.cons.inj same).1
  omega

theorem structured_kernel_no_joint_tuple (domain : List K) (distinct : domain.Nodup)
    (h : Poly K) (D R : Nat) (hDegree : h.DegLt (D+1)) (leading : h.coeff D≠0)
    (radius : D+R<domain.length) :
    ¬∃ p q : Poly K,p.DegLt D ∧ q.DegLt D ∧ count domain
      (jointLaneMismatch [h.eval,fun x => -(h.eval x)] [p,q])≤R := by
  rintro ⟨p,q,hp,hq,close⟩
  have distance := structured_kernel_joint_distance domain distinct h p q D hDegree leading hp
  omega

/-- Nevertheless, at EVERY shared coefficient the scalar oracle has a degree
<D candidate with exact full-domain agreement and zero residual for any weights.
This rules out an unconditional far-joint-source => far-virtual-source claim. -/
theorem structured_kernel_exact_scalar_candidate (domain : List K) (beta : K)
    (source : K → K) (weights : List K) (D : Nat) :
    ∃ p : Poly K,p.DegLt D ∧ scalarRSResidual weights p=0 ∧
      count domain (fun x => weightedVirtualOracle [beta,beta] [source,fun y => -(source y)] x=p.eval x)=domain.length := by
  refine ⟨Poly.zero,?_,?_,?_⟩
  · intro i hi
    simp [Poly.coeff,Poly.zero]
  · unfold scalarRSResidual
    generalize 0=offset
    induction weights generalizing offset with
    | nil => rfl
    | cons w ws ih =>
      change w*Poly.zero.coeff offset+scalarRSResidualFrom Poly.zero (offset+1) ws=0
      rw [ih]
      simp only [Poly.coeff,Poly.zero,List.getD_nil]
      grind
  · classical
    simp [count,structured_batch_kernel,Poly.eval_zero]

end NearCompression
