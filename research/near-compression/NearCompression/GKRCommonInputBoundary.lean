import NearCompression.DualMobiusWeights
import NearCompression.GenericPackedClaimAuthentication

/-! The final GKR obligation is eq(ru) + gamma*eq(rv) against ONE fixed input
vector. The separation lemma does not extract this vector from a commitment.
The adaptive example demonstrates why moving the vector existential after the
challenge changes the statement; it is not an attack against the PCS. -/
namespace NearCompression
open Lean.Grind
variable {K : Type} [Field K]

def gkrInputFunctional (m : Nat) (left right : Nat → K) (gamma : K)
    (values : Nat → K) : K :=
  genericRowMLE m values left+gamma*genericRowMLE m values right

/-- Direct algebraic meaning of the verifier's final eq(ru)+gamma*eq(rv)
weights, before removing the known constant input contribution. -/
theorem gkr_input_functional_weights (m : Nat) (left right : Nat → K) (gamma : K)
    (values : Nat → K) :
    cubeSum m (fun i => (rowEqualityWeight m left i+gamma*rowEqualityWeight m right i)*values i)=
      gkrInputFunctional m left right gamma values := by
  unfold cubeSum gkrInputFunctional
  have split : ∀ indices : List Nat,
      (indices.map (fun i => (rowEqualityWeight m left i+gamma*rowEqualityWeight m right i)*values i)).sum=
      (indices.map (fun i => rowEqualityWeight m left i*values i)).sum+
        gamma*(indices.map (fun i => rowEqualityWeight m right i*values i)).sum := by
    intro indices
    induction indices with
    | nil => simp; grind
    | cons i rest ih => simp only [List.map_cons,List.sum_cons,ih]; grind
  rw [split]
  change cubeSum m (fun i => rowEqualityWeight m left i*values i)+
    gamma*cubeSum m (fun i => rowEqualityWeight m right i*values i)=_
  rw [row_equality_dot,row_equality_dot]

/-- This universal GKR weight family has no nonzero fixed input kernel.
Boolean specialization is algebraic; the random sampler need not hit Boolean
points. A counting theorem must first establish the universal identity. -/
theorem gkr_universal_functionals_separate (m : Nat) (a b : Nat → K)
    (same : ∀ left right gamma,
      gkrInputFunctional m left right gamma a=gkrInputFunctional m left right gamma b)
    (i : Nat) (bound : i<2^m) : a i=b i := by
  obtain ⟨bits,index⟩ := packed_claim_lane_bits m i bound
  have h := same (genericRowBooleanPoint bits) (fun _ => 0) 0
  simp only [gkrInputFunctional,generic_row_mle_boolean,index] at h
  grind

/-- Once a SINGLE input vector is fixed, equality of this universal weight
family carries every deterministic circuit predicate, not just one opening. -/
theorem gkr_common_input_predicate (m : Nat) (a b : Nat → K)
    (same : ∀ left right gamma,
      gkrInputFunctional m left right gamma a=gkrInputFunctional m left right gamma b)
    (predicate : (Nat → K) → Prop)
    (extensional : ∀ x y,(∀ i,i<2^m → x i=y i) → predicate x → predicate y)
    (valid : predicate a) : predicate b := by
  apply extensional a b _ valid
  exact gkr_universal_functionals_separate m a b same

/-- A challenge-dependent pair lies in the sampled equality functional's
kernel at EVERY challenge. It need not be one fixed input vector. -/
def gkrAdaptiveKernel (r : K) (i : Nat) : K := if i=0 then r else r-1

theorem gkr_adaptive_input_kernel (r : K) :
    genericRowMLE 1 (gkrAdaptiveKernel r) (fun _ => r)=0 := by
  simp only [genericRowMLE,gkrAdaptiveKernel,Nat.reduceEqDiff,ite_true,ite_false]
  grind

/-- The adaptive pairs above cannot all equal one pre-challenge vector. -/
theorem gkr_adaptive_kernel_not_fixed (nontrivial : (0:K)≠1) :
    ¬∃ values : Nat → K,∀ r i,i<2 → values i=gkrAdaptiveKernel r i := by
  rintro ⟨values,fixed⟩
  have zero := fixed 0 0 (by decide)
  have one := fixed 1 0 (by decide)
  simp only [gkrAdaptiveKernel,ite_true] at zero one
  exact nontrivial (zero.symm.trans one)

/-- A fixed committed input such as [1,1] has a different answer. The
adaptive kernel example does NOT satisfy authentication to this fixed source. -/
theorem gkr_fixed_ones_functional (r : K) :
    genericRowMLE 1 (fun _ => (1:K)) (fun _ => r)=1 := by
  simp only [genericRowMLE]
  grind

end NearCompression
