import NearCompression.ScalarRSTerminal
import NearCompression.GenericRSPairRepresentation

/-! Reconstructing every terminal oracle leaf certifies that oracle's codeword,
conditional on tree-root binding. Unlike a sampled terminal, no prior degree
bound for an arbitrary committed word is assumed. The explicit bad event is
a distinct typed tree with the same root; reducing it to SHA-384 collisions
requires the separately specified canonical encoding/tree construction.
This theorem says nothing about preceding-oracle proximity. -/
set_option autoImplicit false
namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

/-- Scalar f(x),f(-x) pairs, with domain position outside and lane inside. -/
def reconstructedRSLeaves (coefficients : List (List K)) (anchors : List K) : List (List (K×K)) :=
  anchors.map fun x => coefficients.map fun c => ((Poly.mk c).eval x,(Poly.mk c).eval (-x))

def reconstructedRSResidual (coefficients weights : List (List K)) : K :=
  (coefficients.zip weights).foldr (fun pair acc => scalarRSResidual pair.2 (Poly.mk pair.1)+acc) 0

def reconstructedRSShape (degree lanes : Nat) (matrix : List (List K)) : Bool :=
  decide (matrix.length=lanes) && matrix.all (fun c => decide (c.length=degree))

/-- This root function is fixed for the expected stage/domain/lane context. -/
def reconstructedRSChecks {Digest : Type} [DecidableEq K] [DecidableEq Digest]
    (root : List (List (K×K)) → Digest) (degree lanes : Nat)
    (coefficients weights : List (List K)) (anchors : List K)
    (actualOracle : List (List (K×K))) (claim : K) : Bool :=
  reconstructedRSShape degree lanes coefficients && reconstructedRSShape degree lanes weights &&
    decide (root (reconstructedRSLeaves coefficients anchors)=root actualOracle) &&
    decide (reconstructedRSResidual coefficients weights=claim)

def ReconstructedRSTreeCollision {Digest : Type} (root : List (List (K×K)) → Digest)
    (left right : List (List (K×K))) : Prop := left≠right ∧ root left=root right

/-- Accepted reconstruction gives either an explicit tree-binding failure or
exact equality to a bounded-degree codeword with the checked residual claim.
The degree follows from the disclosed coefficient lengths. -/
theorem reconstructed_rs_collision_or_correct {Digest : Type} [DecidableEq K] [DecidableEq Digest]
    (root : List (List (K×K)) → Digest) (degree lanes : Nat)
    (coefficients weights : List (List K)) (anchors : List K)
    (actualOracle : List (List (K×K))) (claim : K)
    (checked : reconstructedRSChecks root degree lanes coefficients weights anchors actualOracle claim=true) :
    ReconstructedRSTreeCollision root (reconstructedRSLeaves coefficients anchors) actualOracle ∨
    (actualOracle=reconstructedRSLeaves coefficients anchors ∧ coefficients.length=lanes ∧
      (∀ c∈coefficients,(Poly.mk c).DegLt degree) ∧ reconstructedRSResidual coefficients weights=claim) := by
  simp only [reconstructedRSChecks,Bool.and_eq_true,decide_eq_true_eq] at checked
  by_cases same : reconstructedRSLeaves coefficients anchors=actualOracle
  · right
    have shape := checked.1.1.1
    simp only [reconstructedRSShape,Bool.and_eq_true,decide_eq_true_eq] at shape
    refine ⟨same.symm,shape.1,?_,checked.2⟩
    intro c hc
    have size : c.length=degree := of_decide_eq_true (List.all_eq_true.mp shape.2 c hc)
    simpa only [size] using Poly.degLt_length (Poly.mk c)
  · exact Or.inl ⟨same,checked.1.2⟩

/-- Excluding this concrete tree-root collision leaves a certified codeword,
without an assumed degree bound on the previously arbitrary oracle. -/
theorem reconstructed_rs_binding_correct {Digest : Type} [DecidableEq K] [DecidableEq Digest]
    (root : List (List (K×K)) → Digest) (degree lanes : Nat)
    (coefficients weights : List (List K)) (anchors : List K)
    (actualOracle : List (List (K×K))) (claim : K)
    (checked : reconstructedRSChecks root degree lanes coefficients weights anchors actualOracle claim=true)
    (binding : ¬ReconstructedRSTreeCollision root (reconstructedRSLeaves coefficients anchors) actualOracle) :
    actualOracle=reconstructedRSLeaves coefficients anchors ∧ coefficients.length=lanes ∧
      (∀ c∈coefficients,(Poly.mk c).DegLt degree) ∧ reconstructedRSResidual coefficients weights=claim := by
  rcases reconstructed_rs_collision_or_correct root degree lanes coefficients weights anchors actualOracle claim checked with h | h
  · exact False.elim (binding h)
  · exact h

/-- The reconstructed scalar pair has the existing even/odd interpretation,
not an unproved identification with raw even/odd coefficients in a leaf. -/
theorem reconstructed_rs_pair_semantics (coefficients : List K) (x : K) :
    ((Poly.mk coefficients).eval x,(Poly.mk coefficients).eval (-x))=
      rsPairEncode x ((Poly.mk (monomialEvenCoefficients coefficients)).eval (x*x),
        (Poly.mk (monomialOddCoefficients coefficients)).eval (x*x)) :=
  (rs_polynomial_pair_encode coefficients x).symm

/-- Uniqueness between bounded representations follows from complete scalar
coverage; no degree premise about an arbitrary initial oracle is introduced. -/
theorem reconstructed_rs_representation_unique (left right : List K) (degree : Nat)
    (anchors : List K) (leftShape : left.length≤degree) (rightShape : right.length≤degree)
    (distinct : (anchors.flatMap (fun x => [x,-x])).Nodup)
    (enough : degree≤(anchors.flatMap (fun x => [x,-x])).length)
    (pairs : ∀ x∈anchors,((Poly.mk left).eval x,(Poly.mk left).eval (-x))=
      ((Poly.mk right).eval x,(Poly.mk right).eval (-x))) :
    (∀ i,(Poly.mk left).coeff i=(Poly.mk right).coeff i) ∧
      (∀ weights,scalarRSResidual weights (Poly.mk left)=scalarRSResidual weights (Poly.mk right)) := by
  have equal : ∀ x∈anchors.flatMap (fun x => [x,-x]),(Poly.mk left).eval x=(Poly.mk right).eval x := by
    intro x hx
    obtain ⟨a,ha,hx⟩ := List.mem_flatMap.mp hx
    have pair := pairs a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl
    · exact congrArg Prod.fst pair
    · exact congrArg Prod.snd pair
  have unique := scalar_rs_domain_unique (Poly.mk left) (Poly.mk right) degree _
    ((Poly.degLt_length _).mono leftShape) ((Poly.degLt_length _).mono rightShape) distinct enough equal
  exact ⟨unique.1,fun weights => scalar_rs_residual_congr _ _ weights unique.1⟩
end NearCompression
