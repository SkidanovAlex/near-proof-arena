import NearCompression.GenericRSPairRepresentation
import NearCompression.WeightedConsistencyTransfer

namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

/-- Exact low-bit interleaving, with zero padding of a short component. -/
def rsInterleave : List K → List K → List K
  | [],[] => []
  | [],b::bs => 0::b::rsInterleave [] bs
  | a::as,[] => a::0::rsInterleave as []
  | a::as,b::bs => a::b::rsInterleave as bs

theorem rs_interleave_eval (even odd : List K) (x : K) :
    (Poly.mk (rsInterleave even odd)).eval x=
      (Poly.mk even).eval (x*x)+x*(Poly.mk odd).eval (x*x) := by
  induction even generalizing odd with
  | nil =>
    induction odd with
    | nil => simp only [rsInterleave,Poly.eval,Poly.evalL]; grind
    | cons b bs ih => simp only [rsInterleave,Poly.eval,Poly.evalL] at ih ⊢; grind
  | cons a as ih =>
    cases odd with
    | nil =>
      have h := ih []
      simp only [rsInterleave,Poly.eval,Poly.evalL] at h ⊢
      grind
    | cons b bs =>
      have h := ih bs
      simp only [rsInterleave,Poly.eval,Poly.evalL] at h ⊢
      grind

theorem rs_interleave_length (even odd : List K) (D : Nat)
    (he : even.length≤D) (ho : odd.length≤D) : (rsInterleave even odd).length≤2*D := by
  induction D generalizing even odd with
  | zero =>
    have e : even=[] := List.eq_nil_of_length_eq_zero (by omega)
    have o : odd=[] := List.eq_nil_of_length_eq_zero (by omega)
    subst even; subst odd; simp [rsInterleave]
  | succ D ih =>
    cases even with
    | nil => cases odd with
      | nil => simp [rsInterleave]
      | cons b bs =>
        have h := ih [] bs (by simp) (by simp only [List.length_cons] at ho; omega)
        simp only [rsInterleave,List.length_cons] at h ⊢; omega
    | cons a as => cases odd with
      | nil =>
        have h := ih as [] (by simp only [List.length_cons] at he; omega) (by simp)
        simp only [rsInterleave,List.length_cons] at h ⊢; omega
      | cons b bs =>
        have h := ih as bs (by simp only [List.length_cons] at he; omega)
          (by simp only [List.length_cons] at ho; omega)
        simp only [rsInterleave,List.length_cons] at h ⊢; omega

theorem rs_interleave_degree (even odd : List K) (D : Nat)
    (he : even.length≤D) (ho : odd.length≤D) :
    (Poly.mk (rsInterleave even odd)).DegLt (2*D) :=
  (Poly.degLt_length _).mono (rs_interleave_length even odd D he ho)

theorem rs_interleave_pair (even odd : List K) (x : K) :
    rsPairEncode x ((Poly.mk even).eval (x*x),(Poly.mk odd).eval (x*x))=
      ((Poly.mk (rsInterleave even odd)).eval x,
       (Poly.mk (rsInterleave even odd)).eval (-x)) := by
  rw [rs_interleave_eval,rs_interleave_eval]
  have square : (-x)*(-x)=x*x := by grind
  rw [square]
  apply Prod.ext <;> simp only [rsPairEncode] <;> grind

/-- Concrete polynomial instantiation of weighted pair pullback. The source
oracle remains arbitrary. The parent polynomial is explicitly interleaved. -/
theorem weighted_rs_interleaved_pullback (reps : List K) (weight : K → Nat)
    (source : K → K) (even odd : List K) (h2 : (2:K)≠0)
    (nonzero : ∀ x∈reps,x≠0) :
    consistencyMass reps (fun x => weight x+weight (-x))
      (fun x => rsPairDecode x (source x,source (-x))=
        ((Poly.mk even).eval (x*x),(Poly.mk odd).eval (x*x))) ≤
    consistencyMass (reps.flatMap (fun x => [x,-x])) weight
      (fun x => source x=(Poly.mk (rsInterleave even odd)).eval x) := by
  apply consistency_pair_pullback
  intro x member joint
  have eq := congrArg (rsPairEncode x) joint
  rw [rs_pair_encode_decode x h2 (nonzero x member),rs_interleave_pair] at eq
  exact ⟨congrArg Prod.fst eq,congrArg Prod.snd eq⟩

end NearCompression
