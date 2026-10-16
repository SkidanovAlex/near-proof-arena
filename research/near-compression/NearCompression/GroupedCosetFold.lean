import NearCompression.RepeatedAffineFold
import NearCompression.DerivedFoldTransport

/-! Algebra for a four-value coset query replacing two intermediate pair
queries. No Merkle layout, proximity or Fiat--Shamir theorem is asserted. -/
namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

theorem grouped_affine_values_eval (r x : K) : ∀ cs : List K,cs.length%2=0 →
    (Poly.mk (affineFoldValues r cs)).eval x=
      (1-r)*(Poly.mk (monomialEvenCoefficients cs)).eval x+
      r*(Poly.mk (monomialOddCoefficients cs)).eval x
  | [],_ => by
    simp only [affineFoldValues,monomialEvenCoefficients,monomialOddCoefficients,Poly.eval,Poly.evalL]
    grind
  | [_],h => by simp at h
  | a::b::cs,h => by
    have even : cs.length%2=0 := by simp only [List.length_cons] at h;omega
    have ih:=grouped_affine_values_eval r x cs even
    simp only [affineFoldValues,monomialEvenCoefficients,monomialOddCoefficients,Poly.eval,Poly.evalL] at ih ⊢
    grind

theorem grouped_affine_pair_eval (cs : List K) (r x : K)
    (even : cs.length%2=0) (h2 : (2:K)≠0) (hx : x≠0) :
    derivedFoldValue x r ((Poly.mk cs).eval x,(Poly.mk cs).eval (-x))=
      (Poly.mk (affineFoldValues r cs)).eval (x*x) := by
  unfold derivedFoldValue
  rw [rs_polynomial_pair_decode cs x h2 hx,grouped_affine_values_eval r (x*x) cs even]
  grind

def groupedFourFold (x i r s a b c d : K) : K :=
  derivedFoldValue (x*x) s (derivedFoldValue x r (a,c),derivedFoldValue (x*i) r (b,d))

/-- Natural order [x, x*i, -x, -x*i] requires antipodal pairs (0,2)
and (1,3). Adjacent coefficient-style folding of these leaves is wrong. -/
theorem grouped_four_fold_eval (cs : List K) (x i r s : K)
    (even : cs.length%2=0) (nextEven : (affineFoldValues r cs).length%2=0)
    (h2 : (2:K)≠0) (hx : x≠0) (hi : i*i= -1) :
    groupedFourFold x i r s ((Poly.mk cs).eval x) ((Poly.mk cs).eval (x*i))
      ((Poly.mk cs).eval (-x)) ((Poly.mk cs).eval (-(x*i)))=
      (Poly.mk (affineFoldValues s (affineFoldValues r cs))).eval ((x*x)*(x*x)) := by
  have hin : i≠0 := by grind
  have hxi : x*i≠0 := by grind
  have hxx : x*x≠0 := by grind
  have square : (x*i)*(x*i)= -(x*x) := by grind
  unfold groupedFourFold
  rw [grouped_affine_pair_eval cs r x even h2 hx,
    grouped_affine_pair_eval cs r (x*i) even h2 hxi,square]
  exact grouped_affine_pair_eval (affineFoldValues r cs) s (x*x) nextEven h2 hxx
end NearCompression
