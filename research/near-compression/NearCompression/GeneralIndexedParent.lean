import NearCompression.IndexedWeightedPullback
import NearCompression.GeneralWeightedExtraction
namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

private theorem general_dot_empty (ws : List K) : coefficientDot ws []=0 := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp only [coefficientDot,List.getD_nil,List.drop_nil,ih]; grind

private theorem general_interleaved_dot (ew ow ce co : List K) (shape : ew.length=ow.length) :
    coefficientDot (rsInterleave ew ow) (rsInterleave ce co)=
      coefficientDot ew ce+coefficientDot ow co := by
  induction ew generalizing ow ce co with
  | nil => cases ow <;> simp_all [rsInterleave,coefficientDot] <;> grind
  | cons w ew ih =>
    cases ow with
    | nil => simp at shape
    | cons v ow =>
      have len : ew.length=ow.length := by simpa using shape
      cases ce <;> cases co <;>
        simp only [rsInterleave,coefficientDot,List.getD_cons_zero,List.getD_nil,
          List.drop_succ_cons,List.drop_zero,List.drop_nil,ih ow _ _ len,general_dot_empty] <;> grind

theorem general_residual_interleaved (ew ow ce co : List K) (shape : ew.length=ow.length) :
    scalarRSResidual (rsInterleave ew ow) (Poly.mk (rsInterleave ce co))=
      scalarRSResidual ew (Poly.mk ce)+scalarRSResidual ow (Poly.mk co) := by
  simp only [scalarRSResidual,scalar_residual_dot,List.drop_zero]
  exact general_interleaved_dot ew ow ce co shape

theorem general_indexed_parent (N D threshold : Nat) (weight : Nat → Nat)
    (source : Nat → K) (root childRoot : K) (evenWeights oddWeights : List K) (weightShape : evenWeights.length=oddWeights.length)
    (sent even odd : Poly K) (de : even.DegLt D) (do_ : odd.DegLt D)
    (h2 : (2:K)≠0) (nonzero : ∀ y<N,root^y≠0)
    (squared : ∀ y<N,childRoot^y=root^y*root^y)
    (negative : ∀ y<N,root^(y+N)= -(root^y))
    (agree : threshold≤consistencyMass (List.range N) (fun y => weight y+weight (y+N))
      (fun y => rsPairDecode (root^y) (source y,source (y+N))=
        (even.eval (childRoot^y),odd.eval (childRoot^y))))
    (identity : (sent-generalFoldResidualPolynomial evenWeights oddWeights even odd).IsZero) :
    ∃ parent : Poly K,parent.DegLt (2*D) ∧
      threshold≤consistencyMass (List.range (2*N)) weight
        (fun y => source y=parent.eval (root^y)) ∧
      scalarRSResidual (rsInterleave evenWeights oddWeights) parent=sent.eval 0+sent.eval 1 := by
  let ce := canonicalPolynomial D even
  let co := canonicalPolynomial D odd
  let parent := Poly.mk (rsInterleave ce.coeffs co.coeffs)
  have ep : ∀ x,(Poly.mk ce.coeffs).eval x=even.eval x := canonical_polynomial_eval D even de
  have op : ∀ x,(Poly.mk co.coeffs).eval x=odd.eval x := canonical_polynomial_eval D odd do_
  refine ⟨parent,rs_interleave_degree ce.coeffs co.coeffs D
    (canonical_polynomial_length D even) (canonical_polynomial_length D odd),?_,?_⟩
  · apply Nat.le_trans agree
    apply indexed_pair_mass_pullback
    intro y hy joint
    rw [squared y hy] at joint
    have encode := congrArg (rsPairEncode (root^y)) joint
    rw [rs_pair_encode_decode _ h2 (nonzero y hy)] at encode
    have expected := rs_interleave_pair ce.coeffs co.coeffs (root^y)
    rw [ep,op] at expected
    rw [expected] at encode
    refine ⟨congrArg Prod.fst encode,?_⟩
    rw [negative y hy]
    exact congrArg Prod.snd encode
  · change scalarRSResidual _ (Poly.mk (rsInterleave ce.coeffs co.coeffs))=_
    rw [general_residual_interleaved _ _ _ _ weightShape]
    change scalarRSResidual evenWeights ce+scalarRSResidual oddWeights co=_
    rw [canonical_polynomial_residual D even de,canonical_polynomial_residual D odd do_]
    have values (r : K) : sent.eval r=(generalFoldResidualPolynomial evenWeights oddWeights even odd).eval r := by
      have eq := Poly.eval_of_isZero identity r
      rw [Poly.eval_sub] at eq
      grind
    rw [values 0,values 1,general_fold_residual_endpoints]

end NearCompression
