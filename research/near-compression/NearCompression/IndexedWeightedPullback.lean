import NearCompression.WeightedFoldComposition

namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

private theorem consistency_mass_weight_add {A : Type} (xs : List A)
    (w v : A → Nat) (event : A → Prop) :
    consistencyMass xs (fun x => w x+v x) event=
      consistencyMass xs w event+consistencyMass xs v event := by
  classical
  induction xs with
  | nil => simp [consistencyMass]
  | cons x xs ih =>
    simp only [consistencyMass,List.map_cons,List.sum_cons] at ih ⊢
    by_cases h : event x <;> simp_all <;> omega

/-- Exact natural-order domain split, no field inverse/index lookup needed. -/
theorem indexed_pair_mass_pullback (N : Nat) (w : Nat → Nat) (joint event : Nat → Prop)
    (recover : ∀ y<N,joint y → event y ∧ event (y+N)) :
    consistencyMass (List.range N) (fun y => w y+w (y+N)) joint≤
      consistencyMass (List.range (2*N)) w event := by
  have left := consistency_mass_mono (List.range N) w joint event
    (fun y hy h => (recover y (List.mem_range.mp hy) h).1)
  have right := consistency_mass_mono (List.range N) (fun y => w (y+N)) joint
    (fun y => event (y+N)) (fun y hy h => (recover y (List.mem_range.mp hy) h).2)
  rw [consistency_mass_weight_add]
  have size : 2*N=N+N := by omega
  rw [size,List.range_add]
  simp only [consistencyMass,List.map_append,List.sum_append,List.map_map,
    Function.comp_def,Nat.add_comm N] at left right ⊢
  omega

/-- Indexed nonlinear extraction conclusion maps to a CONCRETE parent
candidate in natural root-power order, including trailing-zero normalization. -/
theorem indexed_weighted_parent (N D threshold : Nat) (weight : Nat → Nat)
    (source : Nat → K) (root childRoot : K) (weights : List K) (w0 w1 : K)
    (sent even odd : Poly K) (de : even.DegLt D) (do_ : odd.DegLt D)
    (h2 : (2:K)≠0) (nonzero : ∀ y<N,root^y≠0)
    (squared : ∀ y<N,childRoot^y=root^y*root^y)
    (negative : ∀ y<N,root^(y+N)= -(root^y))
    (agree : threshold≤consistencyMass (List.range N) (fun y => weight y+weight (y+N))
      (fun y => rsPairDecode (root^y) (source y,source (y+N))=
        (even.eval (childRoot^y),odd.eval (childRoot^y))))
    (identity : (sent-weightedFoldResidualPolynomial w0 w1
      (scalarRSResidual weights even) (scalarRSResidual weights odd)).IsZero) :
    ∃ parent : Poly K,parent.DegLt (2*D) ∧
      threshold≤consistencyMass (List.range (2*N)) weight
        (fun y => source y=parent.eval (root^y)) ∧
      scalarRSResidual (rsInterleave (weights.map (fun w => w0*w))
        (weights.map (fun w => w1*w))) parent=sent.eval 0+sent.eval 1 := by
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
    rw [scalar_residual_interleaved]
    change w0*scalarRSResidual weights ce+w1*scalarRSResidual weights co=_
    rw [canonical_polynomial_residual D even de,canonical_polynomial_residual D odd do_]
    have values (r : K) : sent.eval r=affineWeightedResidual w0 w1
        (scalarRSResidual weights even) (scalarRSResidual weights odd) r := by
      have eq := Poly.eval_of_isZero identity r
      rw [Poly.eval_sub,weighted_fold_residual_polynomial_eval] at eq
      grind
    rw [values 0,values 1,affine_weighted_residual_endpoints]

end NearCompression
