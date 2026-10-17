import NearCompression.IndependentMixingCandidates
import NearCompression.CodeSwitchStage

namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

/-- The verifier computes its new weights and claim without a polynomial. -/
def switchVerifierState (weights : List K) (claim : K)
    (templates : List (K × K)) (mixers : List K) : List K × K :=
  let result:=switchInjectAll (weights.map (fun w=>((0:K),w))) claim
    (switchBindConstraints templates mixers)
  (result.1.map Prod.snd,result.2)

private theorem inject_weights (xs ys : List (K × K))
    (same : xs.map Prod.snd=ys.map Prod.snd) (point mixer power : K) :
    (switchInjectPairs point mixer power xs).map Prod.snd=
      (switchInjectPairs point mixer power ys).map Prod.snd := by
  induction xs generalizing ys power with
  | nil => cases ys <;> simp_all [switchInjectPairs]
  | cons x xs ih =>
    cases ys with
    | nil => simp at same
    | cons y ys =>
      simp only [List.map_cons,List.cons.injEq] at same
      simp only [switchInjectPairs,List.map_cons,same.1,ih ys same.2]

/-- Coefficients never influence the verifier's carried weights or claim. -/
theorem switch_inject_verifier_independent (xs ys : List (K × K))
    (same : xs.map Prod.snd=ys.map Prod.snd) (claim : K)
    (constraints : List (SwitchConstraint K)) :
    (switchInjectAll xs claim constraints).1.map Prod.snd=
      (switchInjectAll ys claim constraints).1.map Prod.snd ∧
    (switchInjectAll xs claim constraints).2=(switchInjectAll ys claim constraints).2 := by
  induction constraints generalizing xs ys claim with
  | nil => exact ⟨same,rfl⟩
  | cons c cs ih => exact ih _ _ (inject_weights xs ys same c.point c.mixer 1) _

omit [Field K] in
private theorem zip_second (cs ws : List K) (shape : cs.length=ws.length) :
    (cs.zip ws).map Prod.snd=ws := by
  induction cs generalizing ws with
  | nil => cases ws <;> simp_all
  | cons c cs ih =>
    cases ws with
    | nil => simp at shape
    | cons w ws => simp only [List.length_cons] at shape
                   simp [ih ws (by omega)]

/-- The continuation's scalar functional is exactly injection acceptance for
this same polynomial. Degree and shape prevent normalization/truncation gaps. -/
theorem switch_continuation_functional (D : Nat) (weights : List K)
    (shape : weights.length=D) (claim : K) (templates : List (K × K))
    (mixers : List K) (p : Poly K) (degree : p.DegLt D) :
    scalarRSResidual (switchVerifierState weights claim templates mixers).1 p=
        (switchVerifierState weights claim templates mixers).2 ↔
      SwitchMixedAccept (switchPolynomialPairs D weights p) claim templates mixers := by
  let xs:=switchPolynomialPairs D weights p
  let constraints:=switchBindConstraints templates mixers
  have same : xs.map Prod.snd=(weights.map (fun w=>((0:K),w))).map Prod.snd := by
    have h:=zip_second (rateShiftNormalize D p).coeffs weights (by rw [rate_shift_normalize_length,shape])
    rw [List.map_map]
    change xs.map Prod.snd=weights.map id
    rw [List.map_id]
    exact h
  have independent:=switch_inject_verifier_independent xs _ same claim constraints
  have coefficients : (switchInjectAll xs claim constraints).1.map Prod.fst=
      (rateShiftNormalize D p).coeffs := by
    rw [switch_inject_all_coefficients]
    exact switch_polynomial_pairs_coefficients D weights shape p
  have dot:=affine_fold_terminal_dot (switchInjectAll xs claim constraints).1
  rw [coefficients] at dot
  have congruent:=scalar_rs_residual_congr (rateShiftNormalize D p) p
    ((switchInjectAll xs claim constraints).1.map Prod.snd)
    (rate_shift_normalize_coeff D p degree)
  rw [congruent] at dot
  change scalarRSResidual ((switchInjectAll (weights.map (fun w=>((0:K),w))) claim constraints).1.map Prod.snd) p=
    (switchInjectAll (weights.map (fun w=>((0:K),w))) claim constraints).2 ↔ _
  rw [←independent.1,←independent.2,dot]
  rfl

private theorem unit_mass_bound {A : Type} (domain : List A) (weight : A→Nat)
    (event : A→Prop) (cap : ∀ x∈domain,weight x≤1) :
    consistencyMass domain weight event≤count domain event := by
  classical
  induction domain with
  | nil => simp [consistencyMass,count]
  | cons x xs ih =>
    have head:=cap x (by simp)
    have tail:=ih (fun y hy=>cap y (by simp [hy]))
    simp only [consistencyMass,count,List.map_cons,List.sum_cons,List.countP_cons] at tail ⊢
    by_cases h : event x <;> simp_all <;> omega

/-- Extract the SAME agreeing polynomial and injected functional from the
existing indexed candidate relation. This does not infer that relation from
acceptance, nor identify a code-switch chain with a binary-fold continuation. -/
theorem switch_indexed_continuation_candidate (N D T : Nat) (sizes degrees : Nat→Nat)
    (roots challenges : Nat→K) (oracles : Nat→Nat→K)
    (allWeights : Nat→List K) (claims : Nat→K)
    (sizeInitial : sizes 0=N) (degreeInitial : degrees 0=D)
    (received : K→K) (binding : ∀ i<N,oracles 0 i=received (roots 0^i))
    (weights : List K) (shape : weights.length=D) (claim : K)
    (templates : List (K × K)) (mixers : List K)
    (initialWeights : allWeights 0=(switchVerifierState weights claim templates mixers).1)
    (initialClaim : claims 0=(switchVerifierState weights claim templates mixers).2)
    (candidate : indexedChainCandidate N sizes degrees roots challenges oracles allWeights claims T 0) :
    ∃ p : Poly K, p.DegLt D ∧
      T≤count ((List.range N).map (fun i=>roots 0^i)) (fun x=>p.eval x=received x) ∧
      SwitchMixedAccept (switchPolynomialPairs D weights p) claim templates mixers := by
  obtain ⟨p,degree,functional,mass⟩:=candidate
  have cap : ∀ y∈List.range N,globalChainWeight (List.range N) sizes
      (globalRSChainCheck sizes roots challenges oracles) 0 y≤1 := by
    intro y hy
    exact global_chain_weight_cap N sizes _ 0 sizeInitial (by intro j hj;omega) y
      (by rw [sizeInitial];exact List.mem_range.mp hy)
  rw [sizeInitial] at mass
  have agree:=Nat.le_trans mass (unit_mass_bound _ _ _ cap)
  have transport : count (List.range N) (fun y=>oracles 0 y=p.eval (roots 0^y))=
      count ((List.range N).map (fun i=>roots 0^i)) (fun x=>p.eval x=received x) := by
    classical
    simp only [count,List.countP_map,Function.comp_def]
    apply List.countP_congr
    intro y hy
    simp only [decide_eq_true_eq]
    rw [binding y (List.mem_range.mp hy)]
    exact eq_comm
  rw [transport] at agree
  rw [initialWeights,initialClaim] at functional
  have deg : p.DegLt D := by simpa only [degreeInitial] using degree
  exact ⟨p,deg,agree,(switch_continuation_functional D weights shape claim templates mixers p deg).mp functional⟩
/-- If every agreeing candidate violates an original constraint, existence of
an agreeing candidate for the verifier's new functional is a bad mixing event.
The semantic no-correct-candidate premise must be established by rate transfer. -/
theorem switch_continuation_candidate_count (alphabet domain : List K)
    (complete : ∀ a,a∈alphabet) (received : K→K) (D T : Nat)
    (weights : List K) (shape : weights.length=D) (claim : K)
    (templates : List (K × K)) (sample : List K) (distinct : sample.Nodup)
    (noCorrect : ∀ p : Poly K,p.DegLt D→
      T≤count domain (fun x=>p.eval x=received x)→
      SwitchCandidateWrong (switchPolynomialPairs D weights p) claim templates) :
    count (uniformTuples sample templates.length) (fun rs=>∃ p : Poly K,
      p.DegLt D ∧ T≤count domain (fun x=>p.eval x=received x) ∧
      scalarRSResidual (switchVerifierState weights claim templates rs).1 p=
        (switchVerifierState weights claim templates rs).2)≤
      (johnsonCandidateList alphabet domain received D T).length*
        sample.length^(templates.length-1) := by
  apply Nat.le_trans ?_ (switch_johnson_mixing_count alphabet domain complete
    received D T weights claim templates sample distinct)
  apply count_mono
  intro rs h
  obtain ⟨p,degree,agree,functional⟩:=h
  exact ⟨p,degree,agree,noCorrect p degree agree,
    (switch_continuation_functional D weights shape claim templates rs p degree).mp functional⟩
end NearCompression
