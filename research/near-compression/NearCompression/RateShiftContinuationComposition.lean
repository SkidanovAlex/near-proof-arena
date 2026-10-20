import NearCompression.RateShiftContinuationCandidate
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

private theorem scaled_conditional_sum {A B : Type} (outer : List A) (inner : List B)
    (bad : A→Prop) (accept : A→B→Prop) (scale limit : Nat)
    (good : ∀ a∈outer,¬bad a→count inner (accept a)*scale≤limit) :
    (outer.map (fun a=>count inner (accept a))).sum*scale≤
      count outer bad*inner.length*scale+outer.length*limit := by
  classical
  induction outer with
  | nil => simp [count]
  | cons a rest ih =>
    have tail:=ih (fun b hb=>good b (by simp [hb]))
    have head:=good a (by simp)
    have maximum : count inner (accept a)≤inner.length := List.countP_le_length
    have scaled:=Nat.mul_le_mul_right scale maximum
    simp only [List.map_cons,List.sum_cons,count,List.countP_cons,List.length_cons] at tail head scaled ⊢
    by_cases h : bad a <;> simp_all <;> grind

/-- Joint mixing/continuation experiment. The oracle and complete candidate
list precede gamma, while the whole continuation strategy may depend on gamma.
The semantic no-correct-candidate premise still needs rate-shift transfer. -/
theorem rate_shift_continuation_composition
    (mixSample foldSample : List K) (mixDistinct : mixSample.Nodup) (foldDistinct : foldSample.Nodup)
    (strategy : K→List K→GeneralFoldTranscript K)
    (N D T radius rounds q : Nat) (sizes degrees : Nat→Nat)
    (sizeInitial : sizes 0=N) (degreeInitial : degrees 0=D)
    (positive : ∀ i≤rounds,0<sizes i)
    (sizeHalves : ∀ i<rounds,sizes i=2*sizes (i+1))
    (degreeHalves : ∀ i<rounds,degrees i=2*degrees (i+1))
    (h2 : (2:K)≠0) (regime : 2*N+degrees 0<3*T)
    (omega : K) (received : K→K)
    (domainDistinct : ((List.range N).map (fun i=>omega^i)).Nodup)
    (radiusFits : N≤T+radius) (unique : 2*radius+D≤N)
    (weights points values : List K) (claim : K)
    (weightSize : D≤weights.length) (valueShape : values.length=points.length)
    (noCorrect : ∀ p∈rateShiftUniqueList ((List.range N).map (fun i=>omega^i)) received D radius,
      rateShiftCandidateWrong weights points p claim values)
    (causal : ∀ gamma,∀ path∈uniformTuples foldSample rounds,∀ i<rounds,
      (strategy gamma path).snapshot N sizes i=(strategy gamma (path.take i)).snapshot N sizes i)
    (challengeValues : ∀ gamma,∀ path∈uniformTuples foldSample rounds,∀ i<rounds,
      (strategy gamma path).challenges i=path[i]?.getD 0)
    (bindings : ∀ gamma,∀ path∈uniformTuples foldSample rounds,
      generalFoldPathChecks (strategy gamma) N sizes degrees T rounds path →
      (strategy gamma path).roots 0=omega ∧
      (∀ i<N,(strategy gamma path).oracles 0 i=received (omega^i)) ∧
      (strategy gamma path).weights 0=rateShiftAccumulateWeights weights gamma gamma points ∧
      (strategy gamma path).claims 0=rateShiftAccumulatedClaim claim values gamma) :
    let continuations := (uniformTuples foldSample rounds).flatMap (fun path=>
      (uniformTuples (List.range N) q).map (fun queries=>(path,queries)))
    count (mixSample.flatMap (fun gamma=>continuations.map (fun continuation=>(gamma,continuation))))
      (fun pair=>generalCheckedFoldAccept (strategy pair.1) N sizes degrees T rounds pair.2.1 pair.2.2)*foldSample.length≤
      points.length*continuations.length*foldSample.length+
      mixSample.length*(((List.range rounds).map (fun i=>max (sizes (i+1)) 2)).sum*
        foldSample.length^rounds*N^q+foldSample.length^(rounds+1)*(T-1)^q) := by
  classical
  dsimp only
  let domain:=(List.range N).map (fun i=>omega^i)
  let family:=rateShiftUniqueList domain received D radius
  let bad := fun gamma=>∃ p∈family,rateShiftCandidateWrong weights points p claim values ∧
    rateShiftAccumulatedFunctional weights points gamma p=rateShiftAccumulatedClaim claim values gamma
  have mixing : count mixSample bad≤points.length := by
    have h:=rate_shift_list_mixing_bound family weights points claim values mixSample valueShape mixDistinct
    have len:=rate_shift_unique_list_length domain received D radius
    have small:=Nat.mul_le_mul_right points.length len
    simp only [Nat.one_mul] at small
    exact Nat.le_trans h small
  let continuations := (uniformTuples foldSample rounds).flatMap (fun path=>
    (uniformTuples (List.range N) q).map (fun queries=>(path,queries)))
  let accept := fun gamma (pair : List K×List Nat)=>
    generalCheckedFoldAccept (strategy gamma) N sizes degrees T rounds pair.1 pair.2
  have good (gamma : K) (member : gamma∈mixSample) (notBad : ¬bad gamma) :
      count continuations (accept gamma)*foldSample.length≤
      ((List.range rounds).map (fun i=>max (sizes (i+1)) 2)).sum*foldSample.length^rounds*N^q+
        foldSample.length^(rounds+1)*(T-1)^q := by
    apply general_checked_interactive_fold_soundness foldSample foldDistinct (strategy gamma)
      N T rounds q sizes degrees sizeInitial positive sizeHalves degreeHalves h2 regime
      (causal gamma) (challengeValues gamma)
    intro path hp checks candidate
    obtain ⟨root,oracle,ws,cl⟩:=bindings gamma path hp checks
    obtain ⟨p,mem,equal⟩:=rate_shift_indexed_candidate N D T radius sizes degrees
      (strategy gamma path).roots (strategy gamma path).challenges (strategy gamma path).oracles
      (strategy gamma path).weights (strategy gamma path).claims sizeInitial degreeInitial received
      (by simpa only [root] using oracle) (by simpa only [root] using domainDistinct)
      radiusFits unique weights points values claim gamma weightSize ws cl candidate
    rw [root] at mem
    exact notBad ⟨p,mem,noCorrect p mem,equal⟩
  have total:=scaled_conditional_sum mixSample continuations bad accept foldSample.length _ good
  have scaledMix:=Nat.mul_le_mul_right (continuations.length*foldSample.length) mixing
  have result : (mixSample.map (fun gamma=>count continuations (accept gamma))).sum*foldSample.length≤
      points.length*continuations.length*foldSample.length+
      mixSample.length*(((List.range rounds).map (fun i=>max (sizes (i+1)) 2)).sum*
        foldSample.length^rounds*N^q+foldSample.length^(rounds+1)*(T-1)^q) := by
    grind
  simpa only [count,List.countP_flatMap,List.countP_map,Function.comp_def,accept,continuations] using result
end NearCompression
