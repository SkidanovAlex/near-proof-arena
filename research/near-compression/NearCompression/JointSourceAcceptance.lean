import NearCompression.GKRJointTensorCandidate
import NearCompression.WeightedPCSPrefixStrategy

/-! Far-source acceptance for fixed multiaffine source contractions followed by
an adaptive weighted folding prover. Sources precede the outer coordinates;
the entire inner strategy may depend on them. Ideal independent challenges and
authenticated terminal oracles remain explicit, not inferred from hashes. -/
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

omit [Field K] in
private theorem unit_mass (domain : List K) (event : K → Prop) :
    consistencyMass domain (fun _ => 1) event=count domain event := by
  classical
  induction domain with
  | nil => simp [consistencyMass,count]
  | cons x xs ih =>
    simp only [consistencyMass,count,List.map_cons,List.sum_cons,List.countP_cons] at ih ⊢
    by_cases h : event x <;> simp_all <;> omega

/-- Compose an outer exceptional event with a uniformly bounded inner error. -/
theorem finite_product_acceptance_budget {A B : Type} (outer : List A) (inner : List B)
    (accept : A → B → Prop) (good : A → Prop) (scale budget : Nat)
    (bad : ∀ a∈outer,¬good a → count inner (accept a)*scale≤budget) :
    count (outer.flatMap (fun a => inner.map (fun b => (a,b))))
      (fun pair => accept pair.1 pair.2)*scale≤
    count outer good*inner.length*scale+outer.length*budget := by
  classical
  induction outer with
  | nil => simp [count]
  | cons a rest ih =>
    have tail := ih (fun x hx => bad x (by simp [hx]))
    have head : count inner (accept a)≤inner.length := List.countP_le_length
    simp only [List.flatMap_cons,count,List.countP_append,List.countP_map,
      Function.comp_def,List.countP_cons,List.length_cons,Nat.add_mul] at tail ⊢
    by_cases h : good a
    · have bounded := Nat.mul_le_mul_right scale head
      simp only [h,decide_true,ite_true] at *
      simp_all [count]
      omega
    · have bounded := bad a (by simp) h
      simp only [h,decide_false] at *
      simp_all [count]
      omega

/-- No common prechallenge representative implies a bound on actual weighted
replay acceptance, not merely on existence of a terminal candidate. The inner
messages, initial claim and opening point may depend on all outer coordinates.
This is the far branch only; it is not accepted-proof-to-AIR soundness. -/
theorem joint_source_far_acceptance_count [DecidableEq K]
    (sample : List K) (sampleDistinct : sample.Nodup)
    (outerRounds foldRounds N T queries : Nat) (sizes degrees : Nat → Nat) (roots : Nat → K)
    (betas : List ((Nat → K) → K)) (sources : List (K → K))
    (affine : ∀ beta∈betas,∀ point coordinate,coordinate<outerRounds → ∀ r,
      beta (gkrSetCoordinate point coordinate r)=
        (1-r)*beta (gkrSetCoordinate point coordinate 0)+r*beta (gkrSetCoordinate point coordinate 1))
    (far : ¬∃ lanes,JointBetaRepresentative ((List.range N).map (fun i => roots 0^i))
      (fun _ => 1) outerRounds (degrees 0) T betas sources lanes)
    (points : List K → List K) (pointLength : ∀ z,(points z).length=foldRounds)
    (initial : List K → K) (provers : List K → WeightedPrefixProver K)
    (sourceValues : ∀ z∈uniformTuples sample outerRounds,∀ i<N,(provers z).oracle 0 [] i=
      jointBetaSource betas sources (roots 0^i) z)
    (domainDistinct : ((List.range N).map (fun i => roots 0^i)).Nodup)
    (interpolation : degrees 0-1<T)
    (sizeInitial : sizes 0=N) (positive : ∀ i≤foldRounds,0<sizes i)
    (sizeHalves : ∀ i<foldRounds,sizes i=2*sizes (i+1))
    (degreeHalves : ∀ i<foldRounds,degrees i=2*degrees (i+1))
    (h2 : (2:K)≠0) (regime : 2*N+degrees 0<3*T)
    (pointInjective : ∀ i<foldRounds,∀ a<sizes (i+1),∀ b<sizes (i+1),roots (i+1)^a=roots (i+1)^b → a=b)
    (nonzero : ∀ i<foldRounds,∀ y<sizes (i+1),roots i^y≠0)
    (squared : ∀ i<foldRounds,∀ y<sizes (i+1),roots (i+1)^y=roots i^y*roots i^y)
    (negative : ∀ i<foldRounds,∀ y<sizes (i+1),roots i^(y+sizes (i+1))= -(roots i^y))
    (terminalDegree : 1≤degrees foldRounds)
    (terminalAuthenticated : ∀ z∈uniformTuples sample outerRounds,∀ path∈uniformTuples sample foldRounds,
      weightedReplayCheck (points z) path ((provers z).messages foldRounds path)
        (initial z) ((provers z).terminal path)=true →
      ∀ y<sizes foldRounds,(provers z).oracles path foldRounds y=(provers z).terminal path) :
    let outer := uniformTuples sample outerRounds
    let inner := (uniformTuples sample foldRounds).flatMap (fun path =>
      (uniformTuples (List.range N) queries).map (fun qs => (path,qs)))
    count (outer.flatMap (fun z => inner.map (fun pair => (z,pair))))
      (fun pair => weightedReplayAccept (points pair.1) (initial pair.1)
        ((provers pair.1).messages foldRounds) (provers pair.1).terminal roots
        (provers pair.1).oracles sizes pair.2.1 pair.2.2)*sample.length≤
      (outerRounds*max N 2*sample.length^(outerRounds-1))*inner.length*sample.length+
      outer.length*(((List.range foldRounds).map (fun i => max (sizes (i+1)) 2)).sum*
        sample.length^foldRounds*N^queries+sample.length^(foldRounds+1)*(T-1)^queries) := by
  classical
  dsimp only
  let domain := (List.range N).map (fun i => roots 0^i)
  let good := fun z => ∃ candidate : Poly K,candidate.DegLt (degrees 0) ∧
    T≤consistencyMass domain (fun _ => 1)
      (fun x => jointBetaSource betas sources x z=candidate.eval x)
  have mass : (domain.map (fun _ => 1)).sum=N := by
    have eq : ∀ xs : List K,(xs.map (fun _ => 1)).sum=xs.length := by
      intro xs
      induction xs with
      | nil => rfl
      | cons x xs ih => simp [ih,Nat.add_comm]
    simpa [domain] using eq domain
  have farBound := joint_beta_candidate_far_count domain sample domainDistinct sampleDistinct
    (fun _ => 1) 1 (degrees 0) T outerRounds (by intros; omega)
    (by simpa [mass] using (show 2*N+(degrees 0-1)<3*T by omega))
    (by simpa using interpolation) betas sources affine far
  let inner := (uniformTuples sample foldRounds).flatMap (fun path =>
    (uniformTuples (List.range N) queries).map (fun qs => (path,qs)))
  have bound := finite_product_acceptance_budget (uniformTuples sample outerRounds) inner
    (fun z pair => weightedReplayAccept (points z) (initial z)
      ((provers z).messages foldRounds) (provers z).terminal roots
      (provers z).oracles sizes pair.1 pair.2) good sample.length
    (((List.range foldRounds).map (fun i => max (sizes (i+1)) 2)).sum*
      sample.length^foldRounds*N^queries+sample.length^(foldRounds+1)*(T-1)^queries) (by
    intro z hz absent
    have noCandidate : ¬weightedReplayInitialCandidate (points z) N (degrees 0) T
        (roots 0) (initial z) ((provers z).oracle 0 []) := by
      rintro ⟨candidate,degree,residual,agreement⟩
      apply absent
      refine ⟨candidate,degree,?_⟩
      rw [unit_mass]
      have transfer : count (List.range N)
          (fun i => (provers z).oracle 0 [] i=candidate.eval (roots 0^i))=
          count domain (fun x => jointBetaSource betas sources x z=candidate.eval x) := by
        simp only [domain,count,List.countP_map,Function.comp_def]
        apply List.countP_congr
        intro i hi
        simp [sourceValues z hz i (List.mem_range.mp hi)]
      rwa [transfer] at agreement
    have pcs := weighted_prefix_no_candidate_count sample sampleDistinct (points z) (initial z)
      (provers z) roots N T queries sizes degrees sizeInitial
      (by simpa [pointLength] using positive) (by simpa [pointLength] using sizeHalves)
      (by simpa [pointLength] using degreeHalves) h2 regime
      (by simpa [pointLength] using pointInjective) (by simpa [pointLength] using nonzero)
      (by simpa [pointLength] using squared) (by simpa [pointLength] using negative)
      (by simpa [pointLength] using terminalDegree)
      (by simpa [pointLength] using terminalAuthenticated z hz)
    simpa only [pointLength,noCandidate,not_false_eq_true,and_true] using pcs)
  apply Nat.le_trans bound
  have scaled := Nat.add_le_add_right
    (Nat.mul_le_mul_right sample.length (Nat.mul_le_mul_right inner.length farBound))
    ((uniformTuples sample outerRounds).length*(((List.range foldRounds).map (fun i => max (sizes (i+1)) 2)).sum*
      sample.length^foldRounds*N^queries+sample.length^(foldRounds+1)*(T-1)^queries))
  simpa only [domain,List.length_map,List.length_range] using scaled

end NearCompression
