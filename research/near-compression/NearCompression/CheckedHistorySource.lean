import NearCompression.CheckedHistoryAcceptance
import NearCompression.WeightedVirtualInitial
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

private theorem unit_cap_mass (domain : List Nat) (weight : Nat→Nat) (event : Nat→Prop)
    (cap : ∀ x∈domain,weight x≤1) : consistencyMass domain weight event≤count domain event := by
  classical
  induction domain with
  | nil => simp [consistencyMass,count]
  | cons x xs ih =>
    have head := cap x (by simp)
    have tail := ih (fun y hy=>cap y (by simp [hy]))
    simp only [consistencyMass,count,List.map_cons,List.sum_cons,List.countP_cons] at tail ⊢
    by_cases h : event x <;> simp_all <;> omega

/-- The initial consistency measure cannot manufacture agreement. No claim
about a decoded polynomial or commitment is assumed. -/
theorem indexed_initial_candidate_agreement (tr : GeneralFoldTranscript K)
    (N T : Nat) (sizes degrees : Nat→Nat) (initial : sizes 0=N)
    (candidate : indexedChainCandidate N sizes degrees tr.roots tr.challenges
      tr.oracles tr.weights tr.claims T 0) :
    ∃ p : Poly K,p.DegLt (degrees 0) ∧
      T≤count (List.range N) (fun i=>tr.oracles 0 i=p.eval (tr.roots 0^i)) := by
  obtain ⟨p,degree,residual,mass⟩ := candidate
  refine ⟨p,degree,?_⟩
  rw [initial] at mass
  apply Nat.le_trans mass
  apply unit_cap_mass
  intro y hy
  simpa using global_chain_weight_cap N sizes (globalRSChainCheck sizes tr.roots tr.challenges tr.oracles)
    0 initial (by intro j hj; omega) y (by rw [initial]; exact List.mem_range.mp hy)


/-- Source-far batching followed by arbitrary adaptive checked folding. The
initial no-candidate premise is derived outside a counted outer bad event.
This remains an ideal-oracle statement with explicit state binding. -/
theorem checked_history_joint_far_acceptance_budget
    (sample : List K) (distinct : sample.Nodup)
    (strategy : List K→List K→GeneralFoldTranscript K) (outerRounds N0 T rounds q : Nat)
    (sizes degrees : Nat→Nat) (initial : sizes 0=N0)
    (positive : ∀ j≤rounds,0<sizes j)
    (sizeHalves : ∀ j<rounds,sizes j=2*sizes (j+1))
    (degreeHalves : ∀ j<rounds,degrees j=2*degrees (j+1))
    (regime : 2*N0+degrees 0<3*T) (h2 : (2:K)≠0)
    (fixed : ∀ (z h : List K),h.length<rounds → ∀ r∈sample,
      (strategy z (h++[r])).snapshot N0 sizes h.length=(strategy z h).snapshot N0 sizes h.length)
    (weights : ∀ (z h : List K),h.length<rounds → ∀ r∈sample,
      (strategy z (h++[r])).weights h.length=(strategy z h).weights h.length)
    (claim : ∀ (z h : List K),h.length<rounds → ∀ r∈sample,
      (strategy z (h++[r])).claims h.length=(strategy z h).claims h.length)
    (challenge : ∀ (z h : List K),h.length<rounds → ∀ r∈sample,
      (strategy z (h++[r])).challenges h.length=r)

    (root : K) (betas : List ((Nat→K)→K)) (sources : List (K→K))
    (domainDistinct : ((List.range N0).map (fun i=>root^i)).Nodup)
    (affine : ∀ beta∈betas,∀ point coordinate,coordinate<outerRounds → ∀ r,
      beta (gkrSetCoordinate point coordinate r)=
        (1-r)*beta (gkrSetCoordinate point coordinate 0)+r*beta (gkrSetCoordinate point coordinate 1))
    (far : ¬∃ lanes,JointBetaRepresentative ((List.range N0).map (fun i=>root^i))
      (fun _=>1) outerRounds (degrees 0) T betas sources lanes)
    (interpolation : degrees 0-1<T)
    (initialRoot : ∀ z∈uniformTuples sample outerRounds,(strategy z []).roots 0=root)
    (sourceValues : ∀ z∈uniformTuples sample outerRounds,∀ i<N0,
      (strategy z []).oracles 0 i=jointBetaSource betas sources (root^i) z) :
    let outer:=uniformTuples sample outerRounds
    let inner:=(uniformTuples sample rounds).flatMap (fun path=>
      (uniformTuples (List.range N0) q).map (fun queries=>(path,queries)))
    count (outer.flatMap (fun z=>inner.map (fun pair=>(z,pair))))
      (fun pair=>checkedHistoryAccept (strategy pair.1) sizes degrees pair.2.1 pair.2.2)*sample.length≤
      (outerRounds*max N0 2*sample.length^(outerRounds-1))*inner.length*sample.length+
      outer.length*(((List.range rounds).map (fun i=>max (sizes (i+1)) 2)).sum*
        sample.length^rounds*N0^q+sample.length^(rounds+1)*(T-1)^q) := by
  classical
  dsimp only
  let domain:=(List.range N0).map (fun i=>root^i)
  let good:=fun z=>∃ p : Poly K,p.DegLt (degrees 0) ∧
    T≤consistencyMass domain (fun _=>1) (fun x=>jointBetaSource betas sources x z=p.eval x)
  have mass : (domain.map (fun _=>1)).sum=N0 := by
    have eq : ∀ xs : List K,(xs.map (fun _=>1)).sum=xs.length := by
      intro xs
      induction xs with
      | nil => rfl
      | cons x xs ih => simp [ih,Nat.add_comm]
    simpa [domain] using eq domain
  have farBound := joint_beta_candidate_far_count domain sample domainDistinct distinct
    (fun _=>1) 1 (degrees 0) T outerRounds (by intros; omega)
    (by simpa [mass] using (show 2*N0+(degrees 0-1)<3*T by omega))
    (by simpa using interpolation) betas sources affine far
  let inner:=(uniformTuples sample rounds).flatMap (fun path=>
    (uniformTuples (List.range N0) q).map (fun queries=>(path,queries)))
  have bound := finite_product_acceptance_budget (uniformTuples sample outerRounds) inner
    (fun z pair=>checkedHistoryAccept (strategy z) sizes degrees pair.1 pair.2) good sample.length
    (((List.range rounds).map (fun i=>max (sizes (i+1)) 2)).sum*
      sample.length^rounds*N0^q+sample.length^(rounds+1)*(T-1)^q) (by
    intro z hz absent
    have noInitial : ¬indexedChainCandidate N0 sizes degrees (strategy z []).roots
        (strategy z []).challenges (strategy z []).oracles (strategy z []).weights
        (strategy z []).claims T 0 := by
      intro candidate
      obtain ⟨p,degree,agreement⟩ := indexed_initial_candidate_agreement (strategy z [])
        N0 T sizes degrees initial candidate
      apply absent
      refine ⟨p,degree,?_⟩
      rw [unit_mass]
      have transfer : count (List.range N0)
          (fun i=>(strategy z []).oracles 0 i=p.eval ((strategy z []).roots 0^i))=
          count domain (fun x=>jointBetaSource betas sources x z=p.eval x) := by
        simp only [domain,count,List.countP_map,Function.comp_def]
        apply List.countP_congr
        intro i hi
        simp [sourceValues z hz i (List.mem_range.mp hi),initialRoot z hz]
      rwa [transfer] at agreement
    exact checked_history_interactive_acceptance_budget sample distinct (strategy z) N0 T rounds q
      sizes degrees initial positive sizeHalves degreeHalves regime h2
      (fixed z) (weights z) (claim z) (challenge z) noInitial)
  apply Nat.le_trans bound
  have scaled := Nat.add_le_add_right
    (Nat.mul_le_mul_right sample.length (Nat.mul_le_mul_right inner.length farBound))
    ((uniformTuples sample outerRounds).length*(((List.range rounds).map (fun i=>max (sizes (i+1)) 2)).sum*
      sample.length^rounds*N0^q+sample.length^(rounds+1)*(T-1)^q))
  simpa only [domain,List.length_map,List.length_range] using scaled

end NearCompression
