import NearCompression.WeightedPCSReplay
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

/-- A scalar candidate for the already fixed virtual source and equality
functional. This is the result to be extracted, not a verifier check. -/
def weightedReplayInitialCandidate (point : List K) (N D T : Nat) (omega initial : K)
    (source : Nat→K) : Prop :=
  ∃ p : Poly K,p.DegLt D ∧ scalarRSResidual (equalityWeights point) p=initial ∧
    T≤count (List.range N) (fun i=>source i=p.eval (omega^i))

private theorem unit_cap_mass (domain : List Nat) (weight : Nat→Nat) (event : Nat→Prop)
    (cap : ∀ x∈domain,weight x≤1) : consistencyMass domain weight event≤count domain event := by
  classical
  induction domain with
  | nil=>simp [consistencyMass,count]
  | cons x xs ih=>
    have head:=cap x (by simp)
    have tail:=ih (fun y hy=>cap y (by simp [hy]))
    simp only [consistencyMass,count,List.map_cons,List.sum_cons,List.countP_cons] at tail ⊢
    by_cases h:event x <;> simp_all <;> omega

theorem weighted_replay_initial_candidate (point challenges : List K) (sent : List (WhirQuadratic K))
    (initial terminal : K) (roots : Nat→K) (oracles : Nat→Nat→K)
    (N T : Nat) (sizes degrees : Nat→Nat) (sizeInitial : sizes 0=N)
    (candidate : let tr:=weightedReplayTranscript point challenges sent initial terminal roots oracles
      indexedChainCandidate N sizes degrees tr.roots tr.challenges tr.oracles tr.weights tr.claims T 0) :
    weightedReplayInitialCandidate point N (degrees 0) T (roots 0) initial (oracles 0) := by
  classical
  obtain ⟨p,degree,residual,mass⟩:=candidate
  let tr:=weightedReplayTranscript point challenges sent initial terminal roots oracles
  have cap : ∀ y∈List.range N,globalChainWeight (List.range N) sizes
      (globalRSChainCheck sizes tr.roots tr.challenges tr.oracles) 0 y≤1 := by
    intro y hy
    simpa using global_chain_weight_cap N sizes (globalRSChainCheck sizes tr.roots tr.challenges tr.oracles)
      0 sizeInitial (by intro j hj;omega) y (by rw [sizeInitial];exact List.mem_range.mp hy)
  refine ⟨p,degree,?_,?_⟩
  · simpa only [weightedReplayTranscript,weighted_replay_initial_weights,weightedReplayClaim] using residual
  · rw [sizeInitial] at mass
    exact Nat.le_trans mass (unit_cap_mass _ _ _ cap)

def weightedReplayStrategy (point : List K) (initial : K)
    (messages : List K→List (WhirQuadratic K)) (terminals : List K→K)
    (roots : Nat→K) (oracles : List K→Nat→Nat→K) (history : List K) : FoldTranscript K :=
  weightedReplayTranscript point history (messages history) initial (terminals history) roots (oracles history)

def weightedReplayAccept [DecidableEq K] (point : List K) (initial : K)
    (messages : List K→List (WhirQuadratic K)) (terminals : List K→K)
    (roots : Nat→K) (oracles : List K→Nat→Nat→K) (sizes : Nat→Nat)
    (path : List K) (queries : List Nat) : Prop :=
  weightedReplayCheck point path (messages path) initial (terminals path)=true ∧
    allQueriesPass (globalChainPass sizes
      (globalRSChainCheck sizes roots (fun i=>path.getD i 0) (oracles path)) point.length) queries

/-- Complete ideal-interactive accepted-replay/no-initial-candidate bound.
No caller candidate-absence premise: it is part of the counted error event.
The fixed-source oracle interface, authenticated terminal, actual causal
snapshot and ideal independent sampling remain explicit. No scale division. -/
theorem weighted_replay_no_candidate_count [DecidableEq K]
    (sample : List K) (sampleDistinct : sample.Nodup) (point : List K) (initial : K)
    (messages : List K→List (WhirQuadratic K)) (terminals : List K→K)
    (roots : Nat→K) (oracles : List K→Nat→Nat→K) (source : Nat→K)
    (fixedSource : ∀ history,(oracles history) 0=source)
    (N T q : Nat) (sizes degrees : Nat→Nat)
    (sizeInitial : sizes 0=N) (positive : ∀ i≤point.length,0<sizes i)
    (sizeHalves : ∀ i<point.length,sizes i=2*sizes (i+1))
    (degreeHalves : ∀ i<point.length,degrees i=2*degrees (i+1))
    (h2 : (2:K)≠0) (regime : 2*N+degrees 0<3*T)
    (causal : ∀ path∈uniformTuples sample point.length,∀ i<point.length,
      (weightedReplayStrategy point initial messages terminals roots oracles path).snapshot N sizes i=
      (weightedReplayStrategy point initial messages terminals roots oracles (path.take i)).snapshot N sizes i)
    (pointInjective : ∀ i<point.length,∀ a<sizes (i+1),∀ b<sizes (i+1),roots (i+1)^a=roots (i+1)^b → a=b)
    (nonzero : ∀ i<point.length,∀ y<sizes (i+1),roots i^y≠0)
    (squared : ∀ i<point.length,∀ y<sizes (i+1),roots (i+1)^y=roots i^y*roots i^y)
    (negative : ∀ i<point.length,∀ y<sizes (i+1),roots i^(y+sizes (i+1))= -(roots i^y))
    (terminalDegree : 1≤degrees point.length)
    (terminalAuthenticated : ∀ path∈uniformTuples sample point.length,
      weightedReplayCheck point path (messages path) initial (terminals path)=true →
      ∀ y<sizes point.length,oracles path point.length y=terminals path) :
    count ((uniformTuples sample point.length).flatMap (fun path=>
      (uniformTuples (List.range N) q).map (fun queries=>(path,queries))))
      (fun pair=>weightedReplayAccept point initial messages terminals roots oracles sizes pair.1 pair.2 ∧
        ¬weightedReplayInitialCandidate point N (degrees 0) T (roots 0) initial source)*sample.length≤
      ((List.range point.length).map (fun i=>max (sizes (i+1)) 2)).sum*
        sample.length^point.length*N^q+sample.length^(point.length+1)*(T-1)^q := by
  classical
  by_cases candidate : weightedReplayInitialCandidate point N (degrees 0) T (roots 0) initial source
  · simp [count,candidate]
  · let strategy:=weightedReplayStrategy point initial messages terminals roots oracles
    have bound := checked_interactive_unique_fold_soundness sample sampleDistinct strategy N T point.length q
      sizes degrees sizeInitial positive sizeHalves degreeHalves h2 regime causal
      (by intro path hp i hi;rfl) (by
        intro path hp checks indexed
        have extracted := weighted_replay_initial_candidate point path (messages path) initial (terminals path)
          roots (oracles path) N T sizes degrees sizeInitial indexed
        rw [fixedSource path] at extracted
        exact candidate extracted)
    apply Nat.le_trans ?_ bound
    apply Nat.mul_le_mul_right
    apply count_mono_mem
    intro pair member accepted
    have pathMember : pair.1∈uniformTuples sample point.length := by
      simp only [List.mem_flatMap,List.mem_map] at member
      obtain ⟨path,hpath,queries,hqueries,same⟩:=member
      rw [←same]
      exact hpath
    obtain ⟨replay,queries⟩:=accepted.1
    refine ⟨⟨?_,?_⟩,queries⟩
    · apply weighted_replay_transcript_checks point pair.1 (messages pair.1) initial (terminals pair.1)
        roots (oracles pair.1) N T sizes degrees replay nonzero squared negative terminalDegree
      exact terminalAuthenticated pair.1 pathMember replay
    · intro i hi
      exact ⟨pointInjective i hi,weighted_replay_sent_degree (messages (pair.1.take i)) i⟩
end NearCompression
