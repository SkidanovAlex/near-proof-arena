import NearCompression.WeightedPCSReplayBound
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

/-- Algebraic prover strategy. Stage i sees exactly i prior fold challenges.
The next oracle may depend on the just drawn challenge. Oracle values here are
fixed functions, not an extraction of a Merkle root. Domain roots are public. -/
structure WeightedPrefixProver (K : Type) [Field K] where
  oracle : Nat → List K → Nat → K
  quadratic : Nat → List K → WhirQuadratic K
  terminal : List K → K

def WeightedPrefixProver.oracles (p : WeightedPrefixProver K) (history : List K) (i : Nat) : Nat→K :=
  p.oracle i (history.take i)

def WeightedPrefixProver.messages (p : WeightedPrefixProver K) (rounds : Nat) (history : List K) :=
  (List.range rounds).map (fun i=>p.quadratic i (history.take i))

def WeightedPrefixProver.strategy (p : WeightedPrefixProver K) (point : List K)
    (initial : K) (roots : Nat→K) :=
  weightedReplayStrategy point initial (p.messages point.length) p.terminal roots p.oracles

omit [Field K] in
private theorem take_prefix (history : List K) {j i : Nat} (h : j≤i) :
    (history.take i).take j=history.take j := by
  simp [List.take_take,Nat.min_eq_left h]

private theorem get_prefix (history : List K) {j i : Nat} (h : j<i) :
    (history.take i).getD j 0=history.getD j 0 := by
  simp [List.getD,h]

theorem weighted_prefix_oracle (p : WeightedPrefixProver K) (history : List K)
    {j i : Nat} (h : j≤i) : p.oracles (history.take i) j=p.oracles history j := by
  simp only [WeightedPrefixProver.oracles,take_prefix history h]

theorem weighted_prefix_source (p : WeightedPrefixProver K) (history : List K) :
    p.oracles history 0=p.oracle 0 [] := by simp [WeightedPrefixProver.oracles]

private theorem scale_prefix (point history : List K) (i : Nat) :
    ∀ j≤i,weightedReplayScale point (history.take i) j=weightedReplayScale point history j := by
  intro j hj
  induction j with
  | zero=>rfl
  | succ j ih=>rw [weightedReplayScale,weightedReplayScale,ih (by omega),get_prefix history (by omega)]

/-- Every historical consistency check at stage j<i uses only prefix i:
its child oracle is allowed to depend on challenge j. -/
theorem weighted_prefix_check (p : WeightedPrefixProver K) (history : List K)
    (sizes : Nat→Nat) (roots : Nat→K) {j i : Nat} (h : j<i) :
    globalRSChainCheck sizes roots (fun k=>(history.take i).getD k 0) (p.oracles (history.take i)) j =
    globalRSChainCheck sizes roots (fun k=>history.getD k 0) (p.oracles history) j := by
  funext y
  simp only [globalRSChainCheck,weighted_prefix_oracle p history (by omega : j≤i),
    weighted_prefix_oracle p history (by omega : j+1≤i),get_prefix history h]

/-- Prefix dependence includes the nonuniform history-generated query mass. -/
theorem weighted_prefix_mass (p : WeightedPrefixProver K) (history : List K)
    (seeds : List Nat) (sizes : Nat→Nat) (roots : Nat→K) (i : Nat) :
    globalChainWeight seeds sizes
      (globalRSChainCheck sizes roots (fun k=>(history.take i).getD k 0) (p.oracles (history.take i))) i =
    globalChainWeight seeds sizes
      (globalRSChainCheck sizes roots (fun k=>history.getD k 0) (p.oracles history)) i := by
  suffices ∀ j≤i,globalChainWeight seeds sizes
      (globalRSChainCheck sizes roots (fun k=>(history.take i).getD k 0) (p.oracles (history.take i))) j =
    globalChainWeight seeds sizes
      (globalRSChainCheck sizes roots (fun k=>history.getD k 0) (p.oracles history)) j from this i (by omega)
  intro j hj
  induction j with
  | zero=>rfl
  | succ j ih=>
    funext y
    simp only [globalChainWeight,ih (by omega)]
    rw [congrFun (weighted_prefix_check p history sizes roots (by omega : j<i)) y]

private theorem sent_prefix (p : WeightedPrefixProver K) (history : List K)
    {i rounds : Nat} (h : i<rounds) :
    weightedReplaySent (p.messages rounds (history.take i)) i =
      weightedReplaySent (p.messages rounds history) i := by
  simp [weightedReplaySent,WeightedPrefixProver.messages,List.getD,h,List.take_take]

/-- Derived causality, with no supplied snapshot-causality premise. The current
quadratic and oracle precede draw i; the child oracle is absent from snapshot i. -/
theorem weighted_prefix_snapshot (p : WeightedPrefixProver K) (point history : List K)
    (initial : K) (roots : Nat→K) (N : Nat) (sizes : Nat→Nat) {i : Nat} (h : i<point.length) :
    (p.strategy point initial roots history).snapshot N sizes i =
      (p.strategy point initial roots (history.take i)).snapshot N sizes i := by
  unfold WeightedPrefixProver.strategy weightedReplayStrategy FoldTranscript.snapshot weightedReplayTranscript
  simp only [weighted_prefix_mass,weighted_prefix_oracle p history (Nat.le_refl i),
    weightedReplayTail,scale_prefix point history i i (Nat.le_refl i),sent_prefix p history h]

/-- The accepted-replay bound instantiated by a prefix-indexed prover. Neither
snapshot causality nor a separate fixed-source premise is required. The oracle
strategy remains an ideal interactive interface, not Merkle-root extraction. -/
theorem weighted_prefix_no_candidate_count [DecidableEq K]
    (sample : List K) (sampleDistinct : sample.Nodup) (point : List K) (initial : K)
    (p : WeightedPrefixProver K) (roots : Nat→K)
    (N T q : Nat) (sizes degrees : Nat→Nat)
    (sizeInitial : sizes 0=N) (positive : ∀ i≤point.length,0<sizes i)
    (sizeHalves : ∀ i<point.length,sizes i=2*sizes (i+1))
    (degreeHalves : ∀ i<point.length,degrees i=2*degrees (i+1))
    (h2 : (2:K)≠0) (regime : 2*N+degrees 0<3*T)
    (pointInjective : ∀ i<point.length,∀ a<sizes (i+1),∀ b<sizes (i+1),roots (i+1)^a=roots (i+1)^b → a=b)
    (nonzero : ∀ i<point.length,∀ y<sizes (i+1),roots i^y≠0)
    (squared : ∀ i<point.length,∀ y<sizes (i+1),roots (i+1)^y=roots i^y*roots i^y)
    (negative : ∀ i<point.length,∀ y<sizes (i+1),roots i^(y+sizes (i+1))= -(roots i^y))
    (terminalDegree : 1≤degrees point.length)
    (terminalAuthenticated : ∀ path∈uniformTuples sample point.length,
      weightedReplayCheck point path ((p.messages point.length) path) initial (p.terminal path)=true →
      ∀ y<sizes point.length,p.oracles path point.length y=p.terminal path) :
    count ((uniformTuples sample point.length).flatMap (fun path=>
      (uniformTuples (List.range N) q).map (fun queries=>(path,queries))))
      (fun pair=>weightedReplayAccept point initial (p.messages point.length) p.terminal roots p.oracles sizes pair.1 pair.2 ∧
        ¬weightedReplayInitialCandidate point N (degrees 0) T (roots 0) initial (p.oracle 0 []))*sample.length≤
      ((List.range point.length).map (fun i=>max (sizes (i+1)) 2)).sum*
        sample.length^point.length*N^q+sample.length^(point.length+1)*(T-1)^q := by
  apply weighted_replay_no_candidate_count sample sampleDistinct point initial
    (p.messages point.length) p.terminal roots p.oracles (p.oracle 0 [])
    (weighted_prefix_source p) N T q sizes degrees sizeInitial positive sizeHalves degreeHalves h2 regime
  · intro path hp i hi
    exact weighted_prefix_snapshot p point path initial roots N sizes hi
  · exact pointInjective
  · exact nonzero
  · exact squared
  · exact negative
  · exact terminalDegree
  · exact terminalAuthenticated
end NearCompression
