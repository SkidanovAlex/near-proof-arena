import NearCompression.GKRConcretePCSCount
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security

/-- Concrete PCS sampling supplies exactly the row and final-block lengths
needed for history reindexing; no verifier premise is needed for those lengths. -/
theorem concrete_pcs_sample_lengths {K : Type} (sample : List K)
    (layout : GKRJointLayout) (queries : Nat) (item)
    (member : item∈gkrConcretePCSSamples sample layout queries) :
    item.1.length=layout.rowCoordinates ∧ item.2.1.1.length=layout.inputLog ∧
      item.2.1.2.1.length=layout.inputLog := by
  simp only [gkrConcretePCSSamples,List.mem_flatMap,List.mem_map] at member
  obtain ⟨rows,hr,block,hb,z,hz,pair,hpair,rfl⟩ := member
  simp only [gkrChallengeBlocks,List.mem_flatMap,List.mem_map] at hb
  obtain ⟨left,hl,right,hrr,gamma,hg,rfl⟩ := hb
  exact ⟨uniform_tuple_member_length sample layout.rowCoordinates rows hr,
    uniform_tuple_member_length sample layout.inputLog left hl,
    uniform_tuple_member_length sample layout.inputLog right hrr⟩

/-- Accepted evaluated-GKR errors embed into the concrete PCS failure event.
The input binding is equality of whole input functions, not merely equality
at the final opening point. No representative existence is assumed. -/
theorem concrete_gkr_error_inclusion {K : Type} [Field K] [DecidableEq K]
    (sample : List K) (layout : GKRJointLayout) (queries : Nat)
    (family : GKRBlockPCSFamily K) (roots : Nat → K) (sizes : Nat → Nat)
    (raw : List K → (m : Nat) → List (GKRBlock K) → GKRLayerStrategy K m)
    (layers : List K → List (List GKRWiringGate)) (inputs : List K → Nat → K)
    (rounds : List Nat) (earlier : List (GKRBlock K))
    (entries : List (GKRSourceLane × Poly K)) (existsRep : Prop)
    (accept : List K → GKRBlock K → List K → List K → List Nat → Prop)
    (inputBinding : ∀ item∈gkrConcretePCSSamples sample layout queries,
      inputs item.1=gkrRecoveredCircuitInput layout.commonLog entries
        (gkrHistoryRowpoints layout (item.1++gkrBlockCoordinates item.2.1)) (family.constants item.1 item.2.1))
    (checks : ∀ item∈gkrConcretePCSSamples sample layout queries,
      accept item.1 item.2.1 item.2.2.1 item.2.2.2.1 item.2.2.2.2 →
      gkrEvaluatedVerifierPath (raw item.1) (layers item.1) []
        (rounds++[layout.inputLog]) (earlier++[item.2.1]) ∧
      gkrBlockPCSChecks layout family roots sizes item.1 item.2.1 item.2.2.1 item.2.2.2.1 item.2.2.2.2) :
    count (gkrConcretePCSSamples sample layout queries) (fun item =>
      accept item.1 item.2.1 item.2.2.1 item.2.2.2.1 item.2.2.2.2 ∧
      (¬existsRep ∨ gkrTerminalMismatch (gkrBindCircuitValues (raw item.1) (inputs item.1) (layers item.1))
        (gkrReverseCircuitValues (inputs item.1) (layers item.1)) 1 []
        (rounds++[layout.inputLog]) (earlier++[item.2.1])))≤
    count (gkrConcretePCSSamples sample layout queries) (fun item =>
      (¬existsRep ∨ gkrHistoryTerminalClaim layout raw earlier (item.1++gkrBlockCoordinates item.2.1)≠
        gkrInputFunctional layout.inputLog
          (gkrHistoryLeft layout (item.1++gkrBlockCoordinates item.2.1))
          (gkrHistoryRight layout (item.1++gkrBlockCoordinates item.2.1))
          (gkrHistoryGamma layout (item.1++gkrBlockCoordinates item.2.1))
          (gkrRecoveredCircuitInput layout.commonLog entries
            (gkrHistoryRowpoints layout (item.1++gkrBlockCoordinates item.2.1))
            ((reindexGKRPCSFamily layout family).constants (item.1++gkrBlockCoordinates item.2.1)))) ∧
      gkrBlockPCSChecks layout family roots sizes item.1 item.2.1 item.2.2.1 item.2.2.2.1 item.2.2.2.2) := by
  apply count_mono_mem
  intro item member accepted
  have verified := checks item member accepted.1
  refine ⟨?_,verified.2⟩
  rcases accepted.2 with absent | mismatch
  · exact Or.inl absent
  · apply Or.inr
    have lengths := concrete_pcs_sample_lengths sample layout queries item member
    have event := gkr_pcs_accepted_mismatch_reindex layout family roots sizes raw (layers item.1)
      rounds earlier item.1 item.2.1 item.2.2.1 item.2.2.2.1 item.2.2.2.2
      lengths.1 lengths.2.1 lengths.2.2 entries verified.1
    dsimp only at event
    rw [inputBinding item member] at mismatch
    exact (event.mp ⟨mismatch,verified.2⟩).1

/-- Apply the actual merged near/far PCS theorem to accepted GKR failure,
including absent representatives. All ideal oracle hypotheses remain explicit. -/
theorem concrete_gkr_accepted_failure_budget {K : Type} [Field K] [DecidableEq K] (layout : GKRJointLayout) (metadata : List GKRSourceLane)
    (valid : ∀ lane∈metadata,lane.WellFormed layout)
    (geometry : CanonicalLaneSelectors layout metadata)
    (omega : K) (rootOrder : ∀ j,omega^j=1 ↔ 4*2^layout.commonLog∣j)
    (sample : List K) (sampleDistinct : sample.Nodup)
    (T : Nat) (sources : List (K→K)) (sourceShape : sources.length=metadata.length)
    (original : GKRSourceLane→K→K)
    (projection : ∀ i,∀ hi : i<metadata.length,∀ x,
      (sources[i]'(by omega)) x=original metadata[i] (x^(2^(layout.commonLog-(metadata[i].rowLog+metadata[i].packingLog)))))
    (threshold : T≤4*2^layout.commonLog) (interpolation : 2^layout.commonLog-1<T)
    (separation : 2*(4*2^layout.commonLog-T)+2^layout.commonLog≤4*2^layout.commonLog)
    (family : GKRBlockPCSFamily K)
    (raw : List K → (m : Nat) → List (GKRBlock K) → GKRLayerStrategy K m)
    (earlier : List (GKRBlock K)) (bounds : ∀ h,∀ entry∈(reindexGKRPCSFamily layout family).constants h,entry.1<2^layout.inputLog)
    (initial : ∀ h,(reindexGKRPCSFamily layout family).claim h []=gkrRemoveConstants layout.inputLog (gkrHistoryLeft layout h) (gkrHistoryRight layout h) (gkrHistoryGamma layout h) ((reindexGKRPCSFamily layout family).constants h) ((gkrHistoryTerminalClaim layout raw earlier) h))
    (queries : Nat) (sizes degrees : Nat → Nat) (roots : Nat → K)
    (sourceValues : ∀ h z,∀ i<4*2^layout.commonLog,((reindexGKRPCSFamily layout family).prover h z).oracle 0 [] i=
      weightedVirtualOracle (functionalBatchCoefficients layout.commonLog
        (liftedHeterogeneousWeights layout.commonLog layout.inputLog metadata (gkrHistoryRowpoints layout h) (gkrHistoryLeft layout h) (gkrHistoryRight layout h) (gkrHistoryGamma layout h))
        (fun j => z.getD j 0)) sources (roots 0^i))
    (sizeInitial : sizes 0=4*2^layout.commonLog)
    (degreeInitial : degrees 0=2^layout.commonLog) (rootInitial : roots 0=omega)
    (positive : ∀ i≤layout.commonLog,0<sizes i)
    (sizeHalves : ∀ i<layout.commonLog,sizes i=2*sizes (i+1))
    (degreeHalves : ∀ i<layout.commonLog,degrees i=2*degrees (i+1))
    (h2 : (2:K)≠0) (regime : 2*(4*2^layout.commonLog)+degrees 0<3*T)
    (pointInjective : ∀ i<layout.commonLog,∀ a<sizes (i+1),∀ b<sizes (i+1),roots (i+1)^a=roots (i+1)^b → a=b)
    (nonzero : ∀ i<layout.commonLog,∀ y<sizes (i+1),roots i^y≠0)
    (squared : ∀ i<layout.commonLog,∀ y<sizes (i+1),roots (i+1)^y=roots i^y*roots i^y)
    (negative : ∀ i<layout.commonLog,∀ y<sizes (i+1),roots i^(y+sizes (i+1))= -(roots i^y))
    (terminalDegree : 1≤degrees layout.commonLog)
    (terminalAuthenticated : ∀ h z,∀ path∈uniformTuples sample layout.commonLog,
      weightedReplayCheck z path (((reindexGKRPCSFamily layout family).prover h z).messages layout.commonLog path)
        ((reindexGKRPCSFamily layout family).claim h z) (((reindexGKRPCSFamily layout family).prover h z).terminal path)=true →
      ∀ y<sizes layout.commonLog,((reindexGKRPCSFamily layout family).prover h z).oracles path layout.commonLog y=((reindexGKRPCSFamily layout family).prover h z).terminal path )
    (layers : List K → List (List GKRWiringGate)) (inputs : List K → Nat → K)
    (rounds : List Nat)
    (accept : List K → GKRBlock K → List K → List K → List Nat → Prop)
    (inputBinding : ∀ item∈gkrConcretePCSSamples sample layout queries,
      inputs item.1=gkrRecoveredCircuitInput layout.commonLog
        (metadata.zip (chosenJointSourceRepresentative layout metadata
          (naturalRSDomain omega (4*2^layout.commonLog)) (2^layout.commonLog) T sources))
        (gkrHistoryRowpoints layout (item.1++gkrBlockCoordinates item.2.1)) (family.constants item.1 item.2.1))
    (checks : ∀ item∈gkrConcretePCSSamples sample layout queries,
      accept item.1 item.2.1 item.2.2.1 item.2.2.2.1 item.2.2.2.2 →
      gkrEvaluatedVerifierPath (raw item.1) (layers item.1) []
        (rounds++[layout.inputLog]) (earlier++[item.2.1]) ∧
      gkrBlockPCSChecks layout family roots sizes item.1 item.2.1 item.2.2.1 item.2.2.2.1 item.2.2.2.2) :
    let N := 4*2^layout.commonLog
    let q := heterogeneousJointDimension layout
    let existsRep := ∃ polys,JointBetaRepresentative (naturalRSDomain omega N) (fun _=>1)
      q (2^layout.commonLog) T (metadata.map (heterogeneousJointBeta layout)) sources polys
    let polys := chosenJointSourceRepresentative layout metadata (naturalRSDomain omega N)
      (2^layout.commonLog) T sources
    let outer := uniformTuples sample q
    let inner := (uniformTuples sample layout.commonLog).flatMap (fun path =>
      (uniformTuples (List.range N) queries).map (fun qs => (path,qs)))
    let foldBudget := ((List.range layout.commonLog).map (fun i => max (sizes (i+1)) 2)).sum*
      sample.length^layout.commonLog*N^queries+sample.length^(layout.commonLog+1)*(T-1)^queries
    let nearBudget := sample.length^(gkrHistoryLength layout)*
      ((2*layout.commonLog)*sample.length^layout.commonLog*inner.length+
        (uniformTuples sample layout.commonLog).length*foldBudget)
    let farBudget := (q*max N 2*sample.length^(q-1))*inner.length*sample.length+outer.length*foldBudget
    count (gkrConcretePCSSamples sample layout queries) (fun item =>
      accept item.1 item.2.1 item.2.2.1 item.2.2.2.1 item.2.2.2.2 ∧
      (¬existsRep ∨ gkrTerminalMismatch (gkrBindCircuitValues (raw item.1) (inputs item.1) (layers item.1))
        (gkrReverseCircuitValues (inputs item.1) (layers item.1)) 1 []
        (rounds++[layout.inputLog]) (earlier++[item.2.1])))*sample.length≤
      max nearBudget farBudget := by
  intro N q existsRep polys outer inner foldBudget nearBudget farBudget
  have included := concrete_gkr_error_inclusion sample layout queries family roots sizes raw layers inputs
    rounds earlier (metadata.zip polys) existsRep accept inputBinding checks
  have numerical := gkr_concrete_joint_failure_count layout metadata valid geometry omega rootOrder sample sampleDistinct
    T sources sourceShape original projection threshold interpolation separation family raw earlier bounds initial
    queries sizes degrees roots sourceValues sizeInitial degreeInitial rootInitial positive sizeHalves degreeHalves
    h2 regime pointInjective nonzero squared negative terminalDegree terminalAuthenticated
  exact Nat.le_trans (Nat.mul_le_mul_right sample.length included) numerical

end NearCompression
