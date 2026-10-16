import NearCompression.GKRHistoryPCSFamily
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security

def gkrConcretePCSSamples {K : Type} (sample : List K) (layout : GKRJointLayout) (queries : Nat) :=
  (uniformTuples sample layout.rowCoordinates).flatMap (fun rows =>
    (gkrChallengeBlocks sample layout.inputLog).flatMap (fun block =>
      (uniformTuples sample layout.commonLog).flatMap (fun z =>
        ((uniformTuples sample layout.commonLog).flatMap (fun path =>
          (uniformTuples (List.range (4*2^layout.commonLog)) queries).map (fun qs => (path,qs)))).map
            (fun pair => (rows,block,z,pair)))))

/-- Exact accepted-event transport, including weighted sumcheck and folding
checks. Both branches of an arbitrary history failure predicate are retained. -/
theorem gkr_concrete_pcs_event_count {K : Type} [Field K] [DecidableEq K]
    (sample : List K) (layout : GKRJointLayout) (queries : Nat) (family : GKRBlockPCSFamily K)
    (roots : Nat → K) (sizes : Nat → Nat) (failure : List K → Prop) :
    count (gkrConcretePCSSamples sample layout queries) (fun item =>
      failure (item.1++gkrBlockCoordinates item.2.1) ∧
      gkrBlockPCSChecks layout family roots sizes item.1 item.2.1 item.2.2.1 item.2.2.2.1 item.2.2.2.2)=
    count ((uniformTuples sample (heterogeneousJointDimension layout)).flatMap (fun z =>
      ((uniformTuples sample layout.commonLog).flatMap (fun path =>
        (uniformTuples (List.range (4*2^layout.commonLog)) queries).map (fun qs => (path,qs)))).map (fun pair => (z,pair))))
      (fun pair => failure (pair.1.take (gkrHistoryLength layout)) ∧
        gkrHistoryPCSChecks layout (reindexGKRPCSFamily layout family) roots sizes
          (pair.1.take (gkrHistoryLength layout)) (pair.1.drop (gkrHistoryLength layout)) pair.2.1 pair.2.2) := by
  classical
  rw [←gkr_rows_block_pcs_coordinates sample layout]
  simp only [gkrConcretePCSSamples,count,List.countP_flatMap,List.countP_map,Function.comp_def,List.flatMap_assoc,List.flatMap_map]
  congr 1
  apply List.map_congr_left
  intro rows hr
  have rowLength := uniform_tuple_member_length sample layout.rowCoordinates rows hr
  congr 1
  apply List.map_congr_left
  intro block hb
  simp only [gkrChallengeBlocks,List.mem_flatMap,List.mem_map] at hb
  obtain ⟨left,hl,right,hrr,gamma,hg,rfl⟩ := hb
  have leftLength := uniform_tuple_member_length sample layout.inputLog left hl
  have rightLength := uniform_tuple_member_length sample layout.inputLog right hrr
  congr 1
  apply List.map_congr_left
  intro z _
  have split := gkr_joint_history_suffix_split layout rows (left,right,gamma) z rowLength leftLength rightLength
  simp only [split.1,split.2,
    gkr_pcs_checks_reindex layout family roots sizes rows (left,right,gamma) z _ _ rowLength leftLength rightLength]
  congr 1
  apply List.map_congr_left
  intro path _
  congr 1
  funext qs
  exact decide_eq_decide.mpr Iff.rfl

/-- Invoke the merged PCS near/far bound on concrete row/block samples.
The absent-representative branch is retained. Source, geometry and terminal
authentication assumptions remain explicit; no computational claim is made. -/
theorem gkr_concrete_joint_failure_count {K : Type} [Field K] [DecidableEq K] (layout : GKRJointLayout) (metadata : List GKRSourceLane)
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
      ∀ y<sizes layout.commonLog,((reindexGKRPCSFamily layout family).prover h z).oracles path layout.commonLog y=((reindexGKRPCSFamily layout family).prover h z).terminal path) :
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
    let failure := fun h =>
      (¬existsRep ∨ gkrHistoryTerminalClaim layout raw earlier h≠gkrInputFunctional layout.inputLog
        (gkrHistoryLeft layout h) (gkrHistoryRight layout h) (gkrHistoryGamma layout h)
        (gkrRecoveredCircuitInput layout.commonLog (metadata.zip polys) (gkrHistoryRowpoints layout h)
          ((reindexGKRPCSFamily layout family).constants h)))
    count (gkrConcretePCSSamples sample layout queries) (fun item =>
      failure (item.1++gkrBlockCoordinates item.2.1) ∧
      gkrBlockPCSChecks layout family roots sizes item.1 item.2.1 item.2.2.1 item.2.2.2.1 item.2.2.2.2)*sample.length≤
      max nearBudget farBudget := by
  intro N q existsRep polys outer inner foldBudget nearBudget farBudget failure
  rw [gkr_concrete_pcs_event_count sample layout queries family roots sizes failure]
  exact gkr_joint_failure_acceptance_count layout metadata valid geometry omega rootOrder sample sampleDistinct
    T sources sourceShape original projection threshold interpolation separation
    (reindexGKRPCSFamily layout family).sent (reindexGKRPCSFamily layout family).claim
    (reindexGKRPCSFamily layout family).constants bounds (gkrHistoryTerminalClaim layout raw earlier) initial
    queries sizes degrees roots (reindexGKRPCSFamily layout family).prover sourceValues
    sizeInitial degreeInitial rootInitial positive sizeHalves degreeHalves h2 regime pointInjective nonzero
    squared negative terminalDegree terminalAuthenticated

end NearCompression
