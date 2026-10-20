import NearCompression.ChosenGKRHistoryAcceptance
import NearCompression.GKRHistoryFarAcceptance
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

/-- One joint-experiment bound without a representative-existence premise.
Acceptance together with either absence of a prechallenge representative or
a wrong full recovered GKR input is bounded by the maximum of the near/far
budgets. Existence is fixed before challenges, so no union penalty is needed.
This is still an ideal authenticated-oracle theorem, not end-to-end soundness. -/
theorem gkr_joint_failure_acceptance_count [DecidableEq K] (layout : GKRJointLayout) (metadata : List GKRSourceLane)
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
    (sent : List K → List K→Poly K) (claim : List K → List K→K)
    (constants : List K → List (Nat×K)) (bounds : ∀ h,∀ entry∈constants h,entry.1<2^layout.inputLog)
    (terminalClaim : List K → K)
    (initial : ∀ h,claim h []=gkrRemoveConstants layout.inputLog (gkrHistoryLeft layout h) (gkrHistoryRight layout h) (gkrHistoryGamma layout h) (constants h) (terminalClaim h))
    (queries : Nat) (sizes degrees : Nat → Nat) (roots : Nat → K)
    (provers : List K → List K → WeightedPrefixProver K)
    (sourceValues : ∀ h z,∀ i<4*2^layout.commonLog,(provers h z).oracle 0 [] i=
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
      weightedReplayCheck z path ((provers h z).messages layout.commonLog path)
        (claim h z) ((provers h z).terminal path)=true →
      ∀ y<sizes layout.commonLog,(provers h z).oracles path layout.commonLog y=(provers h z).terminal path) :
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
    count (outer.flatMap (fun z => inner.map (fun pair => (z,pair))))
      (fun pair =>
        let h := pair.1.take (gkrHistoryLength layout)
        let z := pair.1.drop (gkrHistoryLength layout)
        (¬existsRep ∨ terminalClaim h≠gkrInputFunctional layout.inputLog
          (gkrHistoryLeft layout h) (gkrHistoryRight layout h) (gkrHistoryGamma layout h)
          (fun i => gkrScatter (recoveredPrivateSlots layout.commonLog (metadata.zip polys)
            (gkrHistoryRowpoints layout h)) i+gkrScatter (constants h) i)) ∧
        weightedSumcheckChecks (sent h) (claim h) [] z ∧
        weightedReplayAccept z (claim h z) ((provers h z).messages layout.commonLog)
          (provers h z).terminal roots (provers h z).oracles sizes pair.2.1 pair.2.2)*sample.length≤
      max nearBudget farBudget := by
  classical
  dsimp only
  by_cases existsRep : ∃ polys,JointBetaRepresentative
      (naturalRSDomain omega (4*2^layout.commonLog)) (fun _=>1)
      (heterogeneousJointDimension layout) (2^layout.commonLog) T
      (metadata.map (heterogeneousJointBeta layout)) sources polys
  · have near := chosen_gkr_history_acceptance_count layout metadata valid geometry omega rootOrder
      sample sampleDistinct (gkrHistoryLength layout) T sources sourceShape existsRep original projection
      threshold separation (gkrHistoryRowpoints layout) (gkrHistoryLeft layout) (gkrHistoryRight layout)
      (gkrHistoryGamma layout) sent claim constants bounds terminalClaim initial queries sizes degrees roots
      provers sourceValues sizeInitial degreeInitial rootInitial positive sizeHalves degreeHalves h2 regime
      pointInjective nonzero squared negative terminalDegree terminalAuthenticated
    apply Nat.le_trans _ (Nat.le_max_left _ _)
    apply Nat.le_trans _ near
    apply Nat.mul_le_mul_right sample.length
    exact count_mono _ (fun pair accepted => ⟨accepted.1.resolve_left (by simpa using existsRep),accepted.2⟩)
  · let initialFar := fun (z : List K) => claim (z.take (gkrHistoryLength layout)) (z.drop (gkrHistoryLength layout))
    let proversFar := fun (z : List K) => provers (z.take (gkrHistoryLength layout)) (z.drop (gkrHistoryLength layout))
    have far := gkr_history_far_acceptance_count sample sampleDistinct layout metadata valid
      (4*2^layout.commonLog) T queries sizes degrees roots sources
      (by simpa [naturalRSDomain,rootInitial,degreeInitial] using existsRep)
      initialFar proversFar (by
        intro z hz i hi
        have length := uniform_tuple_member_length sample (heterogeneousJointDimension layout) z hz
        rw [show (proversFar z).oracle 0 [] i=weightedVirtualOracle
          (functionalBatchCoefficients layout.commonLog
            (gkrHistoryTables layout metadata (z.take (gkrHistoryLength layout)))
            (fun j => (z.drop (gkrHistoryLength layout)).getD j 0)) sources (roots 0^i)
          from sourceValues _ _ i hi]
        exact gkr_joint_split_oracle layout metadata valid sources z length (roots 0^i))
      (by simpa [rootInitial,naturalRSDomain] using natural_rs_distinct omega _ rootOrder)
      (by simpa [degreeInitial] using interpolation) sizeInitial positive sizeHalves degreeHalves
      h2 regime pointInjective nonzero squared negative terminalDegree (by
        intro z hz path hp checked
        have length := uniform_tuple_member_length sample (heterogeneousJointDimension layout) z hz
        rw [gkr_pcs_point_eq_drop layout z length] at checked
        exact terminalAuthenticated _ _ path hp checked)
    apply Nat.le_trans _ (Nat.le_max_right _ _)
    apply Nat.le_trans _ far
    apply Nat.mul_le_mul_right sample.length
    apply count_mono_mem
    intro pair member accepted
    have hz : pair.1∈uniformTuples sample (heterogeneousJointDimension layout) := by
      obtain ⟨z,hz,equal⟩ := List.mem_flatMap.mp member
      obtain ⟨p,hp,rfl⟩ := List.mem_map.mp equal
      exact hz
    have length := uniform_tuple_member_length sample (heterogeneousJointDimension layout) pair.1 hz
    rw [gkr_pcs_point_eq_drop layout pair.1 length]
    exact accepted.2.2

end NearCompression
