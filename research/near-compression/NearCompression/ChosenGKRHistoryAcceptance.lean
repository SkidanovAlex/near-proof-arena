import NearCompression.ChosenGKRSourceRecovery
import NearCompression.NearHistoryFoldAcceptance
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

/-- Full recovered GKR input failure AND checked PCS acceptance on the joint
history/PCS sample space. The chosen tuple precedes all history-dependent
rowpoints, GKR weights, constants and claims. Constant subtraction, sparse
recovery and shared representation are derived, not independent certificates.
Ideal sampling, representative existence and oracle authentication remain. -/
theorem chosen_gkr_history_acceptance_count [DecidableEq K] (layout : GKRJointLayout) (metadata : List GKRSourceLane)
    (valid : ∀ lane∈metadata,lane.WellFormed layout)
    (geometry : CanonicalLaneSelectors layout metadata)
    (omega : K) (rootOrder : ∀ j,omega^j=1 ↔ 4*2^layout.commonLog∣j)
    (sample : List K) (sampleDistinct : sample.Nodup)
    (earlier T : Nat) (sources : List (K→K)) (sourceShape : sources.length=metadata.length)
    (existsRep : ∃ polys,JointBetaRepresentative (naturalRSDomain omega (4*2^layout.commonLog)) (fun _=>1)
      (heterogeneousJointDimension layout) (2^layout.commonLog) T
      (metadata.map (heterogeneousJointBeta layout)) sources polys)
    (original : GKRSourceLane→K→K)
    (projection : ∀ i,∀ hi : i<metadata.length,∀ x,
      (sources[i]'(by omega)) x=original metadata[i] (x^(2^(layout.commonLog-(metadata[i].rowLog+metadata[i].packingLog)))))
    (threshold : T≤4*2^layout.commonLog)
    (separation : 2*(4*2^layout.commonLog-T)+2^layout.commonLog≤4*2^layout.commonLog)
    (rowpoints : List K → GKRSourceLane→Nat→K) (left right : List K → Nat→K) (gamma : List K → K)
    (sent : List K → List K→Poly K) (claim : List K → List K→K)
    (constants : List K → List (Nat×K)) (bounds : ∀ h,∀ entry∈constants h,entry.1<2^layout.inputLog)
    (terminalClaim : List K → K)
    (initial : ∀ h,claim h []=gkrRemoveConstants layout.inputLog (left h) (right h) (gamma h) (constants h) (terminalClaim h))
    (queries : Nat) (sizes degrees : Nat → Nat) (roots : Nat → K)
    (provers : List K → List K → WeightedPrefixProver K)
    (sourceValues : ∀ h z,∀ i<4*2^layout.commonLog,(provers h z).oracle 0 [] i=
      weightedVirtualOracle (functionalBatchCoefficients layout.commonLog
        (liftedHeterogeneousWeights layout.commonLog layout.inputLog metadata (rowpoints h) (left h) (right h) (gamma h))
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
    let polys := chosenJointSourceRepresentative layout metadata (naturalRSDomain omega (4*2^layout.commonLog))
      (2^layout.commonLog) T sources
    let inner := (uniformTuples sample layout.commonLog).flatMap (fun path =>
      (uniformTuples (List.range (4*2^layout.commonLog)) queries).map (fun qs => (path,qs)))
    count ((uniformTuples sample (earlier+layout.commonLog)).flatMap
      (fun z => inner.map (fun pair => (z,pair))))
      (fun pair =>
        let h := pair.1.take earlier
        let z := pair.1.drop earlier
        terminalClaim h≠gkrInputFunctional layout.inputLog (left h) (right h) (gamma h)
          (fun i => gkrScatter (recoveredPrivateSlots layout.commonLog (metadata.zip polys) (rowpoints h)) i+
            gkrScatter (constants h) i) ∧
        weightedSumcheckChecks (sent h) (claim h) [] z ∧
        weightedReplayAccept z (claim h z) ((provers h z).messages layout.commonLog)
          (provers h z).terminal roots (provers h z).oracles sizes pair.2.1 pair.2.2)*sample.length≤
      sample.length^earlier*((2*layout.commonLog)*sample.length^layout.commonLog*inner.length+
        (uniformTuples sample layout.commonLog).length*
          (((List.range layout.commonLog).map (fun i => max (sizes (i+1)) 2)).sum*
            sample.length^layout.commonLog*(4*2^layout.commonLog)^queries+
            sample.length^(layout.commonLog+1)*(T-1)^queries)) := by
  let domain := naturalRSDomain omega (4*2^layout.commonLog)
  let polys := chosenJointSourceRepresentative layout metadata domain (2^layout.commonLog) T sources
  let entries := metadata.zip polys
  let tables := fun h => liftedHeterogeneousWeights layout.commonLog layout.inputLog metadata
    (rowpoints h) (left h) (right h) (gamma h)
  have representative := chosen_joint_source_representative_valid layout metadata domain
    (2^layout.commonLog) T sources existsRep
  have shape : polys.length=metadata.length := representative.1.trans sourceShape
  have firsts : entries.map Prod.fst=metadata := List.map_fst_zip (by omega)
  have seconds : entries.map Prod.snd=polys := List.map_snd_zip (by omega)
  have sparse := joint_source_entries_sparse layout metadata valid geometry omega rootOrder T sources polys
    sourceShape representative original projection separation
  have shared := joint_representative_shared_functional layout metadata valid geometry domain
    (2^layout.commonLog) T layout.commonLog sources polys sourceShape representative
    tables (by intro h; simp [tables,liftedHeterogeneousWeights])
  have bound := near_history_fold_acceptance_count sample sampleDistinct earlier layout.commonLog
    (4*2^layout.commonLog) T queries sizes degrees roots tables sources polys
    (by simpa [rootInitial,naturalRSDomain] using natural_rs_distinct omega _ rootOrder)
    (by simpa [domain,naturalRSDomain,rootInitial,degreeInitial] using shared)
    threshold (by simpa [degreeInitial] using separation) sent claim provers sourceValues
    sizeInitial positive sizeHalves degreeHalves h2 regime pointInjective nonzero squared negative
    terminalDegree terminalAuthenticated
  dsimp only
  apply Nat.le_trans _ bound
  apply Nat.mul_le_mul_right sample.length
  apply count_mono
  intro pair accepted
  refine ⟨?_,accepted.2⟩
  intro equal
  apply accepted.1
  let h := pair.1.take earlier
  apply (gkr_recovered_terminal_iff layout entries
    (by simpa only [firsts] using valid)
    (by intro entry he; exact representative.2.1 entry.2 (by change entry.2∈polys; rw [←seconds]; exact List.mem_map.mpr ⟨entry,he,rfl⟩))
    sparse (rowpoints h) (left h) (right h) (gamma h) (terminalClaim h) (constants h) (bounds h)).mp
  simpa only [firsts,seconds,←initial h] using equal

end NearCompression
