import NearCompression.ChosenGKRSourceRecovery
import NearCompression.NearFunctionalFoldAcceptance
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

/-- A wrong full input functional of one prechallenge chosen source tuple
bounds checked weighted sumcheck plus adaptive folding acceptance. Sparse
recovery, constant subtraction and shared functional agreement are derived.
Representative existence, source-oracle identity and terminal authentication
remain premises. The bound uses independent ideal challenges, not Fiat-Shamir. -/
theorem chosen_gkr_terminal_acceptance_count [DecidableEq K] (layout : GKRJointLayout) (metadata : List GKRSourceLane)
    (valid : ∀ lane∈metadata,lane.WellFormed layout)
    (geometry : CanonicalLaneSelectors layout metadata)
    (omega : K) (rootOrder : ∀ j,omega^j=1 ↔ 4*2^layout.commonLog∣j)
    (sample : List K) (sampleDistinct : sample.Nodup)
    (T : Nat) (sources : List (K→K)) (sourceShape : sources.length=metadata.length)
    (existsRep : ∃ polys,JointBetaRepresentative (naturalRSDomain omega (4*2^layout.commonLog)) (fun _=>1)
      (heterogeneousJointDimension layout) (2^layout.commonLog) T
      (metadata.map (heterogeneousJointBeta layout)) sources polys)
    (original : GKRSourceLane→K→K)
    (projection : ∀ i,∀ hi : i<metadata.length,∀ x,
      (sources[i]'(by omega)) x=original metadata[i] (x^(2^(layout.commonLog-(metadata[i].rowLog+metadata[i].packingLog)))))
    (threshold : T≤4*2^layout.commonLog)
    (separation : 2*(4*2^layout.commonLog-T)+2^layout.commonLog≤4*2^layout.commonLog)
    (rowpoints : GKRSourceLane→Nat→K) (left right : Nat→K) (gamma : K)
    (sent : List K→Poly K) (claim : List K→K)
    (constants : List (Nat×K)) (bounds : ∀ entry∈constants,entry.1<2^layout.inputLog)
    (terminalClaim : K)
    (initial : claim []=gkrRemoveConstants layout.inputLog left right gamma constants terminalClaim)
    (queries : Nat) (sizes degrees : Nat → Nat) (roots : Nat → K)
    (provers : List K → WeightedPrefixProver K)
    (sourceValues : ∀ z,∀ i<4*2^layout.commonLog,(provers z).oracle 0 [] i=
      weightedVirtualOracle (functionalBatchCoefficients layout.commonLog
        (liftedHeterogeneousWeights layout.commonLog layout.inputLog metadata rowpoints left right gamma)
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
    (terminalAuthenticated : ∀ z,∀ path∈uniformTuples sample layout.commonLog,
      weightedReplayCheck z path ((provers z).messages layout.commonLog path)
        (claim z) ((provers z).terminal path)=true →
      ∀ y<sizes layout.commonLog,(provers z).oracles path layout.commonLog y=(provers z).terminal path) :
    let polys := chosenJointSourceRepresentative layout metadata (naturalRSDomain omega (4*2^layout.commonLog))
      (2^layout.commonLog) T sources
    let outer := uniformTuples sample layout.commonLog
    let inner := (uniformTuples sample layout.commonLog).flatMap (fun path =>
      (uniformTuples (List.range (4*2^layout.commonLog)) queries).map (fun qs => (path,qs)))
    terminalClaim≠gkrInputFunctional layout.inputLog left right gamma
      (fun i=>gkrScatter (recoveredPrivateSlots layout.commonLog (metadata.zip polys) rowpoints) i+gkrScatter constants i) →
    count (outer.flatMap (fun z => inner.map (fun pair => (z,pair))))
      (fun pair => weightedSumcheckChecks sent claim [] pair.1 ∧
        weightedReplayAccept pair.1 (claim pair.1) ((provers pair.1).messages layout.commonLog)
          (provers pair.1).terminal roots (provers pair.1).oracles sizes pair.2.1 pair.2.2)*sample.length≤
      (2*layout.commonLog)*sample.length^layout.commonLog*inner.length+
      outer.length*(((List.range layout.commonLog).map (fun i => max (sizes (i+1)) 2)).sum*
        sample.length^layout.commonLog*(4*2^layout.commonLog)^queries+
        sample.length^(layout.commonLog+1)*(T-1)^queries) := by
  let domain := naturalRSDomain omega (4*2^layout.commonLog)
  let polys := chosenJointSourceRepresentative layout metadata domain (2^layout.commonLog) T sources
  let entries := metadata.zip polys
  let tables := liftedHeterogeneousWeights layout.commonLog layout.inputLog metadata rowpoints left right gamma
  have representative := chosen_joint_source_representative_valid layout metadata domain
    (2^layout.commonLog) T sources existsRep
  have shape : polys.length=metadata.length := representative.1.trans sourceShape
  have firsts : entries.map Prod.fst=metadata := List.map_fst_zip (by omega)
  have seconds : entries.map Prod.snd=polys := List.map_snd_zip (by omega)
  have sparse := joint_source_entries_sparse layout metadata valid geometry omega rootOrder T sources polys
    sourceShape representative original projection separation
  have shared := joint_representative_shared_functional layout metadata valid geometry domain
    (2^layout.commonLog) T layout.commonLog sources polys sourceShape representative
    (fun _ : Unit => tables) (by intro u; simp [tables,liftedHeterogeneousWeights])
  dsimp only
  intro wrong
  have reduced : claim []≠coefficientTableFunctional layout.commonLog tables polys := by
    intro equal
    apply wrong
    apply (gkr_recovered_terminal_iff layout entries
      (by simpa only [firsts] using valid)
      (by intro entry he; exact representative.2.1 entry.2 (by change entry.2∈polys; rw [←seconds]; exact List.mem_map.mpr ⟨entry,he,rfl⟩))
      sparse rowpoints left right gamma terminalClaim constants bounds).mp
    simpa only [firsts,seconds,←initial] using equal
  exact near_functional_fold_acceptance_count sample sampleDistinct layout.commonLog
    (4*2^layout.commonLog) T queries sizes degrees roots tables sources polys
    (by simpa [rootInitial,naturalRSDomain] using natural_rs_distinct omega _ rootOrder)
    (by simpa [domain,naturalRSDomain,rootInitial,degreeInitial] using shared)
    threshold (by simpa [degreeInitial] using separation) sent claim reduced provers sourceValues
    sizeInitial positive sizeHalves degreeHalves h2 regime pointInjective nonzero squared negative
    terminalDegree terminalAuthenticated

end NearCompression
