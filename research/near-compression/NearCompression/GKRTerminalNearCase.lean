import NearCompression.GKRRecoveredTerminal
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

/-- A wrong full GKR input obligation, after the actual sequential constant
subtraction, has the existing recovered-PCS near-case bound. The SAME decoded
polynomial tuple determines the full input and the PCS functional; no separate
private-claim discrepancy premise is supplied. The representative/sparse-image
conditions are still explicit, and this does not cover the far case or hash
commitment authentication. Earlier GKR history may select these fixed weights
and strategy, before the independent PCS sumcheck challenges. -/
theorem gkr_terminal_recovered_near_count (layout : GKRJointLayout)
    (entries : List (GKRSourceLane × Poly K))
    (valid : ∀ lane∈entries.map Prod.fst,lane.WellFormed layout)
    (geometry : CanonicalLaneSelectors layout (entries.map Prod.fst))
    (domain sample : List K) (domainDistinct : domain.Nodup) (sampleDistinct : sample.Nodup)
    (T : Nat) (sources : List (K → K)) (sourceShape : sources.length=entries.length)
    (representative : JointBetaRepresentative domain (fun _ => 1) (heterogeneousJointDimension layout)
      (2^layout.commonLog) T ((entries.map Prod.fst).map (heterogeneousJointBeta layout)) sources (entries.map Prod.snd))
    (sparse : ∀ entry∈entries,∀ i,¬2^(layout.commonLog-(entry.1.rowLog+entry.1.packingLog))∣i → entry.2.coeff i=0)
    (rowpoints : GKRSourceLane → Nat → K) (left right : Nat → K) (gamma : K)
    (threshold : T≤domain.length) (separation : 2*(domain.length-T)+2^layout.commonLog≤domain.length)
    (sent : List K → Poly K) (claim : List K → K)
    (constants : List (Nat × K)) (bounds : ∀ entry∈constants,entry.1<2^layout.inputLog)
    (terminalClaim : K)
    (initial : claim []=gkrRemoveConstants layout.inputLog left right gamma constants terminalClaim)
    (wrong : terminalClaim≠gkrInputFunctional layout.inputLog left right gamma
      (fun i => gkrScatter (recoveredPrivateSlots layout.commonLog entries rowpoints) i+gkrScatter constants i)) :
    let tables := liftedHeterogeneousWeights layout.commonLog layout.inputLog (entries.map Prod.fst) rowpoints left right gamma
    count (uniformTuples sample layout.commonLog) (fun path => weightedSumcheckChecks sent claim [] path ∧
      ∃ candidate : Poly K,candidate.DegLt (2^layout.commonLog) ∧
        scalarRSResidual (equalityWeights path) candidate=claim path ∧
        T≤count domain (fun x => weightedVirtualOracle
          (functionalBatchCoefficients layout.commonLog tables (fun i => path.getD i 0)) sources x=candidate.eval x)) *sample.length≤
      (2*layout.commonLog)*sample.length^layout.commonLog := by
  have reduced : claim []≠recoveredHeterogeneousClaim layout.commonLog layout.inputLog
      entries rowpoints left right gamma := by
    rw [initial,gkr_remove_constants_exact _ _ _ _ _ _ bounds,
      ←recovered_private_vector_functional layout entries valid rowpoints left right gamma]
    exact gkr_known_input_subtraction layout.inputLog left right gamma terminalClaim
      (gkrScatter (recoveredPrivateSlots layout.commonLog entries rowpoints)) (gkrScatter constants) wrong
  exact recovered_heterogeneous_near_count layout entries valid geometry domain sample
    domainDistinct sampleDistinct T sources sourceShape representative sparse rowpoints
    left right gamma threshold separation sent claim reduced
end NearCompression
