import NearCompression.TwoTablePCSExperiment
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security

abbrev TwoTablePCSContext (K : Type) := (K × List K) × (K × List K) × K × List (GKRBlock K)

/-- Instantiate the two-table error lift with the actual merged near/far PCS
failure theorem. Source oracles remain fixed while both rowpoint vectors are
jointly sampled. Absence of a representative is included in the failure event.
Ideal oracle/geometry/authentication premises remain explicit. -/
theorem two_table_concrete_pcs_failure_budget {K : Type} [Field K] [DecidableEq K]
    (layout : GKRJointLayout)
    (metadata : List GKRSourceLane)
    (valid : ∀ lane∈metadata,lane.WellFormed layout)
    (geometry : CanonicalLaneSelectors layout metadata)
    (omega : K)
    (rootOrder : ∀ j,omega^j=1 ↔ 4*2^layout.commonLog∣j)
    (sample : List K)
    (sampleDistinct : sample.Nodup)
    (T : Nat)
    (sources : List (K→K))
    (sourceShape : sources.length=metadata.length)
    (original : GKRSourceLane→K→K)
    (projection : ∀ i,∀ hi : i<metadata.length,∀ x,
      (sources[i]'(by omega)) x=original metadata[i] (x^(2^(layout.commonLog-(metadata[i].rowLog+metadata[i].packingLog)))))
    (threshold : T≤4*2^layout.commonLog)
    (interpolation : 2^layout.commonLog-1<T)
    (separation : 2*(4*2^layout.commonLog-T)+2^layout.commonLog≤4*2^layout.commonLog)
    (family : TwoTablePCSContext K → GKRBlockPCSFamily K)
    (raw : TwoTablePCSContext K → List K → (m : Nat) → List (GKRBlock K) → GKRLayerStrategy K m)
    (bounds : ∀ context : TwoTablePCSContext K, ∀ h,∀ entry∈(reindexGKRPCSFamily layout (family context)).constants h,entry.1<2^layout.inputLog)
    (initial : ∀ context : TwoTablePCSContext K, ∀ h,(reindexGKRPCSFamily layout (family context)).claim h []=gkrRemoveConstants layout.inputLog (gkrHistoryLeft layout h) (gkrHistoryRight layout h) (gkrHistoryGamma layout h) ((reindexGKRPCSFamily layout (family context)).constants h) ((gkrHistoryTerminalClaim layout (raw context) context.2.2.2) h))
    (queries : Nat)
    (sizes degrees : Nat → Nat)
    (roots : Nat → K)
    (sourceValues : ∀ context : TwoTablePCSContext K, ∀ h z,∀ i<4*2^layout.commonLog,((reindexGKRPCSFamily layout (family context)).prover h z).oracle 0 [] i=
      weightedVirtualOracle (functionalBatchCoefficients layout.commonLog
        (liftedHeterogeneousWeights layout.commonLog layout.inputLog metadata (gkrHistoryRowpoints layout h) (gkrHistoryLeft layout h) (gkrHistoryRight layout h) (gkrHistoryGamma layout h))
        (fun j => z.getD j 0)) sources (roots 0^i))
    (sizeInitial : sizes 0=4*2^layout.commonLog)
    (degreeInitial : degrees 0=2^layout.commonLog)
    (rootInitial : roots 0=omega)
    (positive : ∀ i≤layout.commonLog,0<sizes i)
    (sizeHalves : ∀ i<layout.commonLog,sizes i=2*sizes (i+1))
    (degreeHalves : ∀ i<layout.commonLog,degrees i=2*degrees (i+1))
    (h2 : (2:K)≠0)
    (regime : 2*(4*2^layout.commonLog)+degrees 0<3*T)
    (pointInjective : ∀ i<layout.commonLog,∀ a<sizes (i+1),∀ b<sizes (i+1),roots (i+1)^a=roots (i+1)^b → a=b)
    (nonzero : ∀ i<layout.commonLog,∀ y<sizes (i+1),roots i^y≠0)
    (squared : ∀ i<layout.commonLog,∀ y<sizes (i+1),roots (i+1)^y=roots i^y*roots i^y)
    (negative : ∀ i<layout.commonLog,∀ y<sizes (i+1),roots i^(y+sizes (i+1))= -(roots i^y))
    (terminalDegree : 1≤degrees layout.commonLog)
    (terminalAuthenticated : ∀ context : TwoTablePCSContext K, ∀ h z,∀ path∈uniformTuples sample layout.commonLog,
      weightedReplayCheck z path (((reindexGKRPCSFamily layout (family context)).prover h z).messages layout.commonLog path)
        ((reindexGKRPCSFamily layout (family context)).claim h z) (((reindexGKRPCSFamily layout (family context)).prover h z).terminal path)=true →
      ∀ y<sizes layout.commonLog,((reindexGKRPCSFamily layout (family context)).prover h z).oracles path layout.commonLog y=((reindexGKRPCSFamily layout (family context)).prover h z).terminal path )
    (layers : TwoTablePCSContext K → List K → List (List GKRWiringGate))
    (inputs : TwoTablePCSContext K → List K → Nat → K)
    (earlierRounds : List Nat)
    (accept : TwoTablePCSContext K → List K → GKRBlock K → List K → List K → List Nat → Prop)
    (inputBinding : ∀ context : TwoTablePCSContext K, ∀ item∈gkrConcretePCSSamples sample layout queries,
      (inputs context) item.1=gkrRecoveredCircuitInput layout.commonLog
        (metadata.zip (chosenJointSourceRepresentative layout metadata
          (naturalRSDomain omega (4*2^layout.commonLog)) (2^layout.commonLog) T sources))
        (gkrHistoryRowpoints layout (item.1++gkrBlockCoordinates item.2.1)) ((family context).constants item.1 item.2.1))
    (checks : ∀ context : TwoTablePCSContext K, ∀ item∈gkrConcretePCSSamples sample layout queries,
      (accept context) item.1 item.2.1 item.2.2.1 item.2.2.2.1 item.2.2.2.2 →
      gkrEvaluatedVerifierPath ((raw context) item.1) ((layers context) item.1) []
        (earlierRounds++[layout.inputLog]) (context.2.2.2++[item.2.1]) ∧
      gkrBlockPCSChecks layout (family context) roots sizes item.1 item.2.1 item.2.2.1 item.2.2.2.1 item.2.2.2.2)
    (firstRows secondRows : Nat) (rowShape : layout.rowCoordinates=firstRows+secondRows)
    (event : LocalChallengePrefix K → LocalChallengePrefix K → K →
      List (GKRBlock K) → List K → List K → List Nat → Prop)
    (eventInclusion : ∀ context : TwoTablePCSContext K,∀ item∈gkrConcretePCSSamples sample layout queries,
      event (context.1,item.1.take firstRows) (context.2.1,item.1.drop firstRows) context.2.2.1
        (context.2.2.2++[item.2.1]) item.2.2.1 item.2.2.2.1 item.2.2.2.2 →
      accept context item.1 item.2.1 item.2.2.1 item.2.2.2.1 item.2.2.2.2 ∧
      (¬(∃ polys,JointBetaRepresentative (naturalRSDomain omega (4*2^layout.commonLog)) (fun _=>1)
        (heterogeneousJointDimension layout) (2^layout.commonLog) T
        (metadata.map (heterogeneousJointBeta layout)) sources polys) ∨
       gkrTerminalMismatch (gkrBindCircuitValues (raw context item.1) (inputs context item.1) (layers context item.1))
        (gkrReverseCircuitValues (inputs context item.1) (layers context item.1)) 1 []
        (earlierRounds++[layout.inputLog]) (context.2.2.2++[item.2.1]))) :
    let N := 4*2^layout.commonLog
    let q := heterogeneousJointDimension layout
    let outer := uniformTuples sample q
    let inner := (uniformTuples sample layout.commonLog).flatMap (fun path =>
      (uniformTuples (List.range N) queries).map (fun qs => (path,qs)))
    let foldBudget := ((List.range layout.commonLog).map (fun i => max (sizes (i+1)) 2)).sum*
      sample.length^layout.commonLog*N^queries+sample.length^(layout.commonLog+1)*(T-1)^queries
    let nearBudget := sample.length^(gkrHistoryLength layout)*
      ((2*layout.commonLog)*sample.length^layout.commonLog*inner.length+
        (uniformTuples sample layout.commonLog).length*foldBudget)
    let farBudget := (q*max N 2*sample.length^(q-1))*inner.length*sample.length+outer.length*foldBudget
    count ((decodedLocalPrefixes sample firstRows).flatMap (fun p=>
      (decodedLocalPrefixes sample secondRows).flatMap (fun q=>
        (twoTablePCSContinuations sample layout earlierRounds queries).map (fun r=>(p,q,r)))))
      (fun x=>event x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2.1 x.2.2.2.2.2.2)*sample.length ≤
      (airLocalInitialChallenges sample firstRows).length*
        ((airLocalInitialChallenges sample secondRows).length*
          (sample.length*((gkrChallengePaths sample earlierRounds).length*max nearBudget farBudget))) := by
  intro N q outer inner foldBudget nearBudget farBudget
  apply two_table_gkr_pcs_joint_budget sample layout firstRows secondRows rowShape
    earlierRounds queries event sample.length (max nearBudget farBudget)
  intro first hf second hs rho hr earlier he
  let context : TwoTablePCSContext K := (first,second,rho,earlier)
  have numerical := concrete_gkr_accepted_failure_budget layout metadata valid geometry omega rootOrder sample sampleDistinct T sources sourceShape original projection threshold interpolation separation (family context) (raw context) context.2.2.2 (bounds context) (initial context) queries sizes degrees roots (sourceValues context) sizeInitial degreeInitial rootInitial positive sizeHalves degreeHalves h2 regime pointInjective nonzero squared negative terminalDegree (terminalAuthenticated context) (layers context) (inputs context) earlierRounds (accept context) (inputBinding context) (checks context)
  dsimp only at numerical
  apply Nat.le_trans (Nat.mul_le_mul_right sample.length (count_mono_mem _ ?_)) numerical
  intro item member accepted
  exact eventInclusion context item member accepted

end NearCompression
