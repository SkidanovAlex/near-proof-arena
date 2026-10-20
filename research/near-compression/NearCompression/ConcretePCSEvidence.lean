import NearCompression.TwoTableConcretePCS
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security

/-- Ideal-oracle/authentication and verifier hypotheses of the concrete PCS
soundness theorem. No numerical failure inequality is stored in this record. -/
structure ConcreteTwoTablePCSEvidence (layout : GKRJointLayout) (sample : List Fp8) (sampleDistinct : sample.Nodup)
    (T queries : Nat) (sizes : Nat → Nat) (earlierRounds : List Nat) (firstRows secondRows : Nat)
    (event : LocalChallengePrefix Fp8 → LocalChallengePrefix Fp8 → Fp8 →
      List (GKRBlock Fp8) → List Fp8 → List Fp8 → List Nat → Prop) where
  metadata : List GKRSourceLane
  valid : ∀ lane∈metadata,lane.WellFormed layout
  geometry : CanonicalLaneSelectors layout metadata
  omega : Fp8
  rootOrder : ∀ j,omega^j=1 ↔ 4*2^layout.commonLog∣j
  sources : List (Fp8→Fp8)
  sourceShape : sources.length=metadata.length
  original : GKRSourceLane→Fp8→Fp8
  projection : ∀ i,∀ hi : i<metadata.length,∀ x,
      (sources[i]'(by omega)) x=original metadata[i] (x^(2^(layout.commonLog-(metadata[i].rowLog+metadata[i].packingLog))))
  threshold : T≤4*2^layout.commonLog
  interpolation : 2^layout.commonLog-1<T
  separation : 2*(4*2^layout.commonLog-T)+2^layout.commonLog≤4*2^layout.commonLog
  family : TwoTablePCSContext Fp8 → GKRBlockPCSFamily Fp8
  raw : TwoTablePCSContext Fp8 → List Fp8 → (m : Nat) → List (GKRBlock Fp8) → GKRLayerStrategy Fp8 m
  bounds : ∀ context : TwoTablePCSContext Fp8, ∀ h,∀ entry∈(reindexGKRPCSFamily layout (family context)).constants h,entry.1<2^layout.inputLog
  initial : ∀ context : TwoTablePCSContext Fp8, ∀ h,(reindexGKRPCSFamily layout (family context)).claim h []=gkrRemoveConstants layout.inputLog (gkrHistoryLeft layout h) (gkrHistoryRight layout h) (gkrHistoryGamma layout h) ((reindexGKRPCSFamily layout (family context)).constants h) ((gkrHistoryTerminalClaim layout (raw context) context.2.2.2) h)
  degrees : Nat → Nat
  roots : Nat → Fp8
  sourceValues : ∀ context : TwoTablePCSContext Fp8, ∀ h z,∀ i<4*2^layout.commonLog,((reindexGKRPCSFamily layout (family context)).prover h z).oracle 0 [] i=
      weightedVirtualOracle (functionalBatchCoefficients layout.commonLog
        (liftedHeterogeneousWeights layout.commonLog layout.inputLog metadata (gkrHistoryRowpoints layout h) (gkrHistoryLeft layout h) (gkrHistoryRight layout h) (gkrHistoryGamma layout h))
        (fun j => z.getD j 0)) sources (roots 0^i)
  sizeInitial : sizes 0=4*2^layout.commonLog
  degreeInitial : degrees 0=2^layout.commonLog
  rootInitial : roots 0=omega
  positive : ∀ i≤layout.commonLog,0<sizes i
  sizeHalves : ∀ i<layout.commonLog,sizes i=2*sizes (i+1)
  degreeHalves : ∀ i<layout.commonLog,degrees i=2*degrees (i+1)
  h2 : (2:Fp8)≠0
  regime : 2*(4*2^layout.commonLog)+degrees 0<3*T
  pointInjective : ∀ i<layout.commonLog,∀ a<sizes (i+1),∀ b<sizes (i+1),roots (i+1)^a=roots (i+1)^b → a=b
  nonzero : ∀ i<layout.commonLog,∀ y<sizes (i+1),roots i^y≠0
  squared : ∀ i<layout.commonLog,∀ y<sizes (i+1),roots (i+1)^y=roots i^y*roots i^y
  negative : ∀ i<layout.commonLog,∀ y<sizes (i+1),roots i^(y+sizes (i+1))= -(roots i^y)
  terminalDegree : 1≤degrees layout.commonLog
  terminalAuthenticated : ∀ context : TwoTablePCSContext Fp8, ∀ h z,∀ path∈uniformTuples sample layout.commonLog,
      weightedReplayCheck z path (((reindexGKRPCSFamily layout (family context)).prover h z).messages layout.commonLog path)
        ((reindexGKRPCSFamily layout (family context)).claim h z) (((reindexGKRPCSFamily layout (family context)).prover h z).terminal path)=true →
      ∀ y<sizes layout.commonLog,((reindexGKRPCSFamily layout (family context)).prover h z).oracles path layout.commonLog y=((reindexGKRPCSFamily layout (family context)).prover h z).terminal path
  layers : TwoTablePCSContext Fp8 → List Fp8 → List (List GKRWiringGate)
  inputs : TwoTablePCSContext Fp8 → List Fp8 → Nat → Fp8
  accept : TwoTablePCSContext Fp8 → List Fp8 → GKRBlock Fp8 → List Fp8 → List Fp8 → List Nat → Prop
  inputBinding : ∀ context : TwoTablePCSContext Fp8, ∀ item∈gkrConcretePCSSamples sample layout queries,
      (inputs context) item.1=gkrRecoveredCircuitInput layout.commonLog
        (metadata.zip (chosenJointSourceRepresentative layout metadata
          (naturalRSDomain omega (4*2^layout.commonLog)) (2^layout.commonLog) T sources))
        (gkrHistoryRowpoints layout (item.1++gkrBlockCoordinates item.2.1)) ((family context).constants item.1 item.2.1)
  checks : ∀ context : TwoTablePCSContext Fp8, ∀ item∈gkrConcretePCSSamples sample layout queries,
      (accept context) item.1 item.2.1 item.2.2.1 item.2.2.2.1 item.2.2.2.2 →
      gkrEvaluatedVerifierPath ((raw context) item.1) ((layers context) item.1) []
        (earlierRounds++[layout.inputLog]) (context.2.2.2++[item.2.1]) ∧
      gkrBlockPCSChecks layout (family context) roots sizes item.1 item.2.1 item.2.2.1 item.2.2.2.1 item.2.2.2.2
  rowShape : layout.rowCoordinates=firstRows+secondRows
  eventInclusion : ∀ context : TwoTablePCSContext Fp8,∀ item∈gkrConcretePCSSamples sample layout queries,
      event (context.1,item.1.take firstRows) (context.2.1,item.1.drop firstRows) context.2.2.1
        (context.2.2.2++[item.2.1]) item.2.2.1 item.2.2.2.1 item.2.2.2.2 →
      accept context item.1 item.2.1 item.2.2.1 item.2.2.2.1 item.2.2.2.2 ∧
      (¬(∃ polys,JointBetaRepresentative (naturalRSDomain omega (4*2^layout.commonLog)) (fun _=>1)
        (heterogeneousJointDimension layout) (2^layout.commonLog) T
        (metadata.map (heterogeneousJointBeta layout)) sources polys) ∨
       gkrTerminalMismatch (gkrBindCircuitValues (raw context item.1) (inputs context item.1) (layers context item.1))
        (gkrReverseCircuitValues (inputs context item.1) (layers context item.1)) 1 []
        (earlierRounds++[layout.inputLog]) (context.2.2.2++[item.2.1]))

def concreteTwoTablePCSBudget (layout : GKRJointLayout) (sample : List Fp8)
    (T queries : Nat) (sizes : Nat → Nat) (earlierRounds : List Nat) (firstRows secondRows : Nat) : Nat :=
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
    (airLocalInitialChallenges sample firstRows).length*
        ((airLocalInitialChallenges sample secondRows).length*
          (sample.length*((gkrChallengePaths sample earlierRounds).length*max nearBudget farBudget)))

/-- The existing concrete near/far theorem computes the failure budget. -/
theorem concrete_two_table_evidence_bound (layout : GKRJointLayout) (sample : List Fp8) (sampleDistinct : sample.Nodup)
    (T queries : Nat) (sizes : Nat → Nat) (earlierRounds : List Nat) (firstRows secondRows : Nat)
    (event : LocalChallengePrefix Fp8 → LocalChallengePrefix Fp8 → Fp8 →
      List (GKRBlock Fp8) → List Fp8 → List Fp8 → List Nat → Prop)
    (c : ConcreteTwoTablePCSEvidence layout sample sampleDistinct T queries sizes earlierRounds firstRows secondRows event) :
    count ((decodedLocalPrefixes sample firstRows).flatMap (fun p=>
      (decodedLocalPrefixes sample secondRows).flatMap (fun q=>
        (twoTablePCSContinuations sample layout earlierRounds queries).map (fun r=>(p,q,r)))))
      (fun x=>event x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2.1 x.2.2.2.2.2.2)*sample.length ≤
      concreteTwoTablePCSBudget layout sample T queries sizes earlierRounds firstRows secondRows := by
  exact two_table_concrete_pcs_failure_budget
    layout c.metadata c.valid c.geometry c.omega c.rootOrder sample sampleDistinct T c.sources c.sourceShape c.original c.projection c.threshold c.interpolation c.separation c.family c.raw c.bounds c.initial queries sizes c.degrees c.roots c.sourceValues c.sizeInitial c.degreeInitial c.rootInitial c.positive c.sizeHalves c.degreeHalves c.h2 c.regime c.pointInjective c.nonzero c.squared c.negative c.terminalDegree c.terminalAuthenticated c.layers c.inputs earlierRounds c.accept c.inputBinding c.checks firstRows secondRows c.rowShape event c.eventInclusion

end NearCompression
