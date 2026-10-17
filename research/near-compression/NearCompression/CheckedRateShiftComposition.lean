import NearCompression.CheckedRateShiftQueries
import NearCompression.RateShiftContinuationComposition
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

private theorem scaled_conditional_sum {A B : Type} (outer : List A) (inner : List B)
    (bad : A→Prop) (accept : A→B→Prop) (scale limit : Nat)
    (good : ∀ a∈outer,¬bad a→count inner (accept a)*scale≤limit) :
    (outer.map (fun a=>count inner (accept a))).sum*scale≤
      count outer bad*inner.length*scale+outer.length*limit := by
  classical
  induction outer with
  | nil => simp [count]
  | cons a rest ih =>
    have tail:=ih (fun b hb=>good b (by simp [hb]))
    have head:=good a (by simp)
    have maximum : count inner (accept a)≤inner.length := List.countP_le_length
    have scaled:=Nat.mul_le_mul_right scale maximum
    simp only [List.map_cons,List.sum_cons,count,List.countP_cons,List.length_cons] at tail head scaled ⊢
    by_cases h : bad a <;> simp_all <;> grind



/-- Ideal rate-shift experiment: checked virtual folds, prequery next oracle,
source queries, mixing, and checked continuation. No commitment or QROM claim. -/
theorem checked_rate_shift_composition [DecidableEq K]
    (sample : List K) (distinct : sample.Nodup) (N T rounds q minimum radius : Nat)
    (sizes degrees : Nat→Nat) (roots source : Nat→K) (weights : List K) (claim : K)
    (prover : Nat→List K→WhirQuadratic K)
    (nextOracle : List K→K→K) (z y : List K→K)
    (sizeInitial : sizes 0=N) (weightShape : weights.length=degrees 0)
    (positive : ∀ i≤rounds,0<sizes i)
    (sizeHalves : ∀ i<rounds,sizes i=2*sizes (i+1))
    (degreeHalves : ∀ i<rounds,degrees i=2*degrees (i+1))
    (injective : ∀ i<rounds,∀ a<sizes (i+1),∀ b<sizes (i+1),roots (i+1)^a=roots (i+1)^b→a=b)
    (regime : 2*N+degrees 0<3*T) (threshold : T≤2^rounds*minimum)
    (h2 : (2:K)≠0) (nonzero : ∀ i<rounds,∀ j<sizes (i+1),roots i^j≠0)
    (squared : ∀ i<rounds,∀ j<sizes (i+1),roots (i+1)^j=roots i^j*roots i^j)
    (negative : ∀ i<rounds,∀ j<sizes (i+1),roots i^(j+sizes (i+1))= -(roots i^j))
    (initial : ¬indexedChainCandidate N sizes degrees roots (fun _=>0) (fun _=>source)
      (fun _=>weights) (fun _=>claim) T 0)
    (mixSample foldSample : List K) (mixDistinct : mixSample.Nodup) (foldDistinct : foldSample.Nodup)
    (Nc Tc rc qc : Nat) (csizes cdegrees : Nat→Nat) (omega : K)
    (csize : csizes 0=Nc) (cdegree : cdegrees 0=degrees rounds)
    (cpositive : ∀ i≤rc,0<csizes i)
    (csizeHalves : ∀ i<rc,csizes i=2*csizes (i+1))
    (cdegreeHalves : ∀ i<rc,cdegrees i=2*cdegrees (i+1))
    (cregime : 2*Nc+cdegrees 0<3*Tc)
    (domainDistinct : ((List.range Nc).map (fun i=>omega^i)).Nodup)
    (radiusFits : Nc≤Tc+radius) (unique : 2*radius+degrees rounds≤Nc)
    (strategy : List K→List Nat→K→List K→GeneralFoldTranscript K)
    (causal : ∀ prior queries gamma,∀ path∈uniformTuples foldSample rc,∀ i<rc,
      (strategy prior queries gamma path).snapshot Nc csizes i=
        (strategy prior queries gamma (path.take i)).snapshot Nc csizes i)
    (challengeValues : ∀ prior queries gamma,∀ path∈uniformTuples foldSample rc,∀ i<rc,
      (strategy prior queries gamma path).challenges i=path[i]?.getD 0)
    (bindings : ∀ prior queries gamma,∀ path∈uniformTuples foldSample rc,
      generalFoldPathChecks (strategy prior queries gamma) Nc csizes cdegrees Tc rc path →
      (strategy prior queries gamma path).roots 0=omega ∧
      (∀ i<Nc,(strategy prior queries gamma path).oracles 0 i=nextOracle prior (omega^i)) ∧
      (strategy prior queries gamma path).weights 0=
        rateShiftAccumulateWeights (virtualPrefixWeights weights prior rounds) gamma gamma
          (z prior::queries.map (fun i=>roots rounds^i)) ∧
      (strategy prior queries gamma path).claims 0=rateShiftAccumulatedClaim
        ((virtualPrefixTranscript sizes roots source weights claim prover prior).claims rounds)
        (y prior::queries.map (virtualFoldOracles sizes roots (fun i=>prior.getD i 0) source rounds)) gamma) :
    let outer := (uniformTuples sample rounds).flatMap (fun path=>
      (uniformTuples (List.range (sizes rounds)) q).map (fun queries=>(path,queries)))
    let continuations := (uniformTuples foldSample rc).flatMap (fun path=>
      (uniformTuples (List.range Nc) qc).map (fun queries=>(path,queries)))
    let inner := mixSample.flatMap (fun gamma=>continuations.map (fun c=>(gamma,c)))
    let sourceLimit := ((List.range rounds).map (fun i=>max (sizes (i+1)) 2)).sum*
      sample.length^rounds*(sizes rounds)^q+sample.length^(rounds+1)*(minimum-1)^q
    let continuationLimit := (q+1)*continuations.length*foldSample.length+
      mixSample.length*(((List.range rc).map (fun i=>max (csizes (i+1)) 2)).sum*
        foldSample.length^rc*Nc^qc+foldSample.length^(rc+1)*(Tc-1)^qc)
    count (outer.flatMap (fun a=>inner.map (fun b=>(a,b))))
      (fun pair=>virtualPrefixEndpointChecks sizes roots source weights claim prover pair.1.1=true ∧
        generalCheckedFoldAccept (strategy pair.1.1 pair.1.2 pair.2.1) Nc csizes cdegrees Tc rc
          pair.2.2.1 pair.2.2.2)*sample.length*foldSample.length ≤
      sourceLimit*inner.length*foldSample.length+outer.length*continuationLimit*sample.length := by
  classical
  dsimp only
  let outer := (uniformTuples sample rounds).flatMap (fun path=>
    (uniformTuples (List.range (sizes rounds)) q).map (fun queries=>(path,queries)))
  let continuations := (uniformTuples foldSample rc).flatMap (fun path=>
    (uniformTuples (List.range Nc) qc).map (fun queries=>(path,queries)))
  let inner := mixSample.flatMap (fun gamma=>continuations.map (fun c=>(gamma,c)))
  let bad := fun (a : List K×List Nat)=>
    virtualPrefixEndpointChecks sizes roots source weights claim prover a.1=true ∧
    ∃ p∈rateShiftUniqueList ((List.range Nc).map (fun i=>omega^i)) (nextOracle a.1) (degrees rounds) radius,
      ¬rateShiftCandidateWrong (virtualPrefixWeights weights a.1 rounds)
        (z a.1::a.2.map (fun i=>roots rounds^i)) p
        ((virtualPrefixTranscript sizes roots source weights claim prover a.1).claims rounds)
        (y a.1::a.2.map (virtualFoldOracles sizes roots (fun i=>a.1.getD i 0) source rounds))
  let accept := fun (a : List K×List Nat) (b : K×(List K×List Nat))=>
    virtualPrefixEndpointChecks sizes roots source weights claim prover a.1=true ∧
      generalCheckedFoldAccept (strategy a.1 a.2 b.1) Nc csizes cdegrees Tc rc b.2.1 b.2.2
  have sourceBound := checked_virtual_source_stage_bound sample distinct N T rounds q minimum radius
    sizes degrees roots source weights claim prover (fun _=>(List.range Nc).map (fun i=>omega^i))
    nextOracle z y sizeInitial weightShape positive sizeHalves degreeHalves injective regime threshold
    h2 nonzero squared negative initial
  let limit := (q+1)*continuations.length*foldSample.length+
    mixSample.length*(((List.range rc).map (fun i=>max (csizes (i+1)) 2)).sum*
      foldSample.length^rc*Nc^qc+foldSample.length^(rc+1)*(Tc-1)^qc)
  have good : ∀ a∈outer,¬bad a→count inner (accept a)*foldSample.length≤limit := by
    intro a member notBad
    by_cases checked : virtualPrefixEndpointChecks sizes roots source weights claim prover a.1=true
    · have noCorrect : ∀ p∈rateShiftUniqueList ((List.range Nc).map (fun i=>omega^i))
          (nextOracle a.1) (degrees rounds) radius,
          rateShiftCandidateWrong (virtualPrefixWeights weights a.1 rounds)
            (z a.1::a.2.map (fun i=>roots rounds^i)) p
            ((virtualPrefixTranscript sizes roots source weights claim prover a.1).claims rounds)
            (y a.1::a.2.map (virtualFoldOracles sizes roots (fun i=>a.1.getD i 0) source rounds)) := by
        intro p hp
        apply Classical.byContradiction
        intro wrong
        exact notBad ⟨checked,p,hp,wrong⟩
      have queryMember : a.2∈uniformTuples (List.range (sizes rounds)) q := by
        simp only [outer,List.mem_flatMap,List.mem_map] at member
        obtain ⟨path,hp,queries,hq,equal⟩:=member
        cases equal
        exact hq
      have tupleLength : ∀ n,∀ xs∈uniformTuples (List.range (sizes rounds)) n,xs.length=n := by
        intro n
        induction n with
        | zero=>intro xs hx;simpa [uniformTuples] using hx
        | succ n ih=>
          intro xs hx
          simp only [uniformTuples,List.mem_flatMap,List.mem_map] at hx
          obtain ⟨a,ha,rest,hr,rfl⟩:=hx
          simp [ih rest hr]
      have len:=tupleLength q a.2 queryMember
      have bound:=rate_shift_continuation_composition mixSample foldSample mixDistinct foldDistinct
        (strategy a.1 a.2) Nc (degrees rounds) Tc radius rc qc csizes cdegrees csize cdegree
        cpositive csizeHalves cdegreeHalves h2 cregime omega (nextOracle a.1)
        domainDistinct radiusFits unique (virtualPrefixWeights weights a.1 rounds)
        (z a.1::a.2.map (fun i=>roots rounds^i))
        (y a.1::a.2.map (virtualFoldOracles sizes roots (fun i=>a.1.getD i 0) source rounds))
        ((virtualPrefixTranscript sizes roots source weights claim prover a.1).claims rounds)
        (Nat.le_of_eq (virtual_prefix_weight_length weights a.1 degrees rounds weightShape degreeHalves).symm)
        (by simp) noCorrect (causal a.1 a.2) (challengeValues a.1 a.2) (bindings a.1 a.2)
      simpa only [accept,checked,true_and,List.length_cons,List.length_map,len,limit,inner,continuations] using bound
    · simp [accept,checked,count,limit]
  have total:=scaled_conditional_sum outer inner bad accept foldSample.length limit good
  have scaledTotal:=Nat.mul_le_mul_right sample.length total
  have scaledSource:=Nat.mul_le_mul_right (inner.length*foldSample.length) sourceBound
  have result : (outer.map (fun a=>count inner (accept a))).sum*sample.length*foldSample.length≤
      (((List.range rounds).map (fun i=>max (sizes (i+1)) 2)).sum*
        sample.length^rounds*(sizes rounds)^q+sample.length^(rounds+1)*(minimum-1)^q)*
        inner.length*foldSample.length+outer.length*limit*sample.length := by
    change count outer bad*sample.length*(inner.length*foldSample.length)≤_ at scaledSource
    grind
  simpa only [count,List.countP_flatMap,List.countP_map,Function.comp_def,outer,inner,continuations,accept,limit] using result
end NearCompression
