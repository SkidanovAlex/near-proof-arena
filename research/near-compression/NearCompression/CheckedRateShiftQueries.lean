import NearCompression.VirtualFoldCheckedTransfer
import NearCompression.RateShiftQueryTransfer
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

/-- Every member is a normalized close polynomial, even when the list is empty. -/
theorem rate_shift_unique_list_sound (domain : List K) (received : K→K) (D radius : Nat)
    (p : Poly K) (member : p∈rateShiftUniqueList domain received D radius) :
    RateShiftCloseCandidate domain received D radius p := by
  classical
  unfold rateShiftUniqueList at member
  split at member
  next h =>
    have equal : p=Classical.choose h := by simpa using member
    rw [equal]
    exact Classical.choose_spec h
  next h => simp at member

theorem checked_virtual_source_query_bound [DecidableEq K]
    (N T : Nat) (sizes degrees : Nat→Nat) (roots source : Nat→K)
    (weights path : List K) (claim : K) (prover : Nat→List K→WhirQuadratic K)
    (weightShape : weights.length=degrees 0)
    (sizeHalves : ∀ i<path.length,sizes i=2*sizes (i+1))
    (degreeHalves : ∀ i<path.length,degrees i=2*degrees (i+1))
    (h2 : (2:K)≠0) (nonzero : ∀ i<path.length,∀ y<sizes (i+1),roots i^y≠0)
    (squared : ∀ i<path.length,∀ y<sizes (i+1),roots (i+1)^y=roots i^y*roots i^y)
    (negative : ∀ i<path.length,∀ y<sizes (i+1),roots i^(y+sizes (i+1))= -(roots i^y))
    (checked : virtualPrefixEndpointChecks sizes roots source weights claim prover path=true)
    (initial : ¬indexedChainCandidate N sizes degrees roots (fun _=>0) (fun _=>source)
      (fun _=>weights) (fun _=>claim) T 0)
    (good : ¬adaptivePathBad (generalFoldHistoryBad
      (virtualPrefixTranscript sizes roots source weights claim prover) N sizes degrees T) [] path)
    (sizeInitial : sizes 0=N) (minimum : Nat) (threshold : T≤2^path.length*minimum)
    (domain : List K) (received : K→K) (radius q : Nat) (z y : K) :
    count (uniformTuples (List.range (sizes path.length)) q) (fun queries=>
      ∃ p∈rateShiftUniqueList domain received (degrees path.length) radius,
      ¬rateShiftCandidateWrong (virtualPrefixWeights weights path path.length)
        (z::queries.map (fun i=>roots path.length^i)) p
        ((virtualPrefixTranscript sizes roots source weights claim prover path).claims path.length)
        (y::queries.map (virtualFoldOracles sizes roots (fun i=>path.getD i 0) source path.length)))≤(minimum-1)^q := by
  apply rate_shift_query_no_correct_bound
  intro p member functional
  have normalized:=rate_shift_unique_list_sound domain received (degrees path.length) radius p member
  have degree : p.DegLt (degrees path.length) := by
    simpa only [normalized.1] using Poly.degLt_length p
  exact virtual_prefix_checked_no_close N T sizes degrees roots source weights path claim prover
    weightShape sizeHalves degreeHalves h2 nonzero squared negative checked initial good
    sizeInitial minimum threshold p degree functional

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


/-- Exact source-stage experiment: prior challenges, a prefix-dependent next
oracle/OOD claim, then independent source queries. Includes rejecting paths. -/
theorem checked_virtual_source_stage_bound [DecidableEq K]
    (sample : List K) (distinct : sample.Nodup) (N T rounds q minimum radius : Nat)
    (sizes degrees : Nat→Nat) (roots source : Nat→K) (weights : List K) (claim : K)
    (prover : Nat→List K→WhirQuadratic K)
    (nextDomain : List K→List K) (nextOracle : List K→K→K) (z y : List K→K)
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
      (fun _=>weights) (fun _=>claim) T 0) :
    count ((uniformTuples sample rounds).flatMap (fun path=>
      (uniformTuples (List.range (sizes rounds)) q).map (fun queries=>(path,queries))))
      (fun pair=>virtualPrefixEndpointChecks sizes roots source weights claim prover pair.1=true ∧
        ∃ p∈rateShiftUniqueList (nextDomain pair.1) (nextOracle pair.1) (degrees rounds) radius,
        ¬rateShiftCandidateWrong (virtualPrefixWeights weights pair.1 rounds)
          (z pair.1::pair.2.map (fun i=>roots rounds^i)) p
          ((virtualPrefixTranscript sizes roots source weights claim prover pair.1).claims rounds)
          (y pair.1::pair.2.map (virtualFoldOracles sizes roots (fun i=>pair.1.getD i 0) source rounds)))*sample.length≤
      ((List.range rounds).map (fun i=>max (sizes (i+1)) 2)).sum*sample.length^rounds*(sizes rounds)^q+
        sample.length^(rounds+1)*(minimum-1)^q := by
  classical
  let bad:=generalFoldHistoryBad (virtualPrefixTranscript sizes roots source weights claim prover) N sizes degrees T
  let paths:=uniformTuples sample rounds
  let queries:=uniformTuples (List.range (sizes rounds)) q
  let accept:=fun (path : List K) (qs : List Nat)=>virtualPrefixEndpointChecks sizes roots source weights claim prover path=true ∧
    ∃ p∈rateShiftUniqueList (nextDomain path) (nextOracle path) (degrees rounds) radius,
      ¬rateShiftCandidateWrong (virtualPrefixWeights weights path rounds) (z path::qs.map (fun i=>roots rounds^i)) p
        ((virtualPrefixTranscript sizes roots source weights claim prover path).claims rounds)
        (y path::qs.map (virtualFoldOracles sizes roots (fun i=>path.getD i 0) source rounds))
  have localBound : ∀ path∈paths,¬adaptivePathBad bad [] path→count queries (accept path)≤(minimum-1)^q := by
    intro path hp good
    have len : path.length=rounds := by
      have all : ∀ n,∀ xs∈uniformTuples sample n,xs.length=n := by
        intro n
        induction n with
        | zero=>intro xs hx;simpa [uniformTuples] using hx
        | succ n ih=>
          intro xs hx
          simp only [uniformTuples,List.mem_flatMap,List.mem_map] at hx
          obtain ⟨a,ha,rest,hr,rfl⟩:=hx
          simp [ih rest hr]
      exact all rounds path hp
    by_cases checked : virtualPrefixEndpointChecks sizes roots source weights claim prover path=true
    · have bound:=checked_virtual_source_query_bound N T sizes degrees roots source weights path claim prover
        weightShape (by simpa only [len] using sizeHalves) (by simpa only [len] using degreeHalves)
        h2 (by simpa only [len] using nonzero) (by simpa only [len] using squared) (by simpa only [len] using negative)
        checked initial good sizeInitial minimum (by simpa only [len] using threshold)
        (nextDomain path) (nextOracle path) radius q (z path) (y path)
      simpa only [len,accept,checked,true_and] using bound
    · simp [accept,checked,count]
  have badBound:=virtual_prefix_bad_path_bound sample distinct N T rounds sizes degrees roots source weights claim prover
    sizeInitial positive sizeHalves degreeHalves injective regime
  have total:=scaled_conditional_sum paths queries (adaptivePathBad bad []) accept sample.length
    ((minimum-1)^q*sample.length) (fun path hp good=>Nat.mul_le_mul_right sample.length (localBound path hp good))
  have scaled:=Nat.mul_le_mul_right ((sizes rounds)^q) badBound
  have result : (paths.map (fun path=>count queries (accept path))).sum*sample.length≤
      ((List.range rounds).map (fun i=>max (sizes (i+1)) 2)).sum*sample.length^rounds*(sizes rounds)^q+
        sample.length^(rounds+1)*(minimum-1)^q := by
    have plen : paths.length=sample.length^rounds := uniform_tuples_length sample rounds
    have qlen : queries.length=(sizes rounds)^q := by simp [queries,uniform_tuples_length]
    rw [plen,qlen] at total
    simp only [Nat.pow_succ]
    change count paths (adaptivePathBad bad [])*sample.length*((sizes rounds)^q)≤_ at scaled
    grind
  simpa only [count,List.countP_flatMap,List.countP_map,Function.comp_def,paths,queries,accept] using result

end NearCompression
