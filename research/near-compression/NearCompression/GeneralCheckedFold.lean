import NearCompression.GeneralInteractiveFold
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security

structure GeneralFoldTranscriptChecks {K : Type} [Field K] (tr : GeneralFoldTranscript K)
    (N0 : Nat) (sizes degrees : Nat → Nat) (T rounds : Nat) : Prop where
  weightShapes : ∀ i<rounds,(tr.evenWeights i).length=(tr.oddWeights i).length
  parentWeights : ∀ i<rounds,tr.weights i=rsInterleave (tr.evenWeights i) (tr.oddWeights i)
  nextWeights : ∀ i<rounds,tr.weights (i+1)=generalFoldWeights (tr.evenWeights i) (tr.oddWeights i) (tr.challenges i)
  parentClaims : ∀ i<rounds,tr.claims i=(tr.sent i).eval 0+(tr.sent i).eval 1
  nextClaims : ∀ i<rounds,tr.claims (i+1)=(tr.sent i).eval (tr.challenges i)
  nonzero : ∀ i<rounds,∀ y<sizes (i+1),tr.roots i^y≠0
  squared : ∀ i<rounds,∀ y<sizes (i+1),tr.roots (i+1)^y=tr.roots i^y*tr.roots i^y
  negative : ∀ i<rounds,∀ y<sizes (i+1),tr.roots i^(y+sizes (i+1))= -(tr.roots i^y)
  shape : tr.terminal.length≤degrees rounds
  terminalValues : ∀ y<sizes rounds,tr.oracles rounds y=(Poly.mk tr.terminal).eval (tr.roots rounds^y)
  terminalResidual : scalarRSResidual (tr.weights rounds) (Poly.mk tr.terminal)=tr.claims rounds

def generalFoldPrechallengeChecks {K : Type} [Field K] (tr : GeneralFoldTranscript K)
    (sizes : Nat → Nat) (stage : Nat) : Prop :=
  (∀ a<sizes (stage+1),∀ b<sizes (stage+1),
    tr.roots (stage+1)^a=tr.roots (stage+1)^b → a=b) ∧ (tr.sent stage).DegLt 3

noncomputable def generalCheckedFoldBad {K : Type} [Field K]
    (strategy : List K → GeneralFoldTranscript K) (N0 : Nat) (sizes degrees : Nat → Nat)
    (T : Nat) (history : List K) (r : K) : Prop :=
  generalFoldPrechallengeChecks (strategy history) sizes history.length ∧
    generalFoldHistoryBad strategy N0 sizes degrees T history r

def generalFoldPathChecks {K : Type} [Field K] (strategy : List K → GeneralFoldTranscript K)
    (N0 : Nat) (sizes degrees : Nat → Nat) (T rounds : Nat) (path : List K) : Prop :=
  GeneralFoldTranscriptChecks (strategy path) N0 sizes degrees T rounds ∧
    ∀ i<rounds,generalFoldPrechallengeChecks (strategy (path.take i)) sizes i

/-- Actual checked transcript and all of its sampled global-chain queries. -/
def generalCheckedFoldAccept {K : Type} [Field K] (strategy : List K → GeneralFoldTranscript K)
    (N0 : Nat) (sizes degrees : Nat → Nat) (T rounds : Nat)
    (path : List K) (queries : List Nat) : Prop :=
  generalFoldPathChecks strategy N0 sizes degrees T rounds path ∧
    allQueriesPass (generalFoldHistoryQuery strategy sizes rounds path) queries

/-- A malformed prechallenge message/domain rejects for every query tuple,
including the empty tuple. -/
theorem general_checked_fold_reject_prefix {K : Type} [Field K]
    (strategy : List K → GeneralFoldTranscript K) (N0 : Nat) (sizes degrees : Nat → Nat)
    (T rounds : Nat) (path : List K) (queries : List Nat) (i : Nat) (hi : i<rounds)
    (invalid : ¬generalFoldPrechallengeChecks (strategy (path.take i)) sizes i) :
    ¬generalCheckedFoldAccept strategy N0 sizes degrees T rounds path queries := by
  intro accepted
  exact invalid (accepted.1.2 i hi)

/-- Failed terminal/algebraic checks reject without any polynomial candidate
or domain assumptions on the rejected transcript. -/
theorem general_checked_fold_reject_terminal {K : Type} [Field K]
    (strategy : List K → GeneralFoldTranscript K) (N0 : Nat) (sizes degrees : Nat → Nat)
    (T rounds : Nat) (path : List K) (queries : List Nat)
    (invalid : ¬GeneralFoldTranscriptChecks (strategy path) N0 sizes degrees T rounds) :
    ¬generalCheckedFoldAccept strategy N0 sizes degrees T rounds path queries := by
  intro accepted
  exact invalid accepted.1.1

private theorem path_no_bad {A : Type} (bad : List A → A → Prop)
    (history path : List A) (default : A) (good : ¬adaptivePathBad bad history path) :
    ∀ i<path.length,¬bad (history++path.take i) (path[i]?.getD default) := by
  induction path generalizing history with
  | nil => simp
  | cons a rest ih =>
    intro i hi
    have first : ¬bad history a := fun h => good (Or.inl h)
    have tail : ¬adaptivePathBad bad (history++[a]) rest := fun h => good (Or.inr h)
    cases i with
    | zero => simpa using first
    | succ i =>
      have h := ih (history++[a]) tail i (by simpa using hi)
      simpa [List.take_succ_cons,List.append_assoc] using h

private theorem tuple_length {A : Type} (sample : List A) (n : Nat)
    (path : List A) (mem : path∈uniformTuples sample n) : path.length=n := by
  induction n generalizing path with
  | zero => simpa [uniformTuples] using mem
  | succ n ih =>
    simp only [uniformTuples,List.mem_flatMap,List.mem_map] at mem
    obtain ⟨a,ha,rest,hr,rfl⟩ := mem
    simp [ih rest hr]

private theorem adaptive_bounds_from_index {A : Type} (sample : List A)
    (bad : List A → A → Prop) (error : Nat → Nat)
    (history : List A) (remaining : Nat)
    (bound : ∀ h : List A,h.length<history.length+remaining →
      count sample (bad h)≤error h.length) :
    AdaptiveRoundBounds sample bad history ((List.range remaining).map (fun i => error (history.length+i))) := by
  induction remaining generalizing history with
  | zero => trivial
  | succ n ih =>
    rw [List.range_succ_eq_map]
    simp only [List.map_cons,List.map_map,Nat.add_zero]
    constructor
    · exact bound history (by omega)
    · intro a ha
      have next := ih (history++[a]) (by
        intro h hh
        apply bound h
        simp only [List.length_append,List.length_singleton] at hh
        omega)
      simpa [List.length_append,Function.comp_def,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using next

/-- Literal accepted-pair bound for arbitrary adaptive strategies, including
invalid/aborting branches. Prechallenge failures are rejected and contribute
zero extraction bad events; only actually checked terminal paths use the
source no-candidate reduction. No extraction hypothesis remains. -/
theorem general_checked_interactive_fold_soundness {K : Type} [Field K]
    (sample : List K) (sampleDistinct : sample.Nodup)
    (strategy : List K → GeneralFoldTranscript K) (N0 T rounds q : Nat)
    (sizes degrees : Nat → Nat)
    (sizeInitial : sizes 0=N0) (positive : ∀ i≤rounds,0<sizes i)
    (sizeHalves : ∀ i<rounds,sizes i=2*sizes (i+1))
    (degreeHalves : ∀ i<rounds,degrees i=2*degrees (i+1))
    (h2 : (2:K)≠0) (regime : 2*N0+degrees 0<3*T)
    (causal : ∀ path∈uniformTuples sample rounds,∀ i<rounds,
      (strategy path).snapshot N0 sizes i=(strategy (path.take i)).snapshot N0 sizes i)
    (challengeValues : ∀ path∈uniformTuples sample rounds,∀ i<rounds,
      (strategy path).challenges i=path[i]?.getD 0)
    (initial : ∀ path∈uniformTuples sample rounds,
      generalFoldPathChecks strategy N0 sizes degrees T rounds path →
      ¬indexedChainCandidate N0 sizes degrees (strategy path).roots
        (strategy path).challenges (strategy path).oracles (strategy path).weights
        (strategy path).claims T 0) :
    count ((uniformTuples sample rounds).flatMap (fun path =>
      (uniformTuples (List.range N0) q).map (fun queries => (path,queries))))
      (fun pair => generalCheckedFoldAccept strategy N0 sizes degrees T rounds pair.1 pair.2)*sample.length ≤
      ((List.range rounds).map (fun i => max (sizes (i+1)) 2)).sum*
        sample.length^rounds*N0^q + sample.length^(rounds+1)*(T-1)^q := by
  classical
  let bad := generalCheckedFoldBad strategy N0 sizes degrees T
  let checkedQuery : List K → Nat → Prop := fun path seed =>
    generalFoldPathChecks strategy N0 sizes degrees T rounds path ∧
      generalFoldHistoryQuery strategy sizes rounds path seed
  have localBound : ∀ history : List K,history.length<rounds →
      count sample (bad history)≤max (sizes (history.length+1)) 2 := by
    intro history hh
    by_cases checks : generalFoldPrechallengeChecks (strategy history) sizes history.length
    · have subset : count sample (bad history)≤
          count sample (generalFoldHistoryBad strategy N0 sizes degrees T history) :=
        count_mono sample (fun _ h => h.2)
      apply Nat.le_trans subset
      exact general_global_chain_bad_count sample sampleDistinct N0 sizes degrees
        (strategy history).roots (strategy history).challenges (strategy history).oracles
        history.length T sizeInitial (fun j hj => positive j (by omega))
        (fun j hj => sizeHalves j (by omega)) (fun j hj => degreeHalves j (by omega))
        checks.1 ((strategy history).evenWeights history.length)
        ((strategy history).oddWeights history.length)
        ((strategy history).sent history.length) checks.2 regime
    · have zero : count sample (bad history)=0 := by
        simp [count,bad,generalCheckedFoldBad,checks]
      omega
  have bounds := adaptive_bounds_from_index sample bad
    (fun i => max (sizes (i+1)) 2) [] rounds (by simpa using localBound)
  have good : ∀ path∈uniformTuples sample rounds,¬adaptivePathBad bad [] path →
      count (List.range N0) (checkedQuery path)≤T-1 := by
    intro path hp hg
    by_cases pathChecks : generalFoldPathChecks strategy N0 sizes degrees T rounds path
    · have len := tuple_length sample rounds path hp
      have noEvents := path_no_bad bad [] path (0:K) hg
      have cert := pathChecks.1
      have noBad : ∀ i<rounds,¬generalIndexedFoldBad (sizes (i+1)) (degrees (i+1)) T
          (globalChainWeight (List.range N0) sizes
            (globalRSChainCheck sizes (strategy path).roots (strategy path).challenges (strategy path).oracles) i)
          ((strategy path).oracles i) ((strategy path).roots i) ((strategy path).roots (i+1))
          ((strategy path).evenWeights i) ((strategy path).oddWeights i)
          ((strategy path).sent i) ((strategy path).challenges i) := by
        intro i hi
        have absent := noEvents i (by omega)
        have takeLen : (path.take i).length=i := by simp [List.length_take]; omega
        change ¬((strategy path).snapshot N0 sizes i).bad (sizes (i+1)) (degrees (i+1)) T _
        rw [causal path hp i hi,challengeValues path hp i hi]
        have notOld : ¬generalFoldHistoryBad strategy N0 sizes degrees T (path.take i) (path[i]?.getD 0) := by
          intro old
          apply absent
          change generalCheckedFoldBad strategy N0 sizes degrees T (path.take i) (path[i]?.getD 0)
          exact ⟨by simpa [takeLen] using pathChecks.2 i hi,old⟩
        simpa [generalFoldHistoryBad,takeLen] using notOld
      have few := general_chain_query_bound_outside_bad N0 sizes degrees
        (strategy path).roots (strategy path).challenges (strategy path).oracles
        (strategy path).weights (strategy path).claims (strategy path).evenWeights
        (strategy path).oddWeights (strategy path).sent T rounds positive
        sizeHalves degreeHalves cert.weightShapes cert.parentWeights cert.nextWeights cert.parentClaims cert.nextClaims
        h2 cert.nonzero cert.squared cert.negative (strategy path).terminal cert.shape
        cert.terminalValues cert.terminalResidual (initial path hp pathChecks) noBad
      change count (List.range N0) (generalFoldHistoryQuery strategy sizes rounds path)<T at few
      have subset : count (List.range N0) (checkedQuery path)≤
          count (List.range N0) (generalFoldHistoryQuery strategy sizes rounds path) :=
        count_mono _ (fun _ h => h.2)
      omega
    · have zero : count (List.range N0) (checkedQuery path)=0 := by
        simp [count,checkedQuery,pathChecks]
      omega
  have result := interactive_round_query_budget sample (List.range N0) bad []
    ((List.range rounds).map (fun i => max (sizes (i+1)) 2)) q (T-1)
    checkedQuery (by simpa using bounds) (by simpa using good)
  simp only [List.length_map,List.length_range] at result
  rw [←interactive_accepted_cartesian] at result
  have subset : count ((uniformTuples sample rounds).flatMap (fun path =>
        (uniformTuples (List.range N0) q).map (fun queries => (path,queries))))
        (fun pair => generalCheckedFoldAccept strategy N0 sizes degrees T rounds pair.1 pair.2) ≤
      count ((uniformTuples sample rounds).flatMap (fun path =>
        (uniformTuples (List.range N0) q).map (fun queries => (path,queries))))
        (fun pair => allQueriesPass (checkedQuery pair.1) pair.2) := by
    apply count_mono
    intro pair accepted seed hs
    exact ⟨accepted.1,accepted.2 seed hs⟩
  have scaled := Nat.mul_le_mul_right sample.length subset
  exact Nat.le_trans scaled (by simpa using result)


end NearCompression
