import NearCompression.GlobalChainUniqueRegime
import NearCompression.IndependentQueryBudget

/-! Ideal interactive folding, including adaptive challenge transcripts and
with-replacement query tuples. These are algebraic oracle semantics: binding,
Fiat--Shamir/QROM, and the initial AIR/virtual-oracle reduction remain external. -/
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security

structure FoldTranscript (K : Type) [Field K] where
  roots : Nat → K
  challenges : Nat → K
  oracles : Nat → Nat → K
  weights : Nat → List K
  claims : Nat → K
  tailWeights : Nat → List K
  w0 : Nat → K
  w1 : Nat → K
  sent : Nat → Poly K
  terminal : List K

/-- Exactly the data fixed before the challenge on which concentration depends.
In particular it includes the transcript-generated consistency measure. -/
structure FoldSnapshot (K : Type) [Field K] where
  weight : Nat → Nat
  source : Nat → K
  root : K
  childRoot : K
  weights : List K
  w0 : K
  w1 : K
  sent : Poly K

noncomputable def FoldTranscript.snapshot {K : Type} [Field K]
    (tr : FoldTranscript K) (N0 : Nat) (sizes : Nat → Nat) (stage : Nat) : FoldSnapshot K :=
  ⟨globalChainWeight (List.range N0) sizes
      (globalRSChainCheck sizes tr.roots tr.challenges tr.oracles) stage,
    tr.oracles stage,tr.roots stage,tr.roots (stage+1),tr.tailWeights stage,
    tr.w0 stage,tr.w1 stage,tr.sent stage⟩

noncomputable def FoldSnapshot.bad {K : Type} [Field K]
    (snapshot : FoldSnapshot K) (N D T : Nat) (r : K) : Prop :=
  indexedFoldBad N D T snapshot.weight snapshot.source snapshot.root snapshot.childRoot
    snapshot.weights snapshot.w0 snapshot.w1 snapshot.sent r

noncomputable def foldHistoryBad {K : Type} [Field K]
    (strategy : List K → FoldTranscript K) (N0 : Nat) (sizes degrees : Nat → Nat)
    (T : Nat) (history : List K) : K → Prop :=
  ((strategy history).snapshot N0 sizes history.length).bad
    (sizes (history.length+1)) (degrees (history.length+1)) T

/-- Actual acceptance for the algebraic global-chain query checks. Other
verifier checks are certificates below, rather than part of this predicate. -/
def foldHistoryQuery {K : Type} [Field K] (strategy : List K → FoldTranscript K)
    (sizes : Nat → Nat) (rounds : Nat) (history : List K) : Nat → Prop :=
  globalChainPass sizes (globalRSChainCheck sizes (strategy history).roots
    (strategy history).challenges (strategy history).oracles) rounds

/-- All concrete checks needed to connect the disclosed terminal to the source.
No candidate preservation or extraction statement appears in this certificate. -/
structure FoldTranscriptCertificate {K : Type} [Field K] (tr : FoldTranscript K)
    (N0 : Nat) (sizes degrees : Nat → Nat) (T rounds : Nat) : Prop where
  parentWeights : ∀ i<rounds,tr.weights i=rsInterleave
    ((tr.tailWeights i).map (fun w => tr.w0 i*w)) ((tr.tailWeights i).map (fun w => tr.w1 i*w))
  nextWeights : ∀ i<rounds,tr.weights (i+1)=(tr.tailWeights i).map
    (fun w => ((1-tr.challenges i)*tr.w0 i+tr.challenges i*tr.w1 i)*w)
  parentClaims : ∀ i<rounds,tr.claims i=(tr.sent i).eval 0+(tr.sent i).eval 1
  nextClaims : ∀ i<rounds,tr.claims (i+1)=(tr.sent i).eval (tr.challenges i)
  nonzero : ∀ i<rounds,∀ y<sizes (i+1),tr.roots i^y≠0
  squared : ∀ i<rounds,∀ y<sizes (i+1),tr.roots (i+1)^y=tr.roots i^y*tr.roots i^y
  negative : ∀ i<rounds,∀ y<sizes (i+1),tr.roots i^(y+sizes (i+1))= -(tr.roots i^y)
  shape : tr.terminal.length≤degrees rounds
  terminalValues : ∀ y<sizes rounds,tr.oracles rounds y=(Poly.mk tr.terminal).eval (tr.roots rounds^y)
  terminalResidual : scalarRSResidual (tr.weights rounds) (Poly.mk tr.terminal)=tr.claims rounds
  noInitialCandidate : ¬indexedChainCandidate N0 sizes degrees tr.roots tr.challenges
    tr.oracles tr.weights tr.claims T 0

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

/-- Explicit accepted transcript × query count. In the unique-decoding regime,
there is NO nonlinear extraction hypothesis. The strategy must be causal:
completed transcript snapshots equal snapshots fixed at their history prefixes.
Challenges and query seeds are independent ideal uniform draws with replacement.
This statement treats strategies producing check-passing transcripts at every
leaf. A rejecting/aborting implementation additionally needs the elementary
restriction from its accepted leaves to this certified-transcript experiment. -/
theorem interactive_unique_fold_soundness {K : Type} [Field K]
    (sample : List K) (sampleDistinct : sample.Nodup)
    (strategy : List K → FoldTranscript K) (N0 T rounds q : Nat)
    (sizes degrees : Nat → Nat)
    (sizeInitial : sizes 0=N0) (positive : ∀ i≤rounds,0<sizes i)
    (sizeHalves : ∀ i<rounds,sizes i=2*sizes (i+1))
    (degreeHalves : ∀ i<rounds,degrees i=2*degrees (i+1))
    (h2 : (2:K)≠0) (regime : 2*N0+degrees 0<3*T)
    (domain : ∀ history : List K,history.length<rounds →
      ∀ a<sizes (history.length+1),∀ b<sizes (history.length+1),
      (strategy history).roots (history.length+1)^a=
        (strategy history).roots (history.length+1)^b → a=b)
    (quadratic : ∀ history : List K,history.length<rounds →
      ((strategy history).sent history.length).DegLt 3)
    (causal : ∀ path∈uniformTuples sample rounds,∀ i<rounds,
      (strategy path).snapshot N0 sizes i=(strategy (path.take i)).snapshot N0 sizes i)
    (challengeValues : ∀ path∈uniformTuples sample rounds,∀ i<rounds,
      (strategy path).challenges i=path[i]?.getD 0)
    (certificates : ∀ path∈uniformTuples sample rounds,
      FoldTranscriptCertificate (strategy path) N0 sizes degrees T rounds) :
    count ((uniformTuples sample rounds).flatMap (fun path =>
      (uniformTuples (List.range N0) q).map (fun queries => (path,queries))))
      (fun pair => allQueriesPass (foldHistoryQuery strategy sizes rounds pair.1) pair.2)*sample.length ≤
      ((List.range rounds).map (fun i => max (sizes (i+1)) 2)).sum*
        sample.length^rounds*N0^q + sample.length^(rounds+1)*(T-1)^q := by
  let bad := foldHistoryBad strategy N0 sizes degrees T
  have localBound : ∀ history : List K,history.length<rounds →
      count sample (bad history)≤max (sizes (history.length+1)) 2 := by
    intro history hh
    exact global_chain_unique_bad_count sample sampleDistinct N0 sizes degrees
      (strategy history).roots (strategy history).challenges (strategy history).oracles
      history.length T sizeInitial (fun j hj => positive j (by omega))
      (fun j hj => sizeHalves j (by omega)) (fun j hj => degreeHalves j (by omega))
      (domain history hh) ((strategy history).tailWeights history.length)
      ((strategy history).w0 history.length) ((strategy history).w1 history.length)
      ((strategy history).sent history.length) (quadratic history hh) regime
  have bounds := adaptive_bounds_from_index sample bad
    (fun i => max (sizes (i+1)) 2) [] rounds (by simpa using localBound)
  have good : ∀ path∈uniformTuples sample rounds,¬adaptivePathBad bad [] path →
      count (List.range N0) (foldHistoryQuery strategy sizes rounds path)≤T-1 := by
    intro path hp hg
    have len := tuple_length sample rounds path hp
    have noEvents := path_no_bad bad [] path (0:K) hg
    have cert := certificates path hp
    have noBad : ∀ i<rounds,¬indexedFoldBad (sizes (i+1)) (degrees (i+1)) T
        (globalChainWeight (List.range N0) sizes
          (globalRSChainCheck sizes (strategy path).roots (strategy path).challenges (strategy path).oracles) i)
        ((strategy path).oracles i) ((strategy path).roots i) ((strategy path).roots (i+1))
        ((strategy path).tailWeights i) ((strategy path).w0 i) ((strategy path).w1 i)
        ((strategy path).sent i) ((strategy path).challenges i) := by
      intro i hi
      have absent := noEvents i (by omega)
      have takeLen : (path.take i).length=i := by simp [List.length_take]; omega
      change ¬((strategy path).snapshot N0 sizes i).bad (sizes (i+1)) (degrees (i+1)) T _
      rw [causal path hp i hi,challengeValues path hp i hi]
      simpa [bad,foldHistoryBad,takeLen] using absent
    have few := global_chain_query_bound_outside_extraction_bad N0 sizes degrees
      (strategy path).roots (strategy path).challenges (strategy path).oracles
      (strategy path).weights (strategy path).claims (strategy path).tailWeights
      (strategy path).w0 (strategy path).w1 (strategy path).sent T rounds positive
      sizeHalves degreeHalves cert.parentWeights cert.nextWeights cert.parentClaims cert.nextClaims
      h2 cert.nonzero cert.squared cert.negative (strategy path).terminal cert.shape
      cert.terminalValues cert.terminalResidual cert.noInitialCandidate noBad
    change count (List.range N0) (foldHistoryQuery strategy sizes rounds path)<T at few
    omega
  have result := interactive_round_query_budget sample (List.range N0) bad []
    ((List.range rounds).map (fun i => max (sizes (i+1)) 2)) q (T-1)
    (foldHistoryQuery strategy sizes rounds) (by simpa using bounds) (by simpa using good)
  simp only [List.length_map,List.length_range] at result
  rw [←interactive_accepted_cartesian] at result
  simpa using result

end NearCompression
