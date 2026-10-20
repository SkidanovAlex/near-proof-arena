import NearCompression.FunctionalOpeningFold
import NearCompression.WHIRRoundRecurrence
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

def weightedReplayScale (point challenges : List K) : Nat→K
  | 0=>1
  | i+1=>weightedReplayScale point challenges i*
      ((1-challenges.getD i 0)*(1-point.getD i 0)+challenges.getD i 0*point.getD i 0)

/-- Indexed form of equality_weight_at's left-to-right product. Shape checks
ensure every requested point/challenge coordinate exists. -/
def weightedReplayScaleLoop (point challenges : List K) (n : Nat) : K :=
  (List.range n).foldl (fun acc i=>acc*((1-point.getD i 0)*(1-challenges.getD i 0)+
    point.getD i 0*challenges.getD i 0)) 1

theorem weighted_replay_scale_loop (point challenges : List K) (n : Nat) :
    weightedReplayScaleLoop point challenges n=weightedReplayScale point challenges n := by
  induction n with
  | zero=>rfl
  | succ n ih=>
    unfold weightedReplayScaleLoop at ih ⊢
    rw [List.range_succ,List.foldl_append]
    simp only [List.foldl_cons,List.foldl_nil,ih,weightedReplayScale]
    grind

def weightedReplayWeights (point challenges : List K) (i : Nat) : List K :=
  (equalityWeights (point.drop i)).map (fun w=>weightedReplayScale point challenges i*w)

def weightedReplayTail (point challenges : List K) (i : Nat) : List K :=
  (equalityWeights (point.drop (i+1))).map (fun w=>weightedReplayScale point challenges i*w)

def weightedReplaySent (sent : List (WhirQuadratic K)) (i : Nat) : Poly K :=
  let q := sent.getD i ⟨0,0,0⟩
  Poly.mk [q.c0,q.c1,q.c2]

def weightedReplayClaim (initial : K) (sent : List (WhirQuadratic K)) (challenges : List K) : Nat→K
  | 0=>initial
  | i+1=>(weightedReplaySent sent i).eval (challenges.getD i 0)

/-- Exact algebraic tests in round_start and the degree-one terminal. Hash
transcript derivation and root authentication are intentionally not included. -/
def weightedReplayCheck [DecidableEq K] (point challenges : List K) (sent : List (WhirQuadratic K))
    (initial terminal : K) : Bool :=
  decide (challenges.length=point.length) && decide (sent.length=point.length) &&
    (List.range point.length).all (fun i=>decide ((weightedReplaySent sent i).eval 0+
      (weightedReplaySent sent i).eval 1=weightedReplayClaim initial sent challenges i)) &&
    decide (weightedReplayScale point challenges point.length*terminal=
      weightedReplayClaim initial sent challenges point.length)

private theorem scale_interleave (ws : List K) (a b s : K) :
    (rsInterleave (ws.map (fun w=>a*w)) (ws.map (fun w=>b*w))).map (fun w=>s*w)=
      rsInterleave ((ws.map (fun w=>s*w)).map (fun w=>a*w))
        ((ws.map (fun w=>s*w)).map (fun w=>b*w)) := by
  induction ws with
  | nil=>simp [rsInterleave]
  | cons w ws ih=>
    simp only [List.map_cons,rsInterleave,ih,List.cons.injEq]
    exact ⟨by grind,by grind,True.intro⟩

theorem weighted_replay_parent_weights (point challenges : List K) (i : Nat) (bound : i<point.length) :
    weightedReplayWeights point challenges i=rsInterleave
      ((weightedReplayTail point challenges i).map (fun w=>(1-point.getD i 0)*w))
      ((weightedReplayTail point challenges i).map (fun w=>point.getD i 0*w)) := by
  unfold weightedReplayWeights weightedReplayTail
  rw [List.drop_eq_getElem_cons bound]
  simp only [equalityWeights]
  have value : point.getD i 0=point[i] := by simp [List.getD,bound]
  rw [value]
  exact scale_interleave _ _ _ _

theorem weighted_replay_next_weights (point challenges : List K) (i : Nat) :
    weightedReplayWeights point challenges (i+1)=(weightedReplayTail point challenges i).map
      (fun w=>((1-challenges.getD i 0)*(1-point.getD i 0)+challenges.getD i 0*point.getD i 0)*w) := by
  unfold weightedReplayWeights weightedReplayTail
  simp only [weightedReplayScale,List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro w hw
  grind

theorem weighted_replay_initial_weights (point challenges : List K) :
    weightedReplayWeights point challenges 0=equalityWeights point := by
  simp [weightedReplayWeights,weightedReplayScale,Semiring.one_mul]

theorem weighted_replay_terminal_weights (point challenges : List K) :
    weightedReplayWeights point challenges point.length=[weightedReplayScale point challenges point.length] := by
  simp only [weightedReplayWeights,List.drop_length,equalityWeights,List.map_cons,List.map_nil,Semiring.mul_one]

theorem weighted_replay_sent_degree (sent : List (WhirQuadratic K)) (i : Nat) :
    (weightedReplaySent sent i).DegLt 3 := by
  exact Poly.degLt_length _

/-- The modeled transcript uses the verifier-derived equality weights and
claim replacements. No honest coefficient vector or close candidate is supplied. -/
def weightedReplayTranscript (point challenges : List K) (sent : List (WhirQuadratic K))
    (initial terminal : K) (roots : Nat→K) (oracles : Nat→Nat→K) : FoldTranscript K where
  roots:=roots
  challenges:=fun i=>challenges.getD i 0
  oracles:=oracles
  weights:=weightedReplayWeights point challenges
  claims:=weightedReplayClaim initial sent challenges
  tailWeights:=weightedReplayTail point challenges
  w0:=fun i=>1-point.getD i 0
  w1:=fun i=>point.getD i 0
  sent:=weightedReplaySent sent
  terminal:=[terminal]

/-- Derive the soundness ledger's algebra/terminal certificate from actual
endpoint/terminal tests. Full terminal-oracle equality is the explicit output
of terminal tree authentication; it is not a proximity assumption. -/
theorem weighted_replay_transcript_checks [DecidableEq K]
    (point challenges : List K) (sent : List (WhirQuadratic K)) (initial terminal : K)
    (roots : Nat→K) (oracles : Nat→Nat→K) (N0 T : Nat) (sizes degrees : Nat→Nat)
    (checked : weightedReplayCheck point challenges sent initial terminal=true)
    (nonzero : ∀ i<point.length,∀ y<sizes (i+1),roots i^y≠0)
    (squared : ∀ i<point.length,∀ y<sizes (i+1),roots (i+1)^y=roots i^y*roots i^y)
    (negative : ∀ i<point.length,∀ y<sizes (i+1),roots i^(y+sizes (i+1))= -(roots i^y))
    (terminalDegree : 1≤degrees point.length)
    (terminalValues : ∀ y<sizes point.length,oracles point.length y=terminal) :
    FoldTranscriptChecks (weightedReplayTranscript point challenges sent initial terminal roots oracles)
      N0 sizes degrees T point.length := by
  simp only [weightedReplayCheck,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at checked
  obtain ⟨⟨⟨_,_⟩,endpoints⟩,last⟩ := checked
  refine ⟨weighted_replay_parent_weights point challenges,(fun i _=>weighted_replay_next_weights point challenges i),
    ?_,?_,nonzero,squared,negative,terminalDegree,?_,?_⟩
  · intro i hi
    exact (endpoints i (List.mem_range.mpr hi)).symm
  · intro i hi; rfl
  · intro y hy
    have value:=terminalValues y hy
    simpa [weightedReplayTranscript,Poly.eval,Poly.evalL,Semiring.mul_zero,Semiring.add_zero] using value
  · change scalarRSResidual (weightedReplayWeights point challenges point.length) (Poly.mk [terminal])=_
    rw [weighted_replay_terminal_weights]
    simpa [scalarRSResidual,scalarRSResidualFrom,Poly.coeff,weightedReplayTranscript,Semiring.add_zero] using last

/-- Accepted concrete replay and authenticated terminal imply an initial
candidate, fewer than T passing full-domain seeds, or a specific nonlinear
extraction bad event. This does not presume any close candidate. The bad event
can be counted by global_chain_unique_bad_count under its separate regime. -/
theorem weighted_replay_candidate_or_bad [DecidableEq K]
    (point challenges : List K) (sent : List (WhirQuadratic K)) (initial terminal : K)
    (roots : Nat→K) (oracles : Nat→Nat→K) (N0 T : Nat) (sizes degrees : Nat→Nat)
    (checked : weightedReplayCheck point challenges sent initial terminal=true)
    (positive : ∀ i≤point.length,0<sizes i)
    (sizeSteps : ∀ i<point.length,sizes i=2*sizes (i+1))
    (degreeSteps : ∀ i<point.length,degrees i=2*degrees (i+1))
    (h2 : (2:K)≠0)
    (nonzero : ∀ i<point.length,∀ y<sizes (i+1),roots i^y≠0)
    (squared : ∀ i<point.length,∀ y<sizes (i+1),roots (i+1)^y=roots i^y*roots i^y)
    (negative : ∀ i<point.length,∀ y<sizes (i+1),roots i^(y+sizes (i+1))= -(roots i^y))
    (terminalDegree : 1≤degrees point.length)
    (terminalValues : ∀ y<sizes point.length,oracles point.length y=terminal) :
    let tr := weightedReplayTranscript point challenges sent initial terminal roots oracles
    indexedChainCandidate N0 sizes degrees tr.roots tr.challenges tr.oracles tr.weights tr.claims T 0 ∨
    count (List.range N0) (globalChainPass sizes (globalRSChainCheck sizes tr.roots tr.challenges tr.oracles)
      point.length)<T ∨
    ∃ i,i<point.length ∧ indexedFoldBad (sizes (i+1)) (degrees (i+1)) T
      (globalChainWeight (List.range N0) sizes (globalRSChainCheck sizes tr.roots tr.challenges tr.oracles) i)
      (tr.oracles i) (tr.roots i) (tr.roots (i+1)) (tr.tailWeights i) (tr.w0 i) (tr.w1 i) (tr.sent i) (tr.challenges i) := by
  classical
  let tr := weightedReplayTranscript point challenges sent initial terminal roots oracles
  have checks := weighted_replay_transcript_checks point challenges sent initial terminal roots oracles
    N0 T sizes degrees checked nonzero squared negative terminalDegree terminalValues
  by_cases candidate : indexedChainCandidate N0 sizes degrees tr.roots tr.challenges tr.oracles tr.weights tr.claims T 0
  · exact Or.inl candidate
  · right
    by_cases bad : ∃ i,i<point.length ∧ indexedFoldBad (sizes (i+1)) (degrees (i+1)) T
        (globalChainWeight (List.range N0) sizes (globalRSChainCheck sizes tr.roots tr.challenges tr.oracles) i)
        (tr.oracles i) (tr.roots i) (tr.roots (i+1)) (tr.tailWeights i) (tr.w0 i) (tr.w1 i) (tr.sent i) (tr.challenges i)
    · exact Or.inr bad
    · left
      exact global_chain_query_bound_outside_extraction_bad N0 sizes degrees tr.roots tr.challenges tr.oracles
        tr.weights tr.claims tr.tailWeights tr.w0 tr.w1 tr.sent T point.length positive sizeSteps degreeSteps
        checks.parentWeights checks.nextWeights checks.parentClaims checks.nextClaims h2 checks.nonzero
        checks.squared checks.negative tr.terminal checks.shape checks.terminalValues checks.terminalResidual
        candidate (by intro i hi h;exact bad ⟨i,hi,h⟩)
end NearCompression
