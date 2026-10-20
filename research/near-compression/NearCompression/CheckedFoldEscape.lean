import NearCompression.GeneralCheckedFold
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

/-- Local algebra/domain checks for one actual fold, without assumptions on
future rounds or the terminal disclosure. -/
structure GeneralFoldStepChecks (tr : GeneralFoldTranscript K)
    (sizes degrees : Nat→Nat) (i : Nat) : Prop where
  sizeStep : sizes i=2*sizes (i+1)
  degreeStep : degrees i=2*degrees (i+1)
  weightShape : (tr.evenWeights i).length=(tr.oddWeights i).length
  parentWeights : tr.weights i=rsInterleave (tr.evenWeights i) (tr.oddWeights i)
  nextWeights : tr.weights (i+1)=generalFoldWeights (tr.evenWeights i) (tr.oddWeights i) (tr.challenges i)
  parentClaim : tr.claims i=(tr.sent i).eval 0+(tr.sent i).eval 1
  nextClaim : tr.claims (i+1)=(tr.sent i).eval (tr.challenges i)
  nonzero : ∀ y<sizes (i+1),tr.roots i^y≠0
  squared : ∀ y<sizes (i+1),tr.roots (i+1)^y=tr.roots i^y*tr.roots i^y
  negative : ∀ y<sizes (i+1),tr.roots i^(y+sizes (i+1))= -(tr.roots i^y)

/-- A checked transition from no parent candidate to a child candidate. -/
def checkedFoldEscape (tr : GeneralFoldTranscript K) (N0 : Nat)
    (sizes degrees : Nat→Nat) (T i : Nat) : Prop :=
  GeneralFoldStepChecks tr sizes degrees i ∧
  ¬indexedChainCandidate N0 sizes degrees tr.roots tr.challenges tr.oracles tr.weights tr.claims T i ∧
  indexedChainCandidate N0 sizes degrees tr.roots tr.challenges tr.oracles tr.weights tr.claims T (i+1)

/-- Derive the extraction bad event from literal checked state transitions,
including arbitrary coefficient-weight folding and consistency-gated measures. -/
theorem checked_fold_escape_implies_bad (tr : GeneralFoldTranscript K) (N0 : Nat)
    (sizes degrees : Nat→Nat) (T i : Nat) (h2 : (2:K)≠0)
    (escape : checkedFoldEscape tr N0 sizes degrees T i) :
    (tr.snapshot N0 sizes i).bad (sizes (i+1)) (degrees (i+1)) T (tr.challenges i) := by
  obtain ⟨checks,parent,child⟩ := escape
  constructor
  · exact general_indexed_child_implies_success N0 sizes degrees tr.roots tr.challenges
      tr.oracles tr.weights tr.claims T i (tr.evenWeights i) (tr.oddWeights i)
      checks.weightShape (tr.sent i) checks.nextWeights checks.nextClaim child
  · intro outcome
    exact parent (general_indexed_outcome_implies_parent N0 sizes degrees tr.roots tr.challenges
      tr.oracles tr.weights tr.claims T i (tr.evenWeights i) (tr.oddWeights i)
      checks.weightShape (tr.sent i) checks.sizeStep checks.degreeStep checks.parentWeights
      checks.parentClaim h2 checks.nonzero checks.squared checks.negative outcome)

/-- Pointwise prior bound allowing the entire continuation, including its
next oracle, to depend on r. Only the extraction snapshot is fixed before r.
This is an algebraic IOP step, not Merkle/Fiat-Shamir implementation binding. -/
theorem checked_fold_continuation_escape_bound
    (sample : List K) (distinct : sample.Nodup)
    (prior : GeneralFoldTranscript K) (continuation : K→GeneralFoldTranscript K)
    (N0 T i : Nat) (sizes degrees : Nat→Nat)
    (initial : sizes 0=N0) (positive : ∀ j≤i,0<sizes j)
    (sizeHalves : ∀ j≤i,sizes j=2*sizes (j+1))
    (degreeHalves : ∀ j≤i,degrees j=2*degrees (j+1))
    (regime : 2*N0+degrees 0<3*T) (h2 : (2:K)≠0)
    (prechecks : generalFoldPrechallengeChecks prior sizes i)
    (fixed : ∀ r∈sample,(continuation r).snapshot N0 sizes i=prior.snapshot N0 sizes i)
    (challenge : ∀ r∈sample,(continuation r).challenges i=r) :
    count sample (fun r=>checkedFoldEscape (continuation r) N0 sizes degrees T i)
      ≤max (sizes (i+1)) 2 := by
  have bound := general_global_chain_bad_count sample distinct N0 sizes degrees prior.roots
    prior.challenges prior.oracles i T initial positive sizeHalves degreeHalves prechecks.1
    (prior.evenWeights i) (prior.oddWeights i) (prior.sent i) prechecks.2 regime
  apply Nat.le_trans ?_ bound
  -- Restrict to sampled r explicitly, so unreachable continuations need no bindings.
  classical
  unfold count
  apply List.countP_mono_left
  intro r hr escape
  have event := checked_fold_escape_implies_bad (continuation r) N0 sizes degrees T i h2
    (of_decide_eq_true escape)
  rw [fixed r hr,challenge r hr] at event
  exact decide_eq_true event

end NearCompression
