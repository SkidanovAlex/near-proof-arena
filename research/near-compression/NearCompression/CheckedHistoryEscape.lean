import NearCompression.CheckedFoldEscape
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

/-- The snapshot fixes the agreement measure, source and domain; the
coefficient functional and claim are bound separately before the draw. -/
theorem indexed_candidate_snapshot_congr (a b : GeneralFoldTranscript K)
    (N0 T i : Nat) (sizes degrees : Nat→Nat)
    (snapshot : a.snapshot N0 sizes i=b.snapshot N0 sizes i)
    (weights : a.weights i=b.weights i) (claim : a.claims i=b.claims i) :
    indexedChainCandidate N0 sizes degrees a.roots a.challenges a.oracles a.weights a.claims T i ↔
    indexedChainCandidate N0 sizes degrees b.roots b.challenges b.oracles b.weights b.claims T i := by
  have measure := congrArg GeneralFoldSnapshot.weight snapshot
  have source := congrArg GeneralFoldSnapshot.source snapshot
  have root := congrArg GeneralFoldSnapshot.root snapshot
  simp only [GeneralFoldTranscript.snapshot] at measure source root
  unfold indexedChainCandidate
  rw [weights,claim,measure,source,root]

/-- Uses the actual prior prefix's absent candidate and the next prefix's
present candidate. Invalid local checks reject. -/
noncomputable def checkedHistoryEscape
    (strategy : List K→GeneralFoldTranscript K) (N0 T : Nat)
    (sizes degrees : Nat→Nat) (history : List K) (r : K) : Prop :=
  let i:=history.length
  let prior:=strategy history
  let next:=strategy (history++[r])
  generalFoldPrechallengeChecks prior sizes i ∧
  GeneralFoldStepChecks next sizes degrees i ∧
  ¬indexedChainCandidate N0 sizes degrees prior.roots prior.challenges prior.oracles
    prior.weights prior.claims T i ∧
  indexedChainCandidate N0 sizes degrees next.roots next.challenges next.oracles
    next.weights next.claims T (i+1)

/-- Every fixed prefix permits an arbitrary adaptive next oracle. No assumed
candidate preservation or numerical escape bound. -/
theorem checked_history_escape_bound
    (sample : List K) (distinct : sample.Nodup)
    (strategy : List K→GeneralFoldTranscript K) (history : List K)
    (N0 T : Nat) (sizes degrees : Nat→Nat)
    (initial : sizes 0=N0) (positive : ∀ j≤history.length,0<sizes j)
    (sizeHalves : ∀ j≤history.length,sizes j=2*sizes (j+1))
    (degreeHalves : ∀ j≤history.length,degrees j=2*degrees (j+1))
    (regime : 2*N0+degrees 0<3*T) (h2 : (2:K)≠0)
    (fixed : ∀ r∈sample,(strategy (history++[r])).snapshot N0 sizes history.length=
      (strategy history).snapshot N0 sizes history.length)
    (weights : ∀ r∈sample,(strategy (history++[r])).weights history.length=(strategy history).weights history.length)
    (claim : ∀ r∈sample,(strategy (history++[r])).claims history.length=(strategy history).claims history.length)
    (challenge : ∀ r∈sample,(strategy (history++[r])).challenges history.length=r) :
    count sample (checkedHistoryEscape strategy N0 T sizes degrees history)≤
      max (sizes (history.length+1)) 2 := by
  classical
  by_cases checks : generalFoldPrechallengeChecks (strategy history) sizes history.length
  · have bound := checked_fold_continuation_escape_bound sample distinct (strategy history)
      (fun r=>strategy (history++[r])) N0 T history.length sizes degrees initial positive
      sizeHalves degreeHalves regime h2 checks fixed challenge
    apply Nat.le_trans ?_ bound
    unfold count
    apply List.countP_mono_left
    intro r hr event
    obtain ⟨_,step,parent,child⟩ := _root_.of_decide_eq_true event
    apply _root_.decide_eq_true
    refine ⟨step,?_,child⟩
    intro candidate
    exact parent ((indexed_candidate_snapshot_congr _ _ N0 T history.length sizes degrees
      (fixed r hr) (weights r hr) (claim r hr)).mp candidate)
  · simp [count,checkedHistoryEscape,checks]

/-- Finite-tree composition of actual prefix-to-prefix escape bounds. Initial
doom, terminal rejection, query rounds, commitments and QROM remain open. -/
theorem checked_history_adaptive_escape_budget
    (sample : List K) (distinct : sample.Nodup)
    (strategy : List K→GeneralFoldTranscript K) (N0 T rounds limit : Nat)
    (sizes degrees : Nat→Nat) (initial : sizes 0=N0)
    (positive : ∀ j<rounds,0<sizes j)
    (sizeHalves : ∀ j<rounds,sizes j=2*sizes (j+1))
    (degreeHalves : ∀ j<rounds,degrees j=2*degrees (j+1))
    (regime : 2*N0+degrees 0<3*T) (h2 : (2:K)≠0)
    (bounded : ∀ j<rounds,max (sizes (j+1)) 2≤limit)
    (fixed : ∀ h : List K,h.length<rounds → ∀ r∈sample,
      (strategy (h++[r])).snapshot N0 sizes h.length=(strategy h).snapshot N0 sizes h.length)
    (weights : ∀ h : List K,h.length<rounds → ∀ r∈sample,
      (strategy (h++[r])).weights h.length=(strategy h).weights h.length)
    (claim : ∀ h : List K,h.length<rounds → ∀ r∈sample,
      (strategy (h++[r])).claims h.length=(strategy h).claims h.length)
    (challenge : ∀ h : List K,h.length<rounds → ∀ r∈sample,
      (strategy (h++[r])).challenges h.length=r) :
    adaptiveFailureLeaves sample (checkedHistoryEscape strategy N0 T sizes degrees) [] rounds*
      sample.length≤rounds*limit*sample.length^rounds := by
  have localBound : ∀ h : List K,h.length<rounds →
      count sample (checkedHistoryEscape strategy N0 T sizes degrees h)≤limit := by
    intro h hh
    exact Nat.le_trans (checked_history_escape_bound sample distinct strategy h N0 T sizes degrees
      initial (fun j hj=>positive j (by omega)) (fun j hj=>sizeHalves j (by omega))
      (fun j hj=>degreeHalves j (by omega)) regime h2 (fixed h hh) (weights h hh)
      (claim h hh) (challenge h hh)) (bounded h.length hh)
  have bounds : ∀ (n : Nat) (h : List K),h.length+n≤rounds → AdaptiveRoundBounds sample
      (checkedHistoryEscape strategy N0 T sizes degrees) h (List.replicate n limit) := by
    intro n
    induction n with
    | zero => intro h hh; trivial
    | succ n ih =>
      intro h hh
      constructor
      · exact localBound h (by omega)
      · intro r hr
        apply ih (h++[r])
        simp only [List.length_append,List.length_singleton]
        omega
  have result := adaptive_round_failure_budget sample
    (checkedHistoryEscape strategy N0 T sizes degrees) [] (List.replicate rounds limit)
    (bounds rounds [] (by simp))
  simpa using result

end NearCompression
