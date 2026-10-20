import NearCompression.CheckedHistoryEscape
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

/-- The literal local checks along successive adaptive states. The final
coefficient disclosure is checked separately. No candidate/extraction premise. -/
def checkedHistoryPath (strategy : List K→GeneralFoldTranscript K)
    (sizes degrees : Nat→Nat) : List K→List K→Prop
  | _,[] => True
  | history,r::rest =>
      generalFoldPrechallengeChecks (strategy history) sizes history.length ∧
      GeneralFoldStepChecks (strategy (history++[r])) sizes degrees history.length ∧
      checkedHistoryPath strategy sizes degrees (history++[r]) rest

/-- Absent an actual prefix-to-prefix escape, a checked path starting with no
candidate ends with no candidate. This is a deterministic path statement;
chronology/binding premises enter through the separately proved escape count. -/
theorem checked_history_no_escape_preserves_doom
    (strategy : List K→GeneralFoldTranscript K) (N0 T : Nat)
    (sizes degrees : Nat→Nat) (history path : List K)
    (checks : checkedHistoryPath strategy sizes degrees history path)
    (initial : ¬indexedChainCandidate N0 sizes degrees (strategy history).roots
      (strategy history).challenges (strategy history).oracles (strategy history).weights
      (strategy history).claims T history.length)
    (noEscape : ¬adaptivePathBad (checkedHistoryEscape strategy N0 T sizes degrees) history path) :
    ¬indexedChainCandidate N0 sizes degrees (strategy (history++path)).roots
      (strategy (history++path)).challenges (strategy (history++path)).oracles
      (strategy (history++path)).weights (strategy (history++path)).claims T (history++path).length := by
  induction path generalizing history with
  | nil => simpa using initial
  | cons r rest ih =>
    obtain ⟨pre,step,tail⟩ := checks
    have next : ¬indexedChainCandidate N0 sizes degrees (strategy (history++[r])).roots
        (strategy (history++[r])).challenges (strategy (history++[r])).oracles
        (strategy (history++[r])).weights (strategy (history++[r])).claims T (history++[r]).length := by
      intro candidate
      apply noEscape
      apply Or.inl
      refine ⟨pre,step,initial,?_⟩
      simpa using candidate
    have result := ih (history++[r]) tail next (fun bad=>noEscape (Or.inr bad))
    simpa [List.append_assoc] using result

/-- The actual checked disclosure, together with terminal doom, forces fewer
than T globally consistent query seeds. It need not reject every seed. -/
theorem checked_history_terminal_few_queries
    (strategy : List K→GeneralFoldTranscript K) (N0 T : Nat)
    (sizes degrees : Nat→Nat) (path : List K)
    (positive : ∀ j≤path.length,0<sizes j)
    (halves : ∀ j<path.length,sizes j=2*sizes (j+1))
    (checks : checkedHistoryPath strategy sizes degrees [] path)
    (initial : ¬indexedChainCandidate N0 sizes degrees (strategy []).roots
      (strategy []).challenges (strategy []).oracles (strategy []).weights
      (strategy []).claims T 0)
    (noEscape : ¬adaptivePathBad (checkedHistoryEscape strategy N0 T sizes degrees) [] path)
    (shape : (strategy path).terminal.length≤degrees path.length)
    (values : ∀ y<sizes path.length,(strategy path).oracles path.length y=
      (Poly.mk (strategy path).terminal).eval ((strategy path).roots path.length^y))
    (residual : scalarRSResidual ((strategy path).weights path.length)
      (Poly.mk (strategy path).terminal)=(strategy path).claims path.length) :
    count (List.range N0) (generalFoldHistoryQuery strategy sizes path.length path)<T := by
  have doomed := checked_history_no_escape_preserves_doom strategy N0 T sizes degrees [] path
    checks initial noEscape
  simp only [List.nil_append] at doomed
  apply Nat.lt_of_not_ge
  intro many
  exact doomed (indexed_terminal_candidate_of_queries N0 sizes degrees (strategy path).roots
    (strategy path).challenges (strategy path).oracles (strategy path).weights
    (strategy path).claims T path.length positive halves (strategy path).terminal shape values residual many)

/-- Exact independent-query amplification for any fixed terminal state with
fewer than T passing seeds. This is ideal sampling, not Fiat-Shamir/QROM. -/
theorem checked_history_terminal_query_budget
    (strategy : List K→GeneralFoldTranscript K) (N0 T q : Nat)
    (sizes : Nat→Nat) (path : List K)
    (few : count (List.range N0) (generalFoldHistoryQuery strategy sizes path.length path)<T) :
    count (uniformTuples (List.range N0) q)
      (allQueriesPass (generalFoldHistoryQuery strategy sizes path.length path))≤(T-1)^q := by
  rw [independent_query_count]
  exact Nat.pow_le_pow_left (by omega) q

/-- All local and disclosed-terminal checks are part of acceptance, including
for an empty query vector. Full terminal oracle equality is an algebraic IOP
check here; relating it to a committed implementation remains separate. -/
def checkedHistoryTerminalChecks
    (strategy : List K→GeneralFoldTranscript K) (sizes degrees : Nat→Nat)
    (path : List K) : Prop :=
  checkedHistoryPath strategy sizes degrees [] path ∧
  (strategy path).terminal.length≤degrees path.length ∧
  (∀ y<sizes path.length,(strategy path).oracles path.length y=
    (Poly.mk (strategy path).terminal).eval ((strategy path).roots path.length^y)) ∧
  scalarRSResidual ((strategy path).weights path.length)
    (Poly.mk (strategy path).terminal)=(strategy path).claims path.length

/-- Literal checked acceptance count on every no-escape path. Invalid branches
reject even for q=0; no terminal correctness premise is assumed for them. -/
theorem checked_history_terminal_acceptance_budget
    (strategy : List K→GeneralFoldTranscript K) (N0 T q : Nat)
    (sizes degrees : Nat→Nat) (path : List K)
    (positive : ∀ j≤path.length,0<sizes j)
    (halves : ∀ j<path.length,sizes j=2*sizes (j+1))
    (initial : ¬indexedChainCandidate N0 sizes degrees (strategy []).roots
      (strategy []).challenges (strategy []).oracles (strategy []).weights
      (strategy []).claims T 0)
    (noEscape : ¬adaptivePathBad (checkedHistoryEscape strategy N0 T sizes degrees) [] path) :
    count (uniformTuples (List.range N0) q) (fun queries=>
      checkedHistoryTerminalChecks strategy sizes degrees path ∧
      allQueriesPass (generalFoldHistoryQuery strategy sizes path.length path) queries)≤(T-1)^q := by
  classical
  by_cases checks : checkedHistoryTerminalChecks strategy sizes degrees path
  · have few := checked_history_terminal_few_queries strategy N0 T sizes degrees path
      positive halves checks.1 initial noEscape checks.2.1 checks.2.2.1 checks.2.2.2
    have bound := checked_history_terminal_query_budget strategy N0 T q sizes path few
    exact Nat.le_trans (count_mono _ (fun _ h=>h.2)) bound
  · simp [count,checks]

end NearCompression
