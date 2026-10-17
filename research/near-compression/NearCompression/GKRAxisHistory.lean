import NearCompression.GKRAxisExecution
import NearCompression.GKRAdaptiveRounds
namespace NearCompression
open Lean.Grind
variable {K : Type} [Field K]

/-- Exact list-path/point conversion, preserving little-endian challenge order. -/
theorem gkr_round_history_axis (values : Nat → K) (terms : List (GKRIndexedTerm K))
    (history : List K) :
    gkrRoundStateFinal values terms history=
      (gkrAxisValues history.length values (fun i => history.getD i 0),
       terms.map (fun t => gkrAxisTerm history.length t (fun i => history.getD i 0))) := by
  induction history generalizing values terms with
  | nil => simp [gkrRoundStateFinal,gkrAxisValues,gkrAxisTerm]
  | cons r rs ih =>
    rw [gkrRoundStateFinal,ih]
    simp only [List.length_cons,gkrAxisValues,gkrAxisTerm,List.getD_cons_zero,
      List.getD_cons_succ,List.map_map]
    rfl

theorem gkr_history_axis_reset (values : Nat → K) (gates : List (GKRWiringGate × K))
    (ru : List K) (bounds : ∀ item∈gates,item.1.left<2^ru.length) :
    let state := gkrRoundStateFinal values (gkrLeftAxisTerms values gates) ru
    gkrStateClaim state.1 state.2=
      gkrStateClaim values (gkrRightAxisTerms ru.length values (fun i => ru.getD i 0) gates) := by
  rw [gkr_round_history_axis]
  exact gkr_axis_reset ru.length values (fun i => ru.getD i 0) gates bounds

theorem gkr_history_terminal_wiring (values : Nat → K) (gates : List (GKRWiringGate × K))
    (ru rv : List K) (shape : rv.length=ru.length)
    (bounds : ∀ item∈gates,item.1.right<2^ru.length) :
    let state := gkrRoundStateFinal values
      (gkrRightAxisTerms ru.length values (fun i => ru.getD i 0) gates) rv
    gkrStateClaim state.1 state.2=
      gkrLayerWiring ru.length gates (fun i => ru.getD i 0) (fun i => rv.getD i 0)
        (genericRowMLE ru.length values (fun i => ru.getD i 0))
        (genericRowMLE ru.length values (fun i => rv.getD i 0)) := by
  rw [gkr_round_history_axis,shape]
  exact gkr_axes_terminal_wiring ru.length values (fun i => ru.getD i 0)
    (fun i => rv.getD i 0) gates bounds
end NearCompression
