import NearCompression.WHIRTerminalWeight
namespace NearCompression
open Lean.Grind

/-- Bind compiled local terminal data to a supplied replay record. Authenticity
of that record is a separate transcript-refinement obligation. -/
def localTerminalBindingCheck {K : Type} [CommRing K] [DecidableEq K]
    (rowLog : Nat) (point tau : List K) (mixing expectedMixing weight claim expectedClaim : K) : Bool :=
  decide (point.length=rowLog ∧ tau.length=rowLog ∧ mixing=expectedMixing ∧
    weight=whirKernel tau point ∧ claim=expectedClaim)

theorem local_terminal_binding_checked {K : Type} [CommRing K] [DecidableEq K]
    (rowLog : Nat) (point tau : List K) (mixing expectedMixing weight claim expectedClaim : K)
    (checked : localTerminalBindingCheck rowLog point tau mixing expectedMixing weight claim expectedClaim=true) :
    point.length=rowLog ∧ tau.length=rowLog ∧ mixing=expectedMixing ∧
      weight=whirKernel tau point ∧ claim=expectedClaim := by
  exact of_decide_eq_true checked

end NearCompression
