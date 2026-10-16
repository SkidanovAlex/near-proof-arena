import NearCompression.GKRCheckedPath
namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K] [DecidableEq K]

/-- Finite transcript check, preserving dependence on the prior history.
A coefficient-list length bound is a computable sufficient degree check. -/
def gkrAxisMessageCheck (sent : List K→Poly K) (claim : List K→K) : List K→List K→Bool
  | _,[]=>true
  | history,r::rest=>decide ((sent history).coeffs.length≤3 ∧
      (sent history).eval 0+(sent history).eval 1=claim history ∧
      claim (history++[r])=(sent history).eval r) &&
      gkrAxisMessageCheck sent claim (history++[r]) rest

theorem gkr_axis_message_checked (sent : List K→Poly K) (claim : List K→K)
    (history challenges : List K) (checked : gkrAxisMessageCheck sent claim history challenges=true) :
    weightedSumcheckChecks sent claim history challenges := by
  induction challenges generalizing history with
  | nil => trivial
  | cons r rest ih =>
    simp only [gkrAxisMessageCheck,Bool.and_eq_true,decide_eq_true_eq] at checked
    exact ⟨(Poly.degLt_length _).mono checked.1.1,checked.1.2.1,checked.1.2.2,ih _ checked.2⟩

def gkrLayerMessageCheck {m : Nat} (s : GKRLayerStrategy K m) (block : GKRBlock K) : Bool :=
  decide (block.1.length=m ∧ block.2.1.length=m) &&
  gkrAxisMessageCheck s.sentLeft s.claimLeft [] block.1 &&
  decide (s.claimRight block.1 []=s.claimLeft block.1) &&
  gkrAxisMessageCheck (s.sentRight block.1) (s.claimRight block.1) [] block.2.1 &&
  decide (gkrLayerWiring m s.gates (fun i=>block.1.getD i 0) (fun i=>block.2.1.getD i 0)
    (s.a block.1 block.2.1) (s.b block.1 block.2.1)=s.claimRight block.1 block.2.1)

theorem gkr_layer_message_checked {m : Nat} (s : GKRLayerStrategy K m) (block : GKRBlock K)
    (checked : gkrLayerMessageCheck s block=true) :
    block.1.length=m ∧ block.2.1.length=m ∧ s.checked block := by
  simp only [gkrLayerMessageCheck,Bool.and_eq_true,decide_eq_true_eq] at checked
  obtain ⟨⟨⟨⟨shape,left⟩,bridge⟩,right⟩,wiring⟩:=checked
  exact ⟨shape.1,shape.2,gkr_axis_message_checked _ _ _ _ left,bridge,
    gkr_axis_message_checked _ _ _ _ right,wiring⟩
end NearCompression
