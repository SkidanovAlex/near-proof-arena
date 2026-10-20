import NearCompression.ScalarRSReconstructedTerminal

/-! Bridge from the degree-one terminal reconstruction to the indexed oracle
premise of weighted folding. Pair leaves store positions i and i+half, not
adjacent positions. Typed tree binding and byte-encoding refinement are separate. -/
namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

/-- Natural-domain f(x),f(-x) layout for one scalar lane. -/
def weightedTerminalPairLeaves (half : Nat) (oracle : Nat → K) : List (List (K×K)) :=
  (List.range half).map (fun i => [(oracle i,oracle (i+half))])

/-- Exact pair-tree reconstruction implies every indexed scalar terminal
value is the disclosed constant, without a degree premise on the oracle. -/
theorem weighted_terminal_pair_constant (half : Nat) (oracle : Nat → K)
    (anchors : List K) (shape : anchors.length=half) (terminal : K)
    (same : weightedTerminalPairLeaves half oracle=reconstructedRSLeaves [[terminal]] anchors) :
    ∀ y,y<2*half → oracle y=terminal := by
  have eval (x : K) : (Poly.mk [terminal]).eval x=terminal := by
    simp only [Poly.eval,Poly.evalL]
    grind
  have pair (i : Nat) (hi : i<half) : (oracle i,oracle (i+half))=(terminal,terminal) := by
    have cell :=  congrArg (fun leaves => leaves.getD i []) same
    simp only [weightedTerminalPairLeaves,reconstructedRSLeaves] at cell
    have ha : i<anchors.length := by omega
    simp [List.getD,hi,ha,eval] at cell
    exact Prod.ext cell.1 cell.2
  intro y hy
  by_cases first : y<half
  · exact congrArg Prod.fst (pair y first)
  · have second : y-half<half := by omega
    have h := congrArg Prod.snd (pair (y-half) second)
    simpa only [Nat.sub_add_cancel (by omega : half≤y)] using h

/-- The executable terminal's typed reconstruction contract gives either a
concrete tree-root collision or the exact terminal authentication required by
weighted replay soundness. The root function is fixed for the stage context. -/
theorem weighted_terminal_collision_or_authenticated {Digest : Type}
    [DecidableEq K] [DecidableEq Digest]
    (root : List (List (K×K)) → Digest) (half : Nat) (oracle : Nat → K)
    (anchors : List K) (shape : anchors.length=half) (terminal weight claim : K)
    (checked : reconstructedRSChecks root 1 1 [[terminal]] [[weight]] anchors
      (weightedTerminalPairLeaves half oracle) claim=true) :
    ReconstructedRSTreeCollision root (reconstructedRSLeaves [[terminal]] anchors)
      (weightedTerminalPairLeaves half oracle) ∨
    (∀ y,y<2*half → oracle y=terminal) := by
  rcases reconstructed_rs_collision_or_correct root 1 1 [[terminal]] [[weight]] anchors
    (weightedTerminalPairLeaves half oracle) claim checked with collision | correct
  · exact Or.inl collision
  · exact Or.inr (weighted_terminal_pair_constant half oracle anchors shape terminal correct.1)

/-- Discharges the pointwise terminal-oracle premise under explicit absence
of this reconstruction collision; it does not assert SHA-384 security. -/
theorem weighted_terminal_binding_authenticated {Digest : Type}
    [DecidableEq K] [DecidableEq Digest]
    (root : List (List (K×K)) → Digest) (half : Nat) (oracle : Nat → K)
    (anchors : List K) (shape : anchors.length=half) (terminal weight claim : K)
    (checked : reconstructedRSChecks root 1 1 [[terminal]] [[weight]] anchors
      (weightedTerminalPairLeaves half oracle) claim=true)
    (binding : ¬ReconstructedRSTreeCollision root (reconstructedRSLeaves [[terminal]] anchors)
      (weightedTerminalPairLeaves half oracle)) :
    ∀ y,y<2*half → oracle y=terminal := by
  rcases weighted_terminal_collision_or_authenticated root half oracle anchors shape
    terminal weight claim checked with collision | authenticated
  · exact False.elim (binding collision)
  · exact authenticated

end NearCompression
