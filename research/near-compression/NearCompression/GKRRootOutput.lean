import NearCompression.GKRCircuitPath
namespace NearCompression
open Lean.Grind ArenaCore.Security
variable {K : Type} [Field K]

/-- A Boolean root query evaluates the selected actual gate output. The
input dimension m and output dimension n need not coincide. -/
theorem gkr_root_output_wrong {m : Nat} (s : GKRLayerStrategy K m)
    (n : Nat) (wiring : Nat → GKRWiringGate) (bits : Nat → Bool)
    (queries : s.gates=gkrWeightedLayer n wiring [(genericRowBooleanPoint bits,1)])
    (mismatch : s.claimLeft []≠gkrLayerValues s.values wiring (genericRowBitIndex n bits)) :
    s.wrong := by
  have honest:=gkr_layer_initial_queries n s.values wiring [(genericRowBooleanPoint bits,1)]
  rw [gkr_left_initial_claim,gkr_root_query] at honest
  unfold GKRLayerStrategy.wrong
  rw [queries,honest]
  exact mismatch

/-- Concrete false-output version of the fixed-circuit path bound. The
claimed root value is compared with the actual circuit gate evaluation,
not with a caller-supplied abstract wrong-claim predicate. Terminal opening
correctness is still required by the checked-path relation. -/
theorem gkr_false_output_path_budget (sample : List K) (distinct : sample.Nodup)
    (strategy : (m : Nat) → List (GKRBlock K) → GKRLayerStrategy K m)
    (values : Nat → Nat → K) (wiring : Nat → Nat → GKRWiringGate)
    (m : Nat) (rest : List Nat) (history : List (GKRBlock K)) (depth : Nat)
    (n : Nat) (rootWiring : Nat → GKRWiringGate) (bits : Nat → Bool) (claimed : K)
    (fixed : (strategy m history).values=values depth)
    (queries : (strategy m history).gates=gkrWeightedLayer n rootWiring [(genericRowBooleanPoint bits,1)])
    (claim : (strategy m history).claimLeft []=claimed)
    (mismatch : claimed≠gkrLayerValues (values depth) rootWiring (genericRowBitIndex n bits)) :
    count (gkrChallengePaths sample (m::rest))
      (gkrCircuitCheckedToInput strategy values wiring depth history (m::rest))*sample.length≤
      ((m::rest).map (fun k => 4*k+1)).sum*(gkrChallengePaths sample (m::rest)).length := by
  apply gkr_circuit_checked_path_budget sample distinct strategy values wiring (m::rest) history depth
  intro k ks eq
  cases eq
  apply gkr_root_output_wrong _ n rootWiring bits queries
  rw [fixed,claim]
  exact mismatch
end NearCompression
