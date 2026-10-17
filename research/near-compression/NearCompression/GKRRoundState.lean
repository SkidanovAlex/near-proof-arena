import NearCompression.GKRHonestRound

/-! Functional refinement of adjacent bit rounds of the optimized GKR prover.
Indices are the original gate input indices shifted by the consumed bit count.
The total function model leaves native array bounds and mutable writes outside. -/
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

structure GKRIndexedTerm (K : Type) where
  op : GKRBinaryOp
  axis : Bool
  index : Nat
  weight : K
  other : K

def gkrIndexedRoundTerm (values : Nat → K) (t : GKRIndexedTerm K) : GKRRoundTerm K :=
  ⟨t.op,t.axis,decide (t.index%2=1),t.weight,
   values (2*(t.index/2)),values (2*(t.index/2)+1),t.other⟩

def gkrFoldInput (values : Nat → K) (r : K) (i : Nat) : K :=
  values (2*i)+r*(values (2*i+1)-values (2*i))

def gkrAdvanceTerm (r : K) (t : GKRIndexedTerm K) : GKRIndexedTerm K :=
  ⟨t.op,t.axis,t.index/2,t.weight*(if t.index%2=1 then r else 1-r),t.other⟩

def gkrIndexedContribution (values : Nat → K) (t : GKRIndexedTerm K) : K :=
  t.weight*(if t.axis then gkrGateValue t.op t.other (values t.index)
    else gkrGateValue t.op (values t.index) t.other)

def gkrStateClaim (values : Nat → K) (terms : List (GKRIndexedTerm K)) : K :=
  (terms.map (gkrIndexedContribution values)).sum

def gkrStatePolynomial (values : Nat → K) (terms : List (GKRIndexedTerm K)) : Poly K :=
  gkrRoundPolynomial (terms.map (gkrIndexedRoundTerm values))

omit [Field K] in
theorem gkr_index_selected_value (values : Nat → K) (i : Nat) :
    (if decide (i%2=1) then values (2*(i/2)+1) else values (2*(i/2)))=values i := by
  have bound := Nat.mod_lt i (by decide : 0<2)
  have decomp := Nat.mod_add_div i 2
  by_cases h : i%2=1
  · simp [h]
    congr 1
    omega
  · simp [h]
    congr 1
    omega

theorem gkr_state_endpoints (values : Nat → K) (terms : List (GKRIndexedTerm K)) :
    (gkrStatePolynomial values terms).eval 0+(gkrStatePolynomial values terms).eval 1=
      gkrStateClaim values terms := by
  rw [gkrStatePolynomial,gkr_round_polynomial_endpoints]
  unfold gkrStateClaim
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro t ht
  exact congrArg (fun x => t.weight*(if t.axis then gkrGateValue t.op t.other x
    else gkrGateValue t.op x t.other)) (gkr_index_selected_value values t.index)

theorem gkr_advance_contribution (values : Nat → K) (t : GKRIndexedTerm K) (r : K) :
    gkrIndexedContribution (gkrFoldInput values r) (gkrAdvanceTerm r t)=
      gkrRoundTermValue (gkrIndexedRoundTerm values t) r := by
  dsimp only [gkrIndexedContribution,gkrFoldInput,gkrAdvanceTerm,gkrRoundTermValue,
    gkrIndexedRoundTerm,gkrAxisGate]
  by_cases h : t.index%2=1 <;> simp [h]

theorem gkr_state_advance (values : Nat → K) (terms : List (GKRIndexedTerm K)) (r : K) :
    gkrStateClaim (gkrFoldInput values r) (terms.map (gkrAdvanceTerm r))=
      (gkrStatePolynomial values terms).eval r := by
  rw [gkrStatePolynomial,gkr_round_polynomial_eval]
  unfold gkrStateClaim
  simp only [List.map_map,Function.comp_def,gkr_advance_contribution]

theorem gkr_state_degree (values : Nat → K) (terms : List (GKRIndexedTerm K)) :
    (gkrStatePolynomial values terms).DegLt 3 :=
  gkr_round_polynomial_degree _

/-- Adversarial message fixed before r; exact transition to the folded state,
without an assumed honest round polynomial or assumed endpoint linkage. -/
theorem gkr_state_bad_count (values : Nat → K) (terms : List (GKRIndexedTerm K))
    (sent : Poly K) (claim : K) (degree : sent.DegLt 3)
    (endpoints : sent.eval 0+sent.eval 1=claim)
    (wrong : claim≠gkrStateClaim values terms)
    (sample : List K) (distinct : sample.Nodup) :
    count sample (fun r => sent.eval r=
      gkrStateClaim (gkrFoldInput values r) (terms.map (gkrAdvanceTerm r)))≤2 := by
  have discrepancy : sent.eval 0+sent.eval 1≠
      (gkrStatePolynomial values terms).eval 0+(gkrStatePolynomial values terms).eval 1 := by
    rw [endpoints,gkr_state_endpoints]
    exact wrong
  have bound := instruction_round_bad_roots_degree sent (gkrStatePolynomial values terms) 3
    degree (gkr_state_degree values terms) discrepancy sample distinct
  simp only [gkr_state_advance]
  omega
end NearCompression
