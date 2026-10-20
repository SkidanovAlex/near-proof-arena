import NearCompression.GKRLayerTransition

/-! Exact one-round arithmetic of pq384_seed_gkr.prove. Data describe the
current prefix and are fixed before the next challenge. Connecting the indices
and folded arrays of successive prefixes is a separate state invariant. -/
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

/-- axis=false folds the left input; axis=true folds the right input. -/
structure GKRRoundTerm (K : Type) where
  op : GKRBinaryOp
  axis : Bool
  indexBit : Bool
  weight : K
  low : K
  high : K
  other : K

def gkrAxisGate (t : GKRRoundTerm K) (x : K) : K :=
  if t.axis then gkrGateValue t.op t.other x else gkrGateValue t.op x t.other

def gkrRoundTermValue (t : GKRRoundTerm K) (r : K) : K :=
  (t.weight * (if t.indexBit then r else 1-r)) *
    gkrAxisGate t (t.low+r*(t.high-t.low))

def gkrRoundTermPolynomial (t : GKRRoundTerm K) : Poly K :=
  let e0 : K := if t.indexBit then 0 else 1
  let de : K := if t.indexBit then 1 else -1
  let g0 := gkrAxisGate t t.low
  let dg := gkrAxisGate t t.high-g0
  Poly.mk [t.weight*e0*g0,t.weight*(e0*dg+de*g0),t.weight*de*dg]

theorem gkr_axis_gate_affine (t : GKRRoundTerm K) (r : K) :
    gkrAxisGate t (t.low+r*(t.high-t.low)) =
      gkrAxisGate t t.low+r*(gkrAxisGate t t.high-gkrAxisGate t t.low) := by
  rcases t with ⟨op,axis,bit,w,lo,hi,other⟩
  cases axis <;> cases op <;> simp [gkrAxisGate,gkrGateValue] <;> grind

theorem gkr_round_term_eval (t : GKRRoundTerm K) (r : K) :
    (gkrRoundTermPolynomial t).eval r=gkrRoundTermValue t r := by
  unfold gkrRoundTermValue
  rw [gkr_axis_gate_affine]
  unfold gkrRoundTermPolynomial
  cases h : t.indexBit <;> simp [Poly.eval,Poly.evalL] <;> grind

theorem gkr_round_term_degree (t : GKRRoundTerm K) :
    (gkrRoundTermPolynomial t).DegLt 3 :=
  Poly.degLt_length _

theorem gkr_round_term_endpoints (t : GKRRoundTerm K) :
    (gkrRoundTermPolynomial t).eval 0+(gkrRoundTermPolynomial t).eval 1=
      t.weight*gkrAxisGate t (if t.indexBit then t.high else t.low) := by
  rw [gkr_round_term_eval,gkr_round_term_eval]
  cases h : t.indexBit <;> simp [gkrRoundTermValue,h] <;> grind

def gkrRoundPolynomial : List (GKRRoundTerm K) → Poly K
  | [] => Poly.zero
  | t::rest => gkrRoundTermPolynomial t+gkrRoundPolynomial rest

theorem gkr_round_polynomial_degree (terms : List (GKRRoundTerm K)) :
    (gkrRoundPolynomial terms).DegLt 3 := by
  induction terms with
  | nil => exact (Poly.degLt_length Poly.zero).mono (by simp [Poly.zero])
  | cons t rest ih => exact Poly.degLt_add (gkr_round_term_degree t) ih

theorem gkr_round_polynomial_eval (terms : List (GKRRoundTerm K)) (r : K) :
    (gkrRoundPolynomial terms).eval r=(terms.map (fun t => gkrRoundTermValue t r)).sum := by
  induction terms with
  | nil => rfl
  | cons t rest ih => simp [gkrRoundPolynomial,Poly.eval_add,gkr_round_term_eval,ih]

theorem gkr_round_polynomial_endpoints (terms : List (GKRRoundTerm K)) :
    (gkrRoundPolynomial terms).eval 0+(gkrRoundPolynomial terms).eval 1=
      (terms.map (fun t => t.weight*gkrAxisGate t (if t.indexBit then t.high else t.low))).sum := by
  induction terms with
  | nil => simp [gkrRoundPolynomial,Poly.eval,Poly.zero]; grind
  | cons t rest ih =>
    simp only [gkrRoundPolynomial,Poly.eval_add,List.map_cons,List.sum_cons]
    have ht := gkr_round_term_endpoints t
    grind

/-- Literal false-to-true round event. In particular sent and terms cannot
be selected as functions of the challenge quantified inside count. -/
theorem gkr_honest_round_bad_count (terms : List (GKRRoundTerm K))
    (sent : Poly K) (claim : K) (degree : sent.DegLt 3)
    (endpoints : sent.eval 0+sent.eval 1=claim)
    (wrong : claim≠(terms.map (fun t => t.weight*
      gkrAxisGate t (if t.indexBit then t.high else t.low))).sum)
    (sample : List K) (distinct : sample.Nodup) :
    count sample (fun r => sent.eval r=(terms.map (fun t => gkrRoundTermValue t r)).sum)≤2 := by
  have discrepancy : sent.eval 0+sent.eval 1≠
      (gkrRoundPolynomial terms).eval 0+(gkrRoundPolynomial terms).eval 1 := by
    rw [endpoints,gkr_round_polynomial_endpoints]
    exact wrong
  have bound := instruction_round_bad_roots_degree sent (gkrRoundPolynomial terms) 3
    degree (gkr_round_polynomial_degree terms) discrepancy sample distinct
  simp only [gkr_round_polynomial_eval] at bound
  omega
end NearCompression
