import NearCompression.GKRAxisExecution
namespace NearCompression
open Lean.Grind
variable {K : Type} [Field K]

def gkrQueryWeights (n : Nat) : List ((Nat → K) × K) → Nat → K
  | [],_ => 0
  | (point,scale)::rest,i => scale*rowEqualityWeight n point i+gkrQueryWeights n rest i

def gkrQueryFunctional (n : Nat) (values : Nat → K) : List ((Nat → K) × K) → K
  | [] => 0
  | (point,scale)::rest => scale*genericRowMLE n values point+gkrQueryFunctional n values rest

private theorem sum_scaled_add (indices : List Nat) (a b : Nat → K) (scale : K) :
    (indices.map (fun i => scale*a i+b i)).sum=
      scale*(indices.map a).sum+(indices.map b).sum := by
  induction indices with
  | nil => simp; grind
  | cons i rest ih => simp only [List.map_cons,List.sum_cons,ih]; grind

theorem gkr_query_weights_functional (n : Nat) (values : Nat → K)
    (queries : List ((Nat → K) × K)) :
    cubeSum n (fun i => gkrQueryWeights n queries i*values i)=
      gkrQueryFunctional n values queries := by
  induction queries with
  | nil =>
    have zero : ∀ indices : List Nat,(indices.map (fun _ => (0:K))).sum=0 := by
      intro indices
      induction indices with
      | nil => rfl
      | cons i rest ih => simp only [List.map_cons,List.sum_cons,ih]; grind
    change ((List.range (2^n)).map (fun i => (0:K)*values i)).sum=0
    have eq : (fun i => (0:K)*values i)=(fun _ => (0:K)) := by funext i; grind
    rw [eq]
    exact zero _
  | cons q qs ih =>
    have pointwise : (fun i => gkrQueryWeights n (q::qs) i*values i)=
        fun i => q.2*(rowEqualityWeight n q.1 i*values i)+gkrQueryWeights n qs i*values i := by
      funext i
      simp only [gkrQueryWeights]
      grind
    rw [pointwise]
    unfold cubeSum
    rw [sum_scaled_add]
    change q.2*cubeSum n (fun i => rowEqualityWeight n q.1 i*values i)+
      cubeSum n (fun i => gkrQueryWeights n qs i*values i)=_
    rw [row_equality_dot,ih]
    rfl

def gkrLayerValues (values : Nat → K) (gates : Nat → GKRWiringGate) (i : Nat) : K :=
  gkrGateValue (gates i).op (values (gates i).left) (values (gates i).right)

/-- Includes every padded output slot of the layer. -/
def gkrWeightedLayer (n : Nat) (gates : Nat → GKRWiringGate)
    (queries : List ((Nat → K) × K)) : List (GKRWiringGate × K) :=
  (List.range (2^n)).map (fun i => (gates i,gkrQueryWeights n queries i))

theorem gkr_layer_initial_queries (n : Nat) (values : Nat → K) (gates : Nat → GKRWiringGate)
    (queries : List ((Nat → K) × K)) :
    gkrStateClaim values (gkrLeftAxisTerms values (gkrWeightedLayer n gates queries))=
      gkrQueryFunctional n (gkrLayerValues values gates) queries := by
  rw [gkr_left_initial_claim]
  simp only [gkrWeightedLayer,List.map_map]
  exact gkr_query_weights_functional n (gkrLayerValues values gates) queries

theorem gkr_next_queries (n : Nat) (values left right : Nat → K) (gamma : K) :
    gkrQueryFunctional n values [(left,1),(right,gamma)]=gkrInputFunctional n left right gamma values := by
  simp only [gkrQueryFunctional,gkrInputFunctional]
  grind

theorem gkr_root_query (n : Nat) (values : Nat → K) (bits : Nat → Bool) :
    gkrQueryFunctional n values [(genericRowBooleanPoint bits,1)]=
      values (genericRowBitIndex n bits) := by
  simp only [gkrQueryFunctional,generic_row_mle_boolean]
  grind
end NearCompression
