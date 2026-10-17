import NearCompression.RepeatedAffineFold
import NearCompression.StructuredWeightTensor

/-! Actual pair-array folds on consecutive lane blocks. The terminal dot is
exactly the weighted lane MLE sum, with little-endian adjacent-pair folding.
No residual/PCS claim is presumed in this representation theorem. -/
namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

def foldedPairFunction (r : K) (f : Nat → K×K) (i : Nat) : K×K :=
  ((1-r)*(f (2*i)).1+r*(f (2*i+1)).1,(1-r)*(f (2*i)).2+r*(f (2*i+1)).2)

theorem pair_fold_range (r : K) (N : Nat) (f : Nat → K×K) :
    affineFoldVector r ((List.range (2*N)).map f)=
      (List.range N).map (foldedPairFunction r f) := by
  induction N generalizing f with
  | zero => rfl
  | succ N ih =>
    have size : 2*(N+1)=2*N+1+1 := by omega
    rw [size,List.range_succ_eq_map,List.map_cons,List.map_map,
      List.range_succ_eq_map,List.map_cons,List.map_map]
    simp only [Function.comp_def,affineFoldVector]
    rw [ih]
    rw [List.range_succ_eq_map,List.map_cons,List.map_map]
    congr 1
    · simp only [foldedPairFunction]
      congr 1 <;> grind

/-- One lane of length 2^n folds to its two MLE coordinate values. -/
theorem pair_fold_block_terminal (point : List K) (f : Nat → K×K) :
    affineFoldFinal ((List.range (2^point.length)).map f) point=
      [(genericRowMLE point.length (fun i => (f i).1) (fun i => point.getD i 0),
        genericRowMLE point.length (fun i => (f i).2) (fun i => point.getD i 0))] := by
  induction point generalizing f with
  | nil => simp [affineFoldFinal,genericRowMLE]
  | cons r rest ih =>
    have power : 2^(r::rest).length=2*(2^rest.length) := by simp [Nat.pow_succ,Nat.mul_comm]
    rw [power,affineFoldFinal,pair_fold_range,ih]
    simp only [foldedPairFunction,generic_row_mle_add,generic_row_mle_scale]
    simp only [List.length_cons,genericRowMLE,List.getD_cons_zero,List.getD_cons_succ]

private theorem pair_fold_append (r : K) : ∀ xs ys : List (K×K),xs.length%2=0 →
    affineFoldVector r (xs++ys)=affineFoldVector r xs++affineFoldVector r ys
  | [],ys,_ => rfl
  | [_],ys,h => by simp at h
  | a::b::xs,ys,h => by
    have even : xs.length%2=0 := by simp only [List.length_cons] at h; omega
    simp only [List.cons_append,affineFoldVector,pair_fold_append r xs ys even]

theorem pair_fold_blocks_append (point : List K) (xs ys : List (K×K)) (lanes : Nat)
    (shape : xs.length=lanes*2^point.length) :
    affineFoldFinal (xs++ys) point=affineFoldFinal xs point++affineFoldFinal ys point := by
  induction point generalizing xs ys with
  | nil => rfl
  | cons r rest ih =>
    have even : xs.length%2=0 := by simp [shape,Nat.pow_succ,←Nat.mul_assoc]
    rw [affineFoldFinal,pair_fold_append r xs ys even]
    exact ih (affineFoldVector r xs) (affineFoldVector r ys)
      (affine_fold_next_shape xs r rest.length lanes shape)

/-- The array constructed by the weighted prover, after all lanes have been
expanded to the same common-degree cube. Coefficient value is the first coordinate. -/
def weightedLaneBlocks (n : Nat) : List ((Nat → K)×(Nat → K)) → List (K×K)
  | [] => []
  | lane::lanes => (List.range (2^n)).map (fun i => (lane.1 i,lane.2 i))++weightedLaneBlocks n lanes

omit [Field K] in
theorem weighted_lane_blocks_shape (n : Nat) (lanes : List ((Nat → K)×(Nat → K))) :
    (weightedLaneBlocks n lanes).length=lanes.length*2^n := by
  induction lanes with
  | nil => simp [weightedLaneBlocks]
  | cons lane lanes ih => simp only [weightedLaneBlocks,List.length_append,List.length_map,List.length_range,List.length_cons,ih]; grind

theorem weighted_lane_blocks_terminal (point : List K) (lanes : List ((Nat → K)×(Nat → K))) :
    affineFoldFinal (weightedLaneBlocks point.length lanes) point=
      lanes.map (fun lane =>
        (genericRowMLE point.length lane.1 (fun i => point.getD i 0),
         genericRowMLE point.length lane.2 (fun i => point.getD i 0))) := by
  induction lanes with
  | nil =>
    have empty : ∀ point : List K,affineFoldFinal ([] : List (K×K)) point=[] := by
      intro point
      induction point with
      | nil => rfl
      | cons r rs ih => exact ih
    exact empty point
  | cons lane lanes ih =>
    unfold weightedLaneBlocks
    rw [pair_fold_blocks_append point _ _ 1 (by simp),pair_fold_block_terminal,ih]
    rfl

theorem weighted_terminal_dot (point : List K) (lanes : List ((Nat → K)×(Nat → K))) :
    affineFoldDot (affineFoldFinal (weightedLaneBlocks point.length lanes) point)=
      (lanes.map (fun lane =>
        genericRowMLE point.length lane.1 (fun i => point.getD i 0)*
        genericRowMLE point.length lane.2 (fun i => point.getD i 0))).sum := by
  rw [weighted_lane_blocks_terminal]
  induction lanes with
  | nil => rfl
  | cons lane lanes ih => simp only [List.map_cons,List.sum_cons,affineFoldDot,ih]

/-- Lane pairs obtained from a polynomial tuple and its exact weight tables.
Lengths should match in the caller; truncation is exposed by the recursive definition. -/
def polynomialWeightLanes : List (Poly K) → List (Nat → K) → List ((Nat → K)×(Nat → K))
  | p::ps,w::ws => (p.coeff,w)::polynomialWeightLanes ps ws
  | _,_ => []

theorem weighted_terminal_beta (point : List K) (lanes : List (Poly K)) (tables : List (Nat → K)) :
    affineFoldDot (affineFoldFinal
      (weightedLaneBlocks point.length (polynomialWeightLanes lanes tables)) point)=
      weightedLaneValues (functionalBatchCoefficients point.length tables (fun i => point.getD i 0))
        (lanes.map (fun p => genericRowMLE point.length p.coeff (fun i => point.getD i 0))) := by
  rw [weighted_terminal_dot]
  induction lanes generalizing tables with
  | nil => cases tables <;> simp [polynomialWeightLanes,weightedLaneValues,functionalBatchCoefficients]
  | cons p ps ih =>
    cases tables with
    | nil => simp [polynomialWeightLanes,weightedLaneValues,functionalBatchCoefficients]
    | cons w ws =>
      simp only [polynomialWeightLanes,List.map_cons,List.sum_cons,functionalBatchCoefficients,weightedLaneValues]
      have prior := ih ws
      simp only [functionalBatchCoefficients] at prior
      rw [prior]
      grind

private theorem pair_dot_append (xs ys : List (K×K)) :
    affineFoldDot (xs++ys)=affineFoldDot xs+affineFoldDot ys := by
  induction xs with
  | nil => simp only [List.nil_append,affineFoldDot]; grind
  | cons x xs ih => simp only [List.cons_append,affineFoldDot,ih]; grind

private theorem pair_dot_map {A : Type} (indices : List A) (f g : A → K) :
    affineFoldDot (indices.map (fun i => (f i,g i)))=(indices.map (fun i => f i*g i)).sum := by
  induction indices with
  | nil => rfl
  | cons i indices ih => simp only [List.map_cons,List.sum_cons,affineFoldDot,ih]

/-- The initial array dot is exactly the requested coefficient-table functional,
so the sumcheck theorem's false-dot premise is the original false claim. -/
theorem weighted_initial_functional (n : Nat) (lanes : List (Poly K)) (tables : List (Nat → K)) :
    affineFoldDot (weightedLaneBlocks n (polynomialWeightLanes lanes tables))=
      coefficientTableFunctional n tables lanes := by
  have zeros : ∀ indices : List Nat,(indices.map (fun _ => (0:K))).sum=0 := by
    intro indices
    induction indices with
    | nil => rfl
    | cons i indices ih => simp only [List.map_cons,List.sum_cons,ih]; grind
  have sumAdd : ∀ (indices : List Nat) (f g : Nat → K),
      (indices.map (fun i => f i+g i)).sum=(indices.map f).sum+(indices.map g).sum := by
    intro indices
    induction indices with
    | nil => intros; simp only [List.map_nil,List.sum_nil]; grind
    | cons i indices ih => intros; simp only [List.map_cons,List.sum_cons,ih]; grind
  induction lanes generalizing tables with
  | nil => cases tables <;> simp [polynomialWeightLanes,weightedLaneBlocks,affineFoldDot,
      coefficientTableFunctional,weightedLaneValues,zeros]
  | cons p ps ih =>
    cases tables with
    | nil => simp [polynomialWeightLanes,weightedLaneBlocks,affineFoldDot,
        coefficientTableFunctional,weightedLaneValues,zeros]
    | cons w ws =>
      simp only [polynomialWeightLanes,weightedLaneBlocks,pair_dot_append,pair_dot_map]
      rw [ih]
      simp only [coefficientTableFunctional,List.map_cons,weightedLaneValues,sumAdd]
      congr 1
      congr 1
      apply List.map_congr_left
      intro i hi
      grind

end NearCompression
