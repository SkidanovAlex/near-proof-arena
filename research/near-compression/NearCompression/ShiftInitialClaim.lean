import NearCompression.ShiftReductionPolynomial

namespace NearCompression
open Lean.Grind ZkFormal.Air ZkFormal.Algebra
variable {K : Type} [Field K]

/-- Inner product of row MLEs over the Boolean cube is the exact row-table
dot product. This identity does not hold over arbitrary off-cube sums. -/
theorem row_mle_cube_dot (n : Nat) (weights values : Nat→K) :
    whirCubeSum n (fun bits=>packedGridEval n weights bits*packedGridEval n values bits)=
      cubeSum n (fun i=>weights i*values i) := by
  induction n generalizing weights values with
  | zero => simp [whirCubeSum,packedGridEval,genericRowMLE,cubeSum];grind
  | succ n ih =>
    rw [whirCubeSum,cube_sum_split]
    simp only [packed_grid_eval_cons]
    have even : (fun bits=>((1-0)*packedGridEval n (fun i=>weights (2*i)) bits+
        0*packedGridEval n (fun i=>weights (2*i+1)) bits)*
        ((1-0)*packedGridEval n (fun i=>values (2*i)) bits+
        0*packedGridEval n (fun i=>values (2*i+1)) bits))=
        (fun bits=>packedGridEval n (fun i=>weights (2*i)) bits*packedGridEval n (fun i=>values (2*i)) bits) := by
      funext bits;grind
    have odd : (fun bits=>((1-1)*packedGridEval n (fun i=>weights (2*i)) bits+
        1*packedGridEval n (fun i=>weights (2*i+1)) bits)*
        ((1-1)*packedGridEval n (fun i=>values (2*i)) bits+
        1*packedGridEval n (fun i=>values (2*i+1)) bits))=
        (fun bits=>packedGridEval n (fun i=>weights (2*i+1)) bits*packedGridEval n (fun i=>values (2*i+1)) bits) := by
      funext bits;grind
    rw [even,odd,ih,ih]

/-- Ordinary borrow kernel opens the actual cyclic-next column, using the
predecessor permutation only on Boolean row indices. -/
theorem shift_kernel_initial_sum (target : List K) (values : Nat→K) :
    whirCubeSum target.length (fun bits=>shiftKernelDP (target.zip bits) 0 1*
      packedGridEval target.length values bits)=
    packedGridEval target.length (fun i=>values ((i+1)%(2^target.length))) target := by
  have replace := air_cube_boolean_congr target.length
    (fun bits=>shiftKernelDP (target.zip bits) 0 1*packedGridEval target.length values bits)
    (fun bits=>packedGridEval target.length (cyclicRowWeight target.length (fun i=>target.getD i 0)) bits*
      packedGridEval target.length values bits)
    (by intro bits length _;rw [shift_kernel_zipped_row_mle target bits length])
  rw [replace,row_mle_cube_dot]
  unfold cubeSum cyclicRowWeight
  rw [cyclic_predecessor_dot (2^target.length) (Nat.two_pow_pos _)]
  exact row_equality_dot target.length (fun i=>target.getD i 0) _

/-- Initial scalar shift identity, including the alpha^width offset used by
concatenated current/next power batching. -/
theorem shift_reduction_initial_sum (target : List K) (values : Nat→K) (alpha : K) (width : Nat) :
    whirCubeSum target.length (fun bits=>shiftReductionWeight target bits alpha width*
      packedGridEval target.length values bits)=
    packedGridEval target.length values target+alpha^width*
      packedGridEval target.length (fun i=>values ((i+1)%(2^target.length))) target := by
  have distribute : (fun bits=>shiftReductionWeight target bits alpha width*packedGridEval target.length values bits)=
      (fun bits=>whirKernel target bits*packedGridEval target.length values bits+
        alpha^width*(shiftKernelDP (target.zip bits) 0 1*packedGridEval target.length values bits)) := by
    funext bits;unfold shiftReductionWeight;grind
  rw [distribute,whir_cube_add,whir_cube_scale,air_equality_weighted_mle,shift_kernel_initial_sum]

theorem lane_power_batch_append (alpha : K) (xs ys : List K) :
    lanePowerBatch alpha (xs++ys)=lanePowerBatch alpha xs+alpha^xs.length*lanePowerBatch alpha ys := by
  induction xs with
  | nil => simp only [List.nil_append,lanePowerBatch,List.length_nil,Semiring.pow_zero];grind
  | cons x xs ih => simp only [List.cons_append,lanePowerBatch,ih,List.length_cons,Semiring.pow_succ];grind

/-- Column power batching commutes with interpolation of the same row table. -/
theorem row_mle_lane_batch (n : Nat) (columns : List (Nat→K)) (point : List K) (alpha : K) :
    packedGridEval n (fun r=>lanePowerBatch alpha (columns.map (fun col=>col r))) point=
      lanePowerBatch alpha (columns.map (fun col=>packedGridEval n col point)) := by
  induction columns with
  | nil => exact generic_row_mle_zero _ _
  | cons col rest ih =>
    simp only [List.map_cons,lanePowerBatch]
    unfold packedGridEval
    rw [generic_row_mle_add,generic_row_mle_scale]
    exact congrArg (fun v=>genericRowMLE n col (fun i=>point.getD i 0)+alpha*v) ih

/-- Exact honest start claim of pq384_shift: all current columns followed by
all cyclic-next columns, sharing one power-batching challenge. -/
theorem shift_reduction_batched_initial (target : List K) (columns : List (Nat→K)) (alpha : K) :
    whirCubeSum target.length (fun bits=>shiftReductionWeight target bits alpha columns.length*
      lanePowerBatch alpha (columns.map (fun col=>packedGridEval target.length col bits)))=
    lanePowerBatch alpha
      (columns.map (fun col=>packedGridEval target.length col target)++
       columns.map (fun col=>packedGridEval target.length (fun i=>col ((i+1)%(2^target.length))) target)) := by
  have batch (bits : List K) := row_mle_lane_batch target.length columns bits alpha
  have replace : (fun bits=>shiftReductionWeight target bits alpha columns.length*
      lanePowerBatch alpha (columns.map (fun col=>packedGridEval target.length col bits)))=
      (fun bits=>shiftReductionWeight target bits alpha columns.length*
        packedGridEval target.length (fun r=>lanePowerBatch alpha (columns.map (fun col=>col r))) bits) := by
    funext bits;rw [batch]
  rw [replace,shift_reduction_initial_sum,row_mle_lane_batch,lane_power_batch_append,List.length_map]
  have next:=row_mle_lane_batch target.length
    (columns.map (fun col=>fun i=>col ((i+1)%(2^target.length)))) target alpha
  simpa only [List.map_map,Function.comp_def] using congrArg
    (fun v=>lanePowerBatch alpha (columns.map (fun col=>packedGridEval target.length col target))+alpha^columns.length*v) next

def shiftHonestClaims (target : List K) (columns : List (Nat→K)) : List K :=
  columns.map (fun col=>packedGridEval target.length col target)++
    columns.map (fun col=>packedGridEval target.length (fun i=>col ((i+1)%(2^target.length))) target)

/-- Wrong current/next vectors can agree with the honest initial shift sum
at at most 2*width-1 distinct batching challenges. The vector is fixed before
alpha; the subsequent shift messages may still be adaptive. -/
theorem shift_initial_claim_bad_count (target : List K) (columns : List (Nat→K))
    (sent : List K) (lane : Nat) (shape : sent.length=2*columns.length)
    (wrong : sent.getD lane 0≠(shiftHonestClaims target columns).getD lane 0)
    (sample : List K) (distinct : sample.Nodup) :
    ArenaCore.Security.count sample (fun alpha=>lanePowerBatch alpha sent=
      whirCubeSum target.length (fun bits=>shiftReductionWeight target bits alpha columns.length*
        lanePowerBatch alpha (columns.map (fun col=>packedGridEval target.length col bits))))+1≤2*columns.length := by
  simp only [shift_reduction_batched_initial]
  exact lane_claim_batch_bad_count sent (shiftHonestClaims target columns) (2*columns.length) lane shape
    (by simp only [shiftHonestClaims,List.length_append,List.length_map];omega) wrong sample distinct

end NearCompression
