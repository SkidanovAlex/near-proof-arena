import NearCompression.DualBorrowWeightMLE
import NearCompression.AirTraceCoordinateSlice

namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

private theorem weighted_cube_congr (point : List K) (f g : List Bool→K)
    (same : ∀ bits,bits.length=point.length → f bits=g bits) :
    shiftWeightedCubeSum point f=shiftWeightedCubeSum point g := by
  induction point generalizing f g with
  | nil => exact same [] rfl
  | cons x xs ih =>
    simp only [shiftWeightedCubeSum]
    rw [ih _ _ (fun bits hb=>same (false::bits) (by simp [hb])),
      ih _ _ (fun bits hb=>same (true::bits) (by simp [hb]))]

/-- The ordinary weighted Boolean sum is the row MLE, with exactly the
little-endian index convention of the current/next reduction. -/
theorem shift_weighted_cube_row_mle (point : List K) (values : Nat→K) :
    shiftWeightedCubeSum point (fun bits=>values (shiftListBitIndex bits))=
      packedGridEval point.length values point := by
  induction point generalizing values with
  | nil => rfl
  | cons x xs ih =>
    simp only [shiftWeightedCubeSum,shiftListBitIndex,Bool.false_eq_true,ite_false,ite_true,Nat.zero_add,
      List.length_cons,packed_grid_eval_cons]
    have odd : (fun bits=>values (1+2*shiftListBitIndex bits))=
        (fun bits=>values (2*shiftListBitIndex bits+1)) := by funext bits;congr 1;omega
    rw [odd,ih (fun i=>values (2*i)),ih (fun i=>values (2*i+1))]

/-- Ordinary shift kernel, without upper-zeta weights: this is the actual
borrow DP in pq384_shift.py, evaluated at arbitrary field coordinates. -/
theorem shift_kernel_row_mle (coords : List (K×K)) :
    shiftKernelDP coords 0 1=
      packedGridEval coords.length
        (cyclicRowWeight coords.length (fun i=>(coords.map Prod.fst).getD i 0)) (coords.map Prod.snd) := by
  rw [shift_kernel_dp_weighted]
  have cube:=shift_weighted_cube_row_mle (coords.map Prod.snd)
    (cyclicRowWeight coords.length (fun i=>(coords.map Prod.fst).getD i 0))
  simp only [List.length_map] at cube
  rw [←cube]
  apply weighted_cube_congr
  intro bits shape
  simpa only [List.length_map] using (cyclic_row_weight_bits (coords.map Prod.fst) bits (by simpa using shape)).symm

theorem shift_kernel_zipped_row_mle (target point : List K) (length : point.length=target.length) :
    shiftKernelDP (target.zip point) 0 1=
      packedGridEval target.length (cyclicRowWeight target.length (fun i=>target.getD i 0)) point := by
  rw [shift_kernel_row_mle]
  have left : (target.zip point).map Prod.fst=target := List.map_fst_zip (by omega)
  have right : (target.zip point).map Prod.snd=point := List.map_snd_zip (by omega)
  simp only [left,right,List.length_zip,length,Nat.min_self]

/-- Executable current-plus-shift weight. alpha^width is the offset for next
claims in the shared column power batch. -/
def shiftReductionWeight (target point : List K) (alpha : K) (width : Nat) : K :=
  whirKernel target point+alpha^width*shiftKernelDP (target.zip point) 0 1

noncomputable def shiftReductionCoordinatePolynomial (target history suffix : List K)
    (alpha : K) (width : Nat) : Poly K :=
  airKernelCoordinatePolynomial target history suffix+
    Poly.smul (alpha^width) (airCoordinatePolynomial
      (cyclicRowWeight target.length (fun i=>target.getD i 0)) history suffix)

theorem shift_reduction_coordinate_eval (target history suffix : List K) (alpha x : K) (width : Nat)
    (length : history.length+1+suffix.length=target.length) :
    (shiftReductionCoordinatePolynomial target history suffix alpha width).eval x=
      shiftReductionWeight target (history++x::suffix) alpha width := by
  rw [shiftReductionCoordinatePolynomial,Poly.eval_add,Poly.eval_smul,air_kernel_coordinate_eval,
    air_coordinate_polynomial_eval]
  unfold shiftReductionWeight
  rw [shift_kernel_zipped_row_mle target _ (by simp only [List.length_append,List.length_cons];omega),length]

theorem shift_reduction_coordinate_degree (target history suffix : List K) (alpha : K) (width : Nat) :
    (shiftReductionCoordinatePolynomial target history suffix alpha width).DegLt 2 :=
  Poly.degLt_add (air_kernel_coordinate_degree _ _ _)
    (Poly.degLt_smul _ (air_coordinate_polynomial_degree _ _ _))

private theorem affine_batch_degree (alpha : K) (polys : List (Poly K))
    (affine : ∀ p∈polys,p.DegLt 2) : (lanePolynomialBatch alpha polys).DegLt 2 := by
  induction polys with
  | nil => exact (Poly.degLt_length Poly.zero).mono (by change 0≤2;decide)
  | cons p rest ih =>
    exact Poly.degLt_add (affine p (List.mem_cons_self ..))
      (Poly.degLt_smul _ (ih (fun q hq=>affine q (List.mem_cons_of_mem _ hq))))

noncomputable def shiftReductionSlicePolynomial (tr : ZkFormal.Air.Trace K) (t width : Nat)
    (target history suffix : List K) (alpha : K) : Poly K :=
  shiftReductionCoordinatePolynomial target history suffix alpha width *
    lanePolynomialBatch alpha ((List.range width).map (fun c=>
      airCoordinatePolynomial (fun r=>tr.cell t r c) history suffix))

/-- The full shift sumcheck integrand is quadratic in every coordinate:
its actual kernel and batched source-column MLE are both affine. -/
theorem shift_reduction_slice_degree (tr : ZkFormal.Air.Trace K) (t width : Nat)
    (target history suffix : List K) (alpha : K) :
    (shiftReductionSlicePolynomial tr t width target history suffix alpha).DegLt 3 := by
  have columns : (lanePolynomialBatch alpha ((List.range width).map (fun c=>
      airCoordinatePolynomial (fun r=>tr.cell t r c) history suffix))).DegLt 2 := by
    apply affine_batch_degree
    intro p hp
    obtain ⟨c,_,rfl⟩:=List.mem_map.mp hp
    exact air_coordinate_polynomial_degree _ _ _
  exact Poly.degLt_mul (shift_reduction_coordinate_degree target history suffix alpha width) columns

theorem shift_reduction_slice_eval (tr : ZkFormal.Air.Trace K) (t width : Nat)
    (target history suffix : List K) (alpha x : K)
    (targetLength : target.length=tr.log t)
    (length : history.length+1+suffix.length=tr.log t) :
    (shiftReductionSlicePolynomial tr t width target history suffix alpha).eval x=
      shiftReductionWeight target (history++x::suffix) alpha width *
        lanePowerBatch alpha ((List.range width).map (fun c=>
          packedGridEval (tr.log t) (fun r=>tr.cell t r c) (history++x::suffix))) := by
  rw [shiftReductionSlicePolynomial,Poly.eval_mul,
    shift_reduction_coordinate_eval _ _ _ _ _ _ (length.trans targetLength.symm),lane_polynomial_batch_eval]
  simp only [List.map_map,Function.comp_def,air_coordinate_polynomial_eval,length]

end NearCompression
