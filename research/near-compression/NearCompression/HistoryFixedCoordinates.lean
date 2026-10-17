import NearCompression.FixedJointSourceTrace
import NearCompression.BoundedBusCoordinateTyping
namespace NearCompression
open Lean.Grind ZkFormal.Air ZkFormal.Algebra

/-- Fix all covered physical coordinates, including auxiliary coordinates,
separately for each earlier history. Oracles may change with that history,
but stay fixed across later local/GKR/PCS continuations. Eligible decoded
representatives then share one base trace for that earlier history. Empty
eligible fibers are handled by the underlying fixed-trace construction.
This is an ideal-oracle result, not extraction from hash commitments. -/
theorem history_fixed_joint_coordinate_trace {A R : Type}
    (layout : GKRJointLayout) (metadata : List GKRSourceLane)
    (valid : ∀ lane∈metadata,lane.WellFormed layout) (geometry : CanonicalLaneSelectors layout metadata)
    (domain : List Fp8) (distinct : domain.Nodup) (basePoints : ∀ x∈domain,Fp8.IsBase x)
    (D T : Nat) (separation : 2*(domain.length-T)+D≤domain.length)
    (rowLogs coordinateWidth : Nat → Nat) (indices offsets : Nat → Nat → Nat)
    (indexBound : ∀ t column,column<coordinateWidth t → indices t column<metadata.length)
    (sourceOracles : A → Nat → Nat → Fp8 → Fp)
    (sources : A → R → List (Fp8 → Fp8)) (polys : A → R → List (Poly Fp8))
    (decoded : A → R → Trace Fp8) (eligible : A → R → Prop)
    (sourceShape : ∀ a r,eligible a r → (sources a r).length=metadata.length)
    (representative : ∀ a r,eligible a r →
      JointBetaRepresentative domain (fun _=>1) (heterogeneousJointDimension layout) D T
        (metadata.map (heterogeneousJointBeta layout)) (sources a r) (polys a r))
    (fixedOracle : ∀ a r,eligible a r → ∀ t column,column<coordinateWidth t →
      (sources a r).getD (indices t column) (fun _ => 0)=(fun x => Fp8.ofBase (sourceOracles a t column x)))
    (logs : ∀ a r,eligible a r → (decoded a r).log=rowLogs)
    (provenance : ∀ a r,eligible a r → ∀ t row column,∀ hc : column<coordinateWidth t,
      (decoded a r).cell t row column=
        recoveredColumnValues layout.commonLog (metadata[indices t column]'(indexBound t column hc))
          (offsets t column) ((polys a r).getD (indices t column) Poly.zero) row) :
    ∃ fixed : A → Trace Fp,(∀ a,(fixed a).log=rowLogs) ∧
      ∀ a r,eligible a r → (decoded a r).log=(fixed a).log ∧
        ∀ t row column,column<coordinateWidth t →
          (decoded a r).cell t row column=Fp8.ofBase ((fixed a).cell t row column) := by
  classical
  have witnesses : ∀ a,∃ fixed : Trace Fp,fixed.log=rowLogs ∧
      ∀ r,eligible a r → (decoded a r).log=fixed.log ∧
        ∀ t row column,column<coordinateWidth t →
          (decoded a r).cell t row column=Fp8.ofBase (fixed.cell t row column) := by
    intro a
    exact fixed_joint_representative_source_trace layout metadata valid geometry domain distinct basePoints
      D T separation rowLogs coordinateWidth indices offsets indexBound (sourceOracles a)
      (sources a) (polys a) (decoded a) (eligible a) (sourceShape a) (representative a)
      (fixedOracle a) (logs a) (provenance a)
  exact ⟨fun a=>Classical.choose (witnesses a),
    fun a=>(Classical.choose_spec (witnesses a)).1,
    fun a=>(Classical.choose_spec (witnesses a)).2⟩

/-- Formula reads are fixed by covered coordinate cells and row geometry.
Extension-valued literals are allowed; only physical trace cells are lifted. -/
theorem fixed_coordinate_bus_formula (fixed : Trace Fp) (decoded : Trace Fp8)
    (width : Nat → Nat) (logs : decoded.log=fixed.log)
    (cells : ∀ t row column,column<width t →
      decoded.cell t row column=Fp8.ofBase (fixed.cell t row column))
    (t row : Nat) (e : BusProgramFormula Fp8) (bound : busFormulaColumnBound e≤width t) :
    busProgramFormulaValue (busRowProgramEnv decoded t row) e=
      busProgramFormulaValue (busRowProgramEnv (airExt8Trace fixed) t row) e := by
  have heights : decoded.height t=fixed.height t := by simp only [Trace.height,logs]
  induction e with
  | literal x => rfl
  | current c => exact cells t row c (by simp only [busFormulaColumnBound] at bound;omega)
  | next c =>
    change decoded.cell t ((row+1)%decoded.height t) c=
      Fp8.ofBase (fixed.cell t ((row+1)%fixed.height t) c)
    rw [heights]
    exact cells t _ c (by simp only [busFormulaColumnBound] at bound;omega)
  | first => rfl
  | last => simp only [busProgramFormulaValue,busRowProgramEnv,rowEnv,Trace.height,airExt8Trace,logs];rfl
  | transition => simp only [busProgramFormulaValue,busRowProgramEnv,rowEnv,Trace.height,airExt8Trace,logs];rfl
  | add a b ha hb | sub a b ha hb | mul a b ha hb =>
    have ba : busFormulaColumnBound a≤width t := Nat.le_trans (Nat.le_max_left _ _) bound
    have bb : busFormulaColumnBound b≤width t := Nat.le_trans (Nat.le_max_right _ _) bound
    simp only [busProgramFormulaValue,ha ba,hb bb]

/-- The full local residual vector agrees with the earlier fixed coordinate
trace, so its validity cannot vary across eligible later representatives. -/
theorem fixed_coordinate_combined_residuals (fixed : Trace Fp) (decoded : Trace Fp8)
    (width : Nat → Nat) (logs : decoded.log=fixed.log)
    (cells : ∀ t row column,column<width t →
      decoded.cell t row column=Fp8.ofBase (fixed.cell t row column))
    (t row : Nat) (pub : List Fp) (source : List Expr) (auxiliary : List (BusProgramFormula Fp8))
    (sourceBounds : ∀ e∈source,e.colBound≤width t)
    (auxBounds : ∀ e∈auxiliary,busFormulaColumnBound e≤width t) :
    airCombinedRowResiduals decoded t (pub.map Fp8.ofBase) source auxiliary row=
      airCombinedRowResiduals (airExt8Trace fixed) t (pub.map Fp8.ofBase) source auxiliary row := by
  have sources : source.map (fun e=>e.eval decoded t row (pub.map Fp8.ofBase))=
      source.map (fun e=>e.eval (airExt8Trace fixed) t row (pub.map Fp8.ofBase)) := by
    apply List.map_congr_left
    intro e he
    rw [fixed_source_decoded_expression fixed width decoded logs cells t row pub e (sourceBounds e he),
      fixed_source_decoded_expression fixed width (airExt8Trace fixed) rfl
        (fun _ _ _ _=>rfl) t row pub e (sourceBounds e he)]
  have aux : auxiliary.map (busProgramFormulaValue (busRowProgramEnv decoded t row))=
      auxiliary.map (busProgramFormulaValue (busRowProgramEnv (airExt8Trace fixed) t row)) := by
    apply List.map_congr_left
    intro e he
    exact fixed_coordinate_bus_formula fixed decoded width logs cells t row e (auxBounds e he)
  unfold airCombinedRowResiduals
  rw [sources,aux]

end NearCompression
