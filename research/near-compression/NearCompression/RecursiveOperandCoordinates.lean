import NearCompression.DiagnosticExt4Polynomial
namespace NearCompression
open Lean.Grind ZkFormal.Algebra

/-- Flat coordinate basis used by the recursive GKR-to-PCS lane map. -/
def recursiveOperandBasis (i : Nat) : Fp4 :=
  diagnosticExt4ToTower ⟨if i=0 then 1 else 0, if i=1 then 1 else 0,
    if i=2 then 1 else 0, if i=3 then 1 else 0⟩

/-- The four base-field lanes reconstruct the operand in its actual tower order. -/
theorem recursive_operand_reconstruct (a : DiagnosticExt4) :
    ((List.range 4).map (fun i=>diagnosticExt4Embed (diagnosticExt4Get a i)*
      recursiveOperandBasis i)).sum=diagnosticExt4ToTower a := by
  apply QuadExt.ext <;> apply QuadExt.ext <;>
    simp [List.range_succ,diagnosticExt4Embed,diagnosticExt4Base,
      diagnosticExt4ToTower,diagnosticExt4Get,recursiveOperandBasis] <;> grind

private theorem scale_sum (xs : List Fp4) (w : Fp4) :
    (xs.map (fun x=>w*x)).sum=w*xs.sum := by
  induction xs with
  | nil=>simp only [List.map_nil,List.sum_nil];grind
  | cons x xs ih=>simp only [List.map_cons,List.sum_cons,ih];grind

/-- Each GKR terminal weight can be moved into the four PCS lane weights. -/
theorem recursive_operand_weighted (a : DiagnosticExt4) (w : Fp4) :
    ((List.range 4).map (fun i=>(w*recursiveOperandBasis i)*
      diagnosticExt4Embed (diagnosticExt4Get a i))).sum=w*diagnosticExt4ToTower a := by
  rw [←recursive_operand_reconstruct a,←scale_sum]
  simp only [List.map_map]
  have h : (fun i=>(w*recursiveOperandBasis i)*diagnosticExt4Embed (diagnosticExt4Get a i)) =
      (fun i=>w*(diagnosticExt4Embed (diagnosticExt4Get a i)*recursiveOperandBasis i)) := by
    funext i; grind
  rw [h]
  rfl

/-- Summing packed coordinate contributions preserves an arbitrary finite
weighted operand functional. Row/group index decomposition and executable
packing refinement are separate obligations. -/
theorem recursive_operand_functional (indices : List Nat)
    (values : Nat→DiagnosticExt4) (weights : Nat→Fp4) :
    (indices.map (fun j=>((List.range 4).map (fun i=>
      (weights j*recursiveOperandBasis i)*diagnosticExt4Embed
        (diagnosticExt4Get (values j) i))).sum)).sum=
    (indices.map (fun j=>weights j*diagnosticExt4ToTower (values j))).sum := by
  simp only [recursive_operand_weighted]
end NearCompression
