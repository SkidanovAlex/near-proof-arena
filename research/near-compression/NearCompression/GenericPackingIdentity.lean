import NearCompression.GenericRowMLE

namespace NearCompression
open Lean.Grind
variable {K : Type} [CommRing K]

/-- Low coordinates enumerate rows; high coordinates enumerate columns. -/
theorem generic_row_mle_split_axes (n p : Nat) (values point : Nat → K) :
    genericRowMLE (n+p) values point =
      genericRowMLE p
        (fun col => genericRowMLE n (fun row => values (row+2^n*col)) point)
        (fun i => point (n+i)) := by
  induction n generalizing values point with
  | zero => simp only [Nat.zero_add, Nat.pow_zero, Nat.one_mul, genericRowMLE]
  | succ n ih =>
    rw [Nat.succ_add, genericRowMLE, ih, ih]
    simp only [genericRowMLE]
    rw [generic_row_mle_add, generic_row_mle_scale, generic_row_mle_scale]
    congr 1
    · congr 1
      congr 1
      · funext col
        congr 1
        funext row
        congr 1
        simp only [Nat.pow_succ]
        grind
      · funext i; congr 1; omega
    · congr 1
      congr 1
      · funext col
        congr 1
        funext row
        congr 1
        simp only [Nat.pow_succ]
        grind
      · funext i; congr 1; omega

/-- A partial group uses original column numbers and pads missing columns
with zero. The row argument is first in the source table. -/
def genericPackedColumn (p width group col : Nat) (table : Nat → Nat → K)
    (row : Nat) : K :=
  if group*2^p+col < width then table row (group*2^p+col) else 0

def genericPackedValues (n p width group : Nat) (table : Nat → Nat → K)
    (index : Nat) : K :=
  genericPackedColumn p width group (index / 2^n) table (index % 2^n)

theorem generic_packed_values_index (n p width group row col : Nat)
    (table : Nat → Nat → K) (hr : row < 2^n) :
    genericPackedValues n p width group table (row+2^n*col) =
      genericPackedColumn p width group col table row := by
  have pos : 0 < 2^n := Nat.two_pow_pos n
  have hd : (row+2^n*col)/2^n=col := by
    rw [Nat.add_mul_div_left row col pos, Nat.div_eq_of_lt hr, Nat.zero_add]
  have hm : (row+2^n*col)%2^n=row := by
    simp [Nat.add_mod, Nat.mod_eq_of_lt hr]
  simp only [genericPackedValues,hd,hm]

/-- Complete packing identity, including the partially occupied final group.
The full point's first n coordinates are row coordinates; the next p are
column coordinates. The exact same zero-padded columns occur on both sides. -/
theorem generic_packed_mle_identity (n p width group : Nat)
    (table : Nat → Nat → K) (point : Nat → K) :
    genericRowMLE (n+p) (genericPackedValues n p width group table) point =
      genericRowMLE p
        (fun col => genericRowMLE n (genericPackedColumn p width group col table) point)
        (fun i => point (n+i)) := by
  rw [generic_row_mle_split_axes]
  apply generic_row_mle_congr
  intro col _
  apply generic_row_mle_congr
  intro row hr
  exact generic_packed_values_index n p width group row col table hr

theorem generic_padded_column_mle_zero (n p width group col : Nat)
    (table : Nat → Nat → K) (point : Nat → K)
    (missing : width ≤ group*2^p+col) :
    genericRowMLE n (genericPackedColumn p width group col table) point=0 := by
  have absent : ¬group*2^p+col < width := by omega
  have eq : genericPackedColumn p width group col table = (fun _ => 0) := by
    funext row
    simp only [genericPackedColumn,absent,ite_false]
  rw [eq]
  exact generic_row_mle_zero n point

end NearCompression
