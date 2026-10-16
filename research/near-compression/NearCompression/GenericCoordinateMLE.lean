import NearCompression.GenericRowMLE

/-! Linear coordinate reconstruction commutes with row interpolation, including
cyclically shifted tables. Coordinate values and basis elements live in the
same ring; a concrete base-field embedding and wire codec are separate bridges. -/
namespace NearCompression
open Lean.Grind

section Ring
variable {K : Type} [CommRing K]

/-- Finite linear reconstruction; basis order fixes coordinate order. -/
def genericCoordinateReconstruct : List K → (Nat → K) → K
  | [],_ => 0
  | b::bs,coordinates => b*coordinates 0 + genericCoordinateReconstruct bs (fun c => coordinates (c+1))

/-- Reconstruct first and interpolate, or interpolate each coordinate and then
reconstruct: both execute the same linear map over any commutative ring. -/
theorem generic_coordinate_mle (basis : List K) (n : Nat)
    (coordinates : Nat → Nat → K) (point : Nat → K) :
    genericRowMLE n (fun row => genericCoordinateReconstruct basis (coordinates row)) point=
      genericCoordinateReconstruct basis (fun c => genericRowMLE n (fun row => coordinates row c) point) := by
  induction basis generalizing coordinates with
  | nil => exact generic_row_mle_zero n point
  | cons b bs ih =>
    simp only [genericCoordinateReconstruct,generic_row_mle_add,generic_row_mle_scale,ih]

/-- The same reconstruction theorem applies to actual cyclic-next MLEs. -/
theorem generic_coordinate_next_mle (basis : List K) (n : Nat)
    (coordinates : Nat → Nat → K) (point : Nat → K) :
    genericRowNextMLE n (fun row => genericCoordinateReconstruct basis (coordinates row)) point=
      genericCoordinateReconstruct basis (fun c => genericRowNextMLE n (fun row => coordinates row c) point) := by
  exact generic_coordinate_mle basis n (fun row c => coordinates ((row+1)%(2^n)) c) point

/-- Four basis elements in the order used by a power-basis representation. No
linear independence or extension-field irreducibility is assumed or concluded. -/
def genericCoordinateReconstruct4 (v : K) (coordinates : Nat → K) : K :=
  genericCoordinateReconstruct [1,v,v*v,v*v*v] coordinates

theorem generic_coordinate_reconstruct_four (v : K) (coordinates : Nat → K) :
    genericCoordinateReconstruct4 v coordinates=
      coordinates 0+v*coordinates 1+(v*v)*coordinates 2+(v*v*v)*coordinates 3 := by
  simp only [genericCoordinateReconstruct4,genericCoordinateReconstruct,Nat.reduceAdd]
  grind

theorem generic_coordinate_four_mle (v : K) (n : Nat)
    (coordinates : Nat → Nat → K) (point : Nat → K) :
    genericRowMLE n (fun row => genericCoordinateReconstruct4 v (coordinates row)) point=
      genericCoordinateReconstruct4 v (fun c => genericRowMLE n (fun row => coordinates row c) point) :=
  generic_coordinate_mle [1,v,v*v,v*v*v] n coordinates point

theorem generic_coordinate_four_next_mle (v : K) (n : Nat)
    (coordinates : Nat → Nat → K) (point : Nat → K) :
    genericRowNextMLE n (fun row => genericCoordinateReconstruct4 v (coordinates row)) point=
      genericCoordinateReconstruct4 v (fun c => genericRowNextMLE n (fun row => coordinates row c) point) :=
  generic_coordinate_next_mle [1,v,v*v,v*v*v] n coordinates point

end Ring
end NearCompression
