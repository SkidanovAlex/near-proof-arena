import NearCompression.PackedByteLayout
import Lean
open Lean NearCompression
private def slots (regions : List (Nat × Nat)) (width : Nat) : Json :=
  toJson ((List.range width).map (fun c => match packedColumnSlot regions c with
    | .scalar j => [0,j,0]
    | .byte j bit => [1,j,bit]))
def main : IO Unit :=
  IO.println (Json.arr #[slots packedExecRegions 605,slots packedCodeRegions 198]).compress
