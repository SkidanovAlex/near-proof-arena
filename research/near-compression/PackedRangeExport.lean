import NearCompression.PackedRangeBus
import ZkFormal.Air.Export
open NearCompression ZkFormal.Air
private def sends (regions : List (Nat × Nat)) : String :=
  jsonList ((packedMacroBases regions).flatMap (fun base=>
    [(packedRangeSend (packedColumnIndex regions base)).toJson,
     (packedRangeSend (packedColumnIndex regions (base+8))).toJson]))
def main : IO Unit := do
  let table := "{\"width\":24,\"maxLog\":22,\"constraints\":" ++
    jsonList (packedRangeTable.constraints.map Expr.toJson) ++
    ",\"interactions\":" ++ jsonList (packedRangeTable.interactions.map Interaction.toJson) ++ "}"
  IO.println (jsonList [table,sends packedExecRegions,sends packedCodeRegions])
