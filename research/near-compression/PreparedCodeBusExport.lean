import ZkFormal.V2.Export
import NearCompression.PreparedCodeBus
open NearCompression ZkFormal.Air ZkFormal.V2
def main : IO Unit := do
  IO.println ("{\"skeleton\":" ++ (preparedCodeBusAir [] [] [] 193).exportJson ++
    ",\"inactive\":" ++ jsonList (((List.range 25).map fun i => preparedCodeInactive (172+i)).map Expr.toJson) ++ "}")
