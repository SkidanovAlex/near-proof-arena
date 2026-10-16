import NearCompression.PreparedLocalsLiteral
import ZkFormal.V2.Export
open NearCompression ZkFormal.V2
def main : IO Unit := do
  IO.println ("[" ++ String.intercalate "," ((List.range 5).map
    (fun count=>(preparedLocalsLiteralAir 19 count).exportJson)) ++ "]")
