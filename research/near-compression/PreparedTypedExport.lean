import NearCompression.PreparedTypedValue
import ZkFormal.Air.Export
open NearCompression ZkFormal.Air
def main : IO Unit := do
  IO.println ("{\"eqz\":" ++ (Air.mk [preparedTypedEqzTable] 0 0).exportJson ++
    ",\"add64\":" ++ (Air.mk [instructionAdd64Table] 0 0).exportJson ++ "}")
