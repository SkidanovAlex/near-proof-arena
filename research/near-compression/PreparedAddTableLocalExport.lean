import ZkFormal.Air.Export
import NearCompression.PreparedAddTableLocal
open NearCompression
def main : IO Unit := IO.println ("[" ++ String.intercalate "," (([preparedFailureInvariantPython, preparedDoneStepPython, preparedFailureStepPython, preparedAddDepthSource] ++ (List.range 4).map preparedGasStepPython).map ZkFormal.Air.Expr.toJson) ++ "]")
