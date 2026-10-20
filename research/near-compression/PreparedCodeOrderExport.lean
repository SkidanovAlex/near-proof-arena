import ZkFormal.Air.Export
import NearCompression.PreparedCodeOrder
open NearCompression
def main : IO Unit := IO.println ("[" ++ String.intercalate ","
  (((List.range 198).map preparedGasBoolean ++
    (List.range 32).map preparedCodeFirstPC ++
    [preparedCodeNoResume, preparedCodePCStepLow, preparedCodePCStepHigh]).map
      ZkFormal.Air.Expr.toJson) ++ "]")
