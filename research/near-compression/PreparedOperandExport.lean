import ZkFormal.Air.Export
import NearCompression.PreparedOperandBridge

def main : IO Unit := IO.println ("[" ++ String.intercalate "," ((List.range 2).map (fun i => ZkFormal.Air.Expr.toJson (NearCompression.preparedAddCarryPython i))) ++ "]")
