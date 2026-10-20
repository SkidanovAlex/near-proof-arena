import ZkFormal.Air.Export
import NearCompression.PreparedGasPublicBridge

def main : IO Unit := IO.println ("[" ++ String.intercalate "," ((NearCompression.preparedGasSourceConstraints [] []).map ZkFormal.Air.Expr.toJson) ++ "]")
