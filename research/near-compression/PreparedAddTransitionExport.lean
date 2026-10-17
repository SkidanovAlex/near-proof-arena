import ZkFormal.Air.Export
import NearCompression.PreparedAddTransition

def main : IO Unit := IO.println ("[" ++ String.intercalate "," (NearCompression.preparedAddTransitionConstraints.map ZkFormal.Air.Expr.toJson) ++ "]")
