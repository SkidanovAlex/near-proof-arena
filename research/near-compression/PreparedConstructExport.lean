import ZkFormal.Air.Export
import NearCompression.PreparedWasmConstruct

def main : IO Unit := IO.println ("[" ++ String.intercalate "," ([
  NearCompression.preparedFirstEqPython 0 1,
  NearCompression.preparedFirstEqPython 16 1,
  NearCompression.preparedFirstEqPython 25 0,
  NearCompression.preparedLastDonePython].map ZkFormal.Air.Expr.toJson) ++ "]")
