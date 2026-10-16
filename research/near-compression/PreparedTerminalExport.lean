import ZkFormal.Air.Export
import NearCompression.PreparedTerminalCases

def main : IO Unit := IO.println (ZkFormal.Air.Expr.toJson NearCompression.preparedEndDepthPython)
