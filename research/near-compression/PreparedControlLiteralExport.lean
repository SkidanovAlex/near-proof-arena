import NearCompression.PreparedControlLiteral
import ZkFormal.V2.Export
open NearCompression ZkFormal.V2
def main : IO Unit := IO.println (preparedControlLiteralAir 11).exportJson
