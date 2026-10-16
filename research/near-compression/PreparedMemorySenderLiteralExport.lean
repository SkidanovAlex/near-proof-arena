import NearCompression.PreparedMemorySenderLiteral
import ZkFormal.Air.Export
open NearCompression ZkFormal.Air
def main : IO Unit := IO.println preparedMemorySenderLiteralTable.toJson
