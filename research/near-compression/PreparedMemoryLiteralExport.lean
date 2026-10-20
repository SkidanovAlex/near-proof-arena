import NearCompression.PreparedMemoryLiteral
import ZkFormal.Air.Export
open NearCompression ZkFormal.Air
def main : IO Unit := IO.println preparedMemoryLiteralTable.toJson
