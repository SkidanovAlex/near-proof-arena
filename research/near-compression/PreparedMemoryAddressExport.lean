import NearCompression.PreparedMemoryAddress
import ZkFormal.Air.Export
open NearCompression ZkFormal.Air
def main : IO Unit := IO.println (jsonList (preparedMemoryAddressConstraints.map Expr.toJson))
