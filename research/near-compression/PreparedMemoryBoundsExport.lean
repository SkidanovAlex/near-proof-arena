import NearCompression.PreparedMemoryBounds
import ZkFormal.Air.Export
open NearCompression ZkFormal.Air
def main : IO Unit := IO.println (jsonList (preparedMemoryBoundsEquations.map Expr.toJson))
