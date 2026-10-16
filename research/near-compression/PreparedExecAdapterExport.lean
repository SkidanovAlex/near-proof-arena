import NearCompression.PreparedExecTerminal
import NearCompression.PreparedExecClosure
import NearCompression.PreparedExecGas
import NearCompression.PreparedExecWasm
import NearCompression.PreparedExecPC
import ZkFormal.Air.Export
open NearCompression ZkFormal.Air
def main : IO Unit := do
  let expressions := [preparedSPResidualPython, preparedAddDepthResidual,
    preparedSPStepPython, preparedFailureInvariantPython,
    preparedDoneStepPython, preparedFailureStepPython, preparedEndDepthPython, preparedExecStackDepth true, preparedExecStackDepth false] ++
    (List.range 2).map preparedAddCarryPython ++
    (List.range 4).map preparedGasSubtract ++
    (List.range 4).map preparedGasStepPython ++
    (List.range 8).flatMap (fun slot => (List.range 2).map (preparedStackStepPython slot))
  IO.println (jsonList (((expressions.map preparedExecLower) ++
    [preparedExecPCStepLow,preparedExecPCStepHigh] ++
    (List.range 4).map preparedExecGasSubtract ++ (List.range 4).map preparedExecGasUpdate ++ [preparedExecSPChoice]).map Expr.toJson))
