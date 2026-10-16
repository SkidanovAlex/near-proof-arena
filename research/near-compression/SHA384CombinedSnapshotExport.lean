import NearCompression.SHA384BatchedCore
open NearCompression ZkFormal.Air ZkFormal.V2

def main : IO Unit := do
  let air : AirP := {
    tables := [sha512CombinedTable]
    numBuses := 0
    numPub := 0
    maxPub := 0
    pubSegs := [] }
  IO.println air.exportJson
