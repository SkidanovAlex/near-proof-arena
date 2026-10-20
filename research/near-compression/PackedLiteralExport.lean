import NearCompression.PackedLiteralFamily
import ZkFormal.V2.Export
open NearCompression ZkFormal.Air ZkFormal.V2
-- Export explicit constraints, preserving exactly the research spec's raw AIR.
private def rawTable (t : Table) : String :=
  s!"\{\"width\":{t.width},\"maxLog\":{t.maxLog},\"constraints\":" ++
    jsonList (t.constraints.map Expr.toJson) ++ ",\"interactions\":" ++
    jsonList (t.interactions.map Interaction.toJson) ++ "}"
private def rawAir (a : AirP) : String :=
  s!"\{\"format\":\"np-air-v2\",\"numBuses\":{a.numBuses},\"numPub\":{a.numPub},\"maxPub\":{a.maxPub},\"tables\":" ++
    jsonList (a.tables.map rawTable) ++ ",\"pubSegs\":" ++ jsonList (a.pubSegs.map PubSeg.toJson) ++ "}"
def main (args : List String) : IO Unit := do
  match args with
  | [] => IO.println (jsonList [rawAir packedOriginalAir,rawAir packedCandidateAir])
  | [n] => match n.toNat? with
    | some count => IO.println (jsonList [rawAir (preparedLiteralAir count),rawAir (packedCandidateAirFor count)])
    | none => throw (IO.userError "invalid code length")
  | _ => throw (IO.userError "expected optional code length")
