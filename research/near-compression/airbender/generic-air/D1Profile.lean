import ZkFormal.NearV3.D1.NearAirD1Defs
import ZkFormal.Stark.ProtocolDefs
import Lean

open Lean ZkFormal.Air ZkFormal.NearV3.D1

/-- Static AIR dimensions only. maxLog is a cap, not a measured trace height. -/
def main : IO Unit := do
  let tables := nearAirV3D1.tables.zipIdx.map fun ((t, i) : Table × Nat) =>
    Json.mkObj [
      ("index", toJson i), ("width", toJson t.width), ("maxLog", toJson t.maxLog),
      ("constraints", toJson t.allConstraints.length),
      ("interactions", toJson t.interactions.length),
      ("source_degree", toJson ((t.allConstraints.map Expr.degree).foldr max 0)),
      ("group1_aux_columns", toJson (t.auxCount 1)),
      ("group1_aux_degree", toJson (t.auxDegree 1)),
      ("group1_combined_degree", toJson (t.degree 1)),
      ("group2_aux_columns", toJson (t.auxCount 2))]
  IO.println <| (Json.mkObj [
    ("table_count", toJson nearAirV3D1.tables.length),
    ("public_segments", toJson nearAirV3D1.pubSegs.length),
    ("numPub", toJson nearAirV3D1.numPub),
    ("maxPub", toJson nearAirV3D1.maxPub),
    ("tables", toJson tables)]).compress
