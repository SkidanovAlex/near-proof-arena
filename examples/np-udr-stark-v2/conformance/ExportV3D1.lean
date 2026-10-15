import ZkFormal.NearV3.D1.NearAirD1Defs
import ZkFormal.V2.Export
import ZkFormal.Stark.Protocol

/-!
`np-lean-export-v3d1` — prints `nearAirV3D1.exportJson` (format `np-air-v2`), the D1 AIR
(lane v3-d1-tables) the Rust prover's `--d1` paths are fed.

`np-lean-export-v3d1 --layout <g>` — per table `t width auxCount degree quotCount sendG recvG
maxLog` at `auxGroup = g`, as `np-lean-export-v3 --layout`.
-/

open ZkFormal.Air ZkFormal.Stark

def main (args : List String) : IO UInt32 := do
  let AP := ZkFormal.NearV3.D1.nearAirV3D1
  match args with
  | [] => IO.print AP.exportJson; return 0
  | ["--layout", gS] =>
    let some g := gS.toNat? | IO.eprintln "bad g"; return 2
    for (T, t) in AP.tables.zipIdx do
      IO.println s!"{t} {T.width} {T.auxCount g} {T.degree g} {T.quotCount g} {numGroups (T.numSide true) g} {numGroups (T.numSide false) g} {T.maxLog}"
    return 0
  | _ => IO.eprintln "usage: np-lean-export-v3d1 [--layout g]"; return 2
