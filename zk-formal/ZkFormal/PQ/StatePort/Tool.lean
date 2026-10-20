import ZkFormal.Air.Export
import ZkFormal.PQ.StatePort.Bridge
import ZkFormal.NearV3.Assembly.NearAir
import ZkFormal.NearV3.D1.NearAirD1Defs

/-!
# `pq-state-port-eval` — the Lean side of the P3 difftest (vk ⇔ Lean AIR)

Lane `pq-state-port`.  Reads the points file written by
`nearproof-pq-state-port difftest` and prints, per point, the value of every constraint and of
every interaction (bus, signed count, message) computed by **evaluating the Lean `AirP` value
directly** at the given cur/next/public/selector values.  `difftest_p3.py` compares that output
with the Rust keygen's symbolic-DAG evaluation at the same points.

The comparison is over the *translated* AIR (every interaction shifted by `BUS_OFFSET`, exactly as
the driver does), so a mismatch would catch a divergence in either the expression interpreter or
the interaction encoding.  The TAPE harness row is excluded here: it is a Rust-side synthetic
table with no Lean `AirP` counterpart by design (it is the public-message carrier, and its
correctness is `TapeNet`, not an AIR).

Usage:
  `pq-state-port-eval <points.txt> <nearAirV3|nearAirV3D1>`
-/

open ZkFormal ZkFormal.Air ZkFormal.Algebra

namespace ZkFormal.PQ.StatePort.Tool


/-- The bus offset the Rust driver applies to every classical interaction, reserved for the
later direct-Wasm join (keep in sync with `BUS_OFFSET` in the driver). -/
def busOffset : Nat := 128

/-- The translated AIR: every classical interaction moved to `off + bus`. -/
def shiftAir (AP : Air) (off : Nat) : Air :=
  { AP with
    tables := AP.tables.map fun T =>
      { T with interactions := T.interactions.map fun i => { i with bus := off + i.bus } } }

def parseNats (s : String) : List Nat :=
  (s.splitOn " ").filterMap fun x => if x.isEmpty then none else x.toNat?

/-- One line `ti sel(3) | cur | next | pubs`, each side space-separated nats. -/
def parseLine (l : String) : Option (Nat × List Nat × List Nat × List Nat × List Nat) := do
  let (head, rest) ← match l.splitOn " | " with
    | [h, c, n, p] => some (h, (c, n, p))
    | _ => none
  let (c, n, p) := rest
  let (ti, sel) ← match head.splitOn " " with
    | ti :: sel => some (ti.toNat?, sel)
    | _ => none
  let ti ← ti
  some (ti, parseNats (String.intercalate " " sel), parseNats c, parseNats n, parseNats p)

/-- Evaluate one table's constraints and interactions at a point. -/
def evalPoint (A : Air) (ti : Nat) (sel cur nxt pubs : List Nat) : String :=
  let T := A.tables.getD ti ⟨0, [], [], 0⟩
  let get (l : List Nat) (i : Nat) : Fp := ((l.getD i 0 : Nat) : Fp)
  let env : Env Fp :=
    { ofNat := fun n => ((n : Nat) : Fp)
      add := (· + ·), mul := (· * ·), neg := (- ·)
      col := fun c nx => get (if nx then nxt else cur) c
      pub := fun i => get pubs i
      isFirst := get sel 0, isLast := get sel 1, isTransition := get sel 2 }
  let cons := T.allConstraints.map fun e => (e.evalWith env).toNat
  let ints := T.interactions.map fun i =>
    let cnt := i.mult.zipIdx.foldr (fun (b, k) acc => (b.evalWith env) * ((2 ^ k : Nat) : Fp) + acc) 0
    let msg := i.msg.map fun e => (e.evalWith env).toNat
    (i.bus, cnt.toNat, msg)
  let cj := String.intercalate "," (cons.map toString)
  let ij := String.intercalate ","
    (ints.map fun (b, c, m) => s!"[{b},{c},[{String.intercalate "," (m.map toString)}]]")
  s!"\{\"t\":{ti},\"constraints\":[{cj}],\"inters\":[{ij}]}"

end ZkFormal.PQ.StatePort.Tool

open ZkFormal.PQ.StatePort.Tool

/-- `pq-state-port-eval <points.txt> <nearAirV3|nearAirV3D1>`. -/
def main (args : List String) : IO UInt32 := do
  let (pts, which) ← match args with
    | [p, w] => pure (p, w)
    | _ => do
      IO.eprintln "usage: pq-state-port-eval <points.txt> <nearAirV3|nearAirV3D1>"
      return 1
  let AP ← match which with
    | "nearAirV3" => pure ZkFormal.NearV3.Assembly.nearAirV3
    | "nearAirV3D1" => pure ZkFormal.NearV3.D1.nearAirV3D1
    | w => do
      IO.eprintln s!"unknown AIR {w}"
      return 1
  let A := shiftAir AP.toAir busOffset
  let text ← IO.FS.readFile pts
  for l in text.splitOn "\n" do
    if l.isEmpty then continue
    match parseLine l with
    | some (ti, sel, cur, nxt, pubs) => IO.println (evalPoint A ti sel cur nxt pubs)
    | none => IO.eprintln s!"bad point line: {l}"
  return 0
