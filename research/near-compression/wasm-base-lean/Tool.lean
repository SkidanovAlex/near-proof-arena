import WasmBase.Check
/-!
`wasmbase-tool` — exporter and verifier-side preparation for the direct-Wasm base layer.

* `wasmbase-tool air <ncode>`: the AIR `wasmBaseAir ncode` as JSON (the Rust crate interprets it).
* `wasmbase-tool prep <file.wasm> <exportName> <g0>`: `prepare` (PV86), `check` of the exported function,
  and a reference execution with the spec's own `step` from the post-`enter` state with
  `gas.g = g0` (after the prologue charge), as JSON.
* `wasmbase-tool eval <ncode> <points>`: evaluate every constraint, interaction count and message
  of `wasmBaseAir ncode` at the given points (difftest; selectors are free field values).
-/
open NearSpecV3.Wasm WasmBase ZkFormal.Algebra

def jList (xs : List String) : String := "[" ++ ",".intercalate xs ++ "]"
def jStr (s : String) : String := "\"" ++ s ++ "\""

def WasmBase.Expr.toJson : WasmBase.Expr → String
  | .c n => s!"[\"c\",{n}]"
  | .col i => s!"[\"v\",{i}]"
  | .nxt i => s!"[\"n\",{i}]"
  | .pub i => s!"[\"p\",{i}]"
  | .first => "[\"first\"]"
  | .last => "[\"last\"]"
  | .trans => "[\"trans\"]"
  | .add a b => s!"[\"+\",{a.toJson},{b.toJson}]"
  | .sub a b => s!"[\"-\",{a.toJson},{b.toJson}]"
  | .mul a b => s!"[\"*\",{a.toJson},{b.toJson}]"

def interJson (i : Inter) : String :=
  s!"\{\"bus\":{i.bus},\"send\":{i.send},\"count\":{Expr.toJson i.count},\"msg\":{jList (i.msg.map Expr.toJson)}}"

/-- Number of leading columns committed as a separate cached trace (CODE: the records; DATA: the
data image). -/
def cachedCols (T : Table) : Nat :=
  if T.name = "CODE" then Chips.Code.cachedWidth else if T.name = "DATA" then Chips.Data.cachedWidth else 0

/-- End of the data image: one past the last non-zero byte of the initial memory (0 if none). -/
def dataEnd (s : St) : Nat := Id.run do
  let mut e := 0
  for i in [0:s.pages.size] do
    let p := s.pages[i]!
    for j in [0:p.size] do
      if p.get! j != 0 then e := i * pageSize + j + 1
  return e

def tableJson (T : Table) : String :=
  s!"\{\"name\":{jStr T.name},\"cached\":{cachedCols T},\"cols\":{jList (T.cols.map jStr)},\"degree\":{(T.constraints ++ T.inters.flatMap (fun i => i.count :: i.msg)).foldl (fun m e => max m e.degree) 0},\"constraints\":{jList (T.constraints.map Expr.toJson)},\"inters\":{jList (T.inters.map interJson)}}"

def airJson (A : Air) : String :=
  s!"\{\"numPub\":{A.numPub},\"tables\":{jList (A.tables.map tableJson)}}"

/-- Generic evaluation with free selector values (difftest only). -/
def WasmBase.Expr.evalG (cur nxt pub : Nat → F) (sf sl st : F) : WasmBase.Expr → F
  | .c n => (n : F)
  | .col i => cur i
  | .nxt i => nxt i
  | .pub i => pub i
  | .first => sf
  | .last => sl
  | .trans => st
  | .add a b => a.evalG cur nxt pub sf sl st + b.evalG cur nxt pub sf sl st
  | .sub a b => a.evalG cur nxt pub sf sl st - b.evalG cur nxt pub sf sl st
  | .mul a b => a.evalG cur nxt pub sf sl st * b.evalG cur nxt pub sf sl st

def natList (xs : List Nat) : String := jList (xs.map toString)

def runSteps (cfg : NearCfg) (p : Prepared) : Nat → St → Nat → (Nat × Res)
  | 0, _, n => (n, .unmodeled "tool fuel")
  | k + 1, s, n => match step cfg p s with
    | .cont s' => runSteps cfg p k s' (n + 1)
    | r => (n + 1, r)

def valLimbs : Val → (Nat × List Nat)
  | .i32 v => (0, limbs4 v.toNat)
  | .i64 v => (1, limbs4 v.toNat)
  | .ref _ => (2, [0, 0, 0, 0])

def prep (path exportName : String) (g0 : Nat) : IO Unit := do
  let code ← IO.FS.readBinFile path
  let cfg := pv86
  match prepare cfg code with
  | .ok p =>
    let nImp := p.m.imports.size
    let some (_, _, fi) := p.m.exports.find? (fun (n, k, _) => n = exportName && k = 0)
      | throw (IO.userError "export not found")
    let fn := fi - nImp
    match check cfg p fn with
    | none => IO.println "{\"eligible\":false}"
    | some ck =>
      let gas : Gas := { Gas.init g0 with g := g0 }
      match instantiate cfg p gas with
      | .error e => throw (IO.userError s!"instantiate: {e}")
      | .ok s =>
        let s := { s with gas := gas, stack := #[], frames := [] }
        match enter p s fi with
        | .cont s1 =>
          let g1 := s1.gas.g
          let (n, r) := runSteps cfg p 100000000 s1 0
          let (status, stack, gf) := match r with
            | .fin s => ("fin", s.stack.toList, s.gas.g)
            | .abort s e => (s!"abort {e}", s.stack.toList, s.gas.g)
            | .unmodeled w => (s!"unmodeled {w}", [], 0)
            | .cont _ => ("cont", [], 0)
          let vals := stack.map valLimbs
          let recs := ck.records.toList.map natList
          let de := dataEnd s1
          let img := (List.range de).map fun a => (readByte s1 a).toNat
          IO.println s!"\{\"eligible\":true,\"fn\":{fn},\"ncode\":{ck.records.size},\"localTags\":{natList ck.localTags},\"arity\":{ck.arity},\"resTag\":{ck.resTag},\"maxFee\":{ck.maxFee},\"regularOpCost\":{cfg.regularOpCost},\"g0\":{g1},\"steps\":{n},\"status\":{jStr status},\"gFinal\":{gf},\"stack\":{jList (vals.map fun (t, l) => s!"\{\"tag\":{t},\"limbs\":{natList l}}")},\"heights\":{natList ck.heights.toList},\"records\":{jList recs},\"mem\":{memBytes s1},\"dataEnd\":{de},\"data\":{natList img}}"
        | _ => throw (IO.userError "enter failed")
  | .prepErr v w => IO.println s!"\{\"eligible\":false,\"prepare\":{jStr v},\"why\":{jStr w}}"
  | .compileErr _ _ => IO.println "{\"eligible\":false,\"prepare\":\"compile\"}"
  | .outOfDomain w => IO.println s!"\{\"eligible\":false,\"prepare\":{jStr w}}"
  | .unmodeled w => IO.println s!"\{\"eligible\":false,\"prepare\":{jStr w}}"

/-- `points` file: one point per line, `t sf sl st cur... | nxt... | pub...` as decimals. -/
def evalPoints (nloc ncode : Nat) (path : String) : IO Unit := do
  let A := wasmBaseAir nloc ncode
  let lines ← IO.FS.lines path
  for ln in lines do
    if ln.isEmpty then continue
    let parts := (ln.splitOn "|").map fun s => (s.splitOn " ").filter (· ≠ "") |>.map String.toNat!
    match parts with
    | [hd, cur, nxt, pub] =>
      let t := hd.getD 0 0
      let fe (n : Nat) : F := (n : F)
      let sf := fe (hd.getD 1 0); let sl := fe (hd.getD 2 0); let st := fe (hd.getD 3 0)
      let cf := fun i => fe (cur.getD i 0)
      let nf := fun i => fe (nxt.getD i 0)
      let pf := fun i => fe (pub.getD i 0)
      let T := A.tables.getD t default
      let ev := fun (e : WasmBase.Expr) => (e.evalG cf nf pf sf sl st).toNat
      let cs := T.constraints.map ev
      let is := T.inters.map fun i => natList ((ev i.count) :: i.msg.map ev)
      IO.println s!"\{\"t\":{t},\"constraints\":{natList cs},\"inters\":{jList is}}"
    | _ => throw (IO.userError "bad point line")

def main (args : List String) : IO Unit := do
  match args with
  | ["air", l, n] => IO.println (airJson (wasmBaseAir l.toNat! n.toNat!))
  | ["prep", path, exportName, g0] => prep path exportName g0.toNat!
  | ["eval", l, n, path] => evalPoints l.toNat! n.toNat! path
  | _ => IO.eprintln "usage: wasmbase-tool air <ncode> | prep <wasm> <exportName> <g0> | eval <ncode> <points>"
