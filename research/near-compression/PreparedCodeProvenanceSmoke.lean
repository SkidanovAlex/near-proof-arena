import NearCompression.PreparedCodeProvenance
import Lean

open Lean NearCompression NearSpecV3.Wasm ZkFormal.Algebra

private def need (value : Except String α) : IO α :=
  match value with | .ok x => pure x | .error e => throw (IO.userError e)
private def require (condition : Bool) (why : String) : IO Unit :=
  if condition then pure () else throw (IO.userError why)
private def jsonFile (path : System.FilePath) : IO Json := do
  need (Json.parse (←IO.FS.readFile path))
private def field (j : Json) (key : String) : IO Json := need (j.getObjVal? key)
private def naturalList (j : Json) : IO (List Nat) := do
  let xs ← need j.getArr?
  xs.toList.mapM (fun x=>need x.getNat?)

def main (args : List String) : IO Unit := do
  let fixturePath := args.headD "/tmp/prepared-code-table-fixture.json"
  let artifacts : System.FilePath := System.FilePath.mk (args[1]?.getD "/tmp/near-prepared-code-table")
  let fixture ← jsonFile fixturePath
  let cases ← need (←field fixture "cases").getArr?
  let mut reports : Array Json := #[]
  let mut rejected := 0
  for test in cases do
    let label ← need (←field test "label").getStr?
    let raw ← naturalList (←field test "wasm_bytes")
    let bytes : ByteArray := ⟨(raw.map UInt8.ofNat).toArray⟩
    let method ← need (←field test "method").getStr?
    let prepaid ← need (←field test "prepaid").getNat?
    let ctx : CallCtx := {prepaidGas:=prepaid}
    let spec ← jsonFile (artifacts / (label++"-spec.json"))
    let ns ← naturalList (←field spec "public")
    require (ns.all (· < ZkFormal.Algebra.P)) "noncanonical serialized fields"
    let pub := ns.map Fp.ofNat
    let eligible ← match preparedCodePreparedCheck pv86 bytes method ctx pub true with
      | some eligible=>pure eligible
      | none=>throw (IO.userError s!"{label}: actual prepare/code check failed")
    let fn := eligible.setup.methodIndex-eligible.setup.program.m.imports.size
    let pf := eligible.func
    let built ← match preparedCodeVariableBuild pf fn (pub.take 66) with
      | some built=>pure built
      | none=>throw (IO.userError s!"{label}: actual descriptor builder failed")
    require (built==pub) s!"{label}: all public descriptor fields disagree with Python"
    for i in List.range (25*pf.code.size) do
      let index:=66+i
      require (!preparedCodeVariableCheck pf fn (pub.set index (pub.getD index 0+1)))
        s!"{label}: descriptor mutation accepted at{index}"
      rejected:=rejected+1
    for index in List.range' 8 4 do
      require (!preparedCodeVariableCheck pf fn (pub.set index (pub.getD index 0+1)))
        "wrong code count accepted"
      rejected:=rejected+1
    for bad in [pub.take (pub.length-1),pub++[0]] do
      require (!preparedCodeVariableCheck pf fn bad) "wrong length accepted"
      rejected:=rejected+1
    let malformed : List PFunc := [
      {pf with code:=pf.code.set! 0 (.num 0x6B)},
      {pf with gas:=pf.gas.pop},
      {pf with gas:=pf.gas.set! 0 (some (.linear,⟨1,0⟩))},
      {pf with gas:=pf.gas.set! 0 (some (.pure,⟨1,1⟩))},
      {pf with gas:=pf.gas.set! 0 (some (.pure,⟨u64Bound,0⟩))},
      {pf with code:=#[],gas:=#[]}]
    for bad in malformed do
      require (!preparedCodeVariableCheck bad fn pub) "malformed actual function accepted"
      rejected:=rejected+1
    require ((preparedCodePreparedCheck pv86 bytes "absent" ctx pub true).isNone) "missing method accepted"
    require ((preparedCodePreparedCheck pv86 ⟨bytes.data.set! 0 1⟩ method ctx pub true).isNone) "bad magic accepted"
    rejected:=rejected+2
    reports:=reports.push (Json.mkObj [("label",toJson label),("instructions",toJson pf.code.size),
      ("actual_prepare_checked",toJson true),("exact_public_field_parity",toJson pub.length)])
  IO.println (Json.mkObj [("cases",toJson reports),("rejections",toJson rejected),
    ("full_new_air_refinement_claimed",toJson false)]).compress
