import NearCompression.PreparedLiteralRunCall
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
  let fixture ← jsonFile (System.FilePath.mk (args.headD "/tmp/root-prepared-code-table-fixture.json"))
  let artifacts := System.FilePath.mk (args[1]?.getD "/tmp/near-prepared-code-table")
  let cases ← need (←field fixture "cases").getArr?
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
    require (ns.all (· < ZkFormal.Algebra.P)) "noncanonical fields"
    let pub := ns.map Fp.ofNat
    let eligible ← match preparedLiteralRunCallCheck pv86 bytes method ctx pub true with
      | some e=>pure e
      | none=>throw (IO.userError s!"{label}: literal runCall eligibility failed")
    for i in List.range 8 ++ List.range' 19 4 do
      require ((preparedLiteralRunCallCheck pv86 bytes method ctx (pub.set i (pub.getD i 0+1)) true).isNone)
        s!"{label}: altered entry header accepted at {i}"
      rejected:=rejected+1
    require (!preparedExecEntryCheck eligible.setup.program (eligible.setup.methodIndex+1)
      eligible.func eligible.setup.host pub) "wrong defined function accepted"
    rejected:=rejected+1
  IO.println (Json.mkObj [("status",toJson "PASS"),("actual_setup_cases",toJson cases.size),
    ("entry_mutations_rejected",toJson rejected),("scope",toJson "Actual setup/CODE/header eligibility; final public output composition remains open")]).compress
