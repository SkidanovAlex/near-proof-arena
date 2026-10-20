import NearCompression.PreparedExecFinalRow
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

private def stackValues (xs : Array Val) : List (Option Nat) :=
  xs.toList.map (fun v => match v with | .i32 x => some x.toNat | _ => none)

private def matchesPublished (pub : List Fp) (s : St) (err : Option String) : Bool :=
  pub.getD 44 0 == 1 && pub.getD 45 0 == (if err.isSome then 1 else 0) &&
  s.gas.g == preparedExecPublicGas pub true && (pub.getD 43 0).toNat < 9 &&
  stackValues s.stack == stackValues (preparedExecPublicStack pub (pub.getD 43 0).toNat)

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
    match runCall pv86 bytes method ctx (eligible.func.code.size+1) true with
    | .line why => throw (IO.userError s!"{label}: unexpected result {why}")
    | .done actual err =>
      require (matchesPublished pub actual err) s!"{label}: public output differs from actual interpreter"
      for i in [43,44,45,46,47,48,49] ++
          (List.range (2*actual.stack.size)).map (fun j => 50+j) do
        require (!matchesPublished (pub.set i (pub.getD i 0+1)) actual err)
          s!"{label}: public output mutation not detected at {i}"
        rejected:=rejected+1
  IO.println (Json.mkObj [("status",toJson "PASS"),("actual_setup_cases",toJson cases.size),
    ("output_mutations_detected",toJson rejected),("scope",toJson "Actual runCall/public-output decoder parity; mutations tested against decoder, not cryptographic verifier")]).compress
