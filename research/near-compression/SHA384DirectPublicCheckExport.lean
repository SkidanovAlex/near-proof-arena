import NearCompression.SHA384DirectPublicCheck
import Lean
open Lean NearCompression ZkFormal.Algebra
private def need (x : Except String α) : IO α :=
  match x with | .ok a=>pure a | .error e=>throw (IO.userError e)
/-- Accepts only canonical field encodings; raw aliases are deliberately not
reduced into fields by this parity fixture. -/
def main (args : List String) : IO Unit := do
  let input ← need (Json.parse (←IO.FS.readFile (args.headD "/tmp/sha384-public-cases.json")))
  let cases ← need input.getArr?
  let mut results : Array Json := #[]
  for c in cases do
    let label ← need (←need (c.getObjVal? "label")).getStr?
    let fields ← need (←need (c.getObjVal? "public")).getArr?
    let ns ← fields.toList.mapM (fun x=>need x.getNat?)
    unless ns.all (· < P) do throw (IO.userError s!"{label}: noncanonical raw field")
    let pub := ns.map Fp.ofNat
    results := results.push (Json.mkObj [("label",toJson label),
      ("accepted",toJson (sha384DirectPublicCheck pub)),
      ("decoded_digest",toJson ((sha384DirectPublicDecode pub).map UInt8.toNat))])
  IO.println (toJson results).compress
