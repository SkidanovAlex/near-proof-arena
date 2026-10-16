import NearCompression.PreparedExecFinalRow
import Lean

open Lean NearCompression NearSpecV3.Wasm ZkFormal.Algebra

private def need (value : Except String α) : IO α :=
  match value with | .ok x => pure x | .error e => throw (IO.userError e)
private def require (condition : Bool) (why : String) : IO Unit :=
  if condition then pure () else throw (IO.userError why)
private def field (j : Json) (key : String) : IO Json := need (j.getObjVal? key)
private def naturals (j : Json) : IO (List Nat) := do
  let xs ← need j.getArr?
  xs.toList.mapM (fun x => need x.getNat?)

/-- Preparation and eligibility only: never executes the requested function.
The cryptographic frontend must establish the HoldsP premise separately. -/
def main (args : List String) : IO Unit := do
  require (args.length == 1) "expected request/public JSON path"
  let input ← need (Json.parse (← IO.FS.readFile args[0]!))
  let request ← field input "request"
  let raw ← naturals (← field request "wasm_bytes")
  require (raw.all (· < 256)) "noncanonical Wasm byte"
  let code : ByteArray := ⟨(raw.map UInt8.ofNat).toArray⟩
  let method ← need (← field request "method").getStr?
  let prepaid ← need (← field request "prepaid").getNat?
  let ns ← naturals (← field input "public")
  require (ns.all (· < ZkFormal.Algebra.P)) "noncanonical public field"
  let pub := ns.map Fp.ofNat
  let eligible ← match preparedLiteralRunCallCheck pv86 code method {prepaidGas:=prepaid} pub true with
    | some e => pure e
    | none => throw (IO.userError "literal runCall eligibility rejected")
  IO.println (Json.mkObj [("status", toJson "PASS"),
    ("code_length", toJson eligible.func.code.size)]).compress
