import NearCompression.PreparedLocalsCode
import Lean
open Lean NearCompression NearSpecV3.Wasm ZkFormal.Algebra
private def need (x : Except String α) : IO α :=
  match x with | .ok a=>pure a | .error e=>throw (IO.userError e)
private def req (ok : Bool) (why : String) : IO Unit :=
  unless ok do throw (IO.userError why)
private def field (j : Json) (k : String) : IO Json := need (j.getObjVal? k)
private def nats (j : Json) : IO (List Nat) := do
  (←need j.getArr?).toList.mapM (fun x=>need x.getNat?)
def main (args : List String) : IO Unit := do
  let fixture ← need (Json.parse (←IO.FS.readFile (args.headD "/tmp/near-prepared-locals-fixture.json")))
  let out := System.FilePath.mk (args[1]?.getD "/tmp/near-prepared-locals-air")
  let cases ← need (←field fixture "cases").getArr?
  let mut rejected:=0
  let mut fields:=0
  for c in cases do
    let label ← need (←field c "label").getStr?
    let raw ← nats (←field c "wasm_bytes")
    let bytes : ByteArray:=⟨(raw.map UInt8.ofNat).toArray⟩
    let method ← need (←field c "method").getStr?
    let count ← need (←field c "local_count").getNat?
    let prepaid ← need (←field c "prepaid").getNat?
    let ctx : CallCtx:={prepaidGas:=prepaid}
    let spec ← need (Json.parse (←IO.FS.readFile (out/(label++"-spec.json"))))
    let ns ← nats (←field spec "public")
    req (ns.all (·<ZkFormal.Algebra.P)) "noncanonical field serialization"
    let pub:=ns.map Fp.ofNat
    let eligible ← match preparedLocalsSetupCheck count pv86 bytes method ctx pub true with
      | some e=>pure e | none=>throw (IO.userError s!"{label}: actual setup/CODE failed")
    let pf:=eligible.func
    for i in (List.range 4).map (fun j=>8+j) ++ (List.range (32*pf.code.size)).map (fun j=>66+j) do
      req (!preparedLocalsCodeCheck count pf 0 (pub.set i (pub.getD i 0+1))) s!"{label}: field {i}"
      rejected:=rejected+1
    fields:=fields+32*pf.code.size
    for wrong in List.range 6 do
      if wrong != count then
        req (!preparedLocalsCodeCheck wrong pf 0 pub) s!"{label}: wrong count accepted"
        rejected:=rejected+1
    for badPub in [pub.dropLast,pub++[0]] do
      req (!preparedLocalsCodeCheck count pf 0 badPub) s!"{label}: public length"
      rejected:=rejected+1
    for bad in [{pf with locals:=pf.locals.set! 0 VT.i64},
        {pf with code:=pf.code.set! 0 (.localGet count)},
        {pf with code:=pf.code.set! 0 (.localSet count)},
        {pf with code:=pf.code.set! 0 (.localTee count)},
        {pf with code:=pf.code.set! 0 (.call 0)},
        {pf with gas:=pf.gas.pop},
        {pf with type:={pf.type with params:=#[VT.i32]}},
        {pf with type:={pf.type with results:=#[VT.i32]}}] do
      req (!preparedLocalsCodeCheck count bad 0 pub) s!"{label}: malformed prepared metadata"
      rejected:=rejected+1
    req ((preparedLocalsSetupCheck count pv86 bytes "missing" ctx pub true).isNone) "missing export"
    req ((preparedLocalsSetupCheck count pv86 ByteArray.empty method ctx pub true).isNone) "empty module"
    rejected:=rejected+2
  IO.println (Json.mkObj [("status",toJson "PASS"),("actual_prepare_cases",toJson cases.size),
    ("exact_code_fields",toJson fields),("rejected",toJson rejected),
    ("scope",toJson "Executable actual PREP/CODE/local count provenance checker, not full AIR/runCall refinement")]).compress
