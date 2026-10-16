import NearCompression.PreparedControlSetup
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
  let fixturePath := args.headD "/tmp/near-prepared-control-fixture.json"
  let artifacts : System.FilePath := System.FilePath.mk (args[1]?.getD "/tmp/near-prepared-control-air")
  let fixture ← jsonFile fixturePath
  let cases ← need (←field fixture "cases").getArr?
  let mut reports : Array Json := #[]
  let mut rejected := 0
  for test in cases do
    let label ← need (←field test "label").getStr?
    let raw ← naturalList (←field test "wasm_bytes")
    let bytes : ByteArray := ⟨(raw.map UInt8.ofNat).toArray⟩
    let method ← need (←field test "method").getStr?
    let spec ← jsonFile (artifacts / (label++"-spec.json"))
    let ns ← naturalList (←field spec "public")
    require (ns.all (· < ZkFormal.Algebra.P)) "noncanonical serialized fields"
    let pub := ns.map Fp.ofNat
    let program ← match prepare pv86 bytes true with
      | .ok p=>pure p
      | _=>throw (IO.userError s!"{label}: actual prepare failed")
    let fi ← match resolve program method with
      | .ok fi=>pure fi
      | _=>throw (IO.userError "method resolution failed")
    let fn:=fi-program.m.imports.size
    let pf:=program.funcs[fn]!
    let prepaid ← need (←field test "prepaid").getNat?
    let ctx : CallCtx := {prepaidGas:=prepaid}
    let eligible ← match preparedControlSetupCheck pv86 bytes method ctx pub true with
      | some e=>pure e
      | none=>throw (IO.userError s!"{label}: actual setup checker rejected")
    require (preparedControlCodeCheck eligible.func
      (eligible.setup.methodIndex-eligible.setup.program.m.imports.size) pub) "setup function mismatch"
    require ((preparedControlSetupCheck pv86 bytes "" ctx pub true).isNone) "empty method accepted"
    require ((preparedControlSetupCheck pv86 ByteArray.empty method ctx pub true).isNone) "empty code accepted"
    require ((preparedControlSetupCheck pv86 bytes method ctx (pub++[0]) true).isNone) "extra public field accepted"
    require (preparedControlCodeCheck pf fn pub) s!"{label}: actual prepared CODE differs from Python public descriptor"
    for i in List.range (29*pf.code.size) do
      let index:=66+i
      require (!preparedControlCodeCheck pf fn (pub.set index (pub.getD index 0+1)))
        s!"{label}: descriptor mutation accepted at{index}"
      rejected:=rejected+1
    for index in List.range' 8 4 do
      require (!preparedControlCodeCheck pf fn (pub.set index (pub.getD index 0+1)))
        "wrong code count accepted"
      rejected:=rejected+1
    for bad in [pub.take (pub.length-1),pub++[0]] do
      require (!preparedControlCodeCheck pf fn bad) "wrong length accepted"
      rejected:=rejected+1
    let malformed : List PFunc := [
      {pf with code:=pf.code.set! 0 (.num 0x6B)},
      {pf with gas:=pf.gas.pop},
      {pf with gas:=pf.gas.set! 0 (some (.linear,⟨1,0⟩))},
      {pf with gas:=pf.gas.set! 0 (some (.pure,⟨1,1⟩))},
      {pf with gas:=pf.gas.set! 0 (some (.pure,⟨u64Bound,0⟩))},
      {pf with code:=#[],gas:=#[]}]
    for bad in malformed do
      require (!preparedControlCodeCheck bad fn pub) "malformed actual function accepted"
      rejected:=rejected+1
    for pc in List.range pf.code.size do
      if (preparedControlInspect pf.code[pc]!)==some .block then
        let bad:={pf with endOf:=pf.endOf.set! pc (pf.endOf[pc]!+1)}
        require (!preparedControlCodeCheck bad fn pub) "changed prepared endOf accepted"
        rejected:=rejected+1
    for ins in [Instr.block (some .i32),.loop none,.br 0,.brIf 1,.localGet 0,.localSet 0,.localTee 0] do
      require ((preparedControlInspect ins).isNone) "unsupported control/local opcode accepted"
      rejected:=rejected+1
    reports:=reports.push (Json.mkObj [("label",toJson label),("instructions",toJson pf.code.size),
      ("actual_prepare_checked",toJson true),("actual_setup_checked",toJson true),("exact_public_field_parity",toJson pub.length)])
  IO.println (Json.mkObj [("cases",toJson reports),("rejections",toJson rejected),("additional_setup_rejections",toJson (3*cases.size)),
    ("full_new_air_refinement_claimed",toJson false)]).compress
