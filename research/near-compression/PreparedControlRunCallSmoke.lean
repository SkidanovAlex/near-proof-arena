import NearCompression.PreparedControlRunCall
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
  let fixture ← jsonFile (System.FilePath.mk (args.headD "/tmp/near-control-runcall-fixture.json"))
  let artifacts := System.FilePath.mk (args[1]?.getD "/tmp/near-control-runcall-air")
  let cases ← need (←field fixture "cases").getArr?
  let mut rejected := 0
  let mut checkerRejected := 0
  let mut fields := 0
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
    let eligible ← match preparedControlRunCallCheck pv86 bytes method ctx pub true with
      | some e=>pure e
      | none=>throw (IO.userError s!"{label}: literal runCall eligibility failed")
    fields := fields + pub.length
    -- Eligibility-checker negatives; output mutations below use the decoder.
    for i in List.range 12 ++ [19,20,21,22] ++
        (List.range (pub.length-66)).map (fun j=>66+j) do
      require ((preparedControlRunCallCheck pv86 bytes method ctx
        (pub.set i (pub.getD i 0+1)) true).isNone)
        s!"{label}: checker accepted altered header/CODE field {i}"
      checkerRejected := checkerRejected+1
    for badPub in [pub.dropLast, pub ++ [0]] do
      require ((preparedControlRunCallCheck pv86 bytes method ctx badPub true).isNone)
        s!"{label}: checker accepted wrong public length"
      checkerRejected := checkerRejected+1
    require ((preparedControlRunCallCheck pv86 bytes "missing" ctx pub true).isNone)
      s!"{label}: checker accepted missing export"
    require ((preparedControlRunCallCheck pv86 bytes method {prepaidGas:=prepaid+1} pub true).isNone)
      s!"{label}: checker accepted mismatched entry gas"
    for badBytes in [ByteArray.empty, bytes.extract 0 (bytes.size-1),
        (⟨#[255,97,115,109]⟩ : ByteArray)] do
      require ((preparedControlRunCallCheck pv86 badBytes method ctx pub true).isNone)
        s!"{label}: checker accepted malformed module"
    checkerRejected := checkerRejected+5
    match runCall pv86 bytes method ctx (eligible.func.code.size+1) true with
    | .line why => throw (IO.userError s!"{label}: unexpected result {why}")
    | .done actual err =>
      let expectedError ← field test "error"
      require ((toJson err).compress == expectedError.compress)
        s!"{label}: actual interpreter error differs from fixture"
      require (matchesPublished pub actual err) s!"{label}: public output differs from actual interpreter"
      for i in [43,44,45,46,47,48,49] ++
          (List.range (2*actual.stack.size)).map (fun j => 50+j) do
        require (!matchesPublished (pub.set i (pub.getD i 0+1)) actual err)
          s!"{label}: public output mutation not detected at {i}"
        rejected:=rejected+1
  IO.println (Json.mkObj [("status",toJson "PASS"),("actual_setup_cases",toJson cases.size),
    ("checker_mutations_rejected",toJson checkerRejected),("public_fields_checked",toJson fields),
    ("output_mutations_detected",toJson rejected),("scope",toJson "Actual preparation/CODE/entry checker negatives and separate runCall/public-output decoder parity; no cryptographic verifier mutation claim")]).compress
