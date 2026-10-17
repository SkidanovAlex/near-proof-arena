import NearCompression.PreparedRunCall
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

-- This compares precisely the published semantic output relation. It does not
-- replace AIR acceptance: the setup checker alone intentionally does not check output.
private def matchesPublished (pub : List Fp) (final : St) (error : Option String) : Bool :=
  let sp := (pub.getD 33 0).toNat
  (pub.getD 34 0 == 1) && (pub.getD 35 0 == if error.isSome then 1 else 0) &&
  (final.gas.g == preparedPublicGas pub true) && sp < 9 &&
  final.stack.size == sp && (List.range sp).all (fun i=>
    match final.stack[i]? with
    | some (.i32 value) => value == UInt32.ofNat (preparedPublicStackWord pub i)
    | _ => false)

def main (args : List String) : IO Unit := do
  let root : System.FilePath := args.headD "/data/illia/nearproof-wt/direct-wasm-whir/research/near-compression"
  let fixture ← jsonFile (root / "airbender/direct-wasm/prepared-function-fixture.json")
  let cases ← need (←field fixture "cases").getArr?
  let mut reports : Array Json := #[]
  let mut rejected := 0
  let mut outputRejected := 0
  for test in cases do
    let label ← need (←field test "label").getStr?
    let byteNats ← naturalList (←field test "wasm_bytes")
    let bytes : ByteArray := ⟨(byteNats.map UInt8.ofNat).toArray⟩
    let method ← need (←field test "method").getStr?
    let prepaid ← need (←field test "prepaid").getNat?
    let ctx : CallCtx := {prepaidGas:=prepaid}
    let spec ← jsonFile (root / "results/prepared-function-proofs" / label / "spec.json")
    let publicNat ← naturalList (←field spec "public")
    require (publicNat.all (· < ZkFormal.Algebra.P)) "noncanonical public serialization"
    let pub := publicNat.map Fp.ofNat
    let eligible ← match preparedRunCallCheck pv86 bytes method ctx pub true with
      | some result => pure result
      | none => throw (IO.userError s!"{label}: actual runCall checker rejected honest case")
    require (preparedRunCallEntryCheck eligible.setup eligible.func pub) "entry guard mismatch"
    -- All CODE records, all count limbs, and all initial-gas limbs.
    let checkedFields := List.range' 56 160 ++ List.range 8 ++ List.range' 12 4
    for i in checkedFields do
      let altered := pub.set i (pub.getD i 0+1)
      require ((preparedRunCallCheck pv86 bytes method ctx altered true).isNone)
        s!"{label}: checkedFields public mutation accepted at {i}"
      rejected := rejected+1
    let (byteGas,byteError) := payPer (Gas.init prepaid) C.contractLoadingBytes bytes.size
    require byteError.isNone "honest byte loading unexpectedly failed"
    let loadingCost := eligible.setup.host.gas.burnt
    let setupFailures : List (String × ByteArray × String × CallCtx) := [
      ("empty-method",bytes,"",ctx),
      ("missing-method",bytes,"absent",ctx),
      ("bad-magic",⟨bytes.data.set! 0 1⟩,method,ctx),
      ("truncated-module",⟨bytes.data.pop⟩,method,ctx),
      ("byte-loading-exhaustion",bytes,method,{ctx with prepaidGas:=0}),
      ("base-loading-exhaustion",bytes,method,{ctx with prepaidGas:=byteGas.burnt})]
    for (why,code,name,context) in setupFailures do
      require ((preparedRunCallSetup pv86 code name context true).isNone)
        s!"{label}: setup failure accepted: {why}"
      require ((preparedRunCallCheck pv86 code name context pub true).isNone)
        s!"{label}: checker failure accepted: {why}"
      rejected := rejected+1
    let shortEntry : CallCtx := {ctx with prepaidGas:=loadingCost+eligible.func.prologueGas-1}
    let shortSetup ← match preparedRunCallSetup pv86 bytes method shortEntry true with
      | some result => pure result
      | none => throw (IO.userError "entry exhaustion should pass setup")
    let coherentShortPub := (List.range' 12 4).foldl (fun claim i=>claim.set i 0) pub
    require (preparedPublicEntryCheck coherentShortPub shortSetup.host eligible.func)
      "prologue test public gas was not coherent"
    require ((preparedRunCallCheck pv86 bytes method shortEntry coherentShortPub true).isNone)
      "prologue exhaustion accepted with coherent public gas"
    rejected := rejected+1
    for bad in [pub.take 215,pub++[0]] do
      require ((preparedRunCallCheck pv86 bytes method ctx bad true).isNone) "public length accepted"
      rejected := rejected+1
    let fuel := eligible.func.code.size
    let (final,error) ← match runCall pv86 bytes method ctx fuel true false none with
      | .done s e => pure (s,e)
      | .line why => throw (IO.userError s!"{label}: actual runCall failed: {why}")
    require (matchesPublished pub final error) s!"{label}: published semantic output mismatch"
    require ((toJson error).compress == (←field test "error").compress) "exact interpreter error mismatch"
    let expectedOutcome ← need (←field test "actual_run_call_outcome").getStr?
    require (outcome pv86 bytes method ctx fuel true == expectedOutcome) "actual fixture outcome mismatch"
    -- The setup checker does not authenticate output; AIR/bus acceptance supplies
    -- that obligation. These mutations must fail the separate output relation.
    for i in [33,34,35,36,37,38,39] do
      let altered := pub.set i (pub.getD i 0+1)
      require (!(matchesPublished altered final error)) s!"{label}: wrong published output accepted at {i}"
      outputRejected := outputRejected+1
    reports := reports.push (Json.mkObj [
      ("label",toJson label),("setup_and_code_checked",toJson true),
      ("actual_run_call_matches_public",toJson true),("fuel",toJson fuel),
      ("actual_error",toJson error),("actual_fast_gas",toJson final.gas.g),
      ("actual_burnt",toJson final.gas.burnt),("public_mutations_rejected",toJson checkedFields.length),
      ("setup_and_eligibility_rejections",toJson (9:Nat))])
  IO.println (Json.mkObj [("cases",toJson reports),("checker_rejections",toJson rejected),
    ("output_relation_rejections",toJson outputRejected),
    ("air_acceptance_tested_here",toJson false)]).compress
