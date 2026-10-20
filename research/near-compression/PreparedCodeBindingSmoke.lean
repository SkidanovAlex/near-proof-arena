import NearCompression.PreparedCodeBinding
import NearCompression.PreparedWasmEntry
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
  let root : System.FilePath := args.headD "."
  let fixture ← jsonFile (root / "airbender/direct-wasm/prepared-function-fixture.json")
  let cases ← need (←field fixture "cases").getArr?
  let mut reports : Array Json := #[]
  let mut totalMutations := 0
  for test in cases do
    let label ← need (←field test "label").getStr?
    let bytes ← naturalList (←field test "wasm_bytes")
    let bytes : ByteArray := ⟨(bytes.map UInt8.ofNat).toArray⟩
    let p ← match prepare pv86 bytes true with
      | .ok p => pure p
      | _ => throw (IO.userError s!"{label}: actual prepare failed")
    let pf ← match p.funcs[0]? with
      | some pf => pure pf
      | none => throw (IO.userError "missing actual PFunc")
    let spec ← jsonFile (root / "results/prepared-function-proofs" / label / "spec.json")
    let publicNat ← naturalList (←field spec "public")
    require (publicNat.all (· < ZkFormal.Algebra.P)) "noncanonical input serialization"
    let pub := publicNat.map Fp.ofNat
    require (preparedCodePublicCheck pf pub) s!"{label}: actual source/pub check failed"
    let built ← match preparedCodePublicBuild pf (pub.take 56) with
      | some built => pure built
      | none => throw (IO.userError "actual PFunc encoder rejected")
    require (built == pub) "all216 field parity with Python proof statement failed"
    require (built.take 56 == pub.take 56) "header was changed"
    -- All160CODE fields, including opcode/immediate/fee and synthetic padding.
    for i in List.range 160 do
      let index := 56+i
      let altered := pub.set index (pub.getD index 0+1)
      require (!preparedCodePublicCheck pf altered) s!"{label}: CODE mutation accepted at {index}"
      totalMutations := totalMutations+1
    let badFunctions : List (String × PFunc) := [
      ("unsupported-op",{pf with code:=pf.code.set! 0 (.num 0x6B)}),
      ("altered-immediate",{pf with code:=pf.code.set! 0 (.i32Const 123)}),
      ("gas-length",{pf with gas:=pf.gas.pop}),
      ("linear-fee",{pf with gas:=pf.gas.set! 0 (some (.pure,⟨1,1⟩))}),
      ("linear-kind",{pf with gas:=pf.gas.set! 0 (some (.linear,⟨1,0⟩))}),
      ("fee-overflow",{pf with gas:=pf.gas.set! 0 (some (.pure,⟨u64Bound,0⟩))}),
      ("changed-fee",{pf with gas:=pf.gas.set! 0 (some (.pure,⟨1,0⟩))}),
      ("empty-code",{pf with code:=#[],gas:=#[]}),
      ("oversize-code",{pf with code:=Array.replicate 17 .end_,gas:=Array.replicate 17 none})]
    for (why,bad) in badFunctions do
      require (!preparedCodePublicCheck bad pub) s!"{label}: malformed PFunc accepted: {why}"
      totalMutations := totalMutations+1
    require ((preparedCodePublicBuild pf (pub.take 55)).isNone) "short header accepted"
    require (!preparedCodePublicCheck pf (pub.take 215)) "short pub accepted"
    require (!preparedCodePublicCheck pf (pub++[0])) "long pub accepted"
    totalMutations := totalMutations+3
    -- Executable parity for the actual enter normal form, not a mocked gas fee.
    let prepaid ← need (←field test "prepaid").getNat?
    let (gas,e) := payPer (Gas.init prepaid) C.contractLoadingBytes bytes.size
    require e.isNone "loading bytes failed"
    let (gas,e) := payBase gas C.contractLoadingBase
    require e.isNone "loading base failed"
    let host ← need (instantiate pv86 p gas)
    let actual ← match enter p (preparedWasmHostReset host) 0 with
      | .cont s => pure s
      | _ => throw (IO.userError "actual enter failed")
    let expected := preparedWasmEntryState p 0 pf host
    require (actual.gas.g == expected.gas.g && actual.stackRem == expected.stackRem &&
      actual.stack.size == 0 && actual.frames.length == 1) "entry normalization mismatch"
    let af ← match actual.frames.head? with
      | some f => pure f | none => throw (IO.userError "missing entry frame")
    require (af.fn == 0 && af.pc == 0 && af.base == 0 && af.locals.size == pf.locals.size &&
      af.labels.length == 1) "entry frame mismatch"
    reports := reports.push (Json.mkObj [
      ("label",toJson label),("code_length",toJson pf.code.size),
      ("all_216_fields_match_python",toJson true),("mutations_rejected",toJson (172:Nat)),
      ("prologue_gas",toJson pf.prologueGas),("stack_charge",toJson pf.stackCharge),
      ("public",toJson (built.map Fp.toNat))])
  IO.println (Json.mkObj [("cases",toJson reports),("total_mutations_rejected",toJson totalMutations),
    ("actual_prepare",toJson true),("actual_enter_checked",toJson true)]).compress
