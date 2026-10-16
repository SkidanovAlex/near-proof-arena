import NearCompression.BusFormulaCheck
import NearCompression.GeneratedExt8BusSpecCheck
import Lean
open Lean NearCompression ZkFormal.Algebra
private def need (x : Except String α) : IO α :=
  match x with | .ok a => pure a | .error e => throw (IO.userError e)
private def require (b : Bool) (msg : String) : IO Unit :=
  if b then pure () else throw (IO.userError msg)
private def field (j : Json) (k : String) : IO Json := need (j.getObjVal? k)
private def baseScalar (j : Json) : IO Fp := do
  let x ← need j.getNat?
  require (x<2013265921) "noncanonical base scalar"
  return Fp.ofNat x
private def scalar (j : Json) : IO Fp8 := do
  let a ← need j.getArr?
  require (a.size==8) "Ext8 scalar width"
  let xs ← a.toList.mapM baseScalar
  return Fp8.ofCoeffs (fun i=>xs.getD i 0)
private partial def expression (j : Json) : IO ZkFormal.Air.Expr := do
  let a ← need j.getArr?
  require (0<a.size) "empty AIR expression"
  let tag ← need a[0]!.getStr?
  match tag with
  | "c" | "p" =>
      require (a.size==2) "AIR constant/pubValues arity"
      let n ← need a[1]!.getNat?
      return if tag=="c" then .const n else .pub n
  | "v" =>
      require (a.size==3) "AIR column arity"
      let c ← need a[1]!.getNat?
      let nx ← need a[2]!.getBool?
      return .col c nx
  | "first" | "last" | "trans" =>
      require (a.size==1) "AIR selector arity"
      return if tag=="first" then .isFirst else if tag=="last" then .isLast else .isTransition
  | "+" | "*" =>
      require (a.size==3) "AIR binary arity"
      let left ← expression a[1]!
      let right ← expression a[2]!
      return if tag=="+" then .add left right else .mul left right
  | "-" =>
      require (a.size==2) "AIR negation arity"
      return .neg (←expression a[1]!)
  | _ => throw (IO.userError "unknown AIR expression")

private partial def busFormula (j : Json) : IO (BusProgramFormula Fp8) := do
  let a ← need j.getArr?
  require (0<a.size) "empty bus formula"
  let tag ← need a[0]!.getStr?
  match tag with
  | "lit" =>
      require (a.size==2) "bus literal arity"
      return .literal (←scalar a[1]!)
  | "current" | "next" =>
      require (a.size==2) "bus column arity"
      let c ← need a[1]!.getNat?
      return if tag=="current" then .current c else .next c
  | "first" | "last" | "trans" =>
      require (a.size==1) "bus selector arity"
      return if tag=="first" then .first else if tag=="last" then .last else .transition
  | "add" | "sub" | "mul" =>
      require (a.size==3) "bus binary arity"
      let left ← busFormula a[1]!
      let right ← busFormula a[2]!
      return if tag=="add" then .add left right else if tag=="sub" then .sub left right else .mul left right
  | _ => throw (IO.userError "unknown bus formula")

private def instruction (j : Json) : IO (TerminalInstruction Fp8) := do
  let a ← need j.getArr?
  require (a.size==11) "Ext8 instruction width"
  let code ← need a[0]!.getNat?
  let some opcode := terminalDecodeOpcode code | throw (IO.userError "instruction opcode")
  return ⟨opcode,←need a[1]!.getNat?,←need a[2]!.getNat?,←scalar (Json.arr (a.extract 3 11))⟩
private def interaction (j : Json) : IO ZkFormal.Air.Interaction := do
  let bus ← need (←field j "bus").getNat?
  let send ← need (←field j "send").getBool?
  let msg ← (←need (←field j "msg").getArr?).toList.mapM expression
  let mult ← (←need (←field j "mult").getArr?).toList.mapM expression
  return { bus := bus, send := send, msg := msg, mult := mult }
def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected fixture path")
  let document ← need (Json.parse (←IO.FS.readFile path))
  let cases ← need document.getArr?
  require (0<cases.size) "empty fixture"
  let mut count := 0
  for caseData in cases do
    let width ← need (←field caseData "width").getNat?
    let current ← (←need (←field caseData "current").getArr?).toList.mapM baseScalar
    let next ← (←need (←field caseData "next").getArr?).toList.mapM baseScalar
    require (current.length==width && next.length==width) "coordinate width"
    let selectors ← field caseData "selectors"
    let env : TerminalProgramEnvironment Fp8 := {
      current:=fun c=>Fp8.ofBase (current.getD c 0)
      next:=fun c=>Fp8.ofBase (next.getD c 0)
      first:=←scalar (←field selectors "first")
      last:=←scalar (←field selectors "last")
      transition:=←scalar (←field selectors "trans") }
    let residuals ← need (←field caseData "residuals").getArr?
    require (0<residuals.size) "empty residuals"
    let table ← field caseData "table"
    let sourceWidth ← need (←field table "width").getNat?
    let interactions ← (←need (←field table "interactions").getArr?).toList.mapM interaction
    let publicValues ← (←need (←field caseData "public").getArr?).toList.mapM baseScalar
    let alpha ← scalar (←field caseData "alpha")
    let gamma ← scalar (←field caseData "gamma")
    let finals ← (←need (←field caseData "finals").getArr?).toList.mapM scalar
    require (finals.length==interactions.length) "final count"
    let lowered := interactions.map (lowerBusInteraction (publicValues.map Fp8.ofBase) alpha gamma)
    require (width==sourceWidth+8*(busTableChainColumns lowered+interactions.length)) "specified coordinate width"
    let formulas ← residuals.toList.mapM (fun residual=>do busFormula (←field residual "formula"))
    require (generatedExt8BusSpecCheck lowered sourceWidth (fun i=>finals.getD i 0) formulas) "bus specification rejected"

    for residual in residuals do
      let formula ← busFormula (←field residual "formula")
      let program ← (←need (←field residual "instructions").getArr?).toList.mapM instruction
      let root ← need (←field residual "root").getNat?
      let expected ← scalar (←field residual "expected")
      require (busFormulaCheck program width formula root) "formula route rejected"
      require (terminalAcyclicCheck 0 (program.map (terminalProgramNode env))) "acyclicity rejected"
      require (decide (busProgramFormulaValue env formula=expected)) "formula value mismatch"
      require (decide (terminalProgramRun env 0 (fun _=>0) program root=expected)) "program value mismatch"
      count := count+1
  IO.println (Json.mkObj [("status",toJson "PASS"),("cases",toJson cases.size),("residuals",toJson count)]).compress
