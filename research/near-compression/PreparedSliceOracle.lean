import NearCompression.PreparedExecFinalRow
import Lean

open Lean NearSpecV3.Wasm

private def need (x : Except String α) : IO α :=
  match x with | .ok v => pure v | .error e => throw (IO.userError e)

/-- Test oracle only: executes the request without reading proof/public outputs. -/
def main (args : List String) : IO Unit := do
  if args.length != 2 then throw (IO.userError "request path and fuel required")
  let j ← need (Json.parse (← IO.FS.readFile args[0]!))
  let raw ← need (← need (j.getObjVal? "wasm_bytes")).getArr?
  let ns ← raw.toList.mapM (fun x => need x.getNat?)
  if !ns.all (· < 256) then throw (IO.userError "invalid byte")
  let bytes : ByteArray := ⟨(ns.map UInt8.ofNat).toArray⟩
  let method ← need (← need (j.getObjVal? "method")).getStr?
  let prepaid ← need (← need (j.getObjVal? "prepaid")).getNat?
  let fuel ← match args[1]!.toNat? with
    | some x => pure x
    | none => throw (IO.userError "invalid fuel")
  match runCall pv86 bytes method {prepaidGas := prepaid} fuel true false none with
  | .line why => throw (IO.userError s!"unmodeled execution: {why}")
  | .done actual err =>
    let stack ← actual.stack.toList.mapM (fun v => match v with
      | .i32 x => pure x.toNat
      | _ => throw (IO.userError "non-i32 stack outside this slice"))
    IO.println (Json.mkObj [("done", toJson true), ("failed", toJson err.isSome),
      ("gas", toJson actual.gas.g), ("stack", toJson stack)]).compress
