import NearCompression.InstructionAddRange
import Lean

namespace NearCompression
open NearSpecV3.Wasm Lean
private def obj := Json.mkObj
private def num (n : Nat) : Json := toJson n
private def arr (xs : List Json) : Json := toJson xs
private def gasJson (g : Gas) : Json := obj [
  ("burnt",num g.burnt),("promises",num g.promises),("prepaid",num g.prepaid),
  ("limit",num g.limit),("g",num g.g),("host",num g.host),("action",num g.action),
  ("special",toJson g.special),("send_compute",num g.sendCompute)]
private def valJson : Val → Json
  | .i32 v => obj [("tag",num 0),("limbs",toJson [v.toNat % 65536,v.toNat / 65536])]
  | .i64 v => obj [("tag",num 1),("value",num v.toNat)]
  | .ref n => obj [("tag",num 2),("value",toJson n)]
private def stateJson (s : St) : Json := obj [
  ("stack",toJson (s.stack.map valJson)), ("gas",gasJson s.gas),
  ("frames",arr (s.frames.map fun f => obj [("fn",num f.fn),("pc",num f.pc),
    ("base",num f.base),("locals",toJson (f.locals.map valJson)),
    ("labels",arr (f.labels.map fun l => toJson [l.target,l.arity,l.height,if l.isLoop then 1 else 0]))])),
  ("stack_remaining",num s.stackRem),("balance",num s.balance),("storage_usage",num s.storageUsage)]
private def opJson : Instr → Except String Json
  | .i32Const v => .ok (obj [("opcode",num 0x41),("immediate",num v.toNat)])
  | .num 0x6a => .ok (obj [("opcode",num 0x6a),("immediate",num 0)])
  | .drop => .ok (obj [("opcode",num 0x1a),("immediate",num 0)])
  | .end_ => .ok (obj [("opcode",num 0x0b),("immediate",num 0)])
  | _ => .error "unsupported instruction in prepared-function slice"
private def feeJson : Option (IK × Fee) → Json
  | none => Json.null
  | some (k,f) => obj [("kind",num (match k with | .pure=>0 | .unreach=>1 | .pre=>2 | .post=>3 | .between=>4 | .linear=>5)),("linear_kind",toJson (k == .linear)),("constant",num f.c),("linear",num f.l)]
private def event (clock slot : Nat) (write : Bool) (v : Val) : Json :=
  obj [("clock",num clock),("slot",num slot),("write",toJson write),("value",valJson v)]
private def stackEvents (clock : Nat) (op : Instr) (s t : St) : List Json :=
  let n := s.stack.size
  match op with
  | .i32Const _ => [event clock n true (t.stack[n]!) ]
  | .num 0x6a => [event clock (n-1) false (s.stack[n-1]!),
      event clock (n-2) false (s.stack[n-2]!),event clock (n-2) true (t.stack[n-2]!)]
  | .drop => [event clock (n-1) false (s.stack[n-1]!)]
  | _ => []

/-- Valid binary with exported []→[] main. Constants are signed single-byte LEB128. -/
def preparedSliceBytes (a b : UInt8) : ByteArray := ⟨#[0,97,115,109,1,0,0,0,
  1,4,1,96,0,0,3,2,1,0,7,8,1,4,109,97,105,110,0,0,
  10,10,1,8,0,65,a,65,b,106,26,11]⟩

private def shortULEB (n : Nat) : List UInt8 :=
  if n<128 then [UInt8.ofNat n] else [UInt8.ofNat (n%128+128),UInt8.ofNat (n/128)]
/-- Repeated real const/drop pairs with arbitrary section-size LEB for this fixture. -/
def preparedLongSliceBytes (pairs : Nat) : ByteArray :=
  let body : List UInt8 := [0] ++ (List.replicate pairs [65,1,26]).flatten ++ [11]
  let payload := [1] ++ shortULEB body.length ++ body
  ⟨([0,97,115,109,1,0,0,0,1,4,1,96,0,0,3,2,1,0,7,8,1,4,109,97,105,110,0,0,10] ++
    shortULEB payload.length ++ payload).toArray⟩

private def need (x : Option α) (why : String) : Except String α :=
  match x with | some a => .ok a | none => .error why

private def traceSteps (p : Prepared) : Nat → Nat → St → Except String (List Json × St × Option String)
  | 0,_,_ => .error "fixture fuel exhausted"
  | fuel+1,clock,s => do
    let f ← need s.frames.head? "expected frame"
    let pf ← need p.funcs[f.fn]? "expected prepared function"
    let i ← need pf.code[f.pc]? "expected opcode"
    let op ← opJson i
    let fee ← need pf.gas[f.pc]? "missing prepared gas entry"
    let (t,status,err,cont) ← match step pv86 p s with
      | .cont t => pure (t,"continue",none,true)
      | .fin t => pure (t,"finish",none,false)
      | .abort t e => pure (t,"abort",some e,false)
      | .unmodeled e => throw e
    let events := if err.isSome then [] else stackEvents clock i s t
    let row := obj [("clock",num clock),("function",num f.fn),("pc",num f.pc),
      ("instruction",op),("charge",feeJson fee),("before",stateJson s),("after",stateJson t),
      ("stack_events",arr events),("status",toJson status),("error",toJson err)]
    if cont then
      let (rest,last,err) ← traceSteps p fuel (clock+1) t
      pure (row::rest,last,err)
    else pure ([row],t,err)

private def makeCaseBytes (label : String) (bytes : ByteArray) (prepaid : Nat) : Except String Json := do
  let ctx : CallCtx := { prepaidGas := prepaid }
  let p ← match prepare pv86 bytes true with
    | .ok p => pure p
    | _ => throw "actual prepare rejected fixture"
  let mi ← match resolve p "main" with
    | .ok n => pure n
    | _ => throw "actual method resolution failed"
  match link p with
  | .ok => pure ()
  | _ => throw "actual link failed"
  if p.m.start.isSome || !p.m.imports.isEmpty then throw "fixture domain"
  let (gs,e) := payPer (Gas.init prepaid) C.contractLoadingBytes bytes.size
  if e.isSome then throw "loading bytes exhausted"
  let (gs,e) := payBase gs C.contractLoadingBase
  if e.isSome then throw "loading base exhausted"
  let s ← instantiate pv86 p gs
  let s := { s with ctx := ctx, balance := ctx.accountBalance + ctx.attachedDeposit, storageUsage := ctx.storageUsage, gas := {s.gas with g := s.gas.remaining}, stack := #[], frames := [] }
  let entry ← match enter p s mi with
    | .cont t => pure t
    | _ => throw "entry failed"
  let (rows,last,err) ← traceSteps p (p.funcs[0]!.code.size+1) 0 entry
  let final ← sync last
  match runCall pv86 bytes "main" ctx (p.funcs[0]!.code.size+1) true with
  | .done actual actualErr =>
    if actualErr != err || (stateJson actual).compress != (stateJson final).compress then
      throw "trace versus actual runCall mismatch"
  | .line e => throw s!"unexpected runCall line: {e}"
  let code ← (List.range p.funcs[0]!.code.size).mapM fun pc => do
    let op ← opJson p.funcs[0]!.code[pc]!
    pure (obj [("function",num 0),("pc",num pc),("instruction",op),
      ("charge",feeJson p.funcs[0]!.gas[pc]!)])
  pure (obj [("label",toJson label),("wasm_bytes",toJson (bytes.data.map UInt8.toNat)),
    ("method",toJson "main"),("prepaid",num prepaid),("code",arr code),
    ("prologue_gas",num p.funcs[0]!.prologueGas),("stack_charge",num p.funcs[0]!.stackCharge),
    ("entry_before",stateJson s),("entry_after",stateJson entry),("exec_rows",arr rows),
    ("final",stateJson final),("error",toJson err),
    ("actual_run_call_outcome",toJson (outcome pv86 bytes "main" ctx (p.funcs[0]!.code.size+1) true))])

end NearCompression

open Lean
def main (args : List String) : IO Unit := do
  if !args.isEmpty then
    let pairs ← match args with
      | ["--pairs",count] => match count.toNat? with
        | some n => if 0<n && n≤4095 then pure n else throw (IO.userError "pairs must be in1..4095")
        | none => throw (IO.userError "invalid pair count")
      | _ => throw (IO.userError "usage: PreparedCodeTableFixture.lean [--pairs N]")
    let c ← match NearCompression.makeCaseBytes s!"long-{2*pairs+1}"
        (NearCompression.preparedLongSliceBytes pairs) 1000000000000000 with
      | .ok c => pure c
      | .error e => throw (IO.userError e)
    IO.println (Lean.Json.mkObj [("schema",toJson "prepared-wasm-function-witness-v0"),
      ("air_implemented",toJson false),("cases",toJson [c])]).compress
    return
  let mut cases := []
  for (name,a,b) in [("wrap",127,1),("positive",12,23),("negative",64,127)] do
    match NearCompression.makeCaseBytes name (NearCompression.preparedSliceBytes (UInt8.ofNat a) (UInt8.ofNat b)) 1000000000000000 with
    | .ok c => cases := cases ++ [c]
    | .error e => throw (IO.userError e)
  for (name,prepaid) in [("exact-gas",88890835),("range-charge-exhaustion",88890834)] do
    match NearCompression.makeCaseBytes name (NearCompression.preparedSliceBytes 127 1) prepaid with
    | .ok c => cases := cases ++ [c]
    | .error e => throw (IO.userError e)
  for (name,pairs) in [("long-25",12),("long-193",96)] do
    match NearCompression.makeCaseBytes name (NearCompression.preparedLongSliceBytes pairs) 1000000000000000 with
    | .ok c => cases := cases ++ [c]
    | .error e => throw (IO.userError e)
  IO.println (Lean.Json.mkObj [("schema",toJson "prepared-wasm-function-witness-v0"),
    ("air_implemented",toJson false),("cases",toJson cases)]).compress
