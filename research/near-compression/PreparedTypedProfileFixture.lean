import NearCompression.PreparedTypedValue
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
  | .i32 v => obj [("tag",num 0),("limbs",toJson [v.toNat % 65536,v.toNat / 65536,0,0])]
  | .i64 v => obj [("tag",num 1),("limbs",toJson ((List.range 4).map (fun i=>(v.toNat/65536^i)%65536)))]
  | .ref n => obj [("tag",num 2),("value",toJson n)]
private def stateJson (s : St) : Json := obj [
  ("stack",toJson (s.stack.map valJson)), ("gas",gasJson s.gas),
  ("frames",arr (s.frames.map fun f => obj [("fn",num f.fn),("pc",num f.pc),
    ("base",num f.base),("locals",toJson (f.locals.map valJson)),
    ("labels",arr (f.labels.map fun l => toJson [l.target,l.arity,l.height,if l.isLoop then 1 else 0]))])),
  ("stack_remaining",num s.stackRem),("balance",num s.balance),("storage_usage",num s.storageUsage)]
private def opJson : Instr → Except String Json
  | .i32Const v => .ok (obj [("opcode",num 0x41),("immediate",num v.toNat)])
  | .i64Const v => .ok (obj [("opcode",num 0x42),("immediate",num v.toNat)])
  | .num 0x7c => .ok (obj [("opcode",num 0x7c),("immediate",num 0)])
  | .num 0x50 => .ok (obj [("opcode",num 0x50),("immediate",num 0)])
  | .num 0x6a => .ok (obj [("opcode",num 0x6a),("immediate",num 0)])
  | .drop => .ok (obj [("opcode",num 0x1a),("immediate",num 0)])
  | .end_ => .ok (obj [("opcode",num 0x0b),("immediate",num 0)])
  | .block none => .ok (obj [("opcode",num 2),("immediate",num 0)])
  | .brIf 0 => .ok (obj [("opcode",num 13),("immediate",num 0)])
  | .localGet x => .ok (obj [("opcode",num 32),("immediate",num x)])
  | .localSet x => .ok (obj [("opcode",num 33),("immediate",num x)])
  | .localTee x => .ok (obj [("opcode",num 34),("immediate",num x)])
  | _ => .error "unsupported instruction in prepared-typed slice"
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
def preparedTypedProfileLegacySliceBytes (a b : UInt8) : ByteArray := ⟨#[0,97,115,109,1,0,0,0,
  1,4,1,96,0,0,3,2,1,0,7,8,1,4,109,97,105,110,0,0,
  10,10,1,8,0,65,a,65,b,106,26,11]⟩

private def shortULEB (n : Nat) : List UInt8 :=
  if n<128 then [UInt8.ofNat n] else [UInt8.ofNat (n%128+128),UInt8.ofNat (n/128)]
/-- Repeated real const/drop pairs with arbitrary section-size LEB for this fixture. -/
def preparedTypedProfileLegacyLongBytes (pairs : Nat) : ByteArray :=
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
      ("charge",feeJson p.funcs[0]!.gas[pc]!),
      ("end_target",num (if p.funcs[0]!.code[pc]! matches .block _ then p.funcs[0]!.endOf[pc]!+1 else 0))])
  pure (obj [("label",toJson label),("wasm_bytes",toJson (bytes.data.map UInt8.toNat)),
    ("method",toJson "main"),("prepaid",num prepaid),("code",arr code),
    ("local_count",num p.funcs[0]!.locals.size),("local_types",toJson (p.funcs[0]!.locals.map (fun t=>if t==VT.i64 then 1 else 0))),("prologue_gas",num p.funcs[0]!.prologueGas),("stack_charge",num p.funcs[0]!.stackCharge),
    ("entry_before",stateJson s),("entry_after",stateJson entry),("exec_rows",arr rows),
    ("final",stateJson final),("error",toJson err),
    ("actual_run_call_outcome",toJson (outcome pv86 bytes "main" ctx (p.funcs[0]!.code.size+1) true))])

/-- Mixed i32/i64 binary, zero-initialized locals, 64-bit wrap then eqz
feeding real br_if. Values remain typed throughout actual prepare and step. -/
def preparedTypedProfileBytes (value : List UInt8) : ByteArray :=
  let body : List UInt8 := [2,2,126,1,127,
    32,0,26,66] ++ value ++ [34,0,66,1,124,34,1,80,34,2,
    2,64,32,2,13,0,66,7,33,0,11,
    32,0,26,32,1,26,26,11]
  let payload := [1] ++ shortULEB body.length ++ body
  ⟨([0,97,115,109,1,0,0,0,1,4,1,96,0,0,3,2,1,0,7,8,1,4,109,97,105,110,0,0,10] ++
    shortULEB payload.length ++ payload).toArray⟩
end NearCompression
open Lean
def main : IO Unit := do
  let mut cases := []
  for (name,value) in [("typed-profile-wrap",[127]),("typed-profile-nonzero",[1]),
      ("typed-profile-modulus",[129,128,128,192,7]),
      ("typed-profile-high32",[128,128,128,128,16]),
      ("typed-profile-signbit",[128,128,128,128,128,128,128,128,128,127])] do
    let bytes:=NearCompression.preparedTypedProfileBytes (value.map UInt8.ofNat)
    let high : Nat:=1000000000000000
    let base ← match NearCompression.makeCaseBytes name bytes high with
      | .ok c=>pure c | .error e=>throw (IO.userError e)
    cases:=cases++[base]
    if name=="typed-profile-wrap" then
      let entry ← match base.getObjVal? "entry_after" >>= (·.getObjVal? "gas") >>= (·.getObjVal? "g") >>= Json.getNat? with
        | .ok n=>pure n | .error e=>throw (IO.userError e)
      let prologue ← match base.getObjVal? "prologue_gas" >>= Json.getNat? with
        | .ok n=>pure n | .error e=>throw (IO.userError e)
      for (label,budget) in [("typed-profile-first-exhaustion",high-entry+prologue-1),
          ("typed-profile-late-exhaustion",high-entry+prologue)] do
        match NearCompression.makeCaseBytes label bytes budget with
        | .ok c=>cases:=cases++[c]
        | .error e=>throw (IO.userError e)
  IO.println (Lean.Json.mkObj [("schema",toJson "prepared-wasm-typed-witness-v1"),
    ("cases",toJson cases)]).compress
