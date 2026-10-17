import NearCompression.PreparedMemoryExec
import Lean
namespace NearCompression
open NearSpec NearSpecV3 NearSpecV3.Wasm Lean
private def valueJson : Val→Json
  | .i32 x=>toJson [0,x.toNat]
  | .i64 x=>toJson [1,x.toNat]
  | _=>toJson [2,0]
private def bytes : ByteArray := ⟨(#[0,97,115,109,1,0,0,0,
  1,4,1,96,0,0,3,2,1,0,5,3,1,0,2,7,8,1,4,109,97,105,110,0,0,
  10,24,1,22,0,65,16,65,34,65,32,65,40,41,0,0,55,0,0,46,0,0,59,0,0,11,
  11,70,1,0,65,0,11,64]++(Array.range 64).map (fun i=>UInt8.ofNat (129+37*i)))⟩
private def build : Except String Json := do
  let prepaid:=1000000000000000
  let ctx:CallCtx:={prepaidGas:=prepaid}
  let p←match prepare pv86 bytes true with | .ok p=>pure p | _=>throw "prepare failed"
  let mi←match resolve p "main" with | .ok n=>pure n | _=>throw "resolve failed"
  match link p with | .ok=>pure () | _=>throw "link failed"
  let (g,e):=payPer (Gas.init prepaid) C.contractLoadingBytes bytes.size
  if e.isSome then throw "loading bytes"
  let (g,e):=payBase g C.contractLoadingBase
  if e.isSome then throw "loading base"
  let loaded←instantiate pv86 p g
  let loaded:={loaded with ctx,gas:={loaded.gas with g:=loaded.gas.remaining},stack:=#[],frames:=[]}
  let mut s←match enter p loaded mi with | .cont s=>pure s | _=>throw "enter failed"
  for _ in [0:4] do
    s←match step pv86 p s with | .cont next=>pure next | _=>throw "actual const prologue failed"
  let mut rows:List Json:=[]
  for clock in [4:8] do
    let f:=s.frames.head!
    let pf:=p.funcs[f.fn]!
    let instruction:=pf.code[f.pc]!
    let (op,offset,write)←match instruction with
      | .load op _ offset=>pure (op,offset,false)
      | .store op _ offset=>pure (op,offset,true)
      | _=>throw "not memory instruction"
    let width:=if write then storeWidth op else (loadSpec op).1
    let address:=match s.stack[s.stack.size-(if write then 2 else 1)]! with
      | .i32 x=>x.toNat | _=>0
    let input:=match s.stack.back! with | .i32 x=>x.toNat | .i64 x=>x.toNat | _=>0
    let next←match step pv86 p s with | .cont n=>pure n | _=>throw "actual memory step failed"
    let result:=if write then 0 else match next.stack.back! with | .i32 x=>x.toNat | .i64 x=>x.toNat | _=>0
    let raw:=readLE (if write then next else s) (address+offset) width
    rows:=rows++[Json.mkObj [
      ("opcode",toJson op),("offset",toJson offset),("pc",toJson f.pc),("clock",toJson clock),
      ("pages",toJson s.pages.size),("stack",toJson (s.stack.map valueJson)),
      ("next_stack",toJson (next.stack.map valueJson)),("result",toJson result),
      ("address",toJson address),("value",toJson (if write then input else 0)),("raw",toJson raw),
      ("gas_before",toJson s.gas.g),("gas_after",toJson next.gas.g)]]
    s:=next
  let last←match step pv86 p s with | .fin n=>pure n | .cont n=>pure n | _=>throw "root end failed"
  let final←sync last
  match runCall pv86 bytes "main" ctx 64 true with
  | .done actual err=>
    if err.isSome || actual.pages != final.pages || actual.gas.burnt != final.gas.burnt || actual.stack.size != final.stack.size then
      throw "actual runCall mismatch"
  | _=>throw "actual runCall unmodeled"
  pure (Json.mkObj [("profile",toJson "memory-exec-sender-v1"),("wasm_bytes",toJson (bytes.data.map UInt8.toNat)),
    ("rows",toJson rows),("actual_run_call",toJson true),("final_prefix",toJson ((final.pages[0]!.data.take 64).map UInt8.toNat))])
end NearCompression

def main : IO Unit := do
  match NearCompression.build with
  | .ok j=>IO.println j.compress
  | .error e=>throw (IO.userError e)
