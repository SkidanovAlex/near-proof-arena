import NearCompression.PreparedMemoryExec
namespace NearCompression
open NearSpec NearSpecV3 NearSpecV3.Wasm
private def base : St := {
  pages:=#[⟨(Array.range pageSize).map (fun i=>UInt8.ofNat (129+37*i))⟩,
    ⟨(Array.range pageSize).map (fun i=>UInt8.ofNat (146+37*i))⟩],
  globals:=#[],table:=#[],tableMax:=0,elems:=#[],datas:=#[],stackRem:=262144,gas:=Gas.init 1000000000}
private def frame : Frame := {(default:Frame) with pc:=3}
private def ensure (ok:Bool) (label:String) : IO Unit := unless ok do throw (IO.userError label)
private def caseJson (op address offset : Nat) : IO String := do
  let write:=op≥0x36
  let spec:=loadSpec op
  let width:=if write then storeWidth op else spec.1
  let is64:=if write then op==0x37 || op≥0x3c else spec.2.2
  let value:=if write then 18364758544493064720%2^(if is64 then 64 else 32) else 0
  let s:={base with frames:=[frame],stack:=#[.i64 77]}
  let addr:=.i32 (UInt32.ofNat address)
  let input:=if write then pushV (pushV s addr) (if is64 then .i64 (UInt64.ofNat value) else .i32 (UInt32.ofNat value)) else pushV s addr
  let instruction:=if write then .store op 0 offset else .load op 0 offset
  match exec pv86 default input frame default instruction with
  | .cont next=>
    ensure (next.frames.head!.pc==4) "actual PC"
    let raw:=readLE (if write then next else s) (address+offset) width
    let (tag,result):=if write then (0,0) else match next.stack.back? with
      | some (.i32 x)=>(0,x.toNat)
      | some (.i64 x)=>(1,x.toNat)
      | _=>(2,0)
    ensure (next.stack.size==(if write then 1 else 2) && (match next.stack[0]? with | some (Val.i64 x)=>x==77 | _=>false)) "actual mixed stack prefix"
    if !write then ensure (next.pages==s.pages) "load changed memory"
    else
      let flat:=s.pages[0]!.data++s.pages[1]!.data
      let expected:=(List.range width).foldl (fun a i=>a.set! (address+offset+i) (UInt8.ofNat (value/256^i))) flat
      ensure (next.pages[0]!.data++next.pages[1]!.data==expected) "store endian or unrelated bytes"
    return ("{"++s!"\"opcode\":{op},\"address\":{address},\"offset\":{offset},\"pages\":2,\"value\":{value},\"raw\":{raw},\"result\":{result},\"tag\":{tag},\"width\":{width}"++"}")
  | _=>throw (IO.userError "unexpected memory trap")
end NearCompression
open NearCompression

def main : IO Unit := do
  let mut cases : List String:=[]
  for op in [0x28,0x29,0x2c,0x2d,0x2e,0x2f,0x30,0x31,0x32,0x33,0x34,0x35,0x36,0x37,0x3a,0x3b,0x3c,0x3d,0x3e] do
    for (address,offset) in [(0,0),(4095,0),(65535,0),(65534,2)] do
      cases:=cases++[←caseJson op address offset]
  IO.println ("["++String.intercalate "," cases++"]")
