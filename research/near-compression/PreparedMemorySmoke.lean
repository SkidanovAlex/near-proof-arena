import NearCompression.PreparedMemoryLoad
import NearCompression.CachedWriteBytes
import NearCompression.SHA384Chain
namespace NearCompression
open NearSpec NearSpecV3 NearSpecV3.Wasm
private def hash384 (bs : Bytes) : ByteArray := ⟨(sha384ChainDigest bs).toArray⟩
private def ensure (ok : Bool) (label : String) : IO Unit := unless ok do throw (IO.userError label)
private def initial : St := {
  pages:=#[⟨(Array.range pageSize).map (fun i=>UInt8.ofNat (129+37*i))⟩,
    ⟨(Array.range pageSize).map (fun i=>UInt8.ofNat (146+37*i))⟩],
  globals:=#[],table:=#[],tableMax:=0,elems:=#[],datas:=#[],stackRem:=262144,gas:=Gas.init 1000000000 }
private def openings (s : St) (address width : Nat) : List PreparedMemoryReadOpening :=
  let pages:=subpageDirectory s.pages 4096 16
  (List.range width).map fun i=>
    {block:=memoryPageAt pages ((address+i)/4096),
     path:=buildPageOpening (blockTreeHash hash384 4096) pages 5 0 ((address+i)/4096)}
private def expected (address width : Nat) : Nat :=
  ((List.range width).reverse).foldl (fun acc i=>acc*256+(129+37*(address+i)+17*((address+i)/65536))%256) 0
private def bytesLE (width value : Nat) : ByteArray :=
  ⟨((List.range width).map (fun i=>UInt8.ofNat (value/256^i))).toArray⟩
private def frame : Frame := {(default : Frame) with pc:=3}
private def withFrame (s : St) : St := {s with frames:=[frame]}
private def top (s : St) : Nat × Nat := match s.stack.back? with
  | some (.i32 v)=>(32,v.toNat) | some (.i64 v)=>(64,v.toNat) | _=>(0,0)
private def readCase (address width : Nat) : IO Unit := do
  let s:=withFrame initial
  let d:=describeSubpageMemory hash384 s 4096 16 5
  let ws:=openings s address width
  ensure (preparedMemoryReadCheck hash384 d address width ws) s!"honest read {address}/{width}"
  ensure (preparedMemoryReadValue d address width ws == expected address width) "independent little endian"
  ensure (NearSpecV3.Wasm.readLE s address width == expected address width) "actual readLE"
  ensure (!preparedMemoryReadCheck hash384 d address width (ws.drop 1)) "missing opening"
  ensure (!preparedMemoryReadCheck hash384 d address width (ws++[default])) "extra opening"
  let bad:=ws.modify 0 (fun w=>{w with block:=w.block.set! (address%4096) 0})
  ensure (!preparedMemoryReadCheck hash384 d address width bad) "changed byte"
  let bad:=ws.modify 0 (fun w=>{w with path:=w.path.map (fun (dir,h)=>(!dir,h))})
  ensure (!preparedMemoryReadCheck hash384 d address width bad) "changed path direction"
  let bad:=ws.modify 0 (fun w=>{w with block:=w.block.extract 0 4095})
  ensure (!preparedMemoryReadCheck hash384 d address width bad) "short subpage"
  for (op,w,signed,bits) in [(0x28,4,false,32),(0x29,8,false,64),(0x2c,1,true,32),(0x2d,1,false,32),
      (0x2e,2,true,32),(0x2f,2,false,32),(0x30,1,true,64),(0x31,1,false,64),
      (0x32,2,true,64),(0x33,2,false,64),(0x34,4,true,64),(0x35,4,false,64)] do
    if w==width then
      let raw:=expected address width
      let result:=if signed && raw≥2^(width*8-1) then raw+2^bits-2^(width*8) else raw
      match exec pv86 default (pushV s (.i32 (UInt32.ofNat address))) frame default (.load op 0 0) with
      | .cont t=>
        ensure (top t == (bits,result)) s!"actual typed load {op} {address}"
        ensure (t.pages == s.pages && t.frames.head!.pc == 4) "load frame/memory"
      | _=>throw (IO.userError "load unexpectedly trapped")
  IO.println s!"read address={address} width={width} passed"
private def storeCase (address width op : Nat) : IO Unit := do
  let s:=withFrame initial
  let value:=18364758544493064720
  let data:=bytesLE width value
  let d:=describeSubpageMemory hash384 s 4096 16 5
  let ws:=cachedWriteBytesWitness hash384 s 4096 16 5 address data
  let checked:=preparedScalarStoreCheck hash384 d address width (value%256^width) ws
  let t:=match exec pv86 default (pushV (pushV s (.i32 (UInt32.ofNat address))) (.i64 (UInt64.ofNat value))) frame default (.store op 0 0) with
    | .cont t=>t | _=>s
  ensure (t.frames.head!.pc == 4) "actual store continuation"
  ensure (checked == some (describeSubpageMemory hash384 t 4096 16 5)) "checked store root"
  let flat:=s.pages[0]!.data++s.pages[1]!.data
  let expectedFlat:=(List.range width).foldl (fun a i=>a.set! (address+i) (UInt8.ofNat ((value/256^i)%256))) flat
  ensure (t.pages[0]!.data++t.pages[1]!.data == expectedFlat) "independent store pages"
  ensure ((preparedScalarStoreCheck hash384 d address width (value%256^width) (ws++ws)).isNone) "duplicate batches"
  ensure ((preparedScalarStoreCheck hash384 d (address+1) width (value%256^width) ws).isNone) "changed store address"
  let bad:=ws.reverse.map (fun w=>{w with writes:=w.writes.reverse})
  if width>1 then ensure ((preparedScalarStoreCheck hash384 d address width (value%256^width) bad).isNone) "reordered writes"
  IO.println s!"store address={address} width={width} passed"
end NearCompression
open NearCompression NearSpecV3.Wasm

def main : IO Unit := do
  ensure ((hash384 [97,98,99]).data.toList == [203, 0, 117, 63, 69, 163, 94, 139, 181, 160, 61, 105, 154, 198, 80, 7, 39, 44, 50, 171, 14, 222, 209, 99, 26, 139, 96, 90, 67, 255, 91, 237, 128, 134, 7, 43, 161, 231, 204, 35, 88, 186, 236, 161, 52, 200, 37, 167]) "SHA384 independent hashlib fixture"
  for width in [1,2,4,8] do
    for address in [0,4095,65535,131072-width] do
      readCase address width
  for (width,op) in [(1,0x3c),(2,0x3d),(4,0x3e),(8,0x37)] do
    storeCase 65535 width op
  let s:=withFrame initial
  for (address,offset) in [(131072,0),(131071,1),(4294967295,1)] do
    match exec pv86 default (pushV s (.i32 (UInt32.ofNat address))) frame default (.load 0x28 0 offset) with
    | .abort t err=>ensure (err==trapMem && t.pages==s.pages && t.stack.isEmpty) "load trap/postpop"
    | _=>throw (IO.userError "load address wrapped or bounds missed")
    match exec pv86 default (pushV (pushV s (.i32 (UInt32.ofNat address))) (.i64 7)) frame default (.store 0x37 0 offset) with
    | .abort t err=>ensure (err==trapMem && t.pages==s.pages && t.stack.isEmpty) "store trap/postpop"
    | _=>throw (IO.userError "store address wrapped or bounds missed")
  IO.println "memory regression PASS: 16 authenticated reads, 4 stores, 6 actual traps, malformed openings and ordering rejected"
