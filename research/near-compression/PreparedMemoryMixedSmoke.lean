import NearCompression.PreparedMemoryService
import NearCompression.CachedWriteBytes
import NearCompression.SHA384Chain
namespace NearCompression
open NearSpec NearSpecV3 NearSpecV3.Wasm
private def hash (bs : Bytes) : ByteArray := ⟨(sha384ChainDigest bs).toArray⟩
private def ensure (ok : Bool) (why : String) : IO Unit := unless ok do throw (IO.userError why)
private def initial : St := {
  pages:=#[zeroPage],globals:=#[],table:=#[],tableMax:=0,
  elems:=#[],datas:=#[],stackRem:=262144,gas:=Gas.init 0}
private def wr (s : St) (clock value : Nat) : PreparedMemoryRequest :=
  {clock,address:=17,width:=1,action:=.write value
    (cachedWriteBytesWitness hash s 4096 16 4 17 ⟨#[UInt8.ofNat value]⟩)}
private def rd (s : St) (clock value : Nat) : PreparedMemoryRequest :=
  let directory:=subpageDirectory s.pages 4096 16
  let opening:PreparedMemoryReadOpening:={
    block:=memoryPageAt directory 0
    path:=buildPageOpening (blockTreeHash hash 4096) directory 4 0 0}
  {clock,address:=17,width:=1,action:=.read value [opening]}
end NearCompression
open NearCompression NearSpecV3.Wasm

def main : IO Unit := do
  let s:=initial
  let s5:=writeLE s 17 1 5
  let s9:=writeLE s5 17 1 9
  let r0:=rd s 11 0
  let w5:=wr s 12 5
  let r5:=rd s5 13 5
  let w9:=wr s5 14 9
  let r9:=rd s9 15 9
  let root:=describeSubpageMemory hash s 4096 16 4
  let run:=preparedMemoryServiceCheck hash root 11
  ensure (run [] == some root) "empty sequence"
  ensure (run [r0,w5,r5,w9,r9] == some (describeSubpageMemory hash s9 4096 16 4)) "honest read/write interleaving"
  let bads := [
    ("stale initial read after write",[r0,w5,rd s 13 0,w9,r9]),
    ("stale intermediate read after overwrite",[r0,w5,r5,w9,rd s5 15 5]),
    ("future read before write",[rd s5 11 5,w5,r5,w9,r9]),
    ("wrong initial read value",[rd s 11 1,w5,r5,w9,r9]),
    ("wrong intermediate read value",[r0,w5,rd s5 13 9,w9,r9]),
    ("wrong final read value",[r0,w5,r5,w9,rd s9 15 5]),
    ("repeated clock",[r0,w5,{r5 with clock:=12},w9,r9]),
    ("skipped clock",[r0,w5,{r5 with clock:=14},w9,r9]),
    ("reordered events",[r0,r5,w5,w9,r9]),
    ("reordered events with repaired clocks",[r0,{r5 with clock:=12},{w5 with clock:=13},w9,r9]),
    ("stale write after read",[r0,w5,r5,wr s 14 9,r9])]
  for (name,requests) in bads do
    ensure ((run requests).isNone) name
  IO.println "mixed memory service PASS: empty + five-event read/write chain; eleven stale-root/value/clock/order forgeries rejected"
