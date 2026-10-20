import NearCompression.CachedWriteBytes
import NearSpecV3.SHA512
open NearSpec NearSpecV3 NearSpecV3.Wasm NearCompression

def hash512 (bs : Bytes) : ByteArray := ⟨(NearSpecV3.sha512 bs).toArray⟩
def initial : St := {
  pages := #[zeroPage], globals := #[], table := #[], tableMax := 0,
  elems := #[], datas := #[], stackRem := 262144, gas := Gas.init 1000000000000000 }
def require (ok : Bool) (label : String) : IO Unit :=
  unless ok do throw (IO.userError label)

-- IO boundaries keep pure computations from moving between timing intervals.
@[noinline] def buildDescriptor (s : St) : IO BlockDescriptor :=
  pure (describeSubpageMemory hash512 s 4096 16 4)
@[noinline] def buildWitness (address : Nat) (data : ByteArray) : IO (List PageBatchWitness) :=
  pure (honestWriteBytesWitness hash512 initial 4096 16 4 address data)
@[noinline] def checkWitness (d : BlockDescriptor) (address : Nat) (data : ByteArray)
    (ws : List PageBatchWitness) : IO (Option BlockDescriptor) :=
  pure (checkBlockBatchedWriteBytes hash512 d address data ws)

def runCase (name : String) (address size expectedBatches : Nat) : IO Unit := do
  let block := 4096
  let data : ByteArray := ⟨Array.ofFn (fun i : Fin size => UInt8.ofNat (i.val % 251 + 1))⟩
  let start ← IO.monoMsNow
  let d ← buildDescriptor initial
  let afterInitial ← IO.monoMsNow
  let ws ← buildWitness address data
  require (ws.length == expectedBatches) "unexpected batch count"
  let afterWitness ← IO.monoMsNow
  let result ← checkWitness d address data ws
  require result.isSome "honest witness rejected"
  let afterCheck ← IO.monoMsNow
  let cachedWs := cachedWriteBytesWitness hash512 initial block 16 4 address data
  let fields := fun (xs : List PageBatchWitness) => xs.map (fun w => (w.index, w.page, w.path, w.writes))
  require (fields cachedWs == fields ws) "cached payload witness mismatch"
  require (checkBlockBatchedWriteBytes hash512 d address data cachedWs == result) "cached payload output mismatch"
  let actual := writeBytes initial address data
  require (result == some (describeSubpageMemory hash512 actual block 16 4)) "root mismatch"
  let direct := data.data.foldl (fun (acc : Nat × ByteArray) byte =>
    (acc.1 + 1, acc.2.set! acc.1 byte)) (address, zeroPage)
  require (actual.pages == #[direct.2]) "direct memory mismatch"
  let mut mutations := 0
  if let w :: tail := ws then
    require ((checkBlockBatchedWriteBytes hash512 d address data ({ w with page := w.page.set! 0 255 } :: tail)).isNone) "bad page accepted"
    require ((checkBlockBatch hash512 d w.index w.page w.path ((block, 7) :: w.writes)).isNone) "bad offset accepted"
    require ((checkBlockBatchedWriteBytes hash512 d address data tail).isNone) "missing batch accepted"
    require ((checkBlockBatchedWriteBytes hash512 { d with pages := 0 } address data ws).isNone) "unallocated block accepted"
    if let (direction, sibling) :: rest := w.path then
      let bad := { w with path := (direction, sibling.set! 0 (sibling[0]! ^^^ 1)) :: rest }
      require ((checkBlockBatchedWriteBytes hash512 d address data (bad :: tail)).isNone) "bad sibling accepted"
      mutations := mutations + 1
    mutations := mutations + 4
  if ws.length > 1 then
    require ((checkBlockBatchedWriteBytes hash512 d address data ws.reverse).isNone) "reordered batches accepted"
    mutations := mutations + 1
  IO.println s!"case={name} bytes={size} batches={ws.length} initial_ms={afterInitial-start} witness_ms={afterWitness-afterInitial} check_ms={afterCheck-afterWitness} mutations_rejected={mutations}"

def main : IO Unit := do
  IO.println s!"sha512_abc={(hash512 [97, 98, 99]).data.toList.map UInt8.toNat}"
  runCase "empty" 0 0 0
  runCase "same_block" 17 256 1
  runCase "cross_block" 4090 32 2
  runCase "dense" 0 4096 1
