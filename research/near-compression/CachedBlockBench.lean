import NearCompression.CachedBlockSequence
import NearSpecV3.SHA512
open NearSpec NearSpecV3 NearSpecV3.Wasm NearCompression

def digest (bs : Bytes) : ByteArray := ⟨(NearSpecV3.sha512 bs).toArray⟩
def state (pages : Nat) : St := {
  pages := Array.replicate pages zeroPage, globals := #[], table := #[], tableMax := 0,
  elems := #[], datas := #[], stackRem := 262144, gas := Gas.init 1000000000000000 }
def ensure (ok : Bool) (label : String) : IO Unit :=
  unless ok do throw (IO.userError label)
@[noinline] def initReference (s : St) (depth : Nat) : IO BlockDescriptor :=
  pure (describeSubpageMemory digest s 4096 16 depth)
@[noinline] def initCache (s : St) (depth : Nat) : IO CachedPageTree :=
  pure (cachePageTree (blockTreeHash digest 4096) (buildSubpageTree s 4096 16 depth))
@[noinline] def reference (s : St) (depth : Nat) (plan : List BlockBatchPlan) : IO (List PageBatchWitness) :=
  pure (honestBlockSequence digest 4096 16 depth s plan)
@[noinline] def cached (tree : CachedPageTree) (depth : Nat) (plan : List BlockBatchPlan) : IO (List PageBatchWitness) :=
  pure (cachedBlockSequence digest 4096 depth tree plan)
def fields (ws : List PageBatchWitness) := ws.map (fun w => (w.index, w.page, w.path, w.writes))

@[noinline] def verify (d : BlockDescriptor) (ws : List PageBatchWitness) : IO (Option BlockDescriptor) :=
  pure (checkBlockBatches digest d ws)

def bench (name : String) (pages depth : Nat) (plan : List BlockBatchPlan) : IO Unit := do
  let s := state pages
  let t0 ← IO.monoMsNow
  let d ← initReference s depth
  let t1 ← IO.monoMsNow
  let tree ← initCache s depth
  let t2 ← IO.monoMsNow
  let a ← reference s depth plan
  let t3 ← IO.monoMsNow
  let b ← cached tree depth plan
  let t4 ← IO.monoMsNow
  ensure (fields a == fields b) "witness mismatch"
  ensure (cachedPageRoot tree == d.root) "initial root mismatch"
  let t5 ← IO.monoMsNow
  let result ← verify d b
  let t6 ← IO.monoMsNow
  let actual := executeByteRequests s (blockPlanRequests 4096 plan)
  ensure (result == some (describeSubpageMemory digest actual 4096 16 depth)) "post-write root mismatch"
  -- Separate direct memory update, bypassing executeByteRequests/writeByte.
  let direct := (blockPlanRequests 4096 plan).foldl (fun mem r =>
    mem.modify (r.1 / 65536) (fun page => page.set! (r.1 % 65536) r.2)) s.pages
  ensure (actual.pages == direct) "direct memory mismatch"
  IO.println s!"case={name} pages={pages} batches={b.length} reference_init_ms={t1-t0} cache_init_ms={t2-t1} reference_ms={t3-t2} cached_ms={t4-t3} check_ms={t6-t5}"

def main : IO Unit := do
  bench "one_batch" 1 4 [⟨0, [(0, 1)]⟩]
  bench "sixteen_blocks" 1 4 ((List.range 16).map (fun i => ⟨i, [(7, UInt8.ofNat (i+1))]⟩))
  bench "revisits" 1 4 ((List.range 16).map (fun i => ⟨i % 2, [(i % 8, UInt8.ofNat (i+1))]⟩))
  bench "larger_sparse" 4 6 ((List.range 8).map (fun i => ⟨i*7, [(23, UInt8.ofNat (i+1))]⟩))
