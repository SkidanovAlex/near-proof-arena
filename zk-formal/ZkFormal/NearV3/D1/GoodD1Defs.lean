import ZkFormal.NearV3.Assembly.Good
import ZkFormal.NearV3.Assembly.LinkImplicit
import ZkFormal.NearV3.D1.Link.RecordsDefs

/-!
# `ZkFormal.NearV3.D1.GoodD1Defs` — the semantic interface between L1 and F1 (`GoodD1Core`)

Lane `v3-d1-phase2`, items L1/F1.  Definitions only.  The D1 analogue of `Assembly.Good`:

* `encodeSWD1` / `witnessOfD1`: the extracted D1 witness.  It is D0a's witness
  (`stateWitnessOfV3 k x`) with the hint's raw borsh vectors `h.txs` / `h.newTxs` in place of
  D0a's two empty vectors (`u32 0`); `stateWitnessD1Of` is the decoded form.
* `MainExecutionD1.Valid`: the main transition as `checkD1` runs it (pre trie over
  `mainKeys … ++ txKeys ts`, `applyNewChunkD1` with the claim's validity flags).
* `HeaderSemanticsD1`: `checkD1`'s comparisons with the endorsed header.
* **`GoodD1Core`**: every condition of `checkD1a` **except A7ᴰ¹** (`a7D1`), stated on the
  semantic views.  A7 is isolated: see `Link/Statements` (`A7D1Step`), plan §5 R-5.
* `XFromRecords r x`: the extracted views are the records' (what A7 needs about `x`).
-/

namespace ZkFormal.NearV3.D1

open NearSpec NearSpecV3 ZkFormal.NearV3.Assembly

/-- `ChunkStateWitness::V2` bytes with the raw transaction vectors (borsh `Vec`s). -/
def encodeSWD1 (sw : StateWitness) (txs newTxs : Bytes) : Bytes :=
  u8 1 ++ sw.epochId ++ u8 2 ++ sw.innerBytes ++ ReexecV3D0.zeros8 ++ ReexecV3D0.sig0 ++
  V3.encodeTransition sw.main ++ encList V3.encodeEntry sw.entries ++ sw.appliedReceiptsHash ++
  txs ++ encList V3.encodeTransition sw.implicit ++ newTxs

/-- **The extracted D1 witness file.** -/
def witnessOfD1 (k : WalkD0) (x : ExtV3) (h : HintD1) : Bytes :=
  borshBytes witnessTag ++ borshBytes (encodeSWD1 (stateWitnessOfV3 k x) h.txs h.newTxs) ++ u32 0

/-- The decoded D1 witness of `witnessOfD1` (with the decoded transaction lists). -/
def stateWitnessD1Of (k : WalkD0) (x : ExtV3) (ts nts : List Tx) : StateWitnessD1 :=
  let sw := stateWitnessOfV3 k x
  ⟨sw.epochId, sw.innerBytes, sw.inner, sw.main, sw.entries, sw.appliedReceiptsHash, ts, sw.implicit, nts⟩

structure MainExecutionD1 where
  block : Blk
  previous : Blk
  bufferedShards : List Nat
  pre : PTrie
  result : MainOutD1

def MainExecutionD1.ctx (k : WalkD0) (m : MainExecutionD1) : ApplyCtx :=
  blockCtx k.L k.H.shardId k.slotB2.gasLimit m.block m.previous.hdr.nextGasPrice

/-- The main transition as `checkD1` runs it. -/
structure MainExecutionD1.Valid (k : WalkD0) (x : ExtV3) (ts : List Tx) (m : MainExecutionD1) : Prop where
  block : k.blks[k.b2i]? = some m.block
  previous : k.blks[k.b2i + 1]? = some m.previous
  buffered : ∃ v, (partialTrie (x.store 0) k.slotB2.prevStateRoot [keyBufferedIdx]).find
    keyBufferedIdx = some v ∧ NearSpecV3.bufferedShards v = .ok m.bufferedShards
  pre : m.pre = partialTrie (x.store 0) k.slotB2.prevStateRoot
    (mainKeys x.applied m.bufferedShards ++ txKeys ts)
  preRoot : m.pre.hashOf = k.slotB2.prevStateRoot
  run : applyNewChunkD1 prims (m.ctx k) m.pre x.applied (ts.zip (k.c.txValid.map (· != 0))) = .ok m.result
  postRoot : m.result.trie.hashOf = x.post 0
  distinctIds : (m.result.localIds ++ x.applied.map Receipt.receiptId).Nodup

/-- `checkD1`'s comparisons with the endorsed header. -/
structure HeaderSemanticsD1 (k : WalkD0) (nts : List Tx) (m : MainExecutionD1) (last : Bytes) : Prop where
  stateRoot : k.H.prevStateRoot = last
  outcomeRoot : k.H.prevOutcomeRoot = outcomeRootD1 m.result.outcomes
  proposals : k.H.proposals.isEmpty = true
  gasLimit : k.H.gasLimit = k.slotB2.gasLimit
  gasUsed : k.H.prevGasUsed = m.result.gasUsed
  tokensBurnt : k.H.prevBalanceBurnt = m.result.tokensBurnt
  outgoingRoot : k.H.prevOutgoingReceiptsRoot = outgoingReceiptsRoot k.L m.result.outgoing
  congestion : k.H.congestion = { k.slotB2.congestion with
    allowedShard := k.L.shardIds.getD ((m.block.hdr.height + k.idx) % k.L.numShards) k.H.shardId }
  bandwidthRequests : k.H.bwRequests.isEmpty = true
  split : k.H.proposedSplit.isNone = true
  txRoot : k.H.txRoot = merklizeBorsh (nts.map Tx.raw)
  encoded : encodedMerkleRoot k.c.rsDataParts k.c.rsTotalParts
    (u32 nts.length ++ concatAll (nts.map Tx.raw) ++ encodeReceipts m.result.outgoing) =
      some (k.H.encodedMerkleRoot, k.H.encodedLength)

/-- **Every condition of `checkD1a` except A7ᴰ¹**, on the semantic views (`ts`, `nts`: the
hint's decoded transaction vectors). -/
structure GoodD1Core (cb : Bytes) (k : WalkD0) (h : HintD1) (p : Public.PrepD1) (x : ExtV3)
    (ts nts : List Tx) : Prop where
  walk : walkD0 cb = .ok k
  prepared : prepD1 cb h = .ok p
  txs : decodeTxVec h.txs = .ok ts
  newTxs : decodeTxVec h.newTxs = .ok nts
  shape : V3.D0Shape (stateWitnessOfV3 k x)
  witnessBytes : (encodeSWD1 (stateWitnessOfV3 k x) h.txs h.newTxs).length ≤ 8388608
  mainStoreBytes : ((x.store 0).map List.length).foldl (· + ·) 0 ≤ 3000000
  source : SourceSemanticsV3 k x
  receiptCount : h.n = x.applied.length
  txRoot : merklizeBorsh (ts.map Tx.raw) = k.slotB2.txRoot
  txValid : k.c.txValid.length = ts.length
  newSize : nts.all Tx.sizeOk = true
  ownCongestion : k.slotB2.congestion.delayedGas = 0 ∧
    k.slotB2.congestion.bufferedGas = 0 ∧ k.slotB2.congestion.receiptBytes = 0
  executions : ∃ m last, m.Valid k x ts ∧
    ImplicitRunV3 k x 1 m.result.trie.hashOf k.implicitBlks last ∧ HeaderSemanticsD1 k nts m last
  gasLimit : k.slotB2.gasLimit ≤ maxGasLimitD0
  canonicalScheduler : (reads0fD1 k (stateWitnessD1Of k x ts nts)).all (canonical0f k.L) = true
  distinctRequests : ∀ b ∈ k.blks, ∀ s ci, (s, ci) ∈ b.slots → (ci.bwRequests.map (·.toShard)).Nodup
  chachaWords : chachaWordsD1 cb (witnessOfD1 k x h) ≤ W0
  pathDepth : ∀ e ∈ usedProofsD1 k (stateWitnessD1Of k x ts nts), e.proof.path.length ≤ Dp0
  layoutWf : k.L.boundaries.length + 1 = k.L.shardIds.length
  txCount : ts.length ≤ NT0

/-- The extracted views are the records' (nodes, values, heads, receipt lists). -/
def XFromRecords (r : Link.D1Records) (x : ExtV3) : Prop :=
  x.nodes = r.base.nodes ∧ x.values = r.base.values ∧
    x.heads = LinkImplicit.xHeads (r.base.ups.map ZkFormal.NearV3.UpsRows.upsE) ∧ x.receipts = r.base.lists

end ZkFormal.NearV3.D1
