import NearSpecV3.ChunkValidationD1a
import NearSpecV3.PrepD0
import ZkFormal.NearV3.D1.Public.PreparedD1Defs
import ZkFormal.NearV3.D1.UnreadIds

/-!
# `ZkFormal.NearV3.D1.PrepD1` — the native preparation of a D1a verifier (`prepD1`)

Lane `v3-d1-tables` (V3-D1-DESIGN §2.1; user decision P-D1-6: candidate side, not pinned;
P-D1-2: signatures verified natively).  Definitions only (verifier-model import rule): an
executable function of the claim and the hint, built from the trusted spec functions
(`pTxD1`, `Tx.valid` = `sizeOk ∧ Ed25519.verify`, `txCost`, `receiptIdFrom`,
`failedOutcome`/`OutD1.leaf`, `gasRefundReceipt`, `merklizeBorsh`, `outgoingReceiptsRoot`,
`encodedMerkleRoot`, `fwdGasOk`, `fwdLinks`, `pRefund`).

```
prepD1 cb h = prepClaimD1 cb  ≫  prepTxD1 (txs, okbits)  ≫  prepBodyD1 (newTxs, refunds)
```

* `prepClaimD1` is `prepClaim` (PrepD0.lean) without `c.no_tx_flags` and without the zero
  transaction root of the last chunk; it also returns `c.txValid` and `slotB2.txRoot`.
* `prepTxD1` replays `processTxs` steps 1–4 natively (duplicates, the validity flag,
  `Tx.valid`, `txCost`) and, from the hint's per-op `stage` and `ok`, steps 5–8's outcomes,
  receipts (local / forwarded), gas and tokens; the AIR (`txV3`) proves `stage` and `ok`
  against the state.  Then the local receipts (credit ops; outcome, refund and tokens are
  functions of the receipt and the context once the credit succeeds, which `txV3` proves).
* `prepBodyD1` checks everything else `checkD1` checks on these native values: T1, the
  validity-flag count, the two transaction roots, `sizeOk` of the new transactions,
  `e.forwarded` (gas part and size demands), `e.compute`, the header's gas, outgoing root,
  congestion, requests, split, and the Reed–Solomon body
  `u32 |newTxs| ‖ newTxs ‖ encodeReceipts (fwd ++ local refunds ++ refunds)`.

The hint (`HintD1`, on the wire `u32 n ‖ borshBytes txs ‖ borshBytes newTxs ‖ borshBytes bits ‖
borshBytes refunds`): `n` incoming receipts, the raw `transactions` / `new_transactions`
vectors, one byte `stage | ok << 2` per debit op, and the incoming receipts' refunds
(`encodeReceipts`).

Intended lemmas (phase 2, not stated as theorems here): `D1.PrepD1Lemmas`.
-/

namespace ZkFormal.NearV3.D1

open NearSpec NearSpec.TransferV1 NearSpecV3 ZkFormal.NearV3.D1.Public

/-! ## Hint -/

structure HintD1 where
  n : Nat
  txs : Bytes
  newTxs : Bytes
  bits : Bytes
  refunds : Bytes
  deriving Repr, Inhabited

def HintD1.encode (h : HintD1) : Bytes :=
  u32 h.n ++ borshBytes h.txs ++ borshBytes h.newTxs ++ borshBytes h.bits ++ borshBytes h.refunds

def decodeHintD1 (b : Bytes) : Except String HintD1 := do
  let (n, b) ← pU32 "hint n" b
  let (txs, b) ← pBytes "hint txs" b
  let (ntx, b) ← pBytes "hint newTxs" b
  let (bits, b) ← pBytes "hint bits" b
  let (rf, b) ← pBytes "hint refunds" b
  if !b.isEmpty then throw "invalid hint: trailing bytes"
  pure ⟨n, txs, ntx, bits, rf⟩

/-- A borsh `Vec<SignedTransaction>` in the D1 shape, no trailing bytes. -/
def decodeTxVec (b : Bytes) : Except String (List Tx) := do
  let (ts, b) ← pVec "transactions" pTxD1 b
  if !b.isEmpty then throw "invalid hint: trailing bytes after the transactions"
  pure ts

/-- `u32 |rs| ‖ refund receipts`, no trailing bytes. -/
def decodeRefunds (b : Bytes) : Except String (List Receipt) := do
  let (rs, b) ← pVec "refunds" pRefund b
  if !b.isEmpty then throw "invalid hint: trailing bytes after the refunds"
  pure rs

/-! ## Claim part -/

structure PrepCD1 where
  pc : PrepC
  txValid : Bytes
  txRoot : Bytes

/-- `prepClaim` without `c.no_tx_flags` and the zero transaction root (D1 allows
transactions); also returns the validity flags and the last chunk's `tx_root`. -/
def prepClaimD1 (cb : Bytes) : Except String PrepCD1 := do
  let c ← (decodeClaimE cb).mapError (fun e => s!"invalid claim: {e}")
  let H ← (decodeChunkInner c.chunkInner).mapError (fun e => s!"invalid claim: {e}")
  check (c.protocolVersion == 86) "out of domain (c.pv86)"
  check (c.epochs.length == 1) "out of domain (c.single_epoch): more than one epoch"
  let ep := c.epochs.headD ⟨[], 0, 0, [], []⟩
  check (ep.epochId == c.epochId && ep.protocolVersion == c.protocolVersion)
    "invalid: epoch table does not match epoch_id / protocol_version"
  let L ← decodeLayout ep.shardLayout
  check (1 ≤ L.numShards && L.numShards ≤ 64) "out of domain (c.layout)"
  check (rsGenesisParamsOk c.rsDataParts c.rsTotalParts) "invalid: Reed-Solomon parameters"
  check (c.blocks.length ≤ 32) "out of domain (c.segment)"
  check (c.epochStartAfter.length == c.blocks.length) "invalid: epoch_start_after length"
  check (c.epochStartAfter.all (· == 0)) "out of domain (c.single_epoch): epoch start"
  check (c.applyFacts.all fun f => f.validatorUpdate.isNone && f.splitGate.isNone)
    "out of domain (c.no_split_gate)"
  let blks ← c.blocks.mapM decodeBlk
  check (!blks.isEmpty) "invalid: empty chain segment"
  check (blks.all fun b => b.hdr.epochId == c.epochId) "out of domain (c.single_epoch)"
  let hashes := blks.map (·.hdr.hash)
  check (hashes.headD [] == H.prevBlockHash) "invalid: segment does not start at prev_block_hash"
  check ((blks.zip (hashes.drop 1)).all fun (b, h) => b.hdr.prevHash == h)
    "invalid: segment is not hash-linked"
  check (blks.all fun b => b.slots.length == L.numShards) "invalid: slot count"
  check (blks.all fun b => b.slots.all fun (_, ci) => decide (ci.bwRequests.map (·.toShard)).Nodup)
    "out of domain (c.bw_requests): a chunk's bandwidth requests repeat a to_shard"
  let idx ← match L.index H.shardId with
    | some i => pure i
    | none => throw "invalid: shard not in layout"
  let isNew := fun (b : Blk) => match b.slots[idx]? with
    | some (s, _) => s.heightIncluded == b.hdr.height
    | none => false
  check (blks.all fun b => b.slots.all fun (sl, _) => sl.heightIncluded ≤ b.hdr.height)
    "invalid: height_included above block height (block_congestion_info panics)"
  let b2i ← match blks.findIdx? isNew with
    | some i => pure i
    | none => throw "invalid: segment has no new chunk"
  let B2 ← match blks[b2i]? with | some b => pure b | none => throw "invalid: walk"
  check (!B2.isGenesis) "out of domain (c.not_genesis)"
  check c.genesisChunkExtra.isNone "invalid: genesis_chunk_extra for a non-genesis main block"
  let stop ← match (blks.drop (b2i + 1)).findIdx? isNew with
    | some j => pure (b2i + 1 + j)
    | none => throw "invalid: segment does not reach the last-but-one new chunk"
  check (stop + 1 == blks.length) "invalid: segment is not exactly the blocks the validator reads"
  let implicitBlks := (blks.take b2i).reverse
  let sourceBlks := (blks.drop b2i).take (stop - b2i)
  check (c.applyFacts.length == 1 + implicitBlks.length) "invalid: apply_facts length"
  let prevB2 ← match blks[b2i + 1]? with | some b => pure b | none => throw "invalid: walk"
  let slotB2 ← match B2.slots[idx]? with | some p => pure p.2 | none => throw "invalid: slot"
  check (slotB2.gasLimit ≤ maxGasLimitD0) "out of domain (c.gas_limit): chunk gas_limit above 10^15"
  let mut lists : List SrcList := []
  for S in sourceBlks do
    let mut srcs : List SrcList := []
    for (s, ci) in S.slots do
      if s.heightIncluded == S.hdr.height then
        srcs := srcs ++ [⟨chunkHash s.inner ci.encodedMerkleRoot, ci.shardId, ci.prevOutgoingReceiptsRoot⟩]
    let shuffled ← match shuffleWithSeed srcs S.hdr.prevHash with
      | some p => pure p
      | none => throw "invalid: shuffle fuel exhausted (probability < 2^-1024)"
    lists := lists ++ shuffled
  let own := slotB2.congestion
  check (own.delayedGas == 0 && own.bufferedGas == 0 && own.receiptBytes == 0)
    "out of domain (c.own_congestion_zero)"
  let ctxB2 := blockCtx L H.shardId slotB2.gasLimit B2 prevB2.hdr.nextGasPrice
  let ctxs := ctxB2 :: implicitBlks.map fun M => blockCtx L H.shardId slotB2.gasLimit M M.hdr.nextGasPrice
  let sched ← ctxs.mapM fun ctx => match schedPub ctx with
    | some p => pure p
    | none => throw "invalid: bandwidth scheduler aborted (StorageInconsistentState)"
  let allowed := L.shardIds.getD ((B2.hdr.height + idx) % L.numShards) H.shardId
  check (L.numShards == L.boundaries.length + 1)
    "out of domain (c.layout_wf): the shard layout does not have one boundary fewer than shard ids"
  pure ⟨{
    hdr := { K := implicitBlks.length, n := 0, own := H.shardId, ownIdx := idx,
             numShards := L.numShards, height := B2.hdr.height, gasPrice := prevB2.hdr.nextGasPrice,
             gasLimit := slotB2.gasLimit, prevStateRoot := slotB2.prevStateRoot,
             postStateRoot := H.prevStateRoot, outcomeRoot := H.prevOutcomeRoot,
             balanceBurnt := H.prevBalanceBurnt }
    lists, bnds := ownIntervals L H.shardId, sched, L, H, ctxB2,
    rsData := c.rsDataParts, rsTotal := c.rsTotalParts, allowed, ownCongestion := own },
    c.txValid, slotB2.txRoot⟩

/-! ## Transactions (steps 1–4 native, 5–8 from the hint's verdicts) -/

/-- `W_TX + 2·op` walk on the account key `[0] ‖ signer`, `W_TX + 2·op + 1` on the access key. -/
def acctKeyBytes (signer : Bytes) : Bytes := [0] ++ signer
def akKeyBytes (signer : Bytes) (pk : PublicKey) : Bytes := [2] ++ signer ++ [2] ++ pk.encode

/-- The native transaction state. -/
structure TxAcc where
  seen : List Bytes := []
  ops : List TxOp := []
  walks : List KeyWalk := []
  leaves : List Bytes := []
  locals : List Receipt := []
  fwd : List Receipt := []
  gas : Nat := 0
  tokens : Nat := 0
  bits : Bytes := []
  deriving Inhabited

/-- One transaction (`processTx` with the state-dependent verdicts from `bits`). -/
def prepTx (ctx : ApplyCtx) (st : TxAcc) (t : Tx) (flag : Bool) : Except String TxAcc := do
  let h := t.hash
  if st.seen.contains h then return st
  let st := { st with seen := h :: st.seen }
  let failLeaf := (failedOutcome t).leaf
  if !flag then return { st with leaves := st.leaves ++ [failLeaf] }
  let o := st.ops.length
  let valid := t.valid
  let cost := txCost t ctx.gasPrice
  let (bit, rest) ← match st.bits with
    | b :: r => pure (b.toNat, r)
    | [] => throw "invalid hint: missing transaction verdict bits"
  let stage := bit % 4
  let ok := bit / 4
  check (bit < 8 && stage ≤ 2) "invalid hint: verdict byte"
  let st := { st with bits := rest }
  let bound := min (ctx.height * TxParams.nonceRangeMultiplier) (Params.two64 - 1)
  let op : TxOp := { kind := 0, strict := if t.strict then 1 else 0, ok, tov := 0, stage,
                     cok := if cost.isSome then 1 else 0, valid := if valid then 1 else 0,
                     nonce := t.nonce, bound, amount := (cost.map (·.totalCost)).getD 0 }
  let cand := valid && cost.isSome
  check (cand || stage == 0) "invalid hint: a non-candidate transaction with a state read"
  check (ok == 0 || stage == 2) "invalid hint: success without an access key"
  let walks := if !cand then [] else
    [⟨W_TX + 2 * o, acctKeyBytes t.signerId⟩] ++
      (if stage ≥ 1 then [⟨W_TX + 2 * o + 1, akKeyBytes t.signerId t.pkKey⟩] else [])
  let st := { st with walks := st.walks ++ walks }
  match cost, ok with
  | some c, 1 =>
    let rid := receiptIdFrom h ctx.height 0
    let r : Receipt := { predecessorId := t.signerId, receiverId := t.receiverId, receiptId := rid,
                         signerId := t.signerId, signerPk := t.pkKey, gasPrice := c.receiptGasPrice,
                         deposit := t.deposit }
    let st := if t.receiverId == t.signerId then { st with locals := st.locals ++ [r] }
      else { st with fwd := st.fwd ++ [r] }
    if st.tokens + c.burntAmount ≥ Params.two128 then
      return { st with ops := st.ops ++ [{ op with tov := 1 }] }
    let gas := st.gas + c.gasBurnt
    check (gas < Params.two64) "invalid: chunk gas overflow (UnexpectedIntegerOverflow panics)"
    let out : OutD1 := { o := { id := h, receiptIds := [rid], gasBurnt := c.gasBurnt,
                                tokensBurnt := c.burntAmount, executorId := t.signerId },
                         status := .receipt rid }
    pure { st with gas, tokens := st.tokens + c.burntAmount, ops := st.ops ++ [op],
                   leaves := st.leaves ++ [out.leaf] }
  | _, _ => pure { st with ops := st.ops ++ [op], leaves := st.leaves ++ [failLeaf] }

def prepTxs (ctx : ApplyCtx) : TxAcc → List (Tx × Bool) → Except String TxAcc
  | st, [] => .ok st
  | st, (t, f) :: rest => do prepTxs ctx (← prepTx ctx st t f) rest

/-- A local receipt's outcome leaf, refunds and burnt tokens once its credit succeeds
(`TransferV1.applyReceipt`'s outcome, refund and token parts; `none` = out of domain). -/
def localApply (ctx : ApplyCtx) (r : Receipt) : Option (Bytes × List Receipt × Nat) :=
  let p := min r.gasPrice ctx.gasPrice
  let burnt := Params.G * p
  let surplus := Params.G * (r.gasPrice - p)
  if burnt ≥ Params.two128 || surplus ≥ Params.two128 then none else
  let refund : List Receipt := if surplus = 0 then [] else [gasRefundReceipt r ctx.height surplus]
  let o : OutD1 := { o := { id := r.receiptId, receiptIds := refund.map Receipt.receiptId,
                            gasBurnt := Params.G, tokensBurnt := burnt, executorId := r.receiverId },
                     status := .value }
  some (o.leaf, refund, burnt)

structure LocAcc where
  ops : List TxOp
  walks : List KeyWalk
  leaves : List Bytes
  refunds : List Receipt
  tokens : Nat

def prepLocals (ctx : ApplyCtx) : LocAcc → List Receipt → Except String LocAcc
  | st, [] => .ok st
  | st, r :: rs => do
    let some (leaf, rf, burnt) := localApply ctx r
      | throw "out of domain (r.success): receipt fails / overflows"
    check (st.tokens + burnt < Params.two128) "out of domain (r.success): receipt fails / overflows"
    let o := st.ops.length
    let op : TxOp := { kind := 1, strict := 0, ok := 0, tov := 0, stage := 1, cok := 1, valid := 1,
                       nonce := 0, bound := 0, amount := r.deposit }
    prepLocals ctx { ops := st.ops ++ [op], walks := st.walks ++ [⟨W_TX + 2 * o, acctKeyBytes r.receiverId⟩],
                     leaves := st.leaves ++ [leaf], refunds := st.refunds ++ rf,
                     tokens := st.tokens + burnt } rs

/-! ## Unread-key walks (plan §5, R-5 → (B), lane v3-d1-a7b) -/

/-- The walks of **every** `txKeys` entry, in order (`txKeys txs`: the signer account, then the
access key, of every transaction of the witness, duplicates included): walk ids `W_UNR + 2·j`
and `W_UNR + 2·j + 1` for transaction `j`. -/
def unreadWalks (txs : List Tx) : List KeyWalk :=
  txs.zipIdx.flatMap fun (t, j) =>
    [⟨W_UNR + 2 * j, acctKeyBytes t.signerId⟩, ⟨W_UNR + 2 * j + 1, akKeyBytes t.signerId t.pkKey⟩]

/-! ## `prepD1` -/

def prepD1 (cb : Bytes) (h : HintD1) : Except String PrepD1 := do
  let ⟨pc, txValid, txRoot⟩ ← prepClaimD1 cb
  let ctx := pc.ctxB2
  let txs ← decodeTxVec h.txs
  let newTxs ← decodeTxVec h.newTxs
  let refunds ← decodeRefunds h.refunds
  check (txs.length ≤ NT0) "out of domain (w.tx_count): more transactions than the bound"
  check (txValid.length == txs.length) "invalid: tx_valid length"
  check (merklizeBorsh (txs.map Tx.raw) == txRoot) "invalid: transaction root of the last chunk"
  check (newTxs.all Tx.sizeOk) "invalid: new transaction exceeds max_transaction_size"
  let st ← prepTxs ctx { bits := h.bits } (txs.zip (txValid.map (· != 0)))
  check st.bits.isEmpty "invalid hint: extra transaction verdict bits"
  check (st.locals.all fun r => AccountId.isNamed r.receiverId)
    "out of domain (r.shape): local receipt to a non-named account"
  let loc ← prepLocals ctx ⟨st.ops, st.walks, st.leaves, [], st.tokens⟩ st.locals
  let outgoing := st.fwd ++ loc.refunds ++ refunds
  check (outgoing.all fun r => (statusShards ctx).contains (ctx.layout.shardOf r.receiverId))
    "out of domain (e.forwarded): generated receipt buffered"
  check (fwdGasOk ctx outgoing) "out of domain (e.forwarded): generated receipt buffered"
  check ((fwdLinks ctx outgoing).all fun (_, d) => decide (d < fwdDemandMax))
    "out of domain (e.forwarded): forwarding demand above 2^24"
  let nr := st.locals.length + h.n
  check (nr == 0 || st.gas + (nr - 1) * Params.G < ctx.gasLimit)
    "out of domain (e.compute): receipt delayed by the compute limit"
  let H := pc.H
  check H.proposals.isEmpty "invalid: InvalidValidatorProposals"
  check (H.gasLimit == pc.hdr.gasLimit) "invalid: InvalidGasLimit"
  check (H.prevGasUsed == st.gas + nr * Params.G) "invalid: InvalidGasUsed"
  check (H.prevOutgoingReceiptsRoot == outgoingReceiptsRoot pc.L outgoing) "invalid: InvalidReceiptsProof"
  check (H.congestion == { pc.ownCongestion with allowedShard := pc.allowed }) "invalid: InvalidCongestionInfo"
  check H.bwRequests.isEmpty "invalid: InvalidBandwidthRequests"
  check H.proposedSplit.isNone "invalid: InvalidChunkHeaderShardSplit"
  check (H.txRoot == merklizeBorsh (newTxs.map Tx.raw)) "invalid: InvalidTxRoot"
  let body := u32 newTxs.length ++ concatAll (newTxs.map Tx.raw) ++ encodeReceipts outgoing
  match encodedMerkleRoot pc.rsData pc.rsTotal body with
  | none => throw "invalid: Reed-Solomon parameters"
  | some (emr, len) =>
    check (H.encodedMerkleRoot == emr) "invalid: InvalidChunkEncodedMerkleRoot"
    check (H.encodedLength == len) "invalid: InvalidChunkEncodedLength"
  let m0 := loc.leaves.length
  let o0 := 4 + (concatAll (newTxs.map Tx.raw)).length + 4 +
    (concatAll ((st.fwd ++ loc.refunds).map Receipt.encode)).length
  let base : Prep := { hdr := { pc.hdr with n := m0 + h.n }, lists := pc.lists, bnds := pc.bnds,
                       sched := pc.sched, body, fwd := fwdLinks ctx outgoing }
  pure { base, m0, t0 := loc.ops.length, o0, tok0 := loc.tokens, ops := loc.ops, walks := loc.walks,
         leaves := loc.leaves, rids := st.locals.map Receipt.receiptId, uwalks := unreadWalks txs }

/-- The witness bytes the AIR does not see (`sizeV3`'s `OVH`, `PH_WOVH`): the two transaction
vectors, which the extracted witness takes from the hint (`|borsh txs| + |borsh newTxs|`).
`sizeV3` then checks `8 MiB − OVH − Σ x_t ≥ 0` over the whole witness (`w.size`). -/
def txOverhead (h : HintD1) : Nat := h.txs.length + h.newTxs.length

/-- The verifier's public tape: `preparedBytesD1 (prepD1 cb h) (txOverhead h)`. -/
def preparedTapeD1 (cb hb : Bytes) : Except String Bytes := do
  let h ← decodeHintD1 hb
  let p ← prepD1 cb h
  pure (preparedBytesD1 p (txOverhead h))

end ZkFormal.NearV3.D1
