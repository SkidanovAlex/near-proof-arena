import ZkFormal.NearV3.D1.PrepD1

/-!
# `ZkFormal.NearV3.D1.Prep.SpecDefs` — the intermediate values of a `prepD1` run (P2)

Lane `v3-d1-phase2`, item P2.  Definitions only.  `PrepD1Run` holds the values `prepD1` binds
on its way (claim part, decoded vectors, transaction and local-receipt runs); `PrepD1Run.Ok`
lists every check `prepD1` passes, and `PrepD1Run.prep` is its result.  `Prep.Spec.prepD1_spec`
proves `prepD1 cb h = .ok p → ∃ w, w.Ok cb h ∧ p = w.prep h`: the decomposition L1, F1 and R2
read `prepD1` through.
-/

namespace ZkFormal.NearV3.D1

open NearSpec NearSpec.TransferV1 NearSpecV3 ZkFormal.NearV3.D1.Public

/-- The values a successful `prepD1` binds. -/
structure PrepD1Run where
  pc : PrepC
  txValid : Bytes
  txRoot : Bytes
  txs : List Tx
  newTxs : List Tx
  refunds : List Receipt
  st : TxAcc
  loc : LocAcc

namespace PrepD1Run

variable (w : PrepD1Run)

/-- The outgoing receipts: forwarded transaction receipts, local refunds, incoming refunds. -/
def outgoing : List Receipt := w.st.fwd ++ w.loc.refunds ++ w.refunds

/-- The receipts the chunk applies: the local ones, then the `n` incoming ones. -/
def nr (n : Nat) : Nat := w.st.locals.length + n

/-- The Reed–Solomon body. -/
def body : Bytes := u32 w.newTxs.length ++ concatAll (w.newTxs.map Tx.raw) ++ encodeReceipts w.outgoing

/-- The body offset of the incoming refunds. -/
def o0 : Nat := 4 + (concatAll (w.newTxs.map Tx.raw)).length + 4 +
  (concatAll ((w.st.fwd ++ w.loc.refunds).map Receipt.encode)).length

/-- `prepD1`'s result. -/
def prep (h : HintD1) : PrepD1 :=
  { base := { hdr := { w.pc.hdr with n := w.loc.leaves.length + h.n }, lists := w.pc.lists,
              bnds := w.pc.bnds, sched := w.pc.sched, body := w.body,
              fwd := fwdLinks w.pc.ctxB2 w.outgoing },
    m0 := w.loc.leaves.length, t0 := w.loc.ops.length, o0 := w.o0, tok0 := w.loc.tokens,
    ops := w.loc.ops, walks := w.loc.walks, leaves := w.loc.leaves,
    rids := w.st.locals.map Receipt.receiptId, uwalks := unreadWalks w.txs }

/-- Every check of `prepD1` on these values. -/
structure Ok (cb : Bytes) (h : HintD1) : Prop where
  claim : prepClaimD1 cb = .ok ⟨w.pc, w.txValid, w.txRoot⟩
  txs : decodeTxVec h.txs = .ok w.txs
  newTxs : decodeTxVec h.newTxs = .ok w.newTxs
  refunds : decodeRefunds h.refunds = .ok w.refunds
  nt0 : w.txs.length ≤ NT0
  txValidLen : w.txValid.length = w.txs.length
  txRootEq : merklizeBorsh (w.txs.map Tx.raw) = w.txRoot
  newSize : w.newTxs.all Tx.sizeOk = true
  run : prepTxs w.pc.ctxB2 { bits := h.bits } (w.txs.zip (w.txValid.map (· != 0))) = .ok w.st
  bits : w.st.bits = []
  named : (w.st.locals.all fun r => AccountId.isNamed r.receiverId) = true
  locals : prepLocals w.pc.ctxB2 ⟨w.st.ops, w.st.walks, w.st.leaves, [], w.st.tokens⟩ w.st.locals = .ok w.loc
  shards : (w.outgoing.all fun r =>
    (statusShards w.pc.ctxB2).contains (w.pc.ctxB2.layout.shardOf r.receiverId)) = true
  fwdGas : fwdGasOk w.pc.ctxB2 w.outgoing = true
  fwdDemand : ((fwdLinks w.pc.ctxB2 w.outgoing).all fun (_, d) => decide (d < fwdDemandMax)) = true
  compute : w.nr h.n = 0 ∨ w.st.gas + (w.nr h.n - 1) * Params.G < w.pc.ctxB2.gasLimit
  proposals : w.pc.H.proposals.isEmpty = true
  gasLimit : w.pc.H.gasLimit = w.pc.hdr.gasLimit
  gasUsed : w.pc.H.prevGasUsed = w.st.gas + w.nr h.n * Params.G
  outRoot : w.pc.H.prevOutgoingReceiptsRoot = outgoingReceiptsRoot w.pc.L w.outgoing
  congestion : (w.pc.H.congestion == { w.pc.ownCongestion with allowedShard := w.pc.allowed }) = true
  bw : w.pc.H.bwRequests.isEmpty = true
  split : w.pc.H.proposedSplit.isNone = true
  newTxRoot : w.pc.H.txRoot = merklizeBorsh (w.newTxs.map Tx.raw)
  rs : encodedMerkleRoot w.pc.rsData w.pc.rsTotal w.body = some (w.pc.H.encodedMerkleRoot, w.pc.H.encodedLength)

end PrepD1Run

end ZkFormal.NearV3.D1
