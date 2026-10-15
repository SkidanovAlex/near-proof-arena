import ZkFormal.NearV3.Assembly.LinkClaim

/-!
# `ZkFormal.NearV3.D1.Link.ClaimFields` — the claim-level fields of the D1 link (L1 delta)

Lane `v3-d1-phase2`, item L1.  D0a's `ClaimFieldsV3` (`Assembly/LinkClaim`) without
`mainTxRoot`: `prepClaimD1` drops D0a's zero transaction root of the last chunk (D1 allows
transactions; `GoodD1Core.txRoot` ties the root to the hint's transactions instead).  The
generated link copies take `ClaimFieldsD1` where D0a takes `ClaimFieldsV3`.
-/

namespace ZkFormal.NearV3.D1.Link

open NearSpec NearSpecV3

/-- The claim-level `GoodD1Core` fields. -/
structure ClaimFieldsD1 (k : WalkD0) : Prop where
  ownCongestion : k.slotB2.congestion.delayedGas = 0 ∧
    k.slotB2.congestion.bufferedGas = 0 ∧ k.slotB2.congestion.receiptBytes = 0
  gasLimit : k.slotB2.gasLimit ≤ maxGasLimitD0
  distinctRequests : ∀ b ∈ k.blks, ∀ s ci, (s, ci) ∈ b.slots →
    (ci.bwRequests.map (·.toShard)).Nodup
  /-- A12 (`c.layout_wf`), checked by `prepClaimD1`. -/
  layoutWf : k.L.boundaries.length + 1 = k.L.shardIds.length

end ZkFormal.NearV3.D1.Link
