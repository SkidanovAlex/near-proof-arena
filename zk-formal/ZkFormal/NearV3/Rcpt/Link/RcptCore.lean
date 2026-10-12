import ZkFormal.NearV3.Rcpt.Link.RecModel
import ZkFormal.NearV3.Rcpt.Link.NewChunk
import ZkFormal.NearV3.Rcpt.Link.PrepFwd
import ZkFormal.NearV3.Assembly.Execution

/-!
# ZkFormal.NearV3.Rcpt.Link.RcptCore — the receipt core of `m.Valid.run`

**`mainRun_of_records`**: the main chunk's native application succeeds on the AIR's receipts,
`applyNewChunk prims ctx pre x.applied = .ok (mainOut)` with the output determined by the records
(`recModel ls as base T`), from

* `RecHyp pub ls as` — the receipt-side records (receipt view, `MEM` chain, account view, byte
  facts; `memHyp_of` gives the chain from `HoldsP`);
* `MainTrieLink` — the **interface to the trie / scheduler link** (lane v3-link): the scheduler
  step on the pre trie, the trie family `T` of the main instance after it (slot `k` holding
  `v k`), with `T (valsAt 0) = mid` and `TrieOk`;
* the queue reads (`Qv.MainValues`: valid values read at their runtime stages);
* the native `prepBody` facts (`PrepFwd`), the receipt count `h.n = |x.applied|`, the refund
  identity (the run's refunds are the hint body's), and the AIR's per-shard demand check against
  the scheduler grants.
-/

namespace ZkFormal.NearV3.RcptLink

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Link NearSpec NearSpec.TransferV1
  NearSpecV3 ZkFormal.NearV3.Assembly

theorem applied_eq (x : ExtV3) : x.applied = (rv x.receipts).map RcptV.toReceipt := by
  simp [ExtV3.applied, rv, flatR, List.map_flatMap]; rfl

/-- The trie / scheduler link's interface for the main instance. -/
structure MainTrieLink (ls : RcptV3Vs) (as : List AcctV) (base : Nat → NearSpec.Bytes)
    (T : (Nat → NearSpec.Bytes) → PTrie) (ctx : ApplyCtx) (pre mid : PTrie) (so : SchedOut) :
    Prop where
  sched : schedStep prims ctx pre = .ok (mid, so)
  init : T ((recModel ls as base T).valsAt 0) = mid
  trie : (recModel ls as base T).TrieOk

/-- **The receipt core of the main execution.** -/
theorem mainRun_of_records {pub : List Fp} {ls : RcptV3Vs} {as : List AcctV}
    {base : Nat → NearSpec.Bytes} {T : (Nat → NearSpec.Bytes) → PTrie} {ctx : ApplyCtx}
    {pre mid : PTrie} {so : SchedOut} {v : Qv.MainValues} {h : Hint} {p : Prep}
    {refunds : List Receipt}
    (H : RecHyp pub ls as) (hgp : ctx.gasPrice = leN' (pubBytes pub PH_GP 16))
    (L : MainTrieLink ls as base T ctx pre mid so)
    (hv : v.Valid)
    (hR : v.Reads pre mid (T ((recModel ls as base T).valsAt (flatR ls).length)))
    (F : PrepFwd ctx h p refunds) (hn : h.n = (flatR ls).length)
    (hrf : ((recModel ls as base T).accAt ctx (flatR ls).length).refunds = refunds)
    (hsz : ∀ s ∈ statusShards ctx, demand ctx refunds s ≤ so.grant ctx.own s) :
    applyNewChunk prims ctx pre ((rv ls).map RcptV.toReceipt) =
      .ok ((recModel ls as base T).mainOut ctx) := by
  have hlen := recModel_length (ls := ls) (as := as) (base := base) (T := T)
  obtain ⟨ls', hf⟩ := forwardRun_of_split F.status F.gas hsz
  have := applyNewChunk_of_parts (M := recModel ls as base T) hv
    (by rw [hlen]; exact hR) L.sched L.init L.trie
    (rcptOk_all H base T ctx hgp)
    (by rw [hlen, ← hn]; exact F.compute)
    (by rw [hlen, hrf]; exact hf)
  exact this

end ZkFormal.NearV3.RcptLink
