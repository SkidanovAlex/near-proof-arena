import ZkFormal.NearV3.Rcpt.Link.RunModel
import ZkFormal.NearV3.Rcpt.Link.ForwardSound
import ZkFormal.NearV3.Qv.Reads

/-!
# ZkFormal.NearV3.Rcpt.Link.NewChunk — `applyNewChunk` from its parts

The new-chunk application of D0 (`NearSpecV3.applyNewChunk`) is the composition of

1. the delayed-queue read on the pre trie, the scheduler step, the buffered-indices read and the
   group reads on the post-scheduler trie `mid`, and the yield read on the final trie
   (`Qv.MainValues`: `v.Valid ∧ v.Reads pre mid final`);
2. the receipt ledger (`RunModel`: `T (valsAt 0) = mid`, `TrieOk`, `RcptOk3` for every receipt);
3. the native compute guard (`prepBody`: `n = 0 ∨ (n − 1)·G < gas_limit`);
4. the forwarding of all generated refunds from the initial limits (`forwardRun`; from the
   forwarding split by `ForwardSound.forwardRun_of_split`).

**`applyNewChunk_of_parts`**: these give `applyNewChunk prims ctx pre rs = .ok (M.mainOut ctx)`,
where `M.mainOut ctx` is the run's final accumulator (trie `T (valsAt n)`, outcomes, refunds,
`n·G`, `tokAt n`) — determined by the records through `M`.
-/

namespace ZkFormal.NearV3.RcptLink

open NearSpec NearSpec.TransferV1 NearSpecV3 ZkFormal.NearV3.Assembly

/-- The main output a ledger model determines. -/
def RunModel.mainOut (M : RunModel) (ctx : ApplyCtx) : MainOut :=
  let a := M.accAt ctx M.rs.length
  ⟨a.trie, a.outcomes, a.refunds, a.gasBurnt, a.tokensBurnt⟩

theorem readKey_ok {t : PTrie} {key : List Nat} {what : String} {v : Option Bytes}
    (h : t.find key = some v) : readKey t key what = .ok v :=
  (Qv.readKey_iff t key what v).mpr h

theorem RunModel.accAt_zero_refunds (M : RunModel) (ctx : ApplyCtx) :
    (M.accAt ctx 0).refunds = [] := rfl

/-- **`applyNewChunk` from its parts.** -/
theorem applyNewChunk_of_parts {ctx : ApplyCtx} {pre mid : PTrie} {so : SchedOut}
    {v : Qv.MainValues} {M : RunModel} {ls' : List Limit}
    (hv : v.Valid) (hR : v.Reads pre mid (M.T (M.valsAt M.rs.length)))
    (hs : schedStep prims ctx pre = .ok (mid, so))
    (hT0 : M.T (M.valsAt 0) = mid) (hT : M.TrieOk) (hok : ∀ r, r < M.rs.length → M.RcptOk3 ctx r)
    (hc : M.rs.length = 0 ∨ (M.rs.length - 1) * Params.G < ctx.gasLimit)
    (hf : forwardRun ctx (limits0 ctx so.grant) (M.accAt ctx M.rs.length).refunds = .ok ls') :
    applyNewChunk prims ctx pre M.rs = .ok (M.mainOut ctx) := by
  obtain ⟨hdE, hbV, hyE⟩ := hv
  obtain ⟨hd, hb, hg, hy⟩ := hR
  have hled := M.ledgerAll_eq ctx hT hok
  have hacc0 : M.accAt ctx 0 = ⟨mid, [], [], 0, 0⟩ := by
    simp [RunModel.accAt, hT0, RunModel.tokAt]
  rw [hacc0] at hled
  have happ := applyReceipts_of_ledger ctx M.rs 0 _ _ (limits0 ctx so.grant) ls' hled
    (by rcases hc with h | h
        · exact Or.inl (List.eq_nil_of_length_eq_zero h)
        · exact Or.inr (by simpa using h))
    (by simpa using hf)
  have hgroups : forIn v.shards () (Qv.groupReadStep mid) = .ok () :=
    Qv.groupReads_loop mid v.shards hg
  unfold applyNewChunk
  simp only [readKey_ok hd, (Qv.queueEmpty_iff _ _).mpr hdE, hs, readKey_ok hb,
    (Qv.bufferedShards_iff _ _).mpr hbV, bind, Except.bind]
  split
  · rename_i e he; exact absurd (he.symm.trans hgroups) (by simp)
  split
  · rename_i e he; exact absurd (he.symm.trans happ) (by simp)
  rename_i p hp
  obtain rfl : p = (M.accAt ctx M.rs.length, ls') := by simpa using hp.symm.trans happ
  have hy' : (M.accAt ctx M.rs.length).trie.find keyYieldIdx = some v.yielded := hy
  simp only [readKey_ok hy', (Qv.queueEmpty_iff _ _).mpr hyE]
  rfl

end ZkFormal.NearV3.RcptLink
