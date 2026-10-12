import ZkFormal.NearV3.Assembly.TrieAll

/-!
# ZkFormal.NearV3.Assembly.TrieVslotNative — `VSLOT` from the single native choice

`trie_all_accepted` now exports `KeysFinal k w m writes oldPost` (the replay writes exactly the
applied receipts' account keys and `oldPost` upserts to the main post trie) for the same
`writes`/`oldPost` as the node records.  **`vslot_native`**: with the receipt side's native
account views `nativeAccountViews m.pre oldPost (appliedReceipts k w) = some as` (for THAT
`oldPost`), every `VSLOT` message count of the acct sends equals the node receives
(`vslot_accepted` + `vslot_records`), i.e. the `hbal` premise of `balancedAt_vslot`.
-/

namespace ZkFormal.NearV3.Assembly.TrieShared

open NearSpec NearSpecV3 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3 ZkFormal.NearV3.Assembly
  Render Render.UpsGen Rcpt.Candidates Rcpt.Candidates.NodePostUpdate ZkFormal.NearV3.Candidates

theorem vslot_native {k : WalkD0} {w : StateWitness} {m : MainExecutionV3} (hm : m.NativeValid k w)
    {writes : List (List Nat × Bytes)} {oldPost : PTrie} (hr : SizedAccountRun m.pre writes oldPost)
    (hkf : KeysFinal k w m writes oldPost)
    {as : List AcctV} (has : nativeAccountViews m.pre oldPost (appliedReceipts k w) = some as)
    (steps : List ImplicitStepV3) (q : UseRequests) (msg : List Fp) :
    cnt (acctV3Sends as B_VSLOT) msg = cnt (nodeRecvs3 (TrieNative.nodes m steps oldPost writes q) B_VSLOT) msg := by
  obtain ⟨hkeys, state, hup⟩ := hkf
  exact vslot_records as _ (vslot_accepted hm hr hkeys hup has steps q) msg

end ZkFormal.NearV3.Assembly.TrieShared
