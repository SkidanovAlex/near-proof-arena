import ZkFormal.NearV3.Assembly.LinkImplicit
import ZkFormal.NearV3.Assembly.LinkRefine

/-!
# ZkFormal.NearV3.Assembly.LinkMain — the main instance on the native pre trie

The receipt core (`RcptLink.mainRun_of_records`, lane v3-rcpt-sound) is stated for an arbitrary
pre trie.  It is instantiated on the **full pre record tree** `Fpre r 0` (`wf`: `Fpre_wf`); this
module transfers the run to the native pre trie of `m.Valid`,
`partialTrie (x.store 0) k.slotB2.prevStateRoot (mainKeys rs bs)` (`main_transfer`): the pruned
trie simulates `Fpre r 0` on the main keys (`inst_pruned`), so `applyNewChunk_sim` gives the
same outcomes / refunds / gas / tokens and a post trie with the same root.  The pruned trie's
root is `prevStateRoot` (`m.Valid.preRoot`).
-/

namespace ZkFormal.NearV3.Assembly

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near

namespace LinkMain

open ZkFormal.NearV3 ZkFormal.NearV3.Link3 ZkFormal.NearV3.UpsRows LinkImplicit LinkRefine

section
variable {pub : List Fp} {tr : Trace Fp} {r : V3Records} {K : Nat} {r0 rK : List Nat}

/-- The pre record tree of an instance is well-formed. -/
theorem Fpre_wf (W : V3RecordsWf pub r) (L : TrieLink pub tr r K r0 rK) {τ : Nat} (hτ : τ ≤ K) :
    (Fpre r τ).wf = true := by
  obtain ⟨hh, htau⟩ := L.chain.head_mem τ hτ
  have hd := rootedDag3 W.nodes W.heads W.values L.parent L.vparent (vlen_le W.values)
    (recBytes_of W L) hh
  exact fullTree_wfR hd _ hd.root_inst

end

theorem mainKeys_fixed (rs : List NearSpec.Receipt) (bs : List Nat) :
    NearSpecV3.keyDelayedIdx ∈ NearSpecV3.mainKeys rs bs ∧ NearSpecV3.keyBwState ∈ NearSpecV3.mainKeys rs bs ∧
    NearSpecV3.keyBufferedIdx ∈ NearSpecV3.mainKeys rs bs ∧ NearSpecV3.keyYieldIdx ∈ NearSpecV3.mainKeys rs bs := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (by simp)))

theorem mainKeys_group {rs : List NearSpec.Receipt} {bs : List Nat} {x : Nat} (hx : x ∈ bs) :
    NearSpecV3.keyGroupsData x ∈ NearSpecV3.mainKeys rs bs :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hx)))

theorem mainKeys_acct {rs : List NearSpec.Receipt} {bs : List Nat} {r : NearSpec.Receipt} (hr : r ∈ rs) :
    NearSpec.accountKeyPath r.receiverId ∈ NearSpecV3.mainKeys rs bs :=
  List.mem_append_left _ (List.mem_append_right _
    (List.mem_map_of_mem (f := fun r : NearSpec.Receipt => NearSpec.accountKeyPath r.receiverId) hr))

theorem mainKeys_ak {rs : List NearSpec.Receipt} {bs : List Nat} {r : NearSpec.Receipt} (hr : r ∈ rs)
    (h1 : (r.predecessorId == NearSpec.AccountId.system) = true) (h2 : (r.signerId == r.receiverId) = true) :
    NearSpecV3.keyAccessKey r.receiverId r.signerPk ∈ NearSpecV3.mainKeys rs bs :=
  List.mem_append_right _ (List.mem_map_of_mem
    (f := fun r : NearSpec.Receipt => NearSpecV3.keyAccessKey r.receiverId r.signerPk)
    (List.mem_filter.mpr ⟨hr, by simp [h1, h2]⟩))

section Main
variable {cb : NearSpec.Bytes} {h : NearSpecV3.Hint} {p : NearSpecV3.Prep} {oh : Nat}
  {tr : Trace Fp} {r : V3Records}

/-- **The main application on the native pre trie** from the application on the pre record
tree: same outcomes / refunds / gas / tokens, same post root; the native pre trie has root
`prevStateRoot`. -/
theorem main_transfer (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    {k : NearSpecV3.WalkD0} (hw : NearSpecV3.walkD0 cb = .ok k)
    {x : ExtV3} (hxn : x.nodes = r.nodes) (hxv : x.values = r.values)
    {ctx : NearSpecV3.ApplyCtx} {rs : List NearSpec.Receipt} {bs : List Nat} {out : NearSpecV3.MainOut}
    (hcov : ∀ key ∈ NearSpecV3.mainKeys rs bs, (Fpre r 0).find key ≠ none)
    (hbs : ∃ v, (Fpre r 0).find NearSpecV3.keyBufferedIdx = some v ∧ NearSpecV3.bufferedShards v = .ok bs)
    (hrun : NearSpecV3.applyNewChunk NearSpecV3.prims ctx (Fpre r 0) rs = .ok out) :
    (NearSpecV3.partialTrie (x.store 0) k.slotB2.prevStateRoot (NearSpecV3.mainKeys rs bs)).hashOf =
      k.slotB2.prevStateRoot ∧
    ∃ out', NearSpecV3.applyNewChunk NearSpecV3.prims ctx
        (NearSpecV3.partialTrie (x.store 0) k.slotB2.prevStateRoot (NearSpecV3.mainKeys rs bs)) rs = .ok out' ∧
      out'.trie.hashOf = out.trie.hashOf ∧ out' = { out with trie := out'.trie } := by
  have L := trieLink_of hp hsz hH T W
  obtain ⟨hprev, -, -⟩ := prepD0_root_endpoints hp hw
  have hroot : toB (headAt r.heads 0).pre = k.slotB2.prevStateRoot := by
    rw [L.chain.pre0, toB_toNat, hprev]
  have hstore : NearSpecV3.partialTrie (x.store 0) k.slotB2.prevStateRoot (NearSpecV3.mainKeys rs bs) =
      NearSpecV3.partialTrie (storeOf (Rpost r.nodes r.values) (valsOf3 r.nodes r.values) 0)
        (toB (headAt r.heads 0).pre) (NearSpecV3.mainKeys rs bs) := by
    rw [hroot]
    simp only [ExtV3.store, ExtV3.rawStore, ExtV3.valuePosition, partialTrie_eraseDups, hxn, hxv]
    rfl
  have hlen : k.slotB2.prevStateRoot.length = 32 := by
    rw [← hroot, toB_len]; exact (W.heads.len _ (L.chain.head_mem 0 (Nat.zero_le _)).1).1
  refine ⟨(built_spec _ NearSpecV3.trieFuel _ _ hlen).1, ?_⟩
  rw [hstore]
  obtain ⟨hr, hwP, hfind⟩ := inst_pruned W L (Nat.zero_le _) _ hcov
  obtain ⟨hD, hB, hBI, hY⟩ := mainKeys_fixed rs bs
  obtain ⟨v0, hv0, hbs0⟩ := hbs
  obtain ⟨out', hout, href, heq⟩ := applyNewChunk_sim ⟨hr, hfind⟩ hwP (Fpre_wf W L (Nat.zero_le _))
    hD hB hBI hY
    (fun v hv sh hsh y hy => by
      rw [hv0] at hv; cases hv
      rw [hbs0] at hsh; cases hsh
      exact mainKeys_group hy)
    (fun r hr => mainKeys_acct hr) (fun r hr h1 h2 => mainKeys_ak hr h1 h2) hrun
  exact ⟨out', hout, NearSpec.PTrie.hashOf_refinedBy _ _ href, heq⟩

/-- **`GoodV3.executions` from the main application on the pre record tree.**  Inputs: the
receipt core's run on `Fpre r 0` (lane v3-rcpt-sound, instantiated at `pre := Fpre r 0`), its
post root `= x.post 0` (the ups post of instance `0`), the main-key coverage of `Fpre r 0` and the
buffered-index value, the header facts of that run, and the two open implicit hypotheses. -/
theorem executions_of (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    {k : NearSpecV3.WalkD0} (hw : NearSpecV3.walkD0 cb = .ok k)
    (Hpp : PostPreOff0 r) (Hdel : DelayedCovered p.hdr.K r)
    {x : ExtV3} (hxn : x.nodes = r.nodes) (hxv : x.values = r.values)
    (hxh : x.heads = xHeads (r.ups.map upsE))
    {block previous : NearSpecV3.Blk} (hmb : k.blks[k.b2i]? = some block)
    (hmp : k.blks[k.b2i + 1]? = some previous)
    {bs : List Nat} {out : NearSpecV3.MainOut}
    (hcov : ∀ key ∈ NearSpecV3.mainKeys x.applied bs, (Fpre r 0).find key ≠ none)
    (hbs : ∃ v, (Fpre r 0).find NearSpecV3.keyBufferedIdx = some v ∧ NearSpecV3.bufferedShards v = .ok bs)
    (hrun : NearSpecV3.applyNewChunk NearSpecV3.prims
      (NearSpecV3.blockCtx k.L k.H.shardId k.slotB2.gasLimit block previous.hdr.nextGasPrice)
      (Fpre r 0) x.applied = .ok out)
    (hpost : out.trie.hashOf = x.post 0)
    (hhdr : HeaderSemanticsV3 k h p ⟨block, previous, bs, Fpre r 0, out⟩ k.H.prevStateRoot) :
    ∃ m last, m.Valid k x ∧ ImplicitRunV3 k x 1 m.result.trie.hashOf k.implicitBlks last ∧
      HeaderSemanticsV3 k h p m last := by
  have L := trieLink_of hp hsz hH T W
  obtain ⟨hroot, out', hout, hhash, heq⟩ := main_transfer hp hsz hH T W hw hxn hxv hcov hbs hrun
  let m : MainExecutionV3 := ⟨block, previous, bs,
    NearSpecV3.partialTrie (x.store 0) k.slotB2.prevStateRoot (NearSpecV3.mainKeys x.applied bs), out'⟩
  -- the buffered read on the native store
  obtain ⟨v0, hv0, hbs0⟩ := hbs
  obtain ⟨hprev, -, -⟩ := prepD0_root_endpoints hp hw
  have hroot0 : toB (headAt r.heads 0).pre = k.slotB2.prevStateRoot := by
    rw [L.chain.pre0, toB_toNat, hprev]
  have hbuf : (NearSpecV3.partialTrie (x.store 0) k.slotB2.prevStateRoot [NearSpecV3.keyBufferedIdx]).find
      NearSpecV3.keyBufferedIdx = some v0 := by
    have hc : ∀ key ∈ [NearSpecV3.keyBufferedIdx], (Fpre r 0).find key ≠ none := by
      intro key hk; simp only [List.mem_singleton] at hk; subst hk; rw [hv0]; simp
    obtain ⟨-, -, hf⟩ := inst_pruned W L (Nat.zero_le _) _ hc
    have hs : NearSpecV3.partialTrie (x.store 0) k.slotB2.prevStateRoot [NearSpecV3.keyBufferedIdx] =
        NearSpecV3.partialTrie (storeOf (Rpost r.nodes r.values) (valsOf3 r.nodes r.values) 0)
          (toB (headAt r.heads 0).pre) [NearSpecV3.keyBufferedIdx] := by
      rw [hroot0]
      simp only [ExtV3.store, ExtV3.rawStore, ExtV3.valuePosition, partialTrie_eraseDups, hxn, hxv]
      rfl
    rw [hs, hf _ (by simp), hv0]
  have hV : m.Valid k x :=
    { block := hmb
      previous := hmp
      buffered := ⟨v0, hbuf, hbs0⟩
      pre := rfl
      preRoot := hroot
      run := hout
      postRoot := by show out'.trie.hashOf = x.post 0; rw [hhash, hpost] }
  have hpost' : m.result.trie.hashOf = x.post 0 := hV.postRoot
  refine ⟨m, k.H.prevStateRoot, hV,
    implicit_executions hp hsz hH T W hw hmb hmp Hpp Hdel hxn hxv hxh hpost', ?_⟩
  have e : out' = { out with trie := out'.trie } := heq
  exact
    { stateRoot := rfl
      outcomeRoot := by rw [show m.result = out' from rfl, e]; exact hhdr.outcomeRoot
      proposals := hhdr.proposals
      gasLimit := hhdr.gasLimit
      gasUsed := by rw [show m.result = out' from rfl, e]; exact hhdr.gasUsed
      tokensBurnt := by rw [show m.result = out' from rfl, e]; exact hhdr.tokensBurnt
      outgoingRoot := by rw [show m.result = out' from rfl, e]; exact hhdr.outgoingRoot
      congestion := hhdr.congestion
      bandwidthRequests := hhdr.bandwidthRequests
      split := hhdr.split
      txRoot := hhdr.txRoot
      body := by rw [show m.result = out' from rfl, e]; exact hhdr.body
      preparedBody := hhdr.preparedBody
      encoded := hhdr.encoded }

end Main

end LinkMain

end ZkFormal.NearV3.Assembly
