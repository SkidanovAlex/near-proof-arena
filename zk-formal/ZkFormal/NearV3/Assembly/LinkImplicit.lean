import ZkFormal.NearV3.Assembly.LinkVBytes
import ZkFormal.NearV3.Assembly.LinkPartial
import ZkFormal.NearV3.Assembly.StoreNormal
import ZkFormal.NearV3.Spec.StoreBuilt
import ZkFormal.NearV3.Rcpt.Candidates.PreparedRootEndpoints

/-!
# ZkFormal.NearV3.Assembly.LinkImplicit — the implicit transitions `τ = 1..K`

**The reconstruction of the heads.**  A head record of `headV3` carries the instance's pre root
`pre` and its *mid* root `post` (`MIDROOT`: the record tree with the account writes, before the
scheduler's `0x0f` upsert, `RootChain.mid`).  The native post root of instance `τ` is the root
*after* the upsert, i.e. `upsV3`'s `post` (`RootChain.link`/`postK`).  So the reconstruction
`x` takes its heads from the ups entries (`xHeads`): `x.post τ = toB (upsAt τ).post`
(`post_xHeads`).  The node / value records are the views' (`x.nodes = r.nodes`,
`x.values = r.values`), so `x.store τ` is the store of instance `τ`'s records with **pre** value
bytes (`valsOf3`).

**Pre vs post value records.**  `sched_step` runs on `fullTree Rpost Vpost (headAt τ).rid`,
whose written value records carry the acct post streams.  The records reachable from head `τ`
are records of instance `τ` (`RootedDagR`), so the two trees agree as soon as no value record of
instance `τ` changes (`tree_post_eq`).  For `τ ≥ 1` this is the hypothesis **`PostPreOff0`**:
a written value record of an instance `≠ 0` has post bytes = pre bytes.

**The implicit run** (`implicitRun_of`): by induction over `τ = 1..K`, the native pre trie of
`τ` (`partialTrie (x.store τ) root [keyDelayedIdx, keyBwState]`) is a pruning of the record tree
(`inst_pruned`, from `storeBuildR`), the record tree's `applyMissingChunk` is the scheduler step
of `sched_step` (after the delayed-index read, hypothesis **`DelayedCovered`**), and
`applyMissingChunk_refined` transfers it to the pruned trie; its root is the next head's pre
root, and at `τ = K` the claimed `postStateRoot`.
-/

namespace ZkFormal.NearV3.Assembly

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near

namespace LinkImplicit

open ZkFormal.NearV3 ZkFormal.NearV3.Link3 ZkFormal.NearV3.UpsRows

/-! ## Record trees with other value records -/

section Congr
variable {ns : List NodeRec3}

theorem nodeTree3_vals {vs₁ vs₂ : List ValRec3} (g : Nat → NearSpec.PTrie) (r : Rec3)
    (h : ∀ i ∈ r.vids, valOf vs₁ i = valOf vs₂ i) : nodeTree3 vs₁ g r = nodeTree3 vs₂ g r := by
  cases r with
  | leaf k v m =>
    cases v with
    | ref => rfl
    | val i => simp [nodeTree3, slot3, h i (by simp [Rec3.vids])]
  | ext => rfl
  | branch v kids m =>
    cases v with
    | none => rfl
    | some s =>
      cases s with
      | ref => rfl
      | val i => simp [nodeTree3, slot3, h i (by simp [Rec3.vids])]

/-- Two value-record lists that agree on the values the records of instance `τ` reference give
the same trees under instance `τ`'s records. -/
theorem treeOf3_vals {vs₁ vs₂ : List ValRec3} {τ root : Nat} {rk : Nat → Nat}
    (hd : RootedDagR ns vs₁ τ root rk)
    (hv : ∀ (n : Nat) (nr : NodeRec3), ns[n]? = some nr → nr.tau = τ → ∀ i ∈ nr.node.vids, valOf vs₁ i = valOf vs₂ i) :
    ∀ f n, InInst ns τ n → treeOf3 ns vs₁ f n = treeOf3 ns vs₂ f n := by
  intro f
  induction f with
  | zero => intro n _; rfl
  | succ f ih =>
    intro n hn
    obtain ⟨nr, hnr, ht⟩ := hn
    simp only [treeOf3, hnr]
    rw [nodeTree3_congrP vs₁ (g := treeOf3 ns vs₁ f) (g' := treeOf3 ns vs₂ f) nr.node
      (fun c hc => ih c (hd.child n nr hnr ht c hc).2)]
    exact nodeTree3_vals _ _ (hv n nr hnr ht)

theorem fullTree_vals {vs₁ vs₂ : List ValRec3} {τ root : Nat} {rk : Nat → Nat}
    (hd : RootedDagR ns vs₁ τ root rk)
    (hv : ∀ (n : Nat) (nr : NodeRec3), ns[n]? = some nr → nr.tau = τ → ∀ i ∈ nr.node.vids, valOf vs₁ i = valOf vs₂ i)
    {n : Nat} (hn : InInst ns τ n) : fullTree ns vs₁ n = fullTree ns vs₂ n :=
  treeOf3_vals hd hv _ n hn

end Congr

/-! ## Post value records vs pre value records -/

section Post
variable {vs : List NodeS3} {hs : List HeadE} {es : List ValE}

theorem valOf_post_at {pv : Nat → NearSpec.Bytes} {t : Nat}
    (h : ∀ e, es[t]? = some e → wrote vs e.vid = true → pv e.vid = toB e.bytes) :
    valOf (valsPost vs es pv) t = valOf (valsOf3 vs es) t := by
  unfold valOf valsPost valsOf3
  cases he : es[t]? with
  | none => simp [he]
  | some e =>
    by_cases hw : wrote vs e.vid = true
    · simp [he, hw, h e he hw]
    · simp [he, hw]

/-- **The post record tree of head `h` is its pre record tree** when no value record of
instance `h.tau` changes. -/
theorem tree_post_eq (hw : NodeWf3 vs) (hhw : HeadWf hs) (hvw : ValWf es) (hb : ParentBal vs hs)
    (hvb : VParentBal vs es) (hbytes : ∀ s ∈ vs, ∀ x ∈ s.v.ser false, x < 256)
    {h : HeadE} (hh : h ∈ hs) {pv : Nat → NearSpec.Bytes}
    (hpv : ∀ e ∈ es, valTau vs e.vid = h.tau → wrote vs e.vid = true → pv e.vid = toB e.bytes) :
    fullTree (recsOf (vpos (vid0 es)) vs) (valsPost vs es pv) h.rid =
      fullTree (recsOf (vpos (vid0 es)) vs) (valsOf3 vs es) h.rid := by
  have hd := rootedDag3 hw hhw hvw hb hvb (vlen_le hvw) hbytes hh
  refine (fullTree_vals hd ?_ hd.root_inst).symm
  intro n nr hnr ht i hi
  obtain ⟨vr, hvr, hvt⟩ := hd.vals n nr hnr ht i hi
  refine (valOf_post_at ?_).symm
  intro e he hwe
  have he' : (valsOf3 vs es)[i]? = some ⟨valTau vs e.vid, toB e.bytes⟩ := by
    simp [valsOf3, he]
  rw [he'] at hvr
  cases hvr
  exact hpv e (List.mem_of_getElem? he) hvt hwe

end Post

/-! ## The heads of the reconstruction -/

/-- The reconstruction's heads: one per ups entry, carrying its post root. -/
def xHeads (us : List UpsE) : List HeadE :=
  us.map fun u => { (default : HeadE) with tau := u.tau, post := u.post }

theorem post_xHeads {x : ExtV3} {us : List UpsE} (hx : x.heads = xHeads us) {τ : Nat}
    (hm : upsAt us τ ∈ us ∧ (upsAt us τ).tau = τ) : x.post τ = toB (upsAt us τ).post := by
  unfold ExtV3.post upsAt
  rw [hx, xHeads, List.find?_map]
  cases hf : us.find? (fun u => u.tau == τ) with
  | none =>
    exfalso
    have := List.find?_eq_none.mp hf _ hm.1
    simp [hm.2] at this
  | some y =>
    have hf' : us.find? ((fun h : HeadE => h.tau == τ) ∘
        (fun u : UpsE => { (default : HeadE) with tau := u.tau, post := u.post })) = some y := by
      rw [← hf]; rfl
    rw [hf']
    simp

/-! ## The native pre trie of an instance is a pruning of its record tree -/

section Pruned
variable {pub : List Fp} {tr : Trace Fp} {r : V3Records} {K : Nat} {r0 rK : List Nat}

/-- The pre record tree of instance `τ`. -/
noncomputable abbrev Fpre (r : V3Records) (τ : Nat) : NearSpec.PTrie :=
  fullTree (Rpost r.nodes r.values) (valsOf3 r.nodes r.values) (headAt r.heads τ).rid

theorem inst_pruned (W : V3RecordsWf pub r) (L : TrieLink pub tr r K r0 rK) {τ : Nat} (hτ : τ ≤ K)
    (keys : List (List Nat)) (hf : ∀ k ∈ keys, (Fpre r τ).find k ≠ none) :
    (NearSpecV3.partialTrie (storeOf (Rpost r.nodes r.values) (valsOf3 r.nodes r.values) τ)
        (toB (headAt r.heads τ).pre) keys).refinedBy (Fpre r τ) ∧
    (NearSpecV3.partialTrie (storeOf (Rpost r.nodes r.values) (valsOf3 r.nodes r.values) τ)
        (toB (headAt r.heads τ).pre) keys).wf = true ∧
    ∀ k ∈ keys, (NearSpecV3.partialTrie (storeOf (Rpost r.nodes r.values) (valsOf3 r.nodes r.values) τ)
        (toB (headAt r.heads τ).pre) keys).find k = (Fpre r τ).find k := by
  obtain ⟨hh, htau⟩ := L.chain.head_mem τ hτ
  have hd := rootedDag3 W.nodes W.heads W.values L.parent L.vparent (vlen_le W.values)
    (recBytes_of W L) hh
  have hp := pathsRevealed_of_rank hd (rk_lt W.nodes W.heads L.parent _ _) keys hf
  have hS := storeBuildR _ _ _ _ _ keys (storeHF_of W L hh) hd hp
  rw [rootDigest_of W L hh, htau] at hS
  have hlen : (toB (headAt r.heads τ).pre).length = 32 := by
    rw [toB_len]; exact (W.heads.len _ hh).1
  exact ⟨hS.1, (built_spec _ NearSpecV3.trieFuel _ keys hlen).2.1, hS.2.2⟩

end Pruned

/-! ## The implicit run -/

/-- **Written value records of instances `≠ 0` keep their bytes** (open: the `MEM` chain gives
`post = pre` for an acct no receipt writes, and a receipt's slot is a `FINAL` target of an
instance-`0` walk). -/
def PostPreOff0 (r : V3Records) : Prop :=
  ∀ e ∈ r.values, valTau r.nodes e.vid ≠ 0 → wrote r.nodes e.vid = true →
    toB (LinkVPost.pnOf r.accts e.vid) = toB e.bytes

/-- **The delayed-receipts index is determined in every implicit instance** (open: the qv
table's implicit reads). -/
def DelayedCovered (K : Nat) (r : V3Records) : Prop :=
  ∀ τ, 1 ≤ τ → τ ≤ K → (Fpre r τ).find NearSpecV3.keyDelayedIdx ≠ none

/-- The computed root before instance `τ`: the head's pre root, after `K` the claimed post root. -/
def rootAt (p : NearSpecV3.Prep) (r : V3Records) (τ : Nat) : NearSpec.Bytes :=
  if τ ≤ p.hdr.K then toB (headAt r.heads τ).pre else p.hdr.postStateRoot

section Run
variable {cb : NearSpec.Bytes} {h : NearSpecV3.Hint} {p : NearSpecV3.Prep} {oh : Nat}
  {tr : Trace Fp} {r : V3Records}

/-- The ups post root of every instance is the root of the next one. -/
theorem ups_post (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    {τ : Nat} (hτ : τ ≤ p.hdr.K) :
    toB (upsAt (r.ups.map upsE) τ).post = rootAt p r (τ + 1) := by
  have L := trieLink_of hp hsz hH T W
  unfold rootAt
  by_cases hl : τ < p.hdr.K
  · rw [if_pos (by omega), L.chain.link τ hl]
  · have he : τ = p.hdr.K := by omega
    subst he
    rw [if_neg (by omega), L.chain.postK, toB_toNat]

/-- **One implicit instance** `τ ∈ 1..K`. -/
theorem implicit_step (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    (Hpp : PostPreOff0 r) (Hdel : DelayedCovered p.hdr.K r)
    {x : ExtV3} (hxn : x.nodes = r.nodes) (hxv : x.values = r.values)
    (hxh : x.heads = xHeads (r.ups.map upsE))
    {τ : Nat} (h1 : 1 ≤ τ) (hτK : τ ≤ p.hdr.K) {ctx : NearSpecV3.ApplyCtx}
    (hτ : τ < p.sched.length) (hctx : NearSpecV3.schedPub ctx = some p.sched[τ]) :
    ∃ post : NearSpec.PTrie,
      NearSpecV3.applyMissingChunk NearSpecV3.prims ctx
        (NearSpecV3.partialTrie (x.store τ) (rootAt p r τ) [NearSpecV3.keyDelayedIdx, NearSpecV3.keyBwState])
        = .ok post ∧
      post.hashOf = x.post τ ∧ post.hashOf = rootAt p r (τ + 1) := by
  have L := trieLink_of hp hsz hH T W
  obtain ⟨hh, htau⟩ := L.chain.head_mem τ hτK
  -- the post record tree is the pre record tree
  have hFeq : fullTree (Rpost r.nodes r.values)
      (Vpost r.nodes r.values (fun i => toB (LinkVPost.pnOf r.accts i))) (headAt r.heads τ).rid =
      Fpre r τ := by
    apply tree_post_eq W.nodes W.heads W.values L.parent L.vparent (recBytes_of W L) hh
    intro e he hte hwe
    exact Hpp e he (by rw [hte, htau]; omega) hwe
  obtain ⟨Q, o, -, hsched, hnext, hlast⟩ := LinkVBytes.sched_step hp hsz hH T W hτ hτK hctx
  rw [hFeq] at hsched
  have hbw := LinkVBytes.codec_find hp hsz hH T W hτ hτK
  rw [hFeq, ← LinkVBytes.keyBwState_eq] at hbw
  have hdel := Hdel τ h1 hτK
  -- the record tree's missing chunk
  have hF : NearSpecV3.applyMissingChunk NearSpecV3.prims ctx (Fpre r τ) = .ok Q := by
    obtain ⟨dv, hdv⟩ := Option.ne_none_iff_exists'.mp hdel
    unfold NearSpecV3.applyMissingChunk
    simp [NearSpecV3.readKey, hdv, hsched, bind, Except.bind, pure, Except.pure]
  -- the pruned trie
  have hkeys : ∀ k ∈ [NearSpecV3.keyDelayedIdx, NearSpecV3.keyBwState], (Fpre r τ).find k ≠ none := by
    intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl
    · exact hdel
    · rw [hbw]; simp
  obtain ⟨hr, hw, hfind⟩ := inst_pruned W L hτK _ hkeys
  have hstore : NearSpecV3.partialTrie (x.store τ) (rootAt p r τ)
      [NearSpecV3.keyDelayedIdx, NearSpecV3.keyBwState] =
      NearSpecV3.partialTrie (storeOf (Rpost r.nodes r.values) (valsOf3 r.nodes r.values) τ)
        (toB (headAt r.heads τ).pre) [NearSpecV3.keyDelayedIdx, NearSpecV3.keyBwState] := by
    simp only [ExtV3.store, ExtV3.rawStore, ExtV3.valuePosition, rootAt, partialTrie_eraseDups,
      if_pos hτK, hxn, hxv]
    rfl
  rw [hstore]
  have hd' := hfind NearSpecV3.keyDelayedIdx (by simp)
  have hb' := hfind NearSpecV3.keyBwState (by simp)
  obtain ⟨P', hP', hPQ⟩ := LinkPartial.applyMissingChunk_refined hr hw
    (by rw [hd']; exact hdel) (by rw [hb', hbw]; simp) hF
  have hhash : P'.hashOf = Q.hashOf := NearSpec.PTrie.hashOf_refinedBy _ _ hPQ
  -- the ups post root is `Q`'s
  have hups : (upsAt (r.ups.map upsE) τ).post = Q.hashOf.map UInt8.toNat := by
    by_cases hl : τ < p.hdr.K
    · rw [← L.chain.link τ hl]; exact hnext hl
    · have he : τ = p.hdr.K := by omega
      rw [he, L.chain.postK]; exact hlast he
  have hQ : toB (upsAt (r.ups.map upsE) τ).post = Q.hashOf := by rw [hups, toB_toNat]
  refine ⟨P', hP', ?_, ?_⟩
  · rw [post_xHeads hxh (L.chain.ups_mem τ hτK), hQ, hhash]
  · rw [← ups_post hp hsz hH T W hτK, hQ, hhash]

/-- **The implicit run** `τ = 1..K`, from the root after the main instance to the claimed
`postStateRoot`. -/
theorem implicitRun_of (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    {k : NearSpecV3.WalkD0} (hw : NearSpecV3.walkD0 cb = .ok k) {m : MainExecutionV3}
    (hmb : k.blks[k.b2i]? = some m.block) (hmp : k.blks[k.b2i + 1]? = some m.previous)
    (Hpp : PostPreOff0 r) (Hdel : DelayedCovered p.hdr.K r)
    {x : ExtV3} (hxn : x.nodes = r.nodes) (hxv : x.values = r.values)
    (hxh : x.heads = xHeads (r.ups.map upsE)) :
    ImplicitRunV3 k x 1 (rootAt p r 1) k.implicitBlks p.hdr.postStateRoot := by
  obtain ⟨-, -, hKk⟩ := prepD0_root_endpoints hp hw
  have key : ∀ n τ, τ + n = p.hdr.K + 1 → 1 ≤ τ →
      ImplicitRunV3 k x τ (rootAt p r τ) (k.implicitBlks.drop (τ - 1)) p.hdr.postStateRoot := by
    intro n
    induction n with
    | zero =>
      intro τ hτ h1
      have hd : k.implicitBlks.drop (τ - 1) = [] := List.drop_eq_nil_of_le (by omega)
      have hr : rootAt p r τ = p.hdr.postStateRoot := by unfold rootAt; rw [if_neg (by omega)]
      rw [hd, hr]; exact .nil _ _
    | succ n ih =>
      intro τ hτ h1
      obtain ⟨j, rfl⟩ : ∃ j, τ = j + 1 := ⟨τ - 1, by omega⟩
      have hlt : j < k.implicitBlks.length := by omega
      simp only [Nat.add_sub_cancel]
      rw [List.drop_eq_getElem_cons hlt]
      have hci : (schedulerContexts k m)[j + 1]? = some (NearSpecV3.blockCtx k.L k.H.shardId
          k.slotB2.gasLimit k.implicitBlks[j] k.implicitBlks[j].hdr.nextGasPrice) := by
        simp [schedulerContexts, List.getElem?_eq_getElem hlt]
      obtain ⟨sp, hsp, hpub⟩ := prepD0_context_index_of hp hw hmb hmp (j + 1) _ hci
      obtain ⟨hτs, hsp'⟩ := List.getElem?_eq_some_iff.mp hsp
      obtain ⟨post, hrun, hpost, hnext⟩ := implicit_step hp hsz hH T W Hpp Hdel hxn hxv hxh
        (τ := j + 1) (by omega) (by omega) hτs (by rw [hsp']; exact hpub)
      refine .cons (j + 1) _ k.implicitBlks[j] _ post _ hrun hpost ?_
      rw [hnext]
      have := ih (j + 1 + 1) (by omega) (by omega)
      simpa using this
  simpa using key p.hdr.K 1 (by omega) (Nat.le_refl 1)

/-- The main instance's post root (`x.post 0`) is the root the implicit run starts from. -/
theorem post0_eq (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    {x : ExtV3} (hxh : x.heads = xHeads (r.ups.map upsE)) : x.post 0 = rootAt p r 1 := by
  have L := trieLink_of hp hsz hH T W
  rw [post_xHeads hxh (L.chain.ups_mem 0 (Nat.zero_le _)), ups_post hp hsz hH T W (Nat.zero_le _)]

/-- **The implicit part of `GoodV3.executions`** for any main execution whose post root is the
reconstruction's: the implicit run from `m`'s post root ends at `last = k.H.prevStateRoot`, so
`HeaderSemanticsV3.stateRoot` holds by `rfl`. -/
theorem implicit_executions (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    {k : NearSpecV3.WalkD0} (hw : NearSpecV3.walkD0 cb = .ok k) {m : MainExecutionV3}
    (hmb : k.blks[k.b2i]? = some m.block) (hmp : k.blks[k.b2i + 1]? = some m.previous)
    (Hpp : PostPreOff0 r) (Hdel : DelayedCovered p.hdr.K r)
    {x : ExtV3} (hxn : x.nodes = r.nodes) (hxv : x.values = r.values)
    (hxh : x.heads = xHeads (r.ups.map upsE)) (hpost : m.result.trie.hashOf = x.post 0) :
    ImplicitRunV3 k x 1 m.result.trie.hashOf k.implicitBlks k.H.prevStateRoot := by
  obtain ⟨-, hroot, -⟩ := prepD0_root_endpoints hp hw
  rw [hpost, post0_eq hp hsz hH T W hxh, ← hroot]
  exact implicitRun_of hp hsz hH T W hw hmb hmp Hpp Hdel hxn hxv hxh

end Run

end LinkImplicit

end ZkFormal.NearV3.Assembly
