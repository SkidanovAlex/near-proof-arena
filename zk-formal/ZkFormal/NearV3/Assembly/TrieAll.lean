import ZkFormal.NearV3.Assembly.TrieShared

/-!
# ZkFormal.NearV3.Assembly.TrieAll — the trie side of `CompleteV3Stmt` from one native choice

`trie_all_accepted`: for every accepted witness there is ONE choice of native objects
(execution `m`, `steps`; account-write replay `writes`/`oldPost`; native ups instances `insts`;
ranked lookup walks `ws`) such that, with the use requests `q = useReq ws insts W` (any
field-bounded `W`) and head keys `q.edges`:

* the components of `node` (2), `head` (3), `val` (4), `walk` (5), `uniq` (6) exist with their
  native traffic, and of `ups` (7) **given the row cap** `R insts + 1 ≤ 2^22`;
* `UpsOrigin` of the native instances (`TrieA7.a7_perm_native` turns it into the A7 `RPL`/`RPLV`
  permutations);
* the record-level balances of `PARENT`, `VPARENT`, `ENT`, `DIGS`, `DUP`, `EDGE`, `BMAP`,
  `MIDROOT`, and the ups/head `ROOT` records (with `root_endpoints_accepted` for the public side).

With `balancedAt_trie_core`, `balancedAt_edge`, `balancedAt_bmap`, `balancedAt_midroot`,
`balancedAt_root` this gives `R.BalancedAt b` for these nine buses of any bundle carrying these
components.
-/

namespace ZkFormal.NearV3.Assembly.TrieAll

open NearSpec NearSpecV3 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3 ZkFormal.NearV3.Assembly
  Render Render.UpsGen UpsRows Rcpt.Candidates Rcpt.Candidates.NodePostUpdate ZkFormal.NearV3.Candidates
  Qv Qv.Candidates.CombinedWalkGen TrieUpsNative

theorem trie_all_accepted {cb wb : Bytes} (h : checkD0a B0 cb wb = .ok ()) (resolve : Resolve) (pub : List Fp) :
    ∃ (k : WalkD0) (w : StateWitness) (m : MainExecutionV3) (steps : List ImplicitStepV3) (last : Bytes)
      (writes : List (List Nat × Bytes)) (oldPost : PTrie) (insts : List UpsInst) (ws : List WalkR),
      walkD0 cb = .ok k ∧ decodeW wb = .ok w ∧ m.NativeValid k w ∧
      ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last ∧
      SizedAccountRun m.pre writes oldPost ∧
      (∃ Rw : TableRenderV3 pub T_WALK (by decide), Rw.tf = walkTraffic3 (rankWalks [] ws)) ∧
      TrieUpsOrigin.UpsOrigin (m.pre :: steps.map ImplicitStepV3.pre) insts ∧
      ∀ W : List ZkFormal.Near.Msg, W.length < Algebra.P →
        let q := useReq ws insts W
        let ns := TrieNative.nodes m steps oldPost writes q
        let hs := TrieNative.heads m steps oldPost writes q.edges
        let es := TrieNative.vals m steps
        let L := TrieUniqDup.uniqNative m steps
        let Js := upsRanked ws insts
        (∃ (hn : NodeOk ns) (hv : ValOk es) (Rh : TableRenderV3 pub T_HEAD (by decide))
          (Ru : TableRenderV3 pub T_UNIQ (by decide)),
          (∀ sel, ExtOf (nodeRenderV3 pub ns hn sel).tf (nodeTraffic3 ns)) ∧ Rh.tf = headTraffic hs ∧
          (∀ sel, ExtOf (valRenderV3 pub es hv sel).tf (valTraffic es)) ∧
          Ru.tf = uniqTraffic (uniqEntries L)) ∧
        (R insts + 1 ≤ 2 ^ 22 → ∃ hok : UpsRenderOk Js, ExtOf (upsRenderV3 pub Js hok).tf
          (upsTraffic (viewOf (upsTraceAligned Js) T_UPS (segsOf Js)))) ∧
        Link3.ParentBal ns hs ∧ Link3.VParentBal ns es ∧ Link3.EntBal ns es ∧
        Link3.DigsBal ns hs (uniqEntries L) ∧ Link3.DupBal (uniqEntries L) ns es ∧
        (∀ msg, cnt (nodeSends3 ns B_EDGE) msg + cnt (headSends hs B_EDGE) msg +
            cnt (walkSends3 (rankWalks [] ws) B_EDGE) msg + cnt (upsWalkMessages Js B_EDGE true) msg =
          cnt (nodeRecvs3 ns B_EDGE) msg + cnt (headRecvs hs B_EDGE) msg +
            cnt (walkRecvs3 (rankWalks [] ws) B_EDGE) msg + cnt (upsWalkMessages Js B_EDGE false) msg) ∧
        (∀ msg, cnt (nodeSends3 ns B_BMAP) msg + cnt (walkSends3 (rankWalks [] ws) B_BMAP) msg +
            cnt (upsWalkMessages Js B_BMAP true) msg =
          cnt (nodeRecvs3 ns B_BMAP) msg + cnt (walkRecvs3 (rankWalks [] ws) B_BMAP) msg +
            cnt (upsWalkMessages Js B_BMAP false) msg) ∧
        headSends hs B_MIDROOT = Js.map (fun I => [I.tau, I.rid] ++ I.mid) ∧
        (∀ I ∈ Js, I.mid.length = 32 ∧ I.post.length = 32) ∧
        headRecvs hs B_ROOT = nativeInputRoots 0 (m.pre :: steps.map ImplicitStepV3.pre) ∧
        Js.map (fun I => [I.tau + 1] ++ I.post) = nativeRootRecords 0 (m.result.trie :: steps.map ImplicitStepV3.post) := by
  obtain ⟨k, w, m, steps, last, -, -, hk, hw, hm, hv, -⟩ := TrieNative.accepted_native h
  obtain ⟨writes, oldPost, insts, v, ws, hr, hws, hRw, hpos, ho, hfam, horigin, hedges, hbmaps, hrest⟩ :=
    accepted_ups_walks hk hw h hm hv resolve pub
  refine ⟨k, w, m, steps, last, writes, oldPost, insts, ws, hk, hw, hm, hv, hr, hRw, horigin, ?_⟩
  intro W hW
  obtain ⟨he, hb, hups, hmid, hlens, hroot1, hroot2⟩ := hrest W hW
  obtain ⟨hn, hval, hh⟩ := TrieNative.accepted_ok hk hw h hm hv hr (useReq ws insts W) hedges hbmaps hW
    (useReq ws insts W).edges hedges
  refine ⟨⟨hn, hval, headRenderTrie pub _ hh,
      uniqRenderTrie pub _ (TrieUniqOk.uniqNative_ok hk hw h hm hv), nodeRenderV3_ext pub _ hn, rfl,
      valRenderV3_ext pub _ hval, rfl⟩,
    fun hcap => ⟨hups hcap, upsRenderV3_ext pub _ _⟩,
    TrieParent.parentBal_accepted hk hw h hm hv oldPost writes _ _,
    TrieVParent.vparentBal_native m steps oldPost writes _,
    TrieEnt.entBal_accepted hk hw h hm hv oldPost writes _,
    TrieUniqDup.digsBal_accepted hk hw h hm hv oldPost writes _ _,
    TrieUniqDup.dupBal_accepted hk hw h hm hv oldPost writes _,
    he, hb, hmid, hlens, hroot1, hroot2⟩

end ZkFormal.NearV3.Assembly.TrieAll
