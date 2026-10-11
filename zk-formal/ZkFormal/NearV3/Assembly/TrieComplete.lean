import ZkFormal.NearV3.Assembly.TrieUniqOk
import ZkFormal.NearV3.Rcpt.Candidates.AcceptedLookupPhysical

/-!
# ZkFormal.NearV3.Assembly.TrieComplete — the trie part of `CompleteV3Stmt` (state)

For every witness accepted at `B0`, from ONE choice of native objects (`accepted_native`):

* the `TableRenderV3` components of `node` (2), `head` (3), `val` (4), `uniq` (6) and `walk`
  (5) with their `tf` the honest native traffic (`trie_accepted`);
* the record-level balances `PARENT`, `VPARENT`, `ENT`, `DIGS`, `DUP` of those entries.

`balancedAt_trie_core`: any bundle carrying these components is balanced on the five
trie-only buses `PARENT`, `VPARENT`, `ENT`, `DIGS`, `DUP` (`RenderBundleV3.BalancedAt`).

Still open on the trie side (see the lane log): the buses touching `upsV3` (`EDGE`, `BMAP`,
`UPB`, `MIDROOT`, `MEMD`, `ROOT`), the shared buses (`BYTES`, `DIGEST`, `VSLOT`, `KEYNIB`,
`FINAL`, `VBYTES`, `SIZE`, `S0F`/`SPOST`/`SPLEN`), the `upsV3` and SHA components from native
data, and A7.
-/

namespace ZkFormal.NearV3.Assembly.TrieComplete

open NearSpec NearSpecV3 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3 ZkFormal.NearV3.Assembly
  Render Render.UpsGen Rcpt.Candidates Rcpt.Candidates.NodePostUpdate ZkFormal.NearV3.Candidates
  Qv Qv.Candidates.CombinedWalkGen

/-- The ranked native lookup walks of an accepted witness satisfy the walk table's honest-input
condition (rows `≤ 2^22`), for the SAME native execution `m`, `steps`. -/
theorem walk_accepted {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    (hk : walkD0 cb = .ok k) (hw : decodeW wb = .ok w) (h : checkD0a B0 cb wb = .ok ())
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes} (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    (resolve : Resolve) :
    ∃ v : MainValues, ∃ ws : List WalkR, v.Valid ∧ v.Reads m.pre m.pre m.pre ∧
      nativeQueryWalks ((m.pre, m.result.trie) :: steps.map (fun s => (s.pre, s.post)))
        (allLookupQueries (appliedReceipts k w) m.pre v (steps.map ImplicitStepV3.pre) resolve) = some ws ∧
      ZkFormal.NearV3.Candidates.Walk22Render.WalkOk (rankWalks [] ws) := by
  have h' : checkD0a 2000000 cb wb = .ok () := h
  have htrees := TrieUniqDup.forest_wf hm hv
  obtain ⟨v, hvalid, hreads, ws, hws⟩ := native_execution_all_lookups hm hv resolve
  have hbytes := checkD0a_preBytes hk hw h' hm hv
  have hgas : k.slotB2.gasLimit ≤ maxGasLimitD0 := by
    have hh := (relD0a_iff 2000000 cb wb).mpr h'
    simpa only [a1, hk, decide_eq_true_eq] using hh.2.1
  have hn := applyNewChunk_receipt_bound hm.run hgas
  have hreceipt : ∀ r ∈ appliedReceipts k w, r.wf = true := by
    have hd := hw
    unfold decodeW at hd
    obtain ⟨⟨raw, codes⟩, _, hd⟩ := ReexecV3D0.bind_ok' hd
    exact appliedReceipts_wf hd
  have hbuffer : (v.buffered.map List.length).getD 0 ≤ 2000000 := by
    have hread := hreads.2.1
    cases hb : v.buffered with
    | none => simp [hb]
    | some b =>
      rw [hb] at hread
      simpa only [hb, Option.map_some, Option.getD_some] using
        checkD0a_read_bound hk hw h' hm hv (t := m.pre) (by simp) hread
  have hg := main_group_count_bound v hvalid hbuffer
  have hp : (((m.pre, m.result.trie) :: steps.map (fun s => (s.pre, s.post))).map Prod.fst) =
      m.pre :: steps.map ImplicitStepV3.pre := by simp [List.map_map, Function.comp_def]
  have hlen : steps.length ≤ 31 := by
    have hc : checkD0 cb wb = .ok () := by
      have hh := ((relD0a_iff B0 cb wb).mpr h).1
      unfold RelD0 acceptsD0 at hh
      split at hh <;> simp_all
    obtain ⟨_, _, _, _, _, hcount⟩ := checkD0_native_steps hk hw hc
    have hs := hv.length
    simp only [List.length_zip] at hs
    omega
  have hok := native_all_walk_ok _ _ _ _ _ resolve ws hws
    (by rw [hp]; exact htrees) (by simpa only [hp] using hbytes)
    (by simp only [List.length_cons, List.length_map]; change steps.length + 1 ≤ 2013265921; omega)
    hreceipt hn hg (by simp only [List.length_map]; omega)
  exact ⟨v, ws, hvalid, hreads, hws, hok⟩

/-- **The trie components of every accepted witness.**  One choice of native objects; for every
choice of use requests `q` and head keys `keys` (field-bounded lengths) the node, head, value
and uniq components with native traffic and the five record-level trie balances; and for every
queue resolver the walk component. -/
theorem trie_accepted {cb wb : Bytes} (h : checkD0a B0 cb wb = .ok ()) (pub : List Fp) :
    ∃ (k : WalkD0) (w : StateWitness) (m : MainExecutionV3) (steps : List ImplicitStepV3)
      (last : Bytes) (writes : List (List Nat × Bytes)) (oldPost : PTrie),
      walkD0 cb = .ok k ∧ decodeW wb = .ok w ∧ m.NativeValid k w ∧
      ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last ∧
      SizedAccountRun m.pre writes oldPost ∧
      (∀ (q : UseRequests), q.edges.length < Algebra.P → q.bmaps.length < Algebra.P →
        q.windows.length < Algebra.P → ∀ (keys : List ZkFormal.Near.Msg), keys.length < Algebra.P →
        let ns := TrieNative.nodes m steps oldPost writes q
        let hs := TrieNative.heads m steps oldPost writes keys
        let es := TrieNative.vals m steps
        let L := TrieUniqDup.uniqNative m steps
        (∃ (Rn : TableRenderV3 pub T_NODE (by decide)) (Rh : TableRenderV3 pub T_HEAD (by decide))
          (Rv : TableRenderV3 pub T_VAL (by decide)) (Ru : TableRenderV3 pub T_UNIQ (by decide)),
          Rn.tf = nodeTraffic3 ns ∧ Rh.tf = headTraffic hs ∧ Rv.tf = valTraffic es ∧
          Ru.tf = uniqTraffic (uniqEntries L)) ∧
        Link3.ParentBal ns hs ∧ Link3.VParentBal ns es ∧ Link3.EntBal ns es ∧
        Link3.DigsBal ns hs (uniqEntries L) ∧ Link3.DupBal (uniqEntries L) ns es) ∧
      (∀ resolve : Resolve, ∃ v : MainValues, ∃ ws : List WalkR,
        nativeQueryWalks ((m.pre, m.result.trie) :: steps.map (fun s => (s.pre, s.post)))
          (allLookupQueries (appliedReceipts k w) m.pre v (steps.map ImplicitStepV3.pre) resolve) = some ws ∧
        ∃ Rw : TableRenderV3 pub T_WALK (by decide), Rw.tf = walkTraffic3 (rankWalks [] ws)) := by
  obtain ⟨k, w, m, steps, last, writes, oldPost, hk, hw, hm, hv, hr⟩ := TrieNative.accepted_native h
  refine ⟨k, w, m, steps, last, writes, oldPost, hk, hw, hm, hv, hr, ?_, ?_⟩
  · intro q he hb hu keys hkeys
    obtain ⟨hn, hval, hh⟩ := TrieNative.accepted_ok hk hw h hm hv hr q he hb hu keys hkeys
    refine ⟨⟨nodeRenderTrie pub _ hn, headRenderTrie pub _ hh, valRenderTrie pub _ hval,
      uniqRenderTrie pub _ (TrieUniqOk.uniqNative_ok hk hw h hm hv), rfl, rfl, rfl, rfl⟩,
      TrieParent.parentBal_accepted hk hw h hm hv oldPost writes q keys,
      TrieVParent.vparentBal_native m steps oldPost writes q,
      TrieEnt.entBal_accepted hk hw h hm hv oldPost writes q,
      TrieUniqDup.digsBal_accepted hk hw h hm hv oldPost writes q keys,
      TrieUniqDup.dupBal_accepted hk hw h hm hv oldPost writes q⟩
  · intro resolve
    obtain ⟨v, ws, -, -, hws, hok⟩ := walk_accepted hk hw h hm hv resolve
    exact ⟨v, ws, hws, walkRenderTrie pub _ hok, rfl⟩

end ZkFormal.NearV3.Assembly.TrieComplete

namespace ZkFormal.NearV3.Assembly.RenderBundleV3

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Render

variable {pub : List Fp} (R : RenderBundleV3 pub)

/-- **A bundle whose node, head, value and uniq components carry record lists with the five
trie balances is balanced on `PARENT`, `VPARENT`, `ENT`, `DIGS`, `DUP`.** -/
theorem balancedAt_trie_core (vs : List NodeS3) (hs : List HeadE) (es : List ValE) (L : List UEnt)
    (hn : (R ⟨T_NODE, by decide⟩).tf = nodeTraffic3 vs) (hh : (R ⟨T_HEAD, by decide⟩).tf = headTraffic hs)
    (hv : (R ⟨T_VAL, by decide⟩).tf = valTraffic es) (hu : (R ⟨T_UNIQ, by decide⟩).tf = uniqTraffic (uniqEntries L))
    (hP : Link3.ParentBal vs hs) (hVP : Link3.VParentBal vs es) (hE : Link3.EntBal vs es)
    (hD : Link3.DigsBal vs hs (uniqEntries L)) (hU : Link3.DupBal (uniqEntries L) vs es) :
    R.BalancedAt B_PARENT ∧ R.BalancedAt B_VPARENT ∧ R.BalancedAt B_ENT ∧
      R.BalancedAt B_DIGS ∧ R.BalancedAt B_DUP :=
  ⟨R.balancedAt_parent vs hs hn hh hP, R.balancedAt_vparent vs es hn hv hVP, R.balancedAt_ent vs es hn hv hE,
    R.balancedAt_digs vs hs L hn hh hu hD, R.balancedAt_dup vs es L hn hv hu hU⟩

end ZkFormal.NearV3.Assembly.RenderBundleV3
