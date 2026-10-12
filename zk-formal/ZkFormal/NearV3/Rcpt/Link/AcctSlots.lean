import ZkFormal.NearV3.Rcpt.Link.MemOf

/-!
# ZkFormal.NearV3.Rcpt.Link.AcctSlots — the account slots are distinct (`VSLOT`)

`acctV3` sends `VSLOT [a.k]` per record; node records receive `VSLOT [i]` for their written value
slot `i` (`LinkShaKinds.vslot_bal`).  A node record has one value slot and no two node records
reveal the same value id (`Link3.val_unique`), value ids are positions `< 2^22`, so the node
receives are pairwise distinct as `Fp` messages; by the balance so are the acct sends.

* **`acct_k_nodup`** — `(r.accts.map (·.k)).Nodup` (the `hknd` premise of `memHyp_of`);
* **`memHyp_of'`** — `MemHyp (rv r.lists) r.accts` from `HoldsP`, traffic and views alone.
-/

namespace ZkFormal.NearV3.RcptLink

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.NearV3.Assembly

theorem nodup_of_count_le {α : Type} [BEq α] [LawfulBEq α] :
    ∀ (l : List α), (∀ a, l.count a ≤ 1) → l.Nodup
  | [], _ => List.nodup_nil
  | x :: l, h => by
    refine List.nodup_cons.mpr ⟨fun hx => ?_, nodup_of_count_le l (fun a => ?_)⟩
    · have := h x
      rw [List.count_cons_self] at this
      have := List.count_pos_iff.mpr hx
      omega
    · have := h a
      rw [List.count_cons] at this
      omega

theorem count_le_of_nodup {α : Type} [BEq α] [LawfulBEq α] {l : List α} (h : l.Nodup) (a : α) :
    l.count a ≤ 1 := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.nodup_cons] at h
    rw [List.count_cons]
    by_cases hx : x = a
    · subst hx
      rw [List.count_eq_zero.mpr h.1]; simp
    · have : (x == a) = false := by simpa using hx
      simp only [this, Bool.false_eq_true, ↓reduceIte]; have := ih h.2; omega

theorem nodup_of_map {α β : Type} (f : α → β) : ∀ {l : List α}, (l.map f).Nodup → l.Nodup
  | [], _ => List.nodup_nil
  | x :: l, h => by
    rw [List.map_cons, List.nodup_cons] at h
    exact List.nodup_cons.mpr ⟨fun hx => h.1 (List.mem_map_of_mem hx), nodup_of_map f h.2⟩

/-- The node records' `VSLOT` receives are pairwise distinct as `Fp` messages. -/
theorem node_vslot_nodup {pub : List Fp} {tr : Trace Fp} {r : V3Records} (hH : HoldsP nearAirV3 pub tr)
    (T : V3RecordsTraffic pub tr r) (W : V3RecordsWf pub r) :
    ((ZkFormal.NearV3.nodeRecvs3 r.nodes B_VSLOT).map Msg.toFp).Nodup := by
  have hvb := vparentBal_of hH T
  have hlen := ZkFormal.NearV3.Link3.vlen_le W.values
  simp only [ZkFormal.NearV3.nodeRecvs3, show B_VSLOT ≠ B_DIGEST by decide,
    show B_VSLOT ≠ B_PARENT by decide, show B_VSLOT ≠ B_EDGE by decide,
    show B_VSLOT ≠ ZkFormal.NearV3.B_BMAP by decide, show B_VSLOT ≠ ZkFormal.NearV3.B_DUP by decide,
    show B_VSLOT ≠ ZkFormal.NearV3.B_ENT by decide, show B_VSLOT ≠ ZkFormal.NearV3.B_UPB by decide,
    ite_false, ite_true, List.map_flatMap]
  -- the message of a record, and its value id bound
  have hsmall : ∀ n (hn : n < r.nodes.length) i l pre po,
      r.nodes[n].v.value = some (i, l, pre, po, true) → i < P := by
    intro n hn i l pre po hv
    obtain ⟨t, ht, -, hi, -, -⟩ := ZkFormal.NearV3.Link3.val_pos W.nodes W.values hvb hlen hn hv
    have := ZkFormal.NearV3.Link3.vid_small W.values ht
    rw [hi] at this
    unfold P; omega
  apply Sound.nodup_flatMap_of
  · intro p _
    split <;> simp
  · intro a b p q x hab hp hq hxp hxq
    obtain ⟨s, n⟩ := p
    obtain ⟨s', n'⟩ := q
    have hp' := List.mem_of_getElem? hp
    have hq' := List.mem_of_getElem? hq
    obtain ⟨hn, rfl⟩ := ZkFormal.NearV3.Link3.mem_zip_range hp'
    obtain ⟨hn', rfl⟩ := ZkFormal.NearV3.Link3.mem_zip_range hq'
    have ha : a = n := by
      have := List.getElem?_eq_some_iff.mp hp
      obtain ⟨h1, h2⟩ := this
      simp only [List.getElem_zip, List.getElem_range, Prod.mk.injEq] at h2
      exact h2.2
    have hb : b = n' := by
      have := List.getElem?_eq_some_iff.mp hq
      obtain ⟨h1, h2⟩ := this
      simp only [List.getElem_zip, List.getElem_range, Prod.mk.injEq] at h2
      exact h2.2
    have hnn : n ≠ n' := by omega
    dsimp only at hxp hxq
    split at hxp
    · rename_i i l pre po hv
      split at hxq
      · rename_i i' l' pre' po' hv'
        simp only [List.map_cons, List.map_nil, List.mem_singleton] at hxp hxq
        subst hxp
        simp only [Msg.toFp, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hxq
        have hii := ZkFormal.Near.Link.ofNat_inj (hsmall n hn i l pre po hv)
          (hsmall n' hn' i' l' pre' po' hv') hxq
        subst hii
        exact hnn (ZkFormal.NearV3.Link3.val_unique W.nodes W.values hvb hlen hn hn' hv hv')
      · simp at hxq
    · simp at hxp

/-- **The account slots are distinct.** -/
theorem acct_k_nodup {pub : List Fp} {tr : Trace Fp} {r : V3Records} (hH : HoldsP nearAirV3 pub tr)
    (T : V3RecordsTraffic pub tr r) (W : V3RecordsWf pub r) : (r.accts.map (·.k)).Nodup := by
  have hn := node_vslot_nodup hH T W
  have hc : ((ZkFormal.NearV3.acctV3Sends r.accts B_VSLOT).map Msg.toFp).Nodup := by
    apply nodup_of_count_le
    intro m
    rw [vslot_bal hH T]
    exact count_le_of_nodup hn m
  have hs : ZkFormal.NearV3.acctV3Sends r.accts B_VSLOT = r.accts.map fun a => [a.k] := by
    simp [ZkFormal.NearV3.acctV3Sends, B_VSLOT, ZkFormal.NearV3.B_VBYTES, B_BYTES, B_MEM]
  rw [hs, List.map_map] at hc
  have hk : ∀ a ∈ r.accts, a.k < P := by
    intro a ha
    rcases W.accts with he | hw
    · rw [he] at ha; cases ha
    · exact (hw.v1.len a ha).2.2.1
  exact nodup_of_map (fun k => Msg.toFp [k]) (by rw [List.map_map]; exact hc)

/-- **`MemHyp` from the trace and the views alone.** -/
theorem memHyp_of' {pub : List Fp} {tr : Trace Fp} {r : V3Records} (hH : HoldsP nearAirV3 pub tr)
    (T : V3RecordsTraffic pub tr r) (W : V3RecordsWf pub r) : MemHyp (rv r.lists) r.accts :=
  memHyp_of hH T W (acct_k_nodup hH T W)

end ZkFormal.NearV3.RcptLink
