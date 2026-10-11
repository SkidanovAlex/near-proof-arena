import ZkFormal.NearV3.Assembly.LinkTrie
import ZkFormal.NearV3.Extract.SortV3Proof
import ZkFormal.NearV3.Candidates.SortEmptyCap
import ZkFormal.Near.Link.Nodup

/-!
# ZkFormal.NearV3.Assembly.LinkRids — `receiptIds` from the `RIDS` bus and the sort table

* `rids_bal` — the `RIDS` bus (users: rcpt, sort) from `HoldsP`: the sort table at index
  `T_SORT` is silent (`sortV3_empty_or_old`) and then the receipt view sends no ids, or it is the
  v1 sort table at cap 19 (`sortV3_view`) and the receipt view's id sends are, as `Fp` messages,
  a permutation of the sort view's receives;
* `rcptSends3_rids` — the receipt view's id sends are `(r, i, rid[i])` over the flattened
  receipts with their global index `r`;
* **`receiptIds_of_ridBytes`** — if every receipt id is byte-valued, the applied receipts'
  ids are pairwise distinct (the v1 `nodup_ok` argument: the sort ids are exactly the receipt ids
  and strictly increasing).

The byte-ness of the receipt ids is the remaining hypothesis (to come from the `K_RC` list
digest, `RcptLink.list_sha_digest`).
-/

namespace ZkFormal.NearV3.Assembly

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near

namespace LinkRids

open ZkFormal.NearV3

/-! ## Receipt id sends over the flattened receipts -/

theorem zip_range' {α : Type} [Inhabited α] (xs : List α) (off : Nat) :
    (List.range xs.length).map (fun k => (xs.getD k default, off + k)) = xs.zipIdx off := by
  apply List.ext_getElem (by simp)
  intro i hi hi'
  have hi0 : i < xs.length := by simpa using hi
  simp [List.getElem_map, List.getElem_range, List.getElem_zipIdx,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi0]

theorem indexed {α : Type} (ls : RcptV3Vs) (off : Nat) (f : Nat → RcptE → List α) :
    (List.range ls.length).flatMap (fun j => (List.range (ls.getD j default).rs.length).flatMap
      (fun k => f (off + baseR ls j + k) ((ls.getD j default).rs.getD k default))) =
    ((flatR ls).zipIdx off).flatMap (fun p => f p.2 p.1) := by
  induction ls generalizing off with
  | nil => simp [flatR]
  | cons L ls ih =>
    simp only [List.length_cons, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map,
      List.getD_cons_zero, List.getD_cons_succ, baseR, List.take_zero, List.map_nil, List.sum_nil,
      Nat.add_zero, List.take_succ_cons, List.map_cons, List.sum_cons, Function.comp_def,
      flatR, List.flatMap_cons, List.zipIdx_append, List.flatMap_append]
    have hhead : (List.range L.rs.length).flatMap (fun k => f (off + k) (L.rs.getD k default)) =
        (L.rs.zipIdx off).flatMap (fun p => f p.2 p.1) := by
      rw [← zip_range' L.rs off, List.flatMap_map]
    rw [hhead]
    congr 1
    simpa only [baseR, flatR, Nat.add_assoc] using ih (off + L.rs.length)

theorem located_flat {α : Type} (ls : RcptV3Vs) (f : Nat → RcptE → List α) :
    (List.range ls.length).flatMap (fun j => (located ls j).flatMap (fun p => f p.1 p.2.2)) =
      ((flatR ls).zipIdx).flatMap (fun p => f p.2 p.1) := by
  simpa only [located, List.flatMap_map, Nat.zero_add] using indexed ls 0 f

theorem zipIdx_zero {α : Type} (xs : List α) : xs.zipIdx = xs.zip (List.range xs.length) := by
  rw [List.zipIdx_eq_zip_range']
  congr 1
  rw [List.range'_eq_map_range]
  simp

/-- The receipt view's `RIDS` sends: `(r, i, rid[i])` for the `r`-th flattened receipt. -/
theorem rcptSends3_rids (pub : List Fp) (ls : RcptV3Vs) :
    rcptSends3 pub ls B_RIDS = ((flatR ls).zip (List.range (flatR ls).length)).flatMap
      fun p => (List.range 32).map fun i => [p.2, i, p.1.rid.getD i 0] := by
  simp only [rcptSends3, show B_RIDS ≠ B_BYTES by decide, show B_RIDS ≠ B_RCL by decide,
    ite_false, List.nil_append]
  have hs : ∀ (j : Nat) (p : Nat × Nat × RcptE), rSends pub (flatR ls) j p.1 p.2.1 p.2.2 B_RIDS =
      (List.range 32).map (fun i => [p.1, i, p.2.2.rid.getD i 0]) := by
    intro j p
    simp [rSends, B_RIDS, B_BYTES, B_KEYNIB, B_MEM]
  simp only [hs]
  rw [located_flat ls (fun r x => (List.range 32).map fun i => [r, i, x.rid.getD i 0]), ← zipIdx_zero]

/-! ## The `RIDS` balance -/

/-- **`RIDS`**: the sort table is silent and the receipt view sends no ids, or the receipt
view's id sends are a permutation of a sort view's receives. -/
theorem rids_bal {pub : List Fp} {tr : Trace Fp} {r : V3Records} (hH : HoldsP nearAirV3 pub tr)
    (T : V3RecordsTraffic pub tr r) :
    rcptSends3 pub r.lists B_RIDS = [] ∨
      ∃ ids, SortWf ids ∧ ((rcptSends3 pub r.lists B_RIDS).map Msg.toFp).Perm
        (((sortTraffic ids).recvs B_RIDS).map Msg.toFp) := by
  have hb := fun m => bal_users hH (b := B_RIDS) (U := [T_RCPT, T_SORT]) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) m
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at hb
  have hr : ∀ s m, tableBusCount (isAt T_RCPT) tr T_RCPT pub B_RIDS s m =
      tcnt (rcptTraffic3 pub r.lists) s B_RIDS m := fun s m => by
    rw [show isAt T_RCPT = RcptV3.interactions from rfl, tcnt_of_traffic T.lists]
  have hr0 : ∀ m, tcnt (rcptTraffic3 pub r.lists) false B_RIDS m = 0 := by
    intro m
    simp only [tcnt, rcptTraffic3, Bool.false_eq_true, ite_false]
    rw [RcptV3Proof.rids_view_receive_empty]; rfl
  have hL := tableLocal_of_holdsP hH getElem?_sort
  rcases Candidates.SortEmpty.sortV3_empty_or_old tr T_SORT pub hL with hz | hold
  · left
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro m hm
    have h := hb (Msg.toFp m)
    rw [hr, hr, hr0, show isAt T_SORT = sortTableV3.interactions from rfl, hz, hz] at h
    simp only [tcnt, ite_true, rcptTraffic3, Nat.add_zero] at h
    have : 0 < ((rcptSends3 pub r.lists B_RIDS).map Msg.toFp).count (Msg.toFp m) :=
      List.count_pos_iff.mpr (List.mem_map_of_mem hm)
    omega
  · right
    obtain ⟨ids, hW, hT⟩ := sortV3_view tr pub T_SORT hold
    refine ⟨ids, hW, List.perm_iff_count.mpr fun m => ?_⟩
    have h := hb m
    rw [hr, hr, hr0, show isAt T_SORT = Sort.interactions from rfl, tcnt_of_traffic hT,
      tcnt_of_traffic hT] at h
    simp only [tcnt, ite_true, Bool.false_eq_true, ite_false, rcptTraffic3, sortTraffic,
      List.map_nil, List.count_nil, Nat.add_zero, Nat.zero_add] at h
    simpa [sortTraffic] using h

/-! ## Distinct receipt ids -/

open ZkFormal.Near.Link in
/-- **`receiptIds`** given byte-valued receipt ids: the sort ids are exactly the receipt ids, one
per receipt, strictly increasing. -/
theorem receiptIds_of_ridBytes {pub : List Fp} {tr : Trace Fp} {r : V3Records}
    (hH : HoldsP nearAirV3 pub tr) (T : V3RecordsTraffic pub tr r) (W : V3RecordsWf pub r)
    (hrid : ∀ x ∈ flatR r.lists, Bytes8 x.rid) :
    ((flatR r.lists).map fun x => x.toRcptV.toReceipt.receiptId).Nodup := by
  have hrl : (flatR r.lists).length ≤ 2 ^ 22 := W.listsCount.2
  obtain ⟨toks, -, -, hwf, -⟩ := W.lists.toks
  have hlen : ∀ q (hq : q < (flatR r.lists).length), (flatR r.lists)[q].rid.length = 32 :=
    fun q hq => (hwf q hq).lens.1
  have hcan : ∀ x ∈ flatR r.lists, ∀ y ∈ x.rid, y < P := by
    intro x hx y hy
    exact W.lists.canon.2 x hx y (by simp [RcptE.raw3, RcptV.raw, hy])
  generalize hrs : flatR r.lists = rs at hrl hlen hcan hrid
  rcases rids_bal hH T with h0 | ⟨ids, hW, hp⟩
  · rw [rcptSends3_rids, hrs] at h0
    cases rs with
    | nil => exact List.nodup_nil
    | cons x xs =>
      exfalso
      have hm : [0, 0, x.rid.getD 0 0] ∈ ((x :: xs).zip (List.range (x :: xs).length)).flatMap
          fun p => (List.range 32).map fun i => [p.2, i, p.1.rid.getD i 0] :=
        List.mem_flatMap.mpr ⟨(x, 0), mem_zip_range.mpr ⟨by simp, rfl⟩,
          List.mem_map.mpr ⟨0, by simp, rfl⟩⟩
      rw [h0] at hm; simp at hm
  rw [rcptSends3_rids, hrs] at hp
  have hsr : (sortTraffic ids).recvs B_RIDS =
      ids.flatMap fun p => (List.range 32).map fun i => [p.1, i, p.2.getD i 0] := by
    simp [sortTraffic]
  rw [hsr] at hp
  have hpn := perm_nat ?_ ?_ hp
  rotate_left
  · intro m hm
    obtain ⟨⟨x, q⟩, hpr, hm⟩ := List.mem_flatMap.mp hm
    obtain ⟨hq, rfl⟩ := mem_zip_range.mp hpr
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hm
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl
    · unfold P; omega
    · simp at hi; unfold P; omega
    · exact getD_lt (hcan _ (List.getElem_mem hq)) i
  · intro m hm
    obtain ⟨p, hpi, hm⟩ := List.mem_flatMap.mp hm
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hm
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl
    · exact (hW.len p hpi).2
    · simp at hi; unfold P; omega
    · exact getD_lt (hW.canon p hpi) i
  -- every sort entry is a receipt's id
  have hrev : ∀ p (hp : p < ids.length) j, j < 32 →
      ∃ hr : ids[p].1 < rs.length, ids[p].2.getD j 0 = rs[ids[p].1].rid.getD j 0 := by
    intro p hp j hj
    have hm2 : [ids[p].1, j, ids[p].2.getD j 0] ∈ ids.flatMap
        fun p => (List.range 32).map fun i => [p.1, i, p.2.getD i 0] :=
      List.mem_flatMap.mpr ⟨_, List.getElem_mem hp, List.mem_map.mpr ⟨j, by simp; omega, rfl⟩⟩
    obtain ⟨⟨x, r'⟩, hpr, hm3⟩ := List.mem_flatMap.mp (hpn.mem_iff.mpr hm2)
    obtain ⟨hr', rfl⟩ := mem_zip_range.mp hpr
    obtain ⟨j', -, he'⟩ := List.mem_map.mp hm3
    simp only [List.cons.injEq] at he'
    obtain ⟨e1, rfl, e3⟩ := he'
    subst e1
    exact ⟨hr', e3.1.symm⟩
  -- each receipt has a sort entry carrying its id
  have hentry : ∀ q (hq : q < rs.length), ∃ p, ∃ hp : p < ids.length, ids[p].1 = q ∧
      ids[p].2 = rs[q].rid := by
    intro q hq
    have hm : [q, 0, rs[q].rid.getD 0 0] ∈ (rs.zip (List.range rs.length)).flatMap
        fun p => (List.range 32).map fun i => [p.2, i, p.1.rid.getD i 0] :=
      List.mem_flatMap.mpr ⟨(rs[q], q), mem_zip_range.mpr ⟨hq, rfl⟩,
        List.mem_map.mpr ⟨0, by simp, rfl⟩⟩
    obtain ⟨q', hq', hm'⟩ := List.mem_flatMap.mp (hpn.mem_iff.mp hm)
    obtain ⟨i, -, he⟩ := List.mem_map.mp hm'
    simp only [List.cons.injEq] at he
    obtain ⟨p, hpl, rfl⟩ := List.mem_iff_getElem.mp hq'
    refine ⟨p, hpl, he.1, ?_⟩
    have hl1 : ids[p].2.length = 32 := (hW.len _ hq').1
    apply List.ext_getElem (by rw [hl1, hlen q hq])
    intro j hj1 hj2
    obtain ⟨_, e⟩ := hrev p hpl j (by omega)
    rw [← getD_eq_getElem _ 0 hj1, ← getD_eq_getElem _ 0 hj2, e]
    simp only [he.1]
  have hall : ∀ x ∈ ids, ∀ y ∈ x.2, y < 256 := by
    intro x hx y hy
    obtain ⟨p, hpl, rfl⟩ := List.mem_iff_getElem.mp hx
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hy
    have hl1 : ids[p].2.length = 32 := (hW.len _ hx).1
    obtain ⟨hr, e⟩ := hrev p hpl j (by omega)
    rw [← getD_eq_getElem _ 0 hj, e]
    exact getD_lt_of_bytes8 (hrid _ (List.getElem_mem hr)) _
  have hstrict := strict_of_succ
    (fun t => NearSpec.leNat ((ids.getD t (0, [])).2.map UInt8.ofNat)) ids.length
    (fun t ht => hW.incr t ht hall)
  apply nodup_of_getElem
  intro i j hi hj hij he
  simp only [List.length_map] at hi hj
  simp only [List.getElem_map, RcptV.toReceipt] at he
  obtain ⟨p1, hp1, e11, e12⟩ := hentry i hi
  obtain ⟨p2, hp2, e21, e22⟩ := hentry j hj
  have hpne : p1 ≠ p2 := fun e => hij (by subst e; omega)
  have hf : ∀ p (hp : p < ids.length) q (hq : q < rs.length), ids[p].2 = rs[q].rid →
      NearSpec.leNat ((ids.getD p (0, [])).2.map UInt8.ofNat) = NearSpec.leNat (toBytes rs[q].rid) := by
    intro p hp q hq e
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp, Option.getD_some, e]; rfl
  have f1 := hf p1 hp1 i hi e12
  have f2 := hf p2 hp2 j hj e22
  rw [he] at f1
  rcases Nat.lt_or_gt_of_ne hpne with hl | hl
  · have := hstrict p1 p2 hl hp2; omega
  · have := hstrict p2 p1 hl hp1; omega

/-- **`GoodV3.receiptIds`** for the reconstruction whose receipts are the receipt view's lists,
given byte-valued receipt ids. -/
theorem receiptIds_ext {pub : List Fp} {tr : Trace Fp} {r : V3Records}
    (hH : HoldsP nearAirV3 pub tr) (T : V3RecordsTraffic pub tr r) (W : V3RecordsWf pub r)
    (hrid : ∀ x ∈ flatR r.lists, Bytes8 x.rid) (x : ExtV3) (hx : x.receipts = r.lists) :
    (x.applied.map NearSpec.Receipt.receiptId).Nodup := by
  have h := receiptIds_of_ridBytes hH T W hrid
  simp only [ExtV3.applied, hx, List.map_flatMap, List.map_map]
  simp only [flatR, List.map_flatMap] at h
  exact h

end LinkRids

end ZkFormal.NearV3.Assembly
