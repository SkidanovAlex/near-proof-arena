import ZkFormal.NearV3.Assembly.LinkRids
import ZkFormal.NearV3.Rcpt.Link.ListSha
import ZkFormal.NearV3.Rcpt.Link.ListEncodingBounds
import ZkFormal.NearV3.Rcpt.Candidates.ReceiptShaPayloads

/-!
# ZkFormal.NearV3.Assembly.LinkRidBytes — receipt ids are bytes (closes `receiptIds`)

Every receipt list `j` of the receipt view is hashed: `RCL` pairs it with a source-proof block
of `srcpV3` (`[j, |RC(j)|]`), whose leaf receives `digMsg (msgId K_RC j) |RC(j)| leaf`, a digest
the SHA union provides (`digest_provided`).  `RcptLink.list_sha_digest` then makes the list
encoding (header + every receipt's `enc`, which contains its `rid`) byte-valued.  Its `BYTES`
hypothesis is met by `shaFacts_cover` (only `shaR > 0 → ∈ S` is used) with the other senders
`othersRC` (node / val / ups / acct / srcp / mrk / codec), whose ids are never of kind `K_RC`.
-/

namespace ZkFormal.NearV3.Assembly

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near

namespace LinkRidBytes

open ZkFormal.NearV3

/-- `ShaFacts` with the `BYTES` receives replaced by a covering message list. -/
theorem shaFacts_cover {shaS shaR : Nat → List Fp → Nat} (h : ShaFacts shaS shaR) (S : List Msg)
    (hS : ∀ m, shaR B_BYTES m ≤ cnt S m) :
    ShaFacts shaS (fun b m => if b = B_BYTES then cnt S m else shaR b m) where
  sends_only_digest := h.sends_only_digest
  recvs_only_bytes b m hb := by rw [if_neg hb]; exact h.recvs_only_bytes b m hb
  digest m hm := by
    obtain ⟨id, bs, he, hall⟩ := h.digest m hm
    exact ⟨id, bs, he, fun i hi => by rw [if_pos rfl]; exact Nat.lt_of_lt_of_le (hall i hi) (hS _)⟩

/-- The `BYTES` senders other than rcpt. -/
def othersRC (tr : Trace Fp) (pub : List Fp) (r : V3Records) : List Msg :=
  nodeSends3 r.nodes B_BYTES ++ valSends r.values B_BYTES ++ (upsTraffic r.ups).sends B_BYTES ++
    acctV3Sends r.accts B_BYTES ++ (ddTraffic r.srcp r.srcpRep).sends B_BYTES ++
    (mrkTrafficE pub r.mrkE r.mrk).sends B_BYTES ++ (codecBytes tr pub).map fun x => x.map Fp.toNat

theorem sha_le_rc {pub : List Fp} {tr : Trace Fp} {r : V3Records} (hH : HoldsP nearAirV3 pub tr)
    (T : V3RecordsTraffic pub tr r) (m : List Fp) :
    shaU tr pub false B_BYTES m ≤ cnt (rcptSends3 pub r.lists B_BYTES ++ othersRC tr pub r) m := by
  have h := bytes_balance hH T m
  have e : cnt (rcptSends3 pub r.lists B_BYTES ++ othersRC tr pub r) m =
      cnt (nodeSends3 r.nodes B_BYTES ++ valSends r.values B_BYTES) m + (otherBytes tr pub r).count m := by
    unfold cnt othersRC otherBytes otherRecBytes
    simp only [List.map_append, List.count_append, List.map_map]
    rw [show (Msg.toFp ∘ fun x : List Fp => x.map Fp.toNat) = id from funext toFp_map_toNat, List.map_id]
    omega
  omega

/-- No other `BYTES` sender uses an id of kind `K_RC`. -/
theorem othersRC_kinds {cb : NearSpec.Bytes} {h : NearSpecV3.Hint} {p : NearSpecV3.Prep} {oh : Nat}
    {tr : Trace Fp} {r : V3Records} (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r) :
    ∀ m ∈ othersRC tr (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r, ∀ a,
      m.head? = some a → a < P ∧ a % 16 ≠ K_RC := by
  have kin : ∀ {K : Nat} {x : Msg}, KindIn [K] x → K ≠ K_RC → ∀ a, x.head? = some a →
      a < P ∧ a % 16 ≠ K_RC := by
    intro K x hk hK a ha
    obtain ⟨h1, h2⟩ := hk a ha
    rw [List.mem_singleton] at h2
    exact ⟨h1, h2 ▸ hK⟩
  have nv : ∀ {K n : Nat}, (K = K_NPRE ∨ K = K_NPOST ∨ K = K_VPRE) → n < 2 ^ 22 →
      msgId K n < P ∧ msgId K n % 16 ≠ K_RC := by
    intro K n hK hn
    unfold msgId P
    rcases hK with rfl | rfl | rfl <;> simp only [K_NPRE, K_NPOST, K_VPRE, K_RC] <;> omega
  intro m hm a ha
  simp only [othersRC, List.mem_append] at hm
  rcases hm with (((((hm | hm) | hm) | hm) | hm) | hm) | hm
  · obtain ⟨K, n, hh, hK, hn⟩ := nodeVal_bytes_head W.nodes W.values (List.mem_append_left _ hm)
    rw [ha, Option.some.injEq] at hh; subst hh
    exact nv hK hn
  · obtain ⟨K, n, hh, hK, hn⟩ := nodeVal_bytes_head W.nodes W.values (List.mem_append_right _ hm)
    rw [ha, Option.some.injEq] at hh; subst hh
    exact nv hK hn
  · exact kin (upsKindIn_of hp hsz hH T W m hm) (by decide) a ha
  · exact kin (acctKindIn hH T W m hm) (by decide) a ha
  · exact kin (ddKindIn W.srcp m hm) (by decide) a ha
  · exact kin (mrkKindIn W (pubNat_pubOf_lt _) m hm) (by decide) a ha
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hm
    cases hyh : y.head? with
    | none => simp [List.head?_map, hyh] at ha
    | some e =>
      simp only [List.head?_map, hyh, Option.map_some, Option.some.injEq] at ha
      subst ha
      have := codecKindIn hp hsz hH y hy e hyh
      exact ⟨Fp.toNat_lt e, by rw [this]; decide⟩

theorem le_sum_of_mem' : ∀ {l : List Nat} {a : Nat}, a ∈ l → a ≤ l.sum
  | [], _, h => absurd h List.not_mem_nil
  | b :: l, a, h => by
    rcases List.mem_cons.mp h with rfl | h
    · simp
    · have := le_sum_of_mem' h; simp only [List.sum_cons]; omega

/-! ## `RCL`: every list has a source block -/

theorem enc_flat_bound : ∀ (xs : List RcptE), (∀ x ∈ xs, x.enc.length ≤ 347) →
    (xs.flatMap fun x => x.enc).length ≤ 347 * xs.length
  | [], _ => by simp
  | x :: xs, h => by
    have hx := h x (by simp)
    have ih := enc_flat_bound xs (fun y hy => h y (by simp [hy]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.mul_add, Nat.mul_one]
    omega

/-- The list encoding is shorter than `P` (`≤ 12 + 347 · 2^22`). -/
theorem listEncoding_lt {pub : List Fp} {ls : RcptV3Vs} (h : RcptV3Wf pub ls)
    (hr : (flatR ls).length ≤ 2 ^ 22) {j : Nat} (hj : j < ls.length) :
    (RcptLink.listEncoding pub ls[j]).length < P := by
  obtain ⟨toks, -, -, hwf, -⟩ := h.toks
  have he : ∀ x ∈ ls[j].rs, x.enc.length ≤ 347 := by
    intro x hx
    have hx' : x ∈ flatR ls := List.mem_flatMap.mpr ⟨_, List.getElem_mem hj, hx⟩
    obtain ⟨q, hq, rfl⟩ := List.getElem_of_mem hx'
    exact (Rcpt.Candidates.receipt_sha_lengths pub _ (hwf q hq)).1
  have hb := enc_flat_bound _ he
  have hl := RcptLink.located_index_bound ls hj
  have h12 := RcptLink.list_header_length pub ls[j]
  simp only [RcptLink.listEncoding, List.length_append, h12]
  unfold P; omega

theorem rcl_block {pub : List Fp} {tr : Trace Fp} {r : V3Records} (hH : HoldsP nearAirV3 pub tr)
    (T : V3RecordsTraffic pub tr r) (W : V3RecordsWf pub r) {j : Nat} (hj : j < r.lists.length) :
    ∃ B ∈ r.srcp, B.j = j ∧ B.L = (RcptLink.listEncoding pub r.lists[j]).length := by
  have hb := bal_users hH (b := B_RCL) (U := [T_RCPT, T_SRCP]) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel)
    (Msg.toFp [j, lOffs r.lists[j].rs r.lists[j].rs.length])
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at hb
  rw [show isAt T_RCPT = RcptV3.interactions from rfl, tcnt_of_traffic T.lists, tcnt_of_traffic T.lists,
    show isAt T_SRCP = ZkFormal.NearV3.Rcpt.Candidates.DedupTable.interactions from rfl,
    tcnt_of_traffic T.srcp, tcnt_of_traffic T.srcp] at hb
  have r0 : rcptRecvs3 r.lists B_RCL = [] := by
    simp [rcptRecvs3, rRecvs, B_DIGEST, B_FINAL, B_MEM, B_RCL, B_SREC, B_AKC, B_BND]
  have s0 : (ddTraffic r.srcp r.srcpRep).sends B_RCL = [] := DDView.rcl_sends _ _
  have hs : [j, lOffs r.lists[j].rs r.lists[j].rs.length] ∈ rcptSends3 pub r.lists B_RCL := by
    simp only [rcptSends3, List.mem_flatMap, List.mem_range]
    refine ⟨j, hj, ?_⟩
    simp [B_RCL, B_BYTES, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  have hpos : 0 < tcnt (rcptTraffic3 pub r.lists) true B_RCL (Msg.toFp [j, lOffs r.lists[j].rs r.lists[j].rs.length]) := by
    simp only [tcnt, ite_true, rcptTraffic3]
    exact List.count_pos_iff.mpr (List.mem_map_of_mem hs)
  simp only [tcnt, ite_true, Bool.false_eq_true, ite_false, rcptTraffic3, r0, s0, List.map_nil,
    List.count_nil, Nat.add_zero, Nat.zero_add] at hb hpos
  rw [hb] at hpos
  obtain ⟨m, hm, he⟩ := List.mem_map.mp (List.count_pos_iff.mp hpos)
  rw [DDView.rcl_recvs _ _ W.srcp.len] at hm
  obtain ⟨B, hB, rfl⟩ := List.mem_map.mp hm
  simp only [Msg.toFp, List.map_cons, List.map_nil, List.cons.injEq, and_true] at he
  have hjl : j < P := by have := W.listsCount.1; unfold P; omega
  have hlen := listEncoding_lt W.lists W.listsCount.2 hj
  rw [RcptLink.list_encoding_length] at hlen ⊢
  exact ⟨B, hB, ZkFormal.NearV3.Link3.ofNat_eq (W.srcp.j_lt hB) hjl he.1,
    ZkFormal.NearV3.Link3.ofNat_eq (W.srcp.L_lt hB) hlen he.2⟩

/-! ## Receipt encodings (hence ids) are bytes -/

theorem encBytes {cb : NearSpec.Bytes} {h : NearSpecV3.Hint} {p : NearSpecV3.Prep} {oh : Nat}
    {tr : Trace Fp} {r : V3Records} (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r) :
    ∀ x ∈ flatR r.lists, Bytes8 x.enc := by
  intro x hx
  obtain ⟨L, hL, hxL⟩ := List.mem_flatMap.mp hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hL
  obtain ⟨B, hB, hBj, hBL⟩ := rcl_block hH T W hj
  cases hBd : B.dup
  case true =>
    -- a `dup` reference has the empty list (`L = 12`), so the list has no receipt bytes
    have hb := W.srcp.block B hB
    simp only [hBd, ite_true] at hb
    have h12 := hBL.symm.trans hb.1
    have hxe : x.enc = [] := by
      have hl : (RcptLink.listEncoding (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh))
          r.lists[j]).length = 12 + (r.lists[j].rs.flatMap fun x => x.enc).length := by
        simp [RcptLink.listEncoding, RcptLink.list_header_length]
      have hsub : x.enc.length ≤ (r.lists[j].rs.flatMap fun x => x.enc).length := by
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hxL
        rw [List.length_flatMap]
        exact le_sum_of_mem' (List.mem_map_of_mem (f := fun x : RcptE => x.enc.length) (List.getElem_mem hi))
      exact List.eq_nil_of_length_eq_zero (by omega)
    intro y hy; rw [hxe] at hy; simp at hy
  have hdig : 0 < shaU tr (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) true B_DIGEST (digMsg (msgId K_RC j)
      (RcptLink.listEncoding (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r.lists[j]).length B.leaf).toFp := by
    apply digest_provided hH (t := T_SRCP) (by decide)
    rw [show isAt T_SRCP = ZkFormal.NearV3.Rcpt.Candidates.DedupTable.interactions from rfl,
      tcnt_of_traffic T.srcp]
    simp only [tcnt, Bool.false_eq_true, ite_false]
    apply List.count_pos_iff.mpr
    apply List.mem_map_of_mem
    have := DDView.leaf_recv W.srcp.len hB hBd
    rw [hBj, hBL] at this
    exact this
  have hsha := shaFacts_cover (shaU_facts hH) _ (sha_le_rc hH T)
  have hcB : (∀ v ∈ B.leaf, v < P) := by
    have hb := W.srcp.block B hB
    simp only [hBd, Bool.false_eq_true, ite_false] at hb
    exact fun v hv => hb.canon.2.2.1 v (List.mem_append_right _ hv)
  obtain ⟨hb8, -⟩ := RcptLink.list_sha_digest W.lists W.listsCount.1 W.listsCount.2 hsha
    (othersRC tr (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r) (fun m => if_pos rfl) (othersRC_kinds hp hsz hH T W) hj
    (listEncoding_lt W.lists W.listsCount.2 hj)
    hcB hdig
  intro y hy
  apply hb8
  simp only [RcptLink.listEncoding, List.mem_append, List.mem_flatMap]
  right
  exact ⟨x, hxL, hy⟩

theorem ridBytes {cb : NearSpec.Bytes} {h : NearSpecV3.Hint} {p : NearSpecV3.Prep} {oh : Nat}
    {tr : Trace Fp} {r : V3Records} (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r) :
    ∀ x ∈ flatR r.lists, Bytes8 x.rid := by
  intro x hx y hy
  exact encBytes hp hsz hH T W x hx y (by simp [RcptV.enc, hy])

/-- **`GoodV3.receiptIds`** for the reconstruction whose receipts are the receipt view's lists. -/
theorem receiptIds_of {cb : NearSpec.Bytes} {h : NearSpecV3.Hint} {p : NearSpecV3.Prep} {oh : Nat}
    {tr : Trace Fp} {r : V3Records} (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    (x : ExtV3) (hx : x.receipts = r.lists) :
    (x.applied.map NearSpec.Receipt.receiptId).Nodup :=
  LinkRids.receiptIds_ext hH T W (ridBytes hp hsz hH T W) x hx

end LinkRidBytes

end ZkFormal.NearV3.Assembly
