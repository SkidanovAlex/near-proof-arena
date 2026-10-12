import ZkFormal.NearV3.Assembly.LinkBus
import ZkFormal.NearV3.Public.ReceiptIndex
import ZkFormal.NearV3.Assembly.PrepFacts

/-!
# ZkFormal.NearV3.Assembly.LinkSha — the two SHA instances against the rest of `nearAirV3`

`nearAirV3` has two SHA-256 tables (`T_SHA_T = 0`, `T_SHA_R = 1`).  Their union
`shaU tr pub` (`shaUnionCount` over `[0, 1]`) satisfies `ShaFacts` (`shaU_facts`).  This module
reads the `DIGEST` and `BYTES` balances of `nearAirV3` against it:

* **`digest_provided`**: every `DIGEST` message received by a non-SHA table (node, head, ups,
  codec, rcpt, srcp, mrk) is provided by the SHA union (`0 < shaU … true B_DIGEST m`); the
  non-SHA tables never send on `DIGEST` and the SHA tables never receive on it;
* **`bytes_balance`**: the SHA union's `BYTES` receives plus the public body receives
  (`bodyPlan`, bus `0`, side `false`) equal the `BYTES` sends of node, val, ups, codec, rcpt,
  acct, srcp and mrk (in record form except for the raw codec table);
* **`shaHyp_of`**: `Link3.ShaHyp r.nodes r.heads r.values others (shaU …)` for an explicit
  list `others` (the other senders' messages minus the public body receives), under the
  kind-registry hypothesis `OthersKinds` (every other `BYTES` sender's id is canonical with
  kind `∉ {K_NPRE, K_NPOST, K_VPRE}`) and `BodyOk` (a public `BYTES` receive is never a node /
  value record message).
-/

namespace ZkFormal.NearV3.Assembly

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near

/-- The union of the two SHA instances. -/
def shaU (tr : Trace Fp) (pub : List Fp) (s : Bool) : Nat → List Fp → Nat :=
  shaUnionCount tr pub [T_SHA_T, T_SHA_R] s

theorem shaU_eq (tr : Trace Fp) (pub : List Fp) (s : Bool) (b : Nat) (m : List Fp) :
    shaU tr pub s b m = tableBusCount (isAt T_SHA_T) tr T_SHA_T pub b s m +
      tableBusCount (isAt T_SHA_R) tr T_SHA_R pub b s m := by
  simp only [shaU, shaUnionCount, Nat.add_zero]; rfl

theorem shaU_facts {pub : List Fp} {tr : Trace Fp} (hH : HoldsP nearAirV3 pub tr) :
    ShaFacts (shaU tr pub true) (shaU tr pub false) := by
  apply shaUnionFacts
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · exact shaLocal_of_tableLocal (tableLocal_of_holdsP hH getElem?_sha_t)
  · exact shaLocal_of_tableLocal (tableLocal_of_holdsP hH getElem?_sha_r)

/-- A table with no interaction on `(b, s)` has count `0` there. -/
theorem tableBusCount_noside {is : List Interaction} {tr : Trace Fp} {t : Nat} {pub : List Fp}
    {b : Nat} {s : Bool} (h : is.all (fun i => !(i.bus == b && i.send == s)) = true) (m : List Fp) :
    tableBusCount is tr t pub b s m = 0 := by
  rw [tableBusCount_eq]
  apply List.count_eq_zero.mpr
  intro hx
  obtain ⟨r, -, hx⟩ := List.mem_flatMap.mp hx
  unfold rowTraffic at hx
  obtain ⟨i, hi, hx⟩ := List.mem_flatMap.mp hx
  have := List.all_eq_true.mp h i hi
  split at hx
  · rename_i hbs
    simp [hbs.1, hbs.2] at this
  · simp at hx

/-- No prepared public segment on `(b, sd)`: public count `0`. -/
theorem pubCount_noside {b : Nat} {sd : Bool}
    (hb : ZkFormal.NearV3.Public.preparedSegments.all (fun s => !(s.bus == b && s.send == sd)) = true)
    (pub : List Fp) (msg : List Fp) : pubCount nearAirV3 pub b sd msg = 0 := by
  unfold pubCount
  suffices ((pubMsgs nearAirV3 pub).filter (fun x => decide (x = (b, sd, msg)))) = [] by
    rw [this]; rfl
  apply List.filter_eq_nil_iff.mpr
  intro x hx
  have hn : x ≠ (b, sd, msg) := by
    intro he
    subst x
    simp only [pubMsgs, List.mem_flatMap, List.mem_map] at hx
    obtain ⟨s, hseg, m, -, he⟩ := hx
    have h1 := congrArg (fun x : Nat × Bool × List Fp => x.1) he
    have h2 := congrArg (fun x : Nat × Bool × List Fp => x.2.1) he
    have := List.all_eq_true.mp hb s hseg
    simp only at h1 h2
    simp [h1, h2] at this
  simpa using hn

/-! ## `DIGEST` -/

/-- The non-SHA users of `DIGEST` (all receive-only). -/
def digestRecvTables : List Nat := [T_NODE, T_HEAD, T_UPS, T_CODEC, T_RCPT, T_SRCP, T_MRK]

/-- **The SHA union provides every `DIGEST` message received elsewhere**: its `DIGEST` sends
are exactly the receives of the other tables. -/
theorem digest_users_eq {pub : List Fp} {tr : Trace Fp} (hH : HoldsP nearAirV3 pub tr)
    (m : List Fp) :
    shaU tr pub true B_DIGEST m =
      (digestRecvTables.map fun t => tableBusCount (isAt t) tr t pub B_DIGEST false m).sum := by
  have h := hH.balance B_DIGEST m
  rw [pubCount_nobus (by decide +kernel), pubCount_nobus (by decide +kernel),
    busCount_users (U := [T_SHA_T, T_SHA_R, T_NODE, T_HEAD, T_UPS, T_CODEC, T_RCPT, T_SRCP, T_MRK])
      (by decide) (by decide) (by decide +kernel),
    busCount_users (U := [T_SHA_T, T_SHA_R, T_NODE, T_HEAD, T_UPS, T_CODEC, T_RCPT, T_SRCP, T_MRK])
      (by decide) (by decide) (by decide +kernel)] at h
  have F := shaU_facts hH
  have r0 : tableBusCount (isAt T_SHA_T) tr T_SHA_T pub B_DIGEST false m = 0 :=
    (shaFactsAt tr pub T_SHA_T (shaLocal_of_tableLocal (tableLocal_of_holdsP hH getElem?_sha_t))).recvs_only_bytes
      B_DIGEST m (by decide)
  have r1 : tableBusCount (isAt T_SHA_R) tr T_SHA_R pub B_DIGEST false m = 0 :=
    (shaFactsAt tr pub T_SHA_R (shaLocal_of_tableLocal (tableLocal_of_holdsP hH getElem?_sha_r))).recvs_only_bytes
      B_DIGEST m (by decide)
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at h
  rw [r0, r1,
    tableBusCount_noside (is := isAt T_NODE) (by decide +kernel),
    tableBusCount_noside (is := isAt T_HEAD) (by decide +kernel),
    tableBusCount_noside (is := isAt T_UPS) (by decide +kernel),
    tableBusCount_noside (is := isAt T_CODEC) (by decide +kernel),
    tableBusCount_noside (is := isAt T_RCPT) (by decide +kernel),
    tableBusCount_noside (is := isAt T_SRCP) (by decide +kernel),
    tableBusCount_noside (is := isAt T_MRK) (by decide +kernel)] at h
  rw [shaU_eq]
  simp only [digestRecvTables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
  omega

theorem digest_provided {pub : List Fp} {tr : Trace Fp} (hH : HoldsP nearAirV3 pub tr)
    {t : Nat} (ht : t ∈ digestRecvTables) {m : List Fp}
    (hm : 0 < tableBusCount (isAt t) tr t pub B_DIGEST false m) : 0 < shaU tr pub true B_DIGEST m := by
  rw [digest_users_eq hH]
  exact Nat.lt_of_lt_of_le hm (nat_le_sum_of_mem (List.mem_map.mpr ⟨t, ht, rfl⟩))

/-! ## `BYTES` -/

/-- The `BYTES` messages of the raw codec table (`T_CODEC`), row by row. -/
def codecBytes (tr : Trace Fp) (pub : List Fp) : List (List Fp) :=
  (List.range (tr.height T_CODEC)).flatMap fun r => rowTraffic (isAt T_CODEC) tr T_CODEC r pub B_BYTES true

/-- The record-form `BYTES` sends of the viewed tables other than node / val. -/
def otherRecBytes (pub : List Fp) (r : V3Records) : List Msg :=
  (ZkFormal.NearV3.upsTraffic r.ups).sends B_BYTES ++ ZkFormal.NearV3.rcptSends3 pub r.lists B_BYTES ++
    ZkFormal.NearV3.acctV3Sends r.accts B_BYTES ++ (ZkFormal.NearV3.ddTraffic r.srcp r.srcpRep).sends B_BYTES ++
    (mrkTrafficE pub r.mrkE r.mrk).sends B_BYTES

/-- All `BYTES` sends other than node / val, as field messages. -/
def otherBytes (tr : Trace Fp) (pub : List Fp) (r : V3Records) : List (List Fp) :=
  (otherRecBytes pub r).map Msg.toFp ++ codecBytes tr pub

/-- **The `BYTES` balance**: SHA receives + public body receives = all `BYTES` sends. -/
theorem bytes_balance {pub : List Fp} {tr : Trace Fp} {r : V3Records} (hH : HoldsP nearAirV3 pub tr)
    (T : V3RecordsTraffic pub tr r) (m : List Fp) :
    shaU tr pub false B_BYTES m + pubCount nearAirV3 pub B_BYTES false m =
      cnt (ZkFormal.NearV3.nodeSends3 r.nodes B_BYTES ++ ZkFormal.NearV3.valSends r.values B_BYTES) m +
        (otherBytes tr pub r).count m := by
  have h := hH.balance B_BYTES m
  have U : [T_SHA_T, T_SHA_R, T_NODE, T_VAL, T_UPS, T_CODEC, T_RCPT, T_ACCT, T_SRCP, T_MRK].Nodup := by decide
  rw [pubCount_noside (sd := true) (by decide +kernel),
    busCount_users U (by decide) (by decide +kernel), busCount_users U (by decide) (by decide +kernel)] at h
  have s0 : tableBusCount (isAt T_SHA_T) tr T_SHA_T pub B_BYTES true m = 0 :=
    (shaFactsAt tr pub T_SHA_T (shaLocal_of_tableLocal (tableLocal_of_holdsP hH getElem?_sha_t))).sends_only_digest
      B_BYTES m (by decide)
  have s1 : tableBusCount (isAt T_SHA_R) tr T_SHA_R pub B_BYTES true m = 0 :=
    (shaFactsAt tr pub T_SHA_R (shaLocal_of_tableLocal (tableLocal_of_holdsP hH getElem?_sha_r))).sends_only_digest
      B_BYTES m (by decide)
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at h
  rw [s0, s1,
    tableBusCount_noside (s := false) (is := isAt T_NODE) (by decide +kernel),
    tableBusCount_noside (s := false) (is := isAt T_VAL) (by decide +kernel),
    tableBusCount_noside (s := false) (is := isAt T_UPS) (by decide +kernel),
    tableBusCount_noside (s := false) (is := isAt T_CODEC) (by decide +kernel),
    tableBusCount_noside (s := false) (is := isAt T_RCPT) (by decide +kernel),
    tableBusCount_noside (s := false) (is := isAt T_ACCT) (by decide +kernel),
    tableBusCount_noside (s := false) (is := isAt T_SRCP) (by decide +kernel),
    tableBusCount_noside (s := false) (is := isAt T_MRK) (by decide +kernel),
    node_count T _ _ _ (by decide +kernel), val_count T _ _ _ (by decide +kernel),
    ups_count T _ _ _ (by decide +kernel),
    show isAt T_RCPT = ZkFormal.NearV3.RcptV3.interactions from rfl, tcnt_of_traffic T.lists,
    show isAt T_ACCT = ZkFormal.NearV3.AcctV3.interactions from rfl, tcnt_of_traffic T.accts,
    show isAt T_SRCP = ZkFormal.NearV3.Rcpt.Candidates.DedupTable.interactions from rfl, tcnt_of_traffic T.srcp,
    show isAt T_MRK = ZkFormal.NearV3.Candidates.MerkleEmpty.table.interactions from rfl,
    tcnt_of_traffic T.mrk, tableBusCount_eq (isAt T_CODEC)] at h
  rw [shaU_eq]
  simp only [otherBytes, otherRecBytes, codecBytes, cnt, List.map_append, List.count_append]
  simp only [tcnt, ZkFormal.NearV3.nodeTraffic3, ZkFormal.NearV3.valTraffic, ZkFormal.NearV3.rcptTraffic3,
    ZkFormal.NearV3.acctV3Traffic, ite_true] at h
  omega

/-! ## The `ShaHyp` of the trie tables -/

/-- Remove the elements of `L` from `l`, one occurrence each. -/
def eraseAll {α : Type} [BEq α] (l : List α) : List α → List α
  | [] => l
  | a :: L => eraseAll (l.erase a) L

theorem count_eraseAll {α : Type} [BEq α] [LawfulBEq α] :
    ∀ (l L : List α) (x : α), (eraseAll l L).count x = l.count x - L.count x
  | l, [], x => by simp [eraseAll]
  | l, a :: L, x => by
    rw [eraseAll, count_eraseAll, List.count_erase, List.count_cons]
    split <;> omega

theorem eraseAll_sublist {α : Type} [BEq α] : ∀ (l L : List α), (eraseAll l L).Sublist l
  | l, [] => List.Sublist.refl l
  | l, a :: L => (eraseAll_sublist (l.erase a) L).trans List.erase_sublist

/-- The public messages on `(b, s)`, as a list. -/
def pubList (pub : List Fp) (b : Nat) (s : Bool) : List (List Fp) :=
  (pubMsgs nearAirV3 pub).filterMap fun x => if x.1 = b ∧ x.2.1 = s then some x.2.2 else none

theorem count_filterMap_pub (b : Nat) (s : Bool) (M : List Fp) :
    ∀ L : List (Nat × Bool × List Fp),
      (L.filterMap fun x => if x.1 = b ∧ x.2.1 = s then some x.2.2 else none).count M =
        (L.filter fun x => decide (x = (b, s, M))).length
  | [] => rfl
  | ⟨b', s', M'⟩ :: L => by
    have ih := count_filterMap_pub b s M L
    by_cases h : b' = b ∧ s' = s
    · obtain ⟨rfl, rfl⟩ := h
      by_cases hM : M' = M
      · subst hM; simp [ih]
      · simp [ih, hM]
    · have : ¬ ((b', s', M') = (b, s, M)) := fun e => by
        simp only [Prod.mk.injEq] at e; exact h ⟨e.1, e.2.1⟩
      simp only [List.filterMap_cons, List.filter_cons, h, decide_eq_true_eq, this, ite_false]
      exact ih

theorem count_pubList (pub : List Fp) (b : Nat) (s : Bool) (M : List Fp) :
    (pubList pub b s).count M = pubCount nearAirV3 pub b s M :=
  count_filterMap_pub b s M _

/-- **The other `BYTES` senders' messages** (natural numbers), net of the public receives. -/
def othersBytes (tr : Trace Fp) (pub : List Fp) (r : V3Records) : List Msg :=
  (eraseAll (otherBytes tr pub r) (pubList pub B_BYTES false)).map fun x => x.map Fp.toNat

theorem toFp_map_toNat (x : List Fp) : Msg.toFp (x.map Fp.toNat) = x := by
  simp only [Msg.toFp, List.map_map]
  conv => rhs; rw [← List.map_id x]
  apply List.map_congr_left
  intro a _
  exact Fp.ofNat_toNat a

/-- Kind registry for the other `BYTES` senders: ids of kind `∉ {K_NPRE, K_NPOST, K_VPRE}`. -/
def OthersKinds (tr : Trace Fp) (pub : List Fp) (r : V3Records) : Prop :=
  ∀ y ∈ otherBytes tr pub r, ∀ a, y.head? = some a →
    a.toNat % 16 ≠ K_NPRE ∧ a.toNat % 16 ≠ K_NPOST ∧ a.toNat % 16 ≠ K_VPRE

/-- The public `BYTES` receives (the refund body) are never node / value record messages. -/
def BodyOk (pub : List Fp) (r : V3Records) : Prop :=
  ∀ m, 0 < pubCount nearAirV3 pub B_BYTES false m →
    cnt (ZkFormal.NearV3.nodeSends3 r.nodes B_BYTES ++ ZkFormal.NearV3.valSends r.values B_BYTES) m = 0

/-- **`ShaHyp` of the trie tables** against the SHA union, from `HoldsP`, the exact traffic,
the kind registry of the other senders and the body separation. -/
theorem shaHyp_of {pub : List Fp} {tr : Trace Fp} {r : V3Records} (hH : HoldsP nearAirV3 pub tr)
    (T : V3RecordsTraffic pub tr r) (hK : OthersKinds tr pub r) (hB : BodyOk pub r) :
    ZkFormal.NearV3.Link3.ShaHyp r.nodes r.heads r.values (othersBytes tr pub r)
      (shaU tr pub true) (shaU tr pub false) := by
  refine ⟨shaU_facts hH, ?_, ?_, ?_⟩
  · intro m
    have h := bytes_balance hH T m
    have hc : cnt (othersBytes tr pub r) m = (otherBytes tr pub r).count m - pubCount nearAirV3 pub B_BYTES false m := by
      unfold cnt othersBytes
      rw [List.map_map, show (Msg.toFp ∘ fun x : List Fp => x.map Fp.toNat) = id from
        funext toFp_map_toNat, List.map_id, count_eraseAll, count_pubList]
    rw [show ZkFormal.NearV3.nodeSends3 r.nodes B_BYTES ++ ZkFormal.NearV3.valSends r.values B_BYTES ++
        othersBytes tr pub r = (ZkFormal.NearV3.nodeSends3 r.nodes B_BYTES ++
          ZkFormal.NearV3.valSends r.values B_BYTES) ++ othersBytes tr pub r from rfl]
    have hca : cnt ((ZkFormal.NearV3.nodeSends3 r.nodes B_BYTES ++ ZkFormal.NearV3.valSends r.values B_BYTES) ++
        othersBytes tr pub r) m = cnt (ZkFormal.NearV3.nodeSends3 r.nodes B_BYTES ++
          ZkFormal.NearV3.valSends r.values B_BYTES) m + cnt (othersBytes tr pub r) m := by
      unfold cnt; rw [List.map_append, List.count_append]
    rw [hca, hc]
    rcases Nat.eq_zero_or_pos (pubCount nearAirV3 pub B_BYTES false m) with h0 | h0
    · omega
    · have := hB m h0; omega
  · intro y hy a ha
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    have hx' := (eraseAll_sublist _ _).subset hx
    cases hxh : x.head? with
    | none => simp [List.head?_map, hxh] at ha
    | some e =>
      simp only [List.head?_map, hxh, Option.map_some, Option.some.injEq] at ha
      subst ha
      exact ⟨Fp.toNat_lt e, hK x hx' e hxh⟩
  · intro m hm
    unfold cnt at hm
    rw [List.map_append, List.count_append] at hm
    rcases Nat.eq_zero_or_pos (((ZkFormal.NearV3.nodeRecvs3 r.nodes B_DIGEST).map Msg.toFp).count m) with h0 | h0
    · rw [h0, Nat.zero_add] at hm
      apply digest_provided hH (t := T_HEAD) (by decide)
      rw [head_count T]; exact hm
    · apply digest_provided hH (t := T_NODE) (by decide)
      rw [node_count T _ _ _ (by decide +kernel)]; exact h0

/-! ## `BodyOk` from the prepared statement -/

/-- Node / value `BYTES` messages carry ids `msgId K n` with `K ∈ {K_NPRE, K_NPOST, K_VPRE}` and
`n < 2^22`. -/
theorem nodeVal_bytes_head {vs : List ZkFormal.NearV3.NodeS3} {es : List ZkFormal.NearV3.ValE}
    (hw : ZkFormal.NearV3.NodeWf3 vs) (hvw : ZkFormal.NearV3.ValWf es) {x : Msg}
    (hx : x ∈ ZkFormal.NearV3.nodeSends3 vs B_BYTES ++ ZkFormal.NearV3.valSends es B_BYTES) :
    ∃ K n, x.head? = some (msgId K n) ∧ (K = K_NPRE ∨ K = K_NPOST ∨ K = K_VPRE) ∧ n < 2 ^ 22 := by
  rcases List.mem_append.mp hx with hx | hx
  · simp only [ZkFormal.NearV3.nodeSends3, ite_true, List.mem_flatMap] at hx
    obtain ⟨⟨s, n⟩, hsn, hx⟩ := hx
    obtain ⟨hn, -⟩ := ZkFormal.NearV3.Link3.mem_zip_range hsn
    have hc := hw.count
    rcases List.mem_append.mp hx with hx | hx <;>
      obtain ⟨i, -, rfl⟩ := ZkFormal.NearV3.Link3.mem_emitAt3.mp hx
    · exact ⟨K_NPRE, n, rfl, .inl rfl, by omega⟩
    · exact ⟨K_NPOST, n, rfl, .inr (.inl rfl), by omega⟩
  · simp only [ZkFormal.NearV3.valSends, ite_true, List.mem_flatMap] at hx
    obtain ⟨e, he, hx⟩ := hx
    split at hx
    · simp at hx
    · obtain ⟨i, -, rfl⟩ := ZkFormal.NearV3.Link3.mem_emitAt3.mp hx
      obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.mp he
      have hv := ZkFormal.NearV3.Link3.vid_small hvw ht
      have hl := ZkFormal.NearV3.Link3.vlen_le hvw
      exact ⟨K_VPRE, es[t].vid, rfl, .inr (.inr rfl), by omega⟩

/-- **`BodyOk`**: the public `BYTES` receives are the refund body records `(2, 8 + j, byte)`
(`K_RF = 2`), never a node / value record message. -/
theorem bodyOk_of {cb : NearSpec.Bytes} {h : NearSpecV3.Hint} {p : NearSpecV3.Prep} {oh : Nat}
    {r : V3Records} (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < P)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r) :
    BodyOk (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r := by
  intro m hm
  have hlen : (ZkFormal.NearV3.Public.preparedBytes p oh).length < 256 ^ 4 := by unfold P at hsz; omega
  have hI := ZkFormal.NearV3.Public.prepared_receipt_index nearAirV3 p oh rfl (prepD0_roots hp)
    (prepD0_source_roots hp) hlen
  have hc := (ZkFormal.NearV3.Public.prepared_pubIdx nearAirV3 p oh rfl (prepD0_roots hp)
    (prepD0_source_roots hp) hlen).count B_BYTES false m
  rw [show B_BYTES = 0 from rfl, hI.2.2] at hc
  rw [show B_BYTES = 0 from rfl, hc] at hm
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp (List.count_pos_iff.mp hm)
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp hy
  unfold cnt
  apply List.count_eq_zero.mpr
  intro hx
  obtain ⟨x, hx, he⟩ := List.mem_map.mp hx
  obtain ⟨K, n, hK, hk, hn⟩ := nodeVal_bytes_head W.nodes W.values hx
  have h1 := congrArg List.head? he
  cases x with
  | nil => simp at hK
  | cons a xs =>
    simp only [List.head?_cons, Option.some.injEq] at hK
    subst hK
    simp only [Msg.toFp, List.map_cons, List.head?_cons, Option.some.injEq] at h1
    have := ZkFormal.Near.Link.ofNat_inj (by unfold msgId P; rcases hk with rfl | rfl | rfl <;>
      simp [K_NPRE, K_NPOST, K_VPRE] <;> omega) (by unfold P; omega) h1
    unfold msgId at this
    rcases hk with rfl | rfl | rfl <;> simp [K_NPRE, K_NPOST, K_VPRE] at this <;> omega

end ZkFormal.NearV3.Assembly
