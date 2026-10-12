import ZkFormal.NearV3.Assembly.LinkDict
import ZkFormal.NearV3.Assembly.LinkRidBytes
import ZkFormal.NearV3.Rcpt.Link.RcptRoute
import ZkFormal.NearV3.Render.HonestBalanceRcl
import ZkFormal.NearV3.Rcpt.Candidates.NativeSourceDictionary
import ZkFormal.NearV3.Rcpt.Candidates.NativeAppliedBinding
import ZkFormal.NearV3.Rcpt.Candidates.NativeOccurrence
import ZkFormal.NearV3.Rcpt.Candidates.DedupSourceVerify

/-!
# ZkFormal.NearV3.Assembly.LinkSource — `GoodV3.source` from the records (table 20 = `SrcpDD`)

With `d = dictOf p r` (first-occurrence native dictionary over the records):

* `src_count` — the `SRC` balance: table 20 receives exactly the public records
  `Public.sourceRecords p` (`[j, dup byte, rep] ++ root`);
* `idx_match` — two canonical index-headed message lists with equal counts are equal; it gives
  `src_bind` (block `i` is source `i`: `dup`/`rep` bits, root; and every public `dup` byte is
  `≤ 1`, i.e. equal keys have equal metadata) and `rcl_bind` (block `i` ↔ receipt list `i`,
  `L` = its encoded length);
* the leaf of a computed block hashes its list (`list_sha_native`), its path the public root
  (`DedupProof.source_verifyReceiptProof_of_sha`);
* **`source_of_records`**: `SourceSemanticsV3 k (xOf r (dictOf p r))` — `selected`, `shuffle`,
  `dictionaryCount` (`Rcpt.Candidates` native lemmas), `routing` (`route` view of `RcptRoute`),
  **`applied`** (every occurrence of a repeated key has the empty list: `rep ⇒ L = 12`).
-/

namespace ZkFormal.NearV3.Assembly

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.NearV3 NearSpec NearSpecV3

namespace LinkSource

/-! ## Matching index-headed message lists -/

theorem idx_match {A B : List Msg}
    (hA : ∀ i (h : i < A.length), A[i].head? = some i) (hB : ∀ i (h : i < B.length), B[i].head? = some i)
    (cA : ∀ x ∈ A, Link.Canon x) (cB : ∀ x ∈ B, Link.Canon x)
    (hc : ∀ m, cnt A m = cnt B m) : A = B := by
  have side : ∀ {X Y : List Msg}, (∀ i (h : i < X.length), X[i].head? = some i) →
      (∀ i (h : i < Y.length), Y[i].head? = some i) → (∀ x ∈ X, Link.Canon x) →
      (∀ x ∈ Y, Link.Canon x) → (∀ m, cnt X m = cnt Y m) →
      ∀ i (h : i < X.length), ∃ h' : i < Y.length, Y[i] = X[i] := by
    intro X Y hX hY cX cY hc i hi
    have hm : X[i].toFp ∈ Y.map Msg.toFp := by
      have := hc X[i].toFp
      unfold cnt at this
      exact List.count_pos_iff.mp (this ▸ List.count_pos_iff.mpr (List.mem_map_of_mem (List.getElem_mem hi)))
    obtain ⟨y, hy, he⟩ := List.mem_map.mp hm
    have hyx := Link.toFp_inj (cY y hy) (cX _ (List.getElem_mem hi)) he
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hy
    have h1 := hY k hk
    rw [hyx, hX i hi, Option.some.injEq] at h1
    subst h1
    exact ⟨hk, hyx⟩
  have hl : A.length = B.length := by
    rcases Nat.lt_trichotomy A.length B.length with h | h | h
    · obtain ⟨h', -⟩ := side hB hA cB cA (fun m => (hc m).symm) A.length h
      omega
    · exact h
    · obtain ⟨h', -⟩ := side hA hB cA cB hc B.length h
      omega
  apply List.ext_getElem hl
  intro i h1 h2
  obtain ⟨h', he⟩ := side hA hB cA cB hc i h1
  exact he.symm

variable {cb : Bytes} {h : Hint} {p : Prep} {oh : Nat} {tr : Trace Fp} {r : V3Records}

local notation "PUB" => ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)

/-! ## The `SRC` balance -/

theorem src_recvs (bs : List SrcpB) (reps : List Bool) :
    (ddTraffic bs reps).recvs B_SRC =
      (bs.zip reps).map fun v => Rcpt.Candidates.SourcePublic.viewRecord v.1 v.2 := by
  simp only [ddTraffic, show B_SRC ≠ B_SIZE by decide, ite_false]
  induction bs generalizing reps with
  | nil => simp
  | cons B bs ih =>
    cases reps with
    | nil => simp
    | cons rp reps =>
      simp only [List.zip_cons_cons, List.flatMap_cons, List.map_cons, ih]
      congr 1
      cases hd : B.dup <;>
        simp [Rcpt.Candidates.DedupRender.blockMsgs, Rcpt.Candidates.DedupRender.rootMsgs, srcpLeafMsgs,
          srcpItemMsgs, Rcpt.Candidates.SourcePublic.viewRecord, hd, B_SRC, B_BYTES, B_DIGEST, B_RCL]

/-- **The `SRC` balance**: table 20 receives exactly the public source records. -/
theorem src_count (hp : prepD0 cb h = .ok p) (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < ZkFormal.Algebra.P)
    (hH : HoldsP nearAirV3 PUB tr) (T : V3RecordsTraffic PUB tr r) :
    ∀ m, cnt ((ddTraffic r.srcp r.srcpRep).recvs B_SRC) m = cnt (ZkFormal.NearV3.Public.sourceRecords p) m := by
  intro m
  have hroots := prepD0_roots hp
  have hl256 : (ZkFormal.NearV3.Public.preparedBytes p oh).length < 256 ^ 4 := by
    unfold ZkFormal.Algebra.P at hsz; omega
  have hI := ZkFormal.NearV3.Public.prepared_receipt_index nearAirV3 p oh rfl hroots
    (prepD0_source_roots hp) hl256
  have hc := (ZkFormal.NearV3.Public.prepared_pubIdx nearAirV3 p oh rfl hroots
    (prepD0_source_roots hp) hl256).count B_SRC true m
  rw [hI.1] at hc
  have hb := hH.balance B_SRC m
  rw [pubCount_noside (sd := false) (by decide +kernel), hc,
    busCount_users (U := [T_SRCP]) (by decide) (by decide) (by decide +kernel),
    busCount_users (U := [T_SRCP]) (by decide) (by decide) (by decide +kernel)] at hb
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at hb
  rw [show isAt T_SRCP = Rcpt.Candidates.DedupTable.interactions from rfl, tcnt_of_traffic T.srcp,
    tcnt_of_traffic T.srcp] at hb
  simp only [tcnt, ite_true, Bool.false_eq_true, ite_false] at hb
  have hs0 : (ddTraffic r.srcp r.srcpRep).sends B_SRC = [] := by
    simp [ddTraffic, Rcpt.Candidates.DedupRender.blockMsgs, Rcpt.Candidates.DedupRender.rootMsgs,
      srcpLeafMsgs, srcpItemMsgs, B_SRC, B_BYTES, B_DIGEST, B_RCL, B_SIZE]
  rw [hs0] at hb
  simp only [List.map_nil, List.count_nil, Nat.zero_add] at hb
  simp only [ZkFormal.Near.cnt, ZkFormal.NearV3.Assembly.cnt]
  first | exact hb | exact hb.symm

/-! ## Blocks ↔ public sources -/

theorem srcRecords_head (p : Prep) :
    ∀ i (h : i < (ZkFormal.NearV3.Public.sourceRecords p).length),
      (ZkFormal.NearV3.Public.sourceRecords p)[i].head? = some i := by
  intro i hi; simp [ZkFormal.NearV3.Public.sourceRecords]

theorem dupByte_le (sources : List SrcList) (j : Nat) :
    ZkFormal.NearV3.Public.sourceDupByte sources j ≤ 2 := by
  unfold ZkFormal.NearV3.Public.sourceDupByte; split <;> (try split) <;> omega

theorem srcRecords_canon (hp : prepD0 cb h = .ok p) :
    ∀ x ∈ ZkFormal.NearV3.Public.sourceRecords p, Link.Canon x := by
  intro x hx
  simp only [ZkFormal.NearV3.Public.sourceRecords, List.mem_map, List.mem_range] at hx
  obtain ⟨j, hj, rfl⟩ := hx
  have hn := Rcpt.Candidates.prepD0_source_count hp
  have h2 := dupByte_le p.lists j
  intro y hy
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.mem_map] at hy
  rcases hy with rfl | rfl | rfl | ⟨b, -, rfl⟩
  · unfold ZkFormal.Algebra.P; omega
  · unfold ZkFormal.Algebra.P; omega
  · split <;> (unfold ZkFormal.Algebra.P; omega)
  · have := b.toNat_lt; unfold ZkFormal.Algebra.P; omega

theorem view_head {bs : List SrcpB} {reps : List Bool} (W : DDWf bs reps) :
    ∀ i (h : i < ((bs.zip reps).map fun v => Rcpt.Candidates.SourcePublic.viewRecord v.1 v.2).length),
      ((bs.zip reps).map fun v => Rcpt.Candidates.SourcePublic.viewRecord v.1 v.2)[i].head? = some i := by
  intro i hi
  simp only [List.length_map, List.length_zip] at hi
  simp [Rcpt.Candidates.SourcePublic.viewRecord, W.j i (by omega)]

/-- **Block `i` is source `i`** (records equal). -/
theorem src_match (hp : prepD0 cb h = .ok p) (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < ZkFormal.Algebra.P)
    (hH : HoldsP nearAirV3 PUB tr) (T : V3RecordsTraffic PUB tr r) (W : V3RecordsWf PUB r) :
    (r.srcp.zip r.srcpRep).map (fun v => Rcpt.Candidates.SourcePublic.viewRecord v.1 v.2) =
      ZkFormal.NearV3.Public.sourceRecords p :=
  idx_match (view_head W.srcp) (srcRecords_head p)
    (by intro x hx; obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx; exact W.srcp.canon v hv)
    (srcRecords_canon hp)
    (fun m => by rw [← src_recvs]; exact src_count hp hsz hH T m)

/-- Facts of one block from the public match. -/
theorem src_view (hp : prepD0 cb h = .ok p) (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < ZkFormal.Algebra.P)
    (hH : HoldsP nearAirV3 PUB tr) (T : V3RecordsTraffic PUB tr r) (W : V3RecordsWf PUB r)
    {v : SrcpB × Bool} (hv : v ∈ r.srcp.zip r.srcpRep) :
    v.1.j < p.lists.length ∧ v.1.dup.toNat = ZkFormal.NearV3.Public.sourceDupByte p.lists v.1.j ∧
      v.2 = ZkFormal.NearV3.Public.sourceRep p.lists v.1.j ∧
      v.1.root = (p.lists.getD v.1.j ⟨[],0,[]⟩).root.map UInt8.toNat := by
  have hm : Rcpt.Candidates.SourcePublic.viewRecord v.1 v.2 ∈ ZkFormal.NearV3.Public.sourceRecords p := by
    rw [← src_match hp hsz hH T W]; exact List.mem_map_of_mem hv
  obtain ⟨B, rp⟩ := v
  simp only [ZkFormal.NearV3.Public.sourceRecords, List.mem_map, List.mem_range] at hm
  obtain ⟨j, hj, he⟩ := hm
  simp only [Rcpt.Candidates.SourcePublic.viewRecord, List.cons_append, List.nil_append,
    List.cons.injEq] at he
  obtain ⟨h1, h2, h3, h4⟩ := he
  subst h1
  refine ⟨hj, h2.symm, ?_, h4.symm⟩
  show rp = ZkFormal.NearV3.Public.sourceRep p.lists B.j
  revert h3
  cases rp <;> cases ZkFormal.NearV3.Public.sourceRep p.lists B.j <;> simp

theorem src_length (hp : prepD0 cb h = .ok p) (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < ZkFormal.Algebra.P)
    (hH : HoldsP nearAirV3 PUB tr) (T : V3RecordsTraffic PUB tr r) (W : V3RecordsWf PUB r) :
    r.srcp.length = p.lists.length := by
  have := congrArg List.length (src_match hp hsz hH T W)
  simpa [ZkFormal.NearV3.Public.sourceRecords, W.srcp.len] using this

theorem src_dupByte (hp : prepD0 cb h = .ok p) (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < ZkFormal.Algebra.P)
    (hH : HoldsP nearAirV3 PUB tr) (T : V3RecordsTraffic PUB tr r) (W : V3RecordsWf PUB r) :
    ∀ j < p.lists.length, ZkFormal.NearV3.Public.sourceDupByte p.lists j ≤ 1 := by
  intro j hj
  have hm : ([j, ZkFormal.NearV3.Public.sourceDupByte p.lists j,
      if ZkFormal.NearV3.Public.sourceRep p.lists j then 1 else 0] ++
      (p.lists.getD j ⟨[],0,[]⟩).root.map UInt8.toNat) ∈
      (r.srcp.zip r.srcpRep).map (fun v => Rcpt.Candidates.SourcePublic.viewRecord v.1 v.2) := by
    rw [src_match hp hsz hH T W]
    simp only [ZkFormal.NearV3.Public.sourceRecords, List.mem_map, List.mem_range]
    exact ⟨j, hj, rfl⟩
  obtain ⟨v, -, he⟩ := List.mem_map.mp hm
  simp only [Rcpt.Candidates.SourcePublic.viewRecord, List.cons_append, List.nil_append,
    List.cons.injEq] at he
  rw [← he.2.1]
  cases v.1.dup <;> simp

/-- Public `dup` bytes `≤ 1` make the source metadata consistent (equal keys: equal shard and root). -/
theorem consistent_pair (sources : List SrcList)
    (hb1 : ∀ j < sources.length, ZkFormal.NearV3.Public.sourceDupByte sources j ≤ 1)
    {a b : Nat} (hab : a < b) (hb : b < sources.length) (hk : sources[a].key = sources[b].key) :
    sources[a].fromShard = sources[b].fromShard ∧ sources[a].root = sources[b].root := by
  have hgd : sources.getD b ⟨[],0,[]⟩ = sources[b] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hb, Option.getD_some]
  have hmem : sources[a] ∈ sources.take b :=
    List.mem_iff_getElem.mpr ⟨a, by simp; omega, by simp⟩
  have hd : ZkFormal.NearV3.Public.sourceDup sources b = true := by
    unfold ZkFormal.NearV3.Public.sourceDup
    rw [List.any_eq_true]
    exact ⟨sources[a], hmem, by rw [hgd, hk]; simp⟩
  have hc : ZkFormal.NearV3.Public.sourceConsistent sources b = true := by
    have := hb1 b hb
    unfold ZkFormal.NearV3.Public.sourceDupByte at this
    rw [hd] at this
    cases hcc : ZkFormal.NearV3.Public.sourceConsistent sources b
    · rw [hcc] at this; simp at this
    · rfl
  unfold ZkFormal.NearV3.Public.sourceConsistent at hc
  rw [List.all_eq_true] at hc
  have := hc _ hmem
  rw [hgd, hk] at this
  simpa using this

theorem metadata_of_dupByte (sources : List SrcList)
    (hb1 : ∀ j < sources.length, ZkFormal.NearV3.Public.sourceDupByte sources j ≤ 1) :
    Rcpt.Candidates.sourceMetadataConsistent sources = true := by
  simp only [Rcpt.Candidates.sourceMetadataConsistent, List.all_eq_true]
  intro s hs t ht
  obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hs
  obtain ⟨b, hb, rfl⟩ := List.getElem_of_mem ht
  by_cases hk : sources[a].key = sources[b].key
  · rcases Nat.lt_trichotomy a b with hab | rfl | hab
    · obtain ⟨h1, h2⟩ := consistent_pair sources hb1 hab hb hk
      simp [h1, h2]
    · simp
    · obtain ⟨h1, h2⟩ := consistent_pair sources hb1 hab ha hk.symm
      simp [h1, h2]
  · simp [hk]

/-! ## Blocks ↔ receipt lists (`RCL`) -/

theorem enc_ne_nil (x : RcptE) : x.enc ≠ [] := by
  simp [RcptV.enc, RcptV.borshN, u32r]

theorem enc_len (pub : List Fp) (L : ListV3) :
    (RcptLink.listEncoding pub L).length = 12 + (L.rs.map fun x => x.enc.length).sum := by
  simp [RcptLink.listEncoding, RcptLink.list_header_length, List.length_flatMap]

theorem rcl_match (hH : HoldsP nearAirV3 PUB tr) (T : V3RecordsTraffic PUB tr r) (W : V3RecordsWf PUB r) :
    r.srcp.map (fun B => [B.j, B.L]) = (List.range r.lists.length).map (fun j =>
      [j, 12 + ((r.lists.getD j default).rs.map (fun x => x.enc.length)).sum]) := by
  have key : (ddTraffic r.srcp r.srcpRep).recvs B_RCL = rcptSends3 PUB r.lists B_RCL := by
   apply idx_match
   · intro i hi
     have hi' : i < r.srcp.length := by simpa [DDView.rcl_recvs _ _ W.srcp.len] using hi
     simp only [DDView.rcl_recvs _ _ W.srcp.len, List.getElem_map]
     simp [W.srcp.j i hi']
   · intro i hi
     simp only [RcptSkeleton.rcl_sends] at hi ⊢
     simp
   · intro x hx
     rw [DDView.rcl_recvs _ _ W.srcp.len] at hx
     obtain ⟨B, hB, rfl⟩ := List.mem_map.mp hx
     intro y hy
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
     rcases hy with rfl | rfl
     · exact W.srcp.j_lt hB
     · exact W.srcp.L_lt hB
   · intro x hx
     rw [RcptSkeleton.rcl_sends] at hx
     obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
     have hj := List.mem_range.mp hj
     intro y hy
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
     have hl := W.listsCount.1
     rcases hy with rfl | rfl
     · unfold ZkFormal.Algebra.P; omega
     · have := LinkRidBytes.listEncoding_lt W.lists W.listsCount.2 hj
       rw [enc_len] at this
       rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
       exact this
   · intro m
     have hb := bal_users hH (b := B_RCL) (U := [T_RCPT, T_SRCP]) (by decide) (by decide)
       (by decide +kernel) (by decide +kernel) m
     simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at hb
     rw [show isAt T_RCPT = RcptV3.interactions from rfl, tcnt_of_traffic T.lists, tcnt_of_traffic T.lists,
       show isAt T_SRCP = Rcpt.Candidates.DedupTable.interactions from rfl, tcnt_of_traffic T.srcp,
       tcnt_of_traffic T.srcp] at hb
     have r0 : rcptRecvs3 r.lists B_RCL = [] := by
       simp [rcptRecvs3, rRecvs, B_DIGEST, B_FINAL, B_MEM, B_RCL, B_SREC, B_AKC, B_BND]
     simp only [tcnt, ite_true, Bool.false_eq_true, ite_false, rcptTraffic3, r0, DDView.rcl_sends,
       List.map_nil, List.count_nil, Nat.add_zero, Nat.zero_add] at hb
     simp only [ZkFormal.Near.cnt, ZkFormal.NearV3.Assembly.cnt]
     omega
  rw [DDView.rcl_recvs _ _ W.srcp.len, RcptSkeleton.rcl_sends] at key
  exact key

theorem rcl_length (hH : HoldsP nearAirV3 PUB tr) (T : V3RecordsTraffic PUB tr r) (W : V3RecordsWf PUB r) :
    r.srcp.length = r.lists.length := by
  simpa using congrArg List.length (rcl_match hH T W)

theorem rcl_L (hH : HoldsP nearAirV3 PUB tr) (T : V3RecordsTraffic PUB tr r) (W : V3RecordsWf PUB r)
    {i : Nat} (hi : i < r.srcp.length) :
    ∃ hl : i < r.lists.length, r.srcp[i].L = (RcptLink.listEncoding PUB r.lists[i]).length := by
  have hl : i < r.lists.length := by rw [← rcl_length hH T W]; exact hi
  refine ⟨hl, ?_⟩
  have := congrArg (fun l => l[i]?) (rcl_match hH T W)
  simp only [List.getElem?_map, List.getElem?_eq_getElem hi, List.getElem?_range hl, Option.map_some,
    Option.some.injEq, List.cons.injEq] at this
  rw [enc_len, this.2.1, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some]

/-- A block with `L = 12` has the empty receipt list. -/
theorem twelve_empty (hH : HoldsP nearAirV3 PUB tr) (T : V3RecordsTraffic PUB tr r) (W : V3RecordsWf PUB r)
    {i : Nat} (hi : i < r.srcp.length) (h12 : r.srcp[i].L = 12) :
    ∃ hl : i < r.lists.length, r.lists[i].rs = [] := by
  obtain ⟨hl, hL⟩ := rcl_L hH T W hi
  refine ⟨hl, ?_⟩
  rw [h12, enc_len] at hL
  cases hrs : r.lists[i].rs with
  | nil => rfl
  | cons x xs =>
    rw [hrs] at hL
    have := enc_ne_nil x
    have hx : 0 < x.enc.length := List.length_pos_iff.mpr this
    simp only [List.map_cons, List.sum_cons] at hL
    omega

/-! ## SHA: the source table's `BYTES` among the other senders -/

/-- The `BYTES` senders other than table 20. -/
def othersSRC (tr : Trace Fp) (pub : List Fp) (r : V3Records) : List Msg :=
  nodeSends3 r.nodes B_BYTES ++ valSends r.values B_BYTES ++ (upsTraffic r.ups).sends B_BYTES ++
    acctV3Sends r.accts B_BYTES ++ rcptSends3 pub r.lists B_BYTES ++
    (mrkTrafficE pub r.mrkE r.mrk).sends B_BYTES ++ (codecBytes tr pub).map fun x => x.map Fp.toNat

theorem sha_le_src {pub : List Fp} (hH : HoldsP nearAirV3 pub tr) (T : V3RecordsTraffic pub tr r)
    (m : List Fp) :
    shaU tr pub false B_BYTES m ≤
      ZkFormal.Near.cnt ((ddTraffic r.srcp r.srcpRep).sends B_BYTES ++ othersSRC tr pub r) m := by
  have h := bytes_balance hH T m
  have e : ZkFormal.Near.cnt ((ddTraffic r.srcp r.srcpRep).sends B_BYTES ++ othersSRC tr pub r) m =
      ZkFormal.Near.cnt (nodeSends3 r.nodes B_BYTES ++ valSends r.values B_BYTES) m +
        (otherBytes tr pub r).count m := by
    unfold ZkFormal.Near.cnt othersSRC otherBytes otherRecBytes
    simp only [List.map_append, List.count_append, List.map_map]
    rw [show (Msg.toFp ∘ fun x : List Fp => x.map Fp.toNat) = id from funext toFp_map_toNat, List.map_id]
    omega
  omega

theorem othersSRC_kinds (hp : prepD0 cb h = .ok p) (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < ZkFormal.Algebra.P)
    (hH : HoldsP nearAirV3 PUB tr) (T : V3RecordsTraffic PUB tr r) (W : V3RecordsWf PUB r) :
    ∀ m ∈ othersSRC tr PUB r, ∀ a, m.head? = some a → a < ZkFormal.Algebra.P ∧ a % 16 ≠ K_SRC := by
  have kin : ∀ {ks : List Nat} {x : Msg}, KindIn ks x → K_SRC ∉ ks → ∀ a, x.head? = some a →
      a < ZkFormal.Algebra.P ∧ a % 16 ≠ K_SRC := by
    intro ks x hk hK a ha
    obtain ⟨h1, h2⟩ := hk a ha
    exact ⟨h1, fun he => hK (he ▸ h2)⟩
  have nv : ∀ {K n : Nat}, (K = K_NPRE ∨ K = K_NPOST ∨ K = K_VPRE) → n < 2 ^ 22 →
      msgId K n < ZkFormal.Algebra.P ∧ msgId K n % 16 ≠ K_SRC := by
    intro K n hK hn
    unfold msgId ZkFormal.Algebra.P
    rcases hK with rfl | rfl | rfl <;> simp only [K_NPRE, K_NPOST, K_VPRE, K_SRC] <;> omega
  intro m hm a ha
  simp only [othersSRC, List.mem_append] at hm
  rcases hm with (((((hm | hm) | hm) | hm) | hm) | hm) | hm
  · obtain ⟨K, n, hh, hK, hn⟩ := nodeVal_bytes_head W.nodes W.values (List.mem_append_left _ hm)
    rw [ha, Option.some.injEq] at hh; subst hh
    exact nv hK hn
  · obtain ⟨K, n, hh, hK, hn⟩ := nodeVal_bytes_head W.nodes W.values (List.mem_append_right _ hm)
    rw [ha, Option.some.injEq] at hh; subst hh
    exact nv hK hn
  · exact kin (upsKindIn_of hp hsz hH T W m hm) (by decide) a ha
  · exact kin (acctKindIn hH T W m hm) (by decide) a ha
  · exact kin (rcptKindIn W.listsCount.1 W.listsCount.2 m hm) (by decide) a ha
  · exact kin (mrkKindIn W (pubNat_pubOf_lt _) m hm) (by decide) a ha
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hm
    cases hyh : y.head? with
    | none => simp [List.head?_map, hyh] at ha
    | some e =>
      simp only [List.head?_map, hyh, Option.map_some, Option.some.injEq] at ha
      subst ha
      have := codecKindIn hp hsz hH y hy e hyh
      exact ⟨Fp.toNat_lt e, by rw [this]; decide⟩

/-! ## Verification of every first occurrence -/

theorem first_verified (hp : prepD0 cb h = .ok p) (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < ZkFormal.Algebra.P)
    (hH : HoldsP nearAirV3 PUB tr) (T : V3RecordsTraffic PUB tr r) (W : V3RecordsWf PUB r)
    (i : Nat) (hi : i < p.lists.length) (hd : ZkFormal.NearV3.Public.sourceDup p.lists i = false) :
    verifyReceiptProof (p.lists.getD i ⟨[],0,[]⟩).root
      (Rcpt.Candidates.nativeEntryAt p.lists p.hdr.own r.lists r.srcp i).entry = true := by
  have hib : i < r.srcp.length := by rw [src_length hp hsz hH T W]; exact hi
  have hzl : i < (r.srcp.zip r.srcpRep).length := by simp [W.srcp.len, hib]
  have hv : (r.srcp.zip r.srcpRep)[i] ∈ r.srcp.zip r.srcpRep := List.getElem_mem hzl
  have hv1 : (r.srcp.zip r.srcpRep)[i].1 = r.srcp[i] := by simp
  obtain ⟨-, hdup, -, hroot⟩ := src_view hp hsz hH T W hv
  rw [hv1, W.srcp.j i hib] at hdup hroot
  let B := r.srcp[i]
  have hB : B ∈ r.srcp := List.getElem_mem hib
  have hBd : B.dup = false := by
    have h0 : ZkFormal.NearV3.Public.sourceDupByte p.lists i = 0 := by
      simp [ZkFormal.NearV3.Public.sourceDupByte, hd]
    rw [h0] at hdup
    show r.srcp[i].dup = false
    cases hh : r.srcp[i].dup
    · rfl
    · rw [hh] at hdup; simp at hdup
  obtain ⟨hl, hL⟩ := rcl_L hH T W hib
  -- the leaf hashes receipt list `i`
  have hdig : 0 < shaU tr PUB true B_DIGEST
      (digMsg (msgId K_RC i) (RcptLink.listEncoding PUB r.lists[i]).length B.leaf).toFp := by
    apply digest_provided hH (t := T_SRCP) (by decide)
    rw [show isAt T_SRCP = Rcpt.Candidates.DedupTable.interactions from rfl, tcnt_of_traffic T.srcp]
    simp only [tcnt, Bool.false_eq_true, ite_false]
    apply List.count_pos_iff.mpr
    apply List.mem_map_of_mem
    have := DDView.leaf_recv W.srcp.len hB hBd
    rw [show B.j = i from W.srcp.j i hib, show B.L = _ from hL] at this
    exact this
  have hBw : Rcpt.Candidates.DedupProof.BlockWf B := by
    have hb := W.srcp.block B hB
    simpa only [hBd, Bool.false_eq_true, ite_false] using hb
  have hshaR := LinkRidBytes.shaFacts_cover (shaU_facts hH) _ (LinkRidBytes.sha_le_rc hH T)
  have hleaf := RcptLink.list_sha_native W.lists W.listsCount.1 W.listsCount.2 hshaR
    (LinkRidBytes.othersRC tr PUB r) (fun m => if_pos rfl) (LinkRidBytes.othersRC_kinds hp hsz hH T W) hl
    (LinkRidBytes.listEncoding_lt W.lists W.listsCount.2 hl)
    (fun v hv => hBw.canon.2.2.1 v (List.mem_append_right _ hv)) hdig
    (RcptLink.prepared_owner p oh (prepD0_roots hp))
  -- the path hashes to the public root
  obtain ⟨e, hc, hrep⟩ := T.srcpChain
  have hsm : ∀ bb sd, Rcpt.Candidates.DedupProof.sourceMsgs tr T_SRCP r.srcp bb sd =
      if sd then (ddTraffic r.srcp r.srcpRep).sends bb else (ddTraffic r.srcp r.srcpRep).recvs bb := by
    intro bb sd; rw [DDView.sourceMsgs_eq, hrep]
  have hshaS := LinkRidBytes.shaFacts_cover (shaU_facts hH)
    (Rcpt.Candidates.DedupProof.sourceMsgs tr T_SRCP r.srcp B_BYTES true ++ othersSRC tr PUB r)
    (fun m => by rw [hsm]; exact sha_le_src hH T m)
  have hver := Rcpt.Candidates.DedupProof.source_verifyReceiptProof_of_sha (tr := tr) (tt := T_SRCP)
    W.srcp.payload hshaS (othersSRC tr PUB r) (fun m => if_pos rfl) (othersSRC_kinds hp hsz hH T W)
    (fun m hm => by
      rw [hsm] at hm
      apply digest_provided hH (t := T_SRCP) (by decide)
      rw [show isAt T_SRCP = Rcpt.Candidates.DedupTable.interactions from rfl, tcnt_of_traffic T.srcp]
      simp only [tcnt, Bool.false_eq_true, ite_false]
      exact List.count_pos_iff.mpr (List.mem_map_of_mem hm))
    hB hBd (Rcpt.Candidates.nativeEntryAt p.lists p.hdr.own r.lists r.srcp i).entry
    (by
      simp only [Rcpt.Candidates.nativeEntryAt, Rcpt.Candidates.DedupProof.nativeSourceEntry,
        SourceEntryV3.entry, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some]
      exact hleaf)
    (by
      simp only [Rcpt.Candidates.nativeEntryAt, Rcpt.Candidates.DedupProof.nativeSourceEntry,
        SourceEntryV3.entry, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hib, Option.getD_some]
      rfl)
  rw [hroot, Link.toBytes_map_toNat'] at hver
  exact hver

/-! ## Routing -/

theorem routing (hp : prepD0 cb h = .ok p) (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < ZkFormal.Algebra.P)
    (hH : HoldsP nearAirV3 PUB tr) (T : V3RecordsTraffic PUB tr r) (W : V3RecordsWf PUB r)
    {k : WalkD0} (hw : walkD0 cb = .ok k) :
    ∀ x ∈ flatR r.lists, k.L.shardOf x.toRcptV.toReceipt.receiverId = k.H.shardId := by
  intro x hx
  have hb : ∀ m, ZkFormal.Near.cnt (r.bnds.map BndE.rec4) m =
      ZkFormal.Near.cnt (ZkFormal.NearV3.Public.boundaryRecords
        (RoutingBoundedLayout.boundedPrep p k.L k.H.shardId)) m := by
    rw [RcptLink.boundedPrep_self hp hw]; exact RcptLink.bndp_count hp hsz hH T
  have hn := RcptLink.boundaryRequests_bound W.lists W.listsCount.2
  have hp' := RcptLink.bnd_lookup_provider r.bnds _ W.bnds
    (RcptLink.boundaryRequests_canonical W.lists W.listsQ) hn (RcptLink.bnd_lookup_perm hH T)
  exact RcptLink.bounded_prepared_native_routing hp hw W.lists r.bnds W.bnds hb hp' hx

end LinkSource

/-- **`GoodV3.source`** for the records' views with the first-occurrence dictionary. -/
theorem source_of_records {cb : Bytes} {h : Hint} {p : Prep} {oh : Nat} {tr : Trace Fp} {r : V3Records}
    {k : WalkD0} (hp : prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < ZkFormal.Algebra.P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    (hw : walkD0 cb = .ok k) :
    SourceSemanticsV3 k (xOf r (dictOf p r)) := by
  have hn := Rcpt.Candidates.prepD0_source_count hp
  have hmeta := LinkSource.metadata_of_dupByte p.lists (LinkSource.src_dupByte hp hsz hH T W)
  have hv := LinkSource.first_verified hp hsz hH T W
  have ho := prepD0_source_owner hp hw
  have hsel : ∀ B ∈ k.sourceBlks, ∀ x ∈ B.slots, x.1.heightIncluded == B.hdr.height →
      ∃ e : SourceEntryV3, Sum.inl e ∈ dictOf p r ∧
        lookupLast (chunkHash x.1.inner x.2.encodedMerkleRoot) ((dictOf p r).map DictionaryEntryV3.entry) =
          some e.entry ∧
        e.fromShard = x.2.shardId ∧ e.toShard = k.H.shardId ∧
        verifyReceiptProof x.2.prevOutgoingReceiptsRoot e.entry = true := by
    intro B hB x hx hnew
    have hm := Rcpt.Candidates.prepD0_source_slot_mem hp hw hB hx hnew
    obtain ⟨e, he, hl, hf, ht, hv'⟩ := Rcpt.Candidates.nativeDictionary_selected p.lists p.hdr.own r.lists
      r.srcp (Rcpt.Candidates.nativeFillers p.lists) (Rcpt.Candidates.nativeFillers_fresh p.lists) hmeta hv hm
    exact ⟨e, he, hl, hf, ht.trans ho, hv'⟩
  have facts : Rcpt.Candidates.SourceDictionaryFacts k (xOf r (dictOf p r)).dictionary := by
    refine ⟨hsel, ?_, ?_⟩
    · apply Rcpt.Candidates.prepD0_selected_shuffle hp hw _ k.H.shardId
      intro B hB x hx hnew
      obtain ⟨e, _, hl, hf, ht, hv'⟩ := hsel B hB x hx hnew
      exact ⟨e.entry, hl, hf, ht, hv'⟩
    · show (distinctKeys ((dictOf p r).map DictionaryEntryV3.entry)).length = _
      rw [dictOf, Rcpt.Candidates.nativeFillers_dictionary_count p.lists hn,
        Rcpt.Candidates.prepD0_source_keys_count hp hw]
  have hr := LinkSource.routing hp hsz hH T W hw
  have hlen : p.lists.length = r.lists.length :=
    (LinkSource.src_length hp hsz hH T W).symm.trans (LinkSource.rcl_length hH T W)
  have hocc := Rcpt.Candidates.nativeDictionary_ordered_receipts p.lists p.hdr.own r.lists r.srcp
    (Rcpt.Candidates.nativeFillers p.lists) (Rcpt.Candidates.nativeFillers_fresh p.lists)
    (by
      intro i hi hrep
      have hib : i < r.srcp.length := by rw [LinkSource.src_length hp hsz hH T W]; exact hi
      have hzl : i < (r.srcp.zip r.srcpRep).length := by simp [W.srcp.len, hib]
      have hvm : (r.srcp.zip r.srcpRep)[i] ∈ r.srcp.zip r.srcpRep := List.getElem_mem hzl
      obtain ⟨-, -, hrp, -⟩ := LinkSource.src_view hp hsz hH T W hvm
      have hj : (r.srcp.zip r.srcpRep)[i].1.j = i := by simp [W.srcp.j i hib]
      rw [hj] at hrp
      have h12 := W.srcp.rep _ hvm (hrp.trans hrep)
      simp only [List.getElem_zip] at h12
      obtain ⟨hl, hrs⟩ := LinkSource.twelve_empty hH T W hib h12
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some]
      exact hrs)
    hlen k.L k.H.shardId hr
  exact Rcpt.Candidates.nativeDictionary_prepared_sourceSemantics hp hw r.srcp
    (Rcpt.Candidates.nativeFillers p.lists) rfl facts hr hocc


/-- The `GoodV3` fields left after `source` and `dictDepth` (closed for `d = dictOf p r`). -/
structure Rest2FieldsV3 (B : Nat) (cb : Bytes) (k : WalkD0) (x : ExtV3) : Prop where
  shape : V3.D0Shape (stateWitnessOfV3 k x)
  witnessBytes : (V3.encodeSW (stateWitnessOfV3 k x)).length ≤ 8388608
  canonicalScheduler : (reads0f k (stateWitnessOfV3 k x)).all (canonical0f k.L) = true
  unfoldedBytes : unfoldBytes cb (witnessOfV3 k x) ≤ B
  chachaWords : chachaWords cb (witnessOfV3 k x) ≤ W0

/-- **What remains of the link** with the dictionary fixed to `dictOf p r`. -/
def LinkRest2V3Stmt (B : Nat) : Prop :=
  ∀ (cb : Bytes) (h : Hint) (p : Prep) (oh : Nat) (tr : Trace Fp) (r : V3Records) (k : WalkD0),
    prepD0 cb h = .ok p → walkD0 cb = .ok k → ClaimFieldsV3 k →
    (ZkFormal.NearV3.Public.preparedBytes p oh).length < ZkFormal.Algebra.P →
    HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr →
    V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r →
    V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r →
    ZkFormal.Near.ShaFacts
      (shaCountAt tr (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) T_SHA_T true)
      (shaCountAt tr (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) T_SHA_T false) →
    ZkFormal.Near.ShaFacts
      (shaCountAt tr (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) T_SHA_R true)
      (shaCountAt tr (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) T_SHA_R false) →
    V3Balance (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r →
    Rest2FieldsV3 B cb k (xOf r (dictOf p r))

/-- **`source` and `dictDepth` closed**: `LinkRest2V3Stmt B → LinkRestV3Stmt B`. -/
theorem linkRest_of_rest2 {B : Nat} (hR : LinkRest2V3Stmt B) : LinkRestV3Stmt B := by
  intro cb h p oh tr r k hp hw C hsz hH W T hs1 hs2 hb
  have R := hR cb h p oh tr r k hp hw C hsz hH W T hs1 hs2 hb
  exact ⟨dictOf p r, ⟨R.shape, R.witnessBytes, source_of_records hp hsz hH T W hw, R.canonicalScheduler,
    R.unfoldedBytes, R.chachaWords, dictDepth_of_records W⟩⟩

end ZkFormal.NearV3.Assembly
