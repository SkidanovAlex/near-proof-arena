import ZkFormal.NearV3.Assembly.LinkSha
import ZkFormal.NearV3.Rcpt.Link.ListByteIds
import ZkFormal.NearV3.Rcpt.Link.SourceIsolation
import ZkFormal.NearV3.Candidates.MerkleAlias
import ZkFormal.Near.Link.MrkFacts
import ZkFormal.NearV3.Sched.Link.SoundSha
import ZkFormal.NearV3.Sched.Link.CodecSV
import ZkFormal.NearV3.Public.SchedulerIndex

/-!
# ZkFormal.NearV3.Assembly.LinkShaKinds — the `BYTES` kind registry (`OthersKinds`)

`shaHyp_of` (`LinkSha.lean`) needs `OthersKinds`: every `BYTES` message sent by a table other
than node / val has a canonical id whose kind (`id mod 16`) is not `K_NPRE = 7`,
`K_NPOST = 8` or `K_VPRE = 9`.  The other senders and their kinds:

| table | id | kind |
|---|---|---|
| rcpt | `msgId K_RC j`, `K_RF`, `msgId K_PEO r`, `msgId K_LEAF r`, `msgId K_RID r` | 1, 2, 3, 4, 5 |
| mrk  | `msgId K_MRK i` | 6 |
| acct | `msgId K_VPOST a.k` | 10 |
| codec (raw) | `11 + 16·τ` | 11 |
| ups  | `upsIdN τ jj = 12 + 16·(512τ + jj)` | 12 |
| srcp | `msgId K_SRC q` | 13 |

`OthersKinds` splits into one statement per sender (`othersKinds_of`); this module proves the
record-level ones whose index bound is available (`srcpKinds`, `rcptKinds` from the list /
receipt counts) and states the rest as `KindsOk` of that table's record messages.
-/

namespace ZkFormal.NearV3.Assembly

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near

/-- A record message has a canonical id of a kind other than `K_NPRE`/`K_NPOST`/`K_VPRE`. -/
def KindOk (x : Msg) : Prop :=
  ∀ a, x.head? = some a → a < P ∧ a % 16 ≠ K_NPRE ∧ a % 16 ≠ K_NPOST ∧ a % 16 ≠ K_VPRE

/-- Every message of a list has `KindOk`. -/
def KindsOk (l : List Msg) : Prop := ∀ x ∈ l, KindOk x

theorem kindOk_toFp {x : Msg} (h : KindOk x) : ∀ a, x.toFp.head? = some a →
    a.toNat % 16 ≠ K_NPRE ∧ a.toNat % 16 ≠ K_NPOST ∧ a.toNat % 16 ≠ K_VPRE := by
  intro a ha
  cases x with
  | nil => simp [Msg.toFp] at ha
  | cons b xs =>
    simp only [Msg.toFp, List.map_cons, List.head?_cons, Option.some.injEq] at ha
    subst ha
    have hb := h b rfl
    rw [Fp.toNat_ofNat, Nat.mod_eq_of_lt hb.1]
    exact hb.2

theorem kindOk_msgId {K n : Nat} {xs : List Nat} (hK : K < 16) (h7 : K ≠ K_NPRE) (h8 : K ≠ K_NPOST)
    (h9 : K ≠ K_VPRE) (hn : msgId K n < P) : KindOk (msgId K n :: xs) := by
  intro a ha
  simp only [List.head?_cons, Option.some.injEq] at ha
  subst ha
  refine ⟨hn, ?_⟩
  have : msgId K n % 16 = K := by unfold msgId; omega
  rw [this]; exact ⟨h7, h8, h9⟩

/-- **`OthersKinds` from the per-sender registries.** -/
theorem othersKinds_of {tr : Trace Fp} {pub : List Fp} {r : V3Records}
    (hU : KindsOk ((ZkFormal.NearV3.upsTraffic r.ups).sends B_BYTES))
    (hR : KindsOk (ZkFormal.NearV3.rcptSends3 pub r.lists B_BYTES))
    (hA : KindsOk (ZkFormal.NearV3.acctV3Sends r.accts B_BYTES))
    (hS : KindsOk ((ZkFormal.NearV3.srcpTraffic r.srcp).sends B_BYTES))
    (hM : KindsOk ((mrkTrafficE pub r.mrkE r.mrk).sends B_BYTES))
    (hC : ∀ y ∈ codecBytes tr pub, ∀ a, y.head? = some a →
      a.toNat % 16 ≠ K_NPRE ∧ a.toNat % 16 ≠ K_NPOST ∧ a.toNat % 16 ≠ K_VPRE) :
    OthersKinds tr pub r := by
  intro y hy
  simp only [otherBytes, otherRecBytes, List.mem_append, List.mem_map] at hy
  rcases hy with ⟨x, hx, rfl⟩ | hy
  · apply kindOk_toFp
    rcases hx with ((((hx | hx) | hx) | hx) | hx)
    · exact hU x hx
    · exact hR x hx
    · exact hA x hx
    · exact hS x hx
    · exact hM x hx
  · exact hC y hy

/-! ## srcp (`K_SRC = 13`) -/

theorem srcpKinds {bs : List ZkFormal.NearV3.SrcpB} (h : ZkFormal.NearV3.SrcpWf bs) :
    KindsOk ((ZkFormal.NearV3.srcpTraffic bs).sends B_BYTES) := by
  intro x hx
  simp only [ZkFormal.NearV3.srcpTraffic, show B_BYTES ≠ ZkFormal.NearV3.B_SIZE by decide, ite_false] at hx
  obtain ⟨C, hC, hx⟩ := List.mem_flatMap.mp hx
  rw [ZkFormal.NearV3.source_block_bytes] at hx
  obtain ⟨p, hp, hx⟩ := List.mem_flatMap.mp hx
  obtain ⟨j, -, rfl⟩ := ZkFormal.NearV3.Link3.mem_emitAt3.mp hx
  exact kindOk_msgId (by decide) (by decide) (by decide) (by decide)
    (ZkFormal.NearV3.source_payload_id_lt h hC hp)

/-! ## rcpt (`K_RC`, `K_RF`, `K_PEO`, `K_LEAF`, `K_RID`) -/

theorem rcptKinds {pub : List Fp} {ls : ZkFormal.NearV3.RcptV3Vs}
    (hl : ls.length ≤ 2 ^ 22) (hr : (ZkFormal.NearV3.flatR ls).length ≤ 2 ^ 22) :
    KindsOk (ZkFormal.NearV3.rcptSends3 pub ls B_BYTES) := by
  intro x hx a ha
  have hc := ZkFormal.NearV3.RcptLink.receipt_bytes_ids hl hr hx ha
  refine ⟨hc, ?_⟩
  -- the kind of every receipt `BYTES` id
  have hk : a % 16 = K_RC ∨ a % 16 = K_RF ∨ a % 16 = K_PEO ∨ a % 16 = K_LEAF ∨ a % 16 = K_RID := by
    simp only [ZkFormal.NearV3.rcptSends3, ite_true, show B_BYTES ≠ ZkFormal.NearV3.B_RCL by decide,
      ite_false, List.append_nil, List.mem_flatMap] at hx
    obtain ⟨j, -, hx⟩ := hx
    have e := fun {id off : Nat} {xs : List Nat} (hm : x ∈ emitAt id off xs) =>
      ZkFormal.NearV3.RcptLink.emitAt_head_eq hm ha
    rcases List.mem_append.mp hx with hx | hx
    · rw [e hx]; left; unfold msgId K_RC; omega
    · obtain ⟨⟨r, off, y⟩, -, hx⟩ := List.mem_flatMap.mp hx
      simp only [ZkFormal.NearV3.rSends, ite_true, List.mem_append] at hx
      rcases hx with (((hx | hx) | hx) | hx) | hx
      · rw [e hx]; left; unfold msgId K_RC; omega
      · split at hx
        · rw [e hx]; right; left; rfl
        · simp at hx
      · rw [e hx]; right; right; left; unfold msgId K_PEO; omega
      · rw [e hx]; right; right; right; left; unfold msgId K_LEAF; omega
      · split at hx
        · rw [e hx]; right; right; right; right; unfold msgId K_RID; omega
        · simp at hx
  simp only [K_RC, K_RF, K_PEO, K_LEAF, K_RID] at hk
  simp only [K_NPRE, K_NPOST, K_VPRE]
  omega

/-- The receipt registry from the counted view (`V3RecordsWf.listsCount`). -/
theorem rcptKinds_of {pub : List Fp} {r : V3Records} (W : V3RecordsWf pub r) :
    KindsOk (ZkFormal.NearV3.rcptSends3 pub r.lists B_BYTES) :=
  rcptKinds W.listsCount.1 W.listsCount.2

/-! ## acct (`K_VPOST = 10`): the slot `a.k` is a value id, via `VSLOT` and `VPARENT` -/

/-- **`VSLOT`**: the `acctV3` slot messages are exactly the node records' written value slots. -/
theorem vslot_bal {pub : List Fp} {tr : Trace Fp} {r : V3Records} (hH : HoldsP nearAirV3 pub tr)
    (T : V3RecordsTraffic pub tr r) (m : List Fp) :
    ((ZkFormal.NearV3.acctV3Sends r.accts B_VSLOT).map Msg.toFp).count m =
      ((ZkFormal.NearV3.nodeRecvs3 r.nodes B_VSLOT).map Msg.toFp).count m := by
  have h := bal_users hH (b := B_VSLOT) (U := [T_NODE, T_ACCT]) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) m
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at h
  rw [node_count T _ _ _ (by decide +kernel), node_count T _ _ _ (by decide +kernel),
    show isAt T_ACCT = ZkFormal.NearV3.AcctV3.interactions from rfl, tcnt_of_traffic T.accts,
    tcnt_of_traffic T.accts] at h
  simp only [tcnt_unfold] at h
  have z1 : ZkFormal.NearV3.nodeSends3 r.nodes B_VSLOT = [] := by
    simp [ZkFormal.NearV3.nodeSends3, B_VSLOT, B_BYTES, B_PARENT, ZkFormal.NearV3.B_VPARENT, B_EDGE,
      ZkFormal.NearV3.B_BMAP, ZkFormal.NearV3.B_DIGS, ZkFormal.NearV3.B_ENT, ZkFormal.NearV3.B_SIZE,
      ZkFormal.NearV3.B_UPB]
  rw [z1] at h
  simp only [tcnt, List.map_nil, List.count_nil, Nat.zero_add] at h
  exact h

theorem acct_slot_lt {pub : List Fp} {tr : Trace Fp} {r : V3Records} (hH : HoldsP nearAirV3 pub tr)
    (T : V3RecordsTraffic pub tr r) (W : V3RecordsWf pub r) {a : AcctV} (ha : a ∈ r.accts) :
    a.k < 2 ^ 22 := by
  have hvb := vparentBal_of hH T
  have hm : [a.k] ∈ ZkFormal.NearV3.acctV3Sends r.accts B_VSLOT := by
    simp only [ZkFormal.NearV3.acctV3Sends, show B_VSLOT ≠ ZkFormal.NearV3.B_VBYTES by decide,
      show B_VSLOT ≠ B_BYTES by decide, show B_VSLOT ≠ B_MEM by decide, ite_false, ite_true,
      List.mem_map]
    exact ⟨a, ha, rfl⟩
  have hc := List.count_pos_iff.mpr (List.mem_map_of_mem (f := Msg.toFp) hm)
  rw [vslot_bal hH T] at hc
  obtain ⟨x, hx, he⟩ := List.mem_map.mp (List.count_pos_iff.mp hc)
  simp only [ZkFormal.NearV3.nodeRecvs3, show B_VSLOT ≠ B_DIGEST by decide,
    show B_VSLOT ≠ B_PARENT by decide, show B_VSLOT ≠ B_EDGE by decide,
    show B_VSLOT ≠ ZkFormal.NearV3.B_BMAP by decide, show B_VSLOT ≠ ZkFormal.NearV3.B_DUP by decide,
    show B_VSLOT ≠ ZkFormal.NearV3.B_ENT by decide, show B_VSLOT ≠ ZkFormal.NearV3.B_UPB by decide,
    ite_false, ite_true, List.mem_flatMap] at hx
  obtain ⟨⟨s, n⟩, hsn, hx⟩ := hx
  obtain ⟨hn, rfl⟩ := ZkFormal.NearV3.Link3.mem_zip_range hsn
  split at hx
  · rename_i i l pre po hv
    simp only [List.mem_singleton] at hx
    subst hx
    have hlen := ZkFormal.NearV3.Link3.vlen_le W.values
    obtain ⟨t, ht, -, hi, -, -⟩ := ZkFormal.NearV3.Link3.val_pos W.nodes W.values hvb hlen hn hv
    have hvt := ZkFormal.NearV3.Link3.vid_small W.values ht
    have hk := (W.accts.v1.len a ha).2.2.1
    simp only [Msg.toFp, List.map_cons, List.map_nil, List.cons.injEq, and_true] at he
    have := ZkFormal.Near.Link.ofNat_inj (by unfold P; omega) hk he
    omega
  · simp at hx

theorem acctKinds {pub : List Fp} {tr : Trace Fp} {r : V3Records} (hH : HoldsP nearAirV3 pub tr)
    (T : V3RecordsTraffic pub tr r) (W : V3RecordsWf pub r) :
    KindsOk (ZkFormal.NearV3.acctV3Sends r.accts B_BYTES) := by
  intro x hx
  simp only [ZkFormal.NearV3.acctV3Sends, show B_BYTES ≠ ZkFormal.NearV3.B_VBYTES by decide, ite_false,
    ite_true, List.mem_flatMap] at hx
  obtain ⟨a, ha, hx⟩ := hx
  obtain ⟨j, -, rfl⟩ := ZkFormal.NearV3.Link3.mem_emitAt3.mp hx
  have := acct_slot_lt hH T W ha
  exact kindOk_msgId (by decide) (by decide) (by decide) (by decide) (by unfold msgId K_VPOST P; omega)

/-! ## mrk (`K_MRK = 6`): ids below the shape size `≤ 2n`, `n` the receipt count -/

theorem mrkLevels_length2 : ∀ (f j sp : Nat), (mrkLevels f j sp).length ≤ 2 * sp
  | 0, _, _ => by simp [mrkLevels]
  | f + 1, j, sp => by
    have ih := mrkLevels_length2 f (j + 1) ((sp + 1) / 2)
    simp only [mrkLevels, List.length_append, List.length_map, List.length_range]
    split
    · rename_i h; simp only [List.length_nil]; omega
    · rename_i h
      omega

theorem alias_pubNat (pub : List Fp) {i : Nat} (hi : i < 249) :
    pubNat (ZkFormal.NearV3.Candidates.MerklePublic.aliasPublic pub) i =
      pubNat pub (ZkFormal.NearV3.Candidates.MerklePublic.publicIndex i) := by
  unfold pubNat; rw [ZkFormal.NearV3.Candidates.MerklePublic.alias_get pub hi]

theorem alias_n (pub : List Fp) (x : Nat) (hx : x < 4) :
    pubNat (ZkFormal.NearV3.Candidates.MerklePublic.aliasPublic pub) (PV_N + x) =
      pubNat pub (ZkFormal.NearV3.PH_N + x) := by
  rw [alias_pubNat pub (by unfold PV_N; omega)]
  congr 1
  unfold ZkFormal.NearV3.Candidates.MerklePublic.publicIndex
  split
  · omega
  · rename_i h; exact absurd ⟨Nat.le_add_right _ _, by omega⟩ h

/-- The mrk node count from the receipt count: `v.n` is the public `n`, which is the number of
receipts (`RcptV3Wf.count`). -/
theorem mrk_n_le {pub : List Fp} {r : V3Records} (W : V3RecordsWf pub r)
    (hpb : ∀ i, pubNat pub i < 256) (he : r.mrkE = false) : r.mrk.n ≤ 2 ^ 22 := by
  have hw : MrkWf (ZkFormal.NearV3.Candidates.MerklePublic.aliasPublic pub) r.mrk := by
    have := W.mrk; simpa [MrkWfE, he] using this
  have hb : ∀ x, x < 4 → pubNat (ZkFormal.NearV3.Candidates.MerklePublic.aliasPublic pub) (PV_N + x) < 256 :=
    fun x hx => by rw [alias_n pub x hx]; exact hpb _
  have hc := W.lists.count (fun i _ => hpb _)
  have hpe : pubBytes (ZkFormal.NearV3.Candidates.MerklePublic.aliasPublic pub) PV_N 4 =
      pubBytes pub ZkFormal.NearV3.PH_N 4 := by
    unfold pubBytes
    apply List.map_congr_left
    intro j hj
    exact alias_n pub j (List.mem_range.mp hj)
  have hn := ZkFormal.Near.Link.nPubNat_eq _ hb
  rw [hpe, ← hc] at hn
  have hlt := W.listsCount.2
  rw [hw.nfix hb (by rw [hn]; unfold P; omega), hn]
  exact hlt

theorem mrkKinds {pub : List Fp} {r : V3Records} (W : V3RecordsWf pub r)
    (hpb : ∀ i, pubNat pub i < 256) :
    KindsOk ((mrkTrafficE pub r.mrkE r.mrk).sends B_BYTES) := by
  cases he : r.mrkE
  · have hn := mrk_n_le W hpb he
    have hw : MrkWf (ZkFormal.NearV3.Candidates.MerklePublic.aliasPublic pub) r.mrk := by
      have := W.mrk; simpa [MrkWfE, he] using this
    have hl : r.mrk.nodes.length ≤ 2 ^ 23 := by
      rw [hw.shape.1]
      have := mrkLevels_length2 (r.mrk.n + 1) 1 r.mrk.n
      unfold mrkShape; omega
    intro x hx
    simp only [mrkTrafficE, Bool.false_eq_true, ite_false, mrkTraffic, mrkSends, ite_true,
      List.mem_flatMap] at hx
    obtain ⟨⟨nd, q⟩, hq, hx⟩ := hx
    obtain ⟨hql, -⟩ := ZkFormal.NearV3.Link3.mem_zip_range hq
    cases nd with
    | promoted => simp at hx
    | hashed lI lL l rI rL rr =>
      obtain ⟨j, -, rfl⟩ := ZkFormal.NearV3.Link3.mem_emitAt3.mp hx
      have := ZkFormal.Near.Link.hashedBefore_le r.mrk.nodes q
      dsimp only
      exact kindOk_msgId (by decide) (by decide) (by decide) (by decide) (by unfold msgId K_MRK P; omega)
  · intro x hx
    simp [mrkTrafficE] at hx

/-! ## codec (raw, kind `K_SCH = 11`): `τ` is a public instance index (`first_par`) -/

theorem codecOwn : ZkFormal.NearV3.Sched.CodecValOwn nearAirV3 T_CODEC where
  lt := by decide
  tab := rfl
  lenOnly := by decide +kernel
  lenPub := by decide +kernel
  postOnly := by decide +kernel
  postPub := by decide +kernel

theorem sparOwn : ZkFormal.NearV3.Sched.SparOwn nearAirV3 where
  none := by decide +kernel
  pub := by decide +kernel

/-- **The codec's `BYTES` ids** are `11 + 16·τ` with `τ < 34` (a scheduler instance of the
prepared statement), so of kind `11`. -/
theorem codecKinds {cb : NearSpec.Bytes} {h : NearSpecV3.Hint} {p : NearSpecV3.Prep} {oh : Nat}
    {tr : Trace Fp} (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr) :
    ∀ y ∈ codecBytes tr (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)), ∀ a,
      y.head? = some a → a.toNat % 16 ≠ K_NPRE ∧ a.toNat % 16 ≠ K_NPOST ∧ a.toNat % 16 ≠ K_VPRE := by
  have hlen : (ZkFormal.NearV3.Public.preparedBytes p oh).length < 256 ^ 4 := by unfold P at hsz; omega
  have hrec := (ZkFormal.NearV3.Public.prepared_scheduler_index nearAirV3 oh rfl hp (prepD0_roots hp)
    (prepD0_source_roots hp) hlen).2.1
  have hPs := ZkFormal.NearV3.Sched.prepD0_len hp
  have hL := ZkFormal.NearV3.Sched.codec_local hH codecOwn
  have h22 := ZkFormal.NearV3.Sched.codec_h22 hH codecOwn
  intro y hy a ha
  unfold codecBytes at hy
  obtain ⟨w, hw, hy⟩ := List.mem_flatMap.mp hy
  unfold rowTraffic at hy
  obtain ⟨i, hi, hy⟩ := List.mem_flatMap.mp hy
  split at hy
  · rename_i hbs
    obtain ⟨hpos, rfl⟩ := List.mem_replicate.mp hy
    have hi2 := ZkFormal.NearV3.Sched.Codec.bytes_send_i (show i ∈ ZkFormal.NearV3.Sched.Codec.interactions from hi)
      hbs.1 hbs.2
    subst hi2
    obtain ⟨f, j, hf, hF, -, -, hmsg⟩ := ZkFormal.NearV3.Sched.Codec.bytes_row hL h22 (List.mem_range.mp hw) hpos
    have hτ := (ZkFormal.NearV3.Sched.first_par hH codecOwn sparOwn
      (ZkFormal.NearV3.Public.prepared_pubIdx nearAirV3 p oh rfl (prepD0_roots hp) (prepD0_source_roots hp) hlen)
      (p.sched.map ZkFormal.NearV3.Sched.instOf) p.fwd hrec (by simp only [List.length_map]; omega) hf hF).1
    simp only [List.length_map] at hτ
    rw [hmsg] at ha
    simp only [List.map_cons, List.head?_cons, Option.some.injEq] at ha
    subst ha
    have hlt : 11 + 16 * ZkFormal.Chacha.cv tr T_CODEC f ZkFormal.NearV3.Sched.Codec.tau < P := by
      unfold P; omega
    rw [Fp.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    simp only [K_NPRE, K_NPOST, K_VPRE]
    omega
  · simp at hy

end ZkFormal.NearV3.Assembly
