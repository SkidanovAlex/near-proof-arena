import ZkFormal.NearV3.Rcpt.Link.RcptRunHdr
import ZkFormal.Near.Link.OutLeaf

/-!
# ZkFormal.NearV3.Rcpt.Link.OutLeaf3 — the receipt `LEAF(q)` message hashes to the model's outcome leaf

* `leaf_isolate` — the receipt `BYTES` messages with id `msgId K_LEAF q` are receipt `q`'s leaf;
* `othersRC_leaf` — no other `BYTES` sender uses kind `K_LEAF`;
* `leaf_iso` — the `sha_core` isolation hypothesis for `msgId K_LEAF q` and the leaf;
* `peo_sha` — `peoh = sha256 peo` (`sha_core` against the receipt's own `PEO` digest receive);
* `peo_encode3` — under `RecHyp`, `peo` is the model outcome's `partialEncode`;
* **`leaf_hash3`** — `Bytes8 leaf ∧ sha256 leaf = (outcomeOf q).leaf`.
-/

namespace ZkFormal.NearV3.RcptLink

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.Near.Link
  ZkFormal.NearV3.Assembly NearSpec NearSpec.TransferV1 NearSpecV3

/-- Of a receipt's byte streams, only its leaf stream has kind `K_LEAF`. -/
theorem receipt_sends_leaf {pub : List Fp} {xs : List RcptE} {j r off a : Nat} {x : RcptE} {m : Msg}
    (hm : m ∈ rSends pub xs j r off x B_BYTES) (ha : m.head? = some a) (hk : a % 16 = K_LEAF) :
    m ∈ emitAt (msgId K_LEAF r) 0 x.leaf := by
  simp only [rSends, ite_true, List.mem_append] at hm
  rcases hm with (((hm | hm) | hm) | hm) | hm
  · have hh := emitAt_head_eq hm ha
    subst a
    simp [msgId, K_LEAF, K_RC, Nat.add_mod] at hk
  · split at hm
    · have hh := emitAt_head_eq hm ha
      subst a
      simp [K_RF, K_LEAF] at hk
    · simp at hm
  · have hh := emitAt_head_eq hm ha
    subst a
    simp [msgId, K_LEAF, K_PEO, Nat.add_mod] at hk
  · exact hm
  · split at hm
    · have hh := emitAt_head_eq hm ha
      subst a
      simp [msgId, K_RID, K_LEAF, Nat.add_mod] at hk
    · simp at hm

/-- **Leaf isolation.** -/
theorem leaf_isolate {pub : List Fp} {ls : RcptV3Vs} {q : Nat} {m : Msg}
    (hm : m ∈ rcptSends3 pub ls B_BYTES) (ha : m.head? = some (msgId K_LEAF q)) :
    ∃ hq : q < (flatR ls).length, ∃ k, k < (flatR ls)[q].leaf.length ∧
      m = [msgId K_LEAF q, k, (flatR ls)[q].leaf.getD k 0] := by
  simp only [rcptSends3, ite_true, show B_BYTES ≠ B_RCL by decide, ite_false, List.append_nil] at hm
  obtain ⟨j, hj, hm⟩ := List.mem_flatMap.mp hm
  have hj := List.mem_range.mp hj
  rcases List.mem_append.mp hm with hm | hm
  · have hid := emitAt_head_eq hm ha
    exfalso; unfold msgId K_RC K_LEAF at hid; omega
  · obtain ⟨⟨r, off, x⟩, hpos, hm⟩ := List.mem_flatMap.mp hm
    have hm := receipt_sends_leaf hm ha (by simp [msgId, K_LEAF, Nat.add_mod])
    have hid := emitAt_head_eq hm ha
    have hrq : r = q := by unfold msgId at hid; omega
    subst hrq
    obtain ⟨hq, hx⟩ := located_flat hj hpos
    refine ⟨hq, ?_⟩
    rw [hx]
    obtain ⟨k, hk, rfl⟩ := ZkFormal.NearV3.Link3.mem_emitAt3.mp hm
    exact ⟨k, hk, by simp⟩

/-- No other `BYTES` sender uses kind `K_LEAF`. -/
theorem othersRC_leaf {cb : NearSpec.Bytes} {h : NearSpecV3.Hint} {p : NearSpecV3.Prep} {oh : Nat}
    {tr : Trace Fp} {r : V3Records} (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < ZkFormal.Algebra.P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r) :
    ∀ m ∈ LinkRidBytes.othersRC tr (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r, ∀ a,
      m.head? = some a → a < ZkFormal.Algebra.P ∧ a % 16 ≠ K_LEAF := by
  have kin : ∀ {K' : Nat} {x : Msg}, KindIn [K'] x → K' ≠ K_LEAF → ∀ a, x.head? = some a →
      a < ZkFormal.Algebra.P ∧ a % 16 ≠ K_LEAF := by
    intro K' x hk hK' a ha
    obtain ⟨h1, h2⟩ := hk a ha
    rw [List.mem_singleton] at h2
    exact ⟨h1, h2 ▸ hK'⟩
  have nv : ∀ {K' n : Nat}, (K' = K_NPRE ∨ K' = K_NPOST ∨ K' = K_VPRE) → n < 2 ^ 22 →
      msgId K' n < ZkFormal.Algebra.P ∧ msgId K' n % 16 ≠ K_LEAF := by
    intro K' n hK' hn
    unfold msgId ZkFormal.Algebra.P
    rcases hK' with rfl | rfl | rfl <;> simp only [K_NPRE, K_NPOST, K_VPRE, K_LEAF] <;> omega
  intro m hm a ha
  simp only [LinkRidBytes.othersRC, List.mem_append] at hm
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

/-- The `sha_core` isolation for the leaf id of receipt `q`. -/
theorem leaf_iso {cb : NearSpec.Bytes} {h : NearSpecV3.Hint} {p : NearSpecV3.Prep} {oh : Nat}
    {tr : Trace Fp} {r : V3Records} (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < ZkFormal.Algebra.P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    {q : Nat} (hq : q < (flatR r.lists).length) :
    ∀ m ∈ rcptSends3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r.lists B_BYTES ++
        LinkRidBytes.othersRC tr (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r,
      ∀ a, m.head? = some a → Fp.ofNat a = Fp.ofNat (msgId K_LEAF q) →
        ∃ k, k < (flatR r.lists)[q].leaf.length ∧ m = [msgId K_LEAF q, k, (flatR r.lists)[q].leaf.getD k 0] := by
  have hcnt := W.listsCount
  have hid : msgId K_LEAF q < ZkFormal.Algebra.P := by unfold msgId K_LEAF ZkFormal.Algebra.P; omega
  intro m hm a ha he
  rcases List.mem_append.mp hm with hm | hm
  · have hc := receipt_bytes_ids hcnt.1 hcnt.2 hm ha
    have heq := Near.Link.ofNat_inj hc hid he
    subst a
    obtain ⟨hq', k', hk', rfl⟩ := leaf_isolate hm ha
    exact ⟨k', hk', rfl⟩
  · have hh := othersRC_leaf hp hsz hH T W m hm a ha
    have heq := Near.Link.ofNat_inj hh.1 hid he
    have hk : msgId K_LEAF q % 16 = K_LEAF := by simp [msgId, K_LEAF, Nat.add_mod]
    exact False.elim (hh.2 (heq ▸ hk))

/-- **`peoh = sha256 peo`.** -/
theorem peo_sha {cb : NearSpec.Bytes} {h : NearSpecV3.Hint} {p : NearSpecV3.Prep} {oh : Nat}
    {tr : Trace Fp} {r : V3Records} (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < ZkFormal.Algebra.P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    {q : Nat} (hq : q < (flatR r.lists).length) :
    (flatR r.lists)[q].peoh = (sha256 (toBytes (flatR r.lists)[q].peo)).map UInt8.toNat := by
  obtain ⟨j, hj, o, hloc⟩ := flat_located hq
  have hcnt := W.listsCount
  have hdig : 0 < shaU tr (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) true B_DIGEST
      (digMsg (msgId K_PEO q) (flatR r.lists)[q].peo.length (flatR r.lists)[q].peoh).toFp := by
    apply digest_provided hH (t := Assembly.T_RCPT) (by decide)
    rw [show isAt Assembly.T_RCPT = RcptV3.interactions from rfl, tcnt_of_traffic T.lists]
    simp only [tcnt, Bool.false_eq_true, ite_false, rcptTraffic3]
    apply List.count_pos_iff.mpr
    apply List.mem_map_of_mem
    simp only [rcptRecvs3, List.mem_flatMap, List.mem_range]
    refine ⟨j, hj, _, hloc, ?_⟩
    simp [rRecvs]
  have hsha := LinkRidBytes.shaFacts_cover (shaU_facts hH) _ (LinkRidBytes.sha_le_rc hH T)
  obtain ⟨toks, -, -, hwf, -⟩ := W.lists.toks
  have hw := hwf q hq
  have hxm : (flatR r.lists)[q] ∈ flatR r.lists := List.getElem_mem hq
  have hid : msgId K_PEO q < ZkFormal.Algebra.P := by unfold msgId K_PEO ZkFormal.Algebra.P; omega
  have hcan : ∀ y ∈ (flatR r.lists)[q].raw3, y < ZkFormal.Algebra.P := W.lists.canon.2 _ hxm
  have hpeoc : ∀ y ∈ (flatR r.lists)[q].peo, y < ZkFormal.Algebra.P := by
    intro y hy
    rcases receipt_peo_values hw y hy with hy | hy
    · exact hcan y (by simp [RcptE.raw3, hy])
    · unfold ZkFormal.Algebra.P; omega
  have hplen : (flatR r.lists)[q].peo.length < ZkFormal.Algebra.P := by
    have := (Rcpt.Candidates.receipt_sha_lengths
      (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) _ hw).2.1
    unfold ZkFormal.Algebra.P; omega
  refine (sha_core hsha _ (fun m => rfl) hid hpeoc hplen
    (fun y hy => hcan y (by simp [RcptE.raw3, RcptV.raw, hy])) ?_ hdig).2
  intro m hm a ha he
  rcases List.mem_append.mp hm with hm | hm
  · have hc := receipt_bytes_ids hcnt.1 hcnt.2 hm ha
    have heq := Near.Link.ofNat_inj hc hid he
    subst a
    obtain ⟨hq', k', hk', rfl⟩ := peo_isolate hm ha
    exact ⟨k', hk', rfl⟩
  · have hh := othersRC_kind (Or.inl rfl) hp hsz hH T W m hm a ha
    have heq := Near.Link.ofNat_inj hh.1 hid he
    have hk : msgId K_PEO q % 16 = K_PEO := by simp [msgId, K_PEO, Nat.add_mod]
    exact False.elim (hh.2 (heq ▸ hk))

/-! ## The outcome of a receipt -/

section Hyp
variable {pub : List Fp} {ls : RcptV3Vs} {as : List AcctV} (h : RecHyp pub ls as)
  (base : Nat → NearSpec.Bytes) (T : (Nat → NearSpec.Bytes) → PTrie)
include h

/-- The model's refund ids of receipt `q`. -/
theorem refundIds_eq (ctx : ApplyCtx) (hgp : ctx.gasPrice = leN' (pubBytes pub PH_GP 16))
    {q : Nat} (hq : q < (flatR ls).length) :
    ((recModel ls as base T).refundOf ctx q).map Receipt.receiptId =
      if ((flatR ls).getD q default).hr then
        [receiptIdFrom (toBytes ((flatR ls).getD q default).rid) ctx.height 0] else [] := by
  obtain ⟨toks, h0, hw⟩ := toks_at h
  have w := hw q hq
  have ar := arith_at h hq w
  obtain ⟨-, -, -, -, -, a7, -, -, -⟩ := ar
  have hsys := isSys_eq h base T hq
  have hgpr : ((recModel ls as base T).rc q).gasPrice = leN' ((flatR ls).getD q default).gp := by
    rw [recModel_rc hq, R_rv]; rfl
  have hsur : surplusOf ctx.gasPrice ((recModel ls as base T).rc q) =
      Params.G * (leN' ((flatR ls).getD q default).gp -
        min (leN' ((flatR ls).getD q default).gp) (leN' (pubBytes pub PH_GP 16))) := by
    simp [surplusOf, burnPrice, hgpr, hgp]
  unfold RunModel.refundOf
  rw [hsys, hsur]
  cases hhr : ((flatR ls).getD q default).hr
  · have hno : ¬ (((flatR ls).getD q default).sys = false ∧ Params.G * (leN' ((flatR ls).getD q default).gp -
        min (leN' ((flatR ls).getD q default).gp) (leN' (pubBytes pub PH_GP 16))) ≠ 0) := by
      intro hc; rw [a7.mpr hc] at hhr; cases hhr
    cases hs : ((flatR ls).getD q default).sys
    · rw [hs] at hno
      simp only [Bool.false_eq_true, ite_false]
      rw [if_pos (Decidable.of_not_not fun hc => hno ⟨rfl, hc⟩)]; rfl
    · simp
  · obtain ⟨hns, hs0⟩ := a7.mp hhr
    rw [hns]
    simp only [Bool.false_eq_true, ite_false, if_neg hs0, ite_true, List.map_cons, List.map_nil,
      gasRefundReceipt]
    rw [recModel_rc hq, R_rv]; rfl

/-- The model's burnt tokens of receipt `q` are the row's `burnt`. -/
theorem burnt_eq (ctx : ApplyCtx) (hgp : ctx.gasPrice = leN' (pubBytes pub PH_GP 16))
    {q : Nat} (hq : q < (flatR ls).length) :
    (recModel ls as base T).burnt ctx q = leN' ((flatR ls).getD q default).burnt := by
  obtain ⟨toks, h0, hw⟩ := toks_at h
  have ar := arith_at h hq (hw q hq)
  rw [ar.2.2.2.2.1]
  simp only [RunModel.burnt, isSys_eq h base T hq, burntOf, burnPrice, recModel_rc hq, R_rv,
    RcptV.toReceipt, hgp]

/-- **`PEO` is the model outcome's partial encoding.** -/
theorem peo_encode3 (ctx : ApplyCtx) (hgp : ctx.gasPrice = leN' (pubBytes pub PH_GP 16))
    {q : Nat} (hq : q < (flatR ls).length)
    (hrfid : ((flatR ls).getD q default).hr = true →
      toBytes ((flatR ls).getD q default).rfid = receiptIdFrom (toBytes ((flatR ls).getD q default).rid) ctx.height 0) :
    toBytes ((flatR ls).getD q default).peo = ((recModel ls as base T).outcomeOf ctx q).partialEncode := by
  obtain ⟨toks, h0, hw⟩ := toks_at h
  have w := hw q hq
  obtain ⟨-, hv, -, -⟩ := w.ids
  have hv := (valid_length hv).2
  simp only [toBytes_length] at hv
  obtain ⟨-, -, -, -, -, -, -, -, -, l10, -⟩ := w.lens
  simp only [RunModel.outcomeOf, Outcome.partialEncode, refundIds_eq h base T ctx hgp hq,
    burnt_eq h base T ctx hgp hq, recModel_rc hq, R_rv, RcptV.toReceipt]
  rw [u128, leN_leN' l10, u64_G]
  simp only [RcptV.peo, toBytes_append]
  rw [toBytes_borshN (by omega)]
  cases hhr : ((flatR ls).getD q default).hr
  · simp only [Bool.false_eq_true, if_false, List.length_nil, concatAll, List.append_nil,
      List.nil_append]
    simp only [List.append_assoc]; rw [tail5_eq, u32_0_eq]; rfl
  · simp only [if_true, List.length_cons, List.length_nil, concatAll, List.append_nil]
    simp only [List.append_assoc]; rw [tail5_eq, ← hrfid hhr, u32_1_eq]

end Hyp

/-- **The receipt leaf hashes to the model outcome's leaf.** -/
theorem leaf_hash3 {cb : NearSpec.Bytes} {h : NearSpecV3.Hint} {p : NearSpecV3.Prep} {oh : Nat}
    {tr : Trace Fp} {r : V3Records} (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < ZkFormal.Algebra.P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    (H : RecHyp (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r.lists r.accts)
    {pc : PrepC} (hc : prepClaim cb = .ok pc) (hb : prepBody pc h = .ok p)
    (hgp : pc.ctxB2.gasPrice =
      leN' (pubBytes (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) PH_GP 16))
    (base : Nat → NearSpec.Bytes) (Tf : (Nat → NearSpec.Bytes) → PTrie)
    {q : Nat} (hq : q < (flatR r.lists).length) :
    Bytes8 (flatR r.lists)[q].leaf ∧
      sha256 (toBytes (flatR r.lists)[q].leaf) =
        ((recModel r.lists r.accts base Tf).outcomeOf pc.ctxB2 q).leaf := by
  have hrfid : ((flatR r.lists).getD q default).hr = true →
      toBytes ((flatR r.lists).getD q default).rfid =
        receiptIdFrom (toBytes ((flatR r.lists).getD q default).rid) pc.ctxB2.height 0 := by
    intro hhr
    rw [getD_eq_getElem' _ default hq] at hhr ⊢
    rw [rfid_sha hp hsz hH T W hq hhr, toBytes_map_toNat', receiptIdFrom, ridPre, toBytes_append,
      toBytes_append, height_pub oh hp hc hb, zeros8_eq]
  have hpe := peo_encode3 H base Tf pc.ctxB2 hgp hq hrfid
  rw [getD_eq_getElem' _ default hq] at hpe
  have hps := peo_sha hp hsz hH T W hq
  have hencb := H.encB _ (List.getElem_mem hq)
  have hridb : Bytes8 (flatR r.lists)[q].rid := fun y hy => hencb y (by simp [RcptV.enc, hy])
  refine ⟨?_, ?_⟩
  · intro y hy
    simp only [RcptV.leaf, List.mem_append] at hy
    rcases hy with (hy | hy) | hy
    · simp at hy; omega
    · exact hridb y hy
    · rw [hps] at hy; obtain ⟨b, -, rfl⟩ := List.mem_map.mp hy; exact UInt8.toNat_lt _
  · have hid : ((recModel r.lists r.accts base Tf).outcomeOf pc.ctxB2 q).id =
        toBytes (flatR r.lists)[q].rid := by
      simp only [RunModel.outcomeOf, recModel_rc hq, R_rv, RcptV.toReceipt,
        getD_eq_getElem' _ default hq]
    rw [Outcome.leaf, hid]
    simp only [RcptV.leaf, toBytes_append]
    rw [hps, toBytes_map_toNat', hpe, u32_2_eq]

end ZkFormal.NearV3.RcptLink
