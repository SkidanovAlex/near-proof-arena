import ZkFormal.NearV3.Rcpt.Link.RfBody
import ZkFormal.NearV3.Rcpt.Link.RecModel
import ZkFormal.NearV3.Assembly.RcptHeightPrepared
import ZkFormal.Near.Link.Refunds
import ZkFormal.NearV3.Assembly.HeaderWireShape
import ZkFormal.NearV3.Rcpt.Candidates.NativePreparedBody

/-!
# ZkFormal.NearV3.Rcpt.Link.RfEnc — refund ids and refund encodings

* `rid_isolate` — the receipt `BYTES` messages with id `msgId K_RID q` are the refund-id preimage
  `rid ‖ height ‖ 0^8` of receipt `q` (which has a refund);
* **`rfid_sha`** — `rfid = sha256 (rid ‖ height ‖ 0^8)` (`sha_core` against the rcpt `DIGEST`
  receive `digMsg (msgId K_RID q) 48 rfid`);
* `height_pub` — the public height bytes are `u64 pc.ctxB2.height`;
* `toBytes_encRefund3` — `toBytes encRefund = (gasRefundReceipt x.toReceipt height refund).encode`;
* **`rfS_refundOf`** — under `RecHyp`, a receipt's refund bytes are the model's refund list
  encoded (`refundOf`; `hr ↔ ¬sys ∧ surplus ≠ 0`, `ramt = surplus`).
-/

namespace ZkFormal.NearV3.RcptLink

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.Near.Link
  ZkFormal.NearV3.Assembly NearSpec NearSpec.TransferV1 NearSpecV3

/-- The refund-id preimage of a receipt. -/
def ridPre (pub : List Fp) (x : RcptE) : List Nat :=
  x.rid ++ pubBytes pub PH_HEIGHT 8 ++ List.replicate 8 0

theorem receipt_sends_rid {pub : List Fp} {xs : List RcptE} {j r off a : Nat} {x : RcptE} {m : Msg}
    (hm : m ∈ rSends pub xs j r off x B_BYTES) (ha : m.head? = some a) (hk : a % 16 = K_RID) :
    x.hr = true ∧ m ∈ emitAt (msgId K_RID r) 0 (ridPre pub x) := by
  simp only [rSends, ite_true, List.mem_append] at hm
  rcases hm with (((hm | hm) | hm) | hm) | hm
  · have hh := emitAt_head_eq hm ha
    subst a
    simp [msgId, K_RID, K_RC, Nat.add_mod] at hk
  · split at hm
    · have hh := emitAt_head_eq hm ha
      subst a
      simp [K_RF, K_RID] at hk
    · simp at hm
  · have hh := emitAt_head_eq hm ha
    subst a
    simp [msgId, K_PEO, K_RID, Nat.add_mod] at hk
  · have hh := emitAt_head_eq hm ha
    subst a
    simp [msgId, K_LEAF, K_RID, Nat.add_mod] at hk
  · split at hm
    · next hr => exact ⟨hr, by simpa [ridPre, List.append_assoc] using hm⟩
    · simp at hm

/-- **`RID` isolation.** -/
theorem rid_isolate {pub : List Fp} {ls : RcptV3Vs} {q : Nat} {m : Msg}
    (hm : m ∈ rcptSends3 pub ls B_BYTES) (ha : m.head? = some (msgId K_RID q)) :
    ∃ hq : q < (flatR ls).length, ∃ k, k < (ridPre pub (flatR ls)[q]).length ∧
      m = [msgId K_RID q, k, (ridPre pub (flatR ls)[q]).getD k 0] := by
  simp only [rcptSends3, ite_true, show B_BYTES ≠ B_RCL by decide, ite_false, List.append_nil] at hm
  obtain ⟨j, hj, hm⟩ := List.mem_flatMap.mp hm
  have hj := List.mem_range.mp hj
  rcases List.mem_append.mp hm with hm | hm
  · have hid := emitAt_head_eq hm ha
    exfalso; unfold msgId K_RC K_RID at hid; omega
  · obtain ⟨⟨r, off, x⟩, hpos, hm⟩ := List.mem_flatMap.mp hm
    have hm := (receipt_sends_rid hm ha (by simp [msgId, K_RID, Nat.add_mod])).2
    have hid := emitAt_head_eq hm ha
    have hrq : r = q := by unfold msgId at hid; omega
    subst hrq
    obtain ⟨hq, hx⟩ := located_flat hj hpos
    refine ⟨hq, ?_⟩
    rw [hx]
    obtain ⟨k, hk, rfl⟩ := ZkFormal.NearV3.Link3.mem_emitAt3.mp hm
    exact ⟨k, hk, by simp⟩

/-- Every flat index is a located global index. -/
theorem flat_index : ∀ (ls : RcptV3Vs) (q : Nat), q < (flatR ls).length →
    ∃ j, ∃ hj : j < ls.length, ∃ k, k < ls[j].rs.length ∧ baseR ls j + k = q
  | [], q, hq => by simp [flatR] at hq
  | L :: ls, q, hq => by
    by_cases hL : q < L.rs.length
    · exact ⟨0, by simp, q, by simpa using hL, by simp [baseR]⟩
    · have hq' : q - L.rs.length < (flatR ls).length := by
        simp only [flatR, List.flatMap_cons, List.length_append] at hq
        unfold flatR; omega
      obtain ⟨j, hj, k, hk, he⟩ := flat_index ls _ hq'
      refine ⟨j + 1, by simpa using hj, k, by simpa using hk, ?_⟩
      simp only [baseR, List.take_succ_cons, List.map_cons, List.sum_cons] at he ⊢
      omega

theorem flat_located {ls : RcptV3Vs} {q : Nat} (hq : q < (flatR ls).length) :
    ∃ j, j < ls.length ∧ ∃ o, (q, o, (flatR ls)[q]) ∈ located ls j := by
  obtain ⟨j, hj, k, hk, rfl⟩ := flat_index ls q hq
  have hl : (baseR ls j + k, lOffs ls[j].rs k, ls[j].rs[k]) ∈ located ls j := by
    simp only [located, getD_eq_getElem' ls default hj, List.mem_map, List.mem_range]
    exact ⟨k, hk, by rw [getD_eq_getElem' _ default hk]⟩
  obtain ⟨_, hxq⟩ := located_flat hj hl
  exact ⟨j, hj, _, by rw [hxq]; exact hl⟩

/-- **The refund id is `sha256 (rid ‖ height ‖ 0^8)`.** -/
theorem rfid_sha {cb : NearSpec.Bytes} {h : NearSpecV3.Hint} {p : NearSpecV3.Prep} {oh : Nat}
    {tr : Trace Fp} {r : V3Records} (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < ZkFormal.Algebra.P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    {q : Nat} (hq : q < (flatR r.lists).length) (hhr : (flatR r.lists)[q].hr = true) :
    (flatR r.lists)[q].rfid = (sha256 (toBytes (ridPre (ZkFormal.Udr.pubOf Fp
      (ZkFormal.NearV3.Public.preparedBytes p oh)) (flatR r.lists)[q]))).map UInt8.toNat := by
  have hcnt := W.listsCount
  obtain ⟨toks, -, -, hwf, -⟩ := W.lists.toks
  have hw := hwf q hq
  have hl48 := (Rcpt.Candidates.receipt_sha_lengths
      (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) _ hw).2.2.2
  have hxm : (flatR r.lists)[q] ∈ flatR r.lists := List.getElem_mem hq
  have hcan : ∀ y ∈ (flatR r.lists)[q].raw3, y < ZkFormal.Algebra.P := W.lists.canon.2 _ hxm
  obtain ⟨j, hj, o, hloc⟩ := flat_located hq
  have hdig : 0 < shaU tr (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) true B_DIGEST
      (digMsg (msgId K_RID q) (ridPre (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh))
        (flatR r.lists)[q]).length (flatR r.lists)[q].rfid).toFp := by
    have e48 : (ridPre (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh))
        (flatR r.lists)[q]).length = 48 := hl48
    rw [e48]
    apply digest_provided hH (t := Assembly.T_RCPT) (by decide)
    rw [show isAt Assembly.T_RCPT = RcptV3.interactions from rfl, tcnt_of_traffic T.lists]
    simp only [tcnt, Bool.false_eq_true, ite_false, rcptTraffic3]
    apply List.count_pos_iff.mpr
    apply List.mem_map_of_mem
    simp only [rcptRecvs3, List.mem_flatMap, List.mem_range]
    refine ⟨j, hj, _, hloc, ?_⟩
    simp [rRecvs, hhr]
  have hsha := LinkRidBytes.shaFacts_cover (shaU_facts hH) _ (LinkRidBytes.sha_le_rc hH T)
  have hid : msgId K_RID q < ZkFormal.Algebra.P := by unfold msgId K_RID ZkFormal.Algebra.P; omega
  have henc : ∀ y ∈ ridPre (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh))
      (flatR r.lists)[q], y < ZkFormal.Algebra.P := by
    intro y hy
    simp only [ridPre, List.mem_append] at hy
    rcases hy with (hy | hy) | hy
    · exact hcan y (by simp [RcptE.raw3, RcptV.raw, hy])
    · simp only [pubBytes, List.mem_map, List.mem_range] at hy
      obtain ⟨i, -, rfl⟩ := hy
      exact Fp.toNat_lt _
    · rw [List.eq_of_mem_replicate hy]; unfold ZkFormal.Algebra.P; omega
  have hlen : (ridPre (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh))
      (flatR r.lists)[q]).length < ZkFormal.Algebra.P := by
    simp only [ridPre] at hl48 ⊢; rw [hl48]; unfold ZkFormal.Algebra.P; omega
  have := (sha_core hsha _ (fun m => rfl) hid henc hlen
    (fun y hy => hcan y (by simp [RcptE.raw3, RcptV.raw, hy])) ?_ hdig).2
  · exact this
  intro m hm a ha he
  rcases List.mem_append.mp hm with hm | hm
  · have hc := receipt_bytes_ids hcnt.1 hcnt.2 hm ha
    have heq := Near.Link.ofNat_inj hc hid he
    subst a
    obtain ⟨hq', k', hk', rfl⟩ := rid_isolate hm ha
    exact ⟨k', hk', rfl⟩
  · have hh := othersRC_kind (Or.inr (Or.inr rfl)) hp hsz hH T W m hm a ha
    have heq := Near.Link.ofNat_inj hh.1 hid he
    have hk : msgId K_RID q % 16 = K_RID := by simp [msgId, K_RID, Nat.add_mod]
    exact False.elim (hh.2 (heq ▸ hk))

/-! ## Public height, encodings -/

/-- The public height bytes are the context's height. -/
theorem height_pub {cb : NearSpec.Bytes} {h : NearSpecV3.Hint} {p : NearSpecV3.Prep} (oh : Nat)
    (hp : NearSpecV3.prepD0 cb h = .ok p) {pc : PrepC} (hc : prepClaim cb = .ok pc)
    (hb : prepBody pc h = .ok p) :
    toBytes (pubBytes (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) PH_HEIGHT 8) =
      u64 pc.ctxB2.height := by
  have hroots := prepD0_roots hp
  have hpb : pubBytes (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) PH_HEIGHT 8 =
      (u64 p.hdr.height).map UInt8.toNat := by
    apply List.ext_getElem (by simp [pubBytes, u64, leN_length])
    intro i h1 h2
    have hi : i < 8 := by simpa [pubBytes] using h1
    simp only [pubBytes, List.getElem_map, List.getElem_range]
    rw [pubNat_prepared, RcptSkeleton.prepared_height_byte p oh i hroots hi,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa [u64, leN_length] using hi)]
    rfl
  rw [hpb, toBytes_map_toNat', RcptSkeleton.prepBody_height hb, RcptSkeleton.prepClaim_height hc]

theorem toBytes_encRefund3 {x : RcptE} {r : Nat} {a : List Nat} {b c : Nat} (w : x.Wf r a b c)
    (height refund : Nat)
    (hrfid : toBytes x.rfid = receiptIdFrom (toBytes x.rid) height 0)
    (hramt : leN' x.ramt = refund) :
    toBytes x.encRefund = (gasRefundReceipt x.toReceipt height refund).encode := by
  obtain ⟨-, -, hs, -⟩ := w.ids
  have hs := (valid_length hs).2
  simp only [toBytes_length] at hs
  obtain ⟨-, -, h3, -, -, -, -, -, -, -, h11, -⟩ := w.lens
  have hkt : x.kt < 256 := by omega
  simp only [RcptV.encRefund, toBytes_append, gasRefundReceipt, RcptV.toReceipt, Receipt.encode,
    PublicKey.encode]
  have hr16 : u128 (leN' x.ramt) = toBytes x.ramt := leN_leN' h11
  rw [← toBytes_append, systemN_eq, toBytes_borshN (by omega), hrfid, zeros16_eq, tailN_eq,
    ← hramt, hr16]
  have : u8 x.kt = toBytes [x.kt] := by
    simp only [u8, leN, toBytes, List.map_cons, List.map_nil, Nat.mod_eq_of_lt hkt]
  rw [this]
  simp only [List.append_assoc]; rfl

theorem toReceipt_wf3 {x : RcptE} {r : Nat} {a : List Nat} {b c : Nat} (w : x.Wf r a b c) :
    x.toReceipt.wf = true := by
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := w.lens
  obtain ⟨i1, i2, i3, -⟩ := w.ids
  have hgp := leN'_lt (w := 16) h4
  have hdep := leN'_lt (w := 16) h5
  have e : (256 : Nat) ^ 16 = Params.two128 := by decide
  rw [e] at hgp hdep
  simp only [Receipt.wf, RcptV.toReceipt, PublicKey.wf, i1, i2, i3, Bool.and_eq_true, Bool.true_and,
    decide_eq_true_eq, beq_iff_eq, toBytes_length, h1, Bool.or_eq_true, h2]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h3 with h | h <;> simp_all

/-! ## The model's refunds -/

section Hyp
variable {pub : List Fp} {ls : RcptV3Vs} {as : List AcctV} (h : RecHyp pub ls as)
  (base : Nat → NearSpec.Bytes) (T : (Nat → NearSpec.Bytes) → PTrie)
include h

/-- **A receipt's refund bytes are its model refund list, encoded.** -/
theorem rfS_refundOf (ctx : ApplyCtx) (hgp : ctx.gasPrice = leN' (pubBytes pub PH_GP 16))
    {q : Nat} (hq : q < (flatR ls).length)
    (hrfid : ((flatR ls).getD q default).hr = true →
      toBytes ((flatR ls).getD q default).rfid = receiptIdFrom (toBytes ((flatR ls).getD q default).rid) ctx.height 0) :
    toBytes (rfS ((flatR ls).getD q default)) =
      concatAll (((recModel ls as base T).refundOf ctx q).map Receipt.encode) ∧
    ∀ m ∈ (recModel ls as base T).refundOf ctx q, ZkFormal.V3.refundShape m = true := by
  obtain ⟨toks, h0, hw⟩ := toks_at h
  have w := hw q hq
  have ar := arith_at h hq w
  obtain ⟨-, -, -, -, -, a7, a8, -, -⟩ := ar
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
    have hrhs : (if ((flatR ls).getD q default).sys = true then ([] : List Receipt) else
        if Params.G * (leN' ((flatR ls).getD q default).gp -
          min (leN' ((flatR ls).getD q default).gp) (leN' (pubBytes pub PH_GP 16))) = 0 then [] else
        [gasRefundReceipt ((recModel ls as base T).rc q) ctx.height (Params.G * (leN' ((flatR ls).getD q default).gp -
          min (leN' ((flatR ls).getD q default).gp) (leN' (pubBytes pub PH_GP 16))))]) = [] := by
      cases hs : ((flatR ls).getD q default).sys
      · rw [hs] at hno
        simp only [Bool.false_eq_true, ite_false]
        rw [if_pos (Decidable.of_not_not fun hc => hno ⟨rfl, hc⟩)]
      · simp
    rw [hrhs]
    simp only [rfS, hhr, Bool.false_eq_true, ite_false]
    simp [concatAll, toBytes]
  · obtain ⟨hns, hs0⟩ := a7.mp hhr
    rw [hns]
    simp only [Bool.false_eq_true, ite_false, if_neg hs0, List.map_cons, List.map_nil, concatAll,
      List.append_nil, rfS, hhr, ite_true, List.mem_singleton, forall_eq]
    rw [recModel_rc hq, R_rv]
    have hlen16 : ((flatR ls).getD q default).ramt.length = 16 := w.lens.2.2.2.2.2.2.2.2.2.2.1
    refine ⟨toBytes_encRefund3 w ctx.height _ (hrfid hhr) (a8 hhr), ?_⟩
    apply ZkFormal.V3.gasRefundReceipt_shape _ _ _ (toReceipt_wf3 w)
    rw [← a8 hhr]
    have := leN'_lt hlen16
    have e : (256 : Nat) ^ 16 = Params.two128 := by decide
    omega

end Hyp

end ZkFormal.NearV3.RcptLink
