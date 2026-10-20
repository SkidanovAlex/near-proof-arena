import ZkFormal.NearV3.D1.Link.Kinds
import ZkFormal.NearV3.D1.L.Rcpt.Link.ListSha
import ZkFormal.NearV3.Rcpt.Link.ListByteIds

/-!
# `ZkFormal.NearV3.D1.Link.RidBytes` — the receipt-list digest with `rcptV3D1`'s sends (L1)

Lane `v3-d1-phase2`, item L1 (the `BYTES` consumers of next step 3, checkpoint 10).  D0a's
`RcptLink.list_sha_digest` reads the receipt view's `BYTES` sends as `rcptSends3`.  In D1 they are
`rcptSends3G` (the refund bytes `K_RF` at the body offset `O0`):

* `rcptG_bytes_mem`: a `rcptSends3G` `BYTES` message is one of D0a's `rcptSends3`, or has the
  id `K_RF`;
* **`list_sha_digest_G`**: `list_sha_digest` with `rcptSends3G` (the `K_RF` messages are not of
  kind `K_RC`);
* `rcptSends3G_rcl`: the `RCL` sends are D0a's;
* `extraKinds_rc`: the extra `BYTES` senders' ids (`akmV3`: `VPOST(vid)`, body prefix: `K_RF`) are
  canonical and not of kind `K_RC`.
-/

namespace ZkFormal.NearV3.D1.Link

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.NearV3 ZkFormal.NearV3.D1
open ZkFormal.NearV3.Assembly

/-- **`rcptV3D1`'s `BYTES` sends** are D0a's, except the refund bytes (id `K_RF`). -/
theorem rcptG_bytes_mem {o0 t0 m0 : Nat} {pub : List Fp} {ls : RcptV3Vs} {x : Msg}
    (hx : x ∈ RcptD1.rcptSends3G o0 t0 m0 pub ls B_BYTES) :
    x ∈ rcptSends3 pub ls B_BYTES ∨ x.head? = some K_RF := by
  simp only [RcptD1.rcptSends3G, ite_true, show B_BYTES ≠ B_RCL by decide, ite_false,
    List.append_nil, List.mem_flatMap] at hx
  obtain ⟨j, hj, hx⟩ := hx
  have hin : ∀ y, y ∈ (emitAt (msgId K_RC j) 0 (hdrBytes pub (ls.getD j default)) ++
      (located ls j).flatMap fun (r, o, x) => rSends pub (flatR ls) j r o x B_BYTES) →
      y ∈ rcptSends3 pub ls B_BYTES := by
    intro y hy
    simp only [rcptSends3, ite_true, show B_BYTES ≠ B_RCL by decide, ite_false, List.append_nil,
      List.mem_flatMap]
    exact ⟨j, hj, hy⟩
  rcases List.mem_append.mp hx with hx | hx
  · exact .inl (hin x (List.mem_append_left _ hx))
  · obtain ⟨⟨r, o, y⟩, hl, hx⟩ := List.mem_flatMap.mp hx
    have hin' : ∀ z, z ∈ rSends pub (flatR ls) j r o y B_BYTES → z ∈ rcptSends3 pub ls B_BYTES :=
      fun z hz => hin z (List.mem_append_right _ (List.mem_flatMap.mpr ⟨(r, o, y), hl, hz⟩))
    simp only [RcptD1.rSendsG, ite_true, List.mem_append] at hx
    rcases hx with (((hx | hx) | hx) | hx) | hx
    · exact .inl (hin' x (by simp only [rSends, ite_true, List.mem_append]; exact .inl (.inl (.inl (.inl hx)))))
    · split at hx
      · obtain ⟨i, -, rfl⟩ := Link3.mem_emitAt3.mp hx
        exact .inr rfl
      · simp at hx
    · exact .inl (hin' x (by simp only [rSends, ite_true, List.mem_append]; exact .inl (.inl (.inr hx))))
    · exact .inl (hin' x (by simp only [rSends, ite_true, List.mem_append]; exact .inl (.inr hx)))
    · exact .inl (hin' x (by simp only [rSends, ite_true, List.mem_append]; exact .inr hx))

/-- **`rcptV3D1`'s `BYTES` kinds** are D0a's receipt kinds (`K_RC`, `K_RF`, `K_PEO`, `K_LEAF`,
`K_RID`). -/
theorem rcptKindInG {o0 t0 m0 : Nat} {pub : List Fp} {ls : RcptV3Vs}
    (hl : ls.length ≤ 2 ^ 22) (hr : (flatR ls).length ≤ 2 ^ 22) :
    ∀ x ∈ RcptD1.rcptSends3G o0 t0 m0 pub ls B_BYTES, KindIn [K_RC, K_RF, K_PEO, K_LEAF, K_RID] x := by
  intro x hx
  rcases rcptG_bytes_mem hx with hx | hx
  · exact rcptKindIn hl hr x hx
  · intro a ha
    rw [hx, Option.some.injEq] at ha
    subst ha
    exact ⟨by unfold K_RF P; omega, by simp [K_RF, K_RC, K_PEO, K_LEAF, K_RID]⟩

/-- `rcptV3D1`'s `RCL` sends are D0a's. -/
theorem rcptSends3G_rcl (o0 t0 m0 : Nat) (pub : List Fp) (ls : RcptV3Vs) :
    RcptD1.rcptSends3G o0 t0 m0 pub ls B_RCL = rcptSends3 pub ls B_RCL := by
  simp only [RcptD1.rcptSends3G, rcptSends3, RcptD1.rSendsG, rSends, show B_RCL ≠ B_BYTES by decide,
    show B_RCL ≠ B_KEYNIB by decide, show B_RCL ≠ B_MEM by decide, show B_RCL ≠ B_RIDS by decide,
    show B_RCL ≠ B_MPOS by decide, show B_RCL ≠ B_SREC by decide, show B_RCL ≠ B_AKC by decide,
    show B_RCL ≠ B_BND by decide, ite_false, ite_true]

open ZkFormal.NearV3.RcptLink ZkFormal.Near.Link NearSpec in
/-- **`list_sha_digest` with `rcptV3D1`'s sends.** -/
theorem list_sha_digest_G {o0 t0 m0 : Nat} {pub : List Fp} {ls : RcptV3Vs} (h : RcptD1.RcptV3WfD1 pub ls)
    (hl : ls.length ≤ 2 ^ 22) (hr : (flatR ls).length ≤ 2 ^ 22)
    {shaS shaR : Nat → List Fp → Nat} (hsha : ShaFacts shaS shaR) (others : List Msg)
    (hbytes : ∀ m, shaR B_BYTES m = cnt (RcptD1.rcptSends3G o0 t0 m0 pub ls B_BYTES ++ others) m)
    (hother : ∀ m ∈ others, ∀ a, m.head? = some a → a < P ∧ a % 16 ≠ K_RC)
    {i : Nat} (hi : i < ls.length) (hlen : (listEncoding pub ls[i]).length < P)
    {d : List Nat} (hd : ∀ v ∈ d, v < P)
    (hrecv : 0 < shaS B_DIGEST (digMsg (msgId K_RC i) (listEncoding pub ls[i]).length d).toFp) :
    Bytes8 (listEncoding pub ls[i]) ∧ d = (sha256 (toBytes (listEncoding pub ls[i]))).map UInt8.toNat := by
  have hid : msgId K_RC i < P := by unfold msgId K_RC P; omega
  apply sha_core hsha _ hbytes hid (list_encoding_canonical_d1 h (List.getElem_mem hi)) hlen hd _ hrecv
  intro m hm a ha he
  rcases List.mem_append.mp hm with hm | hm
  · rcases rcptG_bytes_mem hm with hm | hm
    · exact list_bytes_field_isolate hl hr hi hm ha he
    · rw [hm, Option.some.injEq] at ha
      subst ha
      have heq := Near.Link.ofNat_inj (by unfold K_RF P; omega) hid he
      unfold msgId K_RC K_RF at heq
      omega
  · have hh := hother m hm a ha
    have heq := Near.Link.ofNat_inj hh.1 hid he
    have hk : msgId K_RC i % 16 = K_RC := by simp [msgId, K_RC, Nat.add_mod]
    exact False.elim (hh.2 (heq ▸ hk))

/-- **The extra `BYTES` senders' ids**: `K_RF` (the public body prefix) or `VPOST(vid)` (`akmV3`),
canonical. -/
theorem extraHeads {cb : NearSpec.Bytes} {h : HintD1} {q : Public.PrepD1} {ov : Nat} {tr : Trace Fp}
    {r : V3Records} (hp : prepD1 cb h = .ok q) (hlen : (Public.preparedBytesD1 q ov).length < P)
    (hH : HoldsP nearAirV3D1 (ZkFormal.Udr.pubOf Fp (Public.preparedBytesD1 q ov)) tr)
    (T : BaseTrafficD1 (ZkFormal.Udr.pubOf Fp (Public.preparedBytesD1 q ov)) tr r)
    (W : BaseWfD1 (ZkFormal.Udr.pubOf Fp (Public.preparedBytesD1 q ov)) r) :
    ∀ y ∈ extraBytes tr (ZkFormal.Udr.pubOf Fp (Public.preparedBytesD1 q ov)), ∀ a, y.head? = some a →
      a.toNat = K_RF ∨ a.toNat % 16 = K_VPOST := by
  intro y hy a ha
  have hP : P < 256 ^ 4 := by unfold P; omega
  have hc : 0 < (extraBytes tr (ZkFormal.Udr.pubOf Fp (Public.preparedBytesD1 q ov))).count y :=
    List.count_pos_iff.mpr hy
  rw [extraBytes_count] at hc
  rcases Nat.eq_zero_or_pos (tableBusCount AkmV3.interactions tr T_AKM
      (ZkFormal.Udr.pubOf Fp (Public.preparedBytesD1 q ov)) B_BYTES true y) with h0 | h0
  · have hpub : 0 < pubCount nearAirV3D1 (ZkFormal.Udr.pubOf Fp (Public.preparedBytesD1 q ov)) B_BYTES true y := by
      omega
    have := pub_bytes_send_head q ov (prepD1_roots hp) (prepD1_source_roots hp) (prepD1_leaves hp)
      (by omega) hpub
    rw [this, Option.some.injEq] at ha
    subst ha
    left; simp [Fp.toNat_ofNat, K_RF, P]
  · obtain ⟨vid, hv, he⟩ := akm_bytes_head hH T W h0
    rw [he, Option.some.injEq] at ha
    subst ha
    have : msgId K_VPOST vid < P := by unfold msgId K_VPOST P; omega
    rw [Fp.toNat_ofNat, Nat.mod_eq_of_lt this]
    right; unfold msgId K_VPOST; omega

/-- **The extra `BYTES` senders' ids are not of kind `K_RC`.** -/
theorem extraKinds_rc {cb : NearSpec.Bytes} {h : HintD1} {q : Public.PrepD1} {ov : Nat} {tr : Trace Fp}
    {r : V3Records} (hp : prepD1 cb h = .ok q) (hlen : (Public.preparedBytesD1 q ov).length < P)
    (hH : HoldsP nearAirV3D1 (ZkFormal.Udr.pubOf Fp (Public.preparedBytesD1 q ov)) tr)
    (T : BaseTrafficD1 (ZkFormal.Udr.pubOf Fp (Public.preparedBytesD1 q ov)) tr r)
    (W : BaseWfD1 (ZkFormal.Udr.pubOf Fp (Public.preparedBytesD1 q ov)) r) :
    ∀ y ∈ extraBytes tr (ZkFormal.Udr.pubOf Fp (Public.preparedBytesD1 q ov)), ∀ a, y.head? = some a →
      a.toNat % 16 ≠ K_RC := by
  intro y hy a ha
  rcases extraHeads hp hlen hH T W y hy a ha with h1 | h1 <;> rw [h1] <;> decide

/-- **The extra `BYTES` senders' ids are not of the kinds `K_PEO`, `K_RID`** (they are of kind
`K_RF` for the public body prefix: the refund stream's kind is shared, see `Rcpt/Link/RfBody`). -/
theorem extraKinds_peo_rid {cb : NearSpec.Bytes} {h : HintD1} {q : Public.PrepD1} {ov : Nat} {tr : Trace Fp}
    {r : V3Records} (hp : prepD1 cb h = .ok q) (hlen : (Public.preparedBytesD1 q ov).length < P)
    (hH : HoldsP nearAirV3D1 (ZkFormal.Udr.pubOf Fp (Public.preparedBytesD1 q ov)) tr)
    (T : BaseTrafficD1 (ZkFormal.Udr.pubOf Fp (Public.preparedBytesD1 q ov)) tr r)
    (W : BaseWfD1 (ZkFormal.Udr.pubOf Fp (Public.preparedBytesD1 q ov)) r) {K : Nat}
    (hK : K = K_PEO ∨ K = K_RID) :
    ∀ y ∈ extraBytes tr (ZkFormal.Udr.pubOf Fp (Public.preparedBytesD1 q ov)), ∀ a, y.head? = some a →
      a.toNat % 16 ≠ K := by
  intro y hy a ha
  rcases extraHeads hp hlen hH T W y hy a ha with h1 | h1 <;> rw [h1] <;>
    rcases hK with rfl | rfl <;> decide

end ZkFormal.NearV3.D1.Link
