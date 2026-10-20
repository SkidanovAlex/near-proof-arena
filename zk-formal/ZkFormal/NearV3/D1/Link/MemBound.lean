import ZkFormal.NearV3.D1.Link.Bus
import ZkFormal.NearV3.D1.R.View
import ZkFormal.NearV3.D1.Extract.TxProof
import ZkFormal.NearV3.D1.Extract.ViewsD1
import ZkFormal.NearV3.D1.Public.Ranges

/-!
# `ZkFormal.NearV3.D1.Link.MemBound` — the `MEM` version bound and `rcptV3D1`'s view (L1)

Lane `v3-d1-phase2`, item L1.  Discharges the last hypothesis of `RcptD1.rcptD1_view`: every
`MEM` message `rcptV3D1` receives has version `≤ 2^25`.  By the `MEM` balance it is sent by
* `rcptV3D1` itself, at `r + 1 + T0` with `r + 1 ≤ 2^22` (`receipt_memory_provider_bound_d1`)
  and `T0 < 2^24`;
* `acctV3`, at `0`;
* `txV3`, at `op + 1`, where `op` is the op's `SIG` index (the `SIG` bus has the public segment
  as its only sender): `op < T0 ≤ 2·NT0`.

No public segment is on `MEM`.  Hence **`rcptD1_view_prep`**: the view of `rcptV3D1` from a
successful `prepD1`, a tape below `P` and `HoldsP nearAirV3D1` alone (the D1 analogue of D0a's
`rcptV3_view_nearAir`).  Also `tx_op_sig`: every `txV3` op's index is a public op index.
-/

namespace ZkFormal.NearV3.D1.Link

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.NearV3 ZkFormal.NearV3.D1
open ZkFormal.NearV3.D1.RcptD1 ZkFormal.NearV3.D1.Public
open ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof (ListBlock ListChain)

theorem mem_of_count_pos {is : List Interaction} {tr : Trace Fp} {t : Nat} {pub : List Fp}
    {tf : Traffic} (h : TableTraffic is tr t pub tf) {b : Nat} {s : Bool} {m : List Fp}
    (hpos : 0 < tableBusCount is tr t pub b s m) :
    ∃ v ∈ (if s then tf.sends b else tf.recvs b), m = Msg.toFp v := by
  cases s
  · rw [(h b m).2] at hpos
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp (List.count_pos_iff.mp hpos)
    exact ⟨v, hv, rfl⟩
  · rw [(h b m).1] at hpos
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp (List.count_pos_iff.mp hpos)
    exact ⟨v, hv, rfl⟩

theorem count_pos_of_mem {is : List Interaction} {tr : Trace Fp} {t : Nat} {pub : List Fp}
    {tf : Traffic} (h : TableTraffic is tr t pub tf) {b : Nat} {v : Msg} (hv : v ∈ tf.recvs b) :
    0 < tableBusCount is tr t pub b false (Msg.toFp v) := by
  rw [(h b _).2]
  exact List.count_pos_iff.mpr (List.mem_map.mpr ⟨v, hv, rfl⟩)

theorem toNat_getD1_le (v : Msg) : (Msg.toFp v |>.getD 1 0).toNat ≤ v.getD 1 0 := by
  rw [Msg.toFp, getD_toFp, Fp.toNat_ofNat]; exact Nat.mod_le _ _

theorem getD1_set_le (v : Msg) (y : Nat) : (v.set 1 y).getD 1 0 ≤ y := by
  match v with
  | [] => simp
  | [_] => simp
  | _ :: _ :: _ => simp

/-- `rcptSends3G` at `T0 = M0 = 0` on `MEM` is D0a's `rcptSends3`. -/
theorem sends3G_mem (o0 : Nat) (pub : List Fp) (ls : RcptV3Vs) :
    rcptSends3G o0 0 0 pub ls B_MEM = rcptSends3 pub ls B_MEM := by
  unfold rcptSends3G rcptSends3
  apply ZkFormal.Near.flatMap_congr'
  intro j _
  simp only [show B_MEM ≠ B_BYTES by decide, show B_MEM ≠ B_RCL by decide, ite_false,
    List.nil_append]
  apply ZkFormal.Near.flatMap_congr'
  intro x _
  unfold rSendsG rSends
  rw [if_neg (show B_MEM ≠ B_BYTES by decide), if_neg (show B_MEM ≠ B_KEYNIB by decide), if_pos rfl,
    if_neg (show B_MEM ≠ B_BYTES by decide), if_neg (show B_MEM ≠ B_KEYNIB by decide), if_pos rfl]

variable {cb : NearSpec.Bytes} {h : HintD1} {p : PrepD1} {ov : Nat} {tr : Trace Fp}

/-- **`txV3`'s op index is public**: every op of the `txV3` view is `< |ops|`. -/
theorem tx_op_lt (hp : prepD1 cb h = .ok p) (hlen : (preparedBytesD1 p ov).length < P)
    (hH : HoldsP nearAirV3D1 (ZkFormal.Udr.pubOf Fp (preparedBytesD1 p ov)) tr)
    {es : List TxE} (hW : TxWf es)
    (hT : TableTraffic TxV3.interactions tr T_TX (ZkFormal.Udr.pubOf Fp (preparedBytesD1 p ov)) (txTraffic es))
    {e : TxE} (he : e ∈ es) :
    e.op < p.ops.length ∧ (Fp.ofNat e.valid : Fp) =
      ZkFormal.NearV3.Public.byteF (UInt8.ofNat (p.ops.getD e.op default).valid) := by
  have hP : P < 256 ^ 4 := by unfold P; omega
  have hv : [e.op, e.valid] ∈ (txTraffic es).recvs B_SIG := by
    simp only [txTraffic, txRecvs, show B_SIG ≠ B_TXP by decide, ite_false, ite_true]
    exact List.mem_map.mpr ⟨e, he, rfl⟩
  have hpos := count_pos_of_mem hT hv
  rcases sender_of_recv hH getElem?_d1_tx hpos with hpub | ⟨t', T', ht', hpos'⟩
  · obtain ⟨-, o, ho, hm⟩ := pub_sig_mem p ov (prepD1_roots hp) (prepD1_source_roots hp)
      (prepD1_leaves hp) (by omega) hpub
    have hc := (hW.ops e he).canon.1
    simp only [Msg.toFp, List.map_cons, List.map_nil, List.cons.injEq] at hm
    obtain ⟨h1, h2, -⟩ := hm
    have hol : o < P := by
      have := (prepD1_m0_t0 hp).2
      obtain ⟨w, -, rfl⟩ := prepD1_spec hp
      change o < w.loc.ops.length at ho
      change w.loc.ops.length ≤ _ at this
      unfold NearSpecV3.NT0 at this; unfold P; omega
    have : e.op = o := by
      have := congrArg Fp.toNat h1
      rw [Fp.toNat_ofNat, natCast_eq, Fp.toNat_ofNat, Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hol] at this
      exact this
    subst this
    exact ⟨ho, h2⟩
  · by_cases h25 : t' = 25
    · subst h25
      rw [show nearAirV3D1.tables[25]? = some TxV3.table from rfl] at ht'
      cases ht'
      obtain ⟨v, hv, -⟩ := mem_of_count_pos hT hpos'
      simp [txTraffic, txSends, show B_SIG ≠ B_MEM by decide, show B_SIG ≠ B_AKMEM by decide] at hv
    · rw [tableBusCount_nobus' (only_of d1_sig_tables ht' (by simpa using h25)) true] at hpos'
      omega

/-- **The `MEM` version bound** of `rcptV3D1`'s reads (the hypothesis of `rcptD1_view`). -/
theorem rcptD1_mem_bound (hp : prepD1 cb h = .ok p) (hlen : (preparedBytesD1 p ov).length < P)
    (hH : HoldsP nearAirV3D1 (ZkFormal.Udr.pubOf Fp (preparedBytesD1 p ov)) tr) :
    ∀ m : List Fp, 0 < tableBusCount tableQD1.interactions tr 16
      (ZkFormal.Udr.pubOf Fp (preparedBytesD1 p ov)) B_MEM false m → (m.getD 1 0).toNat ≤ 2 ^ 25 := by
  intro m hpos
  have hx := extOk_of_prepD1 hp ov hlen
  rcases sender_of_recv hH getElem?_d1_rcpt hpos with hpub | ⟨t', T', ht', hpos'⟩
  · rw [pubCountD1_mem] at hpub; omega
  by_cases h16 : t' = 16
  · subst h16
    rw [getElem?_d1_rcpt] at ht'
    cases ht'
    have hL : LocalD1 tr 16 (ZkFormal.Udr.pubOf Fp (preparedBytesD1 p ov)) :=
      { local_K (rcptD1Local hH) with ext := hx }
    obtain ⟨bs, e, hc⟩ := extract_lists_d1 hL
    have ht := traffic_shift hx.1 (ListChain.view_traffic_d1 hL hc)
    obtain ⟨v, hv, rfl⟩ := mem_of_count_pos ht hpos'
    simp only [ite_true, shiftT, List.mem_map] at hv
    obtain ⟨u, hu, rfl⟩ := hv
    change u ∈ rcptSends3G _ 0 0 _ _ B_MEM at hu
    rw [sends3G_mem] at hu
    have hb := receipt_memory_provider_bound_d1 hL hc hu
    have h1 := toNat_getD1_le (fN (t0V (ZkFormal.Udr.pubOf Fp (preparedBytesD1 p ov)))
      (m0V (ZkFormal.Udr.pubOf Fp (preparedBytesD1 p ov))) B_MEM u)
    have h2 : (fN (t0V (ZkFormal.Udr.pubOf Fp (preparedBytesD1 p ov)))
        (m0V (ZkFormal.Udr.pubOf Fp (preparedBytesD1 p ov))) B_MEM u).getD 1 0 ≤
          u.getD 1 0 + t0V (ZkFormal.Udr.pubOf Fp (preparedBytesD1 p ov)) := by
      simp only [fN, ite_true]; exact getD1_set_le _ _
    have h3 := hx.2.2.1
    omega
  by_cases h17 : t' = 17
  · subst h17
    rw [show nearAirV3D1.tables[17]? = some ZkFormal.NearV3.Assembly.acctTableV3 from rfl] at ht'
    cases ht'
    obtain ⟨as, -, tA⟩ := acctViewD1 hH
    obtain ⟨v, hv, rfl⟩ := mem_of_count_pos tA hpos'
    simp only [ite_true] at hv
    have h0 := account_memory_provider_zero (as := as) (m := v) hv
    have := toNat_getD1_le v
    omega
  by_cases h25 : t' = 25
  · subst h25
    rw [show nearAirV3D1.tables[25]? = some TxV3.table from rfl] at ht'
    cases ht'
    obtain ⟨es, hW, hT⟩ := tx_view tr _ T_TX (txLocal hH)
    obtain ⟨v, hv, rfl⟩ := mem_of_count_pos hT hpos'
    simp only [ite_true, txTraffic, txSends, List.mem_flatMap] at hv
    obtain ⟨e, he, hv⟩ := hv
    split at hv
    · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hv
      have ho := (tx_op_lt hp hlen hH hW hT he).1
      have ht0 := (prepD1_m0_t0 hp).2
      obtain ⟨w, -, rfl⟩ := prepD1_spec hp
      change e.op < w.loc.ops.length at ho
      change w.loc.ops.length ≤ _ at ht0
      have := toNat_getD1_le [e.vidA, e.op + 1, j, (e.lane j).mo, (e.lane j).lk, (e.lane j).st]
      simp only [List.getD_cons_succ, List.getD_cons_zero] at this
      unfold NearSpecV3.NT0 at ht0
      omega
    · simp at hv
  · rw [tableBusCount_nobus' (only_of d1_mem_tables ht' (by simp; omega)) true] at hpos'
    omega

/-- **`rcptV3D1`'s view on the verifier's tape** (the D1 analogue of D0a's
`rcptV3_view_nearAir`): from `prepD1`, the tape bound and `HoldsP` alone. -/
theorem rcptD1_view_prep (hp : prepD1 cb h = .ok p) (hlen : (preparedBytesD1 p ov).length < P)
    (hH : HoldsP nearAirV3D1 (ZkFormal.Udr.pubOf Fp (preparedBytesD1 p ov)) tr) :
    ∃ ls, RcptV3WfD1 (ZkFormal.Udr.pubOf Fp (preparedBytesD1 p ov)) ls ∧
      TableTraffic tableQD1.interactions tr 16 (ZkFormal.Udr.pubOf Fp (preparedBytesD1 p ov))
        (rcptTraffic3D1 (ZkFormal.Udr.pubOf Fp (preparedBytesD1 p ov)) ls) ∧
      ∀ x ∈ flatR ls, x.q < 128 := by
  have hr := prepD1_receipt_ranges hp ov hlen
  exact rcptV3D1_view_nearAir hH (extOk_of_prepD1 hp ov hlen) ⟨hr.count, hr.body⟩
    (rcptD1_mem_bound hp hlen hH)

end ZkFormal.NearV3.D1.Link
