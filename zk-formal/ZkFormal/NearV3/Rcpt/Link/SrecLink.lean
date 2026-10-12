import ZkFormal.NearV3.Rcpt.Link.AkeyAkc
import ZkFormal.NearV3.Rcpt.Link.Srec

/-!
# ZkFormal.NearV3.Rcpt.Link.SrecLink — `SrecBal` from the trace; refunds to their own signer have `ee`

`SREC` is used by rcpt alone.  A received `(q, i, sx_i)` of receipt `q` is sent by a located
receipt `(q', a, v'_a)`; canonical small ids force `q' = q` (the same receipt, `located_flat`),
`a = i` and `v_i = sx_i`.  Hence `SrecBal q x` (**`srecBal_of`**), and with `Srec.srec_neq`:

* **`ee_of_self`** — a system receipt whose signer equals its receiver (as `toBytes`) has
  `ee = true` (so its access-key walk and, with `akf = 0`, `akey_value` apply).
-/

namespace ZkFormal.NearV3.RcptLink

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.Near.Link
  ZkFormal.NearV3.Assembly

theorem rSends_srec (pub : List Fp) (xs : List RcptE) (j r o : Nat) (x : RcptE) :
    rSends pub xs j r o x B_SREC = srecS r x := by
  simp [rSends, srecS, B_SREC, B_BYTES, B_KEYNIB, B_MEM, B_RIDS, B_MPOS]

theorem rRecvs_srec (r : Nat) (x : RcptE) : rRecvs r x B_SREC = srecR r x := by
  simp [rRecvs, srecR, B_SREC, B_DIGEST, B_FINAL, B_MEM]

/-- **`SrecBal` from `HoldsP`.** -/
theorem srecBal_of {pub : List Fp} {tr : Trace Fp} {r : V3Records} (hH : HoldsP nearAirV3 pub tr)
    (T : V3RecordsTraffic pub tr r) (W : V3RecordsWf pub r) {q : Nat} (hq : q < (flatR r.lists).length) :
    SrecBal q (flatR r.lists)[q] := by
  intro m hm
  obtain ⟨toks, -, -, hwf, -⟩ := W.lists.toks
  have hcnt := W.listsCount
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hm
  obtain ⟨hir, hgs⟩ := List.mem_filter.mp hi
  have hir := List.mem_range.mp hir
  have hb := bal_users hH (b := B_SREC) (U := [Assembly.T_RCPT]) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel)
    (Msg.toFp [q, i, (flatR r.lists)[q].sx.getD i 0])
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at hb
  rw [show isAt Assembly.T_RCPT = RcptV3.interactions from rfl, tcnt_of_traffic T.lists,
    tcnt_of_traffic T.lists] at hb
  simp only [tcnt, ite_true, Bool.false_eq_true, ite_false, rcptTraffic3] at hb
  obtain ⟨j, hj, o, hloc⟩ := flat_located hq
  have hrv : 0 < ((rcptRecvs3 r.lists B_SREC).map Msg.toFp).count
      (Msg.toFp [q, i, (flatR r.lists)[q].sx.getD i 0]) := by
    apply List.count_pos_iff.mpr
    apply List.mem_map_of_mem
    simp only [rcptRecvs3, List.mem_flatMap, List.mem_range]
    refine ⟨j, hj, _, hloc, ?_⟩
    rw [rRecvs_srec]
    exact hm
  rw [← hb] at hrv
  obtain ⟨y, hy, hye⟩ := List.mem_map.mp (List.count_pos_iff.mp hrv)
  simp only [rcptSends3, show B_SREC ≠ B_BYTES by decide, show B_SREC ≠ B_RCL by decide, ite_false,
    List.nil_append, List.mem_flatMap, List.mem_range] at hy
  obtain ⟨j', hj', ⟨q', o', x'⟩, hpos, hy⟩ := hy
  rw [rSends_srec] at hy
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hy
  obtain ⟨har, hgv⟩ := List.mem_filter.mp ha
  have har : a < x'.v.length := List.mem_range.mp har
  have hgv : x'.gv.getD a false = true := by simpa using hgv
  obtain ⟨hq', hx'⟩ := located_flat hj' hpos
  -- canonical components
  have hw := hwf q hq
  have hw' := hwf q' hq'
  rw [hx'] at hw'
  have hxm : (flatR r.lists)[q] ∈ flatR r.lists := List.getElem_mem hq
  have hxm' : x' ∈ flatR r.lists := hx' ▸ List.getElem_mem hq'
  have hs64 := (valid_length hw.ids.2.2.1).2
  have hv64 := (valid_length hw'.ids.2.1).2
  simp only [toBytes_length] at hs64 hv64
  simp only [Msg.toFp, List.map_cons, List.map_nil, List.cons.injEq] at hye
  obtain ⟨e1, e2, e3, -⟩ := hye
  have hqq : q' = q := Near.Link.ofNat_inj (by unfold P; omega) (by unfold P; omega) e1
  subst hqq
  rw [← hx'] at har hgv e3 hv64
  have hai : a = i := Near.Link.ofNat_inj (by unfold P; omega) (by unfold P; omega) e2
  subst hai
  have hva : (flatR r.lists)[q'].v.getD a 0 < P := by
    rw [getD_eq_getElem' _ 0 har]
    exact W.lists.canon.2 _ hxm _ (by simp [RcptE.raw3, RcptV.raw])
  have hsa : (flatR r.lists)[q'].sx.getD a 0 < P := by
    have hl := hw.lens.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    rw [getD_eq_getElem' _ 0 (by omega)]
    exact W.lists.canon.2 _ hxm _ (by simp [RcptE.raw3])
  have hval := Near.Link.ofNat_inj hva hsa e3
  apply List.mem_map.mpr
  exact ⟨a, List.mem_filter.mpr ⟨List.mem_range.mpr har, hgv⟩, by rw [hval]⟩

/-- **A system receipt to its own signer has `ee`.** -/
theorem ee_of_self {pub : List Fp} {tr : Trace Fp} {r : V3Records} (hH : HoldsP nearAirV3 pub tr)
    (T : V3RecordsTraffic pub tr r) (W : V3RecordsWf pub r) {q : Nat} (hq : q < (flatR r.lists).length)
    (hs : (flatR r.lists)[q].sys = true)
    (hsv : toBytes (flatR r.lists)[q].s = toBytes (flatR r.lists)[q].v) :
    (flatR r.lists)[q].ee = true := by
  obtain ⟨toks, -, -, hwf, -⟩ := W.lists.toks
  have hw := hwf q hq
  obtain ⟨-, -, -, -, hbv, hbs⟩ := hw.ids
  have heq : (flatR r.lists)[q].s = (flatR r.lists)[q].v := by
    rw [← map_toNat_toBytes hbs, ← map_toNat_toBytes hbv, hsv]
  cases he : (flatR r.lists)[q].ee
  · exact absurd heq (srec_neq hw (srecBal_of hH T W hq) hs he)
  · rfl

end ZkFormal.NearV3.RcptLink
