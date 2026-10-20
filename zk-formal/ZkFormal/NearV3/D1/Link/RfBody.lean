import ZkFormal.NearV3.D1.Link.Keynib
import ZkFormal.NearV3.Rcpt.Link.RfBody

/-!
# `ZkFormal.NearV3.D1.Link.RfBody` — the refund stream at the body offset `O0` (L1)

Lane `v3-d1-phase2`, item L1 (the body delta, next step 3 of checkpoint 10).  The D1 body is
`u32 |newTxs| ‖ newTxs ‖ u32 |out| ‖ enc (fwd ++ local refunds) ‖ enc refunds`; the receipt view
sends its refunds at `bOffsG O0` (from `O0`), and the public body-prefix segment sends positions
`8 … O0 − 1` (they cancel D0a's body receive there).  Support for `rfStream_body` (D1):

* `bOffsG_flat`, `bOffsG_total`: `bOffsG o0 xs q = o0 + |refund bytes before q|`;
* `rfG_isolate`: the receipt `BYTES` messages with id `K_RF` are refund bytes at `bOffsG`;
* `rfStream_atG`: the refund stream at receipt `q`'s offset;
* **`pub_bytes_send_mem`**: a public `BYTES` send is a body-prefix record `(K_RF, 8 + j, B[8 + j])`
  with `8 + j < O0`.
-/

namespace ZkFormal.NearV3.D1.Link

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.Near.Link ZkFormal.NearV3
  ZkFormal.NearV3.D1 ZkFormal.NearV3.RcptLink

theorem bOffsG_flat (o0 : Nat) (xs : List RcptE) (q : Nat) :
    RcptD1.bOffsG o0 xs q = o0 + ((xs.take q).flatMap rfS).length := by
  unfold RcptD1.bOffsG
  congr 1
  induction xs.take q with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.length_append, ih, rfLen_eq]

theorem bOffsG_total (o0 : Nat) (ls : RcptV3Vs) :
    RcptD1.bOffsG o0 (flatR ls) (flatR ls).length = o0 + (rfStream ls).length := by
  rw [bOffsG_flat, List.take_length]; rfl

/-- Of a receipt's byte streams (D1 offsets), only its refund stream has id `K_RF`. -/
theorem receipt_sends_rfG {o0 t0 m0 : Nat} {pub : List Fp} {xs : List RcptE} {j r off : Nat} {x : RcptE}
    {m : Msg} (hm : m ∈ RcptD1.rSendsG o0 t0 m0 pub xs j r off x B_BYTES) (ha : m.head? = some K_RF) :
    x.hr = true ∧ m ∈ emitAt K_RF (RcptD1.bOffsG o0 xs r) x.encRefund := by
  simp only [RcptD1.rSendsG, ite_true, List.mem_append] at hm
  rcases hm with (((hm | hm) | hm) | hm) | hm
  · have hh := emitAt_head_eq hm ha
    exfalso; unfold msgId K_RC K_RF at hh; omega
  · split at hm
    · next hr => exact ⟨hr, hm⟩
    · simp at hm
  · have hh := emitAt_head_eq hm ha
    exfalso; unfold msgId K_PEO K_RF at hh; omega
  · have hh := emitAt_head_eq hm ha
    exfalso; unfold msgId K_LEAF K_RF at hh; omega
  · split at hm
    · have hh := emitAt_head_eq hm ha
      exfalso; unfold msgId K_RID K_RF at hh; omega
    · simp at hm

/-- **`RF` isolation** (D1 offsets). -/
theorem rfG_isolate {o0 t0 m0 : Nat} {pub : List Fp} {ls : RcptV3Vs} {m : Msg}
    (hm : m ∈ RcptD1.rcptSends3G o0 t0 m0 pub ls B_BYTES) (ha : m.head? = some K_RF) :
    ∃ q, ∃ hq : q < (flatR ls).length, (flatR ls)[q].hr = true ∧ ∃ i, i < (flatR ls)[q].encRefund.length ∧
      m = [K_RF, RcptD1.bOffsG o0 (flatR ls) q + i, (flatR ls)[q].encRefund.getD i 0] := by
  simp only [RcptD1.rcptSends3G, ite_true, show B_BYTES ≠ B_RCL by decide, ite_false, List.append_nil] at hm
  obtain ⟨j, hj, hm⟩ := List.mem_flatMap.mp hm
  have hj := List.mem_range.mp hj
  rcases List.mem_append.mp hm with hm | hm
  · have hid := emitAt_head_eq hm ha
    exfalso; unfold msgId K_RC K_RF at hid; omega
  · obtain ⟨⟨q, off, x⟩, hpos, hm⟩ := List.mem_flatMap.mp hm
    obtain ⟨hr, hm⟩ := receipt_sends_rfG hm ha
    obtain ⟨hq, hx⟩ := located_flat hj hpos
    refine ⟨q, hq, by rw [hx]; exact hr, ?_⟩
    rw [hx]
    obtain ⟨i, hi, rfl⟩ := ZkFormal.NearV3.Link3.mem_emitAt3.mp hm
    exact ⟨i, hi, rfl⟩

/-- The refund stream at receipt `q`'s body offset (D1). -/
theorem rfStream_atG (o0 : Nat) {ls : RcptV3Vs} {q : Nat} (hq : q < (flatR ls).length)
    (hr : (flatR ls)[q].hr = true) {i : Nat} (hi : i < (flatR ls)[q].encRefund.length) :
    RcptD1.bOffsG o0 (flatR ls) q - o0 + i < (rfStream ls).length ∧
      (rfStream ls).getD (RcptD1.bOffsG o0 (flatR ls) q - o0 + i) 0 = (flatR ls)[q].encRefund.getD i 0 := by
  have hi' : i < (rfS (flatR ls)[q]).length := by simp only [rfS, hr, ite_true]; exact hi
  obtain ⟨h1, h2⟩ := getD_flatMap_at rfS (flatR ls) q hq i hi'
  rw [bOffsG_flat, Nat.add_sub_cancel_left]
  refine ⟨h1, ?_⟩
  unfold rfStream
  rw [h2]
  simp only [rfS, hr, ite_true]

open ZkFormal.NearV3.D1.Public in
set_option maxHeartbeats 2000000 in
/-- **A public `BYTES` send** of the verifier's tape is a body-prefix record `(K_RF, 8 + j, B[8 + j])`,
`8 + j < O0`. -/
theorem pub_bytes_send_mem (p : PrepD1) (ov : Nat) (hr : ZkFormal.NearV3.Public.RootsSized p.base)
    (hs : ∀ s ∈ p.base.lists, s.root.length = 32) (hleaves : ∀ l ∈ p.leaves, l.length = 32)
    (hlen : (preparedBytesD1 p ov).length < 256 ^ 4) {m : List Fp}
    (hpos : 0 < pubCount nearAirV3D1 (ZkFormal.Udr.pubOf Fp (preparedBytesD1 p ov)) B_BYTES true m) :
    ∃ j, 8 + j < p.o0 ∧ 8 + j < p.base.body.length ∧
      m = [Fp.ofNat K_RF, Fp.ofNat (8 + j), ZkFormal.NearV3.Public.byteF (p.base.body.getD (8 + j) 0)] := by
  rw [pubCountD1_split p ov hr hs hlen, ZkFormal.NearV3.Assembly.pubCount_noside segs_no_bytes_send, Nat.zero_add] at hpos
  obtain ⟨x, hx⟩ := List.exists_mem_of_length_pos hpos
  rw [List.mem_filter, decide_eq_true_eq] at hx
  obtain ⟨hx, rfl⟩ := hx
  rw [newMsgs_eq p ov hr hlen hleaves] at hx
  simp only [List.mem_append] at hx
  rcases hx with (((((h | h) | h) | h) | h) | h) <;> obtain ⟨j, hj, he⟩ := mem_tagged h <;>
    simp only [Prod.mk.injEq] at he
  · have hj' : 8 + j < p.o0 ∧ 8 + j < p.base.body.length := by
      simp only [prefixPayload, List.length_map, List.length_drop, List.length_take] at hj
      omega
    refine ⟨j, hj'.1, hj'.2, ?_⟩
    rw [he.2.2]
    simp only [ZkFormal.NearV3.Public.recordValues, bodyPrefixPlan, prefixPayload, List.map_cons,
      List.map_nil, List.cons_append, List.nil_append, K_RF]
    have hj2 : j < ((p.base.body.take p.o0).drop 8).length := by
      simp only [List.length_drop, List.length_take]; omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj2]
    simp only [Option.map_some, Option.getD_some, List.getElem_drop, List.getElem_take, List.map_cons,
      List.map_nil, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj'.2]
    rfl
  all_goals exact absurd he.1 (by decide)

end ZkFormal.NearV3.D1.Link
