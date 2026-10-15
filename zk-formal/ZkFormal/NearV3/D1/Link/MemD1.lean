import ZkFormal.NearV3.D1.Link.MemEv
import ZkFormal.NearV3.D1.Link.TxOps
import ZkFormal.NearV3.Rcpt.Link.MemOf

/-!
# `ZkFormal.NearV3.D1.Link.MemD1` — the `MEM` bus of `nearAirV3D1` as one timeline (L1)

Lane `v3-d1-phase2`, item L1 (next step 4/5 of checkpoint 10, `MEM`).  `MEM` has three users in
D1: `rcptV3D1` (16), `acctV3` (17) and `txV3` (25).  The timeline is

* `0`: the acct records open their slots (`awMsg`);
* `o + 1` (`o < T0`): op `o` of `txV3` reads its signer account at `tpA` and writes `mo` (only when
  `s1`), as the event `txRv (txOpOf es o)`;
* `T0 + r + 1`: incoming receipt `r` (`rcptV3D1`'s `MEM` sends are shifted by `T0`).

Definitions: `txOpOf` (the op record with index `o`), `txRv`, the events `evsD1` and the activity
mask `actD1`.  Results:

* `es_perm_ops`: the view's op records, ordered by op index (`tx_ops_perm`);
* `rcptSends3G_mem`: `rcptV3D1`'s `MEM` sends are `wrMsg` at `T0 + r`;
* **`mem_bal_d1`**: the `MEM` balance as `wrsA ~ rdsA` over the D1 events (as `Fp` messages).
-/

namespace ZkFormal.NearV3.D1.Link

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.Near.Link ZkFormal.NearV3
  ZkFormal.NearV3.D1
open ZkFormal.NearV3.RcptLink (R aws ars rv rv_length R_rv)

/-- The op record with index `o` (the view's ops are distinct, `tx_ops_perm`). -/
def txOpOf (es : List TxE) (o : Nat) : TxE := (es.find? fun e => e.op == o).getD default

/-- The 16 lanes of a field of an op. -/
def lanesOf (e : TxE) (f : TxLaneE → Nat) : List Nat := (List.range 16).map fun j => f (e.lane j)

/-- An op as a memory event: slot `vidA`, read time `tpA`, read `amt`, written `mo`. -/
def txRv (e : TxE) : RcptV :=
  { (default : RcptV) with kslot := e.vidA, tprev := e.tpA, bef := lanesOf e TxLaneE.amt,
                           aft := lanesOf e TxLaneE.mo, lk := lanesOf e TxLaneE.lk, st := lanesOf e TxLaneE.st }

/-- The D1 memory events: the `T0` ops, then the incoming receipts. -/
def evsD1 (es : List TxE) (t0 : Nat) (ls : RcptV3Vs) : List RcptV :=
  (List.range t0).map (fun o => txRv (txOpOf es o)) ++ rv ls

/-- An op touches `MEM` iff `s1`; every receipt does. -/
def actD1 (es : List TxE) (t0 : Nat) (t : Nat) : Bool :=
  if t < t0 then (txOpOf es t).s1 == 1 else true

theorem txOpOf_eq {es : List TxE} (hnd : (es.map TxE.op).Nodup) {e : TxE} (he : e ∈ es) :
    txOpOf es e.op = e := by
  unfold txOpOf
  induction es with
  | nil => cases he
  | cons x xs ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [List.find?_cons]
    rcases List.mem_cons.mp he with rfl | he'
    · simp
    · by_cases hx : x.op = e.op
      · exact absurd (hx ▸ List.mem_map_of_mem he') hnd.1
      · simp only [show (x.op == e.op) = false from by simpa using hx]
        exact ih hnd.2 he'

theorem txRv_wr (e : TxE) (o i : Nat) (hi : i < 16) :
    wrMsg (txRv e) o i = [e.vidA, o + 1, i, (e.lane i).mo, (e.lane i).lk, (e.lane i).st] := by
  simp [wrMsg, txRv, lanesOf, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]

theorem txRv_rd (e : TxE) (i : Nat) (hi : i < 16) :
    rdMsg (txRv e) i = [e.vidA, e.tpA, i, (e.lane i).amt, (e.lane i).lk, (e.lane i).st] := by
  simp [rdMsg, txRv, lanesOf, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]

/-- `rcptV3D1`'s `MEM` sends: receipt `r` writes at `T0 + r + 1`. -/
theorem rcptSends3G_mem (o0 t0 m0 : Nat) (pub : List Fp) (ls : RcptV3Vs) :
    RcptD1.rcptSends3G o0 t0 m0 pub ls B_MEM =
      (flatR ls).zipIdx.flatMap fun p => (List.range 16).map (wrMsg p.1.toRcptV (t0 + p.2)) := by
  simp only [RcptD1.rcptSends3G, show B_MEM ≠ B_BYTES by decide, show B_MEM ≠ B_RCL by decide,
    ite_false, List.nil_append]
  have hs : ∀ (j : Nat) (p : Nat × Nat × RcptE), RcptD1.rSendsG o0 t0 m0 pub (flatR ls) j p.1 p.2.1 p.2.2 B_MEM =
      (List.range 16).map (wrMsg p.2.2.toRcptV (t0 + p.1)) := by
    intro j p
    simp only [RcptD1.rSendsG, show B_MEM ≠ B_BYTES by decide, show B_MEM ≠ B_KEYNIB by decide, ite_false,
      ite_true]
    apply List.map_congr_left
    intro i _
    simp only [wrMsg]
    congr 1
    simp only [List.cons.injEq]
    exact ⟨by omega, trivial⟩
  simp only [hs]
  exact ZkFormal.NearV3.Assembly.LinkRids.located_flat ls (fun r x => (List.range 16).map (wrMsg x.toRcptV (t0 + r)))

/-! ## The events, split -/

theorem R_evs_tx {es : List TxE} {t0 : Nat} {ls : RcptV3Vs} {o : Nat} (ho : o < t0) :
    R (evsD1 es t0 ls) o = txRv (txOpOf es o) := by
  simp only [R, evsD1, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by simpa using ho)]
  simp [List.getElem?_map, List.getElem?_range ho]

theorem R_evs_rc {es : List TxE} {t0 : Nat} {ls : RcptV3Vs} (r : Nat) :
    R (evsD1 es t0 ls) (t0 + r) = R (rv ls) r := by
  simp only [R, evsD1, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by simp)]
  simp

theorem evsD1_length (es : List TxE) (t0 : Nat) (ls : RcptV3Vs) :
    (evsD1 es t0 ls).length = t0 + (flatR ls).length := by
  simp [evsD1, rv_length]

/-- The op part of the event writes. -/
def txWr (es : List TxE) (t0 : Nat) : List Msg :=
  (List.range t0).flatMap fun o => if (txOpOf es o).s1 = 1 then
    (List.range 16).map (wrMsg (txRv (txOpOf es o)) o) else []
def txRd (es : List TxE) (t0 : Nat) : List Msg :=
  (List.range t0).flatMap fun o => if (txOpOf es o).s1 = 1 then
    (List.range 16).map (rdMsg (txRv (txOpOf es o))) else []

theorem wrsA_split (es : List TxE) (t0 : Nat) (ls : RcptV3Vs) :
    wrsA (actD1 es t0) (evsD1 es t0 ls) = txWr es t0 ++
      (flatR ls).zipIdx.flatMap fun p => (List.range 16).map (wrMsg p.1.toRcptV (t0 + p.2)) := by
  unfold wrsA
  rw [evsD1_length, List.range_add, List.flatMap_append, List.flatMap_map,
    ZkFormal.NearV3.RcptLink.zipIdx_flatMap_eq]
  congr 1
  · unfold txWr
    apply ZkFormal.Near.flatMap_congr'
    intro o ho
    have ho' := List.mem_range.mp ho
    simp only [actD1, ho', ite_true, R_evs_tx ho', beq_iff_eq]
  · apply ZkFormal.Near.flatMap_congr'
    intro r _
    simp only [actD1, show ¬ (t0 + r < t0) by omega, ite_false, ite_true, R_evs_rc, R_rv]

theorem rdsA_split (es : List TxE) (t0 : Nat) (ls : RcptV3Vs) :
    rdsA (actD1 es t0) (evsD1 es t0 ls) = txRd es t0 ++
      (flatR ls).zipIdx.flatMap fun p => (List.range 16).map (rdMsg p.1.toRcptV) := by
  unfold rdsA
  rw [evsD1_length, List.range_add, List.flatMap_append, List.flatMap_map,
    ZkFormal.NearV3.RcptLink.zipIdx_flatMap_eq]
  congr 1
  · unfold txRd
    apply ZkFormal.Near.flatMap_congr'
    intro o ho
    have ho' := List.mem_range.mp ho
    simp only [actD1, ho', ite_true, R_evs_tx ho', beq_iff_eq]
  · apply ZkFormal.Near.flatMap_congr'
    intro r _
    simp only [actD1, show ¬ (t0 + r < t0) by omega, ite_false, ite_true, R_evs_rc, R_rv]

/-! ## The balance -/

section
variable {cb : NearSpec.Bytes} {h : HintD1} {p : Public.PrepD1} {ov : Nat} {tr : Trace Fp}
  {r : ZkFormal.NearV3.Assembly.V3Records} {es : List TxE}
  (hp : prepD1 cb h = .ok p) (hlen : (Public.preparedBytesD1 p ov).length < P)
  (hH : HoldsP nearAirV3D1 (ZkFormal.Udr.pubOf Fp (Public.preparedBytesD1 p ov)) tr) (hW : TxWf es)
  (hT : TableTraffic TxV3.interactions tr T_TX (ZkFormal.Udr.pubOf Fp (Public.preparedBytesD1 p ov)) (txTraffic es))
include hp hlen hH hW hT

theorem txOpOf_op {o : Nat} (ho : o < p.ops.length) : txOpOf es o ∈ es ∧ (txOpOf es o).op = o := by
  have hperm := tx_ops_perm hp hlen hH hW hT
  have hnd : (es.map TxE.op).Nodup := hperm.nodup_iff.mpr List.nodup_range
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp (hperm.mem_iff.mpr (List.mem_range.mpr ho))
  rw [txOpOf_eq hnd he]
  exact ⟨he, rfl⟩

/-- **The view's op records, by op index.** -/
theorem es_perm_ops : es.Perm ((List.range p.ops.length).map (txOpOf es)) := by
  have hperm := tx_ops_perm hp hlen hH hW hT
  have hnd : (es.map TxE.op).Nodup := hperm.nodup_iff.mpr List.nodup_range
  have e1 : (es.map TxE.op).map (txOpOf es) = es := by
    rw [List.map_map]
    have : ∀ e ∈ es, (txOpOf es ∘ TxE.op) e = id e := fun e he => txOpOf_eq hnd he
    rw [List.map_congr_left this, List.map_id]
  have := hperm.map (txOpOf es)
  rwa [e1] at this

theorem txSends_mem_perm : (txSends es B_MEM).Perm (txWr es p.ops.length) := by
  have hs : txSends es B_MEM = es.flatMap fun e => if e.s1 = 1 then
      (List.range 16).map (wrMsg (txRv e) e.op) else [] := by
    simp only [txSends, ite_true]
    apply ZkFormal.Near.flatMap_congr'
    intro e _
    split
    · apply List.map_congr_left
      intro j hj
      rw [txRv_wr e e.op j (List.mem_range.mp hj)]
    · rfl
  rw [hs]
  refine ((es_perm_ops hp hlen hH hW hT).flatMap_right _).trans ?_
  rw [List.flatMap_map]
  unfold txWr
  apply List.Perm.of_eq
  apply ZkFormal.Near.flatMap_congr'
  intro o ho
  rw [(txOpOf_op hp hlen hH hW hT (List.mem_range.mp ho)).2]

theorem txRecvs_mem_perm : (txRecvs es B_MEM).Perm (txRd es p.ops.length) := by
  have hs : txRecvs es B_MEM = es.flatMap fun e => if e.s1 = 1 then
      (List.range 16).map (rdMsg (txRv e)) else [] := by
    simp only [txRecvs, show B_MEM ≠ B_TXP by decide, show B_MEM ≠ B_SIG by decide,
      show B_MEM ≠ B_FINAL by decide, ite_false, ite_true]
    apply ZkFormal.Near.flatMap_congr'
    intro e _
    split
    · apply List.map_congr_left
      intro j hj
      rw [txRv_rd e j (List.mem_range.mp hj)]
    · rfl
  rw [hs]
  refine ((es_perm_ops hp hlen hH hW hT).flatMap_right _).trans ?_
  rw [List.flatMap_map]
  rfl

/-- **The `MEM` balance of `nearAirV3D1`** over the D1 events (ops, then incoming receipts). -/
theorem mem_bal_d1 (T : BaseTrafficD1 (ZkFormal.Udr.pubOf Fp (Public.preparedBytesD1 p ov)) tr r) :
    ((wrsA (actD1 es p.ops.length) (evsD1 es p.ops.length r.lists) ++ aws r.accts).map Msg.toFp).Perm
      ((rdsA (actD1 es p.ops.length) (evsD1 es p.ops.length r.lists) ++ ars r.accts).map Msg.toFp) := by
  have ht0 : RcptD1.t0V (ZkFormal.Udr.pubOf Fp (Public.preparedBytesD1 p ov)) = p.ops.length := by
    have hm := (prepD1_m0_t0 hp).2
    unfold NearSpecV3.NT0 at hm
    rw [Public.t0V_prepared p ov (prepD1_roots hp) (by omega)]
    obtain ⟨w, -, rfl⟩ := prepD1_spec hp
    rfl
  apply List.perm_iff_count.mpr
  intro m
  have hb := ZkFormal.NearV3.Assembly.bal_users_d1 hH (b := B_MEM) (U := [16, 17, 25]) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) m
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at hb
  rw [show isAtD1 16 = RcptD1.tableQD1.interactions from rfl, (T.lists B_MEM m).1, (T.lists B_MEM m).2,
    show isAtD1 17 = ZkFormal.NearV3.AcctV3.interactions from rfl,
    show (17 : Nat) = ZkFormal.NearV3.Assembly.T_ACCT from rfl, (T.accts B_MEM m).1, (T.accts B_MEM m).2,
    show isAtD1 25 = TxV3.interactions from rfl, show (25 : Nat) = T_TX from rfl,
    (hT B_MEM m).1, (hT B_MEM m).2] at hb
  simp only [RcptD1.rcptTraffic3D1, RcptD1.rcptTraffic3G, ZkFormal.NearV3.acctV3Traffic, txTraffic,
    rcptSends3G_mem, ht0, ZkFormal.NearV3.RcptLink.rcptRecvs3_mem, ZkFormal.NearV3.RcptLink.acctV3Sends_mem,
    ZkFormal.NearV3.RcptLink.acctRecvs_mem'] at hb
  rw [((txSends_mem_perm hp hlen hH hW hT).map Msg.toFp).count_eq,
    ((txRecvs_mem_perm hp hlen hH hW hT).map Msg.toFp).count_eq] at hb
  rw [wrsA_split, rdsA_split]
  simp only [aws, ars, List.map_append, List.count_append] at hb ⊢
  omega


/-! ## `MemHypA` from the trace -/

open ZkFormal.NearV3.RcptLink (getD_lt' getElem_flatR_mem mem_raw_of mem_raw3_of) in
/-- **`MemHypA` of the D1 events** from `HoldsP`, the views and the distinct account slots. -/
theorem memHypA_of (T : BaseTrafficD1 (ZkFormal.Udr.pubOf Fp (Public.preparedBytesD1 p ov)) tr r)
    (W : BaseWfD1 (ZkFormal.Udr.pubOf Fp (Public.preparedBytesD1 p ov)) r)
    (hknd : (r.accts.map (·.k)).Nodup) :
    MemHypA (actD1 es p.ops.length) (evsD1 es p.ops.length r.lists) r.accts := by
  have ht0 : RcptD1.t0V (ZkFormal.Udr.pubOf Fp (Public.preparedBytesD1 p ov)) = p.ops.length := by
    have hm := (prepD1_m0_t0 hp).2
    unfold NearSpecV3.NT0 at hm
    rw [Public.t0V_prepared p ov (prepD1_roots hp) (by omega)]
    obtain ⟨w, -, rfl⟩ := prepD1_spec hp
    rfl
  have hT0 : p.ops.length ≤ 8192 := by
    have := (prepD1_m0_t0 hp).2
    obtain ⟨w, -, rfl⟩ := prepD1_spec hp
    unfold NearSpecV3.NT0 at this
    exact this
  obtain ⟨toks, -, -, hwf, -⟩ := W.lists.toks
  have hn : (flatR r.lists).length ≤ 2 ^ 22 := W.listsCount.2
  have hwfR : ∀ q, q < (flatR r.lists).length → ∃ a b c,
      ((flatR r.lists).getD q default).Wf (q + p.ops.length) a b c := by
    intro q hq
    have := hwf q hq
    rw [ht0] at this
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq]
    exact ⟨_, _, _, this⟩
  have hraw : ∀ q, q < (flatR r.lists).length → ∀ y ∈ ((flatR r.lists).getD q default).raw, y < P :=
    fun q hq y hy => W.lists.canon.2 _ (getElem_flatR_mem hq) y (mem_raw3_of hy)
  have hacc : ∀ a ∈ r.accts, (a.k < P ∧ a.tlast < P) ∧ ∀ y ∈ a.pre ++ a.post, y < P := by
    intro a ha
    rcases W.accts with he | hw
    · rw [he] at ha; cases ha
    · exact ⟨⟨(hw.v1.len a ha).2.2.1, (hw.v1.len a ha).2.2.2⟩, hw.v1.canon a ha⟩
  have hlane : ∀ a ∈ r.accts, ∀ (l : List Nat), (∀ y ∈ l, y < P) → ∀ i, ∀ y ∈ acctLane a l i, y < P := by
    intro a ha l hl i y hy
    simp only [acctLane, List.mem_cons, List.not_mem_nil, or_false] at hy
    have hpre : ∀ y ∈ a.pre, y < P := fun y hy => (hacc a ha).2 y (by simp [hy])
    rcases hy with rfl | rfl | rfl
    · exact getD_lt' hl i
    · exact getD_lt' hpre _
    · split
      · exact getD_lt' hpre _
      · unfold P; omega
  have hlenE := evsD1_length es p.ops.length r.lists
  -- the op events' fields are canonical
  have htx : ∀ o, o < p.ops.length → (txOpOf es o).s1 = 1 → ∀ i, i < 16 →
      (txOpOf es o).vidA < P ∧ (txOpOf es o).tpA < P ∧ ((txOpOf es o).lane i).amt < P ∧
        ((txOpOf es o).lane i).mo < P ∧ ((txOpOf es o).lane i).lk < P ∧ ((txOpOf es o).lane i).st < P := by
    intro o ho _ i hi
    have hc := ((hW.ops _ (txOpOf_op hp hlen hH hW hT ho).1).canon)
    have hl := hc.2.2.2.2.2 i hi
    exact ⟨hc.2.1, hc.2.2.2.1, hl.2.2.2.2.1, hl.2.2.2.2.2.2.2.1, hl.2.2.2.2.2.1, hl.2.2.2.2.2.2.1⟩
  have hP : 2 ^ 23 + 8192 < P := by unfold P; omega
  refine ⟨?_, hknd, ?_⟩
  · have hpm := mem_bal_d1 hp hlen hH hW hT T
    apply perm_nat _ _ hpm
    · intro m hm
      rcases mem_WA.mp hm with ⟨q, hq, hact, i, hi, rfl⟩ | ⟨a, ha, i, hi, rfl⟩
      · rw [hlenE] at hq
        by_cases hqT : q < p.ops.length
        · rw [R_evs_tx hqT, txRv_wr _ _ _ hi]
          have hs1 : (txOpOf es q).s1 = 1 := by simpa [actD1, hqT] using hact
          obtain ⟨c1, -, c3, c4, c5, c6⟩ := htx q hqT hs1 i hi
          intro y hy
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
          rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
          · exact c1
          · omega
          · omega
          · exact c4
          · exact c5
          · exact c6
        · obtain ⟨q', rfl⟩ : ∃ q', q = p.ops.length + q' := ⟨q - p.ops.length, by omega⟩
          have hq' : q' < (flatR r.lists).length := by omega
          rw [R_evs_rc, R_rv]
          obtain ⟨_, _, _, w⟩ := hwfR q' hq'
          intro y hy
          simp only [wrMsg, List.mem_cons, List.not_mem_nil, or_false] at hy
          rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
          · exact w.small.1
          · omega
          · unfold P; omega
          · exact getD_lt' (fun y hy => by have := w.aft8 y hy; unfold P; omega) i
          · exact getD_lt' (fun y hy => hraw q' hq' y (mem_raw_of (.inr (.inl hy)))) i
          · exact getD_lt' (fun y hy => hraw q' hq' y (mem_raw_of (.inr (.inr hy)))) i
      · intro y hy
        simp only [awMsg, List.cons_append, List.mem_cons] at hy
        rcases hy with rfl | rfl | rfl | hy
        · exact (hacc a ha).1.1
        · unfold P; omega
        · unfold P; omega
        · exact hlane a ha _ (fun y hy => (hacc a ha).2 y (by simp [hy])) i y hy
    · intro m hm
      simp only [rdsA, ars, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range] at hm
      rcases hm with ⟨q, hq, hm⟩ | ⟨a, ha, i, hi, rfl⟩
      · rw [hlenE] at hq
        split at hm
        · rename_i hact
          obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hm
          have hi' := List.mem_range.mp hi
          by_cases hqT : q < p.ops.length
          · rw [R_evs_tx hqT, txRv_rd _ _ hi']
            have hs1 : (txOpOf es q).s1 = 1 := by simpa [actD1, hqT] using hact
            obtain ⟨c1, c2, c3, -, c5, c6⟩ := htx q hqT hs1 i hi'
            intro y hy
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
            rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
            · exact c1
            · exact c2
            · omega
            · exact c3
            · exact c5
            · exact c6
          · obtain ⟨q', rfl⟩ : ∃ q', q = p.ops.length + q' := ⟨q - p.ops.length, by omega⟩
            have hq' : q' < (flatR r.lists).length := by omega
            rw [R_evs_rc, R_rv]
            obtain ⟨_, _, _, w⟩ := hwfR q' hq'
            intro y hy
            simp only [rdMsg, List.mem_cons, List.not_mem_nil, or_false] at hy
            rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
            · exact w.small.1
            · exact w.small.2.1
            · omega
            · exact getD_lt' (fun y hy => hraw q' hq' y (mem_raw_of (.inl hy))) i
            · exact getD_lt' (fun y hy => hraw q' hq' y (mem_raw_of (.inr (.inl hy)))) i
            · exact getD_lt' (fun y hy => hraw q' hq' y (mem_raw_of (.inr (.inr hy)))) i
        · simp at hm
      · intro y hy
        simp only [arMsg, List.cons_append, List.mem_cons] at hy
        rcases hy with rfl | rfl | rfl | hy
        · exact (hacc a ha).1.1
        · exact (hacc a ha).1.2
        · unfold P; omega
        · exact hlane a ha _ (fun y hy => (hacc a ha).2 y (by simp [hy])) i y hy
  · intro q hq hact ht
    rw [hlenE] at hq ht
    by_cases hqT : q < p.ops.length
    · rw [R_evs_tx hqT] at ht ⊢
      have hs1 : (txOpOf es q).s1 = 1 := by simpa [actD1, hqT] using hact
      obtain ⟨hmem, hop⟩ := txOpOf_op hp hlen hH hW hT hqT
      obtain ⟨d, hd, he⟩ := (hW.ops _ hmem).tA hs1
      change (txOpOf es q).tpA ≤ _ at ht
      change (txOpOf es q).tpA ≤ q
      rw [hop] at he
      have := congrArg Fp.toNat he
      rw [Fp.toNat_ofNat, Fp.toNat_ofNat, Nat.mod_eq_of_lt (by unfold P; omega),
        Nat.mod_eq_of_lt (by unfold P; omega)] at this
      omega
    · obtain ⟨q', rfl⟩ : ∃ q', q = p.ops.length + q' := ⟨q - p.ops.length, by omega⟩
      have hq' : q' < (flatR r.lists).length := by omega
      rw [R_evs_rc, R_rv] at ht ⊢
      obtain ⟨_, _, _, w⟩ := hwfR q' hq'
      have := w.tprev_le (by unfold P; omega)
      omega

end

end ZkFormal.NearV3.D1.Link
