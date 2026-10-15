import ZkFormal.NearV3.D1.L.Assembly.LinkBus
import ZkFormal.NearV3.D1.Link.PlfIds
import ZkFormal.NearV3.Assembly.LinkRids

/-!
# `ZkFormal.NearV3.D1.Link.Rids` — the `RIDS` bus with the local receipt ids (L1)

Lane `v3-d1-phase2`, item L1 (next step 1 of checkpoint 10).  In `nearAirV3D1` the `RIDS` bus
has three users: the receipt view (`(r, i, rid_r[i])` for the incoming receipts, `r < |flatR|`),
the sort table (receives) and `ridV3` (`(W_LOC + l, i, b)` for the public `PRID` bytes
`(j, b)`, `j = 32·l + i`).

* `RidLRange`: the interface for the AIR range check on `ridV3`'s free column `l` (lane
  `v3-d1-a7b`, soundness fix): `l < 2^20`.  Any range check `l < 2^k`, `k ≤ 20`, implies it.
  With it, `j = 32·l + i` holds over the naturals, so `l = j / 32`, `i = j % 32`;
  **discharged** by the AIR's range check (`RidWf.lrange`: `l < 2^12`, lane `v3-d1-a7b` `cb9f87f9`):
  `ridLRange_of`;
* `pub_prid_mem` / `pub_prid_pos`: the public `PRID` messages are exactly
  `(j, ridPayload[j])` (the bytes of `p.rids`, in order);
* `rid_entry`: every `ridV3` record carries the public byte `rids[l][i]`;
  `rid_local`: every local id `l < |rids|` has a record with index `(l, 0)`;
* `rids_bal_d1'`: the receipt view's id sends and `ridV3`'s sends are, as `Fp` messages, a
  permutation of a sort view's receives (or all three are silent);
* **`receiptIdsD1`**: the local ids followed by the incoming receipts' ids are pairwise
  distinct (`MainExecutionD1.distinctIds`, with `localIds = p.rids`), given byte-valued
  incoming ids and `|flatR| ≤ W_LOC`.
-/

namespace ZkFormal.NearV3.D1.Link

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.NearV3 ZkFormal.NearV3.D1
open ZkFormal.NearV3.D1.Public

/-- **The range-check interface on `ridV3`'s column `l`** (lane `v3-d1-a7b`). -/
def RidLRange (es : List RidE) : Prop := ∀ e ∈ es, e.l < 2 ^ 20

/-- **`RidLRange` holds for every `ridV3` view**: the AIR range-checks `l` to 12 bits. -/
theorem ridLRange_of {es : List RidE} (hW : RidWf es) : RidLRange es :=
  fun e he => Nat.lt_of_lt_of_le (hW.lrange e he) (by decide)

/-- `rcptV3D1`'s `RIDS` sends are D0a's. -/
theorem rcptSends3G_rids (o0 t0 m0 : Nat) (pub : List Fp) (ls : RcptV3Vs) :
    RcptD1.rcptSends3G o0 t0 m0 pub ls B_RIDS = rcptSends3 pub ls B_RIDS := by
  simp only [RcptD1.rcptSends3G, rcptSends3, RcptD1.rSendsG, rSends, show B_RIDS ≠ B_BYTES by decide,
    show B_RIDS ≠ B_RCL by decide, show B_RIDS ≠ B_KEYNIB by decide, show B_RIDS ≠ B_MEM by decide,
    ite_false, ite_true]

/-! ## The public `PRID` segment -/

theorem segs_no_prid : ∀ s ∈ ZkFormal.NearV3.Assembly.nearAirV3.pubSegs, s.bus ≠ B_PRID := by
  have hall : ZkFormal.NearV3.Public.preparedSegments.all (fun s => decide (s.bus ≠ B_PRID)) = true := by
    decide +kernel
  intro s hs
  exact of_decide_eq_true (List.all_eq_true.mp hall s hs)

theorem d1_prid_tables : onlyOn B_PRID [T_RID] = true := by decide +kernel

set_option maxHeartbeats 2000000 in
/-- **A public `PRID` message** of the verifier's tape is `[j] ++ ridPayload[j]`. -/
theorem pub_prid_mem (p : PrepD1) (ov : Nat) (hr : ZkFormal.NearV3.Public.RootsSized p.base)
    (hs : ∀ s ∈ p.base.lists, s.root.length = 32) (hleaves : ∀ l ∈ p.leaves, l.length = 32)
    (hlen : (preparedBytesD1 p ov).length < 256 ^ 4) {sd : Bool} {m : List Fp}
    (hpos : 0 < pubCount nearAirV3D1 (ZkFormal.Udr.pubOf Fp (preparedBytesD1 p ov)) B_PRID sd m) :
    sd = true ∧ ∃ j < (ridPayload p.rids).length,
      m = ((j : Nat) : Fp) :: ((ridPayload p.rids).getD j []).map ZkFormal.NearV3.Public.byteF := by
  rw [pubCountD1_split p ov hr hs hlen, pubCount_nobus segs_no_prid sd, Nat.zero_add] at hpos
  obtain ⟨x, hx⟩ := List.exists_mem_of_length_pos hpos
  rw [List.mem_filter, decide_eq_true_eq] at hx
  obtain ⟨hx, rfl⟩ := hx
  rw [newMsgs_eq p ov hr hlen hleaves] at hx
  simp only [List.mem_append] at hx
  rcases hx with (((((h | h) | h) | h) | h) | h) <;> obtain ⟨j, hj, he⟩ := mem_tagged h <;>
    simp only [Prod.mk.injEq] at he
  · exact absurd he.1 (by decide)
  · exact absurd he.1 (by decide)
  · exact absurd he.1 (by decide)
  · exact absurd he.1 (by decide)
  · exact absurd he.1 (by decide)
  · refine ⟨he.2.1, j, hj, ?_⟩
    rw [he.2.2]
    simp [ZkFormal.NearV3.Public.recordValues, ridPlan]

set_option maxHeartbeats 2000000 in
/-- **Every public `PRID` message is sent**: `[j] ++ ridPayload[j]` for `j < |ridPayload|`. -/
theorem pub_prid_pos (p : PrepD1) (ov : Nat) (hr : ZkFormal.NearV3.Public.RootsSized p.base)
    (hs : ∀ s ∈ p.base.lists, s.root.length = 32) (hleaves : ∀ l ∈ p.leaves, l.length = 32)
    (hlen : (preparedBytesD1 p ov).length < 256 ^ 4) {j : Nat} (hj : j < (ridPayload p.rids).length) :
    0 < pubCount nearAirV3D1 (ZkFormal.Udr.pubOf Fp (preparedBytesD1 p ov)) B_PRID true
      (((j : Nat) : Fp) :: ((ridPayload p.rids).getD j []).map ZkFormal.NearV3.Public.byteF) := by
  rw [pubCountD1_split p ov hr hs hlen]
  apply Nat.lt_of_lt_of_le _ (Nat.le_add_left _ _)
  apply List.length_pos_of_mem (a := (B_PRID, true,
    ((j : Nat) : Fp) :: ((ridPayload p.rids).getD j []).map ZkFormal.NearV3.Public.byteF))
  rw [List.mem_filter, decide_eq_true_eq, newMsgs_eq p ov hr hlen hleaves]
  refine ⟨List.mem_append_right _ ?_, rfl⟩
  unfold tagged
  simp only [List.mem_map, List.mem_range]
  exact ⟨_, ⟨j, hj, rfl⟩, by simp [ZkFormal.NearV3.Public.recordValues, ridPlan]⟩

/-! ## The payload of 32-byte ids -/

theorem ridPayload_length {ids : List NearSpec.Bytes} (h32 : ∀ d ∈ ids, d.length = 32) :
    (ridPayload ids).length = 32 * ids.length := by
  induction ids with
  | nil => rfl
  | cons d ds ih =>
    simp only [ridPayload, List.flatMap_cons, List.length_append, List.length_map] at ih ⊢
    rw [ih (fun x hx => h32 x (List.mem_cons_of_mem _ hx)), h32 d (List.mem_cons_self ..)]
    simp only [List.length_cons]; omega

theorem ridPayload_getD {ids : List NearSpec.Bytes} (h32 : ∀ d ∈ ids, d.length = 32) :
    ∀ {l i : Nat}, l < ids.length → i < 32 →
      (ridPayload ids).getD (32 * l + i) [] = [(ids.getD l []).getD i 0] := by
  induction ids with
  | nil => intro l i hl; simp at hl
  | cons d ds ih =>
    intro l i hl hi
    have hd := h32 d (List.mem_cons_self ..)
    simp only [ridPayload, List.flatMap_cons, List.getD_eq_getElem?_getD]
    rcases l with _ | l
    · rw [List.getElem?_append_left (by simp [hd]; omega)]
      simp only [List.getElem?_map, Nat.mul_zero, Nat.zero_add, List.getElem?_cons_zero, Option.getD_some]
      rw [List.getElem?_eq_getElem (by omega)]; rfl
    · rw [List.getElem?_append_right (by simp [hd]; omega)]
      have := ih (fun x hx => h32 x (List.mem_cons_of_mem _ hx)) (l := l) (i := i)
        (by simpa using hl) hi
      simp only [List.getD_eq_getElem?_getD] at this
      simp only [List.length_map, hd, List.getElem?_cons_succ]
      rw [show 32 * (l + 1) + i - 32 = 32 * l + i by omega]
      exact this

/-! ## The local receipt ids of `prepD1` -/

section
open NearSpec NearSpecV3 Sched ZkFormal.NearV3.Assembly

set_option maxHeartbeats 4000000 in
theorem prepTx_localIds {ctx : ApplyCtx} {st st' : TxAcc} {t : Tx} {f : Bool}
    (h : prepTx ctx st t f = .ok st') (hl : ∀ r ∈ st.locals, r.receiptId.length = 32) :
    ∀ r ∈ st'.locals, r.receiptId.length = 32 := by
  unfold prepTx at h
  repeat' (first
    | (obtain ⟨_, _, h⟩ := bind_ok h)
    | (split at h)
    | (dsimp only at h))
  all_goals try (cases h; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    intro r hm
    (try simp only [List.mem_append, List.mem_singleton] at hm)
    first
      | exact hl r hm
      | (rcases hm with hm | rfl
         · exact hl r hm
         · exact ArenaCore.sha256_length _)

theorem prepTxs_localIds {ctx : ApplyCtx} :
    ∀ {st st' : TxAcc} {txs : List (Tx × Bool)}, prepTxs ctx st txs = .ok st' →
      (∀ r ∈ st.locals, r.receiptId.length = 32) → ∀ r ∈ st'.locals, r.receiptId.length = 32
  | st, st', [], h, hl => by
    simp only [prepTxs, Except.ok.injEq] at h
    subst h; exact hl
  | st, st', (t, f) :: rest, h, hl => by
    simp only [prepTxs] at h
    obtain ⟨s1, h1, h2⟩ := bind_ok h
    exact prepTxs_localIds h2 (prepTx_localIds h1 hl)

/-- **The local receipt ids are 32 bytes.** -/
theorem prepD1_rids_len {cb : NearSpec.Bytes} {h : HintD1} {p : PrepD1} (hp : prepD1 cb h = .ok p) :
    ∀ d ∈ p.rids, d.length = 32 := by
  obtain ⟨w, hw, rfl⟩ := prepD1_spec hp
  intro d hd
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hd
  exact prepTxs_localIds hw.run (fun r hr => by change r ∈ ([] : List Receipt) at hr; cases hr) r hr

end

/-! ## `ridV3`'s records -/

/-- At most `NT0` local receipts. -/
theorem prepD1_rids_le {cb : NearSpec.Bytes} {h : HintD1} {p : PrepD1} (hp : prepD1 cb h = .ok p) :
    p.rids.length ≤ NearSpecV3.NT0 := by
  obtain ⟨w, hw, rfl⟩ := prepD1_spec hp
  have g := prepTxs_growth hw.run
  have hz : (w.txs.zip (w.txValid.map (· != 0))).length ≤ w.txs.length := by
    rw [List.length_zip]; exact Nat.min_le_left _ _
  have := hw.nt0
  change (w.st.locals.map _).length ≤ _
  simp only [List.length_map]
  simp only [List.length_nil, Nat.zero_add] at g
  omega

section
variable {cb : NearSpec.Bytes} {h : HintD1} {p : PrepD1} {ov : Nat} {tr : Trace Fp} {es : List RidE}
  (hp : prepD1 cb h = .ok p) (hlen : (preparedBytesD1 p ov).length < P)
  (hH : HoldsP nearAirV3D1 (ZkFormal.Udr.pubOf Fp (preparedBytesD1 p ov)) tr)
  (hW : RidWf es) (hT : TableTraffic RidV3.interactions tr T_RID (ZkFormal.Udr.pubOf Fp (preparedBytesD1 p ov))
    (ridTraffic es))
  (hl : RidLRange es) (h32 : ∀ d ∈ p.rids, d.length = 32)

/-- `j ≡ 32·l + i` over the naturals (`l < 2^20`). -/
theorem rid_idx (hW : RidWf es) (hl : RidLRange es) {e : RidE} (he : e ∈ es) :
    e.i < 32 ∧ e.j = 32 * e.l + e.i := by
  obtain ⟨hi, hf⟩ := hW.idx e he
  refine ⟨hi, ?_⟩
  have h1 := congrArg Fp.toNat hf
  have hl' := hl e he
  have hc := (hW.canon e he).1
  rw [Fp.toNat_ofNat, Fp.toNat_ofNat, Nat.mod_eq_of_lt hc,
    Nat.mod_eq_of_lt (by unfold P; omega)] at h1
  exact h1

include hp hlen hH hW hT hl h32 in
/-- **Every `ridV3` record carries the public byte** `rids[l][i]`, `l < |rids|`. -/
theorem rid_entry {e : RidE} (he : e ∈ es) :
    e.l < p.rids.length ∧ e.i < 32 ∧ e.b = ((p.rids.getD e.l []).getD e.i 0).toNat := by
  have hP : P < 256 ^ 4 := by unfold P; omega
  obtain ⟨hi, hj⟩ := rid_idx hW hl he
  have hr : [e.j, e.b] ∈ (ridTraffic es).recvs B_PRID := by
    simp only [ridTraffic, ridRecvs, ite_true]
    exact List.mem_map.mpr ⟨e, he, rfl⟩
  have hpos := count_pos_of_mem hT hr
  rcases sender_of_recv hH getElem?_d1_rid hpos with hpub | ⟨t', T', ht', hpos'⟩
  · obtain ⟨-, j, hjl, hm⟩ := pub_prid_mem p ov (prepD1_roots hp) (prepD1_source_roots hp)
      (prepD1_leaves hp) (by omega) hpub
    rw [ridPayload_length h32] at hjl
    have hjP : j < P := by
      have := prepD1_rids_le hp
      unfold NearSpecV3.NT0 at this; unfold P; omega
    have hc := hW.canon e he
    -- `e.j = j` and the byte
    have hl0 : (ridPayload p.rids).getD j [] = [(p.rids.getD (j / 32) []).getD (j % 32) 0] := by
      have := ridPayload_getD h32 (l := j / 32) (i := j % 32) (by omega) (Nat.mod_lt _ (by decide))
      rwa [Nat.div_add_mod] at this
    rw [hl0] at hm
    simp only [Msg.toFp, List.map_cons, List.map_nil, List.cons.injEq] at hm
    obtain ⟨h1, h2, -⟩ := hm
    have ej : e.j = j := by
      have := congrArg Fp.toNat h1
      rw [Fp.toNat_ofNat, natCast_eq, Fp.toNat_ofNat, Nat.mod_eq_of_lt hc.1, Nat.mod_eq_of_lt hjP] at this
      exact this
    subst ej
    have hdiv : e.j / 32 = e.l := by omega
    have hmod : e.j % 32 = e.i := by omega
    rw [hdiv, hmod] at h2
    refine ⟨by omega, hi, ?_⟩
    have := congrArg Fp.toNat h2
    unfold ZkFormal.NearV3.Public.byteF at this
    rw [Fp.toNat_ofNat, Fp.toNat_ofNat, Nat.mod_eq_of_lt hc.2.2,
      Nat.mod_eq_of_lt (by have := ((p.rids.getD e.l []).getD e.i 0).toNat_lt; unfold P; omega)] at this
    exact this
  · by_cases h29 : t' = T_RID
    · subst h29
      rw [getElem?_d1_rid] at ht'
      cases ht'
      obtain ⟨v, hv, -⟩ := mem_of_count_pos hT hpos'
      simp [ridTraffic, ridSends, show B_PRID ≠ B_RIDS by decide] at hv
    · rw [tableBusCount_nobus' (only_of d1_prid_tables ht' (by simpa using h29)) true] at hpos'
      omega

include hp hlen hH hW hT hl h32 in
/-- **Every local id has a `ridV3` record** at `(l, 0)`. -/
theorem rid_local {l : Nat} (hl0 : l < p.rids.length) : ∃ e ∈ es, e.l = l ∧ e.i = 0 := by
  have hP : P < 256 ^ 4 := by unfold P; omega
  have hjl : 32 * l < (ridPayload p.rids).length := by rw [ridPayload_length h32]; omega
  have hpos := pub_prid_pos p ov (prepD1_roots hp) (prepD1_source_roots hp) (prepD1_leaves hp)
    (by omega) hjl
  generalize hmdef : (((32 * l : Nat) : Fp) :: ((ridPayload p.rids).getD (32 * l) []).map
    ZkFormal.NearV3.Public.byteF) = m at hpos
  -- no public receive of `m`
  have hpf : pubCount nearAirV3D1 (ZkFormal.Udr.pubOf Fp (preparedBytesD1 p ov)) B_PRID false m = 0 := by
    rcases Nat.eq_zero_or_pos (pubCount nearAirV3D1 (ZkFormal.Udr.pubOf Fp (preparedBytesD1 p ov))
      B_PRID false m) with h0 | h0
    · exact h0
    · exact absurd (pub_prid_mem p ov (prepD1_roots hp) (prepD1_source_roots hp) (prepD1_leaves hp)
        (by omega) h0).1 (by decide)
  have hb := hH.balance B_PRID m
  change busCount.go tr _ B_PRID true m nearAirV3D1.tables 0 + _ =
    busCount.go tr _ B_PRID false m nearAirV3D1.tables 0 + _ at hb
  obtain ⟨t, ht, htp⟩ := go_pos (tr := tr) (pub := ZkFormal.Udr.pubOf Fp (preparedBytesD1 p ov))
    (b := B_PRID) (m := m) false nearAirV3D1.tables 0 (by omega)
  rw [Nat.zero_add] at htp
  by_cases h29 : t = T_RID
  · subst h29
    have hT' : nearAirV3D1.tables[T_RID] = RidV3.table := by
      have := getElem?_d1_rid
      rw [List.getElem?_eq_getElem ht] at this
      exact Option.some.inj this
    rw [hT'] at htp
    obtain ⟨v, hv, hvm⟩ := mem_of_count_pos hT htp
    simp only [ridTraffic, ridRecvs, ite_true] at hv
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hv
    obtain ⟨hi, hj⟩ := rid_idx hW hl he
    have hc := hW.canon e he
    rw [← hmdef] at hvm
    simp only [Msg.toFp, List.map_cons, List.cons.injEq] at hvm
    have := congrArg Fp.toNat hvm.1
    rw [Fp.toNat_ofNat, natCast_eq, Fp.toNat_ofNat, Nat.mod_eq_of_lt hc.1,
      Nat.mod_eq_of_lt (by
        have := prepD1_rids_le hp
        unfold NearSpecV3.NT0 at this; unfold P; omega)] at this
    exact ⟨e, he, by omega, by omega⟩
  · rw [tableBusCount_nobus' (only_of d1_prid_tables (getElem?_of_lt ht) (by simpa using h29)) false] at htp
    omega

end

/-! ## The `RIDS` balance with `ridV3` -/

/-- **`RIDS`** (D1): the sort table is silent and neither the receipt view nor `ridV3` sends ids,
or their id sends are, as `Fp` messages, a permutation of a sort view's receives. -/
theorem ridsBalD1 {pub : List Fp} {tr : Trace Fp} {r : ZkFormal.NearV3.Assembly.V3Records} {es : List RidE}
    (hH : HoldsP nearAirV3D1 pub tr) (T : BaseTrafficD1 pub tr r)
    (hT : TableTraffic RidV3.interactions tr T_RID pub (ridTraffic es)) :
    (rcptSends3 pub r.lists B_RIDS = [] ∧ ridSends es B_RIDS = []) ∨
      ∃ ids, SortWf ids ∧ ((rcptSends3 pub r.lists B_RIDS ++ ridSends es B_RIDS).map Msg.toFp).Perm
        (((sortTraffic ids).recvs B_RIDS).map Msg.toFp) := by
  have hb := fun m => ZkFormal.NearV3.Assembly.bal_users_d1 hH (b := B_RIDS)
    (U := [ZkFormal.NearV3.Assembly.T_RCPT, ZkFormal.NearV3.Assembly.T_SORT, T_RID]) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) m
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at hb
  have hr : ∀ s m, tableBusCount (isAtD1 ZkFormal.NearV3.Assembly.T_RCPT) tr ZkFormal.NearV3.Assembly.T_RCPT
      pub B_RIDS s m = ZkFormal.NearV3.Assembly.tcnt (RcptD1.rcptTraffic3D1 pub r.lists) s B_RIDS m :=
    fun s m => by
      rw [show isAtD1 ZkFormal.NearV3.Assembly.T_RCPT = RcptD1.tableQD1.interactions from rfl,
        show ZkFormal.NearV3.Assembly.T_RCPT = 16 from rfl, ZkFormal.NearV3.Assembly.tcnt_of_traffic T.lists]
  have hd : ∀ s m, tableBusCount (isAtD1 T_RID) tr T_RID pub B_RIDS s m =
      ZkFormal.NearV3.Assembly.tcnt (ridTraffic es) s B_RIDS m := fun s m => by
    rw [show isAtD1 T_RID = RidV3.interactions from rfl, ZkFormal.NearV3.Assembly.tcnt_of_traffic hT]
  have hr0 : ∀ m, ZkFormal.NearV3.Assembly.tcnt (RcptD1.rcptTraffic3D1 pub r.lists) false B_RIDS m = 0 := by
    intro m
    simp only [ZkFormal.NearV3.Assembly.tcnt, RcptD1.rcptTraffic3D1, RcptD1.rcptTraffic3G,
      Bool.false_eq_true, ite_false]
    rw [RcptV3Proof.rids_view_receive_empty]; rfl
  have hd0 : ∀ m, ZkFormal.NearV3.Assembly.tcnt (ridTraffic es) false B_RIDS m = 0 := by
    intro m
    simp [ZkFormal.NearV3.Assembly.tcnt, ridTraffic, ridRecvs, show B_RIDS ≠ B_PRID by decide]
  have hs : ∀ m, ZkFormal.NearV3.Assembly.tcnt (RcptD1.rcptTraffic3D1 pub r.lists) true B_RIDS m +
      ZkFormal.NearV3.Assembly.tcnt (ridTraffic es) true B_RIDS m =
      ((rcptSends3 pub r.lists B_RIDS ++ ridSends es B_RIDS).map Msg.toFp).count m := by
    intro m
    simp only [ZkFormal.NearV3.Assembly.tcnt, ite_true, RcptD1.rcptTraffic3D1, RcptD1.rcptTraffic3G,
      ridTraffic, rcptSends3G_rids, List.map_append, List.count_append]
  have hL := ZkFormal.NearV3.Assembly.tableLocal_of_holdsP hH getElem?_sort_d1
  rcases Candidates.SortEmpty.sortV3_empty_or_old tr ZkFormal.NearV3.Assembly.T_SORT pub hL with hz | hold
  · left
    have hnil : (rcptSends3 pub r.lists B_RIDS ++ ridSends es B_RIDS) = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro m hm
      have h := hb (Msg.toFp m)
      rw [hr, hr, hr0, hd, hd, hd0,
        show isAtD1 ZkFormal.NearV3.Assembly.T_SORT = ZkFormal.NearV3.Assembly.sortTableV3.interactions from rfl, hz, hz] at h
      have h2 := hs (Msg.toFp m)
      have : 0 < ((rcptSends3 pub r.lists B_RIDS ++ ridSends es B_RIDS).map Msg.toFp).count (Msg.toFp m) :=
        List.count_pos_iff.mpr (List.mem_map_of_mem hm)
      omega
    exact List.append_eq_nil_iff.mp hnil
  · right
    obtain ⟨ids, hW, hT'⟩ := sortV3_view tr pub ZkFormal.NearV3.Assembly.T_SORT hold
    refine ⟨ids, hW, List.perm_iff_count.mpr fun m => ?_⟩
    have h := hb m
    rw [hr, hr, hr0, hd, hd, hd0, show isAtD1 ZkFormal.NearV3.Assembly.T_SORT = Sort.interactions from rfl,
      ZkFormal.NearV3.Assembly.tcnt_of_traffic hT', ZkFormal.NearV3.Assembly.tcnt_of_traffic hT'] at h
    have h2 := hs m
    simp only [ZkFormal.NearV3.Assembly.tcnt, ite_true, Bool.false_eq_true, ite_false, sortTraffic,
      List.map_nil, List.count_nil, Nat.add_zero, Nat.zero_add] at h h2
    rw [← h2]
    simpa [sortTraffic] using h

/-! ## Distinct receipt ids: local, then incoming -/

open ZkFormal.Near.Link in
/-- **`MainExecutionD1.distinctIds`** on the views: the local receipt ids (`p.rids`, the public
`PRID` segment) followed by the receipt view's ids are pairwise distinct, given byte-valued
incoming ids, `|flatR| ≤ W_LOC` and the `ridV3` range interface.  The sort view's ids are
exactly these ids, one entry each (index `r` for an incoming receipt, `W_LOC + l` for a local
one), strictly increasing. -/
theorem receiptIdsD1 {cb : NearSpec.Bytes} {h : HintD1} {p : PrepD1} {ov : Nat} {tr : Trace Fp}
    {r : ZkFormal.NearV3.Assembly.V3Records} {es : List RidE}
    (hp : prepD1 cb h = .ok p) (hlen : (preparedBytesD1 p ov).length < P)
    (hH : HoldsP nearAirV3D1 (ZkFormal.Udr.pubOf Fp (preparedBytesD1 p ov)) tr)
    (T : BaseTrafficD1 (ZkFormal.Udr.pubOf Fp (preparedBytesD1 p ov)) tr r)
    (W : BaseWfD1 (ZkFormal.Udr.pubOf Fp (preparedBytesD1 p ov)) r)
    (hW : RidWf es) (hT : TableTraffic RidV3.interactions tr T_RID (ZkFormal.Udr.pubOf Fp (preparedBytesD1 p ov))
      (ridTraffic es)) (hl : RidLRange es)
    (hrid : ∀ x ∈ flatR r.lists, Bytes8 x.rid) (hrs : (flatR r.lists).length ≤ W_LOC) :
    (p.rids ++ (flatR r.lists).map fun x => x.toRcptV.toReceipt.receiptId).Nodup := by
  have h32 := prepD1_rids_len hp
  have hRl := prepD1_rids_le hp
  have hentL := fun {e : RidE} (he : e ∈ es) => rid_entry hp hlen hH hW hT hl h32 he
  have hloc := fun {l : Nat} (hl0 : l < p.rids.length) => rid_local hp hlen hH hW hT hl h32 hl0
  have hb := ridsBalD1 hH T hT
  generalize ZkFormal.Udr.pubOf Fp (preparedBytesD1 p ov) = pub at hb W
  obtain ⟨toks, -, -, hwf, -⟩ := W.lists.toks
  have hlenr : ∀ q (hq : q < (flatR r.lists).length), (flatR r.lists)[q].rid.length = 32 :=
    fun q hq => (hwf q hq).lens.1
  have hcan : ∀ x ∈ flatR r.lists, ∀ y ∈ x.rid, y < P := by
    intro x hx y hy
    exact W.lists.canon.2 x hx y (by simp [RcptE.raw3, RcptV.raw, hy])
  clear hwf
  generalize hrs' : flatR r.lists = rs at hlenr hcan hrid hrs
  have hWL : W_LOC = 1048576 := rfl
  unfold NearSpecV3.NT0 at hRl
  have hP : 2 ^ 22 < P := by unfold P; omega
  rcases hb with ⟨h0, h1⟩ | ⟨ids, hSW, hpm⟩
  · -- silent: no receipts and no local ids
    rw [ZkFormal.NearV3.Assembly.LinkRids.rcptSends3_rids, hrs'] at h0
    have hrs0 : rs = [] := by
      cases rs with
      | nil => rfl
      | cons x xs =>
        exfalso
        have hm : [0, 0, x.rid.getD 0 0] ∈ ((x :: xs).zip (List.range (x :: xs).length)).flatMap
            fun p => (List.range 32).map fun i => [p.2, i, p.1.rid.getD i 0] :=
          List.mem_flatMap.mpr ⟨(x, 0), mem_zip_range.mpr ⟨by simp, rfl⟩,
            List.mem_map.mpr ⟨0, by simp, rfl⟩⟩
        rw [h0] at hm; simp at hm
    have hrd0 : p.rids = [] := by
      cases hq : p.rids with
      | nil => rfl
      | cons d ds =>
        exfalso
        obtain ⟨e, he, -, -⟩ := hloc (l := 0) (by rw [hq]; simp)
        have : [W_LOC + e.l, e.i, e.b] ∈ ridSends es B_RIDS := by
          simp only [ridSends, ite_true]; exact List.mem_map.mpr ⟨e, he, rfl⟩
        rw [h1] at this; simp at this
    rw [hrs0, hrd0]; exact List.nodup_nil
  rw [ZkFormal.NearV3.Assembly.LinkRids.rcptSends3_rids, hrs'] at hpm
  have hsr : (sortTraffic ids).recvs B_RIDS =
      ids.flatMap fun p => (List.range 32).map fun i => [p.1, i, p.2.getD i 0] := by
    simp [sortTraffic]
  rw [hsr] at hpm
  have hpn := perm_nat ?_ ?_ hpm
  rotate_left
  · intro m hm
    rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨⟨x, q⟩, hpr, hm⟩ := List.mem_flatMap.mp hm
      obtain ⟨hq, rfl⟩ := mem_zip_range.mp hpr
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hm
      intro y hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl
      · omega
      · simp at hi; unfold P; omega
      · exact getD_lt (hcan _ (List.getElem_mem hq)) i
    · simp only [ridSends, ite_true] at hm
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
      have := hl e he
      have hc := hW.canon e he
      have hi := (hW.idx e he).1
      intro y hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl
      · unfold P; omega
      · unfold P; omega
      · exact hc.2.2
  · intro m hm
    obtain ⟨p, hpi, hm⟩ := List.mem_flatMap.mp hm
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hm
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl
    · exact (hSW.len p hpi).2
    · simp at hi; unfold P; omega
    · exact getD_lt (hSW.canon p hpi) i
  -- every sort entry is a receipt's id or a local id
  have hrev : ∀ q (hq : q < ids.length) j, j < 32 →
      (∃ hr : ids[q].1 < rs.length, ids[q].2.getD j 0 = rs[ids[q].1].rid.getD j 0) ∨
      (∃ l < p.rids.length, ids[q].1 = W_LOC + l ∧
        ids[q].2.getD j 0 = ((p.rids.getD l []).getD j 0).toNat) := by
    intro q hq j hj
    have hm2 : [ids[q].1, j, ids[q].2.getD j 0] ∈ ids.flatMap
        fun p => (List.range 32).map fun i => [p.1, i, p.2.getD i 0] :=
      List.mem_flatMap.mpr ⟨_, List.getElem_mem hq, List.mem_map.mpr ⟨j, by simp; omega, rfl⟩⟩
    rcases List.mem_append.mp (hpn.mem_iff.mpr hm2) with hm3 | hm3
    · left
      obtain ⟨⟨x, r'⟩, hpr, hm3⟩ := List.mem_flatMap.mp hm3
      obtain ⟨hr', rfl⟩ := mem_zip_range.mp hpr
      obtain ⟨j', -, he'⟩ := List.mem_map.mp hm3
      simp only [List.cons.injEq] at he'
      obtain ⟨e1, rfl, e3⟩ := he'
      subst e1
      exact ⟨hr', e3.1.symm⟩
    · right
      simp only [ridSends, ite_true] at hm3
      obtain ⟨e, he, he'⟩ := List.mem_map.mp hm3
      simp only [List.cons.injEq] at he'
      obtain ⟨e1, e2, e3, -⟩ := he'
      obtain ⟨hlt, hi, hb⟩ := hentL he
      refine ⟨e.l, hlt, e1.symm, ?_⟩
      rw [← e3, hb, ← e2]
  -- each incoming receipt has a sort entry carrying its id
  have hentry : ∀ q (hq : q < rs.length), ∃ p, ∃ hp : p < ids.length, ids[p].1 = q ∧
      ids[p].2 = rs[q].rid := by
    intro q hq
    have hm : [q, 0, rs[q].rid.getD 0 0] ∈ (rs.zip (List.range rs.length)).flatMap
        fun p => (List.range 32).map fun i => [p.2, i, p.1.rid.getD i 0] :=
      List.mem_flatMap.mpr ⟨(rs[q], q), mem_zip_range.mpr ⟨hq, rfl⟩,
        List.mem_map.mpr ⟨0, by simp, rfl⟩⟩
    obtain ⟨q', hq', hm'⟩ := List.mem_flatMap.mp (hpn.mem_iff.mp (List.mem_append_left _ hm))
    obtain ⟨i, -, he⟩ := List.mem_map.mp hm'
    simp only [List.cons.injEq] at he
    obtain ⟨p, hpl, rfl⟩ := List.mem_iff_getElem.mp hq'
    refine ⟨p, hpl, he.1, ?_⟩
    have hl1 : ids[p].2.length = 32 := (hSW.len _ hq').1
    apply List.ext_getElem (by rw [hl1, hlenr q hq])
    intro j hj1 hj2
    rcases hrev p hpl j (by omega) with ⟨_, e⟩ | ⟨l, -, e1, -⟩
    · rw [← getD_eq_getElem _ 0 hj1, ← getD_eq_getElem _ 0 hj2, e]
      simp only [he.1]
    · rw [he.1] at e1; omega
  -- each local id has a sort entry carrying it
  have hentryL : ∀ l (hl0 : l < p.rids.length), ∃ p', ∃ hp : p' < ids.length,
      ids[p'].1 = W_LOC + l ∧ ids[p'].2.map UInt8.ofNat = p.rids[l] := by
    intro l hl0
    obtain ⟨e, he, rfl, he0⟩ := hloc hl0
    have hm : [W_LOC + e.l, e.i, e.b] ∈ ridSends es B_RIDS := by
      simp only [ridSends, ite_true]; exact List.mem_map.mpr ⟨e, he, rfl⟩
    obtain ⟨q', hq', hm'⟩ := List.mem_flatMap.mp (hpn.mem_iff.mp (List.mem_append_right _ hm))
    obtain ⟨i, -, he'⟩ := List.mem_map.mp hm'
    simp only [List.cons.injEq] at he'
    obtain ⟨p', hpl, rfl⟩ := List.mem_iff_getElem.mp hq'
    refine ⟨p', hpl, he'.1, ?_⟩
    have hl1 : ids[p'].2.length = 32 := (hSW.len _ hq').1
    have hl2 : p.rids[e.l].length = 32 := h32 _ (List.getElem_mem hl0)
    apply List.ext_getElem (by rw [List.length_map, hl1, hl2])
    intro j hj1 hj2
    rw [List.length_map] at hj1
    rcases hrev p' hpl j (by omega) with ⟨hr, -⟩ | ⟨l', -, e1, e2⟩
    · rw [he'.1] at hr; omega
    · rw [he'.1] at e1
      have : l' = e.l := by omega
      subst this
      rw [List.getElem_map, ← getD_eq_getElem _ 0 hj1, e2]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl0, Option.getD_some,
        List.getElem?_eq_getElem hj2, UInt8.ofNat_toNat]
  have hall : ∀ x ∈ ids, ∀ y ∈ x.2, y < 256 := by
    intro x hx y hy
    obtain ⟨p, hpl, rfl⟩ := List.mem_iff_getElem.mp hx
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hy
    have hl1 : ids[p].2.length = 32 := (hSW.len _ hx).1
    rcases hrev p hpl j (by omega) with ⟨hr, e⟩ | ⟨l, -, -, e⟩
    · rw [← getD_eq_getElem _ 0 hj, e]
      exact getD_lt_of_bytes8 (hrid _ (List.getElem_mem hr)) _
    · rw [← getD_eq_getElem _ 0 hj, e]
      exact UInt8.toNat_lt _
  have hstrict := strict_of_succ
    (fun t => NearSpec.leNat ((ids.getD t (0, [])).2.map UInt8.ofNat)) ids.length
    (fun t ht => hSW.incr t ht hall)
  -- every element of the combined list is a sort entry's id, at a distinct index
  let idx : Nat → Nat := fun k => if k < p.rids.length then W_LOC + k else k - p.rids.length
  have hcomb : ∀ k (hk : k < (p.rids ++ rs.map fun x => x.toRcptV.toReceipt.receiptId).length),
      ∃ p', ∃ hp : p' < ids.length, ids[p'].1 = idx k ∧
        ids[p'].2.map UInt8.ofNat = (p.rids ++ rs.map fun x => x.toRcptV.toReceipt.receiptId)[k] := by
    intro k hk
    by_cases hkl : k < p.rids.length
    · obtain ⟨p', hp', e1, e2⟩ := hentryL k hkl
      refine ⟨p', hp', by simp only [idx, hkl, ite_true]; exact e1, ?_⟩
      rw [List.getElem_append_left hkl, e2]
    · have hq : k - p.rids.length < rs.length := by
        simp only [List.length_append, List.length_map] at hk; omega
      obtain ⟨p', hp', e1, e2⟩ := hentry (k - p.rids.length) hq
      refine ⟨p', hp', by simp only [idx, hkl, ite_false]; exact e1, ?_⟩
      rw [List.getElem_append_right (by omega)]
      simp only [List.getElem_map, RcptV.toReceipt, e2]
      rfl
  apply nodup_of_getElem
  intro i j hi hj hij he
  obtain ⟨p1, hp1, e11, e12⟩ := hcomb i hi
  obtain ⟨p2, hp2, e21, e22⟩ := hcomb j hj
  have hidx : idx i ≠ idx j := by
    simp only [List.length_append, List.length_map] at hi hj
    simp only [idx]
    split <;> split <;> omega
  have hpne : p1 ≠ p2 := fun e => hidx (by subst e; rw [← e11, ← e21])
  have hf : ∀ q (hq : q < ids.length),
      NearSpec.leNat ((ids.getD q (0, [])).2.map UInt8.ofNat) = NearSpec.leNat (ids[q].2.map UInt8.ofNat) := by
    intro q hq
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq, Option.getD_some]
  have f1 := hf p1 hp1
  have f2 := hf p2 hp2
  rw [e12, he, ← e22] at f1
  rcases Nat.lt_or_gt_of_ne hpne with hl' | hl'
  · have := hstrict p1 p2 hl' hp2; omega
  · have := hstrict p2 p1 hl' hp1; omega

end ZkFormal.NearV3.D1.Link
