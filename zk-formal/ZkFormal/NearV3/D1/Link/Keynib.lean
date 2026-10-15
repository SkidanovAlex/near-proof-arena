import ZkFormal.NearV3.D1.Link.RidBytes
import ZkFormal.NearV3.D1.Extract.KibProof
import ZkFormal.NearV3.D1.Extract.KibD1Proof
import ZkFormal.NearV3.D1.Prep.Spec

/-!
# `ZkFormal.NearV3.D1.Link.Keynib` — `kibV3` on the `KEYNIB` bus (L1)

Lane `v3-d1-phase2`, item L1 (next step 4 of checkpoint 10, `KEYNIB`).  In `nearAirV3D1` the
`KEYNIB` bus has a third sender, `kibD1` (27), relaying the public `PKEY` records of the
transaction / credit walks `p.walks` (and, on `UKEYNIB`, those of the unread-key walks
`p.uwalks`, lane v3-d1-a7b: `kibD1` routes a record by bit 7 of the id's byte 2):

* `prepD1_walk_ids`: the walks of a successful `prepD1` have ids `W_TX ≤ w < W_TX + 2·T0`;
  `prepD1_uwalk_ids`: the unread-key walks have ids `W_UNR ≤ w < W_UNR + 2·NT0`;
* `pub_pkey_mem`: a public `PKEY` message is a row of `keyPayload (p.walks ++ p.uwalks)`;
* `keyPayload_row`: such a row is `(w₀, w₁, w₂, t, sym, last)` of a walk `k ∈ p.walks`
  (`wᵢ = byteAt k.w i`) with `sym` a nibble or `SYM_END`;
* **`kib_entry`**: every `kibD1` record carries a walk id `k.w` (and its byte 2) of some
  `k ∈ p.walks ++ p.uwalks` and a nibble or `SYM_END`;
* `kibKeys` (the raw `KEYNIB` sends of table 27) and **`kibKeys_entry`**: each is such a record
  with `k ∈ p.walks` (a `KEYNIB` send has byte 2 below `128`; an unread walk's is `128`).
-/

namespace ZkFormal.NearV3.D1.Link

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.NearV3 ZkFormal.NearV3.D1
open ZkFormal.NearV3.D1.Public

/-! ## The walk ids of `prepD1` -/

section
open NearSpec NearSpecV3 Sched ZkFormal.NearV3.Assembly

/-- The walk-id invariant: every walk id is `W_TX + 2·o (+1)` for an earlier op `o`. -/
def WalkIdsOk (ws : List KeyWalk) (nops : Nat) : Prop := ∀ k ∈ ws, W_TX ≤ k.w ∧ k.w < W_TX + 2 * nops

set_option maxHeartbeats 4000000 in
theorem prepTx_walkIds {ctx : ApplyCtx} {st st' : TxAcc} {t : Tx} {f : Bool}
    (h : prepTx ctx st t f = .ok st') (hl : WalkIdsOk st.walks st.ops.length) :
    WalkIdsOk st'.walks st'.ops.length := by
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
  all_goals
    intro k hk
    try dsimp only at hk ⊢
    repeat (split at hk)
  all_goals
    try simp only [List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
      List.nil_append, List.append_nil, List.length_append, List.length_cons, List.length_nil] at hk ⊢
  all_goals
    first
      | (have := hl k hk; omega)
      | (obtain hk | hk := hk
         · have := hl k hk; omega
         · first
            | (subst hk; dsimp only; omega)
            | (obtain hk | hk := hk <;> subst hk <;> dsimp only <;> omega))

theorem prepTxs_walkIds {ctx : ApplyCtx} :
    ∀ {st st' : TxAcc} {txs : List (Tx × Bool)}, prepTxs ctx st txs = .ok st' →
      WalkIdsOk st.walks st.ops.length → WalkIdsOk st'.walks st'.ops.length
  | st, st', [], h, hl => by
    simp only [prepTxs, Except.ok.injEq] at h
    subst h; exact hl
  | st, st', (t, f) :: rest, h, hl => by
    simp only [prepTxs] at h
    obtain ⟨s1, h1, h2⟩ := bind_ok h
    exact prepTxs_walkIds h2 (prepTx_walkIds h1 hl)

theorem prepLocals_walkIds {ctx : ApplyCtx} :
    ∀ {st st' : LocAcc} {rs : List Receipt}, prepLocals ctx st rs = .ok st' →
      WalkIdsOk st.walks st.ops.length → WalkIdsOk st'.walks st'.ops.length
  | st, st', [], h, hl => by
    simp only [prepLocals, Except.ok.injEq] at h
    subst h; exact hl
  | st, st', r :: rs, h, hl => by
    simp only [prepLocals] at h
    cases hla : localApply ctx r with
    | none =>
      simp only [hla] at h
      exact absurd h (fun h' => throw_ne h')
    | some v =>
      obtain ⟨leaf, rf, burnt⟩ := v
      simp only [hla] at h
      obtain ⟨_, _, h⟩ := bind_ok h
      apply prepLocals_walkIds h
      intro k hk
      simp only [List.mem_append, List.mem_singleton, List.length_append, List.length_cons,
        List.length_nil] at hk ⊢
      rcases hk with hk | rfl
      · have := hl k hk; omega
      · simp only; omega

/-- **The walk ids of `prepD1`**: `W_TX ≤ w < W_TX + 2·T0`, `T0 ≤ 2·NT0`. -/
theorem prepD1_walk_ids {cb : Bytes} {h : HintD1} {p : PrepD1} (hp : prepD1 cb h = .ok p) :
    ∀ k ∈ p.walks, W_TX ≤ k.w ∧ k.w < W_TX + 2 * (2 * NT0) := by
  have ht := (prepD1_m0_t0 hp).2
  obtain ⟨w, hw, rfl⟩ := prepD1_spec hp
  have h1 := prepTxs_walkIds hw.run (by intro k hk; change k ∈ ([] : List KeyWalk) at hk; cases hk)
  have h2 := prepLocals_walkIds hw.locals h1
  intro k hk
  have := h2 k hk
  change w.loc.ops.length ≤ _ at ht
  omega

theorem unreadWalks_ids (txs : List Tx) :
    ∀ k ∈ unreadWalks txs, W_UNR ≤ k.w ∧ k.w < W_UNR + 2 * txs.length := by
  intro k hk
  simp only [unreadWalks, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hk
  obtain ⟨⟨t, j⟩, hj, hk⟩ := hk
  obtain ⟨-, hj, -⟩ := List.mem_zipIdx hj
  rcases hk with rfl | rfl <;> simp only <;> omega

/-- **The unread-key walk ids of `prepD1`**: `W_UNR ≤ w < W_UNR + 2·NT0`. -/
theorem prepD1_uwalk_ids {cb : Bytes} {h : HintD1} {p : PrepD1} (hp : prepD1 cb h = .ok p) :
    ∀ k ∈ p.uwalks, W_UNR ≤ k.w ∧ k.w < W_UNR + 2 * NT0 := by
  obtain ⟨w, hw, rfl⟩ := prepD1_spec hp
  intro k hk
  have := unreadWalks_ids w.txs k hk
  have := hw.nt0
  omega

/-- Byte 2 of an id: `< 128` for the candidates' walks, `128` for the unread-key walks. -/
theorem prepD1_walk_byte2 {cb : Bytes} {h : HintD1} {p : PrepD1} (hp : prepD1 cb h = .ok p) :
    (∀ k ∈ p.walks, byteAt k.w 2 < 128) ∧ (∀ k ∈ p.uwalks, byteAt k.w 2 = 128) := by
  refine ⟨fun k hk => ?_, fun k hk => ?_⟩
  · have := prepD1_walk_ids hp k hk
    unfold W_TX NT0 at this
    unfold byteAt
    simp only [show (256 : Nat) ^ 2 = 65536 by rfl]
    omega
  · have := prepD1_uwalk_ids hp k hk
    unfold W_UNR NT0 at this
    unfold byteAt
    simp only [show (256 : Nat) ^ 2 = 65536 by rfl]
    omega

end

/-- `rcptV3D1`'s `KEYNIB` sends are D0a's. -/
theorem rcptSends3G_keynib (o0 t0 m0 : Nat) (pub : List Fp) (ls : RcptV3Vs) :
    RcptD1.rcptSends3G o0 t0 m0 pub ls B_KEYNIB = rcptSends3 pub ls B_KEYNIB := by
  simp only [RcptD1.rcptSends3G, rcptSends3, RcptD1.rSendsG, rSends, show B_KEYNIB ≠ B_BYTES by decide,
    show B_KEYNIB ≠ B_RCL by decide, ite_false, ite_true]

/-! ## The public `PKEY` segment -/

theorem segs_no_pkey : ∀ s ∈ ZkFormal.NearV3.Assembly.nearAirV3.pubSegs, s.bus ≠ B_PKEY := by
  have hall : ZkFormal.NearV3.Public.preparedSegments.all (fun s => decide (s.bus ≠ B_PKEY)) = true := by
    decide +kernel
  intro s hs
  exact of_decide_eq_true (List.all_eq_true.mp hall s hs)

theorem d1_pkey_tables : onlyOn B_PKEY [T_KIB] = true := by decide +kernel

set_option maxHeartbeats 2000000 in
/-- **A public `PKEY` message** of the verifier's tape is a row of `keyPayload p.walks`. -/
theorem pub_pkey_mem (p : PrepD1) (ov : Nat) (hr : ZkFormal.NearV3.Public.RootsSized p.base)
    (hs : ∀ s ∈ p.base.lists, s.root.length = 32) (hleaves : ∀ l ∈ p.leaves, l.length = 32)
    (hlen : (preparedBytesD1 p ov).length < 256 ^ 4) {sd : Bool} {m : List Fp}
    (hpos : 0 < pubCount nearAirV3D1 (ZkFormal.Udr.pubOf Fp (preparedBytesD1 p ov)) B_PKEY sd m) :
    sd = true ∧ ∃ row ∈ keyPayload (p.walks ++ p.uwalks), m = row.map ZkFormal.NearV3.Public.byteF := by
  rw [pubCountD1_split p ov hr hs hlen, pubCount_nobus segs_no_pkey sd, Nat.zero_add] at hpos
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
  · refine ⟨he.2.1, _, List.getElem_mem hj, ?_⟩
    rw [he.2.2]
    simp [ZkFormal.NearV3.Public.recordValues, keyPlan, ZkFormal.NearV3.Public.plainPlan,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  · exact absurd he.1 (by decide)
  · exact absurd he.1 (by decide)

/-- **A row of `keyPayload`**: `(w₀, w₁, w₂, t, sym, last)` of a walk, `sym` a nibble or `SYM_END`. -/
theorem keyPayload_row {ws : List KeyWalk} {row : List UInt8} (h : row ∈ keyPayload ws) :
    ∃ k ∈ ws, ∃ t s last : Nat, row = [byteAt k.w 0, byteAt k.w 1, byteAt k.w 2, t, s, last].map UInt8.ofNat ∧
      (s < 16 ∨ s = SYM_END) := by
  obtain ⟨k, hk, hr⟩ := List.mem_flatMap.mp h
  obtain ⟨rr, hrr, rfl⟩ := List.mem_map.mp hr
  refine ⟨k, hk, ?_⟩
  simp only [walkRecs, List.mem_append, List.mem_map, List.mem_singleton] at hrr
  rcases hrr with ⟨⟨s, t⟩, hst, rfl⟩ | rfl
  · refine ⟨t, s, 0, by simp, Or.inl ?_⟩
    obtain ⟨-, hi, hx⟩ := List.mem_zipIdx hst
    have hs : s ∈ (k.key.flatMap fun b : UInt8 => [b.toNat / 16, b.toNat % 16]) := by
      rw [hx]; exact List.getElem_mem _
    obtain ⟨b, -, hb⟩ := List.mem_flatMap.mp hs
    have := b.toNat_lt
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl <;> omega
  · exact ⟨(k.key.flatMap fun b : UInt8 => [b.toNat / 16, b.toNat % 16]).length, SYM_END, 1, rfl, Or.inr rfl⟩

theorem bytes3 (x : Nat) : byteAt x 0 + 256 * byteAt x 1 + 65536 * byteAt x 2 = x % 2 ^ 24 := by
  unfold byteAt
  simp only [Nat.pow_zero, Nat.pow_one, Nat.div_one, show (256 : Nat) ^ 2 = 65536 by rfl,
    show (2 : Nat) ^ 24 = 16777216 by rfl]
  omega

/-! ## `kibV3`'s records and its raw `KEYNIB` sends -/

/-- The raw `KEYNIB` sends of table 27 (`kibV3`). -/
def kibKeys (tr : Trace Fp) (pub : List Fp) : List (List Fp) :=
  (List.range (tr.height T_KIB)).flatMap fun q => rowTraffic (isAtD1 T_KIB) tr T_KIB q pub B_KEYNIB true

theorem toNat_byteF_ofNat {v : Nat} (hv : v < 256) : (ZkFormal.NearV3.Public.byteF (UInt8.ofNat v)).toNat = v := by
  unfold ZkFormal.NearV3.Public.byteF
  rw [Fp.toNat_ofNat, ZkFormal.Near.Link.toNat_ofNat_byte hv, Nat.mod_eq_of_lt (by unfold P; omega)]

/-- **Every `kibD1` record** carries the id (and its byte 2) of a walk `k ∈ p.walks ++ p.uwalks`
and a nibble or `SYM_END`. -/
theorem kib_entry {cb : NearSpec.Bytes} {h : HintD1} {p : PrepD1} {ov : Nat} {tr : Trace Fp} {es : List KibE}
    (hp : prepD1 cb h = .ok p) (hlen : (preparedBytesD1 p ov).length < P)
    (hH : HoldsP nearAirV3D1 (ZkFormal.Udr.pubOf Fp (preparedBytesD1 p ov)) tr) (hW : KibD1Wf es)
    (hT : TableTraffic KibD1.interactions tr T_KIB (ZkFormal.Udr.pubOf Fp (preparedBytesD1 p ov)) (kibD1Traffic es))
    {e : KibE} (he : e ∈ es) :
    ∃ k ∈ p.walks ++ p.uwalks, e.wid = k.w ∧ e.w2 = byteAt k.w 2 ∧ (e.sym < 16 ∨ e.sym = SYM_END) := by
  have hP : P < 256 ^ 4 := by unfold P; omega
  have hr : [e.w0, e.w1, e.w2, e.t, e.sym, e.last] ∈ (kibD1Traffic es).recvs B_PKEY := by
    simp only [kibD1Traffic, kibRecvs, ite_true]
    exact List.mem_map.mpr ⟨e, he, rfl⟩
  have hpos := count_pos_of_mem hT hr
  rcases sender_of_recv hH getElem?_d1_kib hpos with hpub | ⟨t', T', ht', hpos'⟩
  · obtain ⟨-, row, hrow, hm⟩ := pub_pkey_mem p ov (prepD1_roots hp) (prepD1_source_roots hp)
      (prepD1_leaves hp) (by omega) hpub
    obtain ⟨k, hk, t, s, last, rfl, hs⟩ := keyPayload_row hrow
    have hc := hW.canon e he
    simp only [Msg.toFp, List.map_cons, List.map_nil, List.cons.injEq] at hm
    obtain ⟨h0, h1, h2, -, h4, -⟩ := hm
    have cv : ∀ {a v : Nat}, a < P → v < 256 → Fp.ofNat a = ZkFormal.NearV3.Public.byteF (UInt8.ofNat v) →
        a = v := by
      intro a v ha hv he
      have := congrArg Fp.toNat he
      rw [toNat_byteF_ofNat hv, Fp.toNat_ofNat, Nat.mod_eq_of_lt ha] at this
      exact this
    have hb : ∀ i, byteAt k.w i < 256 := fun i => Nat.mod_lt _ (by decide)
    have e0 := cv hc.1 (hb 0) h0
    have e1 := cv hc.2.1 (hb 1) h1
    have e2 := cv hc.2.2.1 (hb 2) h2
    have hs' : s < 256 := by
      rcases hs with hs | hs
      · omega
      · rw [hs]; decide
    have e4 := cv hc.2.2.2.2.1 hs' h4
    have hkw : k.w < 2 ^ 24 := by
      rcases List.mem_append.mp hk with hk | hk
      · have := prepD1_walk_ids hp k hk
        unfold W_TX NearSpecV3.NT0 at this; omega
      · have := prepD1_uwalk_ids hp k hk
        unfold W_UNR NearSpecV3.NT0 at this; omega
    refine ⟨k, hk, ?_, e2, e4 ▸ hs⟩
    unfold KibE.wid
    rw [e0, e1, e2, bytes3, Nat.mod_eq_of_lt hkw]
  · by_cases h27 : t' = T_KIB
    · subst h27
      rw [getElem?_d1_kib] at ht'
      cases ht'
      obtain ⟨v, hv, -⟩ := mem_of_count_pos hT hpos'
      simp [kibD1Traffic, kibD1Sends, show B_PKEY ≠ B_KEYNIB by decide, show B_PKEY ≠ B_UKEYNIB by decide] at hv
    · rw [tableBusCount_nobus' (only_of d1_pkey_tables ht' (by simpa using h27)) true] at hpos'
      omega

/-- **The raw `KEYNIB` sends of `kibD1`** are `(k.w, t, sym, last)` of walks `k ∈ p.walks`, `sym` a
nibble or `SYM_END` (the unread-key walks' records go to `UKEYNIB`). -/
theorem kibKeys_entry {cb : NearSpec.Bytes} {h : HintD1} {p : PrepD1} {ov : Nat} {tr : Trace Fp}
    (hp : prepD1 cb h = .ok p) (hlen : (preparedBytesD1 p ov).length < P)
    (hH : HoldsP nearAirV3D1 (ZkFormal.Udr.pubOf Fp (preparedBytesD1 p ov)) tr) :
    ∀ y ∈ kibKeys tr (ZkFormal.Udr.pubOf Fp (preparedBytesD1 p ov)), ∃ k ∈ p.walks, ∃ t sym last : Nat,
      y = Msg.toFp [k.w, t, sym, last] ∧ (sym < 16 ∨ sym = SYM_END) := by
  obtain ⟨es, hW, hT⟩ := kibD1_view tr _ T_KIB (kibLocal hH)
  intro y hy
  have hc : 0 < tableBusCount KibD1.interactions tr T_KIB (ZkFormal.Udr.pubOf Fp (preparedBytesD1 p ov))
      B_KEYNIB true y := by
    rw [tableBusCount_eq]
    exact List.count_pos_iff.mpr hy
  obtain ⟨v, hv, rfl⟩ := mem_of_count_pos hT hc
  simp only [ite_true, kibD1Traffic, kibD1Sends] at hv
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hv
  obtain ⟨he, hlt⟩ := List.mem_filter.mp he
  obtain ⟨k, hk, hw, h2, hs⟩ := kib_entry hp hlen hH hW hT he
  refine ⟨k, ?_, e.t, e.sym, e.last, by rw [kibMsg, hw], hs⟩
  rcases List.mem_append.mp hk with hk | hk
  · exact hk
  · have h128 := (prepD1_walk_byte2 hp).2 k hk
    have := of_decide_eq_true hlt
    omega

end ZkFormal.NearV3.D1.Link
