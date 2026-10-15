import ZkFormal.NearV3.Assembly.LinkVPost
import ZkFormal.NearV3.D1.Link.Kinds
import ZkFormal.NearV3.D1.Extract.AkmProof

/-!
# `ZkFormal.NearV3.D1.Link.VPost` — the post-state value streams of `nearAirV3D1` (L1)

Lane `v3-d1-phase2`, item L1 (`LinkVPost`).  In D0a every written value slot is an account
slot, written by the acct record with `a.k = i`, and the post value stream of slot `i` is
`pnOf r.accts i = post ‖ pre[16..]`.  In D1 the transactions also write access keys: a
FullAccess `akmV3` record `e` writes slot `e.vid` (`VSLOT (vid)`) with post value
`pb ‖ [bytes[8]]` (`BYTES (VPOST(vid), j, ·)`, `j ≤ 8`).  So:

* `AkmOf pub tr ms`: `ms` are the `akmV3` view's records of the trace;
* `akmPost e`, **`pnOfD1 as ms i`**: the acct stream if an acct record has `k = i`, else the
  FullAccess akm stream of `vid = i`, else `[]`;
* `vslot_bal_rec`: `VSLOT` in record form (acct + akm sends = node receives);
* `node_vslot_le_one`: a slot message is received at most once (two written node slots with
  the same value id are the same, `val_unique`);
* **`writers_le_one`**: at most one writer per slot (acct records with `k = i` plus
  FullAccess akm records with `vid = i`);
* `akm_written`: a FullAccess akm record's `vid` is a written node slot; `akm_vid_lt`;
* `pnOfD1_acct`, `pnOfD1_akm`: the stream of a writer's slot is the writer's;
* **`akmBytes_mem`**: a raw `BYTES` message of `akmV3` is `(VPOST(vid), j, akmPost[j])`,
  `j < 9`, of a FullAccess record.
-/

namespace ZkFormal.NearV3.D1.Link

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.NearV3 ZkFormal.NearV3.D1
open ZkFormal.NearV3.Assembly

/-- `ms` are the `akmV3` view's records of the trace. -/
structure AkmOf (pub : List Fp) (tr : Trace Fp) (ms : List AkmE) : Prop where
  wf : AkmWf ms
  traffic : TableTraffic AkmV3.interactions tr T_AKM pub (akmTraffic ms)

theorem akmOf_exists {pub : List Fp} {tr : Trace Fp} (hH : HoldsP nearAirV3D1 pub tr) :
    ∃ ms, AkmOf pub tr ms := by
  obtain ⟨ms, hw, ht⟩ := akm_view tr pub T_AKM (akmLocal hH)
  exact ⟨ms, hw, ht⟩

/-- The post value stream of a FullAccess akm record: the post nonce, then the permission tag. -/
def akmPost (e : AkmE) : List Nat := e.pb ++ [e.bytes.getD 8 0]

/-- **The post value stream of slot `i`** (D1): the acct record's, else the FullAccess akm
record's, else empty. -/
def pnOfD1 (as : List AcctV) (ms : List AkmE) (i : Nat) : List Nat :=
  match as.find? (fun a => a.k == i) with
  | some a => a.post ++ a.pre.drop 16
  | none => ((ms.find? fun e => e.vid == i && e.fa == 1).map akmPost).getD []

theorem akmSends_vslot (ms : List AkmE) :
    akmSends ms B_VSLOT = ms.flatMap fun e => if e.fa = 1 then [[e.vid]] else [] := by
  simp only [akmSends, show B_VSLOT ≠ B_VBYTES by decide, show B_VSLOT ≠ B_AKMEM by decide,
    ite_false, ite_true]

theorem akmSends_bytes (ms : List AkmE) :
    akmSends ms B_BYTES = ms.flatMap fun e => if e.fa = 1 then
      (List.range 8).map (fun j => [e.vpost, j, e.pb.getD j 0]) ++ [[e.vpost, 8, e.bytes.getD 8 0]]
      else [] := by
  simp only [akmSends, show B_BYTES ≠ B_VBYTES by decide, show B_BYTES ≠ B_AKMEM by decide,
    show B_BYTES ≠ B_VSLOT by decide, ite_false, ite_true]

theorem acctSends_vslot (as : List AcctV) : acctV3Sends as B_VSLOT = as.map fun a => [a.k] := by
  simp only [acctV3Sends, show B_VSLOT ≠ B_VBYTES by decide, show B_VSLOT ≠ B_BYTES by decide,
    show B_VSLOT ≠ B_MEM by decide, ite_false, ite_true]

section
variable {pub : List Fp} {tr : Trace Fp} {r : V3Records} {ms : List AkmE}
  (hH : HoldsP nearAirV3D1 pub tr) (T : BaseTrafficD1 pub tr r) (W : BaseWfD1 pub r)
  (M : AkmOf pub tr ms)

include hH T M in
/-- **`VSLOT` in record form**: acct + akm sends = node receives. -/
theorem vslot_bal_rec (m : List Fp) :
    ((acctV3Sends r.accts B_VSLOT).map Msg.toFp).count m + ((akmSends ms B_VSLOT).map Msg.toFp).count m =
      ((nodeRecvs3 r.nodes B_VSLOT).map Msg.toFp).count m := by
  have h := vslot_bal_d1 hH T m
  rw [(M.traffic B_VSLOT m).1] at h
  exact h

include hH T W in
/-- A slot message is received by the node records at most once. -/
theorem node_vslot_le_one {i : Nat} (hiP : i < P) :
    ((nodeRecvs3 r.nodes B_VSLOT).map Msg.toFp).count (Msg.toFp [i]) ≤ 1 := by
  apply Classical.byContradiction; intro hc
  have hs : 2 ≤ ((nodeRecvs3 r.nodes B_VSLOT).map Msg.toFp).count (Msg.toFp [i]) := by omega
  simp only [nodeRecvs3, show B_VSLOT ≠ B_DIGEST by decide, show B_VSLOT ≠ B_PARENT by decide,
    show B_VSLOT ≠ B_EDGE by decide, show B_VSLOT ≠ B_BMAP by decide, show B_VSLOT ≠ B_DUP by decide,
    show B_VSLOT ≠ B_ENT by decide, show B_VSLOT ≠ B_UPB by decide, ite_false, ite_true,
    List.map_flatMap, List.count_flatMap] at hs
  let f : NodeS3 × Nat → List Msg := fun x =>
    match x.1.v.value with | some (i', _, _, _, true) => [[i']] | _ => []
  have hf1 : ∀ z ∈ r.nodes.zip (List.range r.nodes.length),
      (Function.comp (List.count (Msg.toFp [i])) (fun z => (f z).map Msg.toFp)) z ≤ 1 := by
    intro z _
    simp only [Function.comp, f]
    split <;> simp [List.count_singleton] <;> split <;> omega
  change 2 ≤ ((r.nodes.zip (List.range r.nodes.length)).map
    (Function.comp (List.count (Msg.toFp [i])) (fun z => (f z).map Msg.toFp))).sum at hs
  rw [LinkVPost.sum_01 _ _ hf1] at hs
  obtain ⟨q, q', hq, hq', hqq, e1, e2⟩ :=
    LinkVPost.countP_two _ (l := r.nodes.zip (List.range r.nodes.length)) hs
  have pick : ∀ k (hk : k < (r.nodes.zip (List.range r.nodes.length)).length),
      ((Function.comp (List.count (Msg.toFp [i])) (fun z => (f z).map Msg.toFp))
        (r.nodes.zip (List.range r.nodes.length))[k] == 1) = true →
      ∃ hk' : k < r.nodes.length, ∃ l pre po, r.nodes[k].v.value = some (i, l, pre, po, true) := by
    intro k hk e
    have hk' : k < r.nodes.length := by simpa using hk
    refine ⟨hk', ?_⟩
    simp only [List.getElem_zip, List.getElem_range, Function.comp, f, beq_iff_eq] at e
    cases hv : r.nodes[k].v.value with
    | none => rw [hv] at e; simp at e
    | some z =>
      obtain ⟨i', l, pre, po, w⟩ := z
      rw [hv] at e
      cases w with
      | false => simp at e
      | true =>
        simp only [List.map_cons, List.map_nil, List.count_singleton] at e
        split at e
        · rename_i heq
          have ci := W.nodes.canon _ (List.getElem_mem hk') i' (Link3.value_raw hv).1
          simp only [Msg.toFp, List.map_cons, List.map_nil, List.cons.injEq, and_true, beq_iff_eq] at heq
          have := Link3.ofNat_eq ci hiP heq
          subst this
          exact ⟨l, pre, po, rfl⟩
        · simp at e
  obtain ⟨hk, l, pre, po, hv⟩ := pick q hq e1
  obtain ⟨hk', l', pre', po', hv'⟩ := pick q' hq' e2
  exact hqq (Link3.val_unique W.nodes W.values (vparentBal_of_d1 hH T) (Link3.vlen_le W.values) hk hk' hv hv')

theorem toFp_single_eq {a i : Nat} (ha : a < P) (hi : i < P) :
    Msg.toFp [a] = Msg.toFp [i] ↔ a = i := by
  constructor
  · intro h
    simp only [Msg.toFp, List.map_cons, List.map_nil, List.cons.injEq, and_true] at h
    exact Link3.ofNat_eq ha hi h
  · intro h; rw [h]

theorem count_vslot_acct {as : List AcctV} {i : Nat} (hc : ∀ a ∈ as, a.k < P) (hi : i < P) :
    ((acctV3Sends as B_VSLOT).map Msg.toFp).count (Msg.toFp [i]) = as.countP (fun a => a.k == i) := by
  rw [acctSends_vslot, List.map_map, List.count_eq_countP, List.countP_map]
  apply List.countP_congr
  intro a ha
  simp only [Function.comp, beq_iff_eq]
  exact toFp_single_eq (hc a ha) hi

theorem count_vslot_akm : ∀ {ms : List AkmE} {i : Nat}, (∀ e ∈ ms, e.vid < P) → i < P →
    ((akmSends ms B_VSLOT).map Msg.toFp).count (Msg.toFp [i]) =
      ms.countP (fun e => e.vid == i && e.fa == 1)
  | [], i, _, _ => by simp [akmSends_vslot]
  | e :: es, i, hc, hi => by
    have ih := count_vslot_akm (ms := es) (i := i) (fun e' he' => hc e' (List.mem_cons_of_mem _ he')) hi
    rw [akmSends_vslot] at ih ⊢
    simp only [List.flatMap_cons, List.map_append, List.count_append, List.countP_cons, ih]
    have he := toFp_single_eq (hc e (List.mem_cons_self ..)) hi
    by_cases hfa : e.fa = 1
    · by_cases hv : e.vid = i
      · simp [hfa, hv]; omega
      · have hne : Msg.toFp [e.vid] ≠ Msg.toFp [i] := fun h => hv (he.mp h)
        simp [hfa, hv, hne]
    · simp [hfa]

include hH T W M in
/-- **At most one writer per slot**: acct records with `k = i` and FullAccess akm records with
`vid = i`. -/
theorem writers_le_one {i : Nat} (hiP : i < P) :
    r.accts.countP (fun a => a.k == i) + ms.countP (fun e => e.vid == i && e.fa == 1) ≤ 1 := by
  have hb := vslot_bal_rec hH T M (Msg.toFp [i])
  have h1 := node_vslot_le_one hH T W hiP
  rw [count_vslot_acct (fun a ha => ((W.accts.resolve_left (List.ne_nil_of_mem ha)).v1.len a ha).2.2.1) hiP,
    count_vslot_akm (fun e he => (M.wf.segs e he).canon.1) hiP] at hb
  omega

include hH T W in
/-- A slot message `[k]` the node records receive is a written node slot with value id `k`. -/
theorem node_slot_of_count {k : Nat} (hk : k < P)
    (hc : 0 < ((nodeRecvs3 r.nodes B_VSLOT).map Msg.toFp).count (Msg.toFp [k])) :
    ∃ p, ∃ hp : p < r.nodes.length, ∃ l pre po, r.nodes[p].v.value = some (k, l, pre, po, true) := by
  obtain ⟨x, hx, he⟩ := List.mem_map.mp (List.count_pos_iff.mp hc)
  simp only [nodeRecvs3, show B_VSLOT ≠ B_DIGEST by decide, show B_VSLOT ≠ B_PARENT by decide,
    show B_VSLOT ≠ B_EDGE by decide, show B_VSLOT ≠ B_BMAP by decide, show B_VSLOT ≠ B_DUP by decide,
    show B_VSLOT ≠ B_ENT by decide, show B_VSLOT ≠ B_UPB by decide, ite_false, ite_true,
    List.mem_flatMap] at hx
  obtain ⟨⟨s, n⟩, hsn, hx⟩ := hx
  obtain ⟨hn, rfl⟩ := Link3.mem_zip_range hsn
  split at hx
  · rename_i i l pre po hv
    simp only [List.mem_singleton] at hx
    subst hx
    have ci := W.nodes.canon _ (List.getElem_mem hn) i (Link3.value_raw hv).1
    have := (toFp_single_eq ci hk).mp he
    subst this
    exact ⟨n, hn, l, pre, po, hv⟩
  · simp at hx

include hH T W M in
/-- **A FullAccess akm record writes a node slot** (`VSLOT (vid)`). -/
theorem akm_written {e : AkmE} (he : e ∈ ms) (hfa : e.fa = 1) :
    ∃ p, ∃ hp : p < r.nodes.length, ∃ l pre po, r.nodes[p].v.value = some (e.vid, l, pre, po, true) := by
  have hk := (M.wf.segs e he).canon.1
  have hm : [e.vid] ∈ akmSends ms B_VSLOT := by
    rw [akmSends_vslot, List.mem_flatMap]; exact ⟨e, he, by simp [hfa]⟩
  have hc := List.count_pos_iff.mpr (List.mem_map_of_mem (f := Msg.toFp) hm)
  have hb := vslot_bal_rec hH T M (Msg.toFp [e.vid])
  exact node_slot_of_count hH T W hk (by omega)

include hH T W M in
theorem akm_vid_lt {e : AkmE} (he : e ∈ ms) (hfa : e.fa = 1) : e.vid < 2 ^ 22 := by
  have hk := (M.wf.segs e he).canon.1
  have hm : [e.vid] ∈ akmSends ms B_VSLOT := by
    rw [akmSends_vslot, List.mem_flatMap]; exact ⟨e, he, by simp [hfa]⟩
  have hc := List.count_pos_iff.mpr (List.mem_map_of_mem (f := Msg.toFp) hm)
  have hb := vslot_bal_rec hH T M (Msg.toFp [e.vid])
  exact vslot_lt hH T W hk (by omega)

include hH T W M in
/-- The stream of an acct record's slot is the acct's. -/
theorem pnOfD1_acct {a : AcctV} (ha : a ∈ r.accts) :
    pnOfD1 r.accts ms a.k = a.post ++ a.pre.drop 16 := by
  unfold pnOfD1
  cases hf : r.accts.find? (fun x => x.k == a.k) with
  | none => exact absurd hf (by simp only [List.find?_eq_none]; intro h; exact h a ha (by simp))
  | some a0 =>
    have h0 := List.mem_of_find?_eq_some hf
    have hk : a0.k = a.k := by simpa using List.find?_some hf
    simp only
    by_cases e : a0 = a
    · rw [e]
    · have := LinkStore.two_le_countP (fun x : AcctV => x.k == a.k) e (by simp [hk]) (by simp) h0 ha
      have hkP := ((W.accts.resolve_left (List.ne_nil_of_mem ha)).v1.len a ha).2.2.1
      have := writers_le_one hH T W M hkP
      omega

include hH T W M in
/-- The stream of a FullAccess akm record's slot is the record's. -/
theorem pnOfD1_akm {e : AkmE} (he : e ∈ ms) (hfa : e.fa = 1) :
    pnOfD1 r.accts ms e.vid = akmPost e := by
  have hkP := (M.wf.segs e he).canon.1
  have hw := writers_le_one hH T W M hkP
  have hm1 : 1 ≤ ms.countP (fun x => x.vid == e.vid && x.fa == 1) :=
    List.countP_pos_iff.mpr ⟨e, he, by simp [hfa]⟩
  unfold pnOfD1
  have hn : r.accts.find? (fun a => a.k == e.vid) = none := by
    rw [List.find?_eq_none]
    intro a ha hak
    have : 0 < r.accts.countP (fun a : AcctV => a.k == e.vid) := List.countP_pos_iff.mpr ⟨a, ha, hak⟩
    omega
  rw [hn]
  cases hf : ms.find? (fun x => x.vid == e.vid && x.fa == 1) with
  | none => exact absurd hf (by simp only [List.find?_eq_none]; intro h; exact h e he (by simp [hfa]))
  | some e0 =>
    have h0 := List.mem_of_find?_eq_some hf
    have hp0 := List.find?_some hf
    simp only [Option.map_some, Option.getD_some]
    by_cases ee : e0 = e
    · rw [ee]
    · have := LinkStore.two_le_countP (fun x : AkmE => x.vid == e.vid && x.fa == 1) ee hp0
        (by simp [hfa]) h0 he
      omega

include hH T W M in
/-- **`VBYTES`**: the value record of a FullAccess akm record's slot has at least 9 bytes (the
akm record sends `(vid, 8, bytes[8])`, only value records receive `VBYTES`). -/
theorem akm_vbytes_len {e : AkmE} (he : e ∈ ms) :
    ∃ t, ∃ ht : t < r.values.length, r.values[t].vid = e.vid ∧ 9 ≤ r.values[t].len := by
  have hw := M.wf.segs e he
  have hk := hw.canon.1
  let Mg : Msg := [e.vid, 8, e.bytes.getD 8 0]
  have hb := bal_users_d1 hH (b := B_VBYTES)
    (U := [Assembly.T_VAL, T_CODEC, Assembly.T_ACCT, T_AKEY, T_QV, T_AKM, T_UVAL]) (by decide)
    (by decide) (by decide +kernel) (by decide +kernel) (Msg.toFp Mg)
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at hb
  rw [val_count_d1 T _ _ _ (by decide +kernel), val_count_d1 T _ _ _ (by decide +kernel),
    show isAtD1 Assembly.T_ACCT = AcctV3.interactions from rfl, tcnt_of_traffic T.accts,
    tcnt_of_traffic T.accts,
    tableBusCount_noside (s := false) (is := isAtD1 T_CODEC) (by decide +kernel),
    tableBusCount_noside (s := false) (is := isAtD1 T_AKEY) (by decide +kernel),
    tableBusCount_noside (s := false) (is := isAtD1 T_QV) (by decide +kernel),
    tableBusCount_noside (s := false) (is := isAtD1 T_AKM) (by decide +kernel),
    tableBusCount_noside (s := false) (is := isAtD1 T_UVAL) (by decide +kernel),
    show isAtD1 T_AKM = AkmV3.interactions from rfl, (M.traffic B_VBYTES _).1] at hb
  have hs : 0 < (((akmTraffic ms).sends B_VBYTES).map Msg.toFp).count (Msg.toFp Mg) := by
    apply List.count_pos_iff.mpr
    apply List.mem_map_of_mem
    simp only [akmTraffic, akmSends, ite_true, List.mem_flatMap, List.mem_map, List.mem_range]
    exact ⟨e, he, 8, by have := hw.len.1; omega, rfl⟩
  have r0 : tcnt (acctV3Traffic r.accts) false B_VBYTES (Msg.toFp Mg) = 0 := by
    simp [tcnt, acctV3Traffic, acctRecvs, B_VBYTES, B_MEM]
  have v0 : tcnt (valTraffic r.values) true B_VBYTES (Msg.toFp Mg) = 0 := by
    simp [tcnt, valTraffic, valSends, B_VBYTES, B_BYTES, B_ENT, B_SIZE]
  have hv : 0 < tcnt (valTraffic r.values) false B_VBYTES (Msg.toFp Mg) := by omega
  simp only [tcnt, Bool.false_eq_true, ite_false, valTraffic, valRecvs, ite_true] at hv
  obtain ⟨m, hm, he⟩ := List.mem_map.mp (List.count_pos_iff.mp hv)
  obtain ⟨x, hx', hm⟩ := List.mem_flatMap.mp hm
  obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hx'
  split at hm
  · simp at hm
  · rename_i hz
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
    have ce := W.values.canon _ hx'
    simp only [Mg, Msg.toFp, List.map_cons, List.map_nil, List.cons.injEq] at he
    have e1 := Link3.ofNat_eq ce.1 hk he.1
    have hqP : q < P := by
      have := List.mem_range.mp hq; have := Link3.val_bytes_lt W.values ht; unfold P; omega
    have e2 := Link3.ofNat_eq hqP (by unfold P; omega) he.2.1
    have hq' := List.mem_range.mp hq
    have hsh := (W.values.shape _ hx').2 (by simpa using hz)
    exact ⟨t, ht, e1, by omega⟩

/-- The FullAccess akm streams have length `9`. -/
theorem akmPost_length {e : AkmE} (hw : AkmSegWf e) : (akmPost e).length = 9 := by
  simp [akmPost, hw.len.2]

include M in
/-- **A raw `BYTES` message of `akmV3`** is `(VPOST(vid), j, akmPost[j])`, `j < 9`, of a FullAccess
record. -/
theorem akmBytes_mem {y : List Fp} (hy : y ∈ akmBytes tr pub) :
    ∃ e ∈ ms, e.fa = 1 ∧ ∃ j, j < 9 ∧ y = Msg.toFp [e.vpost, j, (akmPost e).getD j 0] := by
  have hc : 0 < tableBusCount AkmV3.interactions tr T_AKM pub B_BYTES true y := by
    rw [tableBusCount_eq]
    exact List.count_pos_iff.mpr hy
  rw [(M.traffic B_BYTES y).1] at hc
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp (List.count_pos_iff.mp hc)
  simp only [akmTraffic] at hv
  rw [akmSends_bytes, List.mem_flatMap] at hv
  obtain ⟨e, he, hv⟩ := hv
  have hw := M.wf.segs e he
  split at hv
  · rename_i hfa
    refine ⟨e, he, hfa, ?_⟩
    simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at hv
    rcases hv with ⟨j, hj, rfl⟩ | rfl
    · refine ⟨j, by omega, ?_⟩
      simp only [akmPost, List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [hw.len.2]; omega)]
    · refine ⟨8, by omega, ?_⟩
      have h8 : (akmPost e).getD 8 0 = e.bytes.getD 8 0 := by
        unfold akmPost
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hw.len.2]; exact Nat.le_refl _), hw.len.2]
        rfl
      rw [h8]
  · simp at hv

end

theorem akmPost_canon {e : AkmE} (hw : AkmSegWf e) : ∀ x ∈ akmPost e, x < P := by
  intro x hx
  simp only [akmPost, List.mem_append, List.mem_singleton] at hx
  rcases hx with hx | rfl
  · exact hw.canon.2.2.2 x hx
  · rw [List.getD_eq_getElem?_getD]
    cases hb : e.bytes[8]? with
    | none => simp; unfold P; omega
    | some b =>
      have := hw.bytes8 b (List.mem_of_getElem? hb)
      simp only [Option.getD_some]; unfold P; omega

/-- The D1 post streams are canonical. -/
theorem pnOfD1_canon {pub : List Fp} {tr : Trace Fp} {r : V3Records} {ms : List AkmE}
    (W : BaseWfD1 pub r) (M : AkmOf pub tr ms) (i : Nat) : ∀ x ∈ pnOfD1 r.accts ms i, x < P := by
  intro x hx
  unfold pnOfD1 at hx
  cases hf : r.accts.find? (fun a => a.k == i) with
  | some a0 =>
    rw [hf] at hx
    simp only [List.mem_append] at hx
    have ha := List.mem_of_find?_eq_some hf
    have hc := (W.accts.resolve_left (List.ne_nil_of_mem ha)).v1.canon a0 ha
    rcases hx with hx | hx
    · exact hc x (List.mem_append_right _ hx)
    · exact hc x (List.mem_append_left _ (List.mem_of_mem_drop hx))
  | none =>
    rw [hf] at hx
    cases hg : ms.find? (fun e => e.vid == i && e.fa == 1) with
    | none => rw [hg] at hx; simp at hx
    | some e =>
      rw [hg] at hx
      simp only [Option.map_some, Option.getD_some] at hx
      exact akmPost_canon (M.wf.segs e (List.mem_of_find?_eq_some hg)) x hx

/-! ## The extra `BYTES` senders' `K_VPOST` messages -/

section
variable {cb : NearSpec.Bytes} {h : HintD1} {q : Public.PrepD1} {ov : Nat} {tr : Trace Fp} {r : V3Records}
  {ms : List AkmE}

/-- **A `K_VPOST(i)` message of the extra `BYTES` senders** is a FullAccess akm record's post
stream entry (the public body-prefix sends have kind `K_RF`). -/
theorem extra_vpost (hp : prepD1 cb h = .ok q) (hlen : (Public.preparedBytesD1 q ov).length < P)
    (hH : HoldsP nearAirV3D1 (ZkFormal.Udr.pubOf Fp (Public.preparedBytesD1 q ov)) tr)
    (T : BaseTrafficD1 (ZkFormal.Udr.pubOf Fp (Public.preparedBytesD1 q ov)) tr r)
    (W : BaseWfD1 (ZkFormal.Udr.pubOf Fp (Public.preparedBytesD1 q ov)) r)
    (M : AkmOf (ZkFormal.Udr.pubOf Fp (Public.preparedBytesD1 q ov)) tr ms) {i : Nat} (hi : i < 2 ^ 22)
    {y : List Fp} (hy : y ∈ extraBytes tr (ZkFormal.Udr.pubOf Fp (Public.preparedBytesD1 q ov)))
    {e : Fp} (hyh : y.head? = some e) (he : Fp.ofNat e.toNat = Fp.ofNat (msgId K_VPOST i)) :
    ∃ x ∈ ms, x.fa = 1 ∧ x.vid = i ∧ ∃ j, j < 9 ∧
      y.map Fp.toNat = [msgId K_VPOST i, j, (akmPost x).getD j 0] := by
  have hP : P < 256 ^ 4 := by unfold P; omega
  have hiP : msgId K_VPOST i < P := by unfold msgId K_VPOST P; omega
  unfold extraBytes at hy
  rcases List.mem_append.mp hy with hy | hy
  · obtain ⟨x, hx, hfa, j, hj, rfl⟩ := akmBytes_mem M hy
    have hw := M.wf.segs x hx
    have hv := akm_vid_lt hH T W M hx hfa
    have hxP : x.vpost < P := by unfold AkmE.vpost K_VPOST P; omega
    simp only [Msg.toFp, List.map_cons, List.head?_cons, Option.some.injEq] at hyh
    subst hyh
    rw [Fp.ofNat_toNat] at he
    have hid : x.vpost = msgId K_VPOST i := Link3.ofNat_eq hxP hiP he
    have hxi : x.vid = i := by unfold AkmE.vpost msgId at hid; omega
    refine ⟨x, hx, hfa, hxi, j, hj, ?_⟩
    have hcan : ∀ z ∈ [x.vpost, j, (akmPost x).getD j 0], z < P := by
      intro z hz
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl | rfl
      · exact hxP
      · unfold P; omega
      · rw [List.getD_eq_getElem?_getD]
        cases hg : (akmPost x)[j]? with
        | none => simp; unfold P; omega
        | some z =>
          simp only [Option.getD_some]
          have hz := List.mem_of_getElem? hg
          simp only [akmPost, List.mem_append, List.mem_singleton] at hz
          rcases hz with hz | rfl
          · exact hw.canon.2.2.2 z hz
          · rw [List.getD_eq_getElem?_getD]
            cases hb : x.bytes[8]? with
            | none => simp; unfold P; omega
            | some b =>
              have := hw.bytes8 b (List.mem_of_getElem? hb)
              simp only [Option.getD_some]; unfold P; omega
    rw [LinkVPost.toNat_toFp hcan, hid]
  · have hc : 0 < pubCount nearAirV3D1 (ZkFormal.Udr.pubOf Fp (Public.preparedBytesD1 q ov)) B_BYTES true y := by
      rw [← count_pubListD1]; exact List.count_pos_iff.mpr hy
    have hk := pub_bytes_send_head q ov (prepD1_roots hp) (prepD1_source_roots hp) (prepD1_leaves hp)
      (by omega) hc
    rw [hk, Option.some.injEq] at hyh
    subst hyh
    rw [Fp.ofNat_toNat] at he
    have := Link3.ofNat_eq (by unfold K_RF P; omega) hiP he
    unfold K_RF msgId K_VPOST at this
    omega

end

end ZkFormal.NearV3.D1.Link
