import ZkFormal.NearV3.Assembly.LinkUps
import ZkFormal.NearV3.Assembly.LinkStore

/-!
# ZkFormal.NearV3.Assembly.LinkVPost — `VPostOk` from natural-valued post streams

`Link3.VPostOk others pv` asks the `K_VPOST i` messages of `others` to be the bytes of
`pv i : Bytes`.  The acct view only makes them canonical naturals.  `VPostOkN others pn` is the
natural-valued form; **`vpostOk_of_N`** recovers `VPostOk others (fun i => toB (pn i))` when every
streamed id `i` is a written value slot `(i, l, pre, po, true)` of a node record with
`|pn i| ≤ l`: that slot's post window receives `digMsg (msgId K_VPOST i) l po`, SHA-provided, so
`sha_len_le` gives `|pn i| = l` and `sha_core` makes `pn i` byte-valued.  This is a pure addition:
`VPostOk` and all its consumers (`Link/Post3`, `Extract/Ups/*`) are unchanged.
-/

namespace ZkFormal.NearV3.Assembly

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near

namespace LinkVPost

open ZkFormal.NearV3 ZkFormal.NearV3.Link3

/-- Natural-valued post value streams. -/
structure VPostOkN (others : List Msg) (pn : Nat → List Nat) : Prop where
  sends : ∀ i, i < 2 ^ 22 → ∀ m ∈ others, ∀ a, m.head? = some a →
    Fp.ofNat a = Fp.ofNat (msgId K_VPOST i) →
    ∃ j, j < (pn i).length ∧ m = [msgId K_VPOST i, j, (pn i).getD j 0]
  canon : ∀ i, ∀ x ∈ pn i, x < P

/-- The byte form is a special case. -/
theorem VPostOk.toN {others : List Msg} {pv : Nat → NearSpec.Bytes} (h : VPostOk others pv) :
    VPostOkN others (fun i => (pv i).map UInt8.toNat) where
  sends i hi m hm a ha he := by
    obtain ⟨j, hj, e⟩ := h.sends i hi m hm a ha he
    exact ⟨j, by simpa using hj, e⟩
  canon i x hx := by
    obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx
    have := UInt8.toNat_lt y; unfold P; omega

theorem toB_bytes : ∀ l : List Nat, (∀ x ∈ l, x < 256) → (toB l).map UInt8.toNat = l
  | [], _ => rfl
  | x :: l, h => by
    have hx := h x (by simp)
    simp only [toB, List.map_cons, List.cons.injEq] at *
    refine ⟨?_, toB_bytes l (fun y hy => h y (by simp [hy]))⟩
    show (UInt8.ofNat x).toNat = x
    simp only [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (show x < 2 ^ 8 by omega)]

variable {vs : List NodeS3} {hs : List HeadE} {es : List ValE} {others : List Msg}
  {shaS shaR : Nat → List Fp → Nat}

/-- Every `BYTES` message with id `≡ msgId K_VPOST i` (node / val / others) streams `pn i`. -/
theorem vpost_sendsN (hw : NodeWf3 vs) (hvw : ValWf es) {pn : Nat → List Nat} (HP : VPostOkN others pn)
    {i : Nat} (hi : i < 2 ^ 22) :
    ∀ m ∈ nodeSends3 vs B_BYTES ++ valSends es B_BYTES ++ others, ∀ a, m.head? = some a →
      Fp.ofNat a = Fp.ofNat (msgId K_VPOST i) →
      ∃ j, j < (pn i).length ∧ m = [msgId K_VPOST i, j, (pn i).getD j 0] := by
  intro m hm a ha he
  rcases List.mem_append.mp hm with hm | hm
  · -- node / val messages never carry a `K_VPOST` id (`vpost_sends` with no others, empty `pv`)
    have h0 : VPostOk ([] : List Msg) (fun _ => []) := ⟨fun _ _ m hm => by simp at hm⟩
    obtain ⟨j, hj, -⟩ := vpost_sends (others := []) hw hvw h0 hi m (by simpa using hm) a ha he
    simp at hj
  · exact HP.sends i hi m hm a ha he

/-- **Byte-ness of a written post value** from its post-window digest. -/
theorem vpost_bytesN (hw : NodeWf3 vs) (hvw : ValWf es) (H : ShaHyp vs hs es others shaS shaR)
    {pn : Nat → List Nat} (HP : VPostOkN others pn) {p : Nat} (hp : p < vs.length) {i l : Nat}
    {pre po : List Nat} (hv : vs[p].v.value = some (i, l, pre, po, true)) (hi : i < 2 ^ 22)
    (hpl : (pn i).length ≤ l) : (pn i).length = l ∧ ∀ x ∈ pn i, x < 256 := by
  have hlP : l < P := hw.canon _ (List.getElem_mem hp) l (value_raw hv).2
  have hm : digMsg (msgId K_VPOST i) l po ∈ nodeRecvs3 vs B_DIGEST ++ headRecvs hs B_DIGEST := by
    apply List.mem_append_left
    unfold nodeRecvs3; rw [if_pos rfl, List.mem_flatMap]
    refine ⟨(vs[p], p), zip_range_mem vs hp, List.mem_append_right _ ?_⟩
    simp [hv]
  have hrecv := H.digest _ (cnt_pos3 hm)
  have hle := sha_len_le H.sha _ H.bytes (enc := pn i) hlP (by omega) (vpost_sendsN hw hvw HP hi) hrecv
  have hlen : (pn i).length = l := by omega
  rw [← hlen] at hrecv
  have hc := Link.sha_core H.sha _ H.bytes (enc := pn i)
    (by unfold msgId K_VPOST P; omega) (HP.canon i) (by omega)
    (fun x hx => hw.canon _ (List.getElem_mem hp) x (value_po_raw hv x hx))
    (vpost_sendsN hw hvw HP hi) hrecv
  exact ⟨hlen, hc.1⟩

/-- **`VPostOk` from the natural-valued streams**, given that every streamed id is a written value
slot whose length bounds the stream. -/
theorem vpostOk_of_N (hw : NodeWf3 vs) (hvw : ValWf es) (H : ShaHyp vs hs es others shaS shaR)
    {pn : Nat → List Nat} (HP : VPostOkN others pn)
    (hwr : ∀ i, i < 2 ^ 22 → ∀ m ∈ others, ∀ a, m.head? = some a →
      Fp.ofNat a = Fp.ofNat (msgId K_VPOST i) →
      ∃ p, ∃ hp : p < vs.length, ∃ l pre po, vs[p].v.value = some (i, l, pre, po, true) ∧
        (pn i).length ≤ l) :
    VPostOk others (fun i => toB (pn i)) where
  sends i hi m hm a ha he := by
    obtain ⟨p, hp, l, pre, po, hv, hpl⟩ := hwr i hi m hm a ha he
    obtain ⟨-, hb⟩ := vpost_bytesN hw hvw H HP hp hv hi hpl
    obtain ⟨j, hj, rfl⟩ := HP.sends i hi m hm a ha he
    rw [toB_bytes _ hb]
    exact ⟨j, by simpa [toB] using hj, rfl⟩

/-! ## The acct post streams -/

/-- The post stream of the acct record of slot `i` (empty if none). -/
def pnOf (as : List AcctV) (i : Nat) : List Nat :=
  ((as.find? fun a => a.k == i).map fun a => a.post ++ a.pre.drop 16).getD []

theorem acct_wf {pub : List Fp} {r : V3Records} (W : V3RecordsWf pub r) {a : AcctV} (ha : a ∈ r.accts) :
    a.pre.length = 72 ∧ a.post.length = 16 ∧ a.k < P ∧ a.tlast < P :=
  (W.accts.resolve_left (List.ne_nil_of_mem ha)).v1.len a ha

theorem acct_canon {pub : List Fp} {r : V3Records} (W : V3RecordsWf pub r) {a : AcctV} (ha : a ∈ r.accts) :
    ∀ x ∈ a.pre ++ a.post, x < P :=
  (W.accts.resolve_left (List.ne_nil_of_mem ha)).v1.canon a ha

/-- **`VBYTES`**: the value record of an acct slot has at least the acct's 72 pre bytes. -/
theorem vbytes_len {pub : List Fp} {tr : Trace Fp} {r : V3Records} (hH : HoldsP nearAirV3 pub tr)
    (T : V3RecordsTraffic pub tr r) (W : V3RecordsWf pub r) {a : AcctV} (ha : a ∈ r.accts) :
    ∃ t, ∃ ht : t < r.values.length, r.values[t].vid = a.k ∧ 72 ≤ r.values[t].len := by
  obtain ⟨hpre, -, hk, -⟩ := acct_wf W ha
  let M : Msg := [a.k, 71, a.pre.getD 71 0]
  have hb := bal_users hH (b := B_VBYTES) (U := [T_VAL, T_CODEC, T_ACCT, T_AKEY, T_QV]) (by decide)
    (by decide) (by decide +kernel) (by decide +kernel) (Msg.toFp M)
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at hb
  rw [val_count T _ _ _ (by decide +kernel), val_count T _ _ _ (by decide +kernel),
    show isAt T_ACCT = AcctV3.interactions from rfl, tcnt_of_traffic T.accts, tcnt_of_traffic T.accts,
    tableBusCount_noside (s := false) (is := isAt T_CODEC) (by decide +kernel),
    tableBusCount_noside (s := false) (is := isAt T_AKEY) (by decide +kernel),
    tableBusCount_noside (s := false) (is := isAt T_QV) (by decide +kernel)] at hb
  have hs : 0 < tcnt (acctV3Traffic r.accts) true B_VBYTES (Msg.toFp M) := by
    simp only [tcnt, ite_true, acctV3Traffic]
    apply List.count_pos_iff.mpr
    apply List.mem_map_of_mem
    simp only [acctV3Sends, ite_true, List.mem_flatMap]
    exact ⟨a, ha, mem_emitAt3.mpr ⟨71, by omega, rfl⟩⟩
  have r0 : tcnt (acctV3Traffic r.accts) false B_VBYTES (Msg.toFp M) = 0 := by
    simp [tcnt, acctV3Traffic, acctRecvs, B_VBYTES, B_MEM]
  have v0 : tcnt (valTraffic r.values) true B_VBYTES (Msg.toFp M) = 0 := by
    simp [tcnt, valTraffic, valSends, B_VBYTES, B_BYTES, B_ENT, B_SIZE]
  have hv : 0 < tcnt (valTraffic r.values) false B_VBYTES (Msg.toFp M) := by omega
  simp only [tcnt, Bool.false_eq_true, ite_false, valTraffic, valRecvs, ite_true] at hv
  obtain ⟨m, hm, he⟩ := List.mem_map.mp (List.count_pos_iff.mp hv)
  obtain ⟨e, he', hm⟩ := List.mem_flatMap.mp hm
  obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem he'
  split at hm
  · simp at hm
  · rename_i hz
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
    have ce := W.values.canon _ he'
    simp only [M, Msg.toFp, List.map_cons, List.map_nil, List.cons.injEq] at he
    have e1 := ofNat_eq ce.1 hk he.1
    have hqP : q < P := by have := List.mem_range.mp hq; have := val_bytes_lt W.values ht; unfold P; omega
    have e2 := ofNat_eq hqP (by unfold P; omega) he.2.1
    have hq' := List.mem_range.mp hq
    have hsh := (W.values.shape _ he').2 (by simpa using hz)
    exact ⟨t, ht, e1, by omega⟩

/-- **`hvpostLen`** for `pv = toB ∘ pnOf r.accts`. -/
theorem hvpostLen_of {pub : List Fp} {tr : Trace Fp} {r : V3Records} (hH : HoldsP nearAirV3 pub tr)
    (T : V3RecordsTraffic pub tr r) (W : V3RecordsWf pub r) :
    ∀ p (hp : p < r.nodes.length) i l pre po, r.nodes[p].v.value = some (i, l, pre, po, true) →
      (toB (pnOf r.accts i)).length ≤ l := by
  intro p hp i l pre po hv
  simp only [toB, List.length_map, pnOf]
  cases hf : r.accts.find? (fun a => a.k == i) with
  | none => simp
  | some a =>
    have ha := List.mem_of_find?_eq_some hf
    have hk : a.k = i := by simpa using List.find?_some hf
    obtain ⟨hpre, hpost, -, -⟩ := acct_wf W ha
    obtain ⟨t, ht, hvt, hl⟩ := vbytes_len hH T W ha
    obtain ⟨t', ht', hvt', hl'⟩ := val_link W.nodes W.values (vparentBal_of hH T) hp hv
    have := vid_inj W.values (vlen_le W.values) ht ht' (by rw [hvt, hvt', hk])
    subst this
    simp only [Option.map_some, Option.getD_some, List.length_append, List.length_drop]
    omega

/-! ## Acct slots are written value slots, one acct per slot -/

theorem countP_two {α : Type} (p : α → Bool) : ∀ {l : List α}, 2 ≤ l.countP p →
    ∃ i j, ∃ hi : i < l.length, ∃ hj : j < l.length, i ≠ j ∧ p l[i] = true ∧ p l[j] = true
  | [], h => by simp at h
  | x :: l, h => by
    rw [List.countP_cons] at h
    by_cases hx : p x = true
    · rw [if_pos hx] at h
      obtain ⟨y, hy, hpy⟩ := List.countP_pos_iff.mp (show 0 < l.countP p by omega)
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hy
      exact ⟨0, j + 1, by simp, by simp; omega, by omega, hx, by simpa using hpy⟩
    · rw [if_neg hx] at h
      obtain ⟨i, j, hi, hj, hij, h1, h2⟩ := countP_two p (l := l) (by omega)
      exact ⟨i + 1, j + 1, by simp; omega, by simp; omega, by omega, by simpa using h1, by simpa using h2⟩

/-- A `VSLOT` id `i` (an acct's `k`) is the value id of a written slot of a node record. -/
theorem acct_written {pub : List Fp} {tr : Trace Fp} {r : V3Records} (hH : HoldsP nearAirV3 pub tr)
    (T : V3RecordsTraffic pub tr r) (W : V3RecordsWf pub r) {a : AcctV} (ha : a ∈ r.accts) :
    ∃ p, ∃ hp : p < r.nodes.length, ∃ l pre po, r.nodes[p].v.value = some (a.k, l, pre, po, true) := by
  have hm : [a.k] ∈ acctV3Sends r.accts B_VSLOT := by
    simp only [acctV3Sends, show B_VSLOT ≠ B_VBYTES by decide, show B_VSLOT ≠ B_BYTES by decide,
      show B_VSLOT ≠ B_MEM by decide, ite_false, ite_true, List.mem_map]
    exact ⟨a, ha, rfl⟩
  have hc := List.count_pos_iff.mpr (List.mem_map_of_mem (f := Msg.toFp) hm)
  rw [vslot_bal hH T] at hc
  obtain ⟨x, hx, he⟩ := List.mem_map.mp (List.count_pos_iff.mp hc)
  simp only [nodeRecvs3, show B_VSLOT ≠ B_DIGEST by decide, show B_VSLOT ≠ B_PARENT by decide,
    show B_VSLOT ≠ B_EDGE by decide, show B_VSLOT ≠ B_BMAP by decide, show B_VSLOT ≠ B_DUP by decide,
    show B_VSLOT ≠ B_ENT by decide, show B_VSLOT ≠ B_UPB by decide, ite_false, ite_true,
    List.mem_flatMap] at hx
  obtain ⟨⟨s, n⟩, hsn, hx⟩ := hx
  obtain ⟨hn, rfl⟩ := mem_zip_range hsn
  split at hx
  · rename_i i l pre po hv
    simp only [List.mem_singleton] at hx
    subst hx
    have ci := W.nodes.canon _ (List.getElem_mem hn) i (value_raw hv).1
    simp only [Msg.toFp, List.map_cons, List.map_nil, List.cons.injEq, and_true] at he
    have := ofNat_eq ci (acct_wf W ha).2.2.1 he
    subst this
    exact ⟨n, hn, l, pre, po, hv⟩
  · simp at hx

theorem two_le_countP_idx {α : Type} (p : α → Bool) : ∀ (l : List α) (i j : Nat) (hi : i < l.length)
    (hj : j < l.length), i ≠ j → p l[i] = true → p l[j] = true → 2 ≤ l.countP p
  | [], _, _, hi, _, _, _, _ => by simp at hi
  | x :: l, i, j, hi, hj, hij, h1, h2 => by
    rw [List.countP_cons]
    rcases i with _ | i <;> rcases j with _ | j
    · exact absurd rfl hij
    · simp only [List.getElem_cons_zero] at h1
      simp only [List.getElem_cons_succ] at h2
      have := List.countP_pos_iff.mpr ⟨_, List.getElem_mem (by simp at hj; omega), h2⟩
      rw [if_pos h1]; omega
    · simp only [List.getElem_cons_zero] at h2
      simp only [List.getElem_cons_succ] at h1
      have := List.countP_pos_iff.mpr ⟨_, List.getElem_mem (by simp at hi; omega), h1⟩
      rw [if_pos h2]; omega
    · simp only [List.getElem_cons_succ] at h1 h2
      have := two_le_countP_idx p l i j (by simp at hi; omega) (by simp at hj; omega) (by omega) h1 h2
      split <;> omega

theorem sum_01 {α : Type} (g : α → Nat) : ∀ l : List α, (∀ x ∈ l, g x ≤ 1) →
    (l.map g).sum = l.countP (fun x => g x == 1)
  | [], _ => rfl
  | x :: l, h => by
    have hx := h x (by simp)
    have ih := sum_01 g l (fun y hy => h y (by simp [hy]))
    rw [List.map_cons, List.sum_cons, List.countP_cons, ih]
    by_cases e : g x = 1 <;> simp [e] <;> omega

/-- **One acct per slot.** -/
theorem acct_unique {pub : List Fp} {tr : Trace Fp} {r : V3Records} (hH : HoldsP nearAirV3 pub tr)
    (T : V3RecordsTraffic pub tr r) (W : V3RecordsWf pub r) (i : Nat) :
    r.accts.countP (fun a => a.k == i) ≤ 1 := by
  apply Classical.byContradiction; intro hc
  obtain ⟨x, y, hx, hy, hxy, h1, h2⟩ := countP_two (fun a : AcctV => a.k == i) (l := r.accts) (by omega)
  simp only [beq_iff_eq] at h1 h2
  have hs : 2 ≤ ((acctV3Sends r.accts B_VSLOT).map Msg.toFp).count (Msg.toFp [i]) := by
    simp only [acctV3Sends, show B_VSLOT ≠ B_VBYTES by decide, show B_VSLOT ≠ B_BYTES by decide,
      show B_VSLOT ≠ B_MEM by decide, ite_false, ite_true, List.map_map, List.count_eq_countP,
      List.countP_map]
    exact two_le_countP_idx _ r.accts x y hx hy hxy (by simp [h1]) (by simp [h2])
  rw [vslot_bal hH T] at hs
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
  rw [sum_01 _ _ hf1] at hs
  obtain ⟨q, q', hq, hq', hqq, e1, e2⟩ := countP_two _ (l := r.nodes.zip (List.range r.nodes.length)) hs
  have hiP : i < P := by rw [← h1]; exact (acct_wf W (List.getElem_mem hx)).2.2.1
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
          have ci := W.nodes.canon _ (List.getElem_mem hk') i' (value_raw hv).1
          simp only [Msg.toFp, List.map_cons, List.map_nil, List.cons.injEq, and_true, beq_iff_eq] at heq
          have := ofNat_eq ci hiP heq
          subst this
          exact ⟨l, pre, po, rfl⟩
        · simp at e
  obtain ⟨hk, l, pre, po, hv⟩ := pick q hq e1
  obtain ⟨hk', l', pre', po', hv'⟩ := pick q' hq' e2
  exact hqq (val_unique W.nodes W.values (vparentBal_of hH T) (vlen_le W.values) hk hk' hv hv')

theorem toNat_toFp {x : Msg} (h : ∀ y ∈ x, y < P) : (Msg.toFp x).map Fp.toNat = x := by
  simp only [Msg.toFp, List.map_map]
  conv => rhs; rw [← List.map_id x]
  apply List.map_congr_left
  intro y hy
  simp only [Function.comp, id, Fp.toNat_ofNat, Nat.mod_eq_of_lt (h y hy)]

theorem not_vpost {b k i : Nat} (hb : b < P) (hk : b % 16 = k) (hk10 : k ≠ K_VPOST) (hi : i < 2 ^ 22)
    (he : Fp.ofNat b = Fp.ofNat (msgId K_VPOST i)) : False := by
  have := ofNat_eq hb (by unfold msgId K_VPOST P; omega) he
  subst this
  unfold msgId at hk
  apply hk10; rw [← hk]; unfold K_VPOST; omega

/-- **The `K_VPOST` messages of `othersBytes` are acct post streams.** -/
theorem vpost_source {cb : NearSpec.Bytes} {h : NearSpecV3.Hint} {p : NearSpecV3.Prep} {oh : Nat}
    {tr : Trace Fp} {r : V3Records} (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r) {i : Nat} (hi : i < 2 ^ 22) :
    ∀ m ∈ othersBytes tr (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r, ∀ a, m.head? = some a →
      Fp.ofNat a = Fp.ofNat (msgId K_VPOST i) →
      ∃ a' ∈ r.accts, a'.k = i ∧ ∃ j, j < 72 ∧
        m = [msgId K_VPOST i, j, (a'.post ++ a'.pre.drop 16).getD j 0] := by
  intro m hm a ha he
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hm
  have hy' := (eraseAll_sublist _ _).subset hy
  cases hyh : y.head? with
  | none => simp [List.head?_map, hyh] at ha
  | some e =>
    simp only [List.head?_map, hyh, Option.map_some, Option.some.injEq] at ha
    subst ha
    have heP := Fp.toNat_lt e
    simp only [otherBytes, otherRecBytes, List.mem_append, List.map_append] at hy'
    have kinX : ∀ {ks : List Nat} {x : Msg}, KindIn ks x → K_VPOST ∉ ks → y = Msg.toFp x → False := by
      intro ks x hk hks hyx
      subst hyx
      cases x with
      | nil => simp [Msg.toFp] at hyh
      | cons b xs =>
        simp only [Msg.toFp, List.map_cons, List.head?_cons, Option.some.injEq] at hyh
        subst hyh
        obtain ⟨h1, h2⟩ := hk b rfl
        rw [Fp.toNat_ofNat, Nat.mod_eq_of_lt h1] at he
        exact not_vpost h1 rfl (fun e => hks (e ▸ h2)) hi he
    rcases hy' with ((((hy' | hy') | hy') | hy') | hy') | hy'
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy'
      exact (kinX (upsKindIn_of hp hsz hH T W x hx) (by decide) rfl).elim
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy'
      exact (kinX (rcptKindIn W.listsCount.1 W.listsCount.2 x hx) (by decide) rfl).elim
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy'
      simp only [acctV3Sends, show B_BYTES ≠ B_VBYTES by decide, ite_false, ite_true,
        List.mem_flatMap] at hx
      obtain ⟨a', ha', hx⟩ := hx
      obtain ⟨j, hj, rfl⟩ := mem_emitAt3.mp hx
      have hk := acct_slot_lt hH T W ha'
      obtain ⟨hpre, hpost, -, -⟩ := acct_wf W ha'
      have hc := acct_canon W ha'
      have hcan : ∀ z ∈ [msgId K_VPOST a'.k, 0 + j, (a'.post ++ a'.pre.drop 16).getD j 0], z < P := by
        intro z hz
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl | rfl
        · unfold msgId K_VPOST P; omega
        · simp only [List.length_append, List.length_drop] at hj; unfold P; omega
        · rw [List.getD_eq_getElem?_getD]
          cases hg : (a'.post ++ a'.pre.drop 16)[j]? with
          | none => simp; unfold P; omega
          | some z =>
            simp only [Option.getD_some]
            have hz := List.mem_of_getElem? hg
            simp only [List.mem_append] at hz
            rcases hz with hz | hz
            · exact hc z (List.mem_append_right _ hz)
            · exact hc z (List.mem_append_left _ (List.mem_of_mem_drop hz))
      rw [toNat_toFp hcan]
      simp only [Msg.toFp, List.map_cons, List.head?_cons, Option.some.injEq] at hyh
      subst hyh
      rw [Fp.ofNat_toNat] at he
      have hid : msgId K_VPOST a'.k = msgId K_VPOST i :=
        ofNat_eq (by unfold msgId K_VPOST P; omega) (by unfold msgId K_VPOST P; omega) he
      have hki : a'.k = i := by unfold msgId at hid; omega
      refine ⟨a', ha', hki, j, ?_, by rw [hki, Nat.zero_add]⟩
      simp only [List.length_append, List.length_drop] at hj; omega
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy'
      exact (kinX (srcpKindIn W.srcp x hx) (by decide) rfl).elim
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy'
      exact (kinX (mrkKindIn W (pubNat_pubOf_lt _) x hx) (by decide) rfl).elim
    · have := codecKindIn hp hsz hH y hy' e hyh
      exact (not_vpost heP this (by decide) hi he).elim

theorem pnOf_eq {pub : List Fp} {tr : Trace Fp} {r : V3Records} (hH : HoldsP nearAirV3 pub tr)
    (T : V3RecordsTraffic pub tr r) (W : V3RecordsWf pub r) {a : AcctV} (ha : a ∈ r.accts) :
    pnOf r.accts a.k = a.post ++ a.pre.drop 16 := by
  unfold pnOf
  cases hf : r.accts.find? (fun x => x.k == a.k) with
  | none => exact absurd hf (by simp only [List.find?_eq_none]; intro h; exact h a ha (by simp))
  | some a0 =>
    have h0 := List.mem_of_find?_eq_some hf
    have hk : a0.k = a.k := by simpa using List.find?_some hf
    simp only [Option.map_some, Option.getD_some]
    by_cases e : a0 = a
    · rw [e]
    · have := LinkStore.two_le_countP (fun x : AcctV => x.k == a.k) e (by simp [hk]) (by simp) h0 ha
      have := acct_unique hH T W a.k
      omega

/-- **`VPostOk` of the trie `others`** with the acct post streams. -/
theorem vpostOk_holds {cb : NearSpec.Bytes} {h : NearSpecV3.Hint} {p : NearSpecV3.Prep} {oh : Nat}
    {tr : Trace Fp} {r : V3Records} (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r) :
    VPostOk (othersBytes tr (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r) (fun i => toB (pnOf r.accts i)) := by
  have L := trieLink_of hp hsz hH T W
  apply vpostOk_of_N W.nodes W.values L.sha
  · refine ⟨fun i hi m hm a ha he => ?_, fun i x hx => ?_⟩
    · obtain ⟨a', ha', hk, j, hj, rfl⟩ := vpost_source hp hsz hH T W hi m hm a ha he
      obtain ⟨hpre, hpost, -, -⟩ := acct_wf W ha'
      rw [← hk, pnOf_eq hH T W ha']
      exact ⟨j, by simp only [List.length_append, List.length_drop]; omega, rfl⟩
    · unfold pnOf at hx
      cases hf : r.accts.find? (fun a => a.k == i) with
      | none => rw [hf] at hx; simp at hx
      | some a0 =>
        rw [hf] at hx
        simp only [Option.map_some, Option.getD_some, List.mem_append] at hx
        have hc := acct_canon W (List.mem_of_find?_eq_some hf)
        rcases hx with hx | hx
        · exact hc x (List.mem_append_right _ hx)
        · exact hc x (List.mem_append_left _ (List.mem_of_mem_drop hx))
  · intro i hi m hm a ha he
    obtain ⟨a', ha', hk, -⟩ := vpost_source hp hsz hH T W hi m hm a ha he
    obtain ⟨q, hq, l, pre, po, hv⟩ := acct_written hH T W ha'
    rw [hk] at hv
    have hl := hvpostLen_of hH T W q hq i l pre po hv
    simp only [toB, List.length_map] at hl
    exact ⟨q, hq, l, pre, po, hv, hl⟩

end LinkVPost

end ZkFormal.NearV3.Assembly
