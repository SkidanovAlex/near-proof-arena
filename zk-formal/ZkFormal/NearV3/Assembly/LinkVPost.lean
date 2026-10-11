import ZkFormal.NearV3.Assembly.LinkUps

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

end LinkVPost

end ZkFormal.NearV3.Assembly
