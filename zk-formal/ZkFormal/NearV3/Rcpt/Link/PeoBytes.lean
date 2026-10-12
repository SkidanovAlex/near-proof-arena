import ZkFormal.NearV3.Assembly.LinkRidBytes

/-!
# ZkFormal.NearV3.Rcpt.Link.PeoBytes — the `PEO` preimages are bytes (closes `burntB`)

Every receipt `q` (global index) of the receipt view sends its `PEO` preimage as
`BYTES (msgId K_PEO q, k, peo_k)` and receives `DIGEST digMsg (msgId K_PEO q) |peo| peoh`.  The
digest is provided by the SHA union (`digest_provided`); `peo_isolate` shows that the only
receipt `BYTES` messages with that id are the `PEO` stream of receipt `q`, and the other senders
(`othersRC`) never use kind `K_PEO`.  `sha_core` then makes `peo` byte-valued; `burnt ⊆ peo`.

* `located_flat` — a located receipt is `(flatR ls)[q]`;
* `peo_isolate` — `PEO` stream isolation in `rcptSends3`;
* `othersRC_kind` — the other `BYTES` senders never use kind `K_PEO` / `K_RF` / `K_RID`;
* **`peoBytes`**, **`burntBytes`** — from `HoldsP` (+ `prepD0` for the codec registry).
-/

namespace ZkFormal.NearV3.RcptLink

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.Near.Link
  ZkFormal.NearV3.Assembly

theorem length_flatMap_take (ls : RcptV3Vs) (j : Nat) :
    ((ls.take j).flatMap (·.rs)).length = baseR ls j := by
  simp [baseR, List.length_flatMap]

/-- A located receipt is the flattened receipt at its global index. -/
theorem located_flat {ls : RcptV3Vs} {j q o : Nat} {x : RcptE} (hj : j < ls.length)
    (h : (q, o, x) ∈ located ls j) :
    ∃ hq : q < (flatR ls).length, (flatR ls)[q] = x := by
  simp only [located, List.mem_map, List.mem_range] at h
  obtain ⟨k, hk, he⟩ := h
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, -, rfl⟩ := he
  rw [getD_eq_getElem' ls default hj] at hk ⊢
  have hsplit : flatR ls = (ls.take j).flatMap (·.rs) ++ (ls[j].rs ++ (ls.drop (j + 1)).flatMap (·.rs)) := by
    conv => lhs; rw [flatR, ← List.take_append_drop j ls]
    rw [List.flatMap_append, List.drop_eq_getElem_cons hj, List.flatMap_cons]
  have hlen : baseR ls j + k < (flatR ls).length := by
    rw [hsplit]; simp only [List.length_append, length_flatMap_take]; omega
  refine ⟨hlen, ?_⟩
  rw [getD_eq_getElem' _ default hk]
  simp only [hsplit]
  rw [List.getElem_append_right (by rw [length_flatMap_take]; omega)]
  simp only [length_flatMap_take, Nat.add_sub_cancel_left]
  rw [List.getElem_append_left hk]

/-- Of a receipt's byte streams, only its `PEO` stream has kind `K_PEO`. -/
theorem receipt_sends_peo {pub : List Fp} {xs : List RcptE} {j r off a : Nat} {x : RcptE} {m : Msg}
    (hm : m ∈ rSends pub xs j r off x B_BYTES) (ha : m.head? = some a) (hk : a % 16 = K_PEO) :
    m ∈ emitAt (msgId K_PEO r) 0 x.peo := by
  simp only [rSends, ite_true, List.mem_append] at hm
  rcases hm with (((hm | hm) | hm) | hm) | hm
  · have hh := emitAt_head_eq hm ha
    subst a
    simp [msgId, K_PEO, K_RC, Nat.add_mod] at hk
  · split at hm
    · have hh := emitAt_head_eq hm ha
      subst a
      simp [K_RF, K_PEO] at hk
    · simp at hm
  · exact hm
  · have hh := emitAt_head_eq hm ha
    subst a
    simp [msgId, K_LEAF, K_PEO, Nat.add_mod] at hk
  · split at hm
    · have hh := emitAt_head_eq hm ha
      subst a
      simp [msgId, K_RID, K_PEO, Nat.add_mod] at hk
    · simp at hm

/-- **`PEO` isolation**: the receipt `BYTES` messages with id `msgId K_PEO q` are exactly the
`PEO` stream of receipt `q`. -/
theorem peo_isolate {pub : List Fp} {ls : RcptV3Vs} {q : Nat} {m : Msg}
    (hm : m ∈ rcptSends3 pub ls B_BYTES) (ha : m.head? = some (msgId K_PEO q)) :
    ∃ hq : q < (flatR ls).length, ∃ k, k < (flatR ls)[q].peo.length ∧
      m = [msgId K_PEO q, k, (flatR ls)[q].peo.getD k 0] := by
  simp only [rcptSends3, ite_true, show B_BYTES ≠ B_RCL by decide, ite_false, List.append_nil] at hm
  obtain ⟨j, hj, hm⟩ := List.mem_flatMap.mp hm
  have hj := List.mem_range.mp hj
  rcases List.mem_append.mp hm with hm | hm
  · have hid := emitAt_head_eq hm ha
    exfalso; unfold msgId K_RC K_PEO at hid; omega
  · obtain ⟨⟨r, off, x⟩, hpos, hm⟩ := List.mem_flatMap.mp hm
    have hm := receipt_sends_peo hm ha (by simp [msgId, K_PEO, Nat.add_mod])
    have hid := emitAt_head_eq hm ha
    have hrq : r = q := by unfold msgId at hid; omega
    subst hrq
    obtain ⟨hq, hx⟩ := located_flat hj hpos
    refine ⟨hq, ?_⟩
    rw [hx]
    obtain ⟨k, hk, rfl⟩ := ZkFormal.NearV3.Link3.mem_emitAt3.mp hm
    exact ⟨k, hk, by simp⟩

/-- No other `BYTES` sender uses an id of a receipt-stream kind `K_PEO`, `K_RF` or `K_RID`. -/
theorem othersRC_kind {K : Nat} (hK : K = K_PEO ∨ K = K_RF ∨ K = K_RID) {cb : NearSpec.Bytes} {h : NearSpecV3.Hint} {p : NearSpecV3.Prep} {oh : Nat}
    {tr : Trace Fp} {r : V3Records} (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r) :
    ∀ m ∈ LinkRidBytes.othersRC tr (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r, ∀ a,
      m.head? = some a → a < P ∧ a % 16 ≠ K := by
  have kin : ∀ {K' : Nat} {x : Msg}, KindIn [K'] x → K' ≠ K → ∀ a, x.head? = some a →
      a < P ∧ a % 16 ≠ K := by
    intro K' x hk hK' a ha
    obtain ⟨h1, h2⟩ := hk a ha
    rw [List.mem_singleton] at h2
    exact ⟨h1, h2 ▸ hK'⟩
  have nv : ∀ {K' n : Nat}, (K' = K_NPRE ∨ K' = K_NPOST ∨ K' = K_VPRE) → n < 2 ^ 22 →
      msgId K' n < P ∧ msgId K' n % 16 ≠ K := by
    intro K' n hK' hn
    unfold msgId P
    rcases hK with rfl | rfl | rfl <;>
    rcases hK' with rfl | rfl | rfl <;> simp only [K_NPRE, K_NPOST, K_VPRE, K_PEO, K_RF, K_RID] <;> omega
  intro m hm a ha
  simp only [LinkRidBytes.othersRC, List.mem_append] at hm
  rcases hm with (((((hm | hm) | hm) | hm) | hm) | hm) | hm
  · obtain ⟨K, n, hh, hK, hn⟩ := nodeVal_bytes_head W.nodes W.values (List.mem_append_left _ hm)
    rw [ha, Option.some.injEq] at hh; subst hh
    exact nv hK hn
  · obtain ⟨K, n, hh, hK, hn⟩ := nodeVal_bytes_head W.nodes W.values (List.mem_append_right _ hm)
    rw [ha, Option.some.injEq] at hh; subst hh
    exact nv hK hn
  · exact kin (upsKindIn_of hp hsz hH T W m hm) (by rcases hK with rfl | rfl | rfl <;> decide) a ha
  · exact kin (acctKindIn hH T W m hm) (by rcases hK with rfl | rfl | rfl <;> decide) a ha
  · exact kin (ddKindIn W.srcp m hm) (by rcases hK with rfl | rfl | rfl <;> decide) a ha
  · exact kin (mrkKindIn W (pubNat_pubOf_lt _) m hm) (by rcases hK with rfl | rfl | rfl <;> decide) a ha
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hm
    cases hyh : y.head? with
    | none => simp [List.head?_map, hyh] at ha
    | some e =>
      simp only [List.head?_map, hyh, Option.map_some, Option.some.injEq] at ha
      subst ha
      have := codecKindIn hp hsz hH y hy e hyh
      exact ⟨Fp.toNat_lt e, by rw [this]; rcases hK with rfl | rfl | rfl <;> decide⟩

/-- The `PEO` preimage values are raw (canonical) or bytes. -/
theorem receipt_peo_values {x : RcptE} {r tok tok' : Nat} {gp : List Nat}
    (w : x.Wf r gp tok tok') : RawOrByte x.toRcptV x.peo := by
  obtain ⟨-, hv, -, -⟩ := w.ids
  have hv := (valid_length hv).2
  simp only [toBytes_length] at hv
  unfold RcptV.peo
  cases x.hr <;> simp only [Bool.false_eq_true, ite_true, ite_false] <;> rob

/-- **`PEO` preimages are bytes.** -/
theorem peoBytes {cb : NearSpec.Bytes} {h : NearSpecV3.Hint} {p : NearSpecV3.Prep} {oh : Nat}
    {tr : Trace Fp} {r : V3Records} (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r) :
    ∀ x ∈ flatR r.lists, Bytes8 x.peo := by
  intro x hx
  obtain ⟨L, hL, hxL⟩ := List.mem_flatMap.mp hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hL
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hxL
  have hloc : (baseR r.lists j + k, lOffs r.lists[j].rs k, r.lists[j].rs[k]) ∈ located r.lists j := by
    simp only [located, getD_eq_getElem' r.lists default hj, List.mem_map, List.mem_range]
    exact ⟨k, hk, by rw [getD_eq_getElem' _ default hk]⟩
  obtain ⟨hq, hxq⟩ := located_flat hj hloc
  generalize hxe : r.lists[j].rs[k] = x at hloc hxq
  generalize hqe : baseR r.lists j + k = q at hloc hq hxq
  have hcnt := W.listsCount
  -- the digest receive
  have hdig : 0 < shaU tr (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) true B_DIGEST
      (digMsg (msgId K_PEO q) x.peo.length x.peoh).toFp := by
    apply digest_provided hH (t := Assembly.T_RCPT) (by decide)
    rw [show isAt Assembly.T_RCPT = RcptV3.interactions from rfl, tcnt_of_traffic T.lists]
    simp only [tcnt, Bool.false_eq_true, ite_false, rcptTraffic3]
    apply List.count_pos_iff.mpr
    apply List.mem_map_of_mem
    simp only [rcptRecvs3, List.mem_flatMap, List.mem_range]
    refine ⟨j, hj, _, hloc, ?_⟩
    simp [rRecvs]
  have hsha := LinkRidBytes.shaFacts_cover (shaU_facts hH) _ (LinkRidBytes.sha_le_rc hH T)
  obtain ⟨toks, -, -, hwf, -⟩ := W.lists.toks
  have hw := hwf q hq
  rw [hxq] at hw
  have hxm : x ∈ flatR r.lists := hxq ▸ List.getElem_mem hq
  have hid : msgId K_PEO q < P := by unfold msgId K_PEO P; omega
  have hcan : ∀ y ∈ x.raw3, y < P := W.lists.canon.2 x hxm
  have hpeoc : ∀ y ∈ x.peo, y < P := by
    intro y hy
    rcases receipt_peo_values hw y hy with hy | hy
    · exact hcan y (by simp [RcptE.raw3, hy])
    · unfold P; omega
  have hplen : x.peo.length < P := by
    have := (Rcpt.Candidates.receipt_sha_lengths
      (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) _ hw).2.1
    unfold P; omega
  refine (sha_core hsha _ (fun m => rfl) hid hpeoc hplen
    (fun y hy => hcan y (by simp [RcptE.raw3, RcptV.raw, hy])) ?_ hdig).1
  intro m hm a ha he
  rcases List.mem_append.mp hm with hm | hm
  · have hc := receipt_bytes_ids hcnt.1 hcnt.2 hm ha
    have heq := Near.Link.ofNat_inj hc hid he
    subst a
    obtain ⟨hq', k', hk', rfl⟩ := peo_isolate hm ha
    simp only [hxq] at hk' ⊢
    exact ⟨k', hk', rfl⟩
  · have hh := othersRC_kind (Or.inl rfl) hp hsz hH T W m hm a ha
    have heq := Near.Link.ofNat_inj hh.1 hid he
    have hk : msgId K_PEO q % 16 = K_PEO := by simp [msgId, K_PEO, Nat.add_mod]
    exact False.elim (hh.2 (heq ▸ hk))

/-- **`burntB`**: the burnt amounts are bytes (`burnt ⊆ peo`). -/
theorem burntBytes {cb : NearSpec.Bytes} {h : NearSpecV3.Hint} {p : NearSpecV3.Prep} {oh : Nat}
    {tr : Trace Fp} {r : V3Records} (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r) :
    ∀ x ∈ flatR r.lists, Bytes8 x.burnt := by
  intro x hx y hy
  exact peoBytes hp hsz hH T W x hx y (by unfold RcptV.peo; simp [hy])

end ZkFormal.NearV3.RcptLink
