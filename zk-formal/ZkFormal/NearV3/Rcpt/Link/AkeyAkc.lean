import ZkFormal.NearV3.Rcpt.Link.ValBytes
import ZkFormal.NearV3.Rcpt.Link.RcptHoldsB

/-!
# ZkFormal.NearV3.Rcpt.Link.AkeyAkc — the access-key half of `TrieOk.ak`

A gas refund to its own signer (`ee`) whose access-key walk ends at a value slot (`akf = 0`)
sends `AKC (akk, aku + 1)` and receives `AKC (akk, aku)`; the akey table sends `(vid, 0)` and
receives `(vid, U)` per record (only rcpt and akey use `AKC`).

* **`akc_akey`** — such a receipt's `akk` is the `vid` of an akey record.  Counting argument on
  the second components of the `AKC` messages with head `akk`: if no akey record has that vid, the
  balance gives `Σ ((aku+1) mod P) = Σ aku` over the `c ≥ 1` such receipts, i.e. `P·w = c` with
  `c ≤ 2^22 < P` — impossible;
* **`akey_byte`** — `VBYTES`: every akey byte is the byte of a value record with `vid` the akey's;
* **`akey_value`** — hence a value record with `vid = akk` whose 9 bytes are a `FullAccess` key
  (length 9, last byte `1`), byte-valued (`val_bytes8` under `ShaHyp` when it is referenced).
-/

namespace ZkFormal.NearV3.RcptLink

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.Near.Link
  ZkFormal.NearV3.Assembly

/-- The `AKC` send / receive of a receipt. -/
def akcFlag (x : RcptE) : Prop := x.ee = true ∧ x.akf = 0

instance (x : RcptE) : Decidable (akcFlag x) := by unfold akcFlag; infer_instance

def akcS (x : RcptE) : List Msg := if x.ee = true ∧ x.akf = 0 then [[x.akk, x.aku + 1]] else []
def akcR (x : RcptE) : List Msg := if x.ee = true ∧ x.akf = 0 then [[x.akk, x.aku]] else []

theorem located_flatMap {ls : RcptV3Vs} {j : Nat} (hj : j < ls.length) (F : RcptE → List Msg) :
    (located ls j).flatMap (fun (y : Nat × Nat × RcptE) => F y.2.2) = ls[j].rs.flatMap F := by
  simp only [located, getD_eq_getElem' ls default hj, List.flatMap_map]
  exact range_flatMap_getD F default ls[j].rs

theorem range_lists_flatMap (ls : RcptV3Vs) (F : RcptE → List Msg) :
    (List.range ls.length).flatMap (fun j => (located ls j).flatMap (fun (y : Nat × Nat × RcptE) => F y.2.2)) =
      (flatR ls).flatMap F := by
  rw [show (List.range ls.length).flatMap (fun j => (located ls j).flatMap
      (fun (y : Nat × Nat × RcptE) => F y.2.2)) =
      (List.range ls.length).flatMap (fun j => (ls.getD j default).rs.flatMap F) from
    ZkFormal.Near.Link.flatMap_congr' _ (fun j hj => by
      rw [located_flatMap (List.mem_range.mp hj), getD_eq_getElem' ls default (List.mem_range.mp hj)])]
  rw [range_flatMap_getD (fun L : ListV3 => L.rs.flatMap F) default ls, flatR, List.flatMap_assoc]

theorem rcpt_akc_sends (pub : List Fp) (ls : RcptV3Vs) :
    rcptSends3 pub ls B_AKC = (flatR ls).flatMap akcS := by
  rw [← range_lists_flatMap]
  unfold rcptSends3
  apply ZkFormal.Near.Link.flatMap_congr'
  intro j _
  simp only [show B_AKC ≠ B_BYTES by decide, show B_AKC ≠ B_RCL by decide, ite_false, List.nil_append]
  apply ZkFormal.Near.Link.flatMap_congr'
  intro y _
  simp [rSends, akcS, B_AKC, B_BYTES, B_KEYNIB, B_MEM, B_RIDS, B_MPOS, B_SREC]

theorem rcpt_akc_recvs (ls : RcptV3Vs) : rcptRecvs3 ls B_AKC = (flatR ls).flatMap akcR := by
  rw [← range_lists_flatMap]
  unfold rcptRecvs3
  apply ZkFormal.Near.Link.flatMap_congr'
  intro j _
  apply ZkFormal.Near.Link.flatMap_congr'
  intro y _
  simp [rRecvs, akcR, B_AKC, B_DIGEST, B_FINAL, B_MEM, B_SREC]

/-- Weight of an `AKC` message for head `k`: its second component. -/
def akcW (k : Nat) (m : List Fp) : Nat := if m.head? = some (Fp.ofNat k) then (m.getD 1 0).toNat else 0

/-- The counting identity over a list of receipts (all flagged `aku < P`). -/
theorem akc_count (k : Nat) : ∀ (Z : List RcptE), (∀ x ∈ Z, x.aku < P) →
    (((Z.flatMap akcS).map Msg.toFp).map (akcW k)).sum +
      P * (Z.filter fun x => decide (akcFlag x ∧ Fp.ofNat x.akk = Fp.ofNat k ∧ x.aku + 1 = P)).length =
    (((Z.flatMap akcR).map Msg.toFp).map (akcW k)).sum +
      (Z.filter fun x => decide (akcFlag x ∧ Fp.ofNat x.akk = Fp.ofNat k)).length
  | [], _ => by simp
  | x :: Z, hZ => by
    have ih := akc_count k Z (fun y hy => hZ y (by simp [hy]))
    have hx := hZ x (by simp)
    have key : (((akcS x).map Msg.toFp).map (akcW k)).sum +
        P * (if akcFlag x ∧ Fp.ofNat x.akk = Fp.ofNat k ∧ x.aku + 1 = P then 1 else 0) =
        (((akcR x).map Msg.toFp).map (akcW k)).sum +
        (if akcFlag x ∧ Fp.ofNat x.akk = Fp.ofNat k then 1 else 0) := by
      unfold akcS akcR akcFlag
      by_cases hf : x.ee = true ∧ x.akf = 0
      · rw [if_pos hf, if_pos hf]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, akcW, Msg.toFp,
          List.head?_cons, Option.some.injEq, List.getD_cons_succ, List.getD_cons_zero, Fp.toNat_ofNat]
        by_cases hk : Fp.ofNat x.akk = Fp.ofNat k
        · by_cases hw : x.aku + 1 = P
          · simp only [hk, hw, hf.1, hf.2, and_self, and_true, ite_true, Nat.mod_self, Nat.mod_eq_of_lt hx]
            omega
          · simp only [hk, hw, hf.1, hf.2, and_self, and_true, and_false, ite_true, ite_false, Nat.mod_eq_of_lt hx,
              Nat.mod_eq_of_lt (show x.aku + 1 < P by omega)]
            omega
        · simp only [hk, false_and, and_false, ite_false]
          omega
      · rw [if_neg hf, if_neg hf, if_neg (fun h => hf h.1), if_neg (fun h => hf h.1)]
        simp
    have lf : ∀ (q : RcptE → Prop) [DecidablePred q] (Z : List RcptE),
        ((x :: Z).filter fun y => decide (q y)).length = (if q x then 1 else 0) + (Z.filter fun y => decide (q y)).length := by
      intro q _ Z
      rw [List.filter_cons]
      by_cases hq : q x <;> simp [hq] <;> omega
    rw [lf (fun y => akcFlag y ∧ Fp.ofNat y.akk = Fp.ofNat k ∧ y.aku + 1 = P),
      lf (fun y => akcFlag y ∧ Fp.ofNat y.akk = Fp.ofNat k)]
    simp only [List.flatMap_cons, List.map_append, List.sum_append]
    rw [Nat.mul_add]
    omega

/-- **`akk` is an akey record's vid.** -/
theorem akc_akey {pub : List Fp} {tr : Trace Fp} {r : V3Records} (hH : HoldsP nearAirV3 pub tr)
    (T : V3RecordsTraffic pub tr r) (W : V3RecordsWf pub r) {x : RcptE} (hx : x ∈ flatR r.lists)
    (he : x.ee = true) (hf : x.akf = 0) : ∃ e ∈ r.akeys, e.vid = x.akk := by
  obtain ⟨toks, -, -, hwf, -⟩ := W.lists.toks
  have hsmall : ∀ y ∈ flatR r.lists, y.akk < P ∧ y.aku < P := by
    intro y hy
    obtain ⟨q, hq, rfl⟩ := List.getElem_of_mem hy
    have := (hwf q hq).small
    exact ⟨this.2.2.1, this.2.2.2.1⟩
  apply Classical.byContradiction
  intro hno
  have hno' : ∀ e ∈ r.akeys, Fp.ofNat e.vid ≠ Fp.ofNat x.akk := by
    intro e hem heq
    exact hno ⟨e, hem, Near.Link.ofNat_inj (W.akeys.canon e hem).1 (hsmall x hx).1 heq⟩
  -- the balance on `AKC` (users rcpt, akey)
  have hb : ∀ m : List Fp,
      ((rcptSends3 pub r.lists B_AKC).map Msg.toFp ++ (akeySends r.akeys B_AKC).map Msg.toFp).count m =
      ((rcptRecvs3 r.lists B_AKC).map Msg.toFp ++ (akeyRecvs r.akeys B_AKC).map Msg.toFp).count m := by
    intro m
    have h := bal_users hH (b := B_AKC) (U := [Assembly.T_RCPT, T_AKEY]) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) m
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at h
    rw [show isAt Assembly.T_RCPT = RcptV3.interactions from rfl, tcnt_of_traffic T.lists,
      tcnt_of_traffic T.lists, show isAt T_AKEY = AkeyV3.interactions from rfl,
      tcnt_of_traffic T.akeys, tcnt_of_traffic T.akeys] at h
    simp only [tcnt, ite_true, Bool.false_eq_true, ite_false, rcptTraffic3, akeyTraffic] at h
    simp only [List.count_append]
    exact h
  have hp := List.perm_iff_count.mpr hb
  have hs := (hp.map (akcW x.akk)).sum_nat
  rw [rcpt_akc_sends, rcpt_akc_recvs] at hs
  simp only [List.map_append, List.sum_append] at hs
  have a0 : (((akeySends r.akeys B_AKC).map Msg.toFp).map (akcW x.akk)).sum = 0 := by
    simp only [akeySends, show B_AKC ≠ B_VBYTES by decide, ite_false, ite_true, List.map_map]
    apply List.sum_eq_zero_iff_forall_eq_nat.mpr
    intro n hn
    obtain ⟨e, -, rfl⟩ := List.mem_map.mp hn
    simp [akcW, Msg.toFp]
  have a1 : (((akeyRecvs r.akeys B_AKC).map Msg.toFp).map (akcW x.akk)).sum = 0 := by
    simp only [akeyRecvs, ite_true, List.map_map]
    apply List.sum_eq_zero_iff_forall_eq_nat.mpr
    intro n hn
    obtain ⟨e, hem, rfl⟩ := List.mem_map.mp hn
    simp [akcW, Msg.toFp, hno' e hem]
  rw [a0, a1] at hs
  have hc := akc_count x.akk (flatR r.lists) (fun y hy => (hsmall y hy).2)
  have hpos : 0 < ((flatR r.lists).filter fun y => decide (akcFlag y ∧ Fp.ofNat y.akk = Fp.ofNat x.akk)).length :=
    List.length_pos_of_mem (List.mem_filter.mpr ⟨hx, by simp [akcFlag, he, hf]⟩)
  have hle := List.length_filter_le (fun y => decide (akcFlag y ∧ Fp.ofNat y.akk = Fp.ofNat x.akk)) (flatR r.lists)
  have hcnt := W.listsCount.2
  have hP : P = 2013265921 := rfl
  rw [hP] at hc
  omega

/-- **`VBYTES`**: every akey byte is the byte of a value record with the akey's vid. -/
theorem akey_byte {pub : List Fp} {tr : Trace Fp} {r : V3Records} (hH : HoldsP nearAirV3 pub tr)
    (T : V3RecordsTraffic pub tr r) (W : V3RecordsWf pub r) {e : AkeyE} (he : e ∈ r.akeys)
    {j : Nat} (hj : j < 9) :
    ∃ t, ∃ ht : t < r.values.length, r.values[t].vid = e.vid ∧
      e.bytes.getD j 0 = r.values[t].bytes.getD j 0 := by
  have hc := W.akeys.canon e he
  have hlen := W.akeys.len e he
  have hpj : e.bytes.getD j 0 < P := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    exact hc.2.2 _ (List.getElem_mem _)
  let M : Msg := [e.vid, j, e.bytes.getD j 0]
  have hb := bal_users hH (b := B_VBYTES) (U := [T_VAL, T_CODEC, Assembly.T_ACCT, T_AKEY, T_QV]) (by decide)
    (by decide) (by decide +kernel) (by decide +kernel) (Msg.toFp M)
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at hb
  rw [val_count T _ _ _ (by decide +kernel), val_count T _ _ _ (by decide +kernel),
    show isAt T_AKEY = AkeyV3.interactions from rfl, tcnt_of_traffic T.akeys, tcnt_of_traffic T.akeys,
    tableBusCount_noside (s := false) (is := isAt T_CODEC) (by decide +kernel),
    tableBusCount_noside (s := false) (is := isAt Assembly.T_ACCT) (by decide +kernel),
    tableBusCount_noside (s := false) (is := isAt T_QV) (by decide +kernel)] at hb
  have hs : 0 < tcnt (akeyTraffic r.akeys) true B_VBYTES (Msg.toFp M) := by
    simp only [tcnt, ite_true, akeyTraffic]
    apply List.count_pos_iff.mpr
    apply List.mem_map_of_mem
    simp only [akeySends, ite_true, List.mem_flatMap, List.mem_map, List.mem_range]
    exact ⟨e, he, j, hj, rfl⟩
  have r0 : tcnt (akeyTraffic r.akeys) false B_VBYTES (Msg.toFp M) = 0 := by
    simp [tcnt, akeyTraffic, akeyRecvs, B_VBYTES, B_AKC]
  have v0 : tcnt (valTraffic r.values) true B_VBYTES (Msg.toFp M) = 0 := by
    simp [tcnt, valTraffic, valSends, B_VBYTES, B_BYTES, B_ENT, B_SIZE]
  have hv : 0 < tcnt (valTraffic r.values) false B_VBYTES (Msg.toFp M) := by omega
  simp only [tcnt, Bool.false_eq_true, ite_false, valTraffic, valRecvs, ite_true] at hv
  obtain ⟨m, hm, hme⟩ := List.mem_map.mp (List.count_pos_iff.mp hv)
  obtain ⟨v, hv', hm⟩ := List.mem_flatMap.mp hm
  obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hv'
  split at hm
  · simp at hm
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
    have ce := W.values.canon _ hv'
    simp only [M, Msg.toFp, List.map_cons, List.map_nil, List.cons.injEq] at hme
    have e1 := Near.Link.ofNat_inj ce.1 hc.1 hme.1
    have hqP : q < P := by
      have := List.mem_range.mp hq; have := ZkFormal.NearV3.Link3.val_bytes_lt W.values ht
      unfold P; omega
    have e2 := Near.Link.ofNat_inj hqP (by unfold P; omega) hme.2.1
    subst e2
    have hbq : r.values[t].bytes.getD q 0 < P := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (List.mem_range.mp hq)]
      exact ce.2.2.2 _ (List.getElem_mem _)
    exact ⟨t, ht, e1, (Near.Link.ofNat_inj hbq hpj hme.2.2.1).symm⟩

/-- **The access-key value of a refund to its own signer**: its `akk` is the vid of an akey record
(a `FullAccess` key: 9 bytes, permission byte `1`) and the value record with that vid agrees with
it on the 9 bytes. -/
theorem akey_value {pub : List Fp} {tr : Trace Fp} {r : V3Records} (hH : HoldsP nearAirV3 pub tr)
    (T : V3RecordsTraffic pub tr r) (W : V3RecordsWf pub r) {x : RcptE} (hx : x ∈ flatR r.lists)
    (he : x.ee = true) (hf : x.akf = 0) :
    ∃ e ∈ r.akeys, e.vid = x.akk ∧ e.bytes.length = 9 ∧ e.bytes.getD 8 0 = 1 ∧
      ∃ t, ∃ ht : t < r.values.length, r.values[t].vid = x.akk ∧
        ∀ j, j < 9 → r.values[t].bytes.getD j 0 = e.bytes.getD j 0 := by
  obtain ⟨e, hem, hv⟩ := akc_akey hH T W hx he hf
  refine ⟨e, hem, hv, W.akeys.len e hem, W.akeys.last e hem, ?_⟩
  obtain ⟨t, ht, hvt, -⟩ := akey_byte hH T W hem (j := 0) (by decide)
  refine ⟨t, ht, hvt ▸ hv, fun j hj => ?_⟩
  obtain ⟨t', ht', hvt', hb⟩ := akey_byte hH T W hem hj
  have := ZkFormal.NearV3.Link3.vid_inj W.values (ZkFormal.NearV3.Link3.vlen_le W.values) ht ht'
    (by rw [hvt, hvt'])
  subst this
  exact hb.symm

end ZkFormal.NearV3.RcptLink
