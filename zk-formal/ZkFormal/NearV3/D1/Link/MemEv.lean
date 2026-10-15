import ZkFormal.NearV3.Rcpt.Link.Mem3

/-!
# `ZkFormal.NearV3.D1.Link.MemEv` — offline memory checking with inactive events (L1)

Lane `v3-d1-phase2`, item L1 (the run, `MEM` with the transaction ops).  D0a's `Rcpt/Link/Mem3`
for a timeline of events `rs : List RcptV` (event `r` writes at time `r + 1`) where only the
events with `act r` touch the memory.  In D1 the events are the `txV3` ops (time `op + 1`, active
iff the op reads the signer account, `s1`) followed by the incoming receipts (time `T0 + r + 1`).

The slot sequence is encoded for D0a's `lastW`: `kslA act rs r = 2·kslot + 1` for an active event,
`0` otherwise, so `lastW (kslA act rs) (2k + 1)` is the last write to slot `k`.

* `MemHypA`: the writes are a permutation of the reads, distinct account slots, and active reads
  are not in the future;
* **`tprev_eqA`**, **`tlast_eqA`**, **`mem_readA`**, **`mem_finalA`**: as `Mem3`'s.
-/

namespace ZkFormal.NearV3.D1.Link

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Link
open ZkFormal.NearV3.RcptLink (R aws ars rd_mem acct_eq_of_k nodup_range_map')

/-- The encoded slot of event `r` (`0` when inactive). -/
def kslA (act : Nat → Bool) (rs : List RcptV) (r : Nat) : Nat :=
  if act r then 2 * (R rs r).kslot + 1 else 0

theorem kslA_eq {act : Nat → Bool} {rs : List RcptV} {r k : Nat} :
    kslA act rs r = 2 * k + 1 ↔ act r = true ∧ (R rs r).kslot = k := by
  unfold kslA
  split <;> rename_i h <;> simp [h] <;> omega

def wrsA (act : Nat → Bool) (rs : List RcptV) : List Msg :=
  (List.range rs.length).flatMap fun r => if act r then (List.range 16).map (wrMsg (R rs r) r) else []
def rdsA (act : Nat → Bool) (rs : List RcptV) : List Msg :=
  (List.range rs.length).flatMap fun r => if act r then (List.range 16).map (rdMsg (R rs r)) else []

structure MemHypA (act : Nat → Bool) (rs : List RcptV) (as : List AcctV) : Prop where
  perm : (wrsA act rs ++ aws as).Perm (rdsA act rs ++ ars as)
  knd : (as.map (·.k)).Nodup
  tle : ∀ r, r < rs.length → act r = true → (R rs r).tprev ≤ rs.length → (R rs r).tprev ≤ r

theorem mem_WA {act : Nat → Bool} {rs : List RcptV} {as : List AcctV} {m : Msg} :
    m ∈ wrsA act rs ++ aws as ↔
      (∃ r, r < rs.length ∧ act r = true ∧ ∃ i, i < 16 ∧ m = wrMsg (R rs r) r i) ∨
      (∃ a ∈ as, ∃ i, i < 16 ∧ m = awMsg a i) := by
  simp only [wrsA, aws, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range]
  constructor
  · rintro (⟨r, hr, hm⟩ | ⟨a, ha, i, hi, rfl⟩)
    · split at hm
      · next hact =>
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hm
        exact .inl ⟨r, hr, hact, i, List.mem_range.mp hi, rfl⟩
      · simp at hm
    · exact .inr ⟨a, ha, i, hi, rfl⟩
  · rintro (⟨r, hr, hact, i, hi, rfl⟩ | ⟨a, ha, i, hi, rfl⟩)
    · exact .inl ⟨r, hr, by simp only [hact, ite_true]; exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩⟩
    · exact .inr ⟨a, ha, i, hi, rfl⟩

theorem rd_memA {act : Nat → Bool} {rs : List RcptV} {as : List AcctV} {r i : Nat} (hr : r < rs.length)
    (hact : act r = true) (hi : i < 16) : rdMsg (R rs r) i ∈ rdsA act rs ++ ars as := by
  simp only [rdsA, List.mem_append, List.mem_flatMap, List.mem_range]
  exact .inl ⟨r, hr, by simp only [hact, ite_true]; exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩⟩

theorem ar_memA {act : Nat → Bool} {rs : List RcptV} {as : List AcctV} {a : AcctV} (ha : a ∈ as) {i : Nat}
    (hi : i < 16) : arMsg a i ∈ rdsA act rs ++ ars as := by
  simp only [ars, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range]
  exact .inr ⟨a, ha, i, hi, rfl⟩

theorem W_nodupA {act : Nat → Bool} {rs : List RcptV} {as : List AcctV} (hk : (as.map (·.k)).Nodup) :
    (wrsA act rs ++ aws as).Nodup := by
  rw [List.nodup_append]
  refine ⟨?_, ?_, ?_⟩
  · apply Sound.nodup_flatMap_of
    · intro r _
      split
      · exact nodup_range_map' _ (fun i j h => by simp [wrMsg] at h; exact h.1) 16
      · exact List.nodup_nil
    · intro i j a b x hij ha hb hxa hxb
      have e1 : a = i := by
        have := List.getElem?_eq_some_iff.mp ha; simp at this; omega
      have e2 : b = j := by
        have := List.getElem?_eq_some_iff.mp hb; simp at this; omega
      subst e1 e2
      split at hxa
      · split at hxb
        · obtain ⟨i1, -, rfl⟩ := List.mem_map.mp hxa
          obtain ⟨i2, -, he⟩ := List.mem_map.mp hxb
          simp only [wrMsg, List.cons.injEq] at he
          exact hij (by omega)
        · simp at hxb
      · simp at hxa
  · apply Sound.nodup_flatMap_of
    · intro a _; exact nodup_range_map' _ (fun i j h => by simp [awMsg] at h; exact h.1) 16
    · intro i j a b x hij ha hb hxa hxb
      simp only [List.mem_map, List.mem_range] at hxa hxb
      obtain ⟨i1, -, rfl⟩ := hxa
      obtain ⟨i2, -, he⟩ := hxb
      simp only [awMsg, List.cons_append, List.cons.injEq] at he
      have hai := List.mem_of_getElem? ha
      have hbj := List.mem_of_getElem? hb
      have hab := acct_eq_of_k hk hbj hai he.1
      subst hab
      have hlen : i < as.length := (List.getElem?_eq_some_iff.mp ha).1
      have hm : (as.map (·.k))[i]? = (as.map (·.k))[j]? := by simp [ha, hb]
      exact hij ((List.Nodup.getElem?_inj (by simpa using hlen) hk).mp hm)
  · intro x hx y hy hxy
    subst hxy
    rcases (mem_WA (as := []) (act := act) (rs := rs)).mp (List.mem_append_left _ hx) with ⟨r, -, -, i, -, rfl⟩ | ⟨a, ha, -⟩
    · simp only [aws, List.mem_flatMap, List.mem_map, List.mem_range] at hy
      obtain ⟨a, -, i', -, he⟩ := hy
      simp [wrMsg, awMsg] at he
    · cases ha

section Hyp
variable {act : Nat → Bool} {rs : List RcptV} {as : List AcctV} (h : MemHypA act rs as)
include h

theorem R_nodupA : (rdsA act rs ++ ars as).Nodup := h.perm.nodup_iff.mp (W_nodupA h.knd)

theorem read_in_WA {m : Msg} (hm : m ∈ rdsA act rs ++ ars as) : m ∈ wrsA act rs ++ aws as :=
  h.perm.mem_iff.mpr hm

theorem W_keyA {m₁ m₂ : Msg} (h₁ : m₁ ∈ wrsA act rs ++ aws as) (h₂ : m₂ ∈ wrsA act rs ++ aws as)
    (hk : m₁.take 3 = m₂.take 3) : m₁ = m₂ := by
  rcases mem_WA.mp h₁ with ⟨r, hr, -, i, hi, rfl⟩ | ⟨a, ha, i, hi, rfl⟩ <;>
  rcases mem_WA.mp h₂ with ⟨r', hr', -, i', hi', rfl⟩ | ⟨a', ha', i', hi', rfl⟩
  · simp only [wrMsg, List.take, List.cons.injEq, and_true] at hk
    obtain ⟨-, e1, rfl⟩ := hk
    have : r = r' := by omega
    subst this; rfl
  · simp [wrMsg, awMsg, List.take] at hk
  · simp [wrMsg, awMsg, acctLane, List.take] at hk
  · simp only [awMsg, acctLane, List.cons_append, List.take, List.cons.injEq, and_true] at hk
    obtain ⟨e1, -, rfl⟩ := hk
    have := acct_eq_of_k h.knd ha ha' e1
    subst this; rfl

theorem rd_neA {r r' : Nat} (hr : r < rs.length) (hr' : r' < rs.length) (ha : act r = true)
    (ha' : act r' = true) (hne : r ≠ r') : rdMsg (R rs r) 0 ≠ rdMsg (R rs r') 0 := by
  intro he
  have hnd := R_nodupA h
  rw [List.nodup_append] at hnd
  have := Sound.flatMap_disj
    (fun q => if act q then (List.range 16).map (rdMsg (R rs q)) else [])
    (List.range rs.length) r r' r r' (rdMsg (R rs r) 0) hnd.1 hne
    (by simp [hr]) (by simp [hr']) (by simp only [ha, ite_true]; exact List.mem_map.mpr ⟨0, by simp, rfl⟩)
  exact this (by simp only [ha', ite_true]; exact List.mem_map.mpr ⟨0, by simp, he.symm⟩)

theorem rd_ne_arA {r : Nat} (hr : r < rs.length) (hact : act r = true) {a : AcctV} (ha : a ∈ as) :
    rdMsg (R rs r) 0 ≠ arMsg a 0 := by
  intro he
  have hnd := R_nodupA h
  rw [List.nodup_append] at hnd
  refine hnd.2.2 _ ?_ _ ?_ he
  · simp only [rdsA, List.mem_flatMap, List.mem_range]
    exact ⟨r, hr, by simp only [hact, ite_true]; exact List.mem_map.mpr ⟨0, by simp, rfl⟩⟩
  · simp only [ars, List.mem_flatMap, List.mem_map, List.mem_range]
    exact ⟨a, ha, 0, by decide, rfl⟩

omit h in
/-- A write time of slot `k`: `0`, or `r' + 1` for an active event `r'` writing `k`. -/
theorem read_timeA {k t : Nat} {m : Msg} (hm : m ∈ wrsA act rs ++ aws as) (hk : m.take 3 = [k, t, 0]) :
    t = 0 ∨ (∃ r', r' < rs.length ∧ kslA act rs r' = 2 * k + 1 ∧ t = r' + 1) := by
  rcases mem_WA.mp hm with ⟨r, hr, hact, i, hi, rfl⟩ | ⟨a, ha, i, hi, rfl⟩
  · simp only [wrMsg, List.take, List.cons.injEq, and_true] at hk
    exact .inr ⟨r, hr, kslA_eq.mpr ⟨hact, hk.1⟩, hk.2.1.symm⟩
  · simp only [awMsg, acctLane, List.cons_append, List.take, List.cons.injEq, and_true] at hk
    exact .inl hk.2.1.symm

/-- **Each active event reads the last earlier write of its slot.** -/
theorem tprev_eqA : ∀ r, r < rs.length → act r = true →
    (R rs r).tprev = lastW (kslA act rs) (2 * (R rs r).kslot + 1) r := by
  intro r
  induction r using Nat.strongRecOn with
  | _ r ih =>
    intro hr hact
    have hin := read_in_WA h (rd_memA (as := as) hr hact (i := 0) (by decide))
    have htime := read_timeA hin (k := (R rs r).kslot) (t := (R rs r).tprev) rfl
    have hle := h.tle r hr hact (by rcases htime with e | ⟨r', hr', -, e⟩ <;> omega)
    have htL : (R rs r).tprev ≤ lastW (kslA act rs) (2 * (R rs r).kslot + 1) r := by
      rcases htime with e | ⟨r', hr', hk, e⟩
      · omega
      · rw [e]; exact le_lastW _ _ r r' (by omega) hk
    apply Classical.byContradiction; intro hne
    have hlt' : (R rs r).tprev < lastW (kslA act rs) (2 * (R rs r).kslot + 1) r := Nat.lt_of_le_of_ne htL hne
    rcases lastW_cases (kslA act rs) (2 * (R rs r).kslot + 1) r with e | ⟨r0, hr0, hk0, e⟩
    · omega
    obtain ⟨r1, e1, e2, e3, e4⟩ := exists_first (kslA act rs) (2 * (R rs r).kslot + 1) (R rs r).tprev r0
      (by omega) hk0
    have hr1 : r1 < rs.length := by omega
    obtain ⟨hact1, hk1⟩ := kslA_eq.mp e3
    have hL1 : lastW (kslA act rs) (2 * (R rs r).kslot + 1) r1 = (R rs r).tprev := by
      apply lastW_eq_of _ _ _ r1 e1 e4
      rcases htime with e | ⟨r', -, hk, e⟩
      · exact .inl e
      · exact .inr ⟨by omega, by rw [e]; exact hk⟩
    have ht1 : (R rs r1).tprev = (R rs r).tprev := by
      rw [ih r1 (by omega) hr1 hact1, hk1, hL1]
    have hin1 := read_in_WA h (rd_memA (as := as) hr1 hact1 (i := 0) (by decide))
    have hkey : (rdMsg (R rs r) 0).take 3 = (rdMsg (R rs r1) 0).take 3 := by
      simp only [rdMsg, List.take]
      rw [ht1, hk1]
    exact rd_neA h hr hr1 hact hact1 (by omega) (W_keyA h hin hin1 hkey)

/-- **The acct table's final read gets the last write.** -/
theorem tlast_eqA {a : AcctV} (ha : a ∈ as) : a.tlast = lastW (kslA act rs) (2 * a.k + 1) rs.length := by
  have hin := read_in_WA h (ar_memA (act := act) (rs := rs) ha (i := 0) (by decide))
  have htime := read_timeA hin (k := a.k) (t := a.tlast) (by simp [arMsg, acctLane, List.take])
  have htL : a.tlast ≤ lastW (kslA act rs) (2 * a.k + 1) rs.length := by
    rcases htime with e | ⟨r', hr', hk, e⟩
    · omega
    · rw [e]; exact le_lastW _ _ _ r' hr' hk
  apply Classical.byContradiction; intro hne
  have hlt' := Nat.lt_of_le_of_ne htL hne
  rcases lastW_cases (kslA act rs) (2 * a.k + 1) rs.length with e | ⟨r0, hr0, hk0, e⟩
  · omega
  obtain ⟨r1, e1, e2, e3, e4⟩ := exists_first (kslA act rs) (2 * a.k + 1) a.tlast r0 (by omega) hk0
  have hr1 : r1 < rs.length := by omega
  obtain ⟨hact1, hk1⟩ := kslA_eq.mp e3
  have hL1 : lastW (kslA act rs) (2 * a.k + 1) r1 = a.tlast := by
    apply lastW_eq_of _ _ _ r1 e1 e4
    rcases htime with e | ⟨r', -, hk, e⟩
    · exact .inl e
    · exact .inr ⟨by omega, by rw [e]; exact hk⟩
  have ht1 : (R rs r1).tprev = a.tlast := by
    rw [tprev_eqA h r1 hr1 hact1, hk1, hL1]
  have hin1 := read_in_WA h (rd_memA (as := as) hr1 hact1 (i := 0) (by decide))
  have hkey : (rdMsg (R rs r1) 0).take 3 = (arMsg a 0).take 3 := by
    simp only [rdMsg, arMsg, acctLane, List.cons_append, List.take]
    rw [ht1, hk1]
  exact rd_ne_arA h hr1 hact1 ha (W_keyA h hin1 hin hkey)

/-- The payload of an active event's read. -/
theorem mem_readA {r : Nat} (hr : r < rs.length) (hact : act r = true) {i : Nat} (hi : i < 16) :
    (lastW (kslA act rs) (2 * (R rs r).kslot + 1) r = 0 →
      ∃ a ∈ as, a.k = (R rs r).kslot ∧ rdMsg (R rs r) i = awMsg a i) ∧
    (∀ r0, lastW (kslA act rs) (2 * (R rs r).kslot + 1) r = r0 + 1 →
      r0 < r ∧ act r0 = true ∧ (R rs r0).kslot = (R rs r).kslot ∧ rdMsg (R rs r) i = wrMsg (R rs r0) r0 i) := by
  have hin := read_in_WA h (rd_memA (as := as) hr hact hi)
  have ht := tprev_eqA h r hr hact
  refine ⟨fun hL => ?_, fun r0 hL => ?_⟩
  · rcases mem_WA.mp hin with ⟨r', hr', -, i', hi', he⟩ | ⟨a, ha, i', hi', he⟩
    · simp only [rdMsg, wrMsg, List.cons.injEq] at he; omega
    · refine ⟨a, ha, ?_, ?_⟩
      · simp only [rdMsg, awMsg, List.cons_append, List.cons.injEq] at he; exact he.1.symm
      · rw [he]; simp only [rdMsg, awMsg, List.cons_append, List.cons.injEq] at he; rw [he.2.2.1]
  · rcases mem_WA.mp hin with ⟨r', hr', hact', i', hi', he⟩ | ⟨a, ha, i', hi', he⟩
    · have he' := he
      simp only [rdMsg, wrMsg, List.cons.injEq] at he'
      have : r' = r0 := by omega
      subst this
      have hle := lastW_le (kslA act rs) (2 * (R rs r).kslot + 1) r
      refine ⟨by omega, hact', he'.1.symm, ?_⟩
      rw [he, he'.2.2.1]
    · simp only [rdMsg, awMsg, List.cons_append, List.cons.injEq] at he; omega

/-- The payload of the acct table's final read. -/
theorem mem_finalA {a : AcctV} (ha : a ∈ as) {i : Nat} (hi : i < 16) :
    (lastW (kslA act rs) (2 * a.k + 1) rs.length = 0 → arMsg a i = awMsg a i) ∧
    (∀ r0, lastW (kslA act rs) (2 * a.k + 1) rs.length = r0 + 1 →
      r0 < rs.length ∧ act r0 = true ∧ (R rs r0).kslot = a.k ∧ arMsg a i = wrMsg (R rs r0) r0 i) := by
  have hin := read_in_WA h (ar_memA (act := act) (rs := rs) ha hi)
  have ht := tlast_eqA h ha
  refine ⟨fun hL => ?_, fun r0 hL => ?_⟩
  · rcases mem_WA.mp hin with ⟨r', hr', -, i', hi', he⟩ | ⟨b, hb, i', hi', he⟩
    · simp only [arMsg, wrMsg, acctLane, List.cons_append, List.cons.injEq] at he; omega
    · have hk : a.k = b.k := by
        simp only [arMsg, awMsg, acctLane, List.cons_append, List.cons.injEq] at he; exact he.1
      have := acct_eq_of_k h.knd ha hb hk
      subst this
      rw [he]; simp only [arMsg, awMsg, acctLane, List.cons_append, List.cons.injEq] at he
      rw [he.2.2.1]
  · rcases mem_WA.mp hin with ⟨r', hr', hact', i', hi', he⟩ | ⟨b, hb, i', hi', he⟩
    · have he' := he
      simp only [arMsg, wrMsg, acctLane, List.cons_append, List.cons.injEq] at he'
      have : r' = r0 := by omega
      subst this
      refine ⟨hr', hact', he'.1.symm, ?_⟩
      rw [he, he'.2.2.1]
    · simp only [arMsg, awMsg, acctLane, List.cons_append, List.cons.injEq] at he; omega

end Hyp

end ZkFormal.NearV3.D1.Link
