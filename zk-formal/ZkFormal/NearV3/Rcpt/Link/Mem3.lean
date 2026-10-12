import ZkFormal.NearV3.Rcpt.Link.MemBal
import ZkFormal.Near.Link.MemTime
import ZkFormal.Near.Spec.SoundShape

/-!
# ZkFormal.NearV3.Rcpt.Link.Mem3 — offline memory checking on `MEM` (v3 records)

v1's `Near.Link.Mem` argument, restated over an abstract hypothesis bundle `MemHyp rs as`
(receipts `rs : List RcptV` in applied order, account records `as`):

* `perm` — the `MEM` writes are a permutation of the reads (as natural messages);
* `knd` — the account slots are distinct;
* `tle` — a receipt's read time is at most its index once it is at most the receipt count
  (`RcptE.Wf.tprev_le` with `|rs| ≤ 2^22`).

Conclusions (`R r := rs.getD r default`, `lastW` from `Near.Link.MemTime`):

* **`tprev_eq`** — each receipt reads the last earlier write of its slot;
* **`tlast_eq`** — the acct table's final read is the last write of the slot;
* **`mem_read`**, **`mem_final`** — the payloads agree with that write (an earlier receipt's
  `aft`/`lk`/`st` lanes, or the acct record's opening lanes).
-/

namespace ZkFormal.NearV3.RcptLink

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Link

/-- Receipt `r` (default out of range). -/
abbrev R (rs : List RcptV) (r : Nat) : RcptV := rs.getD r default

def wrs (rs : List RcptV) : List Msg :=
  (List.range rs.length).flatMap fun r => (List.range 16).map (wrMsg (R rs r) r)
def rds (rs : List RcptV) : List Msg :=
  (List.range rs.length).flatMap fun r => (List.range 16).map (rdMsg (R rs r))
def aws (as : List AcctV) : List Msg := as.flatMap fun a => (List.range 16).map (awMsg a)
def ars (as : List AcctV) : List Msg := as.flatMap fun a => (List.range 16).map (arMsg a)

structure MemHyp (rs : List RcptV) (as : List AcctV) : Prop where
  perm : (wrs rs ++ aws as).Perm (rds rs ++ ars as)
  knd : (as.map (·.k)).Nodup
  tle : ∀ r, r < rs.length → (R rs r).tprev ≤ rs.length → (R rs r).tprev ≤ r

theorem mem_W {rs : List RcptV} {as : List AcctV} {m : Msg} :
    m ∈ wrs rs ++ aws as ↔
      (∃ r, r < rs.length ∧ ∃ i, i < 16 ∧ m = wrMsg (R rs r) r i) ∨
      (∃ a ∈ as, ∃ i, i < 16 ∧ m = awMsg a i) := by
  simp only [wrs, aws, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range]
  constructor
  · rintro (⟨r, hr, i, hi, rfl⟩ | ⟨a, ha, i, hi, rfl⟩)
    · exact .inl ⟨r, hr, i, hi, rfl⟩
    · exact .inr ⟨a, ha, i, hi, rfl⟩
  · rintro (⟨r, hr, i, hi, rfl⟩ | ⟨a, ha, i, hi, rfl⟩)
    · exact .inl ⟨r, hr, i, hi, rfl⟩
    · exact .inr ⟨a, ha, i, hi, rfl⟩

theorem rd_mem {rs : List RcptV} {as : List AcctV} {r i : Nat} (hr : r < rs.length) (hi : i < 16) :
    rdMsg (R rs r) i ∈ rds rs ++ ars as := by
  simp only [rds, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range]
  exact .inl ⟨r, hr, i, hi, rfl⟩

theorem ar_mem {rs : List RcptV} {as : List AcctV} {a : AcctV} (ha : a ∈ as) {i : Nat} (hi : i < 16) :
    arMsg a i ∈ rds rs ++ ars as := by
  simp only [ars, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range]
  exact .inr ⟨a, ha, i, hi, rfl⟩

theorem acct_eq_of_k {as : List AcctV} (hnd : (as.map (·.k)).Nodup) {a b : AcctV} (ha : a ∈ as)
    (hb : b ∈ as) (hk : a.k = b.k) : a = b := by
  have h1 := acctOf_eq hnd ha
  have h2 := acctOf_eq hnd hb
  rw [hk] at h1
  exact Option.some.inj (h1.symm.trans h2)

theorem nodup_range_map' {α : Type} (f : Nat → α) (hf : ∀ i j, f i = f j → i = j) (n : Nat) :
    ((List.range n).map f).Nodup :=
  Link.nodup_range_map f hf n

theorem W_nodup {rs : List RcptV} {as : List AcctV} (hk : (as.map (·.k)).Nodup) :
    (wrs rs ++ aws as).Nodup := by
  rw [List.nodup_append]
  refine ⟨?_, ?_, ?_⟩
  · apply Sound.nodup_flatMap_of
    · intro r _; exact nodup_range_map' _ (fun i j h => by simp [wrMsg] at h; exact h.1) 16
    · intro i j a b x hij ha hb hxa hxb
      simp only [List.mem_map, List.mem_range] at hxa hxb
      obtain ⟨i1, -, rfl⟩ := hxa
      obtain ⟨i2, -, he⟩ := hxb
      have e1 : a = i := by
        have := List.getElem?_eq_some_iff.mp ha; simp at this; omega
      have e2 : b = j := by
        have := List.getElem?_eq_some_iff.mp hb; simp at this; omega
      simp only [wrMsg, List.cons.injEq] at he
      exact hij (by omega)
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
      have hlen' : j < as.length := (List.getElem?_eq_some_iff.mp hb).1
      have hm : (as.map (·.k))[i]? = (as.map (·.k))[j]? := by simp [ha, hb]
      exact hij ((List.Nodup.getElem?_inj (by simpa using hlen) hk).mp hm)
  · intro x hx y hy hxy
    subst hxy
    simp only [wrs, aws, List.mem_flatMap, List.mem_map, List.mem_range] at hx hy
    obtain ⟨r, -, i, -, rfl⟩ := hx
    obtain ⟨a, -, i', -, he⟩ := hy
    simp [wrMsg, awMsg] at he

section Hyp
variable {rs : List RcptV} {as : List AcctV} (h : MemHyp rs as)
include h

theorem R_nodup : (rds rs ++ ars as).Nodup := h.perm.nodup_iff.mp (W_nodup h.knd)

theorem read_in_W {m : Msg} (hm : m ∈ rds rs ++ ars as) : m ∈ wrs rs ++ aws as :=
  h.perm.mem_iff.mpr hm

/-- Writes are determined by their key `(k, t, i)`. -/
theorem W_key {m₁ m₂ : Msg} (h₁ : m₁ ∈ wrs rs ++ aws as) (h₂ : m₂ ∈ wrs rs ++ aws as)
    (hk : m₁.take 3 = m₂.take 3) : m₁ = m₂ := by
  rcases mem_W.mp h₁ with ⟨r, hr, i, hi, rfl⟩ | ⟨a, ha, i, hi, rfl⟩ <;>
  rcases mem_W.mp h₂ with ⟨r', hr', i', hi', rfl⟩ | ⟨a', ha', i', hi', rfl⟩
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

/-- Distinct receipts read different messages. -/
theorem rd_ne {r r' : Nat} (hr : r < rs.length) (hr' : r' < rs.length) (hne : r ≠ r') :
    rdMsg (R rs r) 0 ≠ rdMsg (R rs r') 0 := by
  intro he
  have hnd := R_nodup h
  rw [List.nodup_append] at hnd
  have := Sound.flatMap_disj (fun q => (List.range 16).map (rdMsg (R rs q)))
    (List.range rs.length) r r' r r' (rdMsg (R rs r) 0) hnd.1 hne
    (by simp [hr]) (by simp [hr']) (List.mem_map.mpr ⟨0, by simp, rfl⟩)
  exact this (List.mem_map.mpr ⟨0, by simp, he.symm⟩)

theorem rd_ne_ar {r : Nat} (hr : r < rs.length) {a : AcctV} (ha : a ∈ as) :
    rdMsg (R rs r) 0 ≠ arMsg a 0 := by
  intro he
  have hnd := R_nodup h
  rw [List.nodup_append] at hnd
  refine hnd.2.2 _ ?_ _ ?_ he
  · simp only [rds, List.mem_flatMap, List.mem_map, List.mem_range]
    exact ⟨r, hr, 0, by decide, rfl⟩
  · simp only [ars, List.mem_flatMap, List.mem_map, List.mem_range]
    exact ⟨a, ha, 0, by decide, rfl⟩

/-- A write time of slot `k`: `0`, or `r' + 1` for a receipt `r'` writing `k`. -/
theorem read_time {k t : Nat} {m : Msg} (hm : m ∈ wrs rs ++ aws as) (hk : m.take 3 = [k, t, 0]) :
    t = 0 ∨ (∃ r', r' < rs.length ∧ ksl rs r' = k ∧ t = r' + 1) := by
  rcases mem_W.mp hm with ⟨r, hr, i, hi, rfl⟩ | ⟨a, ha, i, hi, rfl⟩
  · simp only [wrMsg, List.take, List.cons.injEq, and_true] at hk
    exact .inr ⟨r, hr, hk.1, hk.2.1.symm⟩
  · simp only [awMsg, acctLane, List.cons_append, List.take, List.cons.injEq, and_true] at hk
    exact .inl hk.2.1.symm

/-- **Each receipt reads the last earlier write of its slot.** -/
theorem tprev_eq : ∀ r, r < rs.length → (R rs r).tprev = lastW (ksl rs) (R rs r).kslot r := by
  intro r
  induction r using Nat.strongRecOn with
  | _ r ih =>
    intro hr
    have hin := read_in_W h (rd_mem (as := as) hr (i := 0) (by decide))
    have htime := read_time h hin (k := (R rs r).kslot) (t := (R rs r).tprev) rfl
    have hle := h.tle r hr (by rcases htime with e | ⟨r', hr', -, e⟩ <;> omega)
    have htL : (R rs r).tprev ≤ lastW (ksl rs) (R rs r).kslot r := by
      rcases htime with e | ⟨r', hr', hk, e⟩
      · omega
      · rw [e]; exact le_lastW _ _ r r' (by omega) hk
    apply Classical.byContradiction; intro hne
    have hlt' : (R rs r).tprev < lastW (ksl rs) (R rs r).kslot r := Nat.lt_of_le_of_ne htL hne
    rcases lastW_cases (ksl rs) (R rs r).kslot r with e | ⟨r0, hr0, hk0, e⟩
    · omega
    obtain ⟨r1, e1, e2, e3, e4⟩ := exists_first (ksl rs) (R rs r).kslot (R rs r).tprev r0 (by omega) hk0
    have hr1 : r1 < rs.length := by omega
    have hL1 : lastW (ksl rs) (R rs r).kslot r1 = (R rs r).tprev := by
      apply lastW_eq_of _ _ _ r1 e1 e4
      rcases htime with e | ⟨r', -, hk, e⟩
      · exact .inl e
      · exact .inr ⟨by omega, by rw [e]; exact hk⟩
    have ht1 : (R rs r1).tprev = (R rs r).tprev := by
      rw [ih r1 (by omega) hr1]
      have : (R rs r1).kslot = (R rs r).kslot := e3
      rw [this, hL1]
    have hin1 := read_in_W h (rd_mem (as := as) hr1 (i := 0) (by decide))
    have hkey : (rdMsg (R rs r) 0).take 3 = (rdMsg (R rs r1) 0).take 3 := by
      simp only [rdMsg, List.take]
      have : (R rs r1).kslot = (R rs r).kslot := e3
      rw [ht1, this]
    exact rd_ne h hr hr1 (by omega) (W_key h hin hin1 hkey)

/-- **The acct table's final read gets the last write.** -/
theorem tlast_eq {a : AcctV} (ha : a ∈ as) : a.tlast = lastW (ksl rs) a.k rs.length := by
  have hin := read_in_W h (ar_mem (rs := rs) ha (i := 0) (by decide))
  have htime := read_time h hin (k := a.k) (t := a.tlast) (by simp [arMsg, acctLane, List.take])
  have htL : a.tlast ≤ lastW (ksl rs) a.k rs.length := by
    rcases htime with e | ⟨r', hr', hk, e⟩
    · omega
    · rw [e]; exact le_lastW _ _ _ r' hr' hk
  apply Classical.byContradiction; intro hne
  have hlt' := Nat.lt_of_le_of_ne htL hne
  rcases lastW_cases (ksl rs) a.k rs.length with e | ⟨r0, hr0, hk0, e⟩
  · omega
  obtain ⟨r1, e1, e2, e3, e4⟩ := exists_first (ksl rs) a.k a.tlast r0 (by omega) hk0
  have hr1 : r1 < rs.length := by omega
  have hL1 : lastW (ksl rs) a.k r1 = a.tlast := by
    apply lastW_eq_of _ _ _ r1 e1 e4
    rcases htime with e | ⟨r', -, hk, e⟩
    · exact .inl e
    · exact .inr ⟨by omega, by rw [e]; exact hk⟩
  have ht1 : (R rs r1).tprev = a.tlast := by
    rw [tprev_eq h r1 hr1]
    have : (R rs r1).kslot = a.k := e3
    rw [this, hL1]
  have hin1 := read_in_W h (rd_mem (as := as) hr1 (i := 0) (by decide))
  have hkey : (rdMsg (R rs r1) 0).take 3 = (arMsg a 0).take 3 := by
    simp only [rdMsg, arMsg, acctLane, List.cons_append, List.take]
    have : (R rs r1).kslot = a.k := e3
    rw [ht1, this]
  exact rd_ne_ar h hr1 ha (W_key h hin1 hin hkey)

/-- The payload of a receipt's read. -/
theorem mem_read {r : Nat} (hr : r < rs.length) {i : Nat} (hi : i < 16) :
    (lastW (ksl rs) (R rs r).kslot r = 0 →
      ∃ a ∈ as, a.k = (R rs r).kslot ∧ rdMsg (R rs r) i = awMsg a i) ∧
    (∀ r0, lastW (ksl rs) (R rs r).kslot r = r0 + 1 →
      r0 < r ∧ (R rs r0).kslot = (R rs r).kslot ∧ rdMsg (R rs r) i = wrMsg (R rs r0) r0 i) := by
  have hin := read_in_W h (rd_mem (as := as) hr hi)
  have ht := tprev_eq h r hr
  have hle := lastW_le (ksl rs) (R rs r).kslot r
  refine ⟨fun hL => ?_, fun r0 hL => ?_⟩
  · rcases mem_W.mp hin with ⟨r', hr', i', hi', he⟩ | ⟨a, ha, i', hi', he⟩
    · simp only [rdMsg, wrMsg, List.cons.injEq] at he; omega
    · refine ⟨a, ha, ?_, ?_⟩
      · simp only [rdMsg, awMsg, List.cons_append, List.cons.injEq] at he; exact he.1.symm
      · rw [he]; simp only [rdMsg, awMsg, List.cons_append, List.cons.injEq] at he; rw [he.2.2.1]
  · rcases mem_W.mp hin with ⟨r', hr', i', hi', he⟩ | ⟨a, ha, i', hi', he⟩
    · have he' := he
      simp only [rdMsg, wrMsg, List.cons.injEq] at he'
      have : r' = r0 := by omega
      subst this
      refine ⟨by omega, he'.1.symm, ?_⟩
      rw [he, he'.2.2.1]
    · simp only [rdMsg, awMsg, List.cons_append, List.cons.injEq] at he; omega

/-- The payload of the acct table's final read. -/
theorem mem_final {a : AcctV} (ha : a ∈ as) {i : Nat} (hi : i < 16) :
    (lastW (ksl rs) a.k rs.length = 0 → arMsg a i = awMsg a i) ∧
    (∀ r0, lastW (ksl rs) a.k rs.length = r0 + 1 →
      r0 < rs.length ∧ (R rs r0).kslot = a.k ∧ arMsg a i = wrMsg (R rs r0) r0 i) := by
  have hin := read_in_W h (ar_mem (rs := rs) ha hi)
  have ht := tlast_eq h ha
  refine ⟨fun hL => ?_, fun r0 hL => ?_⟩
  · rcases mem_W.mp hin with ⟨r', hr', i', hi', he⟩ | ⟨b, hb, i', hi', he⟩
    · simp only [arMsg, wrMsg, acctLane, List.cons_append, List.cons.injEq] at he; omega
    · have hk : a.k = b.k := by
        simp only [arMsg, awMsg, acctLane, List.cons_append, List.cons.injEq] at he; exact he.1
      have := acct_eq_of_k h.knd ha hb hk
      subst this
      rw [he]; simp only [arMsg, awMsg, acctLane, List.cons_append, List.cons.injEq] at he
      rw [he.2.2.1]
  · rcases mem_W.mp hin with ⟨r', hr', i', hi', he⟩ | ⟨b, hb, i', hi', he⟩
    · have he' := he
      simp only [arMsg, wrMsg, acctLane, List.cons_append, List.cons.injEq] at he'
      have : r' = r0 := by omega
      subst this
      refine ⟨hr', he'.1.symm, ?_⟩
      rw [he, he'.2.2.1]
    · simp only [arMsg, awMsg, acctLane, List.cons_append, List.cons.injEq] at he; omega

end Hyp

end ZkFormal.NearV3.RcptLink
