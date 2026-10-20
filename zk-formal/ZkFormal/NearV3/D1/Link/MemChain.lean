import ZkFormal.NearV3.D1.Link.MemEv
import ZkFormal.Near.Link.Run

/-!
# `ZkFormal.NearV3.D1.Link.MemChain` — slot values along the D1 `MEM` timeline (L1, the run)

Lane `v3-d1-phase2`, item L1 (next step 2 of checkpoint 12).  D0a's `RecChain` (`slot_acct`,
`lanes`, `bef_val`) reads the `MEM` chain of the receipts only.  In D1 the timeline is the
transaction ops, then the receipts (`MemD1.evsD1`), and an op is an event only when it is
active (`MemEv.MemHypA`).  The chain facts hold for **every active event**, op or receipt:

* `slot_acctA`: an active event's slot is the slot of an acct record (the chain of last writes
  ends at the acct record's opening write);
* `lanesA`: the locked / storage lanes of an active event's read are the acct record's pre-state
  lanes (no event changes them: a write carries the read's `lk` / `st`), and its `bef` is bytes
  (given that every active event's `aft` is bytes);
* `bef_valA`: an active event reads the value of its slot's last earlier write (`wval`: the
  acct record's pre amount, or the `aft` of the last active event writing the slot);
* `final_valA`: the acct record's post amount is the value of the slot's last write.
-/

namespace ZkFormal.NearV3.D1.Link

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Link
open ZkFormal.NearV3.RcptLink (R acct_eq_of_k)

section Hyp
variable {act : Nat → Bool} {rs : List RcptV} {as : List AcctV} (h : MemHypA act rs as)
include h

/-- **Every active event's slot is an acct record's slot.** -/
theorem slot_acctA : ∀ r, r < rs.length → act r = true → ∃ a ∈ as, a.k = (R rs r).kslot := by
  intro r
  induction r using Nat.strongRecOn with
  | _ r ih =>
    intro hr hact
    rcases lastW_cases (kslA act rs) (2 * (R rs r).kslot + 1) r with e | ⟨r0, -, -, e⟩
    · obtain ⟨a, ha, hk, -⟩ := (mem_readA h hr hact (i := 0) (by decide)).1 e
      exact ⟨a, ha, hk⟩
    · obtain ⟨hlt, hact0, hk, -⟩ := (mem_readA h hr hact (i := 0) (by decide)).2 r0 e
      obtain ⟨a, ha, hk'⟩ := ih r0 hlt (by omega) hact0
      exact ⟨a, ha, hk'.trans hk⟩

/-- **The lanes of an active event's read**: locked and storage are the slot's pre-state lanes;
`bef` is bytes. -/
theorem lanesA (hpre : ∀ a ∈ as, Bytes8 a.pre)
    (haft : ∀ r, r < rs.length → act r = true → Bytes8 (R rs r).aft) :
    ∀ r, r < rs.length → act r = true → ∀ a ∈ as, a.k = (R rs r).kslot → ∀ i, i < 16 →
      (R rs r).lk.getD i 0 = a.pre.getD (16 + i) 0 ∧
      (R rs r).st.getD i 0 = (if i < 8 then a.pre.getD (64 + i) 0 else 0) ∧
      (R rs r).bef.getD i 0 < 256 := by
  intro r
  induction r using Nat.strongRecOn with
  | _ r ih =>
    intro hr hact a ha hk i hi
    rcases lastW_cases (kslA act rs) (2 * (R rs r).kslot + 1) r with e | ⟨r0, -, -, e⟩
    · obtain ⟨b, hb, hbk, he⟩ := (mem_readA h hr hact hi).1 e
      have : b = a := acct_eq_of_k h.knd hb ha (hbk.trans hk.symm)
      subst this
      simp only [rdMsg, awMsg, acctLane, List.cons_append, List.nil_append, List.cons.injEq] at he
      refine ⟨he.2.2.2.2.1, he.2.2.2.2.2.1, ?_⟩
      rw [he.2.2.2.1]; exact getD_lt_of_bytes8 (hpre b hb) _
    · obtain ⟨hlt, hact0, hk0, he⟩ := (mem_readA h hr hact hi).2 r0 e
      have hr0 : r0 < rs.length := by omega
      obtain ⟨i1, i2, -⟩ := ih r0 hlt hr0 hact0 a ha (hk.trans hk0.symm) i hi
      simp only [rdMsg, wrMsg, List.cons.injEq] at he
      refine ⟨he.2.2.2.2.1.trans i1, he.2.2.2.2.2.1.trans i2, ?_⟩
      rw [he.2.2.2.1]; exact getD_lt_of_bytes8 (haft r0 hr0 hact0) _

/-- **An active event reads the value of its slot's last write** (`wval`: the acct record's pre
amount, or the last earlier active writer's `aft`). -/
theorem bef_valA (hpreL : ∀ a ∈ as, a.pre.length = 72)
    (hlen : ∀ r, r < rs.length → act r = true → (R rs r).bef.length = 16 ∧ (R rs r).aft.length = 16)
    {r : Nat} (hr : r < rs.length) (hact : act r = true) {a : AcctV} (ha : a ∈ as)
    (hk : a.k = (R rs r).kslot) :
    leN' (R rs r).bef = wval rs a (lastW (kslA act rs) (2 * a.k + 1) r) := by
  have hl := hpreL a ha
  rw [hk]
  rcases lastW_cases (kslA act rs) (2 * (R rs r).kslot + 1) r with e | ⟨r0, -, -, e⟩
  · rw [e]; simp only [wval, if_true]
    congr 1
    apply ext16 (hlen r hr hact).1 (by simp [hl])
    intro i hi
    obtain ⟨b, hb, hbk, he⟩ := (mem_readA h hr hact hi).1 e
    have : b = a := acct_eq_of_k h.knd hb ha (hbk.trans hk.symm)
    subst this
    simp only [rdMsg, awMsg, acctLane, List.cons_append, List.nil_append, List.cons.injEq] at he
    rw [he.2.2.2.1, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take,
      if_pos hi]
  · rw [e]; simp only [wval, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
    obtain ⟨hlt, hact0, -, -⟩ := (mem_readA h hr hact (i := 0) (by decide)).2 r0 e
    have hr0 : r0 < rs.length := by omega
    congr 1
    apply ext16 (hlen r hr hact).1 (hlen r0 hr0 hact0).2
    intro i hi
    obtain ⟨-, -, -, he2⟩ := (mem_readA h hr hact hi).2 r0 e
    simp only [rdMsg, wrMsg, List.cons.injEq] at he2
    exact he2.2.2.2.1

/-- **The acct record's post amount is the value of the slot's last write.** -/
theorem final_valA (hpreL : ∀ a ∈ as, a.pre.length = 72 ∧ a.post.length = 16)
    (hlen : ∀ r, r < rs.length → act r = true → (R rs r).aft.length = 16)
    {a : AcctV} (ha : a ∈ as) :
    leN' a.post = wval rs a (lastW (kslA act rs) (2 * a.k + 1) rs.length) := by
  have hl := hpreL a ha
  rcases lastW_cases (kslA act rs) (2 * a.k + 1) rs.length with e | ⟨r0, hr0, hk0, e⟩
  · rw [e]; simp only [wval, if_true]
    congr 1
    apply ext16 hl.2 (by simp [hl.1])
    intro i hi
    have he := (mem_finalA h ha hi).1 e
    simp only [arMsg, awMsg, acctLane, List.cons_append, List.nil_append, List.cons.injEq] at he
    rw [he.2.2.2.1, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take,
      if_pos hi]
  · rw [e]; simp only [wval, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
    obtain ⟨-, hact0, -, -⟩ := (mem_finalA h ha (i := 0) (by decide)).2 r0 e
    congr 1
    apply ext16 hl.2 (hlen r0 hr0 hact0)
    intro i hi
    obtain ⟨-, -, -, he2⟩ := (mem_finalA h ha hi).2 r0 e
    simp only [arMsg, wrMsg, acctLane, List.cons_append, List.nil_append, List.cons.injEq] at he2
    exact he2.2.2.2.1

end Hyp

end ZkFormal.NearV3.D1.Link
