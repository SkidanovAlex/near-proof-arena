import ZkFormal.NearV3.D1.Link.MemChain
import ZkFormal.NearV3.D1.Link.MemD1

/-!
# `ZkFormal.NearV3.D1.Link.RcptChain` — the incoming receipts on the D1 `MEM` timeline (L1, the run)

Lane `v3-d1-phase2`, item L1 (next step 2 of checkpoint 12).  On the D1 timeline (`evsD1`: the
`T0` ops, then the receipts) receipt `r` is event `T0 + r` and always active.  Restricted to the
receipts, the last write of a slot before receipt `r` is either an earlier receipt (D0a's
`lastW (ksl (rv ls)) k r = r0 + 1`, the same write) or happened at or before `T0` (an op or the
acct record's opening):

* `lastW_shift`: the timeline's last write before `T0 + r` in terms of the receipts' one;
* **`rcpt_prev`**: a receipt whose slot was written by an earlier receipt `r0` reads `r0`'s `aft`;
* `rcpt_first`: otherwise no earlier receipt wrote the slot.

So the receipt run starts from the slot values at time `T0` (the transactions' result), and after
the first receipt of a slot it is D0a's chain.
-/

namespace ZkFormal.NearV3.D1.Link

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Link ZkFormal.NearV3 ZkFormal.NearV3.D1
open ZkFormal.NearV3.RcptLink (R rv rv_length R_rv)

section
variable {es : List TxE} {t0 : Nat} {ls : RcptV3Vs}

theorem actD1_rc (r : Nat) : actD1 es t0 (t0 + r) = true := by
  simp [actD1]

theorem kslA_rc (r : Nat) :
    kslA (actD1 es t0) (evsD1 es t0 ls) (t0 + r) = 2 * ksl (rv ls) r + 1 := by
  simp only [kslA, actD1_rc, ite_true, R_evs_rc, ksl, R]

/-- **The timeline's last write before receipt `r`**, from the receipts' last write. -/
theorem lastW_shift (k : Nat) : ∀ r, lastW (kslA (actD1 es t0) (evsD1 es t0 ls)) (2 * k + 1) (t0 + r) =
    if lastW (ksl (rv ls)) k r = 0 then lastW (kslA (actD1 es t0) (evsD1 es t0 ls)) (2 * k + 1) t0
    else t0 + lastW (ksl (rv ls)) k r
  | 0 => by simp [lastW]
  | r + 1 => by
    rw [show t0 + (r + 1) = (t0 + r) + 1 by omega]
    simp only [lastW]
    rw [kslA_rc]
    by_cases hk : ksl (rv ls) r = k
    · simp only [hk, ite_true, Nat.add_one_ne_zero, ite_false]
      omega
    · have hne : ¬ (2 * ksl (rv ls) r + 1 = 2 * k + 1) := by omega
      simp only [hne, hk, ite_false]
      exact lastW_shift k r

variable {as : List AcctV} (h : MemHypA (actD1 es t0) (evsD1 es t0 ls) as)
include h

/-- **A receipt whose slot an earlier receipt `r0` wrote last reads `r0`'s `aft`.** -/
theorem rcpt_prev {r : Nat} (hr : r < (flatR ls).length) {r0 : Nat}
    (he : lastW (ksl (rv ls)) (R (rv ls) r).kslot r = r0 + 1) {i : Nat} (hi : i < 16) :
    r0 < r ∧ (R (rv ls) r0).kslot = (R (rv ls) r).kslot ∧
      (R (rv ls) r).bef.getD i 0 = (R (rv ls) r0).aft.getD i 0 := by
  have hr' : t0 + r < (evsD1 es t0 ls).length := by rw [evsD1_length]; omega
  have hL := lastW_shift (es := es) (t0 := t0) (ls := ls) (R (rv ls) r).kslot r
  rw [he, if_neg (by omega)] at hL
  have hL' : lastW (kslA (actD1 es t0) (evsD1 es t0 ls)) (2 * (R (evsD1 es t0 ls) (t0 + r)).kslot + 1)
      (t0 + r) = (t0 + r0) + 1 := by
    rw [R_evs_rc, hL]; omega
  obtain ⟨hlt, -, hk, he2⟩ := (mem_readA h hr' (actD1_rc r) hi).2 (t0 + r0) hL'
  rw [R_evs_rc] at he2 hk
  rw [R_evs_rc] at hk
  have hlt' : r0 < r := by omega
  refine ⟨hlt', hk, ?_⟩
  rw [R_evs_rc] at he2
  simp only [rdMsg, wrMsg, List.cons.injEq] at he2
  exact he2.2.2.2.1

omit h in
/-- No earlier receipt wrote the slot of a receipt whose receipts-only last write is `0`. -/
theorem rcpt_first {k r : Nat} (he : lastW (ksl (rv ls)) k r = 0) : ∀ r0, r0 < r → ksl (rv ls) r0 ≠ k := by
  intro r0 hr0 hk
  have := le_lastW (ksl (rv ls)) k r r0 hr0 hk
  omega

end

end ZkFormal.NearV3.D1.Link
