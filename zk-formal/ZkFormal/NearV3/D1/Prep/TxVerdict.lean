import ZkFormal.NearV3.D1.PrepD1Lemmas

/-!
# `ZkFormal.NearV3.D1.Prep.TxVerdict` — `TxVerdictStmt`: the verdict `txV3` recomputes

Lane `v3-d1-phase2` (docs/zk-formal/V3-D1-PHASE2.md, milestone P1).  `verifyAndCharge` succeeds
exactly when the key is FullAccess, the nonce check passes (strict: `N = kn + 1`; monotonic:
`N > kn`), `N < min(height·10⁶, 2⁶⁴ − 1)`, the balance covers the cost, the new amount plus the
locked balance is below `2¹²⁸` and the storage stake holds.  The two spec conditions `txV3` does
not compute are implied: the strict-nonce overflow guard `kn + 1 < 2⁶⁴` (by `N < 2⁶⁴ − 1`) and
`10¹⁹·storage < 2¹²⁸` (by the stake: either `10¹⁹·storage ≤ new + locked < 2¹²⁸`, or
`storage ≤ 770`).
-/

namespace ZkFormal.NearV3.D1

open NearSpec NearSpec.TransferV1 NearSpecV3

/-- `10¹⁹ · 770 < 2¹²⁸` (closed literals). -/
theorem stake770_lt : Params.storageAmountPerByte * Params.zeroBalanceStorageLimit < Params.two128 := by
  decide

theorem stake_lt_of_le {st : Nat} (h : st ≤ Params.zeroBalanceStorageLimit) :
    Params.storageAmountPerByte * st < Params.two128 :=
  Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ h) stake770_lt

/-- The charge part of `verifyAndCharge` (FullAccess) as a Boolean, over atoms. -/
theorem charge_isSome (bL bR : Bool) (hb : bL = bR) (amt C lk req st T lim : Nat)
    (hS : st ≤ lim → req < T) :
    (if (!bL) = true then (none : Option Nat) else
      if amt < C then none else
        if (decide (req ≥ T) || decide (amt - C + lk ≥ T)) = true then none else
          if (!(decide (amt - C + lk ≥ req) || decide (st ≤ lim))) = true then none
          else some (amt - C)).isSome =
      (bR && decide (C ≤ amt) && decide (amt - C + lk < T) &&
        (decide (req ≤ amt - C + lk) || decide (st ≤ lim))) := by
  subst hb
  cases bL
  · simp
  · by_cases h1 : amt < C
    · simp only [Bool.not_true, Bool.false_eq_true, ite_false, h1, ite_true, Option.isSome_none,
        Bool.true_and]
      simp only [show ¬ C ≤ amt by omega, decide_false, Bool.false_and]
    · simp only [Bool.not_true, Bool.false_eq_true, ite_false, h1, Bool.true_and,
        show C ≤ amt by omega, decide_true]
      by_cases h2 : amt - C + lk < T
      · simp only [show ¬ (amt - C + lk ≥ T) by omega, decide_false, Bool.or_false, h2,
          decide_true, Bool.true_and]
        by_cases h3 : req ≤ amt - C + lk
        · simp [show req < T by omega, h3]
        · by_cases h4 : st ≤ lim
          · simp [hS h4, h3, h4]
          · simp [h3, h4]
      · simp [show amt - C + lk ≥ T by omega, h2]

/-- **`TxVerdictStmt`.** -/
theorem txVerdict : TxVerdictStmt := by
  intro a k t c height
  unfold verifyAndCharge
  cases hp : k.perm with
  | gasKey => simp
  | functionCall al =>
    simp only [reduceCtorEq, decide_false, Bool.false_and]
    repeat' split
    all_goals simp
  | fullAccess =>
    simp only [decide_true, Bool.true_and]
    refine charge_isSome _ _ ?_ _ _ _ _ _ _ _ (fun h => stake_lt_of_le h)
    cases hs : t.strict
    · simp
    · by_cases hn : t.nonce = k.nonce + 1
      · by_cases hb : t.nonce < min (height * TxParams.nonceRangeMultiplier) (Params.two64 - 1)
        · have hk : k.nonce + 1 < Params.two64 := by omega
          simp [hk, hn]
        · simp [hb]
      · simp [hn]

end ZkFormal.NearV3.D1
