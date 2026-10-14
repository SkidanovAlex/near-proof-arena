/-!
# `ZkFormal.NearV3.D1.Extract.Tx.Arith` — the `txV3` verdict as arithmetic on the chain results

Pure `Nat` lemmas over an abstract modulus `M` (`= 2¹²⁸ = 256¹⁶` at the use site), so no large
literal meets a free variable (lean4lean / nanoda pitfall).  The carries are case-split
(`0` / `1`), after which everything is linear in `M`.
-/

namespace ZkFormal.NearV3.D1.TxProof

/-- **Debit verdict.** -/
theorem debit_arith {M N Bd C A L St Kn DN DB R T Q DQ DS : Nat}
    {boN boB coC coT boQ boS zN strict : Nat}
    (hbN : boN ≤ 1) (hbB : boB ≤ 1) (hcC : coC ≤ 1) (hcT : coT ≤ 1) (hbQ : boQ ≤ 1) (hbS : boS ≤ 1)
    (hN : N + M * boN = DN + Kn + 1) (hDN : DN < M) (hz : zN = 1 ↔ DN = 0)
    (hB : Bd + M * boB = DB + N + 1) (hDB : DB < M)
    (hC : A + M * coC = R + C) (hR : R < M)
    (hT : T + M * coT = R + L) (hTl : T < M)
    (hD : T + M * boQ = DQ + Q) (hDQ : DQ < M)
    (hS : 770 + M * boS = DS + St) (hDS : DS < M) :
    (boN = 0 ∧ (strict = 0 ∨ zN = 1) ∧ boB = 0 ∧ coC = 0 ∧ coT = 0 ∧ ¬ (boQ = 1 ∧ boS = 1)) ↔
      (Kn < N ∧ (strict ≠ 0 → N = Kn + 1) ∧ N < Bd ∧ C ≤ A ∧ A - C + L < M ∧
        (Q ≤ A - C + L ∨ St ≤ 770)) := by
  have b01 : ∀ x : Nat, x ≤ 1 → x = 0 ∨ x = 1 := fun x hx => by omega
  have e1 : boN = 0 ↔ Kn < N := by rcases b01 boN hbN with rfl | rfl <;> omega
  have e2 : boN = 0 → (zN = 1 ↔ N = Kn + 1) := by
    intro h0; rw [hz]; subst h0; omega
  have e3 : boB = 0 ↔ N < Bd := by rcases b01 boB hbB with rfl | rfl <;> omega
  have e4 : coC = 0 ↔ C ≤ A := by rcases b01 coC hcC with rfl | rfl <;> omega
  have e4' : coC = 0 → R = A - C := by intro h0; subst h0; omega
  have e5 : coC = 0 → (coT = 0 ↔ A - C + L < M) := by
    intro h0; have := e4' h0; rcases b01 coT hcT with rfl | rfl <;> omega
  have e5' : coC = 0 → coT = 0 → T = A - C + L := by
    intro h0 h1; have := e4' h0; subst h1; omega
  have e6 : coC = 0 → coT = 0 → (boQ = 0 ↔ Q ≤ A - C + L) := by
    intro h0 h1; have := e5' h0 h1; rcases b01 boQ hbQ with rfl | rfl <;> omega
  have e7 : boS = 0 ↔ St ≤ 770 := by rcases b01 boS hbS with rfl | rfl <;> omega
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨e1.mp h1, fun hs => (e2 h1).mp (h2.resolve_left hs), e3.mp h3, e4.mp h4, (e5 h4).mp h5, ?_⟩
    rcases b01 boQ hbQ with hq | hq
    · exact Or.inl ((e6 h4 h5).mp hq)
    · rcases b01 boS hbS with hs | hs
      · exact Or.inr (e7.mp hs)
      · exact absurd ⟨hq, hs⟩ h6
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    have k4 := e4.mpr h4
    have k5 := (e5 k4).mpr h5
    refine ⟨e1.mpr h1, ?_, e3.mpr h3, k4, k5, ?_⟩
    · by_cases hs : strict = 0
      · exact Or.inl hs
      · exact Or.inr ((e2 (e1.mpr h1)).mpr (h2 hs))
    · rintro ⟨hq, hs⟩
      rcases h6 with h6 | h6
      · have := (e6 k4 k5).mpr h6; omega
      · have := e7.mpr h6; omega

/-- **Credit facts.** -/
theorem credit_arith {M C A L St R T Q DQ DS : Nat} {boQ boS : Nat}
    (hbQ : boQ ≤ 1) (hbS : boS ≤ 1)
    (hC : R + M * 0 = A + C) (hT : T + M * 0 = R + L)
    (hD : T + M * boQ = DQ + Q) (hDQ : DQ < M)
    (hS : 770 + M * boS = DS + St) (hDS : DS < M) (hTl : T < M)
    (hqs : ¬ (boQ = 1 ∧ boS = 1)) :
    R = A + C ∧ R + L < M ∧ (Q ≤ R + L ∨ St ≤ 770) := by
  refine ⟨by omega, by omega, ?_⟩
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hbQ with hq | hq
  · subst hq; left; omega
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hbS with hs | hs
    · subst hs; right; omega
    · exact absurd ⟨hq, hs⟩ hqs

/-- The debit write: no borrow gives `R = A − C`. -/
theorem debit_write {M C A R : Nat} (hC : A + M * 0 = R + C) : R = A - C ∧ C ≤ A := by omega

end ZkFormal.NearV3.D1.TxProof
