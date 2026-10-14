import ZkFormal.NearV3.D1.Extract.Tx.ChainD

/-!
# `ZkFormal.NearV3.D1.Extract.Tx.ChainZ` — the credit sum `msum` and the zero test `zN`

* `msum` on lane `k` = `Σ_{i ≤ k} (255 − rCᵢ)` (so `msum₁₅ ≠ 0` ⇒ `rC ≠ 2¹²⁸ − 1`);
* `eN = [dN = 0]` on every active row; `zN` on lane `k` is `1` iff `dN₀ … dN_k` are all `0`.
-/

namespace ZkFormal.NearV3.D1.TxProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.D1
  ZkFormal.NearV3.D1.TxV3

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

/-- `Σ_{i ≤ k} (255 − rCᵢ)`. -/
def msV (tr : Trace Fp) (tt s k : Nat) : Nat :=
  ((List.range (k + 1)).map fun i => 255 - bv tr tt (s + i) rCb).sum

theorem natCast_subT (a b : Nat) (h : b ≤ a) : ((a - b : Nat) : Fp) = (a : Fp) - (b : Fp) := by
  have : ((a - b + b : Nat) : Fp) = (a : Fp) := by rw [Nat.sub_add_cancel h]
  rw [natCast_add] at this; grind

theorem msV_succ (s k : Nat) : msV tr tt s (k + 1) = msV tr tt s k + (255 - bv tr tt (s + (k + 1)) rCb) := by
  unfold msV; rw [List.range_succ, List.map_append, List.sum_append]; simp

theorem msV_le (s k : Nat) : msV tr tt s k ≤ 255 * (k + 1) := by
  induction k with
  | zero => simp [msV]
  | succ k ih => rw [msV_succ]; omega

section
variable (hL : TableLocal TxV3.table tr tt pub)
include hL

theorem msum_val {s : Nat} (hop : OpAt tr tt s) :
    ∀ m, m < 16 → tr.cell tt (s + m) msum = ((msV tr tt s m : Nat) : Fp) := by
  have hH := hop.h
  intro m
  induction m with
  | zero =>
    intro _
    have e := con hL (r := s) (by omega)
      (mem_chains (e := first (sub (c msum) (sub (k 255) rC))) (by simp [cChains, chain]))
    have hlf := hop.lf 0 (by omega)
    have hd := bv_lt hL (r := s) (by omega) rCb_bool
    simp only [Nat.add_zero, ite_true] at hlf
    simp only [first, rC, byteC, eval_mul, eval_sub, eval_c, eval_k, hlf,
      eval_byte hL (r := s) (by omega) rCb_bool, Nat.add_zero] at e
    have hm : msV tr tt s 0 = 255 - bv tr tt s rCb := by simp [msV]
    rw [hm, natCast_subT _ _ (by omega)]
    grind
  | succ m ih =>
    intro hk
    have hac := hop.act m (by omega)
    have hl := hop.ll m (by omega)
    rw [if_neg (by omega)] at hl
    have hn : s + m + 1 < tr.height tt := by omega
    have hd := bv_lt hL (r := s + m + 1) (by omega) rCb_bool
    have e := con hL (r := s + m) (by omega)
      (mem_chains (e := inOpE (sub (n msum) (.add (c msum) (sub (k 255) (byteN rCb)))))
        (by simp [cChains, chain]))
    simp only [inOpE, inOp, byteN, eval_mul, eval_sub, eval_add, eval_c, eval_n, eval_k, eval_not,
      hac, hl, eval_bitsN hn, nxt hn, eval_byte hL (r := s + m + 1) (by omega) rCb_bool,
      ih (by omega)] at e
    rw [msV_succ, ← Nat.add_assoc, natCast_add, natCast_subT _ _ (by omega)]
    grind

theorem eN_facts {r : Nat} (hr : r < tr.height tt) (ha : tr.cell tt r act = 1) :
    (tr.cell tt r eN = 0 ∨ tr.cell tt r eN = 1) ∧
      (tr.cell tt r eN = 1 ↔ bv tr tt r dNb = 0) := by
  have hb := isBool hL hr (x := eN) (by simp [boolCols])
  have hd := bv_lt hL hr dNb_bool
  have e1 := con hL hr (mem_chains (e := .mul (c act) (.mul dN (c eN))) (by simp [cChains, chain]))
  have e2 := con hL hr (mem_chains (e := .mul (c act) (sub (.mul dN (c iN)) (not (c eN))))
    (by simp [cChains, chain]))
  simp only [dN, byteC, eval_mul, eval_sub, eval_c, eval_not, ha, eval_byte hL hr dNb_bool] at e1 e2
  refine ⟨hb, ⟨fun h => ?_, fun h => ?_⟩⟩
  · rw [h] at e1
    have : ((bv tr tt r dNb : Nat) : Fp) = ((0 : Nat) : Fp) := by grind
    exact natEq (by unfold P; omega) (by unfold P; omega) this
  · rw [h] at e2
    rcases hb with hb | hb
    · rw [hb] at e2
      exfalso
      have : (1 : Fp) = 0 := by
        have h0 : ((0 : Nat) : Fp) = 0 := rfl
        rw [h0] at e2; grind
      exact fp_one_ne_zero this
    · exact hb

theorem zN_iff {s : Nat} (hop : OpAt tr tt s) :
    ∀ k, k < 16 → ((tr.cell tt (s + k) zN = 0 ∨ tr.cell tt (s + k) zN = 1) ∧
      (tr.cell tt (s + k) zN = 1 ↔ ∀ i, i ≤ k → bv tr tt (s + i) dNb = 0)) := by
  have hH := hop.h
  intro k
  induction k with
  | zero =>
    intro _
    have e := con hL (r := s) (by omega)
      (mem_chains (e := first (sub (c zN) (c eN))) (by simp [cChains, chain]))
    have hlf := hop.lf 0 (by omega)
    simp only [Nat.add_zero, ite_true] at hlf
    simp only [first, eval_mul, eval_sub, eval_c, hlf, Nat.add_zero] at e
    have hz : tr.cell tt s zN = tr.cell tt s eN := by grind
    have hf := eN_facts hL (r := s) (by omega) (by simpa using hop.act 0 (by omega))
    simp only [Nat.add_zero, hz]
    refine ⟨hf.1, ⟨fun h i hi => ?_, fun h => hf.2.2 (by simpa using h 0 (by omega))⟩⟩
    have : i = 0 := by omega
    subst this; simpa using hf.2.1 h
  | succ k ih =>
    intro hk
    have hac := hop.act k (by omega)
    have hl := hop.ll k (by omega)
    rw [if_neg (by omega)] at hl
    have hn : s + k + 1 < tr.height tt := by omega
    have e := con hL (r := s + k) (by omega)
      (mem_chains (e := inOpE (sub (n zN) (.mul (c zN) (n eN)))) (by simp [cChains, chain]))
    simp only [inOpE, inOp, eval_mul, eval_sub, eval_c, eval_n, eval_not, hac, hl, nxt hn] at e
    have hz : tr.cell tt (s + k + 1) zN = tr.cell tt (s + k) zN * tr.cell tt (s + k + 1) eN := by grind
    have hf := eN_facts hL (r := s + k + 1) (by omega) (by simpa [← Nat.add_assoc] using hop.act (k + 1) hk)
    obtain ⟨hb, hi⟩ := ih (by omega)
    rw [← Nat.add_assoc, hz]
    have hdk : tr.cell tt (s + k + 1) eN = 1 ↔ bv tr tt (s + (k + 1)) dNb = 0 := by
      rw [← Nat.add_assoc]; exact hf.2
    rcases hb with hb | hb
    · rw [hb]
      refine ⟨Or.inl (by grind), ⟨fun h => absurd (h.symm.trans (by grind)) fp_one_ne_zero, fun h => ?_⟩⟩
      have := hi.2 (fun i hi' => h i (by omega))
      rw [hb] at this; exact absurd this fp_zero_ne_one
    · rcases hf.1 with he | he
      · rw [hb, he]
        refine ⟨Or.inl (by grind), ⟨fun h => absurd (h.symm.trans (by grind)) fp_one_ne_zero,
          fun h => ?_⟩⟩
        have := hdk.2 (h (k + 1) (by omega))
        rw [he] at this; exact absurd this fp_zero_ne_one
      · rw [hb, he]
        refine ⟨Or.inr (by grind), ⟨fun _ i hi' => ?_, fun _ => by grind⟩⟩
        rcases Nat.lt_or_ge i (k + 1) with h1 | h1
        · exact hi.1 hb i (by omega)
        · have : i = k + 1 := by omega
          subst this
          exact hdk.1 he

end

end ZkFormal.NearV3.D1.TxProof
