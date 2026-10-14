import ZkFormal.NearV3.D1.Extract.Akm.Utf8Row

/-!
# `ZkFormal.NearV3.D1.Extract.Akm.Utf8Body` — a string body of `akmV3` is well-formed UTF-8
-/

namespace ZkFormal.NearV3.D1.AkmProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.D1
  ZkFormal.NearV3.D1.AkmV3

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

section
variable (hL : TableLocal AkmV3.table tr tt pub)
include hL

theorem bitsLow {r : Nat} (hr : r < tr.height tt) (len : Nat) (hl : len ≤ 8) :
    (bits (fun x => c (bb x)) 0 len).eval tr tt r pub =
      ((bitsVal (fun b => cv tr tt r (bb b)) 0 len : Nat) : Fp) :=
  eval_bits tr tt r pub bb 0 len (fun b hb => by rw [Nat.zero_add]; exact isBool hL hr (bb_bool b (by omega)))

/-- The continuation row's bits 7 / 6. -/
theorem cont_bits {r : Nat} (hr : r < tr.height tt) (hS : tr.cell tt r sS = 1) (hk : clsOf tr tt r = 1) :
    bit tr tt r 7 = 1 ∧ bit tr tt r 6 = 0 := by
  have hC : tr.cell tt r cC = 1 := by
    unfold clsOf at hk; split at hk
    · assumption
    · repeat (split at hk <;> try omega)
  exact ⟨bit_one (cl_one hL hr (i := 7) hC (by simp [cUtf8])), bit_zero (cl_zero hL hr (i := 6) hC (by simp [cUtf8]))⟩

theorem cls_cell {r : Nat} (hr : r < tr.height tt) {n : Nat} (hk : clsOf tr tt r = n) (hn : n = 3 ∨ n = 4) :
    (n = 3 → tr.cell tt r c3 = 1) ∧ (n = 4 → tr.cell tt r c4 = 1) := by
  unfold clsOf at hk
  by_cases hC : tr.cell tt r cC = 1
  · rw [if_pos hC] at hk; omega
  rw [if_neg hC] at hk
  by_cases h2 : tr.cell tt r c2 = 1
  · rw [if_pos h2] at hk; omega
  rw [if_neg h2] at hk
  by_cases h3 : tr.cell tt r c3 = 1
  · rw [if_pos h3] at hk; exact ⟨fun _ => h3, fun h => by omega⟩
  rw [if_neg h3] at hk
  by_cases h4 : tr.cell tt r c4 = 1
  · rw [if_pos h4] at hk; exact ⟨fun h => by omega, fun _ => h4⟩
  rw [if_neg h4] at hk; omega

/-- **A string body is UTF-8.** -/
theorem body_utf8 {s ℓ : Nat} (seg : SegAt tr tt s ℓ) {p R : Nat} (hp : p < ℓ)
    (hX : tr.cell tt (s + p) sS = 1) (hrem : tr.cell tt (s + p) rem = ((R : Nat) : Fp))
    (hR : 1 ≤ R) (hRP : R < P) (hu0 : tr.cell tt (s + p) uc = 0) :
    NearSpecV3.utf8Ok ((List.range' p R).map fun i => UInt8.ofNat (bvA tr tt (s + i))) = true := by
  have hH := seg.h
  have B := body hL seg hp hX hrem hR hRP
  have hrow : ∀ j, j < R → s + p + j < tr.height tt := fun j hj => by have := (B j hj).1; omega
  have hS : ∀ j, j < R → tr.cell tt (s + p + j) sS = 1 := fun j hj => (B j hj).2.1
  have hfe0 : ∀ j, j + 1 < R → tr.cell tt (s + p + j) fe = 0 := fun j hj => ((B j (by omega)).2.2.2.2.1 hj).1
  have hact : ∀ j, j < R → tr.cell tt (s + p + j) act = 1 := fun j hj => by
    have := seg.act (p + j) (B j hj).1; rwa [← Nat.add_assoc] at this
  -- flags on the byte after a lead (`j + 1 < R`)
  have second : ∀ j, j + 1 < R → ∀ {pf cl z : Nat}, mul3 (c sS) (not (c fe)) (sub (n pf) (.mul (c cl) (c z))) ∈ cUtf8 →
      tr.cell tt (s + p + j) cl = 1 → tr.cell tt (s + p + j) z = 1 → tr.cell tt (s + p + (j + 1)) pf = 1 :=
    fun j hj _ _ _ hm hc hz => by
      rw [← Nat.add_assoc]
      exact flag_next hL (hrow (j + 1) hj) (hS j (by omega)) (hfe0 j hj) hm hc hz
  have xb := fun j (hj : j < R) => bvA_bits (tr := tr) (tt := tt) (s + p + j)
  have bl := fun j (hj : j < R) (i : Nat) (hi : i < 8) => bit_le hL (hrow j hj) i hi
  have H : U8Rows R (fun j => bvA tr tt (s + p + j)) (fun j => clsOf tr tt (s + p + j))
      (fun j => tr.cell tt (s + p + j) uc) (fun _ => false) (fun _ => false) (fun _ => false) (fun _ => false) := by
    refine ⟨fun j hj => classOk_row hL (hrow j hj) (hS j hj), fun j hj hk => lead_row hL (hrow j hj) (hS j hj) hk,
      fun j hj => ?_, ?_, fun _ => by simpa using hu0, ?_, ?_, ?_, ?_⟩
    · show tr.cell tt (s + p + (j + 1)) uc = ucnF (clsOf tr tt (s + p + j)) (tr.cell tt (s + p + j) uc)
      have h1 : tr.cell tt (s + p + j + 1) uc = tr.cell tt (s + p + j) ucn :=
        step_row hL (r := s + p + j) (by have := hrow (j + 1) hj; omega) (hS j (by omega)) (hfe0 j hj)
      rw [← Nat.add_assoc, h1, ucn_row hL (hrow j (by omega)) (hS j (by omega))]
    · intro _
      show ucnF (clsOf tr tt (s + p + (R - 1))) (tr.cell tt (s + p + (R - 1)) uc) = 0
      rw [← ucn_row hL (hrow (R - 1) (by omega)) (hS (R - 1) (by omega))]
      exact stop_row hL (hrow (R - 1) (by omega)) (hS (R - 1) (by omega))
        ((B (R - 1) (by omega)).2.2.2.2.2 (by omega))
    · -- E0: second byte A0–BF
      intro j hj hk hx hk1
      have hc3 := (cls_cell hL (hrow j (by omega)) hk (Or.inl rfl)).1 rfl
      have x0 := xb j (by omega); have hx' : bvA tr tt (s + p + j) = _ := hx
      have b := fun i (hi : i < 8) => bl j (by omega) i hi
      have hz := ztest hL (hrow j (by omega)) (hact j (by omega)) (e := loE) (z := zl0) (i := il0)
        (by simp [cUtf8]) (by simp [cUtf8]) (by
          unfold loE; rw [bitsLow hL (hrow j (by omega)) 4 (by omega)]
          simp only [bitsVal, Nat.zero_add, Nat.reducePow, Nat.one_mul]
          have := b 0 (by omega); have := b 1 (by omega); have := b 2 (by omega); have := b 3 (by omega)
          have := b 4 (by omega); have := b 5 (by omega); have := b 6 (by omega); have := b 7 (by omega)
          have h0 : cv tr tt (s + p + j) (bb 0) + 2 * cv tr tt (s + p + j) (bb 1) + 4 * cv tr tt (s + p + j) (bb 2) +
            8 * cv tr tt (s + p + j) (bb 3) = 0 := by simp only [bit] at *; omega
          rw [h0]; rfl)
      have hp1 := second j hj (pf := pE0) (by simp [cUtf8]) hc3 hz
      have e := con hL (hrow (j + 1) hj) (uc_mem (e := mul3 (c sS) (c pE0) (not (bt 5))) (by simp [cUtf8]))
      rw [← Nat.add_assoc] at hp1
      simp only [bt, eval_mul3, eval_not, eval_c, hS (j + 1) hj, hp1] at e
      have b5 := bit_one (show tr.cell tt (s + p + (j + 1)) (bb 5) = 1 by grind)
      have cb := cont_bits hL (hrow (j + 1) hj) (hS (j + 1) hj) hk1
      have x1 := xb (j + 1) hj; have := bl (j + 1) hj 4 (by omega)
      show 0xA0 ≤ bvA tr tt (s + p + (j + 1)); omega
    · intro j hj hk hx hk1
      have hc3 := (cls_cell hL (hrow j (by omega)) hk (Or.inl rfl)).1 rfl
      have x0 := xb j (by omega); have hx' : bvA tr tt (s + p + j) = _ := hx
      have b := fun i (hi : i < 8) => bl j (by omega) i hi
      have hz := ztest hL (hrow j (by omega)) (hact j (by omega)) (e := sub loE (k 13)) (z := zl13) (i := il13)
        (by simp [cUtf8]) (by simp [cUtf8]) (by
          simp only [eval_sub, eval_k]
          unfold loE; rw [bitsLow hL (hrow j (by omega)) 4 (by omega)]
          simp only [bitsVal, Nat.zero_add, Nat.reducePow, Nat.one_mul]
          have := b 0 (by omega); have := b 1 (by omega); have := b 2 (by omega); have := b 3 (by omega)
          have := b 4 (by omega); have := b 5 (by omega); have := b 6 (by omega); have := b 7 (by omega)
          have h0 : cv tr tt (s + p + j) (bb 0) + 2 * cv tr tt (s + p + j) (bb 1) + 4 * cv tr tt (s + p + j) (bb 2) +
            8 * cv tr tt (s + p + j) (bb 3) = 13 := by simp only [bit] at *; omega
          rw [h0]; grind)
      have hp1 := second j hj (pf := pED) (by simp [cUtf8]) hc3 hz
      have e := con hL (hrow (j + 1) hj) (uc_mem (e := mul3 (c sS) (c pED) (bt 5)) (by simp [cUtf8]))
      rw [← Nat.add_assoc] at hp1
      simp only [bt, eval_mul3, eval_c, hS (j + 1) hj, hp1] at e
      have b5 := bit_zero (show tr.cell tt (s + p + (j + 1)) (bb 5) = 0 by grind)
      have cb := cont_bits hL (hrow (j + 1) hj) (hS (j + 1) hj) hk1
      have x1 := xb (j + 1) hj
      have := bl (j + 1) hj 0 (by omega); have := bl (j + 1) hj 1 (by omega); have := bl (j + 1) hj 2 (by omega)
      have := bl (j + 1) hj 3 (by omega); have := bl (j + 1) hj 4 (by omega)
      show bvA tr tt (s + p + (j + 1)) ≤ 0x9F; omega
    · intro j hj hk hx hk1
      have hc4 := (cls_cell hL (hrow j (by omega)) hk (Or.inr rfl)).2 rfl
      have x0 := xb j (by omega); have hx' : bvA tr tt (s + p + j) = _ := hx
      have b := fun i (hi : i < 8) => bl j (by omega) i hi
      have hz := ztest hL (hrow j (by omega)) (hact j (by omega)) (e := lo3E) (z := z30) (i := i30)
        (by simp [cUtf8]) (by simp [cUtf8]) (by
          unfold lo3E; rw [bitsLow hL (hrow j (by omega)) 3 (by omega)]
          simp only [bitsVal, Nat.zero_add, Nat.reducePow, Nat.one_mul]
          have := b 0 (by omega); have := b 1 (by omega); have := b 2 (by omega); have := b 3 (by omega)
          have := b 4 (by omega); have := b 5 (by omega); have := b 6 (by omega); have := b 7 (by omega)
          have h0 : cv tr tt (s + p + j) (bb 0) + 2 * cv tr tt (s + p + j) (bb 1) + 4 * cv tr tt (s + p + j) (bb 2) = 0 := by simp only [bit] at *; omega
          rw [h0]; rfl)
      have hp1 := second j hj (pf := pF0) (by simp [cUtf8]) hc4 hz
      have e := con hL (hrow (j + 1) hj) (uc_mem (e := .mul (mul3 (c sS) (c pF0) (not (bt 5))) (not (bt 4)))
        (by simp [cUtf8]))
      rw [← Nat.add_assoc] at hp1
      simp only [bt, eval_mul3, eval_mul, eval_not, eval_c, hS (j + 1) hj, hp1] at e
      have cb := cont_bits hL (hrow (j + 1) hj) (hS (j + 1) hj) hk1
      have x1 := xb (j + 1) hj
      have := bl (j + 1) hj 0 (by omega); have := bl (j + 1) hj 1 (by omega); have := bl (j + 1) hj 2 (by omega)
      have := bl (j + 1) hj 3 (by omega)
      show 0x90 ≤ bvA tr tt (s + p + (j + 1))
      rcases isBool hL (hrow (j + 1) hj) (bb_bool 5 (by omega)) with q5 | q5
      · rw [q5] at e
        have q4 : tr.cell tt (s + p + (j + 1)) (bb 4) = 1 := by grind
        have := bit_one q4; have := bit_zero q5; omega
      · have := bit_one q5; have := bl (j + 1) hj 4 (by omega); omega
    · intro j hj hk hx hk1
      have hc4 := (cls_cell hL (hrow j (by omega)) hk (Or.inr rfl)).2 rfl
      have x0 := xb j (by omega); have hx' : bvA tr tt (s + p + j) = _ := hx
      have b := fun i (hi : i < 8) => bl j (by omega) i hi
      have hz := ztest hL (hrow j (by omega)) (hact j (by omega)) (e := sub lo3E (k 4)) (z := z34) (i := i34)
        (by simp [cUtf8]) (by simp [cUtf8]) (by
          simp only [eval_sub, eval_k]
          unfold lo3E; rw [bitsLow hL (hrow j (by omega)) 3 (by omega)]
          simp only [bitsVal, Nat.zero_add, Nat.reducePow, Nat.one_mul]
          have := b 0 (by omega); have := b 1 (by omega); have := b 2 (by omega); have := b 3 (by omega)
          have := b 4 (by omega); have := b 5 (by omega); have := b 6 (by omega); have := b 7 (by omega)
          have h0 : cv tr tt (s + p + j) (bb 0) + 2 * cv tr tt (s + p + j) (bb 1) + 4 * cv tr tt (s + p + j) (bb 2) = 4 := by simp only [bit] at *; omega
          rw [h0]; grind)
      have hp1 := second j hj (pf := pF4) (by simp [cUtf8]) hc4 hz
      have e5 := con hL (hrow (j + 1) hj) (uc_mem (e := mul3 (c sS) (c pF4) (bt 5)) (by simp [cUtf8]))
      have e4 := con hL (hrow (j + 1) hj) (uc_mem (e := mul3 (c sS) (c pF4) (bt 4)) (by simp [cUtf8]))
      rw [← Nat.add_assoc] at hp1
      simp only [bt, eval_mul3, eval_c, hS (j + 1) hj, hp1] at e5 e4
      have b5 := bit_zero (show tr.cell tt (s + p + (j + 1)) (bb 5) = 0 by grind)
      have b4 := bit_zero (show tr.cell tt (s + p + (j + 1)) (bb 4) = 0 by grind)
      have cb := cont_bits hL (hrow (j + 1) hj) (hS (j + 1) hj) hk1
      have x1 := xb (j + 1) hj
      have := bl (j + 1) hj 0 (by omega); have := bl (j + 1) hj 1 (by omega); have := bl (j + 1) hj 2 (by omega)
      have := bl (j + 1) hj 3 (by omega)
      show bvA tr tt (s + p + (j + 1)) ≤ 0x8F; omega
  have := utf8_rows H hRP R 0 (by omega) (Or.inr (by simpa using hu0))
  rw [List.range'_eq_map_range, List.map_map] at this ⊢
  simpa [Function.comp_def, Nat.add_assoc] using this

end

end ZkFormal.NearV3.D1.AkmProof
