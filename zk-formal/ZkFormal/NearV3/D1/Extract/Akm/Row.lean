import ZkFormal.NearV3.D1.Extract.Akm.Rows

/-!
# `ZkFormal.NearV3.D1.Extract.Akm.Row` — per-row facts of `akmV3`

The value byte `bvA`, the one-hot state, the field-end test `fe = [lastE = 0]`, the in-field
transitions, `al ⇔ endOK`.
-/

namespace ZkFormal.NearV3.D1.AkmProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.D1
  ZkFormal.NearV3.D1.AkmV3

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

/-- The value byte of row `r`. -/
def bvA (tr : Trace Fp) (tt r : Nat) : Nat := bitsVal (fun b => cv tr tt r (bb b)) 0 8

theorem bb_bool : ∀ b, b < 8 → bb b ∈ boolCols := by intro b hb; simp [boolCols, bb, hb]
theorem states_bool : ∀ x ∈ states, x ∈ boolCols := by
  intro x hx; simp only [states, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [boolCols, states]

section
variable (hL : TableLocal AkmV3.table tr tt pub)
include hL

theorem eval_bE {r : Nat} (hr : r < tr.height tt) : bE.eval tr tt r pub = ((bvA tr tt r : Nat) : Fp) :=
  eval_bits tr tt r pub bb 0 8 (fun b hb => by rw [Nat.zero_add]; exact isBool hL hr (bb_bool b hb))

theorem bvA_lt {r : Nat} (hr : r < tr.height tt) : bvA tr tt r < 256 :=
  bitsVal_lt _ 0 8 (fun b hb => cv_bool (by rw [Nat.zero_add]; exact isBool hL hr (bb_bool b hb)))

/-- **One-hot state.** -/
theorem oneHot {r : Nat} (hr : r < tr.height tt) (ha : tr.cell tt r act = 1) {x : Nat} (hx : x ∈ states)
    (h1 : tr.cell tt r x = 1) : ∀ y ∈ states, y ≠ x → tr.cell tt r y = 0 := by
  have e := con hL hr (mem_shape (e := sub (sum (states.map c)) (c act)) (by simp [cShape]))
  simp only [states, List.map_cons, List.map_nil, eval_sub, eval_sum_cons, eval_sum_nil, eval_c, ha] at e
  have b := fun y (hy : y ∈ states) => cv_bool (isBool hL hr (states_bool y hy))
  have hs : cv tr tt r sN + cv tr tt r sT + cv tr tt r sG + cv tr tt r sO + cv tr tt r sA +
      cv tr tt r sL + cv tr tt r sS + cv tr tt r sC = 1 := by
    have b1 := b sN (by simp [states]); have b2 := b sT (by simp [states])
    have b3 := b sG (by simp [states]); have b4 := b sO (by simp [states])
    have b5 := b sA (by simp [states]); have b6 := b sL (by simp [states])
    have b7 := b sS (by simp [states]); have b8 := b sC (by simp [states])
    apply ofNat_inj (by unfold P; omega) (by unfold P; omega)
    simp only [natCast_add, ← cell_eq_cast]
    rw [show ((1 : Nat) : Fp) = 1 from rfl]; grind
  have hx1 : cv tr tt r x = 1 := by unfold cv; rw [h1]; rfl
  intro y hy hne
  have hy0 : cv tr tt r y = 0 := by
    simp only [states, List.mem_cons, List.not_mem_nil, or_false] at hx hy
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | exact absurd rfl hne | omega
  rw [cell_eq_cast, hy0]; rfl

/-- `lastE` on a row in state `x` (`x ≠ sS`): `ix − (len − 1)`. -/
theorem lastE_fixed {r : Nat} (hr : r < tr.height tt) (ha : tr.cell tt r act = 1) {x : Nat} (hx : x ∈ states)
    (h1 : tr.cell tt r x = 1) (hS : x ≠ sS) {L : Nat}
    (hL' : (x = sN ∧ L = 7) ∨ (x = sT ∧ L = 0) ∨ (x = sG ∧ L = 17) ∨ (x = sO ∧ L = 0) ∨
      (x = sA ∧ L = 15) ∨ (x = sL ∧ L = 3) ∨ (x = sC ∧ L = 3)) :
    lastE.eval tr tt r pub = tr.cell tt r ix - ((L : Nat) : Fp) := by
  have z := oneHot hL hr ha hx h1
  simp only [lastE, eval_sum_cons, eval_sum_nil, eval_mul, eval_sub, eval_c, eval_k]
  rcases hL' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  · rw [h1]
    (try rw [z sN (by simp [states]) (by decide)]); (try rw [z sT (by simp [states]) (by decide)])
    (try rw [z sG (by simp [states]) (by decide)]); (try rw [z sO (by simp [states]) (by decide)])
    (try rw [z sA (by simp [states]) (by decide)]); (try rw [z sL (by simp [states]) (by decide)])
    (try rw [z sC (by simp [states]) (by decide)]); (try rw [z sS (by simp [states]) (by decide)])
    grind

theorem lastE_S {r : Nat} (hr : r < tr.height tt) (ha : tr.cell tt r act = 1) (h1 : tr.cell tt r sS = 1) :
    lastE.eval tr tt r pub = tr.cell tt r rem - ((1 : Nat) : Fp) := by
  have z := oneHot hL hr ha (by simp [states]) h1
  simp only [lastE, eval_sum_cons, eval_sum_nil, eval_mul, eval_sub, eval_c, eval_k]
  rw [h1, z sN (by simp [states]) (by decide), z sT (by simp [states]) (by decide),
    z sG (by simp [states]) (by decide), z sO (by simp [states]) (by decide),
    z sA (by simp [states]) (by decide), z sL (by simp [states]) (by decide),
    z sC (by simp [states]) (by decide)]
  grind

/-- `fe = [lastE = 0]` on active rows. -/
theorem fe_iff {r : Nat} (hr : r < tr.height tt) (ha : tr.cell tt r act = 1) :
    (tr.cell tt r fe = 0 ∨ tr.cell tt r fe = 1) ∧ (tr.cell tt r fe = 1 ↔ lastE.eval tr tt r pub = 0) := by
  have hb := isBool hL hr (x := fe) (by simp [boolCols])
  have e1 := con hL hr (mem_fields (e := .mul (c act) (.mul lastE (c fe))) (by simp [cFields]))
  have e2 := con hL hr (mem_fields (e := .mul (c act) (sub (.mul lastE (c invE)) (not (c fe))))
    (by simp [cFields]))
  simp only [eval_mul, eval_sub, eval_c, eval_not, ha] at e1 e2
  refine ⟨hb, fun h => ?_, fun h => ?_⟩
  · rw [h] at e1; grind
  · rw [h] at e2
    rcases hb with hb | hb
    · rw [hb] at e2; exact absurd (by grind) fp_zero_ne_one
    · exact hb

/-- Not at a field end ⇒ not the segment's last row. -/
theorem Row_al_zero {r : Nat} (hr : r < tr.height tt) (ha : tr.cell tt r act = 1)
    (hf : tr.cell tt r fe = 0) : tr.cell tt r al = 0 := by
  have e0 := con hL hr (mem_fields (e := .mul (not (c fe)) (c al)) (by simp [cFields]))
  simp only [eval_mul, eval_c, eval_not, hf] at e0; grind

/-- Inside a field (`fe = 0`): the segment goes on, same state, next index, same `mth`. -/
theorem inside {r : Nat} (hr : r + 1 < tr.height tt) (ha : tr.cell tt r act = 1)
    (hf : tr.cell tt r fe = 0) :
    tr.cell tt r al = 0 ∧ tr.cell tt (r + 1) ix = tr.cell tt r ix + 1 ∧
    tr.cell tt (r + 1) mth = tr.cell tt r mth ∧
    (∀ x ∈ states, tr.cell tt (r + 1) x = tr.cell tt r x) ∧
    (tr.cell tt r sS = 1 → tr.cell tt (r + 1) rem = tr.cell tt r rem - 1) := by
  have hr' : r < tr.height tt := by omega
  have e0 := con hL hr' (mem_fields (e := .mul (not (c fe)) (c al)) (by simp [cFields]))
  have e1 := con hL hr' (mem_fields (e := mul3 (c act) (not (c fe)) (sub (n ix) (.add (c ix) (k 1))))
    (by simp [cFields]))
  have e2 := con hL hr' (mem_fields (e := mul3 (c act) (not (c fe)) (sub (n mth) (c mth)))
    (by simp [cFields]))
  have e3 := con hL hr' (mem_fields (e := mul3 (c sS) (not (c fe)) (sub (n rem) (sub (c rem) (k 1))))
    (by simp [cFields]))
  simp only [eval_mul, eval_mul3, eval_sub, eval_add, eval_c, eval_n, eval_not, eval_k, ha, hf, nxt hr]
    at e0 e1 e2 e3
  refine ⟨by grind, by grind, by grind, fun x hx => ?_, fun h => by rw [h] at e3; grind⟩
  have e4 := con hL hr' (mem_fields (e := mul3 (c act) (not (c fe)) (sub (n x) (c x))) (by
    simp only [cFields, List.mem_append, List.mem_map]
    exact Or.inl (Or.inr ⟨x, hx, rfl⟩)))
  simp only [eval_mul3, eval_sub, eval_c, eval_n, eval_not, ha, hf, nxt hr] at e4
  grind

/-- A field end that does not end the segment: the next row starts a field (`ix = 0`). -/
theorem fgo_next {r : Nat} (hr : r + 1 < tr.height tt) (hf : tr.cell tt r fe = 1)
    (hl : tr.cell tt r al = 0) : tr.cell tt r fgo = 1 ∧ tr.cell tt (r + 1) ix = 0 := by
  have hr' : r < tr.height tt := by omega
  have e1 := con hL hr' (mem_fields (e := sub (c fgo) (.mul (c fe) (not (c al)))) (by simp [cFields]))
  have e2 := con hL hr' (mem_fields (e := .mul (c fgo) (n ix)) (by simp [cFields]))
  simp only [eval_mul, eval_sub, eval_c, eval_n, eval_not, hf, hl, nxt hr] at e1 e2
  have : tr.cell tt r fgo = 1 := by grind
  rw [this] at e2; exact ⟨this, by grind⟩

/-- `al = endOK` on active rows. -/
theorem al_endOK {r : Nat} (hr : r < tr.height tt) (ha : tr.cell tt r act = 1) :
    tr.cell tt r al = tr.cell tt r endOK := by
  have e := con hL hr (mem_events (e := .mul (c act) (sub (c al) (c endOK))) (by simp [cEvents]))
  simp only [eval_mul, eval_sub, eval_c, ha] at e; grind

end

end ZkFormal.NearV3.D1.AkmProof
