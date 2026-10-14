import ZkFormal.NearV3.D1.Extract.Tx.Rows
import ZkFormal.Near.Extract.RcptArithCore

/-!
# `ZkFormal.NearV3.D1.Extract.Tx.Lane` — per-lane equations of the `txV3` byte chains

Lane `v3-d1-phase2` (milestone V2).  For an op starting at row `s` (`segInfo`), each chain's
constraint on lane `j` (the `lf` row for `j = 0`, the `inOp` transition `j − 1 → j` otherwise) as
an equation of naturals `sₖ + 256·coutₖ = aₖ + cinₖ`, ready for `RcptProof.chainC`.
-/

namespace ZkFormal.NearV3.D1.TxProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.D1
  ZkFormal.NearV3.D1.TxV3

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

/-- A byte column group `f 0 … f 7` of row `r` as a natural. -/
def bv (tr : Trace Fp) (tt r : Nat) (f : Nat → Nat) (len : Nat := 8) : Nat :=
  bitsVal (fun b => cv tr tt r (f b)) 0 len

/-- The op's view of row `s + j`. -/
structure OpAt (tr : Trace Fp) (tt s : Nat) : Prop where
  h : s + 16 ≤ tr.height tt
  act : ∀ j, j < 16 → tr.cell tt (s + j) act = 1
  lane : ∀ j, j < 16 → tr.cell tt (s + j) lane = ((j : Nat) : Fp)
  lf : ∀ j, j < 16 → tr.cell tt (s + j) lf = (if j = 0 then 1 else 0)
  l1 : ∀ j, j < 16 → tr.cell tt (s + j) l1 = (if j = 1 then 1 else 0)
  ll : ∀ j, j < 16 → tr.cell tt (s + j) ll = (if j = 15 then 1 else 0)
  const : ∀ j, j < 16 → ∀ x ∈ opConst, tr.cell tt (s + j) x = tr.cell tt s x

section
variable (hL : TableLocal TxV3.table tr tt pub)
include hL

theorem opAt_of {s ℓ : Nat}
    (hseg : IsSeg (isOne tr tt act) (isOne tr tt lf) (isOne tr tt ll) s ℓ) (hH : s + ℓ ≤ tr.height tt) :
    ℓ = 16 ∧ OpAt tr tt s := by
  obtain ⟨h16, hr⟩ := segInfo hL hseg hH
  subst h16
  exact ⟨rfl, hH, fun j hj => (hr j hj).1, fun j hj => (hr j hj).2.1, fun j hj => (hr j hj).2.2.1,
    fun j hj => (hr j hj).2.2.2.1, fun j hj => (hr j hj).2.2.2.2.1, fun j hj => (hr j hj).2.2.2.2.2⟩

theorem bitB {r : Nat} (hr : r < tr.height tt) {f : Nat → Nat} {len : Nat}
    (hf : ∀ b, b < len → f b ∈ boolCols) :
    ∀ b, b < len → tr.cell tt r (f (0 + b)) = 0 ∨ tr.cell tt r (f (0 + b)) = 1 :=
  fun b hb => by rw [Nat.zero_add]; exact isBool hL hr (hf b hb)

theorem eval_byte {r : Nat} (hr : r < tr.height tt) {f : Nat → Nat} {len : Nat}
    (hf : ∀ b, b < len → f b ∈ boolCols) :
    (bits (fun x => c (f x)) 0 len).eval tr tt r pub = ((bv tr tt r f len : Nat) : Fp) :=
  eval_bits tr tt r pub f 0 len (bitB hL hr hf)

theorem bv_lt {r : Nat} (hr : r < tr.height tt) {f : Nat → Nat} {len : Nat}
    (hf : ∀ b, b < len → f b ∈ boolCols) : bv tr tt r f len < 2 ^ len :=
  bitsVal_lt _ 0 len (fun b hb => cv_bool (bitB hL hr hf b hb))

theorem cv_bool' {r : Nat} (hr : r < tr.height tt) {x : Nat} (hx : x ∈ boolCols) :
    cv tr tt r x ≤ 1 := cv_bool (isBool hL hr hx)

end

theorem eval_bitsN {r : Nat} (hr : r + 1 < tr.height tt) (f : Nat → Nat) (len : Nat) :
    (bits (fun x => n (f x)) 0 len).eval tr tt r pub =
      (bits (fun x => c (f x)) 0 len).eval tr tt (r + 1) pub := by
  induction len with
  | zero => rfl
  | succ len ih =>
    rw [bits_succ, bits_succ, eval_sum_append, eval_sum_append,
      show sum ((List.range len).map fun b => smul (2 ^ b) ((fun x => n (f x)) (0 + b))) =
        bits (fun x => n (f x)) 0 len from rfl,
      show sum ((List.range len).map fun b => smul (2 ^ b) ((fun x => c (f x)) (0 + b))) =
        bits (fun x => c (f x)) 0 len from rfl, ih]
    simp only [eval_sum_cons, eval_sum_nil, eval_smul, eval_n, eval_c, nxt hr]

theorem natEq {x y : Nat} (hx : x < P) (hy : y < P) (h : (x : Fp) = (y : Fp)) : x = y :=
  ofNat_inj hx hy h

theorem P_big : 2 ^ 20 < P := by unfold P; omega

end ZkFormal.NearV3.D1.TxProof
