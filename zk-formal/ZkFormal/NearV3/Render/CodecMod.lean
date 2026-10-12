import ZkFormal.NearV3.Render.CodecDefs

/-! The modular constraints (`modE`) on honest codec rows, over the field. -/
namespace ZkFormal.NearV3.Render.Cdc
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.NearV3.Sched.Codec ZkFormal.Chacha.Table.E ZkFormal.NearV3.Candidates

section
variable {tr : Trace Fp} {t r : Nat} {pub : List Fp}

theorem diff_inv (a b : Nat) (ha : a < P) (hb : b < P) :
    (Fp.ofNat a - Fp.ofNat b) * Fp.ofNat (inv (fsub a b)) = if a = b then 0 else 1 := by
  rw [inv_eq, ← SchedField.fsub_cast, SchedField.inverse_product]
  have := ProcKeyInverse.difference_zero a b ha hb
  by_cases h : a = b
  · rw [if_pos (this.mpr h), if_pos h]
  · rw [if_neg (fun h' => h (this.mp h')), if_neg h]

/-- An `isZ` inverse test with honest cells. -/
theorem isZ_mod (gate X : Expr) (iv fl a b : Nat) (ha : a < P) (hb : b < P)
    (hX : zev (tenv tr t r pub) X = (a : Int) - b)
    (hi : (tenv tr t r pub).cur iv = inv (fsub a b))
    (hf : (tenv tr t r pub).cur fl = if a = b then 1 else 0) :
    (Expr.mul gate (sub (c fl) (notE (.mul X (c iv))))).eval tr t r pub = 0 := by
  rw [eval_eq]
  simp only [zev_mul, zev_sub, zev_c, zev_k, notE, hX, hi, hf]
  have hd := diff_inv a b ha hb
  have c1 : ((a : Int) : Fp) = Fp.ofNat a := intCast_ofNat a
  have c2 : ((b : Int) : Fp) = Fp.ofNat b := intCast_ofNat b
  have c3 : (((inv (fsub a b) : Nat) : Int) : Fp) = Fp.ofNat (inv (fsub a b)) := intCast_ofNat _
  by_cases h : a = b
  · rw [if_pos h] at hd ⊢
    have c4 : (((1 : Nat) : Int) : Fp) = 1 := intCast_ofNat 1
    push_cast
    grind
  · rw [if_neg h] at hd ⊢
    push_cast
    grind

/-- A constraint `gate · y` with a vanishing gate. -/
theorem gate_zero (gate y : Expr) (hg : zev (tenv tr t r pub) gate = 0) :
    (Expr.mul gate y).eval tr t r pub = 0 := by
  rw [eval_eq]; simp only [zev_mul, hg, Int.zero_mul]; rfl

/-- `nzb = bpre · ib` on an allowance byte. -/
theorem nzb_mod (x : Nat) (hx : x < P)
    (hb : (tenv tr t r pub).cur bpre = x) (hi : (tenv tr t r pub).cur ib = inv x)
    (hn : (tenv tr t r pub).cur nzb = if x = 0 then 0 else 1) :
    (Expr.mul (c fA) (sub (c nzb) (.mul (c bpre) (c ib)))).eval tr t r pub = 0 := by
  rw [eval_eq]
  simp only [zev_mul, zev_sub, zev_c, hb, hi, hn]
  have hp := SchedField.inverse_product x
  rw [← inv_eq] at hp
  have hm : x % P = 0 ↔ x = 0 := by rw [Nat.mod_eq_of_lt hx]
  have c1 : ((x : Int) : Fp) = Fp.ofNat x := intCast_ofNat x
  have c3 : (((inv x : Nat) : Int) : Fp) = Fp.ofNat (inv x) := intCast_ofNat _
  by_cases h : x = 0
  · rw [if_pos (hm.mpr h)] at hp; rw [if_pos h]; push_cast; grind
  · rw [if_neg (fun h' => h (hm.mp h'))] at hp; rw [if_neg h]; push_cast; grind

theorem cast_zero_of_mod {x : Int} (h : x % 2013265921 = 0) : ((x : Int) : Fp) = 0 :=
  (Lean.Grind.IsCharP.intCast_eq_zero_iff (α := Fp) P x).mpr (by rw [P_val]; exact h)

/-- The `wt` shift inside an allowance field. -/
theorem wt_mod (g : Nat) (hf : (tenv tr t r pub).cur fA = 1) (hr : (tenv tr t r pub).cur rend = 0)
    (hc : (tenv tr t r pub).cur wt = 256 ^ g % 2013265921)
    (hn : (tenv tr t r pub).nxt wt = 256 ^ (g + 1) % 2013265921) :
    (Expr.mul (sub (c fA) (c rend)) (sub (n wt) (smul 256 (c wt)))).eval tr t r pub = 0 := by
  rw [eval_eq]
  simp only [zev_mul, zev_sub, zev_c, zev_n, zev_smul, hf, hr, hc, hn]
  apply cast_zero_of_mod
  rw [Nat.pow_succ]
  generalize 256 ^ g = y
  omega

/-- The `wt` constraint off the inner allowance rows: `fA = rend`. -/
theorem wt_off (hg : (tenv tr t r pub).cur fA = (tenv tr t r pub).cur rend) :
    (Expr.mul (sub (c fA) (c rend)) (sub (n wt) (smul 256 (c wt)))).eval tr t r pub = 0 :=
  gate_zero _ _ (by simp [hg])

end

end ZkFormal.NearV3.Render.Cdc
