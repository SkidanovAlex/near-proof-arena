import ZkFormal.NearV3.Render.CodecCells
import ZkFormal.NearV3.Sched.Complete.Field

/-!
# Codec row cells are below `P`

`hdr_vals`, `rec_vals`, `hash_vals`, `ash_vals`: every value of the honest row assignments is
`< P`, from explicit bounds on the instance constants and the per-row data.
-/
namespace ZkFormal.NearV3.Render.Cdc
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.NearV3.Sched.Codec ZkFormal.NearV3.Candidates.SchedSetAll

abbrev Vals (L : List (Nat × Nat)) : Prop := ∀ q ∈ L, q.2 < 2013265921

theorem inv_lt' (x : Nat) : inv x < 2013265921 := by
  rw [inv_eq]; exact ZkFormal.NearV3.Sched.Complete.finv_lt x

theorem vals_app {xs ys : List (Nat × Nat)} (h1 : Vals xs) (h2 : Vals ys) : Vals (xs ++ ys) := by
  intro q hq
  rcases List.mem_append.mp hq with h | h
  · exact h1 q h
  · exact h2 q h

theorem vals_ite (C : Prop) [Decidable C] {L : List (Nat × Nat)} (h : C → Vals L) :
    Vals (if C then L else []) := by
  split
  · exact h ‹C›
  · intro q hq; simp at hq

theorem vals_cons {a b : Nat} {L : List (Nat × Nat)} (h1 : b < 2013265921) (h2 : Vals L) :
    Vals ((a, b) :: L) := by
  intro q hq
  rcases List.mem_cons.mp hq with rfl | h
  · exact h1
  · exact h2 q h

theorem vals_nil : Vals [] := fun _ h => by simp at h

theorem vals_bits (col : Nat → Nat) (x : Nat) :
    Vals ((List.range 8).map fun i => (col i, bit x i)) := by
  intro q hq
  simp only [List.mem_map, List.mem_range] at hq
  obtain ⟨i, _, rfl⟩ := hq
  have : bit x i < 2 := Nat.mod_lt _ (by decide)
  simp only; omega

theorem vals_regA (vals : Nat → Nat) (h : ∀ i, vals i < 2013265921) : Vals (regA vals) := by
  intro q hq
  simp only [regA, List.mem_map, List.mem_range] at hq
  obtain ⟨i, _, rfl⟩ := hq
  exact h i

theorem getD_lt {l : List Nat} {B : Nat} (h : ∀ x ∈ l, x < B) (hB : 0 < B) (i : Nat) :
    l.getD i 0 < B := by
  rw [List.getD_eq_getElem?_getD]
  cases hx : l[i]? with
  | none => exact hB
  | some x => exact h x (List.mem_of_getElem? hx)

theorem bytesLE_lt (x len : Nat) : ∀ y ∈ bytesLE x len, y < 256 := by
  intro y hy
  simp only [bytesLE, List.mem_map, List.mem_range] at hy
  obtain ⟨i, _, rfl⟩ := hy
  exact Nat.mod_lt _ (by decide)

/-- Bounds on the instance constants. -/
def InstB (I : Inst) : Prop :=
  I.tv < 2013265921 ∧ I.vid < 2013265921 ∧ I.n < 65536 ∧ I.N < 65536 ∧ I.base < 2 ^ 24 ∧
    I.fair < 2 ^ 24

theorem vals_instA (I : Inst) (h : InstB I) : Vals (instA I) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  have := zt0_le I
  have := inv_lt' I.tv
  unfold instA b2n
  repeat' apply vals_cons
  all_goals first | exact vals_nil | omega | (split <;> omega)

theorem params_lt (I : Inst) : ∀ y ∈ params I, y < 256 := by
  intro y hy
  simp only [params, List.mem_append] at hy
  rcases hy with (hy | hy) | hy
  · simp only [hdrBytes, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl <;> first | decide | exact Nat.mod_lt _ (by decide)
  · exact bytesLE_lt _ _ y hy
  · exact bytesLE_lt _ _ y hy

theorem hdr_vals (I : Inst) (p : Nat) (hp : p ≤ 4) (h : InstB I) : Vals (hdrA I p) := by
  have hI := vals_instA I h
  have hb : (hdrBytes I).getD p 0 < 256 := getD_lt (fun y hy => params_lt I y (by
    simp only [params, List.mem_append]; exact Or.inl (Or.inl hy))) (by decide) p
  have := inv_lt' (fsub p 4)
  unfold hdrA
  refine vals_app (vals_app (vals_app (vals_app hI ?_) (vals_regA _ ?_)) (vals_bits _ _)) (vals_bits _ _)
  · unfold b2n
    repeat' apply vals_cons
    all_goals first | exact vals_nil | omega | (split <;> omega)
  · intro i; have := getD_lt (params_lt I) (by decide) (p + i); omega

theorem hash_vals (I : Inst) (dig hpre : List Nat) (j : Nat) (hj : j < 32) (h : InstB I)
    (hd : ∀ x ∈ dig, x < 256) (hh : ∀ x ∈ hpre, x < 256) : Vals (hashA I dig hpre j) := by
  have hI := vals_instA I h
  have h1 := getD_lt hd (by decide) j
  have h2 := getD_lt hh (by decide) j
  have := inv_lt' (fsub j 31)
  have h4 := h.2.2.2.1
  unfold hashA
  refine vals_app (vals_app (vals_app (vals_app hI ?_) (vals_regA _ ?_)) (vals_bits _ _)) (vals_bits _ _)
  · unfold b2n
    repeat' apply vals_cons
    all_goals first | exact vals_nil | omega | (split <;> omega)
  · intro i; have := getD_lt hd (by decide) (j + i); omega

theorem ash_vals (I : Inst) (ash : List Nat) (j : Nat) (hj : j < 32) (h : InstB I)
    (ha : ∀ x ∈ ash, x < 256) : Vals (ashA I ash j) := by
  have hI := vals_instA I h
  have h1 := getD_lt ha (by decide) j
  have := inv_lt' (fsub (32 + j) 63)
  have h4 := h.2.2.2.1
  unfold ashA
  refine vals_app hI ?_
  repeat' apply vals_cons
  all_goals first | exact vals_nil | omega | (split <;> omega)

theorem rec_vals (I : Inst) (R : Rec) (f gg bpo bpr apv apostv bigv : Nat) (h : InstB I)
    (hf : f < 3) (hg : gg < 8) (hk : R.kk < 65536) (hbpo : bpo < 256) (hbpr : bpr < 256)
    (hap : apv < 2 ^ 24) (hapost : apostv < 2 ^ 24) (hbig : bigv ≤ 1)
    (hikl : R.iklv < 2013265921) (hsrc : R.srcS < 2013265921) (hgb : R.gb < 2 ^ 26)
    (hafin : R.afin < 2 ^ 26) (hgfin : R.gfin < 2 ^ 26) (hft : R.ft < 2 ^ 26) :
    Vals (recA I R f gg bpo bpr apv apostv bigv) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  have hI := vals_instA I ⟨h1, h2, h3, h4, h5, h6⟩
  have hz := zt0_le I
  have i1 := inv_lt' (fsub gg 7)
  have i2 := inv_lt' (fsub gg 2)
  have i3 := inv_lt' bpr
  have hc := cbv_le I R
  have hbr := bigRv_le R
  have hapr : apRv R < 16777216 := Nat.mod_lt _ (by decide)
  have ha1 : a1v I R ≤ 4500000 + 16777216 + 2 ^ 24 := by
    rw [a1v_def]; unfold MA; split
    · omega
    · split <;> omega
  have hal : b2n R.al ≤ 1 := by cases R.al <;> decide
  have hpr : b2n I.pres ≤ 1 := by cases I.pres <;> decide
  have hhc : b2n R.hasC ≤ 1 := by cases R.hasC <;> decide
  have huc : b2n R.useC ≤ 1 := by cases R.useC <;> decide
  have hMA : MA = 4500000 := rfl
  have hal2 : b2n R.al * I.base ≤ I.base := by
    rcases (show b2n R.al = 0 ∨ b2n R.al = 1 by omega) with e | e <;> rw [e] <;> omega
  have hwt : 256 ^ gg % 2013265921 < 2013265921 := Nat.mod_lt _ (by decide)
  have hm1 : zt0 I * (R.gfin + R.gb) ≤ R.gfin + R.gb := by
    rcases (show zt0 I = 0 ∨ zt0 I = 1 by omega) with e | e <;> rw [e] <;> omega
  have hm2 : zt0 I * R.ft ≤ R.ft := by
    rcases (show zt0 I = 0 ∨ zt0 I = 1 by omega) with e | e <;> rw [e] <;> omega
  have hm3 : ∀ x, x < 2013265921 → zt0 I * x < 2013265921 := by
    intro x hx; rcases (show zt0 I = 0 ∨ zt0 I = 1 by omega) with e | e <;> rw [e] <;> omega
  have hkm : R.kk % 256 < 256 := Nat.mod_lt _ (by decide)
  have hfm : ∀ x, x % 256 < 256 := fun x => Nat.mod_lt _ (by decide)
  have hb0 := hfm (R.ft / 256)
  have hb1 := hfm (R.ft / 65536)
  have hb2 := hfm R.ft
  unfold recA
  refine vals_app (vals_app (vals_app (vals_app (vals_app (vals_app (vals_app (vals_app
    (vals_app hI ?_) (vals_bits _ _)) (vals_bits _ _)) ?_) (vals_ite _ fun _ => ?_))
    (vals_ite _ fun _ => ?_)) (vals_ite _ fun _ => ?_)) (vals_ite _ fun _ => ?_)) (vals_ite _ fun _ => ?_)
  all_goals
    repeat' apply vals_cons
    all_goals first
      | exact vals_nil
      | omega
      | (split <;> omega)
      | exact hm3 _ (by omega)

end ZkFormal.NearV3.Render.Cdc
