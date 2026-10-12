import ZkFormal.NearV3.Assembly.A9Count
import ZkFormal.NearV3.Assembly.LinkSchedCore
import ZkFormal.Near.Extract.BusCount

/-!
# ZkFormal.NearV3.Assembly.A9Air — the AIR half of `A9Link` (L2)

Σ over the scheduler instances of the last round's RNG position `kend` is at most the number of
active rows of table 9 (`rngV3`, one per drawn word):

* **weighted bus balance** (`wsum_bal`): if two tables' sends / receives of a bus agree message by
  message, then any message weight has the same total on both sides;
* `rng_le`: Σ over the accepting rows of `rngV3` of `kend − kstart` (the message weight on `SGEN`)
  ≤ the active rows (each call occupies `kend − kstart` active rows, disjoint);
* `shuf_le`: Σ over the final rows of `shufV3` of `kq_fin − ks` (weight on `SSHUF`) ≤ Σ over its
  step rows of `kn − kq` (weight on `SGEN`) (telescoping within each shuffle instance);
* `procHdr_le`: Σ over the instances' round headers of `kend − kq` ≤ the `SSHUF` receive weight of
  `procV3`;
* **`a9_air`**: for any family of instance blocks `(F τ, M τ)` (`τ < n`, `tau (F τ) = τ`),
  `Σ_τ lastK (F τ) (M τ) ≤ activeRows tr T_RNG` (`kq_0 = 0`, `kq_{i+1} = kend_i`).
-/

namespace ZkFormal.NearV3.Assembly

namespace A9Air

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2

/-! ## Generic: weighted bus balance -/

section
variable {F : Type} [Lean.Grind.CommRing F] [DecidableEq F]

/-- Traffic of table `t` on bus `b` (side `s`) as a list of messages with multiplicity. -/
def tl (is : List Interaction) (tr : Trace F) (t : Nat) (pub : List F) (b : Nat) (s : Bool) :
    List (List F) :=
  (List.range (tr.height t)).flatMap fun r => ZkFormal.Near.rowTraffic is tr t r pub b s

/-- The weight of a table's traffic, row by row. -/
def wrow (is : List Interaction) (tr : Trace F) (t : Nat) (pub : List F) (b : Nat) (s : Bool)
    (W : List F → Nat) (r : Nat) : Nat :=
  (is.map fun i => if i.bus = b ∧ i.send = s then i.multNat tr t r pub * W (i.msgVal tr t r pub)
    else 0).sum

theorem sum_rep {α : Type} (W : α → Nat) (x : α) : ∀ n, ((List.replicate n x).map W).sum = n * W x
  | 0 => by simp
  | n + 1 => by rw [List.replicate_succ, List.map_cons, List.sum_cons, sum_rep W x n, Nat.succ_mul]; omega

theorem sum_rowTraffic (is : List Interaction) (tr : Trace F) (t r : Nat) (pub : List F) (b : Nat)
    (s : Bool) (W : List F → Nat) :
    ((ZkFormal.Near.rowTraffic is tr t r pub b s).map W).sum = wrow is tr t pub b s W r := by
  unfold ZkFormal.Near.rowTraffic wrow
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons]
    rw [ih]
    congr 1
    split
    · exact sum_rep _ _ _
    · rfl

theorem sum_tl (is : List Interaction) (tr : Trace F) (t : Nat) (pub : List F) (b : Nat) (s : Bool)
    (W : List F → Nat) :
    ((tl is tr t pub b s).map W).sum =
      ((List.range (tr.height t)).map (wrow is tr t pub b s W)).sum := by
  unfold tl
  generalize List.range (tr.height t) = rs
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons]
    rw [ih, sum_rowTraffic]

/-- **Weighted balance**: message-wise equal counts give equal weighted totals. -/
theorem wsum_bal {is₁ is₂ : List Interaction} {tr : Trace F} {t₁ t₂ : Nat} {pub : List F} {b : Nat}
    {s₁ s₂ : Bool}
    (h : ∀ m, tableBusCount is₁ tr t₁ pub b s₁ m = tableBusCount is₂ tr t₂ pub b s₂ m)
    (W : List F → Nat) :
    ((List.range (tr.height t₁)).map (wrow is₁ tr t₁ pub b s₁ W)).sum =
      ((List.range (tr.height t₂)).map (wrow is₂ tr t₂ pub b s₂ W)).sum := by
  rw [← sum_tl, ← sum_tl]
  have hp : (tl is₁ tr t₁ pub b s₁).Perm (tl is₂ tr t₂ pub b s₂) := by
    apply List.perm_iff_count.mpr
    intro m
    have := h m
    rw [ZkFormal.Near.tableBusCount_eq, ZkFormal.Near.tableBusCount_eq] at this
    exact this
  exact (hp.map W).sum_nat

theorem tableBusCount_side {is : List Interaction} {tr : Trace F} {t : Nat} {pub : List F} {b : Nat}
    {s : Bool} (h : ∀ i ∈ is, i.bus = b → i.send ≠ s) (m : List F) :
    tableBusCount is tr t pub b s m = 0 := by
  rw [ZkFormal.Near.tableBusCount_eq, List.count_eq_zero]
  intro hm
  obtain ⟨r, -, hr⟩ := List.mem_flatMap.mp hm
  unfold ZkFormal.Near.rowTraffic at hr
  obtain ⟨i, hi, hr⟩ := List.mem_flatMap.mp hr
  split at hr
  · rename_i hc; exact h i hi hc.1 hc.2
  · simp at hr

end

/-! ## Generic: sums over row intervals -/

theorem sum_range_add (g : Nat → Nat) (a b : Nat) :
    ((List.range (a + b)).map g).sum = ((List.range a).map g).sum +
      ((List.range b).map fun y => g (a + y)).sum := by
  rw [List.range_add, List.map_append, List.sum_append, List.map_map]
  rfl

theorem sum_range_le_of {g c : Nat → Nat} (h : ∀ y, g y ≤ c y) :
    ∀ n, ((List.range n).map g).sum ≤ ((List.range n).map c).sum
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.map_append, List.sum_append, List.sum_append]
    have := sum_range_le_of h n
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    have := h n
    omega

theorem sum_range_zero {g : Nat → Nat} : ∀ n, (∀ y, y < n → g y = 0) →
    ((List.range n).map g).sum = 0
  | 0, _ => by simp
  | n + 1, h => by
    rw [List.range_succ, List.map_append, List.sum_append, sum_range_zero n (fun y hy => h y (by omega))]
    simp [h n (by omega)]

/-- **Interval charging**: if every row `r` with `g r ≠ 0` heads an interval `[r − d, r]` whose other
rows have `g = 0` and `g r ≤ Σ_{interval} c`, then `Σ_{r<h} g ≤ Σ_{r<h} c`. -/
theorem interval_le (g c : Nat → Nat) (H : Nat)
    (hstep : ∀ r, r < H → g r ≠ 0 → ∃ d, d ≤ r ∧
      g r ≤ ((List.range (d + 1)).map fun y => c (r - d + y)).sum ∧
      ∀ y, y < d → g (r - d + y) = 0) :
    ∀ h, h ≤ H → ((List.range h).map g).sum ≤ ((List.range h).map c).sum := by
  intro h
  induction h using Nat.strongRecOn with
  | _ h ih =>
    intro hH
    rcases h with _ | r
    · simp
    · by_cases hg : g r = 0
      · rw [List.range_succ, List.map_append, List.map_append, List.sum_append, List.sum_append]
        have := ih r (by omega) (by omega)
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hg]
        omega
      · obtain ⟨d, hdr, hgr, hz⟩ := hstep r (by omega) hg
        have e : r + 1 = (r - d) + (d + 1) := by omega
        rw [e, sum_range_add g (r - d) (d + 1), sum_range_add c (r - d) (d + 1)]
        have h1 := ih (r - d) (by omega) (by omega)
        have h2 : ((List.range (d + 1)).map fun y => g (r - d + y)).sum = g r := by
          rw [List.range_succ, List.map_append, List.sum_append, sum_range_zero d hz]
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
          rw [show r - d + d = r by omega]; omega
        omega

theorem sum_range_one : ∀ n, ((List.range n).map fun _ => 1).sum = n
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, sum_range_one n]; simp

theorem sum_le_sum_range {g c : Nat → Nat} : ∀ {n}, (∀ y, y < n → g y ≤ c y) →
    ((List.range n).map g).sum ≤ ((List.range n).map c).sum
  | 0, _ => by simp
  | n + 1, h => by
    rw [List.range_succ, List.map_append, List.map_append, List.sum_append, List.sum_append]
    have := sum_le_sum_range (n := n) (fun y hy => h y (by omega))
    have := h n (by omega)
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega

/-- Telescoping with truncated differences. -/
theorem tele (f : Nat → Nat) : ∀ d, f d - f 0 ≤ ((List.range d).map fun y => f (y + 1) - f y).sum
  | 0 => by simp
  | d + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append]
    have := tele f d
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega


/-! ## Message weights -/

/-- Weight of a `busGen` message `[key, kstart, n, j, kend]`: `kend − kstart`. -/
def Wg (m : List Fp) : Nat := (m.getD 19 0).toNat - (m.getD 16 0).toNat

/-- Weight of a `busShuf` message `[lid, key, kq, L, kend]`: `kend − kq`. -/
def Wsh (m : List Fp) : Nat := (m.getD 19 0).toNat - (m.getD 17 0).toNat

theorem multNat_c1 {tr : Trace Fp} {t r : Nat} {pub : List Fp} {i : Interaction} {x : Nat}
    (hi : i.mult = [ZkFormal.Chacha.Table.E.c x]) :
    i.multNat tr t r pub = if ZkFormal.Chacha.cv tr t r x = 1 then 1 else 0 := by
  unfold Interaction.multNat
  rw [hi]
  simp only [Interaction.multNat.go]
  have e : (ZkFormal.Chacha.Table.E.c x).eval tr t r pub = 1 ↔ ZkFormal.Chacha.cv tr t r x = 1 := by
    show tr.cell t r x = 1 ↔ (tr.cell t r x).toNat = 1
    constructor
    · intro h; rw [h]; rfl
    · intro h; rw [← Fp.ofNat_toNat (tr.cell t r x), h]; rfl
  by_cases h : ZkFormal.Chacha.cv tr t r x = 1
  · simp [e.mpr h, h]
  · have : ¬ (ZkFormal.Chacha.Table.E.c x).eval tr t r pub = 1 := fun h' => h (e.mp h')
    simp [this, h]

/-! ## `rngV3`: accepted calls occupy disjoint runs of active rows -/

section Rng
open ZkFormal.Chacha ZkFormal.Chacha.Rng ZkFormal.Chacha.Rng.Table
variable {tr : Trace Fp} {t : Nat} {pub : List Fp}

theorem activeRows_sum (tr : Trace Fp) (t : Nat) :
    activeRows tr t = ((List.range (tr.height t)).map fun r => if cv tr t r colA = 1 then 1 else 0).sum := by
  unfold activeRows
  generalize List.range (tr.height t) = rs
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    rw [List.filter_cons, List.map_cons, List.sum_cons, ← ih]
    split <;> simp_all <;> omega

/-- The `SGEN` weight of a row of `rngV3`. -/
theorem wrow_rng {bc bg : Nat} (hbc : bc ≠ bg) (r : Nat) :
    wrow (interactions bc bg) tr t pub bg true Wg r =
      (if cv tr t r colAcc = 1 then 1 else 0) * Wg ((interactions bc bg)[1]!.msgVal tr t r pub) := by
  unfold wrow
  simp only [interactions, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hbc,
    false_and, ite_false, true_and, ite_true, Nat.zero_add, Nat.add_zero, List.getElem!_cons_succ,
    List.getElem!_cons_zero]
  rw [multNat_c1 rfl]

theorem eval_kE1 (r : Nat) :
    (ZkFormal.Air.Expr.add kE (ZkFormal.Chacha.Table.E.k 1)).eval tr t r pub = Fp.ofNat (kv tr t r + 1) := by
  rw [eval_eq]
  have : zev (tenv tr t r pub) (ZkFormal.Air.Expr.add kE (ZkFormal.Chacha.Table.E.k 1)) =
      ((kv tr t r + 1 : Nat) : Int) := by
    simp only [kE, idxE, zev_add, zev_smul, zev_c, cur_cv, zev_num, zev_k, kv]
    omega
  rw [this, intCast_ofNat]

section
variable (hL : GLocal tr t pub) {bc bg : Nat} (hW : ChachaRecv tr t pub bc bg)
include hL hW

/-- The start row of the call ending at row `r`. -/
theorem call_start {r : Nat} (hr : r < tr.height t) (ha : cv tr t r colA = 1) :
    attv tr t r ≤ r ∧ cv tr t (r - attv tr t r) colSt = 1 := by
  generalize hdd : attv tr t r = d
  obtain ⟨hdr, ha0, hatt0, -, -, -, -, -⟩ := walk hL hW hr ha d (by omega)
  refine ⟨hdr, ?_⟩
  have := bSt hL (show r - d < _ by omega)
  rcases (show cv tr t (r - d) colSt = 0 ∨ cv tr t (r - d) colSt = 1 by omega) with h | h
  · exfalso
    rcases Nat.eq_zero_or_pos (r - d) with h0 | h0
    · rw [h0] at ha0 h; have := first_start hL ha0; omega
    · obtain ⟨r', hr'⟩ : ∃ r', r - d = r' + 1 := ⟨r - d - 1, by omega⟩
      have t0 := trans0 hL (show r' + 1 < _ by omega)
      rw [← hr', ha0, h] at t0
      have := bA hL (show r' < _ by omega); have := bAcc hL (show r' < _ by omega)
      have ha1 : cv tr t r' colA = 1 := by
        rcases (show cv tr t r' colA = 0 ∨ cv tr t r' colA = 1 by omega) with h1 | h1
        · rw [h1] at t0; simp at t0
        · exact h1
      have hacc1 : cv tr t r' colAcc = 0 := by rw [ha1] at t0; simp at t0; omega
      have := (cont hL (show r' + 1 < _ by omega) ha1 hacc1).2.2.2.2.1
      rw [← hr'] at this; omega
  · exact h

/-- **`rngV3`**: the `SGEN` send weight is at most the number of active rows. -/
theorem rng_le (hbc : bc ≠ bg) :
    ((List.range (tr.height t)).map (wrow (interactions bc bg) tr t pub bg true Wg)).sum ≤
      activeRows tr t := by
  rw [activeRows_sum]
  apply interval_le _ _ (tr.height t) _ _ (Nat.le_refl _)
  intro r hr hg
  rw [wrow_rng hbc] at hg ⊢
  have hacc : cv tr t r colAcc = 1 := by
    by_cases h : cv tr t r colAcc = 1
    · exact h
    · simp [h] at hg
  have ha : cv tr t r colA = 1 := by
    have hz := hL.zc hr (mem_cM (e := .mul (ZkFormal.Chacha.Table.E.c colAcc)
      (ZkFormal.Chacha.Table.E.sub (ZkFormal.Chacha.Table.E.k 1) (ZkFormal.Chacha.Table.E.c colA)))
      (by simp [cM]))
    simp only [zev_mul, zev_c, zev_sub, zev_k, cur_cv, hacc] at hz
    have := bA hL hr; have := hz (by omega) (by omega); omega
  obtain ⟨hdr, hst⟩ := call_start hL hW hr ha
  generalize hdd : attv tr t r = d at hdr hst
  obtain ⟨-, ha0, -, -, -, hks0, hk0, -⟩ := walk hL hW hr ha d (by omega)
  have hc0 := (rng_contract hL hW (show r - d < _ by omega) ha0).2.2.2.1
  obtain ⟨-, hks⟩ := start hL (show r - d < _ by omega) hst hc0
  have hcr := (rng_contract hL hW hr ha).2.2.2.1
  refine ⟨d, hdr, ?_, ?_⟩
  · -- the weight is `d + 1`
    have hkv : kv tr t r < 2 ^ 30 := by
      unfold kv
      have := nbits_lt (f := fun b => cv tr t r (colIdx b)) (n := 4) (bIdx hL hr)
      unfold numv; omega
    have hW' : Wg ((interactions bc bg)[1]!.msgVal tr t r pub) ≤ d + 1 := by
      unfold Wg
      simp only [interactions, List.getElem!_cons_succ, List.getElem!_cons_zero, Interaction.msgVal,
        keyMsg, List.map_append, List.map_map, List.map_cons, List.map_nil]
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_right (by simp), List.getElem?_append_right (by simp)]
      simp only [List.length_map, List.length_range]
      simp only [show 19 - 16 = 3 by rfl, show 16 - 16 = 0 by rfl, List.getElem?_cons_succ,
        List.getElem?_cons_zero, Option.getD_some]
      rw [eval_kE1, Fp.toNat_ofNat]
      show (kv tr t r + 1) % P - cv tr t r colKs ≤ d + 1
      unfold P; rw [Nat.mod_eq_of_lt (by omega)]
      omega
    have hall : ((List.range (d + 1)).map fun y =>
        if cv tr t (r - d + y) colA = 1 then 1 else 0).sum = d + 1 := by
      have : ∀ y, y < d + 1 → (if cv tr t (r - d + y) colA = 1 then 1 else 0) = 1 := by
        intro y hy
        obtain ⟨-, hay, -⟩ := walk hL hW hr ha (d - y) (by omega)
        rw [show r - d + y = r - (d - y) by omega, ite_eq_left_iff.mpr (fun h => absurd hay h)]
      rw [List.map_congr_left (fun y hy => this y (List.mem_range.mp hy))]
      exact sum_range_one _
    rw [hall, ite_eq_left_iff.mpr (fun h => absurd hacc h), Nat.one_mul]; exact hW'
  · intro y hy
    obtain ⟨-, -, -, -, -, -, -, hacc0⟩ := walk hL hW hr ha (d - y) (by omega)
    show wrow (interactions bc bg) tr t pub bg true Wg (r - d + y) = 0
    rw [wrow_rng hbc, show r - d + y = r - (d - y) by omega, hacc0 (by omega)]
    simp

end

end Rng

/-! ## `shufV3`: a shuffle instance's RNG span is paid by its step rows -/

section Shuf
open ZkFormal.Chacha ZkFormal.Chacha.Shuffle ZkFormal.Chacha.Shuffle.Table
open ZkFormal.NearV3.Sched (B_SSIN B_SSOUT B_SSMEM B_SGEN B_SSHUF)
variable {tr : Trace Fp} {t : Nat} {pub : List Fp}

abbrev shufIs : List Interaction := interactions B_SSIN B_SSOUT B_SSMEM B_SGEN B_SSHUF

theorem wrow_shuf (r : Nat) :
    wrow shufIs tr t pub B_SSHUF true Wsh r =
      (if cv tr t r colFin = 1 then 1 else 0) * (cv tr t r colKq - cv tr t r colKs) := by
  unfold wrow Wsh
  simp only [shufIs, interactions, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  simp (config := { decide := true }) only [ZkFormal.NearV3.Sched.B_SSIN, ZkFormal.NearV3.Sched.B_SSOUT,
    ZkFormal.NearV3.Sched.B_SSMEM, ZkFormal.NearV3.Sched.B_SGEN, ZkFormal.NearV3.Sched.B_SSHUF]
  simp only [ite_false, ite_true, false_and, and_false, and_true, true_and, Nat.zero_add, Nat.add_zero]
  rw [multNat_c1 rfl]
  congr 1

theorem wrow_gen_ge {r : Nat} (ha : cv tr t r colA = 1) (hf : cv tr t r colFin = 0) :
    cv tr t r colKn - cv tr t r colKq ≤ wrow shufIs tr t pub B_SGEN false Wg r := by
  unfold wrow Wg
  simp only [shufIs, interactions, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  simp (config := { decide := true }) only [ZkFormal.NearV3.Sched.B_SSIN, ZkFormal.NearV3.Sched.B_SSOUT,
    ZkFormal.NearV3.Sched.B_SSMEM, ZkFormal.NearV3.Sched.B_SGEN, ZkFormal.NearV3.Sched.B_SSHUF]
  simp only [ite_false, ite_true, false_and, and_false, and_true, true_and, Nat.zero_add, Nat.add_zero]
  have hm : Interaction.multNat ⟨48, [gStep], keyMsg ++ [ZkFormal.Chacha.Table.E.c colKq,
      .add (ZkFormal.Chacha.Table.E.c colQ) (ZkFormal.Chacha.Table.E.k 1), ZkFormal.Chacha.Table.E.c colJ,
      ZkFormal.Chacha.Table.E.c colKn], false⟩ tr t r pub = 1 := by
    unfold Interaction.multNat
    simp only [Interaction.multNat.go]
    have : gStep.eval tr t r pub = 1 := by
      rw [eval_eq]; simp only [gStep, zev_sub, zev_c, cur_cv, ha, hf]; rfl
    simp [this]
  rw [hm, Nat.one_mul]
  apply Nat.le_of_eq
  simp only [Interaction.msgVal, keyMsg, List.map_append, List.map_cons, List.map_nil, List.map_map]
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by simp), List.getElem?_append_right (by simp)]
  simp only [List.length_append, List.length_map, List.length_range, List.length_cons, List.length_nil]
  rfl

section
variable (hL : SLocal tr t pub) (hG : GenRecv tr t pub) (hH : tr.height t ≤ 2 ^ 22)
include hL hG hH

/-- **`shufV3`**: the `SSHUF` send weight is at most the `SGEN` receive weight. -/
theorem shuf_le :
    ((List.range (tr.height t)).map (wrow shufIs tr t pub B_SSHUF true Wsh)).sum ≤
      ((List.range (tr.height t)).map (wrow shufIs tr t pub B_SGEN false Wg)).sum := by
  apply interval_le _ _ (tr.height t) _ _ (Nat.le_refl _)
  intro r hr hg
  rw [wrow_shuf] at hg ⊢
  have hfin : cv tr t r colFin = 1 := by
    by_cases h : cv tr t r colFin = 1
    · exact h
    · simp [h] at hg
  obtain ⟨d, hdr, -, -, hst, hrows⟩ := inst_rows hL hG hH hr hfin
  have hst' := (start_facts hL hH (show r - d < _ by omega) hst).2.1
  refine ⟨d, hdr, ?_, ?_⟩
  · rw [ite_eq_left_iff.mpr (fun h => absurd hfin h), Nat.one_mul]
    have hks : cv tr t (r - d) colKs = cv tr t r colKs := (hrows d (Nat.le_refl _)).2.2.2.2.2.1
    have ht := tele (fun y => cv tr t (r - d + y) colKq) d
    simp only [Nat.add_zero, show r - d + d = r by omega] at ht
    rw [hst', hks] at ht
    refine Nat.le_trans ht ?_
    rw [List.range_succ, List.map_append, List.sum_append]
    refine Nat.le_trans ?_ (Nat.le_add_right _ _)
    apply sum_le_sum_range
    intro y hy
    have hx := hrows (d - y) (by omega)
    rw [show r - (d - y) = r - d + y by omega] at hx
    obtain ⟨hay, -, -, -, -, -, -, hfy, hkq⟩ := hx
    have e1 := hkq (by omega)
    rw [show r - d + y + 1 = r - d + (y + 1) by omega] at e1
    rw [e1]
    exact wrow_gen_ge hay (hfy (by omega))
  · intro y hy
    show wrow shufIs tr t pub B_SSHUF true Wsh (r - d + y) = 0
    rw [wrow_shuf]
    have := (hrows (d - y) (by omega)).2.2.2.2.2.2.2.1 (by omega)
    rw [show r - (d - y) = r - d + y by omega] at this
    simp [this]

end

end Shuf

/-! ## Generic list sums -/

theorem le_sum_of_mem {α : Type} (f : α → Nat) : ∀ {l : List α} {x : α}, x ∈ l → f x ≤ (l.map f).sum
  | _ :: _, _, .head _ => by simp
  | y :: l, x, .tail _ h => by
    have := le_sum_of_mem f h
    simp only [List.map_cons, List.sum_cons]; omega

theorem sum_range_split (f : Nat → Nat) (x : Nat) : ∀ H,
    ((List.range H).map f).sum =
      ((List.range H).map fun r => if r = x then 0 else f r).sum + (if x < H then f x else 0)
  | 0 => by simp
  | H + 1 => by
    rw [List.range_succ, List.map_append, List.map_append, List.sum_append, List.sum_append,
      sum_range_split f x H]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    by_cases h1 : H = x
    · subst h1; simp
    · by_cases h2 : x < H
      · simp [h1, h2, show x < H + 1 by omega]; omega
      · simp [h1, h2, show ¬ x < H + 1 by omega]

/-- A duplicate-free list of rows below `H` sums to at most the sum over all rows. -/
theorem nodup_sum_le {H : Nat} : ∀ {S : List Nat}, S.Nodup → (∀ x ∈ S, x < H) → ∀ (f : Nat → Nat),
    (S.map f).sum ≤ ((List.range H).map f).sum
  | [], _, _, _ => by simp
  | x :: S, hS, hlt, f => by
    have hx : x ∉ S := (List.nodup_cons.mp hS).1
    have ih := nodup_sum_le (List.nodup_cons.mp hS).2 (fun y hy => hlt y (List.mem_cons_of_mem _ hy))
      (fun r => if r = x then 0 else f r)
    have e : (S.map fun r => if r = x then 0 else f r) = S.map f := by
      apply List.map_congr_left
      intro y hy
      have : y ≠ x := fun h => hx (h ▸ hy)
      simp [this]
    rw [e] at ih
    rw [sum_range_split f x H, if_pos (hlt x (List.mem_cons_self ..))]
    simp only [List.map_cons, List.sum_cons]
    omega

theorem sum_flatMap' {α : Type} (g : α → List Nat) (F : Nat → Nat) : ∀ l : List α,
    ((l.flatMap g).map F).sum = (l.map fun a => ((g a).map F).sum).sum
  | [] => rfl
  | a :: l => by
    rw [List.flatMap_cons, List.map_append, List.sum_append, sum_flatMap' g F l]; rfl

/-! ## `nearAirV3`: the two balances -/

section V3
open ZkFormal.Chacha
open ZkFormal.NearV3.Sched (B_SCHACHA B_SGEN B_SSHUF B_SSIN B_SSOUT B_SSMEM)
variable {pub : List Fp} {tr : Trace Fp}

theorem isAt_rng : isAt T_RNG = Rng.Table.interactions B_SCHACHA B_SGEN := rfl
theorem isAt_shuf : isAt T_SHUF = shufIs := rfl
theorem isAt_proc : isAt T_PROC = ZkFormal.NearV3.Sched.Proc.interactions := rfl

/-- **`SGEN`**: the stream table's sends are the shuffle table's receives, weight by weight. -/
theorem gen_bal (hH : HoldsP nearAirV3 pub tr) (W : List Fp → Nat) :
    ((List.range (tr.height T_RNG)).map
        (wrow (Rng.Table.interactions B_SCHACHA B_SGEN) tr T_RNG pub B_SGEN true W)).sum =
      ((List.range (tr.height T_SHUF)).map (wrow shufIs tr T_SHUF pub B_SGEN false W)).sum := by
  apply wsum_bal
  intro m
  have h := bal_users hH (b := B_SGEN) (U := [T_RNG, T_SHUF]) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) m
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at h
  rw [isAt_rng, isAt_shuf] at h
  rw [tableBusCount_side (s := false) (by decide +kernel) m,
    tableBusCount_side (is := shufIs) (s := true) (by decide +kernel) m] at h
  omega

/-- **`SSHUF`**: the shuffle table's sends are the process table's receives, weight by weight. -/
theorem shuf_bal (hH : HoldsP nearAirV3 pub tr) (W : List Fp → Nat) :
    ((List.range (tr.height T_SHUF)).map (wrow shufIs tr T_SHUF pub B_SSHUF true W)).sum =
      ((List.range (tr.height T_PROC)).map
        (wrow ZkFormal.NearV3.Sched.Proc.interactions tr T_PROC pub B_SSHUF false W)).sum := by
  apply wsum_bal
  intro m
  have h := bal_users hH (b := B_SSHUF) (U := [T_SHUF, T_PROC]) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) m
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at h
  rw [isAt_shuf, isAt_proc] at h
  rw [tableBusCount_side (is := shufIs) (s := false) (by decide +kernel) m,
    tableBusCount_side (is := ZkFormal.NearV3.Sched.Proc.interactions) (s := true)
      (by decide +kernel) m] at h
  omega

/-! ## The process table's round headers -/

open ZkFormal.NearV3.Sched in
/-- RNG position after the last round of the instance with key block `f` (`0` without rounds). -/
def lastK (tr : Trace Fp) (f m : Nat) : Nat :=
  if m = 0 then 0 else cv tr T_PROC (Proc.hdrAt tr T_PROC f (m - 1)) Proc.kend

open ZkFormal.NearV3.Sched in
/-- RNG span of a header row (`kend − kq`; `0` off headers). -/
def hdrW (tr : Trace Fp) (r : Nat) : Nat :=
  if cv tr T_PROC r Proc.kH = 1 then cv tr T_PROC r Proc.kend - cv tr T_PROC r Proc.kq else 0

open ZkFormal.NearV3.Sched in
theorem hdrW_le (hL : Proc.PLocal tr T_PROC pub) {r : Nat} (hr : r < tr.height T_PROC) :
    hdrW tr r ≤ wrow Proc.interactions tr T_PROC pub B_SSHUF false Wsh r := by
  unfold hdrW
  split
  · rename_i hh
    obtain ⟨m1, v1, -, -⟩ := Proc.hdr_msgs hL hr hh
    have hmem : Proc.interactions[1]! ∈ Proc.interactions := mem_i 1 (by decide)
    have := le_sum_of_mem (fun i => if i.bus = B_SSHUF ∧ i.send = false then
      i.multNat tr T_PROC r pub * Wsh (i.msgVal tr T_PROC r pub) else 0) hmem
    refine Nat.le_trans (Nat.le_of_eq ?_) this
    rw [Proc.i1_def] at m1 v1 ⊢
    simp only [true_and, ite_true, m1, Nat.one_mul, v1, Wsh]
    simp only [List.map_append, List.map_cons, List.map_nil, List.map_map]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by simp), List.getElem?_append_right (by simp)]
    simp only [List.length_append, List.length_map, List.length_range, List.length_cons,
      List.length_nil]
    simp only [show 19 - (1 + 16) = 2 by rfl, show 17 - (1 + 16) = 0 by rfl, List.getElem?_cons_succ,
      List.getElem?_cons_zero, Option.getD_some, Function.comp, Fp.toNat_ofNat]
    have h1 := cv_lt (tr := tr) (t := T_PROC) r Proc.kend
    have h2 := cv_lt (tr := tr) (t := T_PROC) r Proc.kq
    unfold P; rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2]
  · exact Nat.zero_le _

open ZkFormal.NearV3.Sched in
/-- Per instance: the last `kend` telescopes over the round headers (`kq_0 = 0`, `kq_{i+1} = kend_i`). -/
theorem lastK_le {f m : Nat} (I : Proc.Inst tr T_PROC f m) :
    lastK tr f m ≤ ((List.range m).map fun i => hdrW tr (Proc.hdrAt tr T_PROC f i)).sum := by
  unfold lastK
  split
  · exact Nat.zero_le _
  · rename_i hm
    let a : Nat → Nat := fun i => if i < m then cv tr T_PROC (Proc.hdrAt tr T_PROC f i) Proc.kq
      else cv tr T_PROC (Proc.hdrAt tr T_PROC f (m - 1)) Proc.kend
    have ht := tele a m
    have ha0 : a 0 = 0 := by
      simp only [a, if_pos (show 0 < m by omega)]; exact (I.first (by omega)).2.1
    have ham : a m = cv tr T_PROC (Proc.hdrAt tr T_PROC f (m - 1)) Proc.kend := by
      simp only [a, if_neg (Nat.lt_irrefl m)]
    rw [ha0, ham, Nat.sub_zero] at ht
    refine Nat.le_trans ht (sum_le_sum_range ?_)
    intro i hi
    have hh := ((I.hdr i hi).1).2.1
    have e : a (i + 1) - a i =
        cv tr T_PROC (Proc.hdrAt tr T_PROC f i) Proc.kend - cv tr T_PROC (Proc.hdrAt tr T_PROC f i) Proc.kq := by
      simp only [a, if_pos hi]
      by_cases h1 : i + 1 < m
      · rw [if_pos h1, (I.chain i h1).2.1]
      · rw [if_neg h1, show m - 1 = i by omega]
    rw [e]
    unfold hdrW; rw [if_pos hh]
    exact Nat.le_refl _

open ZkFormal.NearV3.Sched in
/-- All instances' headers: distinct rows (`tau` and the header order). -/
theorem hdrs_le (hL : Proc.PLocal tr T_PROC pub) {n : Nat} {F M : Nat → Nat}
    (hF : ∀ τ, τ < n → cv tr T_PROC (F τ) Proc.tau = τ ∧ Proc.Inst tr T_PROC (F τ) (M τ)) :
    ((List.range n).map fun τ =>
        ((List.range (M τ)).map fun i => hdrW tr (Proc.hdrAt tr T_PROC (F τ) i)).sum).sum ≤
      ((List.range (tr.height T_PROC)).map
        (wrow Proc.interactions tr T_PROC pub B_SSHUF false Wsh)).sum := by
  let g : Nat → List Nat := fun τ => (List.range (M τ)).map (Proc.hdrAt tr T_PROC (F τ))
  have hmem : ∀ τ, τ < n → ∀ x ∈ g τ, x < tr.height T_PROC ∧ cv tr T_PROC x Proc.tau = τ := by
    intro τ hτ x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    obtain ⟨hτf, I⟩ := hF τ hτ
    have H := (I.hdr i (List.mem_range.mp hi)).1
    exact ⟨H.1, H.2.2.1.trans hτf⟩
  have hnd : ∀ τ, ((g τ)).Nodup := by
    intro τ
    show List.Pairwise (· ≠ ·) _
    rw [List.pairwise_map]
    exact List.pairwise_lt_range.imp (fun {i j} h => by
      have := Proc.hdrAt_mono tr T_PROC (F τ) h; omega)
  have key : ∀ k, k ≤ n →
      ((List.range' (n - k) k).flatMap g).Nodup ∧
      ∀ x ∈ (List.range' (n - k) k).flatMap g, x < tr.height T_PROC ∧
        n - k ≤ cv tr T_PROC x Proc.tau := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      obtain ⟨ih1, ih2⟩ := ih (by omega)
      rw [show n - (k + 1) = n - (k + 1) by rfl, List.range'_succ, List.flatMap_cons,
        show n - (k + 1) + 1 = n - k by omega]
      refine ⟨List.nodup_append.mpr ⟨hnd _, ih1, ?_⟩, ?_⟩
      · intro x hx y hy hxy
        subst hxy
        have := (hmem (n - (k + 1)) (by omega) x hx).2
        have := (ih2 x hy).2
        omega
      · intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · have := hmem (n - (k + 1)) (by omega) x hx; omega
        · have := ih2 x hx; omega
  have hS := key n (Nat.le_refl _)
  rw [Nat.sub_self, ← List.range_eq_range'] at hS
  have hsum : ((List.range n).map fun τ =>
      ((List.range (M τ)).map fun i => hdrW tr (Proc.hdrAt tr T_PROC (F τ) i)).sum).sum =
      (((List.range n).flatMap g).map (hdrW tr)).sum := by
    rw [sum_flatMap']
    simp only [g, List.map_map]
    rfl
  rw [hsum]
  refine Nat.le_trans (nodup_sum_le hS.1 (fun x hx => (hS.2 x hx).1) _) ?_
  exact sum_le_sum_range (fun r hr => hdrW_le hL hr)

open ZkFormal.NearV3.Sched in
/-- **The AIR half of `A9Link`** (L2): for any family of instance blocks of `procV3` with distinct
`tau`, the RNG positions after their last rounds sum to at most the active rows of `rngV3`. -/
theorem a9_air (hH : HoldsP nearAirV3 pub tr) {n : Nat} {F M : Nat → Nat}
    (hF : ∀ τ, τ < n → cv tr T_PROC (F τ) Proc.tau = τ ∧ Proc.Inst tr T_PROC (F τ) (M τ)) :
    ((List.range n).map fun τ => lastK tr (F τ) (M τ)).sum ≤ Rng.activeRows tr T_RNG := by
  have SO := LinkSchedCore.shufOwn_v3
  have O := LinkSchedCore.schedOwn_v3
  have hLp := pLocal_of hH O.tp_lt O.tp_tab
  have hLs : Shuffle.SLocal tr T_SHUF pub := by
    have := local_of_holdsP hH SO.ts_lt; rw [SO.ts_tab] at this; exact this
  have hG : Shuffle.GenRecv tr T_SHUF pub :=
    genRecv_of_holdsP hH (B := shufB) (by decide) SO.tc_lt SO.tc_tab SO.tg_lt SO.tg_tab
      SO.ts_lt SO.ts_tab SO.onlyC SO.pubC SO.onlyG SO.pubG
  have hHs : tr.height T_SHUF ≤ 2 ^ 22 := by
    have hb := hH.logBound T_SHUF SO.ts_lt
    rw [← tables_get SO.ts_lt, SO.ts_tab] at hb
    exact Nat.pow_le_pow_right (by decide) hb.2
  have hLg := gLocal_of_holdsP hH SO.tg_lt SO.tg_tab
  have hW := chachaRecv_of_holdsP hH SO.tc_lt SO.tc_tab SO.tg_lt SO.tg_tab SO.onlyC SO.pubC
  calc ((List.range n).map fun τ => lastK tr (F τ) (M τ)).sum
      ≤ ((List.range n).map fun τ =>
          ((List.range (M τ)).map fun i => hdrW tr (Proc.hdrAt tr T_PROC (F τ) i)).sum).sum :=
        sum_le_sum_range (fun τ hτ => lastK_le (hF τ hτ).2)
    _ ≤ ((List.range (tr.height T_PROC)).map
          (wrow Proc.interactions tr T_PROC pub B_SSHUF false Wsh)).sum := hdrs_le hLp hF
    _ = ((List.range (tr.height T_SHUF)).map (wrow shufIs tr T_SHUF pub B_SSHUF true Wsh)).sum :=
        (shuf_bal hH Wsh).symm
    _ ≤ ((List.range (tr.height T_SHUF)).map (wrow shufIs tr T_SHUF pub B_SGEN false Wg)).sum :=
        shuf_le hLs hG hHs
    _ = ((List.range (tr.height T_RNG)).map
          (wrow (Rng.Table.interactions B_SCHACHA B_SGEN) tr T_RNG pub B_SGEN true Wg)).sum :=
        (gen_bal hH Wg).symm
    _ ≤ Rng.activeRows tr T_RNG := rng_le hLg hW (by decide)

end V3

end A9Air

end ZkFormal.NearV3.Assembly
