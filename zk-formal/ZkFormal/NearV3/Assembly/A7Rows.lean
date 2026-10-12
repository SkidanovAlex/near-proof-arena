import ZkFormal.NearV3.Assembly.A7Trace
import ZkFormal.NearV3.Assembly.A7UpsView

/-!
# ZkFormal.NearV3.Assembly.A7Rows — (E2): the A7 rows of a `upsV3` segment in plan terms

For a segment `s` with layout `UpsLayout s L ps fls ws` and plan `UpsPlan s ps ci ti di si kd sdx`:

* **`a7S_eq`**: `a7S s = L + Σ_k ℓ_k` (the value rows and the node-part rows; the walk rows count nothing);
* **`a7Rpl_sum`**: for any weight `w`, the `RPL` sends weigh `w [nD] + Σ_{k ≥ nT} w [sN_k]` (the segment's first row,
  and the first row of every upper part; a value row's first row has `up = 0`, `valUp`);
* **`a7Rplv_sum`**: the `RPLV` sends weigh `w [vid]` if `pres = 1`, else nothing;
* **`nD_eq`**: on the first row `nD = N_D` (`UpsA7Wf`, `dd` one-hot at `D`).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace ZkFormal.NearV3.UpsRows

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3

/-! ## Sums over rows -/

theorem sum_range_add (f : Nat → Nat) (a b : Nat) :
    ((List.range (a + b)).map f).sum = ((List.range a).map f).sum + ((List.range b).map fun d => f (a + d)).sum := by
  rw [List.range_add, List.map_append, List.sum_append, List.map_map]; rfl

theorem sum_consec (f : Nat → Nat) : ∀ (l : List (Nat × Nat)) (s0 : Nat), Consec s0 l →
    ((List.range (segEnd s0 l - s0)).map fun d => f (s0 + d)).sum =
      (l.map fun p => ((List.range p.2).map fun d => f (p.1 + d)).sum).sum
  | [], s0, _ => by simp [segEnd]
  | (a, ℓ) :: rest, s0, ⟨h1, h2⟩ => by
    subst h1
    have hE := sum_segEnd rest (a + ℓ) h2
    have ih := sum_consec f rest (a + ℓ) h2
    simp only [segEnd, List.map_cons, List.sum_cons]
    rw [show segEnd (a + ℓ) rest - a = ℓ + (segEnd (a + ℓ) rest - (a + ℓ)) by omega, sum_range_add, ← ih]
    congr 1
    apply congrArg; apply List.map_congr_left; intro d _; congr 1; omega

theorem sum_ones : ∀ (n : Nat) (f : Nat → Nat), (∀ d, d < n → f d = 1) → ((List.range n).map f).sum = n
  | 0, _, _ => rfl
  | n + 1, f, h => by
    rw [List.range_succ, List.map_append, List.sum_append, sum_ones n f (fun d hd => h d (by omega))]
    simp [h n (by omega)]

theorem sum_zeros : ∀ (n : Nat) (f : Nat → Nat), (∀ d, d < n → f d = 0) → ((List.range n).map f).sum = 0
  | 0, _, _ => rfl
  | n + 1, f, h => by
    rw [List.range_succ, List.map_append, List.sum_append, sum_zeros n f (fun d hd => h d (by omega))]
    simp [h n (by omega)]

theorem sum_first (n : Nat) (hn : 0 < n) (f : Nat → Nat) (h : ∀ d, 0 < d → d < n → f d = 0) :
    ((List.range n).map f).sum = f 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map,
    sum_zeros m (f ∘ Nat.succ) (fun d hd => h (d + 1) (by omega) (by omega))]
  rfl

theorem map_range_getD {α β : Type} (F : α → β) (d : α) : ∀ l : List α,
    l.map F = (List.range l.length).map fun k => F (l.getD k d)
  | [] => rfl
  | a :: l => by
    rw [List.length_cons, List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, List.getD_cons_zero]
    rw [map_range_getD F d l]
    simp [Function.comp_def, List.getD_cons_succ]

theorem sumFM' {α β : Type} (f : β → Nat) (g : α → List β) : ∀ (l : List α),
    ((l.flatMap g).map f).sum = (l.map fun p => ((g p).map f).sum).sum
  | [] => rfl
  | p :: r => by simp [List.flatMap_cons, List.map_append, List.sum_append, sumFM' f g r]

/-! ## Row facts -/

/-- A value row's first row is not an upper part. -/
theorem valUp {C D : URow} (ok : URowOk C D) (hC : ∀ x, C x < P) (hD : ∀ x, D x < P)
    (hpf : C pf = 1) (hvb : C vb = 1) : C UpsV3.up = 0 := by
  have f1 := factN ok hC hD (e := .mul (c pf) (sub (c UpsV3.up) (sumc [kRDB, kRDE, kPT])))
    (memPlan (by simp [cPlan]))
  have f2 := factN ok hC hD (e := .mul (c vb) (c kRDB)) (memPlan (by simp [cPlan, UpsV3.kinds]))
  have f3 := factN ok hC hD (e := .mul (c vb) (c kRDE)) (memPlan (by simp [cPlan, UpsV3.kinds]))
  have f4 := factN ok hC hD (e := .mul (c vb) (c kPT)) (memPlan (by simp [cPlan, UpsV3.kinds]))
  have b := fun x => hC x
  simp only [P_lit] at b
  have := b UpsV3.up; have := b kRDB; have := b kRDE; have := b kPT
  simp only [sumc, List.map_cons, List.map_nil] at f1
  nev_simp at f1 f2 f3 f4
  simp only [hpf, hvb, P_lit] at f1 f2 f3 f4
  simp at f1 f2 f3 f4
  omega

attribute [local irreducible] UpsSeg.row UpsSeg.next

section
variable {v : List UpsSeg} (hw : UpsWf v) {s : UpsSeg} (hs : s ∈ v)
  {L : Nat} {ps : List (Nat × Nat)} {fls : List (List (Nat × Nat))} {wsl : List Nat}
  (hL : UpsLayout s L ps fls wsl) {ci ti di si : Nat} {kd sdx : Nat → Nat} (hP : UpsPlan s ps ci ti di si kd sdx)
include hw hs hL hP

theorem rowWalk (i : Nat) (hi : i < 4) :
    s.row i vb = 0 ∧ s.row i qb = 0 ∧ s.row i pf = 0 ∧ (s.row i sf = 1 ↔ i = 0) := by
  have hlt : i < s.rows.length := by have := hL.walk.1; omega
  obtain ⟨ha, hact, hwk, -⟩ := kinds (okRow hw hs hlt) (rowLt hw hs i) (nextLt hw hs i)
  have hwk1 := hL.wk i hi
  have hl := layoutRow (okRow hw hs hlt) (rowLt hw hs i) (nextLt hw hs i)
  obtain ⟨bpf, -, hpfq, -⟩ := hl
  have hF := (walkFlags hw hs hL i hi).1
  refine ⟨by omega, by omega, ?_, hF⟩
  rcases bpf with h | h
  · exact h
  · rcases hpfq h with h' | h' <;> omega

theorem rowVal (d : Nat) (hd : d < L) :
    s.row (4 + d) vb = 1 ∧ s.row (4 + d) qb = 0 ∧ s.row (4 + d) sf = 0 ∧ (s.row (4 + d) pf = 1 ↔ d = 0) ∧
      (s.row (4 + d) pf = 1 → s.row (4 + d) UpsV3.up = 0) := by
  have hlt : 4 + d < s.rows.length := by have := hL.value.2.1; omega
  obtain ⟨ha, hact, hwk, -⟩ := kinds (okRow hw hs hlt) (rowLt hw hs (4 + d)) (nextLt hw hs (4 + d))
  obtain ⟨h1, -, h3, -⟩ := hL.value.2.2 d hd
  refine ⟨h1, by omega, by omega, h3, fun hp => valUp (okRow hw hs hlt) (rowLt hw hs _) (nextLt hw hs _) hp h1⟩

theorem rowPart (k : Nat) (hk : k < ps.length) (d : Nat) (hd : d < ps[k].2) :
    s.row (ps[k].1 + d) vb = 0 ∧ s.row (ps[k].1 + d) qb = 1 ∧ s.row (ps[k].1 + d) sf = 0 ∧
      (s.row (ps[k].1 + d) pf = 1 ↔ d = 0) := by
  obtain ⟨-, U⟩ := hL.part k hk
  have hlt : ps[k].1 + d < s.rows.length := by have := U.le; omega
  obtain ⟨ha, hact, hwk, -⟩ := kinds (okRow hw hs hlt) (rowLt hw hs _) (nextLt hw hs _)
  obtain ⟨h1, -, h3, -⟩ := U.rows d hd
  exact ⟨by omega, h1, by omega, h3⟩

theorem partUp (k : Nat) (hk : k < ps.length) : s.row ps[k].1 UpsV3.up = 1 ↔ nTof ci ti ≤ k := by
  by_cases h : nTof ci ti ≤ k
  · exact ⟨fun _ => h, fun _ => (hP.upper k hk h).2.1⟩
  · have := (hP.term k hk (by omega)).2.2.2.1
    constructor
    · intro h'; omega
    · intro h'; exact absurd h' h

theorem rows_len : s.rows.length = 4 + L + (segEnd (4 + L) ps - (4 + L)) := by
  have := hL.cover; have := sum_segEnd ps (4 + L) hL.consec; omega

/-- **(E2) value and node-part rows.** -/
theorem a7S_eq : s.a7S = L + (ps.map (·.2)).sum := by
  unfold UpsSeg.a7S
  have hc := sum_consec (fun i => s.row i vb + s.row i qb) ps (4 + L) hL.consec
  rw [rows_len hw hs hL hP, sum_range_add, sum_range_add, hc]
  have h1 := sum_zeros 4 (fun i => s.row i vb + s.row i qb) (fun i hi => by
    obtain ⟨a, b, -⟩ := rowWalk hw hs hL hP i hi; simp only [a, b])
  have h2 := sum_ones L (fun d => s.row (4 + d) vb + s.row (4 + d) qb) (fun d hd => by
    obtain ⟨a, b, -⟩ := rowVal hw hs hL hP d hd; simp only [a, b])
  have h3 : (ps.map fun p => ((List.range p.2).map fun d => s.row (p.1 + d) vb + s.row (p.1 + d) qb).sum).sum =
      (ps.map (·.2)).sum := by
    congr 1
    apply List.map_congr_left
    intro p hp
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hp
    exact sum_ones _ _ (fun d hd => by obtain ⟨a, b, -⟩ := rowPart hw hs hL hP k hk d hd; simp only [a, b])
  rw [h1, h2, h3]; omega

/-- **(E2) `RPL`**: the segment's first row sends `[nD]`, every upper part's first row `[sN]`. -/
theorem a7Rpl_sum (w : List Fp → Nat) :
    ((s.a7Rpl.map Msg.toFp).map w).sum = w (Msg.toFp [s.row 0 UnfoldA7.Ups.nD]) +
      ((List.range ps.length).map fun k =>
        if nTof ci ti ≤ k then w (Msg.toFp [s.row (ps.getD k (0, 0)).1 sN]) else 0).sum := by
  unfold UpsSeg.a7Rpl
  rw [List.map_flatMap, sumFM']
  have hc := sum_consec (fun i => ((((a7RplRow (s.row i)).map Msg.toFp)).map w).sum) ps (4 + L) hL.consec
  rw [rows_len hw hs hL hP, sum_range_add, sum_range_add, hc]
  have h1 := sum_first 4 (by omega) (fun i => ((((a7RplRow (s.row i)).map Msg.toFp)).map w).sum) (fun i h0 hi => by
    obtain ⟨-, -, a, b⟩ := rowWalk hw hs hL hP i hi
    have : s.row i sf ≠ 1 := fun h => by have := b.1 h; omega
    simp [a7RplRow, a, this])
  have h0 : ((((a7RplRow (s.row 0)).map Msg.toFp)).map w).sum = w (Msg.toFp [s.row 0 UnfoldA7.Ups.nD]) := by
    obtain ⟨-, -, a, b⟩ := rowWalk hw hs hL hP 0 (by omega)
    simp [a7RplRow, a, b.2 rfl]
  have h2 := sum_zeros L (fun d => ((((a7RplRow (s.row (4 + d))).map Msg.toFp)).map w).sum) (fun d hd => by
    obtain ⟨-, -, a, -, b⟩ := rowVal hw hs hL hP d hd
    by_cases hp : s.row (4 + d) pf = 1
    · simp [a7RplRow, a, b hp]
    · simp [a7RplRow, a, hp])
  have h3 : (ps.map fun p => ((List.range p.2).map fun d =>
        ((((a7RplRow (s.row (p.1 + d))).map Msg.toFp)).map w).sum).sum).sum =
      ((List.range ps.length).map fun k =>
        if nTof ci ti ≤ k then w (Msg.toFp [s.row (ps.getD k (0, 0)).1 sN]) else 0).sum := by
    rw [map_range_getD _ (0, 0) ps]
    congr 1
    apply List.map_congr_left
    intro k hk
    have hk' := List.mem_range.mp hk
    rw [getD_ps hk']
    obtain ⟨-, U⟩ := hL.part k hk'
    rw [sum_first _ U.pos _ (fun d h0 hd => by
      obtain ⟨-, -, a, b⟩ := rowPart hw hs hL hP k hk' d hd
      have : s.row (ps[k].1 + d) pf ≠ 1 := fun h => by have := b.1 h; omega
      simp [a7RplRow, a, this])]
    obtain ⟨-, -, a, b⟩ := rowPart hw hs hL hP k hk' 0 U.pos
    have hu := partUp hw hs hL hP k hk'
    have hpf : s.row ps[k].1 pf = 1 := by simpa using b.2 rfl
    have ha : s.row ps[k].1 sf = 0 := by simpa using a
    by_cases hT : nTof ci ti ≤ k
    · simp [a7RplRow, ha, hpf, hu.2 hT, hT]
    · have : s.row ps[k].1 UpsV3.up ≠ 1 := fun h => hT (hu.1 h)
      simp [a7RplRow, ha, this, hT]
  rw [h1, h0, h2, h3]; omega

/-- **(E2) `RPLV`**: one send `[vid]` on the first row iff `pres = 1`. -/
theorem a7Rplv_sum (w : List Fp → Nat) :
    ((s.a7Rplv.map Msg.toFp).map w).sum = if s.row 0 pres = 1 then w (Msg.toFp [s.row 0 vid]) else 0 := by
  unfold UpsSeg.a7Rplv
  rw [List.map_flatMap, sumFM']
  have hc := sum_consec (fun i => ((((a7RplvRow (s.row i)).map Msg.toFp)).map w).sum) ps (4 + L) hL.consec
  rw [rows_len hw hs hL hP, sum_range_add, sum_range_add, hc]
  have h1 := sum_first 4 (by omega) (fun i => ((((a7RplvRow (s.row i)).map Msg.toFp)).map w).sum) (fun i h0 hi => by
    obtain ⟨-, -, -, b⟩ := rowWalk hw hs hL hP i hi
    have : s.row i sf ≠ 1 := fun h => by have := b.1 h; omega
    simp [a7RplvRow, this])
  have h0 : ((((a7RplvRow (s.row 0)).map Msg.toFp)).map w).sum =
      if s.row 0 pres = 1 then w (Msg.toFp [s.row 0 vid]) else 0 := by
    obtain ⟨-, -, -, b⟩ := rowWalk hw hs hL hP 0 (by omega)
    by_cases hp : s.row 0 pres = 1 <;> simp [a7RplvRow, b.2 rfl, hp]
  have h2 := sum_zeros L (fun d => ((((a7RplvRow (s.row (4 + d))).map Msg.toFp)).map w).sum) (fun d hd => by
    obtain ⟨-, -, a, -⟩ := rowVal hw hs hL hP d hd
    simp [a7RplvRow, a])
  have h3 : (ps.map fun p => ((List.range p.2).map fun d =>
        ((((a7RplvRow (s.row (p.1 + d))).map Msg.toFp)).map w).sum).sum).sum = 0 := by
    apply ZkFormal.NearV3.A7UpsProof.sumZ
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
    exact sum_zeros _ _ (fun d hd => by
      obtain ⟨-, -, a, -⟩ := rowPart hw hs hL hP k hk d hd
      simp [a7RplvRow, a])
  rw [h1, h0, h2, h3]; omega

/-- **`nD = N_D`** on the first row. -/
theorem nD_eq (hA : UpsA7Wf v) : s.row 0 UnfoldA7.Ups.nD = s.row 0 (11 + di) := by
  have h0 : 0 < s.rows.length := by have := hL.walk.1; omega
  have h := hA s hs
  have hdd := (hP.seg 0 h0).2.2.1
  have e : nev (s.row 0) (s.next 0) (sum [.mul (c UpsV3.dd0) (c UpsV3.N0), .mul (c UpsV3.dd1) (c UpsV3.N1),
      .mul (c UpsV3.dd2) (c UpsV3.N2)]) = s.row 0 (11 + di) :=
    nev_sel3 (okRow hw hs h0) (rowLt hw hs 0) (nextLt hw hs 0) (base := 28) (off := 11) hP.ix.2.2.1 hdd
  have e2 := uev_toNat (rowLt hw hs 0) (nextLt hw hs 0) (sum [.mul (c UpsV3.dd0) (c UpsV3.N0),
    .mul (c UpsV3.dd1) (c UpsV3.N1), .mul (c UpsV3.dd2) (c UpsV3.N2)]) rfl
  rw [← h, toNat_natCast, Nat.mod_eq_of_lt (rowLt hw hs 0 _), e] at e2
  exact e2

end

end ZkFormal.NearV3.UpsRows
