import ZkFormal.NearV3.Render.Padded

/-!
# Row-bounded trace congruence

`TableLocal` and `TableTraffic` of table `t` read only the rows `r < 2^log t` (and the
cyclic successor `(r+1) % 2^log t`).  Two traces with the same height at `t` whose cells
agree on those rows satisfy the same obligations (`tableLocal_congr_rows`,
`tableTraffic_congr_rows`).  This transfers a completeness proof about a function-backed
honest trace to the array-backed `rowsTrace`, whose cells read `0` outside the array.
-/
namespace ZkFormal.NearV3.Render
open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Air ZkFormal.Algebra

theorem foldr_congr_mem {α β : Type} (f g : α → β → β) (b : β) :
    ∀ (l : List α), (∀ x ∈ l, ∀ y, f x y = g x y) → l.foldr f b = l.foldr g b
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.foldr_cons]
    rw [foldr_congr_mem f g b xs (fun z hz => h z (List.mem_cons_of_mem _ hz))]
    exact h x (List.mem_cons_self ..) _

section
variable {tr₁ tr₂ : Trace Fp} {t : Nat} (hl : tr₁.log t = tr₂.log t)
  (hc : ∀ r, r < tr₁.height t → ∀ c, tr₁.cell t r c = tr₂.cell t r c)
include hl hc

omit hc in
theorem height_congr_rows : tr₁.height t = tr₂.height t := by
  unfold Trace.height; rw [hl]

theorem rowEnv_congr_rows (r : Nat) (hr : r < tr₁.height t) (pub : List Fp) :
    rowEnv tr₁ t r pub = rowEnv tr₂ t r pub := by
  have hh := height_congr_rows hl
  have hcol : (fun (c : Nat) (nx : Bool) => tr₁.cell t (if nx then (r + 1) % tr₁.height t else r) c) =
      (fun (c : Nat) (nx : Bool) => tr₂.cell t (if nx then (r + 1) % tr₂.height t else r) c) := by
    funext c nx
    rw [← hh]
    cases nx
    · exact hc r hr c
    · exact hc _ (Nat.mod_lt _ (Nat.two_pow_pos _)) c
  unfold rowEnv
  rw [hh]
  rw [hh] at hcol
  simp only [hcol]

theorem eval_congr_rows (e : Expr) (r : Nat) (hr : r < tr₁.height t) (pub : List Fp) :
    e.eval tr₁ t r pub = e.eval tr₂ t r pub := by
  unfold Expr.eval; rw [rowEnv_congr_rows hl hc r hr pub]

theorem multNat_congr_rows (i : Interaction) (r : Nat) (hr : r < tr₁.height t) (pub : List Fp) :
    i.multNat tr₁ t r pub = i.multNat tr₂ t r pub := by
  unfold Interaction.multNat
  generalize 0 = k
  induction i.mult generalizing k with
  | nil => rfl
  | cons b bs ih =>
    simp only [Interaction.multNat.go]
    rw [ih, show b.eval tr₁ t r pub = b.eval tr₂ t r pub from eval_congr_rows hl hc b r hr pub]

theorem msgVal_congr_rows (i : Interaction) (r : Nat) (hr : r < tr₁.height t) (pub : List Fp) :
    i.msgVal tr₁ t r pub = i.msgVal tr₂ t r pub := by
  simp only [Interaction.msgVal, eval_congr_rows hl hc _ r hr pub]

theorem tableBusCount_congr_rows (is : List Interaction) (pub : List Fp) (b : Nat) (s : Bool)
    (m : List Fp) : tableBusCount is tr₁ t pub b s m = tableBusCount is tr₂ t pub b s m := by
  unfold tableBusCount
  rw [← height_congr_rows hl]
  apply foldr_congr_mem
  intro r hr acc
  have hr' := List.mem_range.mp hr
  simp only [msgVal_congr_rows hl hc _ r hr' pub, multNat_congr_rows hl hc _ r hr' pub]

theorem tableLocal_congr_rows {T : ZkFormal.Air.Table} {pub : List Fp} (h : TableLocal T tr₁ t pub) :
    TableLocal T tr₂ t pub := by
  have hh := height_congr_rows hl
  refine ⟨hl ▸ h.log_ge, hl ▸ h.log_le, ?_, ?_⟩
  · intro r hr e he
    rw [← hh] at hr
    rw [← eval_congr_rows hl hc e r hr pub]
    exact h.constr r hr e he
  · intro r hr i hi b hb
    rw [← hh] at hr
    rw [← eval_congr_rows hl hc b r hr pub]
    exact h.bits r hr i hi b hb

theorem tableTraffic_congr_rows {is : List Interaction} {pub : List Fp} {tf : Traffic}
    (h : TableTraffic is tr₁ t pub tf) : TableTraffic is tr₂ t pub tf := by
  intro b m
  rw [← tableBusCount_congr_rows hl hc, ← tableBusCount_congr_rows hl hc]
  exact h b m

end

/-- The array-backed trace of `mkTab (2^log) W f` agrees with the function-backed trace of
`f` on every row of its height, provided `f` vanishes beyond column `W`. -/
theorem rowsTrace_cells (log W : Nat) (f : Nat → Nat → Nat) (hf : ∀ r c, W ≤ c → f r c = 0)
    (t r : Nat) (hr : r < 2 ^ log) (c : Nat) :
    (rowsTrace log (mkTab (2 ^ log) W f)).cell t r c = Fp.ofNat (f r c) := by
  by_cases h2 : c < W
  · exact rowsTrace_mkTab log W f t r c hr h2
  · unfold rowsTrace
    dsimp only
    simp [mkTab, Array.getD_eq_getD_getElem?, hr, h2, hf r c (Nat.le_of_not_lt h2)]


/-- The array-backed copy of table `t` of any trace (canonical naturals of its cells, width `W`). -/
def arrTrace (tr : Trace Fp) (t W : Nat) : Trace Fp :=
  rowsTrace (tr.log t) (mkTab (2 ^ tr.log t) W (fun r c => (tr.cell t r c).toNat))

/-- `arrTrace` agrees with the source on the rows of its table when the source vanishes beyond
column `W` there. -/
theorem arrTrace_cells (tr : Trace Fp) (t W : Nat)
    (hz : ∀ r, r < tr.height t → ∀ c, W ≤ c → tr.cell t r c = 0) :
    ∀ r, r < tr.height t → ∀ c, tr.cell t r c = (arrTrace tr t W).cell t r c := by
  intro r hr c
  have hr' : r < 2 ^ tr.log t := hr
  unfold arrTrace
  by_cases hc : c < W
  · rw [rowsTrace_mkTab _ _ _ t r c hr' hc, Fp.ofNat_toNat]
  · unfold rowsTrace
    dsimp only
    rw [hz r hr c (Nat.le_of_not_lt hc)]
    simp [mkTab, Array.getD_eq_getD_getElem?, hr', hc]
    rfl

theorem arrTrace_log (tr : Trace Fp) (t W t' : Nat) : (arrTrace tr t W).log t' = tr.log t := rfl

/-- Local legality and traffic transfer from a trace to its array-backed copy. -/
theorem arrTrace_transfer {tr : Trace Fp} {t W : Nat} {pub : List Fp}
    (hz : ∀ r, r < tr.height t → ∀ c, W ≤ c → tr.cell t r c = 0) :
    (∀ {T : ZkFormal.Air.Table}, TableLocal T tr t pub → TableLocal T (arrTrace tr t W) t pub) ∧
    (∀ {is : List Interaction} {tf : Traffic}, TableTraffic is tr t pub tf →
      TableTraffic is (arrTrace tr t W) t pub tf) :=
  ⟨fun h => tableLocal_congr_rows (tr₁ := tr) (tr₂ := arrTrace tr t W) rfl (arrTrace_cells tr t W hz) h,
   fun h => tableTraffic_congr_rows (tr₁ := tr) (tr₂ := arrTrace tr t W) rfl (arrTrace_cells tr t W hz) h⟩

/-- Bus counts on a bus no interaction uses vanish. -/
theorem tableBusCount_off_bus (is : List Interaction) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (b : Nat) (s : Bool) (m : List Fp) (h : ∀ i ∈ is, i.bus ≠ b) :
    tableBusCount is tr t pub b s m = 0 := by
  simp only [tableBusCount]
  induction List.range (tr.height t) with
  | nil => rfl
  | cons r rs ih =>
    rw [List.foldr_cons, ih]
    clear ih
    induction is with
    | nil => rfl
    | cons i is ih' =>
      rw [List.foldr_cons, ih' (fun j hj => h j (List.mem_cons_of_mem _ hj))]
      have := h i (List.mem_cons_self ..)
      simp [this]

/-- Field messages as natural-number messages (exact on `Fp`: `ofNat ∘ toNat = id`). -/
def natMsgs (l : List (List Fp)) : List ZkFormal.Near.Msg := l.map (·.map Fp.toNat)

theorem natMsgs_toFp (l : List (List Fp)) : (natMsgs l).map ZkFormal.Near.Msg.toFp = l := by
  unfold natMsgs ZkFormal.Near.Msg.toFp
  rw [List.map_map]
  conv => rhs; rw [← List.map_id l]
  apply List.map_congr_left
  intro m _
  simp only [Function.comp, List.map_map]
  conv => rhs; rw [← List.map_id m]
  apply List.map_congr_left
  intro x _
  exact Fp.ofNat_toNat x

end ZkFormal.NearV3.Render
