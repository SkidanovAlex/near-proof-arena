import ZkFormal.Near.Extract.BusCount

/-!
# Column agreement

A table's local constraints and traffic read only the columns below the expressions'
`colBound`.  Two traces with the same height that agree on those columns have the same
`TableLocal` and `TableTraffic` (used to add columns to a table without re-proving it).
-/
namespace ZkFormal.NearV3.Render
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

variable {tr1 tr2 : Trace Fp} {t W : Nat}

theorem eval_congr_cols (hh : tr1.log t = tr2.log t)
    (hc : ∀ r c, c < W → tr1.cell t r c = tr2.cell t r c) (pub : List Fp) (r : Nat) :
    ∀ e : Expr, e.colBound ≤ W → e.eval tr1 t r pub = e.eval tr2 t r pub := by
  have hH : tr1.height t = tr2.height t := by unfold Trace.height; rw [hh]
  intro e
  induction e with
  | col cc nx =>
    intro hb
    simp only [Expr.colBound] at hb
    simp only [Expr.eval, Expr.evalWith, rowEnv, hH]
    exact hc _ _ (by omega)
  | add a b iha ihb =>
    intro hb; simp only [Expr.colBound] at hb
    have h1 := iha (by omega); have h2 := ihb (by omega)
    simp only [Expr.eval, Expr.evalWith] at h1 h2 ⊢; rw [h1, h2]; rfl
  | mul a b iha ihb =>
    intro hb; simp only [Expr.colBound] at hb
    have h1 := iha (by omega); have h2 := ihb (by omega)
    simp only [Expr.eval, Expr.evalWith] at h1 h2 ⊢; rw [h1, h2]; rfl
  | neg a ih =>
    intro hb; simp only [Expr.colBound] at hb
    have h1 := ih (by omega)
    simp only [Expr.eval, Expr.evalWith] at h1 ⊢; rw [h1]; rfl
  | _ => intro _; simp only [Expr.eval, Expr.evalWith, rowEnv, hH]

theorem rowTraffic_congr_cols (hh : tr1.log t = tr2.log t)
    (hc : ∀ r c, c < W → tr1.cell t r c = tr2.cell t r c) (is : List Interaction)
    (hb : ∀ i ∈ is, ∀ e ∈ i.mult ++ i.msg, e.colBound ≤ W) (r : Nat) (pub : List Fp) (b : Nat) (sd : Bool) :
    rowTraffic is tr1 t r pub b sd = rowTraffic is tr2 t r pub b sd := by
  unfold rowTraffic
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [List.flatMap_cons]
    rw [ih (fun j hj => hb j (by simp [hj]))]
    congr 1
    have hi := hb i (by simp)
    have hm : i.multNat tr1 t r pub = i.multNat tr2 t r pub := by
      unfold Interaction.multNat
      have H : ∀ (l : List Expr), (∀ e ∈ l, e.colBound ≤ W) → ∀ k,
          Interaction.multNat.go tr1 t r pub l k = Interaction.multNat.go tr2 t r pub l k := by
        intro l; induction l with
        | nil => intro _ k; rfl
        | cons e es ih =>
          intro he k; simp only [Interaction.multNat.go]
          rw [eval_congr_cols hh hc pub r e (he e (by simp)), ih (fun x hx => he x (by simp [hx])) (k+1)]
      exact H i.mult (fun e he => hi e (List.mem_append_left _ he)) 0
    have hv : i.msgVal tr1 t r pub = i.msgVal tr2 t r pub := by
      unfold Interaction.msgVal
      apply List.map_congr_left; intro e he
      exact eval_congr_cols hh hc pub r e (hi e (List.mem_append_right _ he))
    rw [hm, hv]

theorem tableLocal_congr_cols (hh : tr1.log t = tr2.log t)
    (hc : ∀ r c, c < W → tr1.cell t r c = tr2.cell t r c) {T : Table} {pub : List Fp}
    (hcols : ∀ e ∈ T.exprs, e.colBound ≤ W) (h : TableLocal T tr2 t pub) : TableLocal T tr1 t pub := by
  have hH : tr1.height t = tr2.height t := by unfold Trace.height; rw [hh]
  refine ⟨by rw [hh]; exact h.log_ge, by rw [hh]; exact h.log_le, ?_, ?_⟩
  · intro r hr e he
    rw [eval_congr_cols hh hc pub r e (hcols e (List.mem_append_left _ he))]
    exact h.constr r (by rw [← hH]; exact hr) e he
  · intro r hr i hi b hb
    rw [eval_congr_cols hh hc pub r b (hcols b (List.mem_append_right _
      (List.mem_flatMap.2 ⟨i, hi, List.mem_append_left _ hb⟩)))]
    exact h.bits r (by rw [← hH]; exact hr) i hi b hb

theorem tableTraffic_congr_cols (hh : tr1.log t = tr2.log t)
    (hc : ∀ r c, c < W → tr1.cell t r c = tr2.cell t r c) {is : List Interaction} {pub : List Fp}
    {tf : Traffic} (hb : ∀ i ∈ is, ∀ e ∈ i.mult ++ i.msg, e.colBound ≤ W)
    (h : TableTraffic is tr2 t pub tf) : TableTraffic is tr1 t pub tf := by
  have hH : tr1.height t = tr2.height t := by unfold Trace.height; rw [hh]
  intro b m
  have e : ∀ sd, tableBusCount is tr1 t pub b sd m = tableBusCount is tr2 t pub b sd m := by
    intro sd
    rw [tableBusCount_eq, tableBusCount_eq, hH]
    congr 1
    congr 1
    funext r
    exact rowTraffic_congr_cols hh hc is hb r pub b sd
  rw [e true, e false]
  exact h b m

/-! ## Pinning a trace to one table index -/

/-- Table `s` of `tr`, read at every table index. -/
def pinTrace (tr : Trace Fp) (s : Nat) : Trace Fp := ⟨fun _ => tr.log s, fun _ r c => tr.cell s r c⟩

theorem eval_pin (tr : Trace Fp) (s t r : Nat) (pub : List Fp) (e : Expr) :
    e.eval (pinTrace tr s) t r pub = e.eval tr s r pub := rfl

theorem rowTraffic_pin (tr : Trace Fp) (s t r : Nat) (pub : List Fp) (is : List Interaction)
    (b : Nat) (sd : Bool) : rowTraffic is (pinTrace tr s) t r pub b sd = rowTraffic is tr s r pub b sd := by
  unfold rowTraffic
  congr 1
  funext i
  have hm : i.multNat (pinTrace tr s) t r pub = i.multNat tr s r pub := by
    unfold Interaction.multNat
    have H : ∀ (l : List Expr) k, Interaction.multNat.go (pinTrace tr s) t r pub l k =
        Interaction.multNat.go tr s r pub l k := by
      intro l; induction l with
      | nil => intro k; rfl
      | cons e es ih => intro k; simp only [Interaction.multNat.go]; rw [eval_pin, ih (k+1)]
    exact H i.mult 0
  have hv : i.msgVal (pinTrace tr s) t r pub = i.msgVal tr s r pub := by
    unfold Interaction.msgVal; apply List.map_congr_left; intro e _; exact eval_pin tr s t r pub e
  rw [hm, hv]

theorem tableLocal_pin {T : Table} {tr : Trace Fp} {s : Nat} {pub : List Fp} (t : Nat)
    (h : TableLocal T tr s pub) : TableLocal T (pinTrace tr s) t pub :=
  ⟨h.log_ge, h.log_le, fun r hr e he => by rw [eval_pin]; exact h.constr r hr e he,
    fun r hr i hi b hb => by rw [eval_pin]; exact h.bits r hr i hi b hb⟩

theorem tableTraffic_pin {is : List Interaction} {tr : Trace Fp} {s : Nat} {pub : List Fp}
    {tf : Traffic} (t : Nat) (h : TableTraffic is tr s pub tf) : TableTraffic is (pinTrace tr s) t pub tf := by
  intro b m
  have e : ∀ sd, tableBusCount is (pinTrace tr s) t pub b sd m = tableBusCount is tr s pub b sd m := by
    intro sd
    rw [tableBusCount_eq, tableBusCount_eq]
    show ((List.range (tr.height s)).flatMap _).count m = _
    congr 2
    funext r
    exact rowTraffic_pin tr s t r pub is b sd
  rw [e true, e false]
  exact h b m

end ZkFormal.NearV3.Render
