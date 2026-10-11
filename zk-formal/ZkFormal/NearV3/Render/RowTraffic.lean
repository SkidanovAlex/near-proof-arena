import ZkFormal.NearV3.Render.PaddedCongr
import ZkFormal.NearV3.Candidates.ShaHeight.Traffic

/-!
# Exact traffic of a row-function table, trace-free

For a table whose interaction expressions read only the current row (`currentOnly`: no
next-row cells, no row selectors), the bus traffic of any trace whose table `t` has the cells
`Fp.ofNat (cell r c)` on its `2^L` rows is determined by `cell` alone: `rowsTraffic is cell L pub`,
computed row by row on the single-row trace of `cell` (`rowFn`).  `rowFn_traffic` turns this into
`TableTraffic` (`natMsgs`, exact on `Fp`).
-/
namespace ZkFormal.NearV3.Render
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra
open ZkFormal.NearV3.Candidates.ShaHeight

/-- The trace whose every table and row reads row `r` of `cell` (height `2^L`). -/
def rowFn (cell : Nat → Nat → Nat) (L r : Nat) : Trace Fp :=
  ⟨fun _ => L, fun _ _ c => Fp.ofNat (cell r c)⟩

/-- The messages of all rows, as field elements (trace-free: a function of `cell`, `L`, `pub`). -/
def rowsTrafficFp (is : List Interaction) (cell : Nat → Nat → Nat) (L t : Nat) (pub : List Fp)
    (b : Nat) (s : Bool) : List (List Fp) :=
  (List.range (2 ^ L)).flatMap fun r => rowTraffic is (rowFn cell L r) t r pub b s

/-- The traffic of a row-function table. -/
def rowsTraffic (is : List Interaction) (cell : Nat → Nat → Nat) (L t : Nat) (pub : List Fp) : Traffic :=
  ⟨fun b => natMsgs (rowsTrafficFp is cell L t pub b true),
   fun b => natMsgs (rowsTrafficFp is cell L t pub b false)⟩

/-- All interaction expressions read the current row only. -/
def CurrentOnly (is : List Interaction) : Prop :=
  ∀ i ∈ is, ∀ e ∈ i.exprs, currentOnly e = true

theorem flatMap_congr_rt {α β : Type} {l : List α} {f g : α → List β} (h : ∀ x ∈ l, f x = g x) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons]
    rw [h x (List.mem_cons_self ..), ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]

theorem rowTraffic_current (is : List Interaction) (hc : CurrentOnly is) (a b : Trace Fp)
    (t r : Nat) (pub : List Fp) (hcell : ∀ c, a.cell t r c = b.cell t r c) (bus : Nat) (s : Bool) :
    rowTraffic is a t r pub bus s = rowTraffic is b t r pub bus s := by
  unfold rowTraffic
  apply flatMap_congr_rt
  intro i hi
  have hm : i.multNat a t r pub = i.multNat b t r pub := by
    unfold Interaction.multNat
    have key : ∀ (xs : List Expr), (∀ e ∈ xs, currentOnly e = true) → ∀ k,
        Interaction.multNat.go a t r pub xs k = Interaction.multNat.go b t r pub xs k := by
      intro xs
      induction xs with
      | nil => intro _ k; rfl
      | cons x xs ih =>
        intro hx k
        simp only [Interaction.multNat.go]
        rw [eval_current x (hx x (List.mem_cons_self ..)) a b t r pub hcell,
          ih (fun e he => hx e (List.mem_cons_of_mem _ he))]
    exact key i.mult (fun e he => hc i hi e (List.mem_append_left _ he)) 0
  have hv : i.msgVal a t r pub = i.msgVal b t r pub := by
    unfold Interaction.msgVal
    apply List.map_congr_left
    intro e he
    exact eval_current e (hc i hi e (List.mem_append_right _ he)) a b t r pub hcell
  rw [hm, hv]

/-- **Exact traffic of a row-function table.** -/
theorem rowFn_traffic (is : List Interaction) (hc : CurrentOnly is) (cell : Nat → Nat → Nat)
    (tr : Trace Fp) (t L : Nat) (pub : List Fp) (hlog : tr.log t = L)
    (hcell : ∀ r, r < 2 ^ L → ∀ c, tr.cell t r c = Fp.ofNat (cell r c)) :
    TableTraffic is tr t pub (rowsTraffic is cell L t pub) := by
  have hrow : ∀ bus s, (List.range (tr.height t)).flatMap (fun r => rowTraffic is tr t r pub bus s) =
      rowsTrafficFp is cell L t pub bus s := by
    intro bus s
    unfold rowsTrafficFp
    rw [show tr.height t = 2 ^ L by unfold Trace.height; rw [hlog]]
    apply flatMap_congr_rt
    intro r hr
    rw [rowTraffic_current is hc tr (rowFn cell L r) t r pub
      (fun c => hcell r (List.mem_range.mp hr) c) bus s]
  intro bus m
  rw [tableBusCount_eq, tableBusCount_eq, hrow, hrow]
  exact ⟨by simp only [rowsTraffic, natMsgs_toFp], by simp only [rowsTraffic, natMsgs_toFp]⟩

end ZkFormal.NearV3.Render
