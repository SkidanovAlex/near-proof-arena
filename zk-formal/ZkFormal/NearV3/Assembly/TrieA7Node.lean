import ZkFormal.NearV3.Assembly.RenderV3Trie
import ZkFormal.Near.Render.Proof.RcptCells

/-!
# ZkFormal.NearV3.Assembly.TrieA7Node — record-level traffic of `nodeA7`'s appended interactions

The A7 extension of `nodeV3` (`Tables/UnfoldA7.lean`, `UnfoldA7.Node.interactions`) receives
`RPL (nid)` on the first row of every replaced record and sends `SIZE (3, ra)` on the `SUM`
row.  With the replaced records chosen by a predicate `S` on record ids (`selN vs S`: the row
choice of `nodeA7Trace`, true on the rows of records `n` with `S n`):

* `node_rpl_recvs`: the `RPL` receives are `[n]` for the records `n` with `S n`, in order;
* `node_rpl_sends`: no `RPL` sends;
* `node_size_sends`: the only `SIZE` send is `[3, nodeA7Total vs S]`, with
  `nodeA7Total vs S = Σ_n (2 − [S n]) · |ser n|` (the record's rows are its pre bytes);
* `node_size_recvs`: no `SIZE` receives.
-/

namespace ZkFormal.NearV3.Assembly.TrieA7

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.Render
  ZkFormal.NearV3.UnfoldA7

/-! ## Generic facts -/

theorem multNat_one {i : Interaction} {g : Expr} (h : i.mult = [g]) (tr : Trace Fp) (t r : Nat)
    (pub : List Fp) : i.multNat tr t r pub = if g.eval tr t r pub = 1 then 1 else 0 := by
  simp [Interaction.multNat, Interaction.multNat.go, h]

theorem flatMap_filter_single (S : Nat → Bool) (l : List Nat) :
    l.flatMap (fun n => if S n = true then [[n]] else []) = (l.filter S).map fun n => [n] := by
  induction l with
  | nil => rfl
  | cons x l ih => cases h : S x <;> simp [List.filter_cons, h, ih]

theorem length_le_sum {α : Type} (l : List α) (f : α → Nat) (h : ∀ x ∈ l, 1 ≤ f x) :
    l.length ≤ (l.map f).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    have := h x (by simp)
    have := ih (fun y hy => h y (by simp [hy]))
    omega

theorem prefixF_eq (g : Nat → Fp) : ∀ n, prefixF g n = ((List.range n).map g).foldr (· + ·) 0
  | 0 => rfl
  | n + 1 => by
    rw [prefixF, prefixF_eq g n, List.range_succ, List.map_append, List.foldr_append]
    simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    generalize (List.range n).map g = l
    induction l with
    | nil => simp only [List.foldr_nil]; grind
    | cons a l ih => simp only [List.foldr_cons]; rw [← ih]; grind

theorem foldr_append_fp (a b : List Fp) :
    (a ++ b).foldr (· + ·) 0 = a.foldr (· + ·) 0 + b.foldr (· + ·) 0 := by
  induction a with
  | nil => simp only [List.nil_append, List.foldr_nil]; grind
  | cons x a ih => simp only [List.cons_append, List.foldr_cons, ih]; grind

theorem foldr_flatMap_fp {α : Type} (l : List α) (f : α → List Fp) :
    (l.flatMap f).foldr (· + ·) 0 = (l.map fun x => (f x).foldr (· + ·) 0).foldr (· + ·) 0 := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [List.flatMap_cons, foldr_append_fp, ih, List.map_cons, List.foldr_cons]

theorem foldr_ofNat (l : List Nat) : (l.map Fp.ofNat).foldr (· + ·) 0 = Fp.ofNat l.sum := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.map_cons, List.foldr_cons, ih, List.sum_cons]
    exact (ZkFormal.Near.Render.RcptP.ofNat_add_e x l.sum).symm

/-! ## `nodeA7` -/

section Node
open NodeGen3
open ZkFormal.Near.Render.NodeGen (b2n)

/-- The row choice of replaced node records: the record rows of the records `n` with `S n`. -/
def selN (vs : List NodeS3) (S : Nat → Bool) (q : Nat) : Bool :=
  decide (q < R vs) && S ((recsOf vs).getD q default).n

/-- The A7 node total `Σ_n (2 − [S n]) · |ser n|`. -/
def nodeA7Total (vs : List NodeS3) (S : Nat → Bool) : Nat :=
  ((List.range vs.length).map fun n => (if S n then 1 else 2) * ((rec vs n).v.ser false).length).sum

theorem node_base_cell (vs : List NodeS3) (q x : Nat) (hq : q < (nodeTraceAligned vs).height T_NODE)
    (hx : x < ZkFormal.NearV3.NodeV3.width) :
    (nodeTraceAligned vs).cell T_NODE q x =
      Fp.ofNat (NodeGen3.cell vs ((nodeTraceAligned vs).height T_NODE) q x) :=
  rowsTrace_mkTab _ _ _ _ q x hq hx

theorem node_height (vs : List NodeS3) (hok : NodeOk vs) : R vs + 1 ≤ (nodeTraceAligned vs).height T_NODE := by
  have hh := padded_log_fits ((vs.map fun s => (s.v.ser false).length).sum + 1) hok.rows
  rw [R_eq hok]; exact hh.1

theorem length_le_R (vs : List NodeS3) : vs.length ≤ R vs := by
  have : R vs = ((List.range vs.length).map fun n => (layN vs n).length).sum := by
    simp [R, recsOf, nodeRecs, List.length_flatMap]
  rw [this]
  have := length_le_sum (List.range vs.length) (fun n => (layN vs n).length)
    (fun n _ => lay_pos (rec vs n).v)
  simpa using this

theorem node_P (vs : List NodeS3) (hok : NodeOk vs) : R vs < P := by
  have := hok.rows; rw [← R_eq hok] at this
  have : (2 : Nat) ^ 22 < P := by decide
  omega

/-- `nodeA7`'s appended cells on a row: `nf`, `nid`, `rpl`. -/
theorem node_cells (vs : List NodeS3) (S : Nat → Bool) (q : Nat)
    (hq : q < (nodeTraceAligned vs).height T_NODE) :
    let tr := nodeA7Trace vs T_NODE (selN vs S)
    let H := (nodeTraceAligned vs).height T_NODE
    tr.cell T_NODE q ZkFormal.NearV3.NodeV3.nf = Fp.ofNat (NodeGen3.cell vs H q 1) ∧
    tr.cell T_NODE q ZkFormal.NearV3.NodeV3.nid = Fp.ofNat (NodeGen3.cell vs H q 4) ∧
    tr.cell T_NODE q ZkFormal.NearV3.NodeV3.sumr = Fp.ofNat (NodeGen3.cell vs H q 3) ∧
    tr.cell T_NODE q Node.rpl =
      (if selN vs S q = true ∧ Fp.ofNat (NodeGen3.cell vs H q 1) = 1 then 1 else 0) ∧
    tr.cell T_NODE q Node.ra = prefixF (nodeInc (nodeTraceAligned vs) T_NODE (selN vs S)) q := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [nodeA7Trace]; rw [cell_withCols_lt (by decide)]; exact node_base_cell vs q _ hq (by decide)
  · simp only [nodeA7Trace]; rw [cell_withCols_lt (by decide)]; exact node_base_cell vs q _ hq (by decide)
  · simp only [nodeA7Trace]; rw [cell_withCols_lt (by decide)]; exact node_base_cell vs q _ hq (by decide)
  · simp only [nodeA7Trace]; rw [cell_withCols_ge (by decide)]
    simp only [nodeCols, Node.rpl, ite_true, nodeRpl]
    rw [node_base_cell vs q ZkFormal.NearV3.NodeV3.nf hq (by decide)]; rfl
  · simp only [nodeA7Trace]; rw [cell_withCols_ge (by decide)]
    simp [nodeCols, Node.rpl, Node.ra]

theorem cell1_le (vs : List NodeS3) (H q : Nat) : NodeGen3.cell vs H q 1 ≤ 1 :=
  NodeGen3.cell_bool vs H q (x := 1) (by decide)

theorem ofNat01 (x : Nat) (hx : x ≤ 1) : (Fp.ofNat x = 1 ↔ x = 1) := by
  rcases (show x = 0 ∨ x = 1 by omega) with rfl | rfl <;> decide

/-- One row's `RPL` receives. -/
theorem node_rpl_row (vs : List NodeS3) (S : Nat → Bool) (pub : List Fp) (q : Nat)
    (hq : q < (nodeTraceAligned vs).height T_NODE) :
    (rowTraffic UnfoldA7.Node.interactions (nodeA7Trace vs T_NODE (selN vs S)) T_NODE q pub B_RPL false).map
        (List.map Fp.toNat) =
      if selN vs S q = true ∧ NodeGen3.cell vs ((nodeTraceAligned vs).height T_NODE) q 1 = 1 then
        [[NodeGen3.cell vs ((nodeTraceAligned vs).height T_NODE) q 4 % P]] else [] := by
  obtain ⟨cF, cI, -, cR, -⟩ := node_cells vs S q hq
  have hb := cell1_le vs ((nodeTraceAligned vs).height T_NODE) q
  have o1 : Fp.ofNat 1 = (1 : Fp) := by decide
  have o0 : Fp.ofNat 0 = (0 : Fp) := by decide
  have z : ((0 : Fp) = 1) = False := by decide
  have m11 : Fp.mul 1 1 = 1 := by decide
  have m10 : (Fp.mul 1 0 = 1) = False := by decide
  have m01 : (Fp.mul 0 1 = 1) = False := by decide
  have m00 : (Fp.mul 0 0 = 1) = False := by decide
  rcases (show NodeGen3.cell vs ((nodeTraceAligned vs).height T_NODE) q 1 = 0 ∨
      NodeGen3.cell vs ((nodeTraceAligned vs).height T_NODE) q 1 = 1 by omega) with h | h <;>
  by_cases hs : selN vs S q = true <;>
  simp [rowTraffic, UnfoldA7.Node.interactions, Dsl.recv, Dsl.send, B_RPL, B_SIZE, Interaction.multNat,
    Interaction.multNat.go, Interaction.msgVal, cF, cI, cR, h, hs, o1, o0, z, m11, m10, m01, m00]

theorem selN_lt {vs : List NodeS3} {S : Nat → Bool} {q : Nat} (h : selN vs S q = true) : q < R vs := by
  simp only [selN, Bool.and_eq_true, decide_eq_true_eq] at h; exact h.1

theorem rec_flat (vs : List NodeS3) (S : Nat → Bool) :
    (List.range (R vs)).flatMap (fun q =>
      if (S ((recsOf vs).getD q default).n = true ∧ ((recsOf vs).getD q default).pos = 0) then
        [[((recsOf vs).getD q default).n]] else []) =
      (List.range vs.length).flatMap (fun n => if S n = true then [[n]] else []) := by
  rw [show R vs = (recsOf vs).length from rfl,
    ← ZkFormal.Near.Render.flatMap_getD default (recsOf vs)
      (fun r => if (S r.n = true ∧ r.pos = 0) then [[r.n]] else [])]
  simp only [recsOf, List.flatMap_assoc, nodeRecs, List.flatMap_map]
  apply ZkFormal.Near.Render.flatMap_congr'
  intro n _
  obtain ⟨m, hm⟩ : ∃ m, (layN vs n).length = m + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos (lay_pos (rec vs n).v)).symm⟩
  rw [hm, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
  rw [ZkFormal.Near.Render.flatMap_nil' (fun p _ => by simp [mkR])]
  simp [mkR]

/-- **`RPL` receives of the honest `nodeA7` trace**: one `[n]` per record `n` with `S n`. -/
theorem node_rpl_recvs (vs : List NodeS3) (hok : NodeOk vs) (S : Nat → Bool) (pub : List Fp) :
    (traceTraffic UnfoldA7.Node.interactions (nodeA7Trace vs T_NODE (selN vs S)) T_NODE pub).recvs B_RPL =
      ((List.range vs.length).filter S).map fun n => [n] := by
  have hH := node_height vs hok
  have hP := node_P vs hok
  have hL := length_le_R vs
  simp only [traceTraffic]
  rw [show (nodeA7Trace vs T_NODE (selN vs S)).height T_NODE = (nodeTraceAligned vs).height T_NODE from rfl]
  rw [ZkFormal.Near.Render.flatMap_congr' (fun q hq => node_rpl_row vs S pub q (List.mem_range.1 hq)),
    ZkFormal.Near.Render.range_split (show R vs ≤ (nodeTraceAligned vs).height T_NODE by omega),
    List.flatMap_append,
    ZkFormal.Near.Render.flatMap_nil' (l := List.map _ _) (fun q hq => by
      obtain ⟨q', _, rfl⟩ := List.mem_map.1 hq
      have : selN vs S (R vs + q') = false := by
        simp only [selN, Bool.and_eq_false_imp, decide_eq_true_eq]; intro h; omega
      simp [this]),
    List.append_nil, ← flatMap_filter_single, ← rec_flat]
  apply ZkFormal.Near.Render.flatMap_congr'
  intro q hq
  have hq' := List.mem_range.1 hq
  rw [cell_node hq', Rc.c1, Rc.c4]
  have hn : ((recsOf vs).getD q default).n < P := by
    have : ((recsOf vs).getD q default).n < vs.length := by
      have hmem : (recsOf vs).getD q default ∈ recsOf vs := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by exact hq'), Option.getD_some]
        exact List.getElem_mem _
      simp only [recsOf, nodeRecs, List.mem_flatMap, List.mem_map, List.mem_range] at hmem
      obtain ⟨n, hn, p, _, he⟩ := hmem
      show ((List.flatMap (nodeRecs vs) (List.range vs.length)).getD q default).n < vs.length
      rw [← he]; exact hn
    omega
  rw [Nat.mod_eq_of_lt hn]
  simp only [selN, decide_eq_true hq', Bool.true_and, b2n]
  by_cases hs : S ((recsOf vs).getD q default).n = true <;>
    by_cases hp : ((recsOf vs).getD q default).pos = 0 <;> simp [hs, hp]


/-- The per-row increment of `ra` on a record row, as a function of the record row. -/
def incG (vs : List NodeS3) (S : Nat → Bool) (r : NRec) : Fp :=
  2 - (if S r.n = true ∧ r.pos = 0 then Fp.ofNat ((rec vs r.n).v.ser false).length else 0)

theorem nodeInc_row (vs : List NodeS3) (S : Nat → Bool) (q : Nat) (hq : q < R vs)
    (hH : q < (nodeTraceAligned vs).height T_NODE) :
    nodeInc (nodeTraceAligned vs) T_NODE (selN vs S) q = incG vs S ((recsOf vs).getD q default) := by
  have e : ∀ x, x < ZkFormal.NearV3.NodeV3.width → (nodeTraceAligned vs).cell T_NODE q x =
      Fp.ofNat (rowCell vs ((recsOf vs).getD q default) x) := fun x hx => by
    rw [node_base_cell vs q x hH hx, cell_node hq]
  have hs : selN vs S q = S ((recsOf vs).getD q default).n := by simp [selN, hq]
  simp only [nodeInc, nodeRpl, incG, hs, e _ (show ZkFormal.NearV3.NodeV3.act < _ by decide),
    e _ (show ZkFormal.NearV3.NodeV3.nf < _ by decide), e _ (show ZkFormal.NearV3.NodeV3.len < _ by decide)]
  rw [show ZkFormal.NearV3.NodeV3.act = 0 from rfl, show ZkFormal.NearV3.NodeV3.nf = 1 from rfl,
    show ZkFormal.NearV3.NodeV3.len = 6 from rfl, Rc.c0, Rc.c1, Rc.c6]
  have o1 : Fp.ofNat 1 = (1 : Fp) := by decide
  have o0 : Fp.ofNat 0 = (0 : Fp) := by decide
  have z : ((0 : Fp) = 1) = False := by decide
  by_cases h1 : S ((recsOf vs).getD q default).n = true <;>
    by_cases h2 : ((recsOf vs).getD q default).pos = 0 <;> simp [h1, h2, b2n, o1, o0, z] <;> grind

theorem foldr_const2 (m : Nat) : ((List.range m).map fun _ => (2 : Fp)).foldr (· + ·) 0 = Fp.ofNat (2 * m) := by
  have : ((List.range m).map fun _ => (2 : Fp)) = ((List.range m).map fun _ => 2).map Fp.ofNat := by
    simp only [List.map_map]; rfl
  rw [this, foldr_ofNat]
  congr 1
  clear this
  induction m with
  | zero => rfl
  | succ m ih => rw [List.range_succ, List.map_append, List.sum_append, ih]; simp; omega

theorem rec_inc (vs : List NodeS3) (hok : NodeOk vs) (S : Nat → Bool) (n : Nat) (hn : n < vs.length) :
    ((nodeRecs vs n).map (incG vs S)).foldr (· + ·) 0 =
      Fp.ofNat ((if S n then 1 else 2) * ((rec vs n).v.ser false).length) := by
  have hk := len_eq hok hn
  obtain ⟨m, hm⟩ : ∃ m, (layN vs n).length = m + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos (lay_pos (rec vs n).v)).symm⟩
  rw [hk, hm]
  simp only [nodeRecs, hm, List.range_succ_eq_map, List.map_cons, List.map_map, List.foldr_cons]
  have hrest : (List.range m).map (incG vs S ∘ mkR vs n ∘ Nat.succ) = (List.range m).map fun _ => (2 : Fp) := by
    apply List.map_congr_left; intro p _
    simp [incG, mkR]; decide
  rw [hrest, foldr_const2]
  have h0 : incG vs S (mkR vs n 0) = 2 - (if S n = true then Fp.ofNat (m + 1) else 0) := by
    simp only [incG, mkR, and_true]; rw [hk, hm]
  rw [h0]
  have a1 := ZkFormal.Near.Render.RcptP.ofNat_add_e m 1
  have a2 : Fp.ofNat (2 * m) = Fp.ofNat m + Fp.ofNat m := by
    rw [show 2 * m = m + m by omega]; exact ZkFormal.Near.Render.RcptP.ofNat_add_e m m
  have o1 : Fp.ofNat 1 = (1 : Fp) := by decide
  cases S n
  · simp only [Bool.false_eq_true, ite_false]
    rw [show 2 * (m + 1) = m + m + 1 + 1 by omega, ZkFormal.Near.Render.RcptP.ofNat_add_e,
      ZkFormal.Near.Render.RcptP.ofNat_add_e, ZkFormal.Near.Render.RcptP.ofNat_add_e, a2, o1]
    grind
  · simp only [ite_true, Nat.one_mul]
    rw [a1, a2, o1]
    grind

theorem node_total_lt (vs : List NodeS3) (hok : NodeOk vs) (S : Nat → Bool) : nodeA7Total vs S < P := by
  have h1 : nodeA7Total vs S ≤ 2 * R vs := by
    rw [R_eq hok, nodeA7Total, ← map_getD' default (fun s : NodeS3 => (s.v.ser false).length) vs]
    generalize List.range vs.length = l
    induction l with
    | nil => simp
    | cons x l ih =>
      simp only [List.map_cons, List.sum_cons, Function.comp_def] at ih ⊢
      have : (if S x = true then 1 else 2) * ((rec vs x).v.ser false).length ≤
          2 * ((vs.getD x default).v.ser false).length := by
        show _ ≤ 2 * ((rec vs x).v.ser false).length
        cases S x <;> simp <;> omega
      omega
  have := node_P vs hok
  have : (2 : Nat) ^ 22 < P := by decide
  have := hok.rows; rw [← R_eq hok] at this
  have : 2 * 2 ^ 22 < P := by decide
  omega

/-- The value of `ra` on the `SUM` row: the A7 node total. -/
theorem node_ra (vs : List NodeS3) (hok : NodeOk vs) (S : Nat → Bool) :
    prefixF (nodeInc (nodeTraceAligned vs) T_NODE (selN vs S)) (R vs) = Fp.ofNat (nodeA7Total vs S) := by
  have hH := node_height vs hok
  rw [prefixF_eq, List.map_congr_left (g := fun q => incG vs S ((recsOf vs).getD q default))
    (fun q hq => nodeInc_row vs S q (List.mem_range.1 hq) (by have := List.mem_range.1 hq; omega)),
    show R vs = (recsOf vs).length from rfl, map_getD' default (incG vs S) (recsOf vs)]
  simp only [recsOf, List.map_flatMap, foldr_flatMap_fp]
  rw [List.map_congr_left (g := fun n => Fp.ofNat ((if S n then 1 else 2) * ((rec vs n).v.ser false).length))
    (fun n hn => rec_inc vs hok S n (List.mem_range.1 hn))]
  rw [show (List.range vs.length).map (fun n => Fp.ofNat ((if S n then 1 else 2) * ((rec vs n).v.ser false).length)) =
      ((List.range vs.length).map fun n => (if S n then 1 else 2) * ((rec vs n).v.ser false).length).map Fp.ofNat by
    simp only [List.map_map]; rfl, foldr_ofNat]
  rfl

/-- **`SIZE` sends of the honest `nodeA7` trace**: exactly `[3, nodeA7Total vs S]`. -/
theorem node_size_sends (vs : List NodeS3) (hok : NodeOk vs) (S : Nat → Bool) (pub : List Fp) :
    (traceTraffic UnfoldA7.Node.interactions (nodeA7Trace vs T_NODE (selN vs S)) T_NODE pub).sends B_SIZE =
      [[3, nodeA7Total vs S]] := by
  have hH := node_height vs hok
  have hrow : ∀ q, q < (nodeTraceAligned vs).height T_NODE →
      (rowTraffic UnfoldA7.Node.interactions (nodeA7Trace vs T_NODE (selN vs S)) T_NODE q pub B_SIZE true).map
        (List.map Fp.toNat) = if q = R vs then [[3, nodeA7Total vs S]] else [] := by
    intro q hq
    obtain ⟨-, -, cS, -, cA⟩ := node_cells vs S q hq
    have o1 : Fp.ofNat 1 = (1 : Fp) := by decide
    have o0 : Fp.ofNat 0 = (0 : Fp) := by decide
    have z : ((0 : Fp) = 1) = False := by decide
    have h3 : (3 : Fp).toNat = 3 := rfl
    by_cases hqR : q = R vs
    · subst hqR
      have : NodeGen3.cell vs ((nodeTraceAligned vs).height T_NODE) (R vs) 3 = 1 := by rw [cell_sum]; rfl
      simp [rowTraffic, UnfoldA7.Node.interactions, Dsl.recv, Dsl.send, B_RPL, B_SIZE, Interaction.multNat,
        Interaction.multNat.go, Interaction.msgVal, cS, cA, this, o1, node_ra vs hok S, Fp.toNat_ofNat,
        Nat.mod_eq_of_lt (node_total_lt vs hok S)]
      exact h3
    · have : NodeGen3.cell vs ((nodeTraceAligned vs).height T_NODE) q 3 = 0 := by
        rcases Nat.lt_or_gt_of_ne hqR with h | h
        · rw [cell_node h, Rc.c3]
        · rw [cell_pad h]; rfl
      simp [rowTraffic, UnfoldA7.Node.interactions, Dsl.recv, Dsl.send, B_RPL, B_SIZE, Interaction.multNat,
        Interaction.multNat.go, cS, this, o0, z, hqR]
  simp only [traceTraffic]
  rw [show (nodeA7Trace vs T_NODE (selN vs S)).height T_NODE = (nodeTraceAligned vs).height T_NODE from rfl,
    ZkFormal.Near.Render.flatMap_congr' (fun q hq => hrow q (List.mem_range.1 hq))]
  rw [ZkFormal.Near.Render.range_split (show R vs + 1 ≤ (nodeTraceAligned vs).height T_NODE from hH),
    List.range_succ, List.flatMap_append, List.flatMap_append,
    ZkFormal.Near.Render.flatMap_nil' (l := List.range (R vs)) (fun q hq => by
      have := List.mem_range.1 hq; simp; omega),
    ZkFormal.Near.Render.flatMap_nil' (l := List.map _ _) (fun q hq => by
      obtain ⟨q', _, rfl⟩ := List.mem_map.1 hq; simp; omega)]
  simp

/-- No `RPL` sends. -/
theorem node_rpl_sends (vs : List NodeS3) (sel : Nat → Bool) (pub : List Fp) :
    (traceTraffic UnfoldA7.Node.interactions (nodeA7Trace vs T_NODE sel) T_NODE pub).sends B_RPL = [] := by
  simp only [traceTraffic]
  apply ZkFormal.Near.Render.flatMap_nil'
  intro q _
  simp [rowTraffic, UnfoldA7.Node.interactions, Dsl.recv, Dsl.send, B_RPL, B_SIZE]

/-- No `SIZE` receives. -/
theorem node_size_recvs (vs : List NodeS3) (sel : Nat → Bool) (pub : List Fp) :
    (traceTraffic UnfoldA7.Node.interactions (nodeA7Trace vs T_NODE sel) T_NODE pub).recvs B_SIZE = [] := by
  simp only [traceTraffic]
  apply ZkFormal.Near.Render.flatMap_nil'
  intro q _
  simp [rowTraffic, UnfoldA7.Node.interactions, Dsl.recv, Dsl.send, B_RPL, B_SIZE]

end Node

end ZkFormal.NearV3.Assembly.TrieA7
