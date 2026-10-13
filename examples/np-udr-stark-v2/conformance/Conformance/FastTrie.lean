import ZkFormal.NearV3.Render.UnfoldA7Aligned

/-!
# Conformance.FastTrie — executable twins of the trie-side renders

The honest renders of `nodeV3`, `valV3`, `upsV3` and their A7 extensions recompute global data
per cell: `NodeGen3.cell` / `ValGen.cell` / `UpsGen.cell` rebuild the whole record list (and
`UpsGen.uU` the `UPB` use count, `ValGen.szAt` a prefix sum) on every cell, and the A7 columns
`ra` / `rb` / `s` are `prefixF` running sums recomputed per row.  That is quadratic (or worse)
in the table height, too slow for fixture-size inputs.

Each twin here hoists the global data out of the cell function (computed once, as an `Array`)
and is **equal** to the render it replaces (`*_eq`, no hypotheses), so a dump of the twin is a
dump of the definition used in `TrieSide.trie_side_exact`:

* `nodeTraceFast vs = nodeTraceAligned vs`, `valTraceFast es = valTraceAligned es`,
  `upsTraceFast insts = upsTraceAligned insts`, `walkTraceFast ws = walkTraceAligned ws`;
* `nodeA7Fast vs t sel = nodeA7Trace vs t sel`, `valA7Fast es t sel = valA7Trace es t sel`,
  `upsA7Fast insts t = upsA7Trace insts t` (running sums from `prefixTab`, `prefixGet_tab`).
-/

namespace Conformance.FastTrie

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Render ZkFormal.NearV3
  ZkFormal.NearV3.Render ZkFormal.NearV3.UnfoldA7 ZkFormal.Size

/-! ## Running sums -/

/-- `a` extended by `k` running-sum entries, from row `r` with accumulator `acc`. -/
def prefixLoop (g : Nat → Fp) : Nat → Nat → Fp → Array Fp → Array Fp
  | 0, _, _, a => a
  | k + 1, r, acc, a => prefixLoop g k (r + 1) (acc + g r) (a.push acc)

/-- `[prefixF g 0, …, prefixF g (n-1)]`. -/
def prefixTab (g : Nat → Fp) (n : Nat) : Array Fp := prefixLoop g n 0 0 #[]

/-- `prefixF g r`, read from a table when `r` is in range. -/
def prefixGet (a : Array Fp) (g : Nat → Fp) (r : Nat) : Fp :=
  if h : r < a.size then a[r] else prefixF g r

theorem prefixLoop_spec (g : Nat → Fp) :
    ∀ (k r : Nat) (acc : Fp) (a : Array Fp), a.size = r → acc = prefixF g r →
      (∀ j (h : j < a.size), a[j] = prefixF g j) →
      ∀ j (h : j < (prefixLoop g k r acc a).size), (prefixLoop g k r acc a)[j] = prefixF g j
  | 0, _, _, _, _, _, ha => ha
  | k + 1, r, acc, a, hs, hacc, ha => by
    apply prefixLoop_spec g k (r + 1) (acc + g r) (a.push acc) (by simp [hs]) (by simp [prefixF, hacc])
    intro j hj
    rw [Array.getElem_push]
    split
    · exact ha j _
    · have : j = r := by simp at hj; omega
      subst this; exact hacc

theorem prefixGet_tab (g : Nat → Fp) (n r : Nat) : prefixGet (prefixTab g n) g r = prefixF g r := by
  unfold prefixGet
  split
  · exact prefixLoop_spec g n 0 0 #[] rfl rfl (fun j h => by simp at h) r _
  · rfl

/-! ## `nodeV3` -/

/-- `nodeTraceAligned` with the record list, its length and the total hoisted. -/
def nodeTraceFast (vs : List NodeS3) : Trace Fp :=
  let log := padLog22 (logOf ((vs.map fun s => (s.v.ser false).length).sum + 1))
  let rs := (NodeGen3.recsOf vs).toArray
  let tot := NodeGen3.total vs
  rowsTrace log (mkTab (2 ^ log) NodeV3.width (fun q col =>
    if q < rs.size then NodeGen3.rowCell vs (rs.getD q default) col
    else if q = rs.size then NodeGen3.sumCell tot col
    else NodeGen3.padCell tot col))

theorem nodeTraceFast_eq (vs : List NodeS3) : nodeTraceFast vs = nodeTraceAligned vs := by
  unfold nodeTraceFast nodeTraceAligned
  dsimp only
  congr 1; congr 1
  funext q col
  simp only [NodeGen3.cell, NodeGen3.R, List.size_toArray, Array.getD_eq_getD_getElem?,
    List.getElem?_toArray, List.getD_eq_getElem?_getD]
  split
  · rfl
  · split <;> simp_all

/-! ## `valV3` -/

/-- `szAt` for every `q ≤ |recs|`: `szTab[q] = Σ_{i<q} gw recs[i]`. -/
def szLoop (w : List Nat) (acc : Nat) (a : Array Nat) : Array Nat :=
  match w with
  | [] => a.push acc
  | x :: xs => szLoop xs (acc + x) (a.push acc)

theorem szLoop_spec : ∀ (w : List Nat) (acc : Nat) (a : Array Nat) (j : Nat) (h : j < (szLoop w acc a).size),
    (szLoop w acc a)[j] = if hj : j < a.size then a[j] else acc + (w.take (j - a.size)).sum
  | [], acc, a, j, h => by
    simp only [szLoop, Array.getElem_push] at h ⊢
    split <;> simp_all <;> omega
  | x :: xs, acc, a, j, h => by
    simp only [szLoop] at h ⊢
    rw [szLoop_spec xs (acc + x) (a.push acc) j h]
    simp only [Array.size_push, Array.getElem_push]
    by_cases h1 : j < a.size
    · simp [h1, show j < a.size + 1 by omega]
    · by_cases h2 : j = a.size
      · subst h2; simp
      · have h3 : ¬ j < a.size + 1 := by omega
        simp only [h1, h3, dite_false]
        rw [show j - a.size = (j - (a.size + 1)) + 1 by omega, List.take_succ_cons, List.sum_cons]
        omega

theorem szLoop_size : ∀ (w : List Nat) (acc : Nat) (a : Array Nat), (szLoop w acc a).size = a.size + w.length + 1
  | [], _, _ => by simp [szLoop]
  | _ :: xs, _, _ => by simp [szLoop, szLoop_size xs]; omega

/-- `szAt es q`, from the table for `q ≤ |recs|` (beyond: the total). -/
def szGet (sz : Array Nat) (q : Nat) : Nat := if h : q < sz.size then sz[q] else sz.back?.getD 0

theorem szGet_eq (es : List ValE) (q : Nat) :
    szGet (szLoop ((ValGen.recs es).map (ValGen.gw es)) 0 #[]) q = ValGen.szAt es q := by
  unfold szGet ValGen.szAt
  split
  · rename_i h
    rw [szLoop_spec _ 0 #[] q h]
    simp [List.map_take]
  · rename_i h
    rw [szLoop_size] at h
    simp only [List.size_toArray, List.length_nil, List.length_map, Nat.zero_add] at h
    rw [Array.back?, szLoop_size]
    simp only [List.size_toArray, List.length_nil, Nat.zero_add, List.length_map, Nat.add_sub_cancel]
    have hl : (ValGen.recs es).length < (szLoop ((ValGen.recs es).map (ValGen.gw es)) 0 #[]).size := by
      rw [szLoop_size]; simp
    rw [Array.getElem?_eq_getElem hl, Option.getD_some, szLoop_spec _ 0 #[] _ hl]
    rw [List.take_of_length_le (by simp)]
    simp [List.take_of_length_le (show (ValGen.recs es).length ≤ q by omega)]

/-- `valTraceAligned` with the record list and the `sz` prefix sums hoisted. -/
def valTraceFast (es : List ValE) : Trace Fp :=
  let log := padLog22 (logOf (ValGen.R es + 1))
  let rs := (ValGen.recs es).toArray
  let R := ValGen.R es
  let sz := szLoop ((ValGen.recs es).map (ValGen.gw es)) 0 #[]
  rowsTrace log (mkTab (2 ^ log) ValV3.width (fun q col =>
    if col = 11 then szGet sz q
    else if q < R then ValGen.recCell es (rs.getD q default) col
    else if q = R ∧ col = 12 then 1 else 0))

theorem valTraceFast_eq (es : List ValE) : valTraceFast es = valTraceAligned es := by
  unfold valTraceFast valTraceAligned valRowsAt
  dsimp only
  congr 1; congr 1
  funext q col
  simp only [ValGen.cell, szGet_eq, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
    List.getD_eq_getElem?_getD]

/-! ## `upsV3` -/

open UpsGen in
/-- `UpsGen.rowCell` with the `UPB` use count `u` given. -/
def rowCellU (insts : List UpsInst) (u : Nat) (r : Nat × RK) (col : Nat) : Int :=
  let I := inst insts r.1
  if isSeg col then segCell I col
  else match r.2 with
    | .w t => wCell I t col
    | .v p => vCell I p col
    | .q k p => qCell I k p u col

open UpsGen in
theorem rowCell_eq (insts : List UpsInst) (q : Nat) (r : Nat × RK) (col : Nat) :
    rowCell insts q r col = rowCellU insts (uU insts q) r col := by
  unfold rowCell rowCellU; rfl

open UpsGen in
/-- `uU insts q` for every row, from the key list (computed once). -/
def upsU (insts : List UpsInst) : Array Nat :=
  let ks := ((recs insts).map (rkey insts)).toArray
  (Array.range ks.size).map fun q => ((ks.toList.take q).filter (· == ks.getD q none)).length

open UpsGen in
theorem upsU_get (insts : List UpsInst) (q : Nat) (hq : q < (recs insts).length) :
    (upsU insts).getD q 0 = uU insts q := by
  simp only [upsU, Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range,
    List.size_toArray, List.length_map, hq, ite_true, Option.map_some, Option.getD_some]
  unfold uU
  have hk : ((recs insts).map (rkey insts)).toArray[q]?.getD none = rkey insts ((recs insts).getD q default) := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hq]
  rw [hk, ← List.map_take, List.filter_map, List.length_map]
  rfl

/-- `upsTraceAligned` with the row list and the use counts hoisted. -/
def upsTraceFast (insts : List UpsInst) : Trace Fp :=
  let rs := (UpsGen.recs insts).toArray
  let us := upsU insts
  let log := padLog22 (logOf (rs.size + 1))
  rowsTrace log (mkTab (2 ^ log) 200 (fun r c =>
    ((if r < rs.size then rowCellU insts (us.getD r 0) (rs.getD r default) c else 0 : Int) : Fp).toNat))

theorem upsTraceFast_eq (insts : List UpsInst) : upsTraceFast insts = upsTraceAligned insts := by
  unfold upsTraceFast upsTraceAligned
  dsimp only
  simp only [List.size_toArray]
  have hR : (UpsGen.recs insts).length = UpsGen.R insts := rfl
  rw [hR]
  congr 1; congr 1
  funext r c
  unfold UpsGen.cell
  by_cases h : r < UpsGen.R insts
  · simp only [h, ite_true, rowCell_eq, upsU_get insts r h, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
      List.getD_eq_getElem?_getD]
  · simp only [h, ite_false]


/-! ## `walkV3` -/

/-- `walkTraceAligned` with the row records and their count hoisted. -/
def walkTraceFast (ws : List WalkR) : Trace Fp :=
  let rs := (WalkGen.recs ws).toArray
  let n := ZkFormal.NearV3.Render.rows ws
  let log := padLog22 (logOf n)
  rowsTrace log (mkTab (2 ^ log) WalkV3.width (fun q col =>
    if q < n then WalkGen.rowCell (rs.getD q default) col else 0))

theorem walkTraceFast_eq (ws : List WalkR) : walkTraceFast ws = walkTraceAligned ws := by
  unfold walkTraceFast walkTraceAligned
  dsimp only
  congr 1; congr 1
  funext q col
  simp only [WalkGen.cell, Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getD_eq_getElem?_getD]

/-! ## A7 extensions -/

/-- `nodeA7Trace` over the fast base render, `ra` from a running-sum table. -/
def nodeA7Fast (vs : List NodeS3) (t : Nat) (sel : Nat → Bool) : Trace Fp :=
  let tr := nodeTraceFast vs
  let pa := prefixTab (nodeInc tr t sel) (tr.height t)
  Trace.withCols tr t 186 (fun r col =>
    if col = Node.rpl then nodeRpl tr t sel r
    else if col = Node.ra then prefixGet pa (nodeInc tr t sel) r else 0)

theorem nodeA7Fast_eq (vs : List NodeS3) (t : Nat) (sel : Nat → Bool) :
    nodeA7Fast vs t sel = nodeA7Trace vs t sel := by
  unfold nodeA7Fast nodeA7Trace
  simp only [prefixGet_tab, nodeTraceFast_eq]
  rfl

def valA7Fast (es : List ValE) (t : Nat) (sel : Nat → Bool) : Trace Fp :=
  let tr := valTraceFast es
  let pa := prefixTab (valInc tr t sel) (tr.height t)
  Trace.withCols tr t 15 (fun r col =>
    if col = Val.rplv then valRpl tr t sel r
    else if col = Val.rb then prefixGet pa (valInc tr t sel) r else 0)

theorem valA7Fast_eq (es : List ValE) (t : Nat) (sel : Nat → Bool) :
    valA7Fast es t sel = valA7Trace es t sel := by
  unfold valA7Fast valA7Trace
  simp only [prefixGet_tab, valTraceFast_eq]
  rfl

def upsA7Fast (insts : List UpsInst) (t : Nat) : Trace Fp :=
  let tr := upsTraceFast insts
  let g := fun q => tr.cell t q ZkFormal.NearV3.UpsV3.vb + tr.cell t q ZkFormal.NearV3.UpsV3.qb
  let pa := prefixTab g (tr.height t)
  Trace.withCols tr t 200 (fun r col =>
    if col = Ups.s then prefixGet pa g r
    else if col = Ups.nD then upsND tr t r else 0)

theorem upsA7Fast_eq (insts : List UpsInst) (t : Nat) : upsA7Fast insts t = upsA7Trace insts t := by
  unfold upsA7Fast upsA7Trace
  simp only [prefixGet_tab, upsTraceFast_eq]
  rfl

end Conformance.FastTrie
