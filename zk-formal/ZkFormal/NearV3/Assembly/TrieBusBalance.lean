import ZkFormal.NearV3.Assembly.RenderV3Trie
import ZkFormal.NearV3.Assembly.UniqNative
import ZkFormal.Chacha.Bus

/-!
# ZkFormal.NearV3.Assembly.TrieBusBalance — per-bus reduction of `RenderBundleV3.Balanced`

`R.Balanced` (`RenderV3Bundle.lean`) quantifies over all 77 buses and sums all 25 tables.
`R.BalancedAt b` is its bus-`b` instance; `balanced_iff` splits it.  On a bus `b`, a table
whose interactions never use `b` on side `s` contributes `0` (`cnt_tf_off`, from the exact
traffic of its render), so the bus-`b` equation only involves the tables that touch `b`:
`sum_tables` restricts the 25-table sum to any table filter `p` covering those tables.

The trie-only buses (no non-trie table and no public segment touches them; `trieOnly_*` are
kernel checks on `nearAirV3`):

| bus | tables (s = send, r = receive) |
|---|---|
| `PARENT` (2) | node s/r, head s |
| `EDGE` (4) | node s/r, head s/r, walk s/r, ups s/r |
| `BMAP` (11) | node s/r, walk s/r, ups s/r |
| `DIGS` (17) | node s, head s, uniq r |
| `DUP` (19) | uniq s, node r, val r |
| `ENT` (20) | node s/r, val s/r |
| `VPARENT` (22) | node s, val r |
| `MEMD` (23) | ups s/r |
| `MIDROOT` (24) | head s, ups r |
| `UPB` (25) | node s/r, ups s/r |

`ROOT` (10) is head r, ups s plus public messages on both sides.  The shared buses `BYTES`,
`DIGEST`, `VSLOT`, `KEYNIB`, `FINAL`, `VBYTES`, `SIZE`, `S0F`/`SPOST`/`SPLEN` also involve
receipt/scheduler tables.

**Proved here:** `balancedAt_digs` — the `DIGS` equation of any bundle whose node, head and
uniq components carry the traffic of record lists satisfying `Link3.DigsBal` (the honest
lists do: `UniqNative.uniqOf_digsBal`).  The generic `balancedAt_of_trie` turns a
trie-tables-only record-level count equation into `R.BalancedAt b` for every trie-only bus.
-/

namespace ZkFormal.NearV3.Assembly

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.NearV3.Render

/-- A bus count vanishes on a side no interaction of the bus has. -/
theorem tableBusCount_off_side (is : List Interaction) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (b : Nat) (s : Bool) (m : List Fp) (h : ∀ i ∈ is, i.bus = b → i.send ≠ s) :
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
      by_cases hb : i.bus = b
      · simp [this hb]
      · simp [hb]

theorem nearTablesFull_length : nearTablesFull.length = 25 := rfl

theorem tables_eq_full (t : Nat) (ht : t < nearAirV3.tables.length) :
    nearAirV3.tables[t] = nearTablesFull[t]'(by rw [nearTablesFull_length]; exact ht) := rfl

/-- `p` covers every table that uses bus `b` on side `s` (a kernel check for concrete `p`). -/
def Covers (b : Nat) (s : Bool) (p : Nat → Bool) : Bool :=
  (List.range 25).all fun t => p t ||
    ((nearTablesFull.getD t default).interactions.all fun i => !(i.bus == b && i.send == s))

theorem sum_range_filter (g : Nat → Nat) (p : Nat → Bool) :
    ∀ n, (∀ t, t < n → p t = false → g t = 0) →
      ((List.range n).map g).sum = (((List.range n).filter p).map g).sum
  | 0, _ => rfl
  | n + 1, hz => by
    rw [List.range_succ, List.map_append, List.filter_append, List.map_append, List.sum_append,
      List.sum_append, sum_range_filter g p n (fun t ht => hz t (by omega))]
    by_cases hp : p n = true
    · simp [hp]
    · have hpf : p n = false := by simpa using hp
      simp [List.filter, hpf, hz n (by omega) hpf]

namespace RenderBundleV3

variable {pub : List Fp} (R : RenderBundleV3 pub)

/-- The bus-`b` instance of `Balanced`. -/
def BalancedAt (b : Nat) : Prop :=
  ∀ m,
    (nearTablesFull.mapIdx fun (t : Nat) (_ : ZkFormal.Air.Table) => cnt (sel true (R.tf t) b) m).sum
        + pubCount nearAirV3 pub b true m =
      (nearTablesFull.mapIdx fun (t : Nat) (_ : ZkFormal.Air.Table) => cnt (sel false (R.tf t) b) m).sum
        + pubCount nearAirV3 pub b false m

theorem balanced_iff : R.Balanced ↔ ∀ b, R.BalancedAt b :=
  ⟨fun h b m => h b m, fun h b m => h b m⟩

/-- The count of a component's traffic is its table's bus count. -/
theorem cnt_tf (t : Nat) (ht : t < nearAirV3.tables.length) (s : Bool) (b : Nat) (m : List Fp) :
    cnt (sel s (R.tf t) b) m =
      tableBusCount nearAirV3.tables[t].interactions (R ⟨t, ht⟩).tr t pub b s m := by
  have htf : R.tf t = (R ⟨t, ht⟩).tf := by simp only [tf, ht, ↓reduceDIte]
  rw [htf]
  cases s
  · exact ((R ⟨t, ht⟩).traffic b m).2.symm
  · exact ((R ⟨t, ht⟩).traffic b m).1.symm

theorem cnt_tf_off (t : Nat) (ht : t < nearAirV3.tables.length) (s : Bool) (b : Nat) (m : List Fp)
    (h : ∀ i ∈ nearAirV3.tables[t].interactions, i.bus = b → i.send ≠ s) :
    cnt (sel s (R.tf t) b) m = 0 := by
  rw [R.cnt_tf t ht]
  exact tableBusCount_off_side _ _ _ _ _ _ _ h

theorem mapIdx_sum (s : Bool) (b : Nat) (m : List Fp) :
    (nearTablesFull.mapIdx fun (t : Nat) (_ : ZkFormal.Air.Table) => cnt (sel s (R.tf t) b) m).sum =
      ((List.range 25).map fun t => cnt (sel s (R.tf t) b) m).sum := by
  apply congrArg List.sum
  apply List.ext_getElem
  · rw [List.length_mapIdx, List.length_map, List.length_range, nearTablesFull_length]
  · intro i h1 h2
    simp only [List.getElem_mapIdx, List.getElem_map, List.getElem_range]

/-- **Restriction of a bus sum to the tables using the bus.** -/
theorem sum_tables (s : Bool) (b : Nat) (m : List Fp) (p : Nat → Bool) (hc : Covers b s p = true) :
    (nearTablesFull.mapIdx fun (t : Nat) (_ : ZkFormal.Air.Table) => cnt (sel s (R.tf t) b) m).sum =
      (((List.range 25).filter p).map fun t => cnt (sel s (R.tf t) b) m).sum := by
  rw [R.mapIdx_sum]
  apply sum_range_filter
  intro t ht hp
  have hc' := List.all_eq_true.mp hc t (List.mem_range.mpr ht)
  rw [hp, Bool.false_or] at hc'
  apply R.cnt_tf_off t (by rw [nearAirV3_tables_length]; exact ht)
  intro i hi hb hs
  have hi' : i ∈ (nearTablesFull.getD t default).interactions := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [nearTablesFull_length]; exact ht),
      Option.getD_some, ← tables_eq_full]
    exact hi
  have := List.all_eq_true.mp hc' i hi'
  simp [hb, hs] at this

end RenderBundleV3

/-! ## Kernel checks: which tables use the trie buses -/

/-- The DIGS senders are node (2) and head (3); the receiver is uniq (6). -/
theorem covers_digs_send : Covers B_DIGS true (fun t => t == 2 || t == 3) = true := by decide +kernel
theorem covers_digs_recv : Covers B_DIGS false (fun t => t == 6) = true := by decide +kernel

theorem pub_off (b : Nat) (s : Bool) (h : (nearAirV3.pubSegs.all fun g => !(g.bus == b && g.send == s)) = true)
    (pub m : List Fp) : pubCount nearAirV3 pub b s m = 0 := by
  apply ZkFormal.Chacha.pubCount_zero
  intro seg hseg hb hs
  have := List.all_eq_true.mp h seg hseg
  simp [hb, hs] at this

theorem pub_digs (s : Bool) (pub m : List Fp) : pubCount nearAirV3 pub B_DIGS s m = 0 :=
  pub_off _ _ (by cases s <;> decide +kernel) pub m

namespace RenderBundleV3

variable {pub : List Fp} (R : RenderBundleV3 pub)

/-- **`DIGS` balance of a bundle** from the record-level `DigsBal` of its node, head and uniq
components. -/
theorem balancedAt_digs (vs : List NodeS3) (hs : List HeadE) (L : List UEnt)
    (hn : ExtOf (R ⟨T_NODE, by decide⟩).tf (nodeTraffic3 vs)) (hh : (R ⟨T_HEAD, by decide⟩).tf = headTraffic hs)
    (hu : (R ⟨T_UNIQ, by decide⟩).tf = uniqTraffic (uniqEntries L))
    (hbal : Link3.DigsBal vs hs (uniqEntries L)) : R.BalancedAt B_DIGS := by
  intro m
  rw [R.sum_tables true _ m _ covers_digs_send, R.sum_tables false _ m _ covers_digs_recv,
    pub_digs, pub_digs]
  have e2 := R.tf_ext 2 (by decide) hn B_DIGS (by decide) (by decide) (by decide)
  have e3 : R.tf 3 = headTraffic hs := by rw [← hh]; rfl
  have e6 : R.tf 6 = uniqTraffic (uniqEntries L) := by rw [← hu]; rfl
  have hf2 : (List.range 25).filter (fun t => t == 2 || t == 3) = [2, 3] := by decide
  have hf6 : (List.range 25).filter (fun t => t == 6) = [6] := by decide
  rw [hf2, hf6]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, e2.1, e2.2, e3, e6, sel,
    ite_true, Bool.false_eq_true, ite_false]
  have hp := (hbal.count_eq m)
  simp only [List.map_append, List.count_append] at hp
  simp only [cnt, nodeTraffic3, headTraffic, uniqTraffic]
  omega

end RenderBundleV3

end ZkFormal.NearV3.Assembly
