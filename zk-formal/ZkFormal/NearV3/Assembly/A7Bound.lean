import ZkFormal.NearV3.Assembly.LinkV3
import ZkFormal.Chacha.Bus

/-!
# ZkFormal.NearV3.Assembly.A7Bound — the A7 facts of the records from the bus balance

From `HoldsP nearAirV3` and the records' exact traffic (`V3RecordsTraffic`, incl. the A7 views):

* **`a7_rpl_perm`**: the ups `RPL` sends are a permutation of the replaced node records
  `((range |nodes|).filter rplN).map [·]` (as field messages); `RPL` is used by `nodeA7` (receives)
  and `upsA7` (sends) only, no public segment (kernel checks);
* **`a7_rplv_perm`**: the same for `RPLV` and the replaced value records `[e.vid]`;
* **`a7_total_le`**: `nodeA7Sum + valA7Sum + Σ a7S ≤ B0` — the `SIZE` messages with tags `3, 4, 5`
  are sent by `nodeA7`/`valA7`/`upsA7` only (every other `SIZE` send has a constant tag `0, 1, 2`)
  and received by `sizeA7` only, which checks `B0 − Σ y_t` in 24 bits.
-/

namespace ZkFormal.NearV3.Assembly

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.NearV3

namespace A7Bound

/-! ## Bus sums restricted to the tables using a bus -/

/-- `p` covers every table of `nearAirV3` that uses bus `b` on side `s`. -/
def CoversS (b : Nat) (s : Bool) (p : Nat → Bool) : Bool :=
  (List.range 25).all fun t => p t ||
    ((nearTablesFull.getD t default).interactions.all fun i => !(i.bus == b && i.send == s))

theorem tbc_off (is : List Interaction) (tr : Trace Fp) (t : Nat) (pub : List Fp)
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

theorem go_sum (tr : Trace Fp) (pub : List Fp) (b : Nat) (s : Bool) (m : List Fp) :
    ∀ (Ts : List ZkFormal.Air.Table) (t0 : Nat), busCount.go tr pub b s m Ts t0 =
      ((List.range Ts.length).map fun i => tableBusCount (Ts.getD i (default : ZkFormal.Air.Table)).interactions tr (t0 + i) pub b s m).sum
  | [], _ => rfl
  | T :: Ts, t0 => by
    rw [busCount.go, go_sum tr pub b s m Ts (t0 + 1), List.length_cons, List.range_succ_eq_map, List.map_cons,
      List.sum_cons, List.map_map]
    congr 1
    congr 1
    apply List.map_congr_left; intro i _
    simp only [Function.comp_apply, List.getD_cons_succ]
    congr 1; omega

theorem busCount_range (tr : Trace Fp) (pub : List Fp) (b : Nat) (s : Bool) (m : List Fp) :
    busCount nearAirV3.toAir tr pub b s m =
      ((List.range 25).map fun t => tableBusCount (nearTablesFull.getD t default).interactions tr t pub b s m).sum := by
  unfold busCount
  rw [go_sum]
  rfl

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

theorem busCount_cover (tr : Trace Fp) (pub : List Fp) (b : Nat) (s : Bool) (m : List Fp) (p : Nat → Bool)
    (hc : CoversS b s p = true) :
    busCount nearAirV3.toAir tr pub b s m =
      (((List.range 25).filter p).map fun t => tableBusCount (nearTablesFull.getD t default).interactions tr t pub b s m).sum := by
  rw [busCount_range]
  apply sum_range_filter
  intro t ht hp
  have hc' := List.all_eq_true.mp hc t (List.mem_range.mpr ht)
  rw [hp, Bool.false_or] at hc'
  apply tbc_off
  intro i hi hb hs
  have := List.all_eq_true.mp hc' i hi
  simp [hb, hs] at this

theorem pub_off (b : Nat) (s : Bool) (h : (nearAirV3.pubSegs.all fun g => !(g.bus == b && g.send == s)) = true)
    (pub m : List Fp) : pubCount nearAirV3 pub b s m = 0 := by
  apply ZkFormal.Chacha.pubCount_zero
  intro seg hseg hb hs
  have := List.all_eq_true.mp h seg hseg
  simp [hb, hs] at this

theorem tbc_append (is js : List Interaction) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (b : Nat) (s : Bool) (m : List Fp) :
    tableBusCount (is ++ js) tr t pub b s m = tableBusCount is tr t pub b s m + tableBusCount js tr t pub b s m :=
  tableBusCount_append is js tr t pub b s m

/-! ## `RPL` / `RPLV` -/

theorem covers_rpl_send : CoversS UnfoldA7.B_RPL true (fun t => t == 7) = true := by decide +kernel
theorem covers_rpl_recv : CoversS UnfoldA7.B_RPL false (fun t => t == 2) = true := by decide +kernel
theorem covers_rplv_send : CoversS UnfoldA7.B_RPLV true (fun t => t == 7) = true := by decide +kernel
theorem covers_rplv_recv : CoversS UnfoldA7.B_RPLV false (fun t => t == 4) = true := by decide +kernel

theorem ups_base_rpl : ∀ i ∈ UpsV3.interactions, i.bus = UnfoldA7.B_RPL ∨ i.bus = UnfoldA7.B_RPLV → False := by
  decide +kernel
theorem node_base_rpl : ∀ i ∈ NodeV3.interactions, i.bus = UnfoldA7.B_RPL → False := by decide +kernel
theorem val_base_rplv : ∀ i ∈ ValV3.interactions, i.bus = UnfoldA7.B_RPLV → False := by decide +kernel
theorem node_a7_rpl_send : ∀ i ∈ UnfoldA7.Node.interactions, i.bus = UnfoldA7.B_RPL → i.send ≠ true := by
  decide +kernel
theorem val_a7_rplv_send : ∀ i ∈ UnfoldA7.Val.interactions, i.bus = UnfoldA7.B_RPLV → i.send ≠ true := by
  decide +kernel
theorem ups_a7_rpl_recv : ∀ i ∈ UnfoldA7.Ups.interactions, i.bus = UnfoldA7.B_RPL ∨ i.bus = UnfoldA7.B_RPLV →
    i.send ≠ false := by decide +kernel

section
variable {pub : List Fp} {tr : Trace Fp} {r : V3Records}

theorem filter7 : (List.range 25).filter (fun t => t == 7) = [7] := by decide
theorem filter2 : (List.range 25).filter (fun t => t == 2) = [2] := by decide
theorem filter4 : (List.range 25).filter (fun t => t == 4) = [4] := by decide

/-- **`RPL` balance in record form.** -/
theorem a7_rpl_perm (hH : HoldsP nearAirV3 pub tr) (T : V3RecordsTraffic pub tr r) :
    ((r.ups.flatMap UpsSeg.a7Rpl).map Msg.toFp).Perm
      ((((List.range r.nodes.length).filter r.rplN).map fun n => ([n] : Msg)).map Msg.toFp) := by
  rw [List.perm_iff_count]
  intro m
  have hb := hH.balance UnfoldA7.B_RPL m
  rw [pub_off _ _ (by decide +kernel) pub m, pub_off _ _ (by decide +kernel) pub m,
    busCount_cover tr pub _ _ m _ covers_rpl_send, busCount_cover tr pub _ _ m _ covers_rpl_recv,
    filter7, filter2] at hb
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at hb
  rw [show (nearTablesFull.getD 7 default).interactions = UpsV3.interactions ++ UnfoldA7.Ups.interactions from rfl,
    show (nearTablesFull.getD 2 default).interactions = NodeV3.interactions ++ UnfoldA7.Node.interactions from rfl,
    tbc_append, tbc_append,
    tbc_off UpsV3.interactions tr 7 pub _ true m (fun i hi hb' => absurd (Or.inl hb') (ups_base_rpl i hi)),
    tbc_off NodeV3.interactions tr 2 pub _ false m (fun i hi hb' => absurd hb' (node_base_rpl i hi)),
    Nat.zero_add, Nat.zero_add] at hb
  have h1 := (T.a7ups UnfoldA7.B_RPL m).1
  have h2 := (T.a7nodes UnfoldA7.B_RPL m).2
  simp only [a7UpsTraffic, a7NodeTraffic, ite_true] at h1 h2
  rw [← h1, ← h2]
  exact hb

/-- **`RPLV` balance in record form.** -/
theorem a7_rplv_perm (hH : HoldsP nearAirV3 pub tr) (T : V3RecordsTraffic pub tr r) :
    ((r.ups.flatMap UpsSeg.a7Rplv).map Msg.toFp).Perm
      ((((List.range r.values.length).filter r.rplV).map fun t => ([(r.values.getD t default).vid] : Msg)).map Msg.toFp) := by
  rw [List.perm_iff_count]
  intro m
  have hb := hH.balance UnfoldA7.B_RPLV m
  rw [pub_off _ _ (by decide +kernel) pub m, pub_off _ _ (by decide +kernel) pub m,
    busCount_cover tr pub _ _ m _ covers_rplv_send, busCount_cover tr pub _ _ m _ covers_rplv_recv,
    filter7, filter4] at hb
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at hb
  rw [show (nearTablesFull.getD 7 default).interactions = UpsV3.interactions ++ UnfoldA7.Ups.interactions from rfl,
    show (nearTablesFull.getD 4 default).interactions = ValV3.interactions ++ UnfoldA7.Val.interactions from rfl,
    tbc_append, tbc_append,
    tbc_off UpsV3.interactions tr 7 pub _ true m (fun i hi hb' => absurd (Or.inr hb') (ups_base_rpl i hi)),
    tbc_off ValV3.interactions tr 4 pub _ false m (fun i hi hb' => absurd hb' (val_base_rplv i hi)),
    Nat.zero_add, Nat.zero_add] at hb
  have h1 := (T.a7ups UnfoldA7.B_RPLV m).1
  have h2 := (T.a7values UnfoldA7.B_RPLV m).2
  simp only [a7UpsTraffic, a7ValTraffic, ite_true, show UnfoldA7.B_RPLV ≠ UnfoldA7.B_RPL by decide,
    ite_false] at h1 h2
  rw [← h1, ← h2]
  exact hb

end

/-! ## `SIZE` tags `3, 4, 5` -/

theorem tbc_off_msg (is : List Interaction) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (b : Nat) (s : Bool) (m : List Fp) (h : ∀ i ∈ is, i.bus = b → i.send = s → ∀ r, i.msgVal tr t r pub ≠ m) :
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
      · by_cases hs : i.send = s
        · simp [this hb hs r]
        · simp [hs]
      · simp [hb]

/-- Every `(b, s)` interaction of `is` has a constant tag in `cs`. -/
def HeadIn (b : Nat) (s : Bool) (cs : List Nat) (is : List Interaction) : Bool :=
  is.all fun i => !(i.bus == b && i.send == s) ||
    match i.msg with
    | .const c :: _ => cs.contains c
    | _ => false

theorem tbc_head_off (is : List Interaction) (tr : Trace Fp) (t : Nat) (pub : List Fp) (b : Nat) (s : Bool)
    (cs : List Nat) (hcs : ∀ c ∈ cs, c < 3) (hh : HeadIn b s cs is = true) (τ : Nat) (hτ : 3 ≤ τ) (hτ' : τ < 6)
    (y : List Fp) : tableBusCount is tr t pub b s (((τ : Nat) : Fp) :: y) = 0 := by
  apply tbc_off_msg
  intro i hi hb hs r he
  have := List.all_eq_true.mp hh i hi
  simp only [hb, hs, beq_self_eq_true, Bool.and_self, Bool.not_true, Bool.false_or] at this
  unfold Interaction.msgVal at he
  split at this
  · rename_i c rest hm
    rw [hm] at he
    simp only [List.map_cons, List.cons.injEq] at he
    have hc := hcs c (by simpa using this)
    have e : (c : Fp) = ((τ : Nat) : Fp) := he.1
    have := ofNat_inj (a := c) (b := τ) (by unfold P; omega) (by unfold P; omega) e
    omega
  · simp at this

theorem covers_size_send : CoversS B_SIZE true (fun t => t == 2 || t == 4 || t == 7 || t == 20) = true := by
  decide +kernel
theorem covers_size_recv : CoversS B_SIZE false (fun t => t == 21) = true := by decide +kernel
theorem filter_send : (List.range 25).filter (fun t => t == 2 || t == 4 || t == 7 || t == 20) = [2, 4, 7, 20] := by
  decide
theorem filter21 : (List.range 25).filter (fun t => t == 21) = [21] := by decide

theorem node_base_head : HeadIn B_SIZE true [0] NodeV3.interactions = true := by decide +kernel
theorem val_base_head : HeadIn B_SIZE true [1] ValV3.interactions = true := by decide +kernel
theorem ups_base_size : ∀ i ∈ UpsV3.interactions, i.bus = B_SIZE → i.send ≠ true := by decide +kernel
theorem srcp_head : HeadIn B_SIZE true [2] (nearTablesFull.getD 20 default).interactions = true := by
  decide +kernel

section
variable {pub : List Fp} {tr : Trace Fp} {r : V3Records}

/-- The `SIZE` balance on a message with tag `3, 4, 5`, in record form. -/
theorem size_tag (hH : HoldsP nearAirV3 pub tr) (T : V3RecordsTraffic pub tr r) (τ : Nat) (hτ : 3 ≤ τ)
    (hτ' : τ < 6) (y : List Fp) :
    (([[3, nodeA7Sum r.nodes r.rplN], [4, valA7Sum r.values r.rplV], [5, (r.ups.map UpsSeg.a7S).sum]] : List Msg).map
        Msg.toFp).count (((τ : Nat) : Fp) :: y) =
      (([[3, r.a7.y0], [4, r.a7.y1], [5, r.a7.y2]] : List Msg).map Msg.toFp).count (((τ : Nat) : Fp) :: y) := by
  have hb := hH.balance B_SIZE (((τ : Nat) : Fp) :: y)
  rw [pub_off _ _ (by decide +kernel) pub _, pub_off _ _ (by decide +kernel) pub _,
    busCount_cover tr pub _ _ _ _ covers_size_send, busCount_cover tr pub _ _ _ _ covers_size_recv,
    filter_send, filter21] at hb
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at hb
  rw [show (nearTablesFull.getD 2 default).interactions = NodeV3.interactions ++ UnfoldA7.Node.interactions from rfl,
    show (nearTablesFull.getD 4 default).interactions = ValV3.interactions ++ UnfoldA7.Val.interactions from rfl,
    show (nearTablesFull.getD 7 default).interactions = UpsV3.interactions ++ UnfoldA7.Ups.interactions from rfl,
    show (nearTablesFull.getD 21 default).interactions = SizeV3.interactions ++ UnfoldA7.Size.interactions from rfl,
    tbc_append, tbc_append, tbc_append, tbc_append,
    tbc_head_off _ tr 2 pub _ _ [0] (by simp) node_base_head τ hτ hτ' y,
    tbc_head_off _ tr 4 pub _ _ [1] (by simp) val_base_head τ hτ hτ' y,
    tbc_off UpsV3.interactions tr 7 pub _ true _ ups_base_size,
    tbc_head_off _ tr 20 pub _ _ [2] (by simp) srcp_head τ hτ hτ' y] at hb
  have hN := (T.a7nodes B_SIZE (((τ : Nat) : Fp) :: y)).1
  have hV := (T.a7values B_SIZE (((τ : Nat) : Fp) :: y)).1
  have hU := (T.a7ups B_SIZE (((τ : Nat) : Fp) :: y)).1
  have hS := (T.size B_SIZE (((τ : Nat) : Fp) :: y)).2
  have hY := (T.a7size B_SIZE (((τ : Nat) : Fp) :: y)).2
  rw [show T_NODE = 2 from rfl] at hN
  rw [show T_VAL = 4 from rfl] at hV
  rw [show T_UPS = 7 from rfl] at hU
  rw [show T_SIZE = 21 from rfl] at hS hY
  rw [hN, hV, hU, hS, hY] at hb
  have h0 : ((((sizeTraffic r.size).recvs B_SIZE).map Msg.toFp).count (((τ : Nat) : Fp) :: y)) = 0 := by
    simp only [sizeTraffic, ite_true]
    apply List.count_eq_zero.2
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false, Msg.toFp]
    rintro (h | h | h) <;> simp only [List.cons.injEq] at h <;>
    · have := ofNat_inj (by unfold P; omega) (by unfold P; omega) h.1.symm
      omega
  rw [h0] at hb
  simp only [a7NodeTraffic, a7ValTraffic, a7UpsTraffic, a7SizeTraffic, ite_true,
    show B_SIZE ≠ UnfoldA7.B_RPL by decide, show B_SIZE ≠ UnfoldA7.B_RPLV by decide, ite_false] at hb
  simp only [List.map_cons, List.map_nil, List.count_cons, List.count_nil] at hb ⊢
  omega

end

/-! ## The A7 total of the records fits `B0` -/

theorem sum_map_le {α : Type} (l : List α) (f g : α → Nat) (h : ∀ x ∈ l, f x ≤ g x) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => exact Nat.le_refl _
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h a (by simp)) (ih (fun x hx => h x (by simp [hx])))

theorem sum_range_getD {α : Type} [Inhabited α] (g : α → Nat) :
    ∀ l : List α, ((List.range l.length).map fun n => g (l.getD n default)).sum = (l.map g).sum
  | [] => rfl
  | a :: l => by
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, List.sum_cons, List.map_cons,
      List.sum_cons]
    congr 1
    rw [← sum_range_getD g l]
    congr 1

theorem sum_map_mul2 {α : Type} (f : α → Nat) : ∀ l : List α, (l.map fun x => 2 * f x).sum = 2 * (l.map f).sum
  | [] => rfl
  | a :: l => by simp only [List.map_cons, List.sum_cons, sum_map_mul2 f l]; omega

theorem sum_map_two {α : Type} : ∀ l : List α, (l.map fun _ => 2).sum = 2 * l.length
  | [] => rfl
  | a :: l => by simp only [List.map_cons, List.sum_cons, sum_map_two l, List.length_cons]; omega

theorem weighted_le {α : Type} [Inhabited α] (l : List α) (S : Nat → Bool) (g : α → Nat) :
    ((List.range l.length).map fun n => (if S n then 1 else 2) * g (l.getD n default)).sum ≤ 2 * (l.map g).sum := by
  rw [← sum_range_getD g l, ← sum_map_mul2]
  apply sum_map_le; intro n _
  split <;> omega

theorem toFp_inj {a b : Nat} (ha : a < P) (hb : b < P) (h : Fp.ofNat a = Fp.ofNat b) : a = b :=
  ofNat_inj ha hb h

section
variable {pub : List Fp} {tr : Trace Fp} {r : V3Records}

theorem tag_eq (hH : HoldsP nearAirV3 pub tr) (T : V3RecordsTraffic pub tr r) (W : V3RecordsWf pub r)
    {τ N : Nat} (hτ : 3 ≤ τ) (hτ' : τ < 6) (hin : ([τ, N] : Msg) ∈
      ([[3, nodeA7Sum r.nodes r.rplN], [4, valA7Sum r.values r.rplV], [5, (r.ups.map UpsSeg.a7S).sum]] : List Msg)) :
    Msg.toFp ([τ, N] : Msg) ∈ (([[3, r.a7.y0], [4, r.a7.y1], [5, r.a7.y2]] : List Msg).map Msg.toFp) := by
  have := size_tag hH T τ hτ hτ' [Fp.ofNat N]
  have hpos : 0 < (([[3, nodeA7Sum r.nodes r.rplN], [4, valA7Sum r.values r.rplV],
      [5, (r.ups.map UpsSeg.a7S).sum]] : List Msg).map Msg.toFp).count (((τ : Nat) : Fp) :: [Fp.ofNat N]) :=
    List.count_pos_iff.2 (List.mem_map.2 ⟨_, hin, rfl⟩)
  rw [this] at hpos
  exact List.count_pos_iff.1 hpos

/-- **The A7 total of the records fits `B0`.** -/
theorem a7_total_le (hH : HoldsP nearAirV3 pub tr) (T : V3RecordsTraffic pub tr r) (W : V3RecordsWf pub r) :
    nodeA7Sum r.nodes r.rplN + valA7Sum r.values r.rplV + (r.ups.map UpsSeg.a7S).sum ≤ UnfoldA7.B0 := by
  -- bounds
  have hN : nodeA7Sum r.nodes r.rplN ≤ 2 ^ 23 := by
    have := weighted_le r.nodes r.rplN (fun s => (s.v.ser false).length)
    have := W.nodes.rows
    unfold nodeA7Sum; omega
  have hV : valA7Sum r.values r.rplV ≤ 2 ^ 23 := by
    have h1 := weighted_le r.values r.rplV ValE.len
    have h2 := W.values.rows
    have h3 : (r.values.map ValE.len).sum ≤ (r.values.map fun e => if e.vz then 1 else e.len).sum :=
      sum_map_le _ _ _ (fun e he => by
        have := (W.values.shape e he)
        cases hz : e.vz
        · simp
        · simp only [ite_true]; have := (this.1 hz).1; omega)
    unfold valA7Sum; omega
  have hU : (r.ups.map UpsSeg.a7S).sum ≤ 2 ^ 23 := by
    have h1 : (r.ups.map UpsSeg.a7S).sum ≤ (r.ups.map fun s => 2 * s.rows.length).sum :=
      sum_map_le _ _ _ (fun s hs => by
        unfold UpsSeg.a7S
        have : ((List.range s.rows.length).map fun i => s.row i UpsV3.vb + s.row i UpsV3.qb).sum ≤
            ((List.range s.rows.length).map fun _ => 2).sum :=
          sum_map_le _ _ _ (fun i hi => by
            have hi := List.mem_range.1 hi
            have ok := W.ups.rows s hs i hi
            have hC := (W.ups.canon s hs).1
            have hD : ∀ x, s.next i x < P := by
              intro x; unfold UpsSeg.next; split
              · exact hC _ _
              · exact (W.ups.canon s hs).2 x
            have b1 := UpsRows.rowBool ok (hC i) (x := UpsV3.vb) (by simp [UpsV3.rowBools])
            have b2 := UpsRows.rowBool ok (hC i) (x := UpsV3.qb) (by simp [UpsV3.rowBools])
            omega)
        rw [sum_map_two, List.length_range] at this; exact this)
    have h2 := W.ups.count
    have h3 : (r.ups.map fun s => 2 * s.rows.length).sum = 2 * (r.ups.map (·.rows.length)).sum := by
      rw [← sum_map_mul2]
    omega
  -- the tags
  have e3 := tag_eq hH T W (τ := 3) (N := nodeA7Sum r.nodes r.rplN) (by omega) (by omega) (by simp)
  have e4 := tag_eq hH T W (τ := 4) (N := valA7Sum r.values r.rplV) (by omega) (by omega) (by simp)
  have e5 := tag_eq hH T W (τ := 5) (N := (r.ups.map UpsSeg.a7S).sum) (by omega) (by omega) (by simp)
  have hP : 2 ^ 27 < P := by unfold P; omega
  obtain ⟨hy0, hy1, hy2⟩ := W.a7size.canon
  have pick : ∀ (τ N : Nat), 3 ≤ τ → τ < 6 → Msg.toFp ([τ, N] : Msg) ∈ (([[3, r.a7.y0], [4, r.a7.y1], [5, r.a7.y2]] : List Msg).map Msg.toFp) →
      N < P → (τ = 3 → N = r.a7.y0) ∧ (τ = 4 → N = r.a7.y1) ∧ (τ = 5 → N = r.a7.y2) := by
    intro τ N h1 h2 hm hNP
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false, Msg.toFp,
      List.cons.injEq, and_true] at hm
    have ne : ∀ a b : Nat, a < 6 → b < 6 → a ≠ b → Fp.ofNat a ≠ Fp.ofNat b := fun a b ha hb hab e =>
      hab (toFp_inj (by unfold P; omega) (by unfold P; omega) e)
    rcases hm with ⟨ht, hn⟩ | ⟨ht, hn⟩ | ⟨ht, hn⟩
    · have := toFp_inj (by unfold P; omega) (by unfold P; omega) ht
      have := toFp_inj hNP hy0 hn; omega
    · have := toFp_inj (by unfold P; omega) (by unfold P; omega) ht
      have := toFp_inj hNP hy1 hn; omega
    · have := toFp_inj (by unfold P; omega) (by unfold P; omega) ht
      have := toFp_inj hNP hy2 hn; omega
  have q0 := (pick 3 _ (by omega) (by omega) e3 (by omega)).1 rfl
  have q1 := (pick 4 _ (by omega) (by omega) e4 (by omega)).2.1 rfl
  have q2 := (pick 5 _ (by omega) (by omega) e5 (by omega)).2.2 rfl
  obtain ⟨b, hb, hs⟩ := W.a7size.slack
  rw [← q0, ← q1, ← q2, Nat.mod_eq_of_lt (by unfold UnfoldA7.B0 at *; omega)] at hs
  unfold UnfoldA7.B0 at hs ⊢
  omega

end

end A7Bound

end ZkFormal.NearV3.Assembly
