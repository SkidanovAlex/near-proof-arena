import ZkFormal.NearV3.Assembly.LinkTrie

/-!
# ZkFormal.NearV3.Assembly.LinkStore — `mainStoreBytes`: the main store is within the size budget

Steps 4–6 of the `mainStoreBytes` plan (`docs/logs/v3-link-2026-10.md`):

* `eid_unique` — two `uniq` entries never share an id.  `DIGS` counting by message head: the
  receives with head `E` are `32 · #{entries with eid E}`; the sends with head `NPRE c` are
  `32 ·` the `PARENT` sends with head `c` (one per kid slot / head root), which by `ParentBal`
  equal the `PARENT` receives with head `c` (`≤ 1`); the sends with head `VPRE i` are `32 ·` the
  `VPARENT` sends with head `i`, by `VParentBal` the value records with id `i` (`≤ 1`).
* `eq0_nondup` — the record of an `eq = 0` entry is not a duplicate (a duplicate receives
  `DUP (eid, ·)`, sent by an `eq = 1` entry with the same id).
* `store_sum_le` — every duplicate-free list of blobs of an instance's store sums to at most the
  non-duplicate record bytes `nodeStoreSum + valStoreSum` (`≤ 3,000,000`, `size_totals`).
-/

namespace ZkFormal.NearV3.Assembly

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near

namespace LinkStore

open ZkFormal.NearV3 ZkFormal.NearV3.Link3

/-! ## Counting messages by their first component -/

/-- Number of messages of `l` whose first component is `E`. -/
def hcN (E : Nat) (l : List Msg) : Nat := (l.map List.head?).count (some E)

/-- Every message of `l` starts with a canonical value. -/
def HeadsLt (l : List Msg) : Prop := ∀ m ∈ l, ∀ x, m.head? = some x → x < P

theorem hcN_append (E : Nat) (a b : List Msg) : hcN E (a ++ b) = hcN E a + hcN E b := by
  simp [hcN, List.count_append]

theorem hcN_flatMap {α : Type} (E : Nat) (l : List α) (f : α → List Msg) :
    hcN E (l.flatMap f) = (l.map fun x => hcN E (f x)).sum := by
  induction l with
  | nil => simp [hcN]
  | cons a l ih =>
    rw [List.flatMap_cons, hcN_append, ih]; simp

theorem hcN_nil (E : Nat) : hcN E [] = 0 := rfl

theorem hcN_cons (E : Nat) (m : Msg) (l : List Msg) :
    hcN E (m :: l) = (if m.head? = some E then 1 else 0) + hcN E l := by
  simp only [hcN, List.map_cons, List.count_cons, beq_iff_eq]; omega

theorem hcN_block (E a : Nat) (f : Nat → List Nat) :
    hcN E ((List.range 32).map fun i => a :: f i) = if a = E then 32 else 0 := by
  have : ((List.range 32).map fun i => a :: f i).map List.head? = List.replicate 32 (some a) := by
    rw [List.map_map]
    apply List.ext_getElem (by simp)
    intro i h1 h2; rw [List.getElem_replicate]; simp
  unfold hcN; rw [this, List.count_replicate]
  by_cases h : a = E <;> simp [h]

theorem count_ofNat {L : List (Option Nat)} (hL : ∀ o ∈ L, ∀ x, o = some x → x < P) {E : Nat}
    (hE : E < P) : (L.map (Option.map Fp.ofNat)).count (some (Fp.ofNat E)) = L.count (some E) := by
  induction L with
  | nil => rfl
  | cons o L ih =>
    simp only [List.map_cons, List.count_cons]
    rw [ih (fun o' h => hL o' (List.mem_cons_of_mem _ h))]
    congr 1
    cases o with
    | none => simp
    | some x =>
      have hx := hL _ List.mem_cons_self x rfl
      by_cases h : x = E
      · subst h; simp
      · have : Fp.ofNat x ≠ Fp.ofNat E := fun e => h (ofNat_eq hx hE e)
        simp [h, this]

theorem head_toFp (m : Msg) : (Msg.toFp m).head? = m.head?.map Fp.ofNat := by
  cases m <;> rfl

/-- **Counting through a balance**: a permutation of the `Fp` images preserves head counts. -/
theorem hcN_perm {A B : List Msg} (hp : (A.map Msg.toFp).Perm (B.map Msg.toFp)) (hA : HeadsLt A)
    (hB : HeadsLt B) {E : Nat} (hE : E < P) : hcN E A = hcN E B := by
  have h := (hp.map List.head?).count_eq (some (Fp.ofNat E))
  have e : ∀ X : List Msg, (X.map Msg.toFp).map List.head? = (X.map List.head?).map (Option.map Fp.ofNat) := by
    intro X; simp only [List.map_map]; apply List.map_congr_left; intro m _; exact head_toFp m
  rw [e, e, count_ofNat _ hE, count_ofNat _ hE] at h
  · exact h
  · intro o ho x hx; obtain ⟨m, hm, rfl⟩ := List.mem_map.mp ho; exact hB m hm x hx
  · intro o ho x hx; obtain ⟨m, hm, rfl⟩ := List.mem_map.mp ho; exact hA m hm x hx

theorem msgId_eq_iff {K c E : Nat} (hK : K < 16) : msgId K c = E ↔ E % 16 = K ∧ c = E / 16 := by
  unfold msgId; omega


theorem hcN_map {α : Type} (E : Nat) (l : List α) (g : α → Msg) :
    hcN E (l.map g) = (l.map fun x => if (g x).head? = some E then 1 else 0).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.map_cons, hcN_cons, ih]; simp

theorem sum_map_mul {α : Type} (k : Nat) (l : List α) (f : α → Nat) :
    (l.map fun x => k * f x).sum = k * (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih, Nat.mul_add]

theorem sum_map_add {α : Type} (l : List α) (f g : α → Nat) :
    (l.map fun x => f x + g x).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; omega

/-- The heads of a list are those of `range n`: each value occurs at most once. -/
theorem hcN_le_one_of_heads {l : List Msg} {n : Nat} (h : l.map List.head? = (List.range n).map some)
    (E : Nat) : hcN E l ≤ 1 := by
  unfold hcN; rw [h]
  exact List.nodup_iff_count.mp (List.Pairwise.map some (fun _ _ h e => h (Option.some.inj e)) List.nodup_range) _

theorem hcN_pos_of_heads {l : List Msg} {n : Nat} (h : l.map List.head? = (List.range n).map some)
    {E : Nat} (hE : 0 < hcN E l) : E < n := by
  unfold hcN at hE; rw [h] at hE
  obtain ⟨x, hx, he⟩ := List.mem_map.mp (List.count_pos_iff.mp hE)
  cases he; exact List.mem_range.mp hx

theorem two_le_countP {α : Type} (p : α → Bool) {a b : α} (hab : a ≠ b) (pa : p a = true) (pb : p b = true) :
    ∀ {l : List α}, a ∈ l → b ∈ l → 2 ≤ l.countP p
  | [], ha, _ => by simp at ha
  | x :: l, ha, hb => by
    rcases List.mem_cons.mp ha with h1 | ha' <;> rcases List.mem_cons.mp hb with h2 | hb'
    · exact absurd (h1.trans h2.symm) hab
    · subst h1; have := List.countP_pos_iff.mpr ⟨b, hb', pb⟩; rw [List.countP_cons, if_pos pa]; omega
    · subst h2; have := List.countP_pos_iff.mpr ⟨a, ha', pa⟩; rw [List.countP_cons, if_pos pb]; omega
    · have := two_le_countP p hab pa pb ha' hb'; rw [List.countP_cons]; split <;> omega

/-! ## `DIGS` windows counted by head -/

theorem hcN_kids (E τ d : Nat) (R : List (Nat × Nat × Nat × List Nat × List Nat)) :
    hcN E (R.flatMap fun (c, _, _, pre, _) =>
        (List.range 32).map fun i => [msgId K_NPRE c, τ, i, pre.getD i 0]) =
      if E % 16 = K_NPRE then 32 * hcN (E / 16) (R.map fun (c, l, r, _, _) => [c, τ, d + 1, l, r]) else 0 := by
  induction R with
  | nil => simp [hcN_nil]
  | cons x R ih =>
    obtain ⟨c, l, r, pre, po⟩ := x
    rw [List.flatMap_cons, hcN_append, ih, hcN_block, List.map_cons, hcN_cons]
    simp only [List.head?_cons, Option.some.injEq]
    have := msgId_eq_iff (K := K_NPRE) (c := c) (E := E) (by decide)
    by_cases h1 : E % 16 = K_NPRE <;> by_cases h2 : c = E / 16 <;> simp_all <;> omega

theorem hcN_digsOf (E : Nat) (s : NodeS3) :
    hcN E (digsOf s) =
      (if E % 16 = K_NPRE then 32 * hcN (E / 16)
        (s.v.revealed.map fun (c, l, r, _, _) => [c, s.tau, s.depth + 1, l, r]) else 0) +
      (if E % 16 = K_VPRE then 32 * hcN (E / 16) (vparMsg s) else 0) := by
  unfold digsOf
  rw [hcN_append, hcN_kids E s.tau s.depth]
  congr 1
  unfold vparMsg
  cases s.v.value with
  | none => simp [hcN_nil]
  | some x =>
    obtain ⟨i, l, pre, po, w⟩ := x
    simp only
    rw [hcN_block, hcN_cons, hcN_nil]
    simp only [List.head?_cons, Option.some.injEq]
    have := msgId_eq_iff (K := K_VPRE) (c := i) (E := E) (by decide)
    by_cases h1 : E % 16 = K_VPRE <;> by_cases h2 : i = E / 16 <;> simp_all <;> omega

theorem hcN_digsH (E : Nat) (h : HeadE) :
    hcN E (digsH h) = if E % 16 = K_NPRE then 32 * hcN (E / 16) [[h.rid, h.tau, 0, h.rlen, h.rres]] else 0 := by
  unfold digsH
  rw [hcN_block, hcN_cons, hcN_nil]
  simp only [List.head?_cons, Option.some.injEq]
  have := msgId_eq_iff (K := K_NPRE) (c := h.rid) (E := E) (by decide)
  by_cases h1 : E % 16 = K_NPRE <;> by_cases h2 : h.rid = E / 16 <;> simp_all <;> omega

theorem sum_map_zero {α : Type} (l : List α) : (l.map fun _ => (0 : Nat)).sum = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]

theorem sum_ite {α : Type} (l : List α) (c : Prop) [Decidable c] (A : α → Nat) :
    (l.map fun x => if c then A x else 0).sum = if c then (l.map A).sum else 0 := by
  by_cases hc : c
  · simp only [hc, ite_true]
  · simp only [hc, ite_false, sum_map_zero]

theorem hcN_map' {α : Type} (E : Nat) (l : List α) (g : α → Msg) :
    hcN E (l.map g) = (l.map fun x => hcN E [g x]).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.map_cons, hcN_cons, ih, List.map_cons, List.sum_cons, hcN_cons, hcN_nil, Nat.add_zero]

/-- **The `DIGS` sends by head**: `32 ·` the `PARENT` sends (kind `NPRE`) or the `VPARENT` sends
(kind `VPRE`) with the record id as head. -/
theorem hcN_digs (E : Nat) (vs : List NodeS3) (hs : List HeadE) :
    hcN E (nodeSends3 vs B_DIGS ++ headSends hs B_DIGS) =
      (if E % 16 = K_NPRE then 32 * hcN (E / 16) (nodeSends3 vs B_PARENT ++ headSends hs B_PARENT) else 0) +
      (if E % 16 = K_VPRE then 32 * hcN (E / 16) (nodeSends3 vs B_VPARENT) else 0) := by
  have L : hcN E (nodeSends3 vs B_DIGS ++ headSends hs B_DIGS) =
      ((vs.zip (List.range vs.length)).map fun x => hcN E (digsOf x.1)).sum +
      (hs.map fun h => hcN E (digsH h)).sum := by
    rw [digsS, hcN_append, hcN_flatMap, hcN_flatMap]
  have R1 : hcN (E / 16) (nodeSends3 vs B_PARENT ++ headSends hs B_PARENT) =
      ((vs.zip (List.range vs.length)).map fun x => hcN (E / 16)
        (x.1.v.revealed.map fun (c, l, r, _, _) => [c, x.1.tau, x.1.depth + 1, l, r])).sum +
      (hs.map fun h => hcN (E / 16) [[h.rid, h.tau, 0, h.rlen, h.rres]]).sum := by
    rw [parentS, headS, hcN_append, hcN_flatMap, hcN_map']
  have R2 : hcN (E / 16) (nodeSends3 vs B_VPARENT) =
      ((vs.zip (List.range vs.length)).map fun x => hcN (E / 16) (vparMsg x.1)).sum := by
    rw [vparentS, hcN_flatMap]
  have e1 : ((vs.zip (List.range vs.length)).map fun x => hcN E (digsOf x.1)) =
      ((vs.zip (List.range vs.length)).map fun x =>
        (if E % 16 = K_NPRE then 32 * hcN (E / 16)
          (x.1.v.revealed.map fun (c, l, r, _, _) => [c, x.1.tau, x.1.depth + 1, l, r]) else 0) +
        (if E % 16 = K_VPRE then 32 * hcN (E / 16) (vparMsg x.1) else 0)) := by
    apply List.map_congr_left; intro x _; exact hcN_digsOf E x.1
  have e2 : (hs.map fun h => hcN E (digsH h)) = hs.map fun h =>
      if E % 16 = K_NPRE then 32 * hcN (E / 16) [[h.rid, h.tau, 0, h.rlen, h.rres]] else 0 := by
    apply List.map_congr_left; intro h _; exact hcN_digsH E h
  rw [L, R1, R2, e1, e2, sum_map_add, sum_ite, sum_ite, sum_ite]
  by_cases h1 : E % 16 = K_NPRE
  · have h2 : ¬ E % 16 = K_VPRE := by rw [h1]; decide
    have h3 : ¬ K_NPRE = K_VPRE := by decide
    simp only [h1, h3, ite_true, ite_false, sum_map_mul, Nat.mul_add, Nat.add_zero]
  · simp only [h1, ite_false, Nat.zero_add]
    by_cases h2 : E % 16 = K_VPRE
    · simp only [h2, ite_true, sum_map_mul, Nat.add_zero]
    · simp only [h2, ite_false]

/-! ## The receive sides -/

theorem hcN_uniqRecvs (E : Nat) (us : List UniqE) :
    hcN E (uniqRecvs us B_DIGS) = 32 * us.countP (fun e => e.eid == E) := by
  rw [digsR, hcN_flatMap]
  induction us with
  | nil => rfl
  | cons e us ih =>
    rw [List.map_cons, List.sum_cons, ih, hcN_block, List.countP_cons]
    by_cases h : e.eid = E <;> simp [h, Nat.mul_add] <;> omega

theorem parentR_heads (vs : List NodeS3) :
    (nodeRecvs3 vs B_PARENT).map List.head? = (List.range vs.length).map some := by
  rw [parentR, List.map_map]
  apply List.ext_getElem (by simp)
  intro i h1 h2; simp

theorem vparentR_heads {es : List ValE} (hvw : ValWf es) :
    (valRecvs es B_VPARENT).map List.head? = (List.range es.length).map some := by
  rw [vparentR, List.map_map]
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, Function.comp, List.head?_cons, List.getElem_range]
  rw [vid_small hvw]

theorem headsLt_of_heads {l : List Msg} {n : Nat} (h : l.map List.head? = (List.range n).map some)
    (hn : n ≤ 2 ^ 22) : HeadsLt l := by
  intro m hm x hx
  have : some x ∈ (List.range n).map some := by rw [← h]; exact List.mem_map.mpr ⟨m, hm, hx⟩
  obtain ⟨y, hy, he⟩ := List.mem_map.mp this
  cases he; have := List.mem_range.mp hy; unfold P; omega

variable {vs : List NodeS3} {hs : List HeadE} {es : List ValE} {us : List UniqE} {others : List Msg}
  {shaS shaR : Nat → List Fp → Nat}

theorem parentS_lt (hw : NodeWf3 vs) (hhw : HeadWf hs) :
    HeadsLt (nodeSends3 vs B_PARENT ++ headSends hs B_PARENT) := by
  intro m hm x hx
  rw [List.mem_append, parentS, headS] at hm
  rcases hm with hm | hm
  · rw [List.mem_flatMap] at hm
    obtain ⟨⟨s, n⟩, hsn, hm⟩ := hm
    obtain ⟨hn, rfl⟩ := mem_zip_range hsn
    obtain ⟨⟨c, l, r, pre, po⟩, hk, rfl⟩ := List.mem_map.mp hm
    cases hx
    exact hw.canon _ (List.getElem_mem hn) _ (revealed_raw hk).1
  · obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hm
    cases hx; exact (hhw.canon h hh).2.1

theorem vparentS_lt (hw : NodeWf3 vs) : HeadsLt (nodeSends3 vs B_VPARENT) := by
  intro m hm x hx
  rw [vparentS, List.mem_flatMap] at hm
  obtain ⟨⟨s, n⟩, hsn, hm⟩ := hm
  obtain ⟨hn, rfl⟩ := mem_zip_range hsn
  unfold vparMsg at hm
  cases hv : vs[n].v.value with
  | none => simp [hv] at hm
  | some y =>
    obtain ⟨i, l, pre, po, w⟩ := y
    simp only [hv, List.mem_singleton] at hm
    subst hm; cases hx
    exact hw.canon _ (List.getElem_mem hn) _ (value_raw hv).1

theorem uniqR_lt (huw : UniqWf us) : HeadsLt (uniqRecvs us B_DIGS) := by
  intro m hm x hx
  rw [digsR, List.mem_flatMap] at hm
  obtain ⟨e, he, hm⟩ := hm
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp hm
  cases hx; exact (huw.canon e he).1

theorem digsS_lt (hw : NodeWf3 vs) (hhw : HeadWf hs) (hvw : ValWf es) (hb : ParentBal vs hs)
    (hvb : VParentBal vs es) (H : ShaHyp vs hs es others shaS shaR) :
    HeadsLt (nodeSends3 vs B_DIGS ++ headSends hs B_DIGS) := by
  intro m hm x hx
  obtain ⟨E, τ', j, hE, -, -, rfl⟩ := digs_send hw hhw hvw hb hvb H hm
  cases hx; exact hE

/-! ## Step 4: `uniq` ids are unique -/

/-- **`DIGS` counting**: at most one `uniq` entry per id. -/
theorem eid_count (hw : NodeWf3 vs) (hhw : HeadWf hs) (hvw : ValWf es) (huw : UniqWf us)
    (hb : ParentBal vs hs) (hvb : VParentBal vs es) (H : ShaHyp vs hs es others shaS shaR)
    (hD : DigsBal vs hs us) {E : Nat} (hE : E < P) : us.countP (fun e => e.eid == E) ≤ 1 := by
  have h1 := hcN_uniqRecvs E us
  have h2 := hcN_perm hD (digsS_lt hw hhw hvw hb hvb H) (uniqR_lt huw) hE
  rw [hcN_digs] at h2
  have hE16 : E / 16 < P := by unfold P at *; omega
  have hpar : hcN (E / 16) (nodeSends3 vs B_PARENT ++ headSends hs B_PARENT) ≤ 1 := by
    rw [hcN_perm (List.perm_iff_count.mpr hb) (parentS_lt hw hhw)
      (headsLt_of_heads (parentR_heads vs) hw.count) hE16]
    exact hcN_le_one_of_heads (parentR_heads vs) _
  have hvpar : hcN (E / 16) (nodeSends3 vs B_VPARENT) ≤ 1 := by
    rw [hcN_perm (List.perm_iff_count.mpr hvb) (vparentS_lt hw)
      (headsLt_of_heads (vparentR_heads hvw) (vlen_le hvw)) hE16]
    exact hcN_le_one_of_heads (vparentR_heads hvw) _
  by_cases n1 : E % 16 = K_NPRE
  · have n2 : ¬ E % 16 = K_VPRE := by rw [n1]; decide
    rw [if_pos n1, if_neg n2] at h2; omega
  · rw [if_neg n1] at h2
    by_cases n2 : E % 16 = K_VPRE
    · rw [if_pos n2] at h2; omega
    · rw [if_neg n2] at h2; omega

/-- **The id of a `uniq` entry is a record id**: a node record (`NPRE n`, `n < |vs|`) or a value
record (`VPRE t`, `t < |es|`). -/
theorem eid_cases (hw : NodeWf3 vs) (hhw : HeadWf hs) (hvw : ValWf es) (huw : UniqWf us)
    (hb : ParentBal vs hs) (hvb : VParentBal vs es) (H : ShaHyp vs hs es others shaS shaR)
    (hD : DigsBal vs hs us) {e : UniqE} (he : e ∈ us) :
    (e.eid = msgId K_NPRE (e.eid / 16) ∧ e.eid / 16 < vs.length) ∨
      (e.eid = msgId K_VPRE (e.eid / 16) ∧ e.eid / 16 < es.length) := by
  have hE := (huw.canon e he).1
  have h0 : 0 < us.countP (fun e' => e'.eid == e.eid) := List.countP_pos_iff.mpr ⟨e, he, by simp⟩
  have h1 := hcN_uniqRecvs e.eid us
  have h2 := hcN_perm hD (digsS_lt hw hhw hvw hb hvb H) (uniqR_lt huw) hE
  rw [hcN_digs] at h2
  have hE16 : e.eid / 16 < P := by unfold P at *; omega
  by_cases n1 : e.eid % 16 = K_NPRE
  · have n2 : ¬ e.eid % 16 = K_VPRE := by rw [n1]; decide
    rw [if_pos n1, if_neg n2] at h2
    rw [hcN_perm (List.perm_iff_count.mpr hb) (parentS_lt hw hhw)
      (headsLt_of_heads (parentR_heads vs) hw.count) hE16] at h2
    left
    exact ⟨((msgId_eq_iff (by decide)).2 ⟨n1, rfl⟩).symm,
      hcN_pos_of_heads (parentR_heads vs) (by omega)⟩
  · rw [if_neg n1] at h2
    by_cases n2 : e.eid % 16 = K_VPRE
    · rw [if_pos n2] at h2
      rw [hcN_perm (List.perm_iff_count.mpr hvb) (vparentS_lt hw)
        (headsLt_of_heads (vparentR_heads hvw) (vlen_le hvw)) hE16] at h2
      right
      exact ⟨((msgId_eq_iff (by decide)).2 ⟨n2, rfl⟩).symm,
        hcN_pos_of_heads (vparentR_heads hvw) (by omega)⟩
    · rw [if_neg n2] at h2; omega

/-! ## Step 5: the record of an `eq = 0` entry is not a duplicate -/

theorem dup_sender (huw : UniqWf us) (hDUP : DupBal us vs es) {m : Msg}
    (hm : m ∈ nodeRecvs3 vs B_DUP ++ valRecvs es B_DUP) :
    ∃ e' ∈ us, e'.eq = 1 ∧ Msg.toFp [e'.eid, e'.peid] = Msg.toFp m := by
  have h1 := List.mem_map_of_mem (f := Msg.toFp) hm
  rw [← hDUP.mem_iff, List.mem_map, dupS] at h1
  obtain ⟨m', hm', he⟩ := h1
  obtain ⟨e', he', rfl⟩ := List.mem_map.mp hm'
  obtain ⟨he'', hq⟩ := List.mem_filter.mp he'
  exact ⟨e', he'', by simpa using hq, he⟩

theorem eq0_nondup_node (hw : NodeWf3 vs) (hhw : HeadWf hs) (hvw : ValWf es) (huw : UniqWf us)
    (hb : ParentBal vs hs) (hvb : VParentBal vs es) (H : ShaHyp vs hs es others shaS shaR)
    (hD : DigsBal vs hs us) (hDUP : DupBal us vs es) {e : UniqE} (he : e ∈ us) (h0 : e.eq = 0)
    {n : Nat} (hn : n < vs.length) (hid : e.eid = msgId K_NPRE n) : vs[n].dup = false := by
  cases hd : vs[n].dup with
  | false => rfl
  | true =>
    exfalso
    have hm : [eidN n, vs[n].repE] ∈ nodeRecvs3 vs B_DUP ++ valRecvs es B_DUP := by
      rw [dupR]; apply List.mem_append_left
      exact List.mem_filterMap.mpr ⟨(vs[n], n), zip_range_mem vs hn, by simp [hd]⟩
    obtain ⟨e', he', h1, hfe⟩ := dup_sender huw hDUP hm
    simp only [Msg.toFp, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hfe
    have hid' : e'.eid = e.eid := by
      rw [hid]; exact ofNat_eq (huw.canon e' he').1 (nid_lt hw hn K_NPRE (by decide)) hfe.1
    have hne : e ≠ e' := by intro h; rw [← h] at h1; omega
    have := two_le_countP (fun x : UniqE => x.eid == e.eid) hne (by simp) (by simp [hid']) he he'
    have := eid_count hw hhw hvw huw hb hvb H hD (huw.canon e he).1
    omega

theorem eq0_nondup_val (hw : NodeWf3 vs) (hhw : HeadWf hs) (hvw : ValWf es) (huw : UniqWf us)
    (hb : ParentBal vs hs) (hvb : VParentBal vs es) (H : ShaHyp vs hs es others shaS shaR)
    (hD : DigsBal vs hs us) (hDUP : DupBal us vs es) {e : UniqE} (he : e ∈ us) (h0 : e.eq = 0)
    {t : Nat} (ht : t < es.length) (hid : e.eid = msgId K_VPRE t) : es[t].dup = false := by
  cases hd : es[t].dup with
  | false => rfl
  | true =>
    exfalso
    have hm : [eidV es[t], es[t].repE] ∈ nodeRecvs3 vs B_DUP ++ valRecvs es B_DUP := by
      rw [dupR]; apply List.mem_append_right
      exact List.mem_flatMap.mpr ⟨es[t], List.getElem_mem ht, by simp [hd]⟩
    obtain ⟨e', he', h1, hfe⟩ := dup_sender huw hDUP hm
    simp only [Msg.toFp, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hfe
    have hlt : eidV es[t] < P := by
      have := vlen_le hvw; unfold eidV msgId K_VPRE P; rw [vid_small hvw ht]; omega
    have hid' : e'.eid = e.eid := by
      rw [hid, ofNat_eq (huw.canon e' he').1 hlt hfe.1, eidV, vid_small hvw ht]
    have hne : e ≠ e' := by intro h; rw [← h] at h1; omega
    have := two_le_countP (fun x : UniqE => x.eid == e.eid) hne (by simp) (by simp [hid']) he he'
    have := eid_count hw hhw hvw huw hb hvb H hD (huw.canon e he).1
    omega

/-! ## Step 6: the store sum -/

theorem valPart_le : ∀ (l : List ValE), (∀ e ∈ l, (e.vz = true → e.len = 0 ∧ e.bytes = []) ∧
    (e.vz = false → e.bytes.length = e.len ∧ 0 < e.len)) →
    ((l.filter fun e => !e.dup).map fun e => (toB e.bytes).length).sum ≤ valStoreSum l
  | [], _ => by simp [valStoreSum]
  | e :: l, h => by
    have ih := valPart_le l (fun e' he' => h e' (List.mem_cons_of_mem _ he'))
    have he := h e List.mem_cons_self
    unfold valStoreSum at ih ⊢
    cases hd : e.dup <;> cases hz : e.vz <;>
      simp_all [List.filter_cons, toB]

/-- **The store of an instance is within the non-duplicate record bytes**: every duplicate-free
list of blobs of the witness store of a head's instance sums to at most `nodeStoreSum + valStoreSum`. -/
theorem store_sum_le (hw : NodeWf3 vs) (hhw : HeadWf hs) (hvw : ValWf es) (huw : UniqWf us)
    (hb : ParentBal vs hs) (hvb : VParentBal vs es) (H : ShaHyp vs hs es others shaS shaR)
    (hD : DigsBal vs hs us) (hDUP : DupBal us vs es) (hENT : EntBal vs es) {h : HeadE} (hh : h ∈ hs)
    (D : List NearSpec.Bytes) (hDn : D.Nodup)
    (hsub : ∀ d ∈ D, d ∈ storeOf (recsOf (vpos (vid0 es)) vs) (valsOf3 vs es) h.tau) :
    (D.map List.length).sum ≤ nodeStoreSum vs + valStoreSum es := by
  let f : NodeS3 ⊕ ValE → NearSpec.Bytes := Sum.elim (fun s => toB (s.v.ser false)) (fun e => toB e.bytes)
  let L : List (NodeS3 ⊕ ValE) :=
    (vs.filter fun s => !s.dup).map Sum.inl ++ (es.filter fun e => !e.dup).map Sum.inr
  have hc := sum_le_of_cover List.length f L D hDn (by
    intro d hd
    obtain ⟨e, he, -, hbe, -⟩ := store_cov hw hhw hvw huw hb hvb H hD hh d (hsub d hd)
    obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem he
    obtain ⟨t0, h0, -, heq, hbt, -⟩ := uniq_walkback hw hvw huw hDUP hENT t ht
    have hm0 : us[t0] ∈ us := List.getElem_mem h0
    rcases eid_cases hw hhw hvw huw hb hvb H hD hm0 with ⟨hid, hn⟩ | ⟨hid, ht'⟩
    · generalize us[t0].eid / 16 = n at hid hn
      have nd := eq0_nondup_node hw hhw hvw huw hb hvb H hD hDUP hm0 heq hn hid
      refine ⟨Sum.inl vs[n], List.mem_append_left _ (List.mem_map.mpr
        ⟨_, List.mem_filter.mpr ⟨List.getElem_mem hn, by simp [nd]⟩, rfl⟩), ?_⟩
      rw [← hbe, ← hbt, hid, bOf, bN_node vs es hn]; rfl
    · generalize us[t0].eid / 16 = n at hid ht'
      have nd := eq0_nondup_val hw hhw hvw huw hb hvb H hD hDUP hm0 heq ht' hid
      refine ⟨Sum.inr es[n], List.mem_append_right _ (List.mem_map.mpr
        ⟨_, List.mem_filter.mpr ⟨List.getElem_mem ht', by simp [nd]⟩, rfl⟩), ?_⟩
      rw [← hbe, ← hbt, hid, bOf, bN_val vs es ht']; rfl)
  have hL : (L.map (List.length ∘ f)).sum =
      ((vs.filter fun s => !s.dup).map fun s => (s.v.ser false).length).sum +
      ((es.filter fun e => !e.dup).map fun e => (toB e.bytes).length).sum := by
    simp only [L, List.map_append, List.sum_append, List.map_map]
    congr 2
    apply List.map_congr_left; intro s _; simp [f, toB]
  have hv := valPart_le es (fun e he => hvw.shape e he)
  unfold nodeStoreSum
  omega

end LinkStore

/-! ## `mainStoreBytes` from the records -/

theorem foldl_add_eq_sum : ∀ (l : List Nat) (a : Nat), l.foldl (· + ·) a = a + l.sum
  | [], a => by simp
  | x :: l, a => by rw [List.foldl_cons, foldl_add_eq_sum l, List.sum_cons]; omega

/-- **`GoodV3.mainStoreBytes`** for any duplicate-free list of blobs of instance `0`'s witness
store (`R = recsOf (vpos (vid0 r.values)) r.nodes`, `V = valsOf3 r.nodes r.values`). -/
theorem mainStoreBytes_of {cb : NearSpec.Bytes} {h : NearSpecV3.Hint} {p : NearSpecV3.Prep} {oh : Nat}
    {tr : Trace Fp} {r : V3Records} (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    (D : List NearSpec.Bytes) (hDn : D.Nodup)
    (hsub : ∀ d ∈ D, d ∈ storeOf (ZkFormal.NearV3.Link3.recsOf
      (ZkFormal.NearV3.Link3.vpos (ZkFormal.NearV3.Link3.vid0 r.values)) r.nodes)
      (ZkFormal.NearV3.Link3.valsOf3 r.nodes r.values) 0) :
    (D.map List.length).foldl (· + ·) 0 ≤ 3000000 := by
  have L := trieLink_of hp hsz hH T W
  obtain ⟨hm, ht⟩ := L.chain.head_mem 0 (Nat.zero_le _)
  have hs := LinkStore.store_sum_le W.nodes W.heads W.values W.uniq L.parent L.vparent L.sha L.digs
    L.dup L.ent hm D hDn (by rw [ht]; exact hsub)
  have := (size_totals hH T W).2.2
  rw [foldl_add_eq_sum, Nat.zero_add]; omega


theorem eraseDups_nodup' {α : Type} [BEq α] [LawfulBEq α] (xs : List α) : xs.eraseDups.Nodup := by
  match xs with
  | [] => simp
  | a :: xs =>
    rw [List.eraseDups_cons, List.nodup_cons]
    refine ⟨?_, eraseDups_nodup' _⟩
    simp
termination_by xs.length
decreasing_by exact Nat.lt_succ_of_le (List.length_filter_le ..)

/-- **`GoodV3.mainStoreBytes`** for the reconstruction whose records are the views' records. -/
theorem mainStoreBytes_ext {cb : NearSpec.Bytes} {h : NearSpecV3.Hint} {p : NearSpecV3.Prep} {oh : Nat}
    {tr : Trace Fp} {r : V3Records} (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    (x : ExtV3) (hn : x.nodes = r.nodes) (hv : x.values = r.values) :
    ((x.store 0).map List.length).foldl (· + ·) 0 ≤ 3000000 := by
  apply mainStoreBytes_of hp hsz hH T W _ (eraseDups_nodup' _)
  intro d hd
  have hd := List.mem_eraseDups.mp hd
  simp only [ExtV3.rawStore, ExtV3.valuePosition, hn, hv] at hd
  exact hd

end ZkFormal.NearV3.Assembly
