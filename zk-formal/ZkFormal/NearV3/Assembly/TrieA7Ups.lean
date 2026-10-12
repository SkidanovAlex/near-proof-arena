import ZkFormal.NearV3.Assembly.TrieA7Node

/-!
# ZkFormal.NearV3.Assembly.TrieA7Ups — record-level traffic of `upsA7`'s appended interactions

The A7 extension of `upsV3` (`Tables/UnfoldA7.lean`, `Ups.interactions`) sends
`RPL (sN)` on the first row of every upper part (kinds `RDB`, `RDE`, `PT`), `RPL (N_D)` and,
when the old `0x0f` value is present, `RPLV (vid)` on the segment's first row, and
`SIZE (5, s)` on the table's last row.  On the honest aligned trace (`upsA7Trace insts T_UPS`):

* `ups_rpl_sends`: `RPL` sends = `insts.flatMap upsRplMsgs` — per instance `[N_D]`, then
  `[sN]` of every upper part with a row (`nDOf`, `upperB`);
* `ups_rplv_sends`: `RPLV` sends = `insts.flatMap upsRplvMsgs` — `[vid]` when the walk's last
  step is a value step (`presV`);
* `ups_size_sends`: the only `SIZE` send is `[5, upsA7Total insts % P]`,
  `upsA7Total insts = Σ_I (L_I + Σ_k |Q_k|)`;
* no `RPL`/`RPLV`/`SIZE` receives.
-/

namespace ZkFormal.NearV3.Assembly.TrieA7

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.Render
  ZkFormal.NearV3.UnfoldA7

section Ups
open UpsGen

/-- The terminal record `N_D` of an instance (as the segment's `nD` cell). -/
def nDOf (I : UpsInst) : Nat :=
  if I.D = 0 then I.N.getD 0 0 else if I.D = 1 then I.N.getD 1 0 else if I.D = 2 then I.N.getD 2 0 else 0

/-- Upper parts (`RDB`, `RDE`, `PT`): they replace their source record. -/
def upperB (Q : UpsPartI) : Bool := Q.kind == 0 || Q.kind == 1 || Q.kind == 11

/-- `RPL` sends of one instance's segment (row order). -/
def upsRplMsgs (I : UpsInst) : List Msg :=
  [nDOf I % P] :: (List.range (nQ I)).flatMap fun k =>
    if upperB (part I k) = true ∧ 0 < (part I k).q.length then [[(part I k).sN % P]] else []

/-- `RPLV` sends of one instance's segment. -/
def upsRplvMsgs (I : UpsInst) : List Msg :=
  if (step I 3).mode = 0 then [[(step I 3).e.getD 3 0 % P]] else []

/-- The A7 ups total `Σ_I (L_I + Σ_k |Q_k|)`. -/
def upsA7Total (insts : List UpsInst) : Nat :=
  (insts.map fun I => L I + ((List.range (nQ I)).map fun k => (part I k).q.length).sum).sum

theorem ups_base_cell (insts : List UpsInst) (q x : Nat) (hq : q < (upsTraceAligned insts).height T_UPS)
    (hx : x < 200) : (upsTraceAligned insts).cell T_UPS q x = ((UpsGen.cell insts q x : Int) : Fp) := by
  exact (rowsTrace_mkTab _ _ _ T_UPS q x hq hx).trans (Fp.ofNat_toNat _)

theorem ups_height (insts : List UpsInst) (h : UpsRenderOk insts) :
    UpsGen.R insts + 1 ≤ (upsTraceAligned insts).height T_UPS := by
  have := (padded_log_fits (UpsGen.R insts + 1) h.ok.cap)
  exact this.1

/-- Row values on an active row `(i, rk)`. -/
def rplRow (I : UpsInst) : RK → List Msg
  | .w t => if t = 0 then [[nDOf I % P]] else []
  | .v _ => []
  | .q k p => if p = 0 ∧ upperB (part I k) = true then [[(part I k).sN % P]] else []

def rplvRow (I : UpsInst) : RK → List Msg
  | .w t => if t = 0 then upsRplvMsgs I else []
  | _ => []

def sRow : RK → Nat
  | .w _ => 0
  | _ => 1

theorem castInd (p : Prop) [Decidable p] : ((ind p : Int) : Fp) = if p then 1 else 0 := by
  unfold ind; split <;> decide

theorem cast_nat (n : Nat) : (((n : Nat) : Int) : Fp) = Fp.ofNat n := by
  rw [Lean.Grind.Ring.intCast_natCast]; rfl

theorem upV_cast (Q : UpsPartI) : ((upV Q : Int) : Fp) = if upperB Q = true then 1 else 0 := by
  unfold upV kin upperB
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  by_cases h0 : Q.kind = 0
  · simp [h0, ind]; decide
  · by_cases h1 : Q.kind = 1
    · simp [h1, ind]; decide
    · by_cases h11 : Q.kind = 11
      · simp [h11, ind]; decide
      · simp [h0, h1, h11, ind]; decide

theorem nD_cast (I : UpsInst) :
    ((ind (I.D = 0) : Int) : Fp) * (((I.N.getD 0 0 : Nat) : Int) : Fp) +
      (((ind (I.D = 1) : Int) : Fp) * (((I.N.getD 1 0 : Nat) : Int) : Fp) +
        (((ind (I.D = 2) : Int) : Fp) * (((I.N.getD 2 0 : Nat) : Int) : Fp) + 0)) = Fp.ofNat (nDOf I) := by
  simp only [castInd, cast_nat, nDOf]
  by_cases h0 : I.D = 0
  · simp [h0]; grind
  · by_cases h1 : I.D = 1
    · simp [h1]; grind
    · by_cases h2 : I.D = 2
      · simp [h2]; grind
      · simp [h0, h1, h2]; rw [show Fp.ofNat 0 = (0 : Fp) by decide]; grind


theorem ups_cells (insts : List UpsInst) (q : Nat) (hq : q < (upsTraceAligned insts).height T_UPS) :
    (∀ x, x < 200 → (upsA7Trace insts T_UPS).cell T_UPS q x = ((UpsGen.cell insts q x : Int) : Fp)) ∧
    (upsA7Trace insts T_UPS).cell T_UPS q Ups.nD =
      ((UpsGen.cell insts q 28 : Int) : Fp) * ((UpsGen.cell insts q 11 : Int) : Fp) +
        (((UpsGen.cell insts q 29 : Int) : Fp) * ((UpsGen.cell insts q 12 : Int) : Fp) +
          (((UpsGen.cell insts q 30 : Int) : Fp) * ((UpsGen.cell insts q 13 : Int) : Fp) + 0)) ∧
    (upsA7Trace insts T_UPS).cell T_UPS q Ups.s =
      prefixF (fun r => (upsTraceAligned insts).cell T_UPS r ZkFormal.NearV3.UpsV3.vb +
        (upsTraceAligned insts).cell T_UPS r ZkFormal.NearV3.UpsV3.qb) q := by
  refine ⟨fun x hx => ?_, ?_, ?_⟩
  · simp only [upsA7Trace]; rw [cell_withCols_lt hx]; exact ups_base_cell insts q x hq hx
  · simp only [upsA7Trace]; rw [cell_withCols_ge (by decide)]
    simp only [upsCols, Ups.s, Ups.nD, upsND]
    simp only [show (201 = 200) = False by decide, if_false, if_true]
    rw [ups_base_cell insts q _ hq (by decide), ups_base_cell insts q _ hq (by decide),
      ups_base_cell insts q _ hq (by decide), ups_base_cell insts q _ hq (by decide),
      ups_base_cell insts q _ hq (by decide), ups_base_cell insts q _ hq (by decide)]
    rfl
  · simp only [upsA7Trace]; rw [cell_withCols_ge (by decide)]
    simp [upsCols, Ups.s]

/-- One row's `RPL` sends. -/
theorem ups_rpl_row (insts : List UpsInst) (pub : List Fp) (q : Nat)
    (hq : q < (upsTraceAligned insts).height T_UPS) :
    (rowTraffic UnfoldA7.Ups.interactions (upsA7Trace insts T_UPS) T_UPS q pub B_RPL true).map
        (List.map Fp.toNat) =
      if q < UpsGen.R insts then rplRow (inst insts ((recs insts).getD q default).1) ((recs insts).getD q default).2
      else [] := by
  obtain ⟨cB, cD, -⟩ := ups_cells insts q hq
  have z : ((0 : Fp) = 1) = False := by decide
  have o1 : ((1 : Int) : Fp) = 1 := by decide
  have o0 : ((0 : Int) : Fp) = 0 := by decide
  have m11 : Fp.mul 1 1 = 1 := by decide
  have m10 : Fp.mul 1 0 = 0 := by decide
  have m01 : Fp.mul 0 1 = 0 := by decide
  have m00 : Fp.mul 0 0 = 0 := by decide
  have bpf := cB _ (show ZkFormal.NearV3.UpsV3.pf < 200 by decide)
  have bup := cB _ (show ZkFormal.NearV3.UpsV3.up < 200 by decide)
  have bsN := cB _ (show ZkFormal.NearV3.UpsV3.sN < 200 by decide)
  have bsf := cB _ (show ZkFormal.NearV3.UpsV3.sf < 200 by decide)
  by_cases hR : q < UpsGen.R insts
  · have hc : ∀ x, UpsGen.cell insts q x = rowCell insts q ((recs insts).getD q default) x := fun x => by
      simp [UpsGen.cell, hR]
    simp only [hc] at bpf bup bsN bsf cD
    simp only [hR, if_true]
    generalize (recs insts).getD q default = a at bpf bup bsN bsf cD
    obtain ⟨i, rk⟩ := a
    have hD : ∀ rk, rowCell insts q (i, rk) 28 = ind ((inst insts i).D = 0) ∧
        rowCell insts q (i, rk) 29 = ind ((inst insts i).D = 1) ∧
        rowCell insts q (i, rk) 30 = ind ((inst insts i).D = 2) ∧
        rowCell insts q (i, rk) 11 = ((inst insts i).N.getD 0 0 : Nat) ∧
        rowCell insts q (i, rk) 12 = ((inst insts i).N.getD 1 0 : Nat) ∧
        rowCell insts q (i, rk) 13 = ((inst insts i).N.getD 2 0 : Nat) := fun rk => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    rw [(hD _).1, (hD _).2.1, (hD _).2.2.1, (hD _).2.2.2.1, (hD _).2.2.2.2.1, (hD _).2.2.2.2.2, nD_cast] at cD
    cases rk with
    | w t =>
      rw [show rowCell insts q (i, .w t) ZkFormal.NearV3.UpsV3.pf = 0 from rfl] at bpf
      rw [show rowCell insts q (i, .w t) ZkFormal.NearV3.UpsV3.up = 0 from rfl] at bup
      rw [show rowCell insts q (i, .w t) ZkFormal.NearV3.UpsV3.sf = ind (t = 0) from rfl] at bsf
      by_cases ht : t = 0
      · subst ht
        simp [rowTraffic, UnfoldA7.Ups.interactions, Dsl.send, B_RPL, B_RPLV, B_SIZE, Interaction.multNat,
          Interaction.multNat.go, Interaction.msgVal, bpf, bup, bsN, bsf, cD, rplRow, castInd, cast_nat, upV_cast,
          z, o1, o0, m11, m10, m01, m00, Fp.toNat_ofNat]
      · simp [rowTraffic, UnfoldA7.Ups.interactions, Dsl.send, B_RPL, B_RPLV, B_SIZE, Interaction.multNat,
          Interaction.multNat.go, Interaction.msgVal, bpf, bup, bsN, bsf, cD, rplRow, castInd, cast_nat, upV_cast,
          z, o1, o0, m11, m10, m01, m00, Fp.toNat_ofNat]
        simp [ht]
    | v p =>
      rw [show rowCell insts q (i, .v p) ZkFormal.NearV3.UpsV3.pf = ind (p = 0) from rfl] at bpf
      rw [show rowCell insts q (i, .v p) ZkFormal.NearV3.UpsV3.up = 0 from rfl] at bup
      rw [show rowCell insts q (i, .v p) ZkFormal.NearV3.UpsV3.sf = 0 from rfl] at bsf
      simp [rowTraffic, UnfoldA7.Ups.interactions, Dsl.send, B_RPL, B_RPLV, B_SIZE, Interaction.multNat,
          Interaction.multNat.go, Interaction.msgVal, bpf, bup, bsN, bsf, cD, rplRow, castInd, cast_nat, upV_cast,
          z, o1, o0, m11, m10, m01, m00, Fp.toNat_ofNat] <;>
        (by_cases hp : p = 0 <;> simp [hp] <;> decide)
    | q k p =>
      rw [show rowCell insts q (i, .q k p) ZkFormal.NearV3.UpsV3.pf = ind (p = 0) from rfl] at bpf
      rw [show rowCell insts q (i, .q k p) ZkFormal.NearV3.UpsV3.up = upV (part (inst insts i) k) from rfl] at bup
      rw [show rowCell insts q (i, .q k p) ZkFormal.NearV3.UpsV3.sN = ((part (inst insts i) k).sN : Nat) from rfl] at bsN
      rw [show rowCell insts q (i, .q k p) ZkFormal.NearV3.UpsV3.sf = 0 from rfl] at bsf
      by_cases hp : p = 0 <;> by_cases hu : upperB (part (inst insts i) k) = true <;>
      simp [rowTraffic, UnfoldA7.Ups.interactions, Dsl.send, B_RPL, B_RPLV, B_SIZE, Interaction.multNat,
          Interaction.multNat.go, Interaction.msgVal, bpf, bup, bsN, bsf, cD, rplRow, castInd, cast_nat, upV_cast,
          z, o1, o0, m11, m10, m01, m00, Fp.toNat_ofNat] <;> (try simp [hp, hu]) <;> (try decide) <;>
        (try (rw [show Fp.mul 1 1 = 1 by decide]; simp))
  · have hc : ∀ x, UpsGen.cell insts q x = 0 := fun x => by simp [UpsGen.cell, hR]
    simp only [hc] at bpf bup bsf
    simp [hR, rowTraffic, UnfoldA7.Ups.interactions, Dsl.send, B_RPL, B_RPLV, B_SIZE, Interaction.multNat,
      Interaction.multNat.go, bpf, bup, bsf, z, o0, m00]

/-- One row's `RPLV` sends. -/
theorem ups_rplv_row (insts : List UpsInst) (pub : List Fp) (q : Nat)
    (hq : q < (upsTraceAligned insts).height T_UPS) :
    (rowTraffic UnfoldA7.Ups.interactions (upsA7Trace insts T_UPS) T_UPS q pub B_RPLV true).map
        (List.map Fp.toNat) =
      if q < UpsGen.R insts then rplvRow (inst insts ((recs insts).getD q default).1) ((recs insts).getD q default).2
      else [] := by
  obtain ⟨cB, -, -⟩ := ups_cells insts q hq
  have z : ((0 : Fp) = 1) = False := by decide
  have o1 : ((1 : Int) : Fp) = 1 := by decide
  have o0 : ((0 : Int) : Fp) = 0 := by decide
  have bsf := cB _ (show ZkFormal.NearV3.UpsV3.sf < 200 by decide)
  have bpr := cB _ (show ZkFormal.NearV3.UpsV3.pres < 200 by decide)
  have bvi := cB _ (show ZkFormal.NearV3.UpsV3.vid < 200 by decide)
  have common : ∀ (a b c : Fp), (upsA7Trace insts T_UPS).cell T_UPS q ZkFormal.NearV3.UpsV3.sf = a →
      (upsA7Trace insts T_UPS).cell T_UPS q ZkFormal.NearV3.UpsV3.pres = b →
      (upsA7Trace insts T_UPS).cell T_UPS q ZkFormal.NearV3.UpsV3.vid = c →
      (rowTraffic UnfoldA7.Ups.interactions (upsA7Trace insts T_UPS) T_UPS q pub B_RPLV true).map
        (List.map Fp.toNat) = if a * b = 1 then [[c.toNat]] else [] := by
    intro a b c ha hb hc
    by_cases h : a * b = 1
    · have h2 : Fp.mul a b = 1 := h
      simp [rowTraffic, UnfoldA7.Ups.interactions, Dsl.send, B_RPL, B_RPLV, B_SIZE, Interaction.multNat,
        Interaction.multNat.go, Interaction.msgVal, ha, hb, hc, h, h2]
    · have h2 : ¬ Fp.mul a b = 1 := h
      simp [rowTraffic, UnfoldA7.Ups.interactions, Dsl.send, B_RPL, B_RPLV, B_SIZE, Interaction.multNat,
        Interaction.multNat.go, Interaction.msgVal, ha, hb, hc, h, h2]
  by_cases hR : q < UpsGen.R insts
  · have hc : ∀ x, UpsGen.cell insts q x = rowCell insts q ((recs insts).getD q default) x := fun x => by
      simp [UpsGen.cell, hR]
    simp only [hc] at bsf bpr bvi
    simp only [hR, if_true]
    generalize (recs insts).getD q default = a at bsf bpr bvi
    obtain ⟨i, rk⟩ := a
    rw [show rowCell insts q (i, rk) ZkFormal.NearV3.UpsV3.pres = presV (inst insts i) from rfl] at bpr
    rw [show rowCell insts q (i, rk) ZkFormal.NearV3.UpsV3.vid = vidV (inst insts i) from rfl] at bvi
    have hpv : ((presV (inst insts i) : Int) : Fp) = if (step (inst insts i) 3).mode = 0 then 1 else 0 :=
      castInd _
    have hvv : ((vidV (inst insts i) : Int) : Fp) =
        if (step (inst insts i) 3).mode = 0 then Fp.ofNat ((step (inst insts i) 3).e.getD 3 0) else 0 := by
      unfold vidV; rw [Lean.Grind.Ring.intCast_mul, castInd, cast_nat]; split <;> grind
    rw [hpv] at bpr; rw [hvv] at bvi
    cases rk with
    | w t =>
      rw [show rowCell insts q (i, .w t) ZkFormal.NearV3.UpsV3.sf = ind (t = 0) from rfl, castInd] at bsf
      rw [common _ _ _ bsf bpr bvi]
      by_cases ht : t = 0 <;> by_cases hm : (step (inst insts i) 3).mode = 0 <;>
        simp [ht, hm, rplvRow, upsRplvMsgs, Fp.toNat_ofNat] <;> decide
    | v p =>
      rw [show rowCell insts q (i, .v p) ZkFormal.NearV3.UpsV3.sf = 0 from rfl, o0] at bsf
      rw [common _ _ _ bsf bpr bvi]; simp [rplvRow]
      split <;> simp_all <;> decide
    | q k p =>
      rw [show rowCell insts q (i, .q k p) ZkFormal.NearV3.UpsV3.sf = 0 from rfl, o0] at bsf
      rw [common _ _ _ bsf bpr bvi]; simp [rplvRow]
      split <;> simp_all <;> decide
  · have hc : ∀ x, UpsGen.cell insts q x = 0 := fun x => by simp [UpsGen.cell, hR]
    simp only [hc, o0] at bsf bpr bvi
    rw [common _ _ _ bsf bpr bvi]; simp [hR]; decide

/-- Sends on bus `b` of the honest `upsA7` trace from a per-row description on active rows. -/
theorem ups_sends_of_rows (insts : List UpsInst) (h : UpsRenderOk insts) (pub : List Fp) (b : Nat)
    (G : UpsInst → RK → List Msg)
    (hrow : ∀ q, q < (upsTraceAligned insts).height T_UPS →
      (rowTraffic UnfoldA7.Ups.interactions (upsA7Trace insts T_UPS) T_UPS q pub b true).map (List.map Fp.toNat) =
        if q < UpsGen.R insts then G (inst insts ((recs insts).getD q default).1) ((recs insts).getD q default).2
        else []) :
    (traceTraffic UnfoldA7.Ups.interactions (upsA7Trace insts T_UPS) T_UPS pub).sends b =
      insts.flatMap fun I => (recsI I).flatMap (G I) := by
  have hH := ups_height insts h
  simp only [traceTraffic]
  rw [show (upsA7Trace insts T_UPS).height T_UPS = (upsTraceAligned insts).height T_UPS from rfl,
    ZkFormal.Near.Render.flatMap_congr' (fun q hq => hrow q (List.mem_range.1 hq)),
    ZkFormal.Near.Render.range_split (show UpsGen.R insts ≤ (upsTraceAligned insts).height T_UPS by omega),
    List.flatMap_append,
    ZkFormal.Near.Render.flatMap_nil' (l := List.map _ _) (fun q hq => by
      obtain ⟨q', _, rfl⟩ := List.mem_map.1 hq; simp only [show ¬ (UpsGen.R insts + q' < UpsGen.R insts) by omega,
        if_false]),
    List.append_nil,
    ZkFormal.Near.Render.flatMap_congr' (l := List.range (UpsGen.R insts))
      (g := fun q => G (inst insts ((recs insts).getD q default).1) ((recs insts).getD q default).2)
      (fun q hq => by simp [List.mem_range.1 hq]),
    show UpsGen.R insts = (recs insts).length from rfl,
    ← ZkFormal.Near.Render.flatMap_getD default (recs insts) (fun a => G (inst insts a.1) a.2)]
  simp only [recs, List.flatMap_assoc, List.flatMap_map]
  rw [ZkFormal.Near.Render.flatMap_getD default insts (fun I => (recsI I).flatMap (G I))]
  rfl

theorem rplRow_flat (I : UpsInst) : (recsI I).flatMap (rplRow I) = upsRplMsgs I := by
  simp only [recsI, List.flatMap_append, List.flatMap_map, upsRplMsgs]
  rw [ZkFormal.Near.Render.flatMap_nil' (l := List.range (L I)) (f := fun a => rplRow I (RK.v a)) (fun p _ => rfl)]
  simp only [List.flatMap_assoc, List.flatMap_map]
  rw [show List.range 4 = [0, 1, 2, 3] from rfl]
  simp only [List.flatMap_cons, List.flatMap_nil, rplRow, ite_true, List.append_nil, List.nil_append,
    show (1 = 0) = False by decide, show (2 = 0) = False by decide, show (3 = 0) = False by decide, if_false,
    List.singleton_append, List.cons.injEq, true_and]
  apply ZkFormal.Near.Render.flatMap_congr'
  intro k _
  generalize (part I k).q.length = n
  cases n with
  | zero => simp
  | succ n =>
    rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map,
      ZkFormal.Near.Render.flatMap_nil' (fun p _ => by simp [rplRow])]
    by_cases hu : upperB (part I k) = true <;> simp [rplRow, hu]

theorem rplvRow_flat (I : UpsInst) : (recsI I).flatMap (rplvRow I) = upsRplvMsgs I := by
  simp only [recsI, List.flatMap_append, List.flatMap_map]
  rw [ZkFormal.Near.Render.flatMap_nil' (l := List.range (L I)) (f := fun a => rplvRow I (RK.v a)) (fun p _ => rfl),
    ZkFormal.Near.Render.flatMap_nil' (f := rplvRow I) (fun r hr => by
      simp only [List.mem_flatMap, List.mem_map] at hr
      obtain ⟨k, _, p, _, rfl⟩ := hr; rfl)]
  rw [show List.range 4 = [0, 1, 2, 3] from rfl]
  simp [rplvRow]

/-- **`RPL` sends of the honest `upsA7` trace.** -/
theorem ups_rpl_sends (insts : List UpsInst) (h : UpsRenderOk insts) (pub : List Fp) :
    (traceTraffic UnfoldA7.Ups.interactions (upsA7Trace insts T_UPS) T_UPS pub).sends B_RPL =
      insts.flatMap upsRplMsgs := by
  rw [ups_sends_of_rows insts h pub B_RPL rplRow (ups_rpl_row insts pub)]
  exact ZkFormal.Near.Render.flatMap_congr' (fun I _ => rplRow_flat I)

/-- **`RPLV` sends of the honest `upsA7` trace.** -/
theorem ups_rplv_sends (insts : List UpsInst) (h : UpsRenderOk insts) (pub : List Fp) :
    (traceTraffic UnfoldA7.Ups.interactions (upsA7Trace insts T_UPS) T_UPS pub).sends B_RPLV =
      insts.flatMap upsRplvMsgs := by
  rw [ups_sends_of_rows insts h pub B_RPLV rplvRow (ups_rplv_row insts pub)]
  exact ZkFormal.Near.Render.flatMap_congr' (fun I _ => rplvRow_flat I)

/-- `upsA7` receives nothing on its appended interactions. -/
theorem ups_recvs (insts : List UpsInst) (pub : List Fp) (b : Nat) :
    (traceTraffic UnfoldA7.Ups.interactions (upsA7Trace insts T_UPS) T_UPS pub).recvs b = [] := by
  simp only [traceTraffic]
  apply ZkFormal.Near.Render.flatMap_nil'
  intro q _
  simp [rowTraffic, UnfoldA7.Ups.interactions, Dsl.send]

theorem vbqb_row (insts : List UpsInst) (q : Nat) (hq : q < (upsTraceAligned insts).height T_UPS) :
    (upsTraceAligned insts).cell T_UPS q ZkFormal.NearV3.UpsV3.vb +
        (upsTraceAligned insts).cell T_UPS q ZkFormal.NearV3.UpsV3.qb =
      Fp.ofNat (if q < UpsGen.R insts then sRow ((recs insts).getD q default).2 else 0) := by
  rw [ups_base_cell insts q _ hq (by decide), ups_base_cell insts q _ hq (by decide)]
  have o1 : ((1 : Int) : Fp) = 1 := by decide
  have o0 : ((0 : Int) : Fp) = 0 := by decide
  by_cases hR : q < UpsGen.R insts
  · simp only [UpsGen.cell, hR, if_true]
    generalize (recs insts).getD q default = a
    obtain ⟨i, rk⟩ := a
    cases rk with
    | w t =>
      rw [show rowCell insts q (i, .w t) ZkFormal.NearV3.UpsV3.vb = 0 from rfl,
        show rowCell insts q (i, .w t) ZkFormal.NearV3.UpsV3.qb = 0 from rfl]; simp only [sRow]; decide
    | v p =>
      rw [show rowCell insts q (i, .v p) ZkFormal.NearV3.UpsV3.vb = 1 from rfl,
        show rowCell insts q (i, .v p) ZkFormal.NearV3.UpsV3.qb = 0 from rfl]; simp only [sRow]; decide
    | q k p =>
      rw [show rowCell insts q (i, .q k p) ZkFormal.NearV3.UpsV3.vb = 0 from rfl,
        show rowCell insts q (i, .q k p) ZkFormal.NearV3.UpsV3.qb = 1 from rfl]; simp only [sRow]; decide
  · simp only [UpsGen.cell, hR, if_false]; decide

theorem sum_flatMap_nat {α : Type} (l : List α) (f : α → List Nat) :
    (l.flatMap f).sum = (l.map fun x => (f x).sum).sum := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [List.flatMap_cons, List.sum_append, ih]

theorem sum_map_zero {α : Type} (l : List α) (f : α → Nat) (h : ∀ x ∈ l, f x = 0) : (l.map f).sum = 0 := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [List.map_cons, List.sum_cons, h x (by simp), ih (fun y hy => h y (by simp [hy]))]

theorem sum_map_one {α : Type} (l : List α) : (l.map fun _ => 1).sum = l.length := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [List.map_cons, List.sum_cons, ih, List.length_cons]; omega

theorem sum_le_sum_of_le {α : Type} {l : List α} {f g : α → Nat} (h : ∀ x ∈ l, f x ≤ g x) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons]
    have := h x (by simp); have := ih (fun y hy => h y (by simp [hy])); omega

theorem sum_le_sum_of_le' {α : Type} {l : List α} {f g : α → Nat} (h : ∀ x ∈ l, f x ≤ g x) :
    (l.map f).sum ≤ (l.map g).sum := sum_le_sum_of_le h

theorem sRow_flat (I : UpsInst) :
    ((recsI I).map sRow).sum = L I + ((List.range (nQ I)).map fun k => (part I k).q.length).sum := by
  simp only [recsI, List.map_append, List.sum_append, List.map_map, List.map_flatMap]
  rw [show List.range 4 = [0, 1, 2, 3] from rfl, sum_flatMap_nat]
  have hv : ((List.range (L I)).map (sRow ∘ RK.v)).sum = L I := by
    rw [show (sRow ∘ RK.v) = fun _ => 1 from rfl, sum_map_one, List.length_range]
  have hq : ∀ k, ((List.range (part I k).q.length).map (sRow ∘ RK.q k)).sum = (part I k).q.length := by
    intro k; rw [show (sRow ∘ RK.q k) = fun _ => 1 from rfl, sum_map_one, List.length_range]
  rw [hv, List.map_congr_left (fun k _ => hq k)]
  rw [show (List.map (sRow ∘ RK.w) [0, 1, 2, 3]).sum = 0 from rfl, Nat.zero_add]

/-- The value of `s` on the last row: the A7 ups total. -/
theorem ups_s_last (insts : List UpsInst) (h : UpsRenderOk insts) :
    prefixF (fun r => (upsTraceAligned insts).cell T_UPS r ZkFormal.NearV3.UpsV3.vb +
        (upsTraceAligned insts).cell T_UPS r ZkFormal.NearV3.UpsV3.qb)
      ((upsTraceAligned insts).height T_UPS - 1) = Fp.ofNat (upsA7Total insts) := by
  have hH := ups_height insts h
  rw [prefixF_eq, List.map_congr_left (g := fun q => Fp.ofNat (if q < UpsGen.R insts then
      sRow ((recs insts).getD q default).2 else 0))
    (fun q hq => vbqb_row insts q (by have := List.mem_range.1 hq; omega))]
  rw [show (List.range ((upsTraceAligned insts).height T_UPS - 1)).map (fun q => Fp.ofNat (if q < UpsGen.R insts then
      sRow ((recs insts).getD q default).2 else 0)) = ((List.range ((upsTraceAligned insts).height T_UPS - 1)).map
      (fun q => if q < UpsGen.R insts then sRow ((recs insts).getD q default).2 else 0)).map Fp.ofNat by
    simp only [List.map_map]; rfl, foldr_ofNat]
  congr 1
  rw [ZkFormal.Near.Render.range_split (show UpsGen.R insts ≤ (upsTraceAligned insts).height T_UPS - 1 by omega),
    List.map_append, List.sum_append, List.map_map]
  have hz : ((List.range ((upsTraceAligned insts).height T_UPS - 1 - UpsGen.R insts)).map
      ((fun q => if q < UpsGen.R insts then sRow ((recs insts).getD q default).2 else 0) ∘ (UpsGen.R insts + ·))).sum = 0 := by
    apply sum_map_zero; intro y _
    simp only [Function.comp_def]; simp only [show ¬ (UpsGen.R insts + y < UpsGen.R insts) by omega, if_false]
  rw [hz, Nat.add_zero,
    List.map_congr_left (g := fun q => sRow ((recs insts).getD q default).2) (fun q hq => by
      simp [List.mem_range.1 hq]),
    show UpsGen.R insts = (recs insts).length from rfl,
    ZkFormal.NearV3.Render.ValGen.map_getD default (fun a : Nat × RK => sRow a.2) (recs insts)]
  simp only [recs, List.map_flatMap, List.map_map]
  rw [sum_flatMap_nat]
  simp only [upsA7Total]
  rw [← ZkFormal.NearV3.Render.ValGen.map_getD default
    (fun I => L I + ((List.range (nQ I)).map fun k => (part I k).q.length).sum) insts]
  congr 1
  apply List.map_congr_left
  intro i _
  rw [← sRow_flat]
  simp [Function.comp_def, inst]

theorem upsA7Total_le (insts : List UpsInst) : upsA7Total insts ≤ UpsGen.R insts := by
  have e : UpsGen.R insts = ((recs insts).map fun _ => 1).sum := by rw [sum_map_one]; rfl
  rw [e]
  simp only [recs, List.map_flatMap, List.map_map, sum_flatMap_nat, upsA7Total]
  rw [← ZkFormal.NearV3.Render.ValGen.map_getD default
    (fun I => L I + ((List.range (nQ I)).map fun k => (part I k).q.length).sum) insts]
  apply sum_le_sum_of_le
  intro i _
  rw [← sRow_flat]
  show ((recsI (insts.getD i default)).map sRow).sum ≤ ((recsI (insts.getD i default)).map ((fun _ => 1) ∘ _)).sum
  apply sum_le_sum_of_le'
  intro r _
  cases r <;> simp [sRow]

/-- **`SIZE` sends of the honest `upsA7` trace**: exactly `[5, upsA7Total insts]`. -/
theorem ups_size_sends (insts : List UpsInst) (h : UpsRenderOk insts) (pub : List Fp) :
    (traceTraffic UnfoldA7.Ups.interactions (upsA7Trace insts T_UPS) T_UPS pub).sends B_SIZE =
      [[5, upsA7Total insts]] := by
  have hH := ups_height insts h
  have hlt : upsA7Total insts < P := by
    have := upsA7Total_le insts
    have := h.ok.cap
    have : (2 : Nat) ^ 22 < P := by decide
    omega
  have hrow : ∀ q, q < (upsTraceAligned insts).height T_UPS →
      (rowTraffic UnfoldA7.Ups.interactions (upsA7Trace insts T_UPS) T_UPS q pub B_SIZE true).map
        (List.map Fp.toNat) =
      if q + 1 = (upsTraceAligned insts).height T_UPS then [[5, upsA7Total insts]] else [] := by
    intro q hq
    obtain ⟨-, -, cS⟩ := ups_cells insts q hq
    have he : (upsA7Trace insts T_UPS).height T_UPS = (upsTraceAligned insts).height T_UPS := rfl
    by_cases hl : q + 1 = (upsTraceAligned insts).height T_UPS
    · obtain rfl : q = (upsTraceAligned insts).height T_UPS - 1 := by omega
      simp [rowTraffic, UnfoldA7.Ups.interactions, Dsl.send, B_RPL, B_RPLV, B_SIZE, Interaction.multNat,
        Interaction.multNat.go, Interaction.msgVal, hl, he, cS, ups_s_last insts h, Fp.toNat_ofNat,
        Nat.mod_eq_of_lt hlt]
      rfl
    · have z : ((0 : Fp) = 1) = False := by decide
      simp [rowTraffic, UnfoldA7.Ups.interactions, Dsl.send, B_RPL, B_RPLV, B_SIZE, Interaction.multNat,
        Interaction.multNat.go, hl, he, z]
  simp only [traceTraffic]
  rw [show (upsA7Trace insts T_UPS).height T_UPS = (upsTraceAligned insts).height T_UPS from rfl,
    ZkFormal.Near.Render.flatMap_congr' (fun q hq => hrow q (List.mem_range.1 hq))]
  obtain ⟨m, hm⟩ : ∃ m, (upsTraceAligned insts).height T_UPS = m + 1 := ⟨_, (Nat.succ_pred_eq_of_pos (by omega)).symm⟩
  rw [hm, List.range_succ, List.flatMap_append,
    ZkFormal.Near.Render.flatMap_nil' (fun q hq => by have := List.mem_range.1 hq; simp; omega)]
  simp

end Ups

end ZkFormal.NearV3.Assembly.TrieA7
