import ZkFormal.NearV3.Rcpt.Candidates.DedupTableLocal
import ZkFormal.NearV3.Rcpt.Candidates.DedupTrafficProof
import ZkFormal.NearV3.Rcpt.Candidates.DedupTableFacts
import ZkFormal.NearV3.Rcpt.Tables.SrcpDD
import ZkFormal.NearV3.Render.ColAgree
import ZkFormal.NearV3.Rcpt.Render.SizeRender
import ZkFormal.NearV3.Render.Padded

/-!
# ZkFormal.NearV3.Render.PaddedSrcpDD — honest aligned render of table 20 (`SrcpDD.table`)

The rows are `DedupRender.cell bs rep` (the dedup candidate renderer: computed blocks as in
`srcpV3`, a `dup` occurrence as one reference root row, the repetition bit in column 56) plus
the A10 slack bits `db_e` (columns 57…62) = the bits of `DP0 − |path|` on root rows.  The
hypotheses are the renderer's `TableFacts bs rep`, the row bound `R bs ≤ 2^22` and A10 for
every block.  Height `2^padLog22 (logOf R)` (cap 22, `log ≡ 1 mod 3`).
-/

namespace ZkFormal.NearV3.Render

open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Air ZkFormal.Algebra ZkFormal.Size
open ZkFormal.NearV3.Rcpt.Candidates

namespace SrcpDDGen

/-- The depth slack of a row: `DP0 − |path|` on a block's root row, else `0`. -/
def depthVal (bs : List SrcpB) (pos : Nat) : Nat :=
  if pos < DedupRender.R bs then
    match (DedupRender.recs bs).getD pos default with
    | (i, .root) => SrcpV3.DP0 - (bs.getD i default).path.length
    | _ => 0
  else 0

/-- The honest cells of table 20. -/
def cell (bs : List SrcpB) (rep : Nat → Bool) (pos x : Nat) : Nat :=
  if x < DedupRender.width then DedupRender.cell bs rep pos x
  else if x < SrcpDD.width then (depthVal bs pos / 2 ^ (x - DedupRender.width)) % 2 else 0

def trace (log : Nat) (f : Nat → Nat → Nat) : Trace Fp :=
  ⟨fun _ => log, fun _ r c => Fp.ofNat (f r c)⟩

theorem recs_fst_lt (bs : List SrcpB) {pos : Nat} (hp : pos < DedupRender.R bs) :
    ((DedupRender.recs bs).getD pos default).1 < bs.length := by
  have hm : (DedupRender.recs bs).getD pos default ∈ DedupRender.recs bs := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by unfold DedupRender.R at hp; exact hp)]
    exact List.getElem_mem _
  simp only [DedupRender.recs, List.mem_flatMap, List.mem_range, List.mem_map] at hm
  obtain ⟨i, hi, k, -, he⟩ := hm
  rw [show (DedupRender.recs bs).getD pos default = (i, k) from he.symm]; exact hi

/-- A generated row with `rt = 1` and `dup = 0` is a computed block's root row. -/
theorem computed_root (bs : List SrcpB) (rep : Nat → Bool) {pos : Nat}
    (h1 : DedupRender.cell bs rep pos SrcpV3.rt = 1) :
    ∃ i, i < bs.length ∧ DedupRender.cell bs rep pos SrcpV3.dup = (bs.getD i default).dup.toNat ∧
      DedupRender.cell bs rep pos SrcpV3.q = (bs.getD i default).ql - 1 ∧
      ((bs.getD i default).dup = false →
        DedupRender.cell bs rep pos SrcpV3.qe = (bs.getD i default).qe) ∧
      depthVal bs pos = SrcpV3.DP0 - (bs.getD i default).path.length := by
  unfold DedupRender.cell at h1
  split at h1
  · rename_i hp
    have hi := recs_fst_lt bs hp
    generalize hr : (DedupRender.recs bs).getD pos default = p at h1 hi
    obtain ⟨i, k⟩ := p
    cases k with
    | root =>
      refine ⟨i, hi, ?_, ?_, ?_, ?_⟩
      · unfold DedupRender.cell; rw [if_pos hp, hr]
        cases hd : (bs.getD i default).dup <;>
          (have hd' := hd; rw [List.getD_eq_getElem?_getD] at hd';
           simp [DedupRender.rowFrame, DedupRender.frame, SrcpGen.rootFrame, SrcpGen.Frame.cell, SrcpV3.dup,
            hd', List.getD_eq_getElem?_getD])
      · unfold DedupRender.cell; rw [if_pos hp, hr]
        cases hd : (bs.getD i default).dup <;>
          (have hd' := hd; rw [List.getD_eq_getElem?_getD] at hd';
           simp [DedupRender.rowFrame, DedupRender.frame, SrcpGen.rootFrame, SrcpGen.Frame.cell, SrcpV3.q,
            hd', List.getD_eq_getElem?_getD])
      · intro hd
        have hd' := hd; rw [List.getD_eq_getElem?_getD] at hd'
        unfold DedupRender.cell; rw [if_pos hp, hr]
        simp [DedupRender.rowFrame, DedupRender.frame, SrcpGen.rootFrame, SrcpGen.Frame.cell, SrcpV3.qe, hd',
          List.getD_eq_getElem?_getD]
      · unfold depthVal; rw [if_pos hp, hr]
    | leaf p =>
      simp [DedupRender.rowFrame, DedupRender.frame, SrcpGen.leafFrame, SrcpGen.Frame.cell, SrcpV3.rt] at h1
    | path a o =>
      simp [DedupRender.rowFrame, DedupRender.frame, SrcpGen.pathFrame, SrcpGen.Frame.cell, SrcpV3.rt] at h1
  · simp [SrcpV3.rt, SrcpV3.sz] at h1

/-- The A10 constraints hold on the honest rows. -/
theorem depth_constraints {bs : List SrcpB} {rep : Nat → Bool} (h : DedupRender.TableFacts bs rep)
    (hd : ∀ B ∈ bs, B.path.length ≤ SrcpV3.DP0)
    {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (hc : ∀ r, r < tr.height t → ∀ x, tr.cell t r x = Fp.ofNat (cell bs rep r x)) :
    ∀ r, r < tr.height t → ∀ e ∈ SrcpDD.depthConstraints, e.eval tr t r pub = 0 := by
  intro r hr e he
  have hbit : ∀ b, b < 6 → tr.cell t r (SrcpDD.db b) = Fp.ofNat ((depthVal bs r / 2 ^ b) % 2) := by
    intro b hb
    rw [hc r hr]
    simp only [cell, SrcpDD.db, SrcpDD.width, DedupRender.width, show ¬ 57 + b < 57 by omega,
      show 57 + b < 63 by omega, if_false, if_true, Nat.add_sub_cancel_left]
  have hbool : ∀ b, b < 6 → tr.cell t r (SrcpDD.db (0 + b)) = 0 ∨ tr.cell t r (SrcpDD.db (0 + b)) = 1 := by
    intro b hb
    rw [Nat.zero_add, hbit b hb]
    rcases Nat.mod_two_eq_zero_or_one (depthVal bs r / 2 ^ b) with h2 | h2 <;> rw [h2]
    · exact Or.inl rfl
    · exact Or.inr rfl
  simp only [SrcpDD.depthConstraints, List.mem_append, List.mem_map, List.mem_range,
    List.mem_singleton] at he
  rcases he with ⟨b, hb, rfl⟩ | rfl
  · have := hbool b hb
    rw [Nat.zero_add] at this
    simp only [eval_bool, eval_c]
    rcases this with h0 | h0 <;> rw [h0] <;> grind
  · have hlow : ∀ x, x < DedupRender.width → tr.cell t r x = Fp.ofNat (DedupRender.cell bs rep r x) := by
      intro x hx; rw [hc r hr]; unfold SrcpDDGen.cell; rw [if_pos hx]
    have hrt := hlow SrcpV3.rt (by decide)
    have hdp := hlow SrcpV3.dup (by decide)
    have hb1 := DedupRender.cell_bool_bound bs rep r SrcpV3.rt (by decide)
    simp only [DedupTable.computedRoot, eval_mul, eval_c, eval_sub, eval_k, hrt, hdp]
    rcases (show DedupRender.cell bs rep r SrcpV3.rt = 0 ∨ DedupRender.cell bs rep r SrcpV3.rt = 1 by omega)
      with h0 | h1
    · have hd0 : DedupRender.cell bs rep r SrcpV3.dup = 0 := by
        have hb2 := DedupRender.cell_bool_bound bs rep r SrcpV3.dup (by decide)
        rcases (show DedupRender.cell bs rep r SrcpV3.dup = 0 ∨ DedupRender.cell bs rep r SrcpV3.dup = 1 by omega)
          with hz | h1'
        · exact hz
        exfalso
        -- a `dup` cell is only set on root rows
        unfold DedupRender.cell at h0 h1'
        split at h1'
        · rename_i hp
          rw [if_pos hp] at h0
          generalize (DedupRender.recs bs).getD r default = p at h0 h1'
          obtain ⟨i, k⟩ := p
          cases k <;> cases hd : (bs.getD i default).dup <;>
            simp_all [DedupRender.rowFrame, DedupRender.frame, SrcpGen.rootFrame, SrcpGen.leafFrame,
              SrcpGen.pathFrame, SrcpGen.Frame.cell, SrcpV3.rt, SrcpV3.dup]
        · simp [SrcpV3.dup, SrcpV3.sz] at h1'
      rw [h0, hd0, show (Fp.ofNat 0 - Fp.ofNat 0 : Fp) = 0 by grind, Lean.Grind.Semiring.zero_mul]
    · obtain ⟨i, hi, hdup, hq, hqe, hdv⟩ := computed_root bs rep h1
      have hB : bs.getD i default ∈ bs := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; exact List.getElem_mem _
      cases hBd : (bs.getD i default).dup
      · have hf := (h.block _ hB).counter
        have hlen := hd _ hB
        have hqe' := hqe hBd
        rw [hBd] at hdup
        generalize bs.getD i default = B at hq hqe' hdv hB hlen hf hBd
        have hbits : SrcpDD.depthBits.eval tr t r pub = ((SrcpV3.DP0 - B.path.length : Nat) : Fp) := by
          rw [show SrcpDD.depthBits = Dsl.bits (fun e => Dsl.c (SrcpDD.db e)) 0 6 from rfl,
            eval_bits tr t r pub SrcpDD.db 0 6 hbool]
          congr 1
          rw [SizeRender.bitsVal_congr _ (fun e => (depthVal bs r / 2 ^ e) % 2) 6 (fun e he => by
              simp only [cv, hbit e he, Fp.toNat_ofNat]
              exact Nat.mod_eq_of_lt (by
                have := Nat.mod_lt (depthVal bs r / 2 ^ e) (show 2 > 0 by decide)
                unfold ZkFormal.Algebra.P; omega)),
            SizeRender.bitsVal_bits, hdv]
          exact Nat.mod_eq_of_lt (by unfold SrcpV3.DP0; omega)
        have cq : tr.cell t r SrcpV3.q = ((B.ql - 1 : Nat) : Fp) := by
          rw [hlow _ (by decide), hq]; rfl
        have cqe : tr.cell t r SrcpV3.qe = ((B.ql + B.path.length : Nat) : Fp) := by
          rw [hlow _ (by decide), hqe', hf.qe]; rfl
        have hql := hf.qpos
        rw [h1, hdup, hbits, cq, cqe]
        have e1 := congrArg (fun n : Nat => (n : Fp))
          (show (SrcpV3.DP0 - B.path.length) + B.path.length = SrcpV3.DP0 by omega)
        have e2 := congrArg (fun n : Nat => (n : Fp)) (show (B.ql - 1) + 1 = B.ql by omega)
        simp only [natCast_add] at e1 e2
        rw [natCast_add]
        have : ((1 : Nat) : Fp) = 1 := rfl
        simp only [Bool.toNat_false]
        grind
      · rw [hBd] at hdup
        rw [h1, hdup, show (Fp.ofNat 1 - Fp.ofNat (Bool.toNat true) : Fp) = 0 by grind,
          Lean.Grind.Semiring.zero_mul]

end SrcpDDGen

/-- Every `DedupTable` expression reads only its 57 columns. -/
theorem dd_cols : ∀ e ∈ (DedupTable.table 24).exprs, e.colBound ≤ DedupRender.width := by
  intro e he
  exact of_decide_eq_true (List.all_eq_true.mp DedupTable.expressions_width e he)

theorem dd_icols : ∀ i ∈ DedupTable.interactions, ∀ e ∈ i.mult ++ i.msg, e.colBound ≤ DedupRender.width :=
  fun i hi e he => dd_cols e (List.mem_append_right _ (List.mem_flatMap.2 ⟨i, hi, he⟩))

def srcpDDTrace (bs : List SrcpB) (rep : Nat → Bool) : Trace Fp :=
  SrcpDDGen.trace (padLog22 (logOf (DedupRender.R bs))) (SrcpDDGen.cell bs rep)

/-- **Table 20 completeness** at the aligned height, with exactly the dedup renderer's traffic. -/
theorem srcpDD_aligned_complete (bs : List SrcpB) (rep : Nat → Bool) (h : DedupRender.TableFacts bs rep)
    (hR : DedupRender.R bs ≤ 2 ^ 22) (hd : ∀ B ∈ bs, B.path.length ≤ NearSpecV3.Dp0)
    (hl : ∀ B ∈ bs, B.root.length = 32 ∧ B.leaf.length = 32 ∧
      ∀ it ∈ B.path, it.sib.length = 32 ∧ it.acc.length = 32)
    (t : Nat) (pub : List Fp) :
    TableLocal SrcpDD.table (srcpDDTrace bs rep) t pub ∧
    TableTraffic DedupTable.interactions (srcpDDTrace bs rep) t pub (DedupRender.traffic bs rep) ∧
    (srcpDDTrace bs rep).log t % 3 = 1 := by
  have hh := padded_log_fits (DedupRender.R bs) hR
  let trB := SrcpDDGen.trace (padLog22 (logOf (DedupRender.R bs))) (DedupRender.cell bs rep)
  have hlog : (srcpDDTrace bs rep).log t = trB.log t := rfl
  have hHB : DedupRender.R bs ≤ trB.height t := hh.1
  have hcB : ∀ r, r < trB.height t → ∀ x, trB.cell t r x = Fp.ofNat (DedupRender.cell bs rep r x) :=
    fun _ _ _ => rfl
  have hLB : TableLocal (DedupTable.table 24) trB t pub :=
    DedupRender.table_local h hh.2.1 (by have := hh.2.2.1; change padLog22 _ ≤ 24; omega) hHB hcB
  have hTB := DedupRender.table_traffic h.nonempty rep hl hHB hcB (pub := pub)
  have hcols : ∀ r c, c < DedupRender.width → (srcpDDTrace bs rep).cell t r c = trB.cell t r c := by
    intro r c hc
    simp [srcpDDTrace, trB, SrcpDDGen.trace, SrcpDDGen.cell, hc]
  have hL := tableLocal_congr_cols hlog hcols dd_cols hLB
  refine ⟨SrcpDD.local_of_dedup hL (by change padLog22 _ ≤ SrcpV3.maxLog; unfold SrcpV3.maxLog; exact hh.2.2.1)
    (SrcpDDGen.depth_constraints h hd (fun _ _ _ => rfl)),
    tableTraffic_congr_cols hlog hcols dd_icols hTB, hh.2.2.2⟩

end ZkFormal.NearV3.Render
