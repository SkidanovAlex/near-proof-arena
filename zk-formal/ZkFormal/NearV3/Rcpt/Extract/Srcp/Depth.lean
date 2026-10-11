import ZkFormal.NearV3.Rcpt.Extract.Srcp.Proof
import ZkFormal.NearV3.Rcpt.Tables.SrcpD
import NearSpecV3.ChunkValidationV0a

/-!
# ZkFormal.NearV3.Rcpt.Extract.Srcp.Depth — the `srcpV3` view with the A10 depth bound

On `SrcpV3.tableD` every extracted source block has at most `Dp0 = 32` path items: the root
row's slack `DP0 − (qe − q − 1)` is a 6-bit value, `q + 1 = ql` is the leaf message and
`qe = ql + |path|` (`block_wf`), so `DP0 − |path| ∈ [0, 64)` in the field, which forces
`|path| ≤ DP0` because `|path| ≤ 2^22/64` is far below `P`.
-/

namespace ZkFormal.NearV3.SrcpProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.SrcpV3

theorem DP0_eq : SrcpV3.DP0 = NearSpecV3.Dp0 := rfl

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

theorem depth_bools (hL : TableLocal SrcpV3.tableD tr tt pub) {r : Nat} (hr : r < tr.height tt)
    (e : Nat) (he : e < 6) : tr.cell tt r (db e) = 0 ∨ tr.cell tt r (db e) = 1 := by
  have h := hL.constr r hr (bool (c (db e))) (List.mem_append_right _
    (List.mem_append_left _ (List.mem_map.2 ⟨e, List.mem_range.2 he, rfl⟩)))
  simp only [eval_bool, eval_c] at h
  exact bool_cases h

/-- **One block's depth bound.** -/
theorem block_depth (hL : TableLocal SrcpV3.tableD tr tt pub) {s m : Nat}
    (hs : s < tr.height tt) (ht : tr.cell tt s rt = 1) (hm : PathRun tr tt (s + 32) m) :
    m ≤ DP0 := by
  have hB := local_base hL
  have hw := block_wf hB hs ht hm
  have hqe : (tr.cell tt s qe).toNat = (tr.cell tt (s + 1) q).toNat + m := by
    have := hw.root.1
    simpa [blockOf, SrcpB.lastQ, pathItems] using this
  have hbd := hm.bound
  have hH : tr.height tt ≤ 2 ^ 22 := by
    have := hL.log_le; unfold Trace.height
    exact Nat.pow_le_pow_right (by decide) (by simpa [tableD, maxLog] using this)
  have hq1 := (afterRoot hB (r := s) (by omega) ht).2.2.2.1
  -- the depth constraint on the root row
  have hc := hL.constr s hs (.mul (c rt) (sub depthBits (sub (k DP0) (sub (sub (c qe) (c q)) (k 1)))))
    (List.mem_append_right _ (List.mem_append_right _ (by simp)))
  have hbits : depthBits.eval tr tt s pub = ((bitsVal (fun b => cv tr tt s (db b)) 0 6 : Nat) : Fp) :=
    eval_bits tr tt s pub db 0 6 (fun b hb => depth_bools hL hs (0 + b) (by omega))
  have hlt : bitsVal (fun b => cv tr tt s (db b)) 0 6 < 2 ^ 6 :=
    bitsVal_lt _ 0 6 (fun b hb => cv_bool (depth_bools hL hs (0 + b) (by omega)))
  simp only [eval_mul, eval_c, eval_sub, eval_k, hbits, ht] at hc
  generalize bitsVal (fun b => cv tr tt s (db b)) 0 6 = d at hc hlt
  have eqe : tr.cell tt s qe = (((tr.cell tt (s + 1) q).toNat + m : Nat) : Fp) := by
    rw [← hqe]; exact (Fp.ofNat_toNat _).symm
  have eq1 : tr.cell tt (s + 1) q = (((tr.cell tt (s + 1) q).toNat : Nat) : Fp) :=
    (Fp.ofNat_toNat _).symm
  rw [hq1] at eq1 eqe
  generalize (tr.cell tt s q + 1).toNat = a at eq1 eqe
  have key : ((d + m : Nat) : Fp) = ((DP0 : Nat) : Fp) := by
    rw [natCast_add]
    have e2 : tr.cell tt s qe = (a : Fp) + (m : Fp) := by rw [eqe, natCast_add]
    rw [e2] at hc
    have e3 : tr.cell tt s q = (a : Fp) - 1 := by rw [← eq1]; grind
    rw [e3] at hc
    grind
  have hm64 : 64 * m ≤ 2 ^ 22 := by omega
  have := ofNat_inj (a := d + m) (b := DP0) (by unfold P; omega) (by unfold DP0 P; omega) key
  unfold DP0 at this ⊢; omega

/-- Every block of a chain is within the depth budget. -/
theorem BlockChain.depth (hL : TableLocal SrcpV3.tableD tr tt pub) {s e : Nat} {bs : List SrcpB}
    (hc : BlockChain tr tt s bs e) : ∀ B ∈ bs, B.path.length ≤ DP0 := by
  induction hc with
  | last s m hs ht hm hp =>
    intro B hB
    simp only [List.mem_singleton] at hB; subst hB
    simpa [blockOf, pathItems] using block_depth hL hs ht hm
  | cons s m hs ht hm bs e hc ih =>
    intro B hB
    rcases List.mem_cons.1 hB with rfl | hB
    · simpa [blockOf, pathItems] using block_depth hL hs ht hm
    · exact ih B hB

end ZkFormal.NearV3.SrcpProof

namespace ZkFormal.NearV3

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

/-- **The `srcpV3` view with A10** (`SrcpV3.tableD`, `nearAirV3` table 20): the `srcp_view`
records, and every source block's path has at most `Dp0` items. -/
theorem srcpD_view {tr : Trace Fp} {pub : List Fp} {tt : Nat}
    (hL : TableLocal SrcpV3.tableD tr tt pub) :
    ∃ bs, SrcpWf bs ∧ (∀ B ∈ bs, B.path.length ≤ NearSpecV3.Dp0) ∧
      TableTraffic SrcpV3.interactions tr tt pub (srcpTraffic bs) := by
  have hB := SrcpV3.local_base hL
  have hH : 0 < tr.height tt := by unfold Trace.height; exact Nat.two_pow_pos _
  obtain ⟨bs, e, hc⟩ := SrcpProof.blocks_from hB hH (SrcpProof.row0 hB hH).1
  exact ⟨bs, SrcpProof.BlockChain.wf hB hc, SrcpProof.BlockChain.depth hL hc,
    SrcpProof.BlockChain.table_traffic hB hc⟩

end ZkFormal.NearV3
