import ZkFormal.NearV3.Rcpt.Tables.SrcpDD
import ZkFormal.NearV3.Rcpt.Candidates.DedupExtractProof
import ZkFormal.NearV3.Rcpt.Candidates.DedupPublicViews
import ZkFormal.NearV3.Rcpt.Candidates.DedupPayloadIsolation
import ZkFormal.NearV3.Public.ReceiptIndex
import NearSpecV3.ChunkValidationV0a

/-!
# ZkFormal.NearV3.Rcpt.Extract.Srcp.DDView — the view of table 20 (`SrcpDD.table`)

`SrcpDD.table` is `DedupTable` plus the A10 depth bits (`Rcpt/Tables/SrcpDD.lean`).  The view
is the dedup extraction (`DedupProof.extract_blocks`, a `BlockChain` of computed blocks and
one-row skipped `dup` references) with the per-block repetition bits
`reps = (sourceViews …).map Prod.snd`, as records:

* `ddTraffic bs reps` — the exact traffic (`DedupRender.blockMsgs` per block, `SIZE (2, srcpSize bs)`);
* `DDWf bs reps` — numbering, the per-block shapes (`dup ⇒` empty one-row reference,
  else `BlockWf`), `rep ⇒ L = 12`, canonical public records, and **A10**: every block's path has
  `≤ Dp0` items (computed: the depth bits on the root row; skipped: no path).
-/

namespace ZkFormal.NearV3

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl
open ZkFormal.NearV3.Rcpt.Candidates

/-- Record traffic of table 20. -/
def ddTraffic (bs : List SrcpB) (reps : List Bool) : Traffic :=
  ⟨fun bb => if bb = B_SIZE then [[2, srcpSize bs]] else
      (bs.zip reps).flatMap fun v => DedupRender.blockMsgs v.1 v.2 bb true,
   fun bb => if bb = B_SIZE then [] else
      (bs.zip reps).flatMap fun v => DedupRender.blockMsgs v.1 v.2 bb false⟩

/-- Record well-formedness of table 20. -/
structure DDWf (bs : List SrcpB) (reps : List Bool) : Prop where
  len : reps.length = bs.length
  nonempty : bs ≠ []
  j : ∀ k (h : k < bs.length), bs[k].j = k
  q0 : ∀ h : 0 < bs.length, bs[0].ql = 1
  qnext : ∀ k (h : k + 1 < bs.length), bs[k + 1].ql = bs[k].qe + 1
  block : ∀ B ∈ bs, if B.dup then B.L = 12 ∧ B.path = [] ∧ B.le = 0 ∧ B.qe + 1 = B.ql
    else DedupProof.BlockWf B
  rep : ∀ v ∈ bs.zip reps, v.2 = true → v.1.L = 12
  canon : ∀ v ∈ bs.zip reps, ZkFormal.Near.Link.Canon (SourcePublic.viewRecord v.1 v.2)
  /-- A10 -/
  depth : ∀ B ∈ bs, B.path.length ≤ NearSpecV3.Dp0
  rows : DedupRender.R bs ≤ 2 ^ 22
  /-- the SHA-linker facts of the dedup chain (message ids canonical) -/
  payload : DedupProof.PayloadWf bs

namespace DDView

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

theorem zip_views (s : Nat) (bs : List SrcpB) :
    bs.zip ((DedupProof.sourceViews tr tt s bs).map Prod.snd) = DedupProof.sourceViews tr tt s bs := by
  induction bs generalizing s with
  | nil => rfl
  | cons B bs ih => simp only [DedupProof.sourceViews, List.map_cons, List.zip_cons_cons, ih]

theorem chainMsgs_eq (s : Nat) (bs : List SrcpB) (bb : Nat) (sd : Bool) :
    DedupProof.chainMsgs tr tt s bs bb sd =
      (DedupProof.sourceViews tr tt s bs).flatMap fun v => DedupRender.blockMsgs v.1 v.2 bb sd := by
  induction bs generalizing s with
  | nil => rfl
  | cons B bs ih =>
    rw [DedupProof.chainMsgs, ih]
    simp only [DedupProof.sourceViews, List.flatMap_cons]

theorem sourceMsgs_eq (bs : List SrcpB) (bb : Nat) (sd : Bool) :
    DedupProof.sourceMsgs tr tt bs bb sd =
      (if sd then (ddTraffic bs ((DedupProof.sourceViews tr tt 0 bs).map Prod.snd)).sends bb
       else (ddTraffic bs ((DedupProof.sourceViews tr tt 0 bs).map Prod.snd)).recvs bb) := by
  unfold DedupProof.sourceMsgs ddTraffic
  by_cases hb : bb = B_SIZE
  · subst hb; cases sd <;> simp [srcpSize]
  · cases sd <;> simp only [hb, ite_false, Bool.false_eq_true, ite_true, zip_views, chainMsgs_eq]

/-- One computed block's depth bound (the root row's depth bits). -/
theorem block_depth (hL : TableLocal SrcpDD.table tr tt pub) {s m : Nat}
    (hs : s < tr.height tt) (ht : tr.cell tt s SrcpV3.rt = 1) (hd : tr.cell tt s SrcpV3.dup = 0)
    (hm : DedupProof.PathRun tr tt (s + 32) m) : m ≤ SrcpV3.DP0 := by
  have hB := SrcpDD.local_dedup hL
  have hw := DedupProof.block_wf hB hs ht hd hm
  have hqe : (tr.cell tt s SrcpV3.qe).toNat = (tr.cell tt (s + 1) SrcpV3.q).toNat + m := by
    have := hw.root.1
    simpa [DedupProof.blockOf, SrcpB.lastQ, DedupProof.pathItems] using this
  have hbd := hm.bound
  have hH : tr.height tt ≤ 2 ^ 22 := by
    have := hL.log_le; unfold Trace.height
    exact Nat.pow_le_pow_right (by decide) (by simpa [SrcpDD.table, SrcpV3.maxLog] using this)
  have hq1 := (DedupProof.computed_after_root hB (r := s) (by omega) ht hd).2.2.2
  have hbool : ∀ e, e < 6 → tr.cell tt s (SrcpDD.db (0 + e)) = 0 ∨ tr.cell tt s (SrcpDD.db (0 + e)) = 1 := by
    intro e he
    have h := hL.constr s hs (Dsl.bool (Dsl.c (SrcpDD.db (0 + e)))) (List.mem_append_right _
      (List.mem_append_left _ (List.mem_map.2 ⟨0 + e, List.mem_range.2 (by omega), rfl⟩)))
    simp only [eval_bool, eval_c] at h
    exact bool_cases h
  have hc := hL.constr s hs (.mul DedupTable.computedRoot (Dsl.sub SrcpDD.depthBits
      (Dsl.sub (Dsl.k SrcpV3.DP0) (Dsl.sub (Dsl.sub (Dsl.c SrcpV3.qe) (Dsl.c SrcpV3.q)) (Dsl.k 1)))))
    (List.mem_append_right _ (List.mem_append_right _ (by simp)))
  have hbits : SrcpDD.depthBits.eval tr tt s pub =
      ((bitsVal (fun b => cv tr tt s (SrcpDD.db b)) 0 6 : Nat) : Fp) :=
    eval_bits tr tt s pub SrcpDD.db 0 6 hbool
  have hlt : bitsVal (fun b => cv tr tt s (SrcpDD.db b)) 0 6 < 2 ^ 6 :=
    bitsVal_lt _ 0 6 (fun b hb => cv_bool (hbool b hb))
  simp only [DedupTable.computedRoot, eval_mul, eval_c, eval_sub, eval_k, hbits, ht, hd] at hc
  generalize bitsVal (fun b => cv tr tt s (SrcpDD.db b)) 0 6 = d at hc hlt
  have eqe : tr.cell tt s SrcpV3.qe = (((tr.cell tt (s + 1) SrcpV3.q).toNat + m : Nat) : Fp) := by
    rw [← hqe]; exact (Fp.ofNat_toNat _).symm
  have eq1 : tr.cell tt (s + 1) SrcpV3.q = (((tr.cell tt (s + 1) SrcpV3.q).toNat : Nat) : Fp) :=
    (Fp.ofNat_toNat _).symm
  rw [hq1] at eq1 eqe
  generalize (tr.cell tt s SrcpV3.q + 1).toNat = a at eq1 eqe
  have key : ((d + m : Nat) : Fp) = ((SrcpV3.DP0 : Nat) : Fp) := by
    rw [natCast_add]
    have e2 : tr.cell tt s SrcpV3.qe = (a : Fp) + (m : Fp) := by rw [eqe, natCast_add]
    rw [e2] at hc
    have e3 : tr.cell tt s SrcpV3.q = (a : Fp) - 1 := by rw [← eq1]; grind
    rw [e3] at hc
    grind
  have hm64 : 64 * m ≤ 2 ^ 22 := by omega
  have := ofNat_inj (a := d + m) (b := SrcpV3.DP0) (by unfold P; omega) (by unfold SrcpV3.DP0 P; omega) key
  unfold SrcpV3.DP0 at this ⊢; omega

theorem chain_depth (hL : TableLocal SrcpDD.table tr tt pub) {s e : Nat} {bs : List SrcpB}
    (hc : DedupProof.BlockChain tr tt s bs e) : ∀ B ∈ bs, B.path.length ≤ NearSpecV3.Dp0 := by
  have span : ∀ {s n : Nat} {B : SrcpB}, DedupProof.BlockSpan tr tt s B n →
      B.path.length ≤ NearSpecV3.Dp0 := by
    intro s n B h
    cases h with
    | computed m hs ht hd hm =>
      have h' : m ≤ NearSpecV3.Dp0 := block_depth hL hs ht hd hm
      simpa [DedupProof.blockOf, DedupProof.pathItems] using h'
    | skipped hs hd => simp [DedupProof.skipBlock]
  induction hc with
  | last s n B hs hp =>
    intro B' hB; simp only [List.mem_singleton] at hB; subst hB; exact span hs
  | cons s n B hs bs e ht ih =>
    intro B' hB
    rcases List.mem_cons.1 hB with rfl | hB
    · exact span hs
    · exact ih B' hB

/-- The `BYTES` sends of one block are its payload bytes (none for a `dup` reference). -/
theorem block_bytes (B : SrcpB) (rp : Bool) :
    DedupRender.blockMsgs B rp B_BYTES true =
      (DedupProof.payloads B).flatMap fun p => emitAt (msgId K_SRC p.1) 0 p.2 := by
  cases hd : B.dup
  · simp only [DedupRender.blockMsgs, DedupRender.rootMsgs, DedupProof.payloads, hd,
      Bool.false_eq_true, ite_false]
    rw [show srcpLeafMsgs B.j B.L B.ql B.leaf B_BYTES true ++
        B.path.flatMap (fun it => srcpItemMsgs it B_BYTES true) = srcpBlockMsgs B B_BYTES true by
      simp [srcpBlockMsgs, srcpRootMsgs, B_BYTES, B_DIGEST, B_RCL, B_SRC], source_block_bytes]
    simp [B_BYTES, B_DIGEST, B_RCL, B_SRC]
  · simp [DedupRender.blockMsgs, DedupRender.rootMsgs, DedupProof.payloads, hd, B_BYTES, B_DIGEST,
      B_RCL, B_SRC]

/-- Every `BYTES` send of table 20 is a payload byte of a computed block. -/
theorem bytes_mem {bs : List SrcpB} {reps : List Bool} {x : Msg}
    (hx : x ∈ (ddTraffic bs reps).sends B_BYTES) :
    ∃ B ∈ bs, ∃ p ∈ DedupProof.payloads B, x ∈ emitAt (msgId K_SRC p.1) 0 p.2 := by
  simp only [ddTraffic, show B_BYTES ≠ B_SIZE by decide, ite_false, List.mem_flatMap] at hx
  obtain ⟨v, hv, hx⟩ := hx
  rw [block_bytes] at hx
  obtain ⟨p, hp, hx⟩ := List.mem_flatMap.mp hx
  exact ⟨v.1, (List.of_mem_zip hv).1, p, hp, hx⟩

theorem mem_zip_of_mem {bs : List SrcpB} {reps : List Bool} (hl : reps.length = bs.length)
    {B : SrcpB} (hB : B ∈ bs) : ∃ rp, (B, rp) ∈ bs.zip reps := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hB
  exact ⟨reps[i]'(by omega), List.mem_iff_getElem.mpr ⟨i, by simp [hl, hi], by simp⟩⟩

theorem rcl_block_msgs (B : SrcpB) (rp : Bool) :
    DedupRender.blockMsgs B rp B_RCL false = [[B.j, B.L]] := by
  cases hd : B.dup <;>
    simp [DedupRender.blockMsgs, DedupRender.rootMsgs, srcpLeafMsgs, srcpItemMsgs, hd, B_RCL, B_DIGEST,
      B_BYTES, B_SRC]

theorem rcl_recvs (bs : List SrcpB) (reps : List Bool) (hl : reps.length = bs.length) :
    (ddTraffic bs reps).recvs B_RCL = bs.map fun B => [B.j, B.L] := by
  simp only [ddTraffic, show B_RCL ≠ B_SIZE by decide, ite_false, rcl_block_msgs]
  induction bs generalizing reps with
  | nil => simp
  | cons B bs ih =>
    cases reps with
    | nil => simp at hl
    | cons rp reps => simp [ih reps (by simpa using hl)]

theorem rcl_sends (bs : List SrcpB) (reps : List Bool) : (ddTraffic bs reps).sends B_RCL = [] := by
  simp [ddTraffic, DedupRender.blockMsgs, DedupRender.rootMsgs, srcpLeafMsgs, srcpItemMsgs, B_RCL,
    B_DIGEST, B_BYTES, B_SRC, B_SIZE]

theorem leaf_recv {bs : List SrcpB} {reps : List Bool} (hl : reps.length = bs.length)
    {B : SrcpB} (hB : B ∈ bs) (hd : B.dup = false) :
    digMsg (msgId K_RC B.j) B.L B.leaf ∈ (ddTraffic bs reps).recvs B_DIGEST := by
  obtain ⟨rp, hv⟩ := mem_zip_of_mem hl hB
  simp only [ddTraffic, show B_DIGEST ≠ B_SIZE by decide, ite_false, List.mem_flatMap]
  refine ⟨(B, rp), hv, ?_⟩
  simp [DedupRender.blockMsgs, hd, srcpLeafMsgs, B_DIGEST, B_BYTES]

end DDView

namespace DDWf

variable {bs : List SrcpB} {reps : List Bool}

theorem j_lt (h : DDWf bs reps) {B : SrcpB} (hB : B ∈ bs) : B.j < P := by
  obtain ⟨rp, hv⟩ := DDView.mem_zip_of_mem h.len hB
  exact h.canon _ hv B.j (by simp [SourcePublic.viewRecord])

theorem L_lt (h : DDWf bs reps) {B : SrcpB} (hB : B ∈ bs) : B.L < P := by
  have hb := h.block B hB
  cases hd : B.dup
  · simp only [hd, Bool.false_eq_true, ite_false] at hb; exact hb.canon.2.1
  · simp only [hd, ite_true] at hb; rw [hb.1]; unfold P; omega

end DDWf

/-- **The view of table 20** (`SrcpDD.table`): a dedup block chain, its repetition bits, the
record well-formedness (with A10) and the exact traffic. -/
theorem srcpDD_view {tr : Trace Fp} {pub : List Fp} {tt : Nat}
    (hL : TableLocal SrcpDD.table tr tt pub) :
    ∃ bs e, DedupProof.BlockChain tr tt 0 bs e ∧
      DDWf bs ((DedupProof.sourceViews tr tt 0 bs).map Prod.snd) ∧
      TableTraffic DedupTable.interactions tr tt pub
        (ddTraffic bs ((DedupProof.sourceViews tr tt 0 bs).map Prod.snd)) := by
  have hB := SrcpDD.local_dedup hL
  obtain ⟨bs, e, hc⟩ := DedupProof.extract_blocks hB
  have hH : tr.height tt ≤ 2 ^ 22 := by
    have := hL.log_le; unfold Trace.height
    exact Nat.pow_le_pow_right (by decide) (by simpa [SrcpDD.table, SrcpV3.maxLog] using this)
  have hvf := hc.views_facts hB
  refine ⟨bs, e, hc, ⟨by simp [DedupProof.sourceViews_length], hc.nonempty, ?_, ?_, hc.q_next hB,
    hc.local hB, ?_, ?_, DDView.chain_depth hL hc, ?_, hc.payload_wf hB⟩, ?_⟩
  · intro i hi
    have hh := hc.j_indices hB i hi
    rw [(DedupProof.row0 hB).2.1] at hh
    simpa only [show Fp.toNat 0 = 0 from rfl, Nat.zero_add] using hh
  · intro hb
    have hh := hc.q_start hB hb
    rw [(DedupProof.row0 hB).2.2.1] at hh
    simpa only [show Fp.toNat 0 = 0 from rfl, Nat.zero_add] using hh
  · intro v hv; rw [DDView.zip_views] at hv; exact (hvf v hv).2
  · intro v hv; rw [DDView.zip_views] at hv; exact (hvf v hv).1
  · have he := hc.bound
    have hr := hc.rows
    omega
  · intro bb m
    simp only [tableBusCount_eq, hc.all_traffic hB, DDView.sourceMsgs_eq, ite_true,
      Bool.false_eq_true, ite_false]
    simp

end ZkFormal.NearV3
