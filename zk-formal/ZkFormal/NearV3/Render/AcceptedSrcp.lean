import ZkFormal.NearV3.Render.AcceptedRcpt
import ZkFormal.NearV3.Render.HonestBalanceSrc
import ZkFormal.NearV3.Rcpt.SrcpDepth
import ZkFormal.NearV3.Rcpt.Link.RelSources
import ZkFormal.NearV3.Assembly.PreparedSources
import ZkFormal.NearV3.Rcpt.Candidates.PreparedRepeated
import ZkFormal.NearV3.Rcpt.Candidates.SourceRepetition
import ZkFormal.NearV3.Rcpt.Candidates.PreparedNonempty
import ZkFormal.NearV3.Rcpt.Candidates.RawWitnessBudget
import ZkFormal.NearV3.Assembly.CodecSize
import ZkFormal.NearV3.Assembly.PrepFacts

/-!
# The honest `srcpV3` inputs of an accepted witness

One proof input per prepared source occurrence, in prepared (applied) order: the prepared
root, the prepared duplicate flag and the witness entry selected for the occurrence's key
(`sourceEntry`, last wins).  These satisfy the RCL and SRC alignment premises with the honest
receipt input (`acceptedSrcp_rcl`, `acceptedSrcp_src`), so `honest_rcl_balance` and
`honest_src_balance` hold for the accepted witness without further hypotheses.
-/

namespace ZkFormal.NearV3.Render
open NearSpec NearSpecV3 ZkFormal.Near ZkFormal.Algebra
open ZkFormal.NearV3.Assembly.RcptSkeleton ZkFormal.NearV3.Rcpt.Candidates

/-- The honest source-proof inputs. -/
def acceptedSrcpInputs (p : Prep) (w : StateWitness) : List SrcpGen.ProofInput :=
  (List.range p.lists.length).map fun j =>
    ⟨(p.lists.getD j ⟨[], 0, []⟩).root, ZkFormal.NearV3.Public.sourceDup p.lists j,
     sourceEntry w.entries (p.lists.getD j ⟨[], 0, []⟩)⟩

theorem map_range_getD {α β : Type} (l : List α) (d : α) (f : α → β) :
    (List.range l.length).map (fun j => f (l.getD j d)) = l.map f := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < l.length by simpa using h1)]

/-- The RCL alignment premise: the srcp inputs carry the honest receipt lists in order. -/
theorem acceptedSrcp_rcl (p : Prep) (w : StateWitness) (ctx : ApplyCtx) :
    (acceptedSrcpInputs p w).map (fun y => y.entry.receipts) =
      (sourceInputLists ctx p.lists w.entries).map (List.map Input.receipt) := by
  rw [sourceInputLists_receipts, acceptedSrcpInputs, List.map_map]
  exact map_range_getD p.lists ⟨[], 0, []⟩ (fun s => (sourceEntry w.entries s).receipts)

/-- The SRC alignment premise: the srcp inputs carry the prepared roots and duplicate flags. -/
theorem acceptedSrcp_src (p : Prep) (w : StateWitness) :
    (acceptedSrcpInputs p w).map (fun y => (y.root, y.dup)) = (List.range p.lists.length).map
      (fun j => ((p.lists.getD j ⟨[], 0, []⟩).root, ZkFormal.NearV3.Public.sourceDup p.lists j)) := by
  simp [acceptedSrcpInputs, List.map_map, Function.comp_def]

/-- **RCL balances for an accepted witness** (no alignment hypothesis left). -/
theorem accepted_rcl_balance (pub : List Fp) (x : RcptInput) (ok : RcptOk pub x)
    (hx : x.lists = sourceInputLists x.ctx x.p.lists x.w.entries) :
    (rcptTraffic3 pub (nativeRcptLists pub x)).sends B_RCL =
      (srcpTraffic (SrcpGen.blocksOfProofs (acceptedSrcpInputs x.p x.w))).recvs B_RCL :=
  honest_rcl_balance pub x ok _ (by rw [hx]; exact acceptedSrcp_rcl x.p x.w x.ctx)

/-- Table 20's `RCL` receives: `[j, L_j]` per prepared occurrence (dedup or not). -/
theorem dd_rcl_recvs (p : Prep) (w : StateWitness) :
    (DedupRender.traffic (DedupCompile.blocks p.lists w.entries) (sourceRepeated p.lists)).recvs B_RCL =
      (srcpTraffic (SrcpGen.blocksOfProofs (acceptedSrcpInputs p w))).recvs B_RCL := by
  have hl : (DedupRender.traffic (DedupCompile.blocks p.lists w.entries) (sourceRepeated p.lists)).recvs B_RCL =
      (List.range p.lists.length).map fun j => [j, (DedupCompile.block p.lists w.entries j).L] := by
    simp only [DedupRender.traffic, show B_RCL ≠ B_SIZE by decide, ite_false, DedupRender.sourceMsgs,
      DedupCompile.blocks_length]
    rw [← flatMap_singleton_map]
    apply ZkFormal.Near.Link.flatMap_congr'
    intro j hj
    have hj := List.mem_range.mp hj
    have hg : (DedupCompile.blocks p.lists w.entries).getD j default = DedupCompile.block p.lists w.entries j := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa [DedupCompile.blocks_length] using hj),
        Option.getD_some]
      simp [DedupCompile.blocks]
    rw [hg]
    have hjj : (DedupCompile.block p.lists w.entries j).j = j := by
      simp [DedupCompile.block, SrcpGen.blockOfProof]
    cases hd : (DedupCompile.block p.lists w.entries j).dup <;>
      simp [DedupRender.blockMsgs, DedupRender.rootMsgs, srcpLeafMsgs, srcpItemMsgs, hd, hjj, B_SRC, B_BYTES,
        B_DIGEST, B_RCL]
  have hr : (srcpTraffic (SrcpGen.blocksOfProofs (acceptedSrcpInputs p w))).recvs B_RCL =
      (List.range p.lists.length).map fun j => [j, (DedupCompile.block p.lists w.entries j).L] := by
    have h0 : (srcpTraffic (SrcpGen.blocksOfProofs (acceptedSrcpInputs p w))).recvs B_RCL =
        (SrcpGen.blocksOfProofs (acceptedSrcpInputs p w)).map fun B => [B.j, B.L] := by
      simp only [srcpTraffic, show B_RCL ≠ B_SIZE by decide, ite_false]
      rw [← flatMap_singleton_map]
      apply ZkFormal.Near.Link.flatMap_congr'
      intro B _
      simp [srcpBlockMsgs, srcpRootMsgs, srcpLeafMsgs, srcpItemMsgs, B_RCL, B_DIGEST, B_BYTES, B_SRC]
    rw [h0]
    apply List.ext_getElem
    · simp [SrcpGen.blocksOfProofs, acceptedSrcpInputs]
    · intro i h1 h2
      simp [SrcpGen.blocksOfProofs, acceptedSrcpInputs, SrcpGen.blockOfProof, DedupCompile.block,
        DedupCompile.entryAt, sourceEntry]
  rw [hl, hr]

/-- **SRC balances for an accepted witness** (table 20): the dedup blocks receive the prepared
source records; `sourceMetadataConsistent` from `RelD0a`. -/
theorem accepted_src_balance_dd {budget : Nat} {cb wb : Bytes} {hint : Hint} {p : Prep}
    (ha : RelD0a budget cb wb) (hp : prepD0 cb hint = .ok p) (w : StateWitness) :
    (DedupRender.traffic (DedupCompile.blocks p.lists w.entries) (sourceRepeated p.lists)).recvs B_SRC =
      ZkFormal.NearV3.Public.preparedOn p B_SRC true :=
  honest_src_balance_dd p w.entries (relD0a_prepared_metadata ha hp)

/-- Every prepared source occurrence selects a used proof, so A10 bounds its path. -/
theorem prepared_paths_A10 {budget : Nat} {cb wb : Bytes} {hint : Hint} {p : Prep}
    {k : WalkD0} {w : StateWitness}
    (ha : RelD0a budget cb wb) (hp : prepD0 cb hint = .ok p)
    (hk : walkD0 cb = .ok k) (hw : decodeW wb = .ok w) :
    ∀ s ∈ p.lists, (sourceEntry w.entries s).proof.path.length ≤ Dp0 := by
  obtain ⟨k', w', hk', hw', hv, -⟩ := relD0a_sources_verified ha
  have hek := Except.ok.inj (hk'.symm.trans hk)
  have hew := Except.ok.inj (hw'.symm.trans hw)
  subst k'; subst w'
  have hd := Rcpt.SrcpDepth.relD0a_paths ha hk hw
  refine preparedSourceLists_property (fun s => (sourceEntry w.entries s).proof.path.length ≤ Dp0)
    k.sourceBlks ?_ (ZkFormal.NearV3.Assembly.prepD0_source_lists hp hk)
  intro B hB s hs
  obtain ⟨x, hx, hs⟩ := List.mem_flatMap.mp hs
  by_cases hn : x.1.heightIncluded == B.hdr.height
  · simp only [hn, ↓reduceIte, List.mem_singleton] at hs
    subst s
    obtain ⟨e, he, -, -, -⟩ := hv B hB x hx hn
    have hu : e ∈ usedProofs k w := by
      apply List.mem_flatMap.mpr
      refine ⟨B, hB, List.mem_filterMap.mpr ⟨x, hx, ?_⟩⟩
      simpa only [hn, ↓reduceIte] using he
    simpa only [sourceEntry, he, Option.getD_some] using hd e hu
  · simp [hn] at hs

/-- **A10 for the accepted srcp inputs.** -/
theorem acceptedSrcp_depth {budget : Nat} {cb wb : Bytes} {hint : Hint} {p : Prep}
    {k : WalkD0} {w : StateWitness}
    (ha : RelD0a budget cb wb) (hp : prepD0 cb hint = .ok p)
    (hk : walkD0 cb = .ok k) (hw : decodeW wb = .ok w) :
    ∀ x ∈ acceptedSrcpInputs p w, x.entry.proof.path.length ≤ Dp0 := by
  intro x hx
  simp only [acceptedSrcpInputs, List.mem_map, List.mem_range] at hx
  obtain ⟨j, hj, rfl⟩ := hx
  apply prepared_paths_A10 ha hp hk hw
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
  exact List.getElem_mem hj

/-- **The srcp row bound for the accepted inputs** (A10 and the source-list envelope). -/
theorem acceptedSrcp_rows {budget : Nat} {cb wb : Bytes} {hint : Hint} {p : Prep}
    {k : WalkD0} {w : StateWitness}
    (ha : RelD0a budget cb wb) (hp : prepD0 cb hint = .ok p)
    (hk : walkD0 cb = .ok k) (hw : decodeW wb = .ok w) (hl : p.lists.length ≤ Rcpt.SrcpDepth.maxLists) :
    srcpRows (SrcpGen.blocksOfProofs (acceptedSrcpInputs p w)) ≤ 2 ^ SrcpV3.maxLog :=
  Rcpt.SrcpDepth.proofInputs_rows_A10 _ (by simpa [acceptedSrcpInputs] using hl)
    (acceptedSrcp_depth ha hp hk hw)

/-! ## Table 20 (`SrcpDD`) inputs: the dedup blocks of the prepared sources -/

/-- A10 for every dedup block (each carries its occurrence's selected entry path). -/
theorem acceptedDD_depth {budget : Nat} {cb wb : Bytes} {hint : Hint} {p : Prep}
    {k : WalkD0} {w : StateWitness}
    (ha : RelD0a budget cb wb) (hp : prepD0 cb hint = .ok p)
    (hk : walkD0 cb = .ok k) (hw : decodeW wb = .ok w) :
    ∀ B ∈ DedupCompile.blocks p.lists w.entries, B.path.length ≤ Dp0 := by
  intro B hB
  simp only [DedupCompile.blocks, List.mem_map, List.mem_range] at hB
  obtain ⟨j, hj, rfl⟩ := hB
  simp only [DedupCompile.block, SrcpGen.blockOfProof, SrcpGen.proofItems_length]
  apply prepared_paths_A10 ha hp hk hw
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
  exact List.getElem_mem hj

theorem sum_le_mul {α : Type} (l : List α) (f : α → Nat) (c : Nat) (h : ∀ a ∈ l, f a ≤ c) :
    (l.map f).sum ≤ c * l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.mul_succ]
    have := h a (by simp)
    have := ih (fun b hb => h b (by simp [hb]))
    omega

/-- The dedup rows fit `2^22` (≤ 1984 occurrences, ≤ 32 path items each). -/
theorem acceptedDD_rows {budget : Nat} {cb wb : Bytes} {hint : Hint} {p : Prep}
    {k : WalkD0} {w : StateWitness}
    (ha : RelD0a budget cb wb) (hp : prepD0 cb hint = .ok p)
    (hk : walkD0 cb = .ok k) (hw : decodeW wb = .ok w) :
    DedupRender.R (DedupCompile.blocks p.lists w.entries) ≤ 2 ^ 22 := by
  rw [DedupRender.R_accounting]
  have hn := prepD0_source_count hp
  have hd := acceptedDD_depth ha hp hk hw
  have hl := List.length_filter_le (fun B : SrcpB => !B.dup) (DedupCompile.blocks p.lists w.entries)
  have hs := sum_le_mul ((DedupCompile.blocks p.lists w.entries).filter fun B => !B.dup)
    (fun B => B.path.length) Dp0 (fun B hB => hd B (List.mem_filter.mp hB).1)
  rw [DedupCompile.blocks_length] at hl ⊢
  simp only [Dp0] at hs
  omega

/-- **Duplicate occurrences are empty** for the accepted srcp inputs (distinct applied receipt
ids, `relD0a_repeated_empty`). -/
theorem acceptedSrcp_duplicate {budget : Nat} {cb wb raw : Bytes} {codes : List Bytes}
    {w : StateWitness} {hint : Hint} {p : Prep}
    (h : RelD0a budget cb wb) (hp : prepD0 cb hint = .ok p)
    (hf : decodeWitnessFile wb = .ok (raw, codes)) (hw : decodeStateWitness raw = .ok w) :
    ∀ x ∈ acceptedSrcpInputs p w, x.dup = true →
      (u64 x.entry.proof.toShard ++ encodeReceipts x.entry.receipts).length = 12 := by
  intro x hx hd
  simp only [acceptedSrcpInputs, List.mem_map, List.mem_range] at hx
  obtain ⟨j, hj, rfl⟩ := hx
  have hrep := sourceDup_repeated p.lists hj hd
  have he := DedupCompile.relD0a_repeated_empty h hp hf hw hj hrep
  have he' : (sourceEntry w.entries (p.lists.getD j ⟨[], 0, []⟩)).receipts = [] := he
  simp only [he']
  simp [encodeReceipts, concatAll, u64, u32, leN]

/-- **`ProofInputsOk` for the accepted srcp inputs**, given the decoded widths of the prepared
roots and proof siblings and the RC-preimage length bound (explicit). -/
theorem acceptedSrcp_ok {budget : Nat} {cb wb raw : Bytes} {codes : List Bytes}
    {k : WalkD0} {w : StateWitness} {hint : Hint} {p : Prep}
    (h : RelD0a budget cb wb) (hp : prepD0 cb hint = .ok p) (hk : walkD0 cb = .ok k)
    (hdw : decodeW wb = .ok w)
    (hf : decodeWitnessFile wb = .ok (raw, codes)) (hw : decodeStateWitness raw = .ok w)
    (hne : p.lists ≠ [])
    (hroot : ∀ x ∈ acceptedSrcpInputs p w, x.root.length = 32)
    (hsib : ∀ x ∈ acceptedSrcpInputs p w, ∀ s ∈ x.entry.proof.path, s.1.length = 32)
    (hlen : ∀ x ∈ acceptedSrcpInputs p w,
      (u64 x.entry.proof.toShard ++ encodeReceipts x.entry.receipts).length < Algebra.P) :
    SrcpGen.ProofInputsOk (acceptedSrcpInputs p w) := by
  obtain ⟨-, hl, -⟩ := DedupCompile.relD0a_inputs h hp hf hw
  refine ⟨?_, hroot, hsib, hlen, acceptedSrcp_duplicate h hp hf hw, acceptedSrcp_rows h hp hk hdw hl⟩
  intro he
  have := congrArg List.length he
  simp [acceptedSrcpInputs] at this
  exact hne this

/-! ## Widths and the RC-preimage bound from decoding (no explicit premises left) -/

theorem nat_le_sum_mem {l : List Nat} {x : Nat} (h : x ∈ l) : x ≤ l.sum := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    simp only [List.sum_cons]
    rcases List.mem_cons.1 h with rfl | h
    · omega
    · have := ih h; omega

/-- A decoded witness entry's RC preimage `u64 to_shard ++ borsh(receipts)` is no longer than
the decoded witness bytes (canonical re-encoding never enlarges, `decodeStateWitness_encodeSW_size`). -/
theorem entry_rc_length_le {raw : Bytes} {w : StateWitness} (hw : decodeStateWitness raw = .ok w) :
    ∀ e ∈ w.entries, (u64 e.proof.toShard ++ encodeReceipts e.receipts).length ≤ raw.length := by
  intro e he
  have hs := ZkFormal.NearV3.Assembly.decodeStateWitness_encodeSW_size hw
  have hm : (ZkFormal.V3.encodeEntry e).length ≤ (concatAll (w.entries.map ZkFormal.V3.encodeEntry)).length := by
    rw [ZkFormal.NearV3.Render.concatAll_length, List.map_map]
    exact nat_le_sum_mem (List.mem_map.mpr ⟨e, he, rfl⟩)
  have hsw : (concatAll (w.entries.map ZkFormal.V3.encodeEntry)).length ≤ (ZkFormal.V3.encodeSW w).length := by
    simp only [ZkFormal.V3.encodeSW, encList, List.length_append]
    omega
  have he' : (u64 e.proof.toShard ++ encodeReceipts e.receipts).length ≤ (ZkFormal.V3.encodeEntry e).length := by
    have hr : encodeReceipts e.receipts = encList Receipt.encode e.receipts := rfl
    simp only [ZkFormal.V3.encodeEntry, hr, List.length_append, u64, leN, List.length_cons,
      List.length_nil]
    omega
  omega

/-- **`ProofInputsOk` for the accepted srcp inputs from acceptance alone**: nonempty source
lists (`prepD0_sources_nonempty`), 32-byte prepared roots (`prepD0_source_roots`), 32-byte
decoded siblings (`relD0a_source_paths`), and RC preimages `≤ |raw| ≤ 8 MiB < P`. -/
theorem acceptedSrcp_ok_of_accept {budget : Nat} {cb wb raw : Bytes} {codes : List Bytes}
    {k : WalkD0} {w : StateWitness} {hint : Hint} {p : Prep}
    (h : RelD0a budget cb wb) (hp : prepD0 cb hint = .ok p) (hk : walkD0 cb = .ok k)
    (hdw : decodeW wb = .ok w)
    (hf : decodeWitnessFile wb = .ok (raw, codes)) (hw : decodeStateWitness raw = .ok w) :
    SrcpGen.ProofInputsOk (acceptedSrcpInputs p w) := by
  obtain ⟨raw', codes', w', hf', hw', hlen', hpath⟩ := relD0a_source_paths h
  have hraw : raw' = raw := by
    rw [hf] at hf'
    cases hf'
    rfl
  subst raw'
  have hww : w' = w := by
    rw [hw] at hw'
    cases hw'
    rfl
  subst w'
  rw [ZkFormal.NearV3.Rcpt.Candidates.lenT_eq_length] at hlen'
  have hentry : ∀ s : SrcList, sourceEntry w.entries s = ⟨[],[],⟨0,0,[]⟩⟩ ∨
      ∃ e, lookupLast s.key w.entries = some e ∧ sourceEntry w.entries s = e := by
    intro s
    cases he : lookupLast s.key w.entries with
    | none => left; simp [sourceEntry, he]
    | some e => right; exact ⟨e, rfl, by simp [sourceEntry, he]⟩
  refine acceptedSrcp_ok h hp hk hdw hf hw
    (ZkFormal.NearV3.Rcpt.Candidates.prepD0_sources_nonempty hp hk) ?_ ?_ ?_
  · intro x hx
    simp only [acceptedSrcpInputs, List.mem_map, List.mem_range] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    apply ZkFormal.NearV3.Assembly.prepD0_source_roots hp
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
    exact List.getElem_mem hj
  · intro x hx st hst
    simp only [acceptedSrcpInputs, List.mem_map, List.mem_range] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    rcases hentry (p.lists.getD j ⟨[], 0, []⟩) with he | ⟨e, hl, he⟩
    · simp only [he] at hst; simp at hst
    · simp only [he] at hst
      exact (hpath _ e hl st hst).1
  · intro x hx
    simp only [acceptedSrcpInputs, List.mem_map, List.mem_range] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    have hP : (8388608 : Nat) < Algebra.P := by unfold Algebra.P; omega
    rcases hentry (p.lists.getD j ⟨[], 0, []⟩) with he | ⟨e, hl, he⟩
    · simp only [he]
      simp only [encodeReceipts, concatAll, u64, u32, leN, List.map_nil, List.length_append,
        List.length_cons, List.length_nil]
      omega
    · simp only [he]
      have := entry_rc_length_le hw e (lookupLast_mem hl)
      omega

end ZkFormal.NearV3.Render
