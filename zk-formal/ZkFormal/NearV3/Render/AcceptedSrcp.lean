import ZkFormal.NearV3.Render.AcceptedRcpt
import ZkFormal.NearV3.Render.HonestBalanceSrc
import ZkFormal.NearV3.Rcpt.SrcpDepth
import ZkFormal.NearV3.Rcpt.Link.RelSources
import ZkFormal.NearV3.Assembly.PreparedSources
import ZkFormal.NearV3.Rcpt.Candidates.PreparedRepeated
import ZkFormal.NearV3.Rcpt.Candidates.SourceRepetition

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

/-- **SRC balances for an accepted witness** against the prepared source segment. -/
theorem accepted_src_balance (p : Prep) (w : StateWitness) :
    (srcpTraffic (SrcpGen.blocksOfProofs (acceptedSrcpInputs p w))).recvs B_SRC =
      ZkFormal.NearV3.Public.preparedOn p B_SRC true :=
  honest_src_balance p _ (acceptedSrcp_src p w)

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

end ZkFormal.NearV3.Render
