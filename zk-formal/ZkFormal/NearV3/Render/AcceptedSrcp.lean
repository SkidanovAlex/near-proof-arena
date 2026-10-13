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
import ZkFormal.NearV3.Render.AcceptedSrcpCore

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

/-- The SRC alignment premise: the srcp inputs carry the prepared roots and duplicate flags. -/
theorem acceptedSrcp_src (p : Prep) (w : StateWitness) :
    (acceptedSrcpInputs p w).map (fun y => (y.root, y.dup)) = (List.range p.lists.length).map
      (fun j => ((p.lists.getD j ⟨[], 0, []⟩).root, ZkFormal.NearV3.Public.sourceDup p.lists j)) := by
  simp [acceptedSrcpInputs, List.map_map, Function.comp_def]

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
