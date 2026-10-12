import ZkFormal.NearV3.Assembly.LinkCore
import ZkFormal.NearV3.Rcpt.Candidates.NativeDictionary
import ZkFormal.NearV3.Rcpt.Candidates.NativeFillers

/-!
# ZkFormal.NearV3.Assembly.LinkDict — the source dictionary from the records; `dictDepth`

The dictionary of the link is the executable first-occurrence dictionary of the prepared
sources over the records (`Rcpt.Candidates.nativeDictionary`, fillers `nativeFillers`):

    `dictOf p r = nativeDictionary p.lists p.hdr.own r.lists r.srcp (nativeFillers p.lists)`.

Every source entry of it carries a source-proof block of `r.srcp` (or the empty default block),
so **`RestFieldsV3.dictDepth`** follows from the A10 depth view `W.srcpDepth`
(`dictDepth_of_records`).
-/

namespace ZkFormal.NearV3.Assembly

open NearSpec NearSpecV3

namespace LinkDict

/-- Every source entry of a native dictionary has the path of some block of `bs`, or the
empty default block. -/
theorem nativeDictionary_path {sources : List SrcList} {own : Nat} {rs : ZkFormal.NearV3.RcptV3Vs}
    {bs : List ZkFormal.NearV3.SrcpB} {fillers : List ProofEntry} {e : SourceEntryV3}
    (he : Sum.inl e ∈ ZkFormal.NearV3.Rcpt.Candidates.nativeDictionary sources own rs bs fillers) :
    e.path ∈ bs ∨ e.path = default := by
  simp only [ZkFormal.NearV3.Rcpt.Candidates.nativeDictionary, List.mem_append, List.mem_map,
    reduceCtorEq, and_false, exists_false, or_false, Sum.inl.injEq] at he
  obtain ⟨e', he', rfl⟩ := he
  simp only [ZkFormal.NearV3.Rcpt.Candidates.firstNativeSources, List.mem_map] at he'
  obtain ⟨i, -, rfl⟩ := he'
  simp only [ZkFormal.NearV3.Rcpt.Candidates.nativeEntryAt,
    ZkFormal.NearV3.Rcpt.Candidates.DedupProof.nativeSourceEntry]
  by_cases hi : i < bs.length
  · left
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    exact List.getElem_mem hi
  · right
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega), Option.getD_none]

/-- **The depth bound of a native dictionary** from the blocks' depth bound. -/
theorem nativeDictionary_depth {sources : List SrcList} {own : Nat} {rs : ZkFormal.NearV3.RcptV3Vs}
    {bs : List ZkFormal.NearV3.SrcpB} {fillers : List ProofEntry}
    (hd : ∀ B ∈ bs, B.path.length ≤ Dp0) :
    ∀ e : SourceEntryV3, Sum.inl e ∈ ZkFormal.NearV3.Rcpt.Candidates.nativeDictionary sources own rs bs fillers →
      e.path.path.length ≤ Dp0 := by
  intro e he
  rcases nativeDictionary_path he with h | h
  · exact hd _ h
  · rw [h]
    show ([] : List ZkFormal.NearV3.SrcpItem).length ≤ Dp0
    exact Nat.zero_le _

end LinkDict

/-- The source dictionary of the link: prepared sources, records' receipt lists and source
blocks, fresh fillers. -/
def dictOf (p : Prep) (r : V3Records) : List DictionaryEntryV3 :=
  ZkFormal.NearV3.Rcpt.Candidates.nativeDictionary p.lists p.hdr.own r.lists r.srcp
    (ZkFormal.NearV3.Rcpt.Candidates.nativeFillers p.lists)

/-- **`RestFieldsV3.dictDepth`** for `xOf r (dictOf p r)`, from the A10 view (`W.srcpDepth`). -/
theorem dictDepth_of_records {pub : List ZkFormal.Algebra.Fp} {p : Prep} {r : V3Records}
    (W : V3RecordsWf pub r) :
    ∀ e : SourceEntryV3, Sum.inl e ∈ (xOf r (dictOf p r)).dictionary → e.path.path.length ≤ Dp0 :=
  LinkDict.nativeDictionary_depth W.srcpDepth

end ZkFormal.NearV3.Assembly
