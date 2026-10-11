import ZkFormal.NearV3.Render.PaddedUps
import ZkFormal.NearV3.Render.Ups.NativePartInputs
import ZkFormal.NearV3.Render.Ups.NativeByteFamily

/-!
# `UpsRenderOk` from native execution

Each `upsV3` instance of a native run is `nativeInstance` of the native `traceUpsert` run of the
`τ`-th forest root along `[0, 15]`, its parts the native part encoding (`encodeNativeParts`).
`upsRenderOk_of_native` derives the whole honest-input condition `UpsRenderOk` of the aligned
`upsV3` render (`PaddedUps.ups_aligned_complete`) from native data:
* per part (`PartOk`, `FieldsOk`, `WindowOk`, `ByteInput`, `MemOk`): `nativeInstance_partInputs`;
* per instance (`InstOk`): `nativeInstance_semantic_ok`.

**Remaining explicit premises** (`UpsNativeOk`, all decidable facts about the native data):
the forest root lookup and the native upsert (`hroot`, `hr`), a well-formed tree, value length
`1 ≤ |v| < 2^24`, path depth `≤ 400`, the native part encoding, per-part header/prefix lengths
`< 2^22`, and the authenticated walk `WalkOkU` (lookup semantics of the trie walk); for the table:
at least one instance and the row cap `R + 1 ≤ 2^22`.
-/
namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows Assembly ZkFormal.Near ZkFormal.Algebra

/-- The native data of one `upsV3` instance. -/
structure UpsNativeData where
  ts : List PTrie
  tau : Nat
  root : OccurrenceAddress
  value : Bytes
  run : TreeRun
  baseI : UpsInst
  base : Nat → UpsPartI
  Qs : List UpsPartI

namespace UpsNativeData
def recordId (d : UpsNativeData) : PTrie → Nat :=
  pathRecordId (extendedAddresses d.root.nid d.root.vid d.root.depth d.root.tree [0,15])

/-- The generated `upsV3` instance. -/
def inst (d : UpsNativeData) : UpsInst :=
  nativeInstance d.recordId d.baseI d.root.tree d.run d.value d.Qs
end UpsNativeData

/-- The explicit native premises of one instance. -/
structure UpsNativeOk (d : UpsNativeData) : Prop where
  hroot : forestRootAt 0 0 d.ts d.tau = some d.root
  hr : traceUpsert d.root.tree [0,15] d.value = some d.run
  hw : d.root.tree.wf = true
  hv1 : 1 ≤ d.value.length
  hv : d.value.length < 2 ^ 24
  hd : fdepth d.root.tree [0,15] ≤ 400
  he : encodeNativeParts d.recordId d.root.tree d.run (nativeSourceBase d.recordId d.run d.base) = some d.Qs
  hq : ∀ k, k < d.Qs.length → (part d.inst k).qhk < 2 ^ 22 ∧ (part d.inst k).phk < 2 ^ 22
  walk : WalkOkU d.inst

theorem UpsNativeOk.instOk {d : UpsNativeData} (h : UpsNativeOk d) : InstOk d.inst :=
  nativeInstance_semantic_ok d.recordId d.baseI h.hr h.hw h.hv1 h.hv _ h.he h.walk

theorem UpsNativeOk.parts {d : UpsNativeData} (h : UpsNativeOk d) (k : Nat) (hk : k < nQ d.inst) :
    Nonempty (ByteInput d.inst (part d.inst k)) ∧ FieldsOk (part d.inst k) ∧
      PartOk d.inst k (part d.inst k) ∧ WindowOk d.inst (part d.inst k) ∧ MemOk d.inst (part d.inst k) := by
  have hk' : k < d.Qs.length := by
    have := nativeInstance_nQ d.recordId d.baseI d.root.tree d.run d.value d.Qs
    unfold UpsNativeData.inst at hk; omega
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := nativeInstance_partInputs h.hroot h.hr h.hw h.hv h.hd d.baseI d.base
    h.he k hk' (h.hq k hk').1 (h.hq k hk').2
  exact ⟨h1, h2, h3, h4, h5⟩

/-- **`UpsRenderOk` from native execution.** -/
theorem upsRenderOk_of_native (ds : List UpsNativeData) (hok : ∀ d ∈ ds, UpsNativeOk d)
    (hpos : 0 < ds.length) (hcap : R (ds.map UpsNativeData.inst) + 1 ≤ 2 ^ 22) :
    UpsRenderOk (ds.map UpsNativeData.inst) := by
  have hmem : ∀ I ∈ ds.map UpsNativeData.inst, ∃ d ∈ ds, I = d.inst := by
    intro I hI
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hI
    exact ⟨d, hd, rfl⟩
  refine ⟨⟨by simpa using hpos, fun I hI => ?_, hcap⟩, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨d, hd, rfl⟩ := hmem I hI; exact (hok d hd).instOk
  · intro I hI k hk; obtain ⟨d, hd, rfl⟩ := hmem I hI; exact ((hok d hd).parts k hk).2.2.1
  · intro I hI k hk; obtain ⟨d, hd, rfl⟩ := hmem I hI; exact ((hok d hd).parts k hk).2.1
  · intro I hI k hk; obtain ⟨d, hd, rfl⟩ := hmem I hI; exact ((hok d hd).parts k hk).2.2.2.1
  · intro I hI k hk; obtain ⟨d, hd, rfl⟩ := hmem I hI; exact ((hok d hd).parts k hk).1
  · intro I hI k hk; obtain ⟨d, hd, rfl⟩ := hmem I hI; exact ((hok d hd).parts k hk).2.2.2.2

/-- **`upsV3` aligned completeness from native execution.** -/
theorem ups_native_aligned_complete (ds : List UpsNativeData) (hok : ∀ d ∈ ds, UpsNativeOk d)
    (hpos : 0 < ds.length) (hcap : R (ds.map UpsNativeData.inst) + 1 ≤ 2 ^ 22) (t : Nat) (pub : List Fp) :
    let insts := ds.map UpsNativeData.inst
    TableLocal UpsV3.table (upsTraceAligned insts) t pub ∧
    TableTraffic UpsV3.interactions (upsTraceAligned insts) t pub
      (upsTraffic (UpsRows.viewOf (upsTraceAligned insts) t (segsOf insts))) ∧
    (upsTraceAligned insts).log t % 3 = 1 :=
  ups_aligned_complete _ (upsRenderOk_of_native ds hok hpos hcap) t pub

end ZkFormal.NearV3.Render.UpsGen
