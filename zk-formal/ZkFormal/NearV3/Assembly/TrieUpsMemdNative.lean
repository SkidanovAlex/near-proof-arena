import ZkFormal.NearV3.Assembly.TrieUpsMemdPair
import ZkFormal.NearV3.Assembly.TrieUpsTermRV
import ZkFormal.NearV3.Assembly.TrieUpsSplitLink
import ZkFormal.NearV3.Render.Ups.NativeInstanceBoundary
import ZkFormal.NearV3.Render.Ups.NativePlanFamily
import ZkFormal.NearV3.Render.Ups.NativePartInputs
import ZkFormal.NearV3.Rcpt.Candidates.NativeReaderOriginProvider

/-!
# ZkFormal.NearV3.Assembly.TrieUpsMemdNative — `MemdLink` for native instances

**`nativeInstance_memdLink`**: every receiving part of a native upsert instance stores, as its
child memory `mB`, the exact memory scalar `RV` of its `MEMD` child part (upper parts and `WEX`:
the part below; `SPB` in the cases `LSb, LSc, ESl0, ESn0`: the moved node, part 0).
-/

namespace ZkFormal.NearV3.Assembly.TrieUpsMemdNative

open NearSpec ZkFormal.NearV3 Render Render.UpsGen UpsRows TrieUpsMemdPair

theorem nativeInstance_memdLink (recordId : PTrie→Nat) (baseI : UpsInst)
    {root : PTrie} {v : Bytes} {run : TreeRun} (hr : traceUpsert root [0,15] v=some run)
    (hw : root.wf=true) (hv : v.length<2^24) (base : Nat→UpsPartI) {Qs : List UpsPartI}
    (he : encodeNativeMemoryParts recordId root run base=some Qs) :
    MemdLink (nativeInstance recordId baseI root run v Qs) := by
  intro k hk hR
  rw [nativeInstance_nQ] at hk
  let B := nativeMemoryBase run base
  have hplan := fun k' (hk' : k' < Qs.length) => nativeInstance_plan recordId baseI hr hw B he k' hk'
  obtain ⟨p,Q,hp,hQ,henc,hpart⟩ := nativeInstance_part recordId baseI hr B he k hk
  have hkind : (part (nativeInstance recordId baseI root run v Qs) k).kind = p.kind.ix := by
    rw [hpart]; change Q.kind = _; exact encodeTreePart_kind henc
  have hmB : (part (nativeInstance recordId baseI root run v Qs) k).mB = (B k).mB := by
    rw [hpart]; change Q.mB = _
    rw [encodeTreePart_mB henc]
    simp [positionedPart, withPlanPosition, withDescentPosition]
  obtain ⟨hW, hS⟩ := traceUpsert_splitLinked root [0,15] v run hr k p hp
  have hchild : ∀ j, (part (nativeInstance recordId baseI root run v Qs) k).jm = j + 1 →
      child (nativeInstance recordId baseI root run v Qs) (part (nativeInstance recordId baseI root run v Qs) k) =
        part (nativeInstance recordId baseI root run v Qs) j := by
    intro j hj; simp [child, hj]
  unfold RecvK at hR
  rw [hkind] at hR
  rcases hR with hd | hs
  · -- RDB, RDE, WEX, PT: the part below
    have hjm := (hplan k hk).jmD (by rw [hkind]; exact hd)
    have hpos : 0 < k := by
      by_cases hk0 : k = 0
      · subst hk0
        have hnu := traceUpsert_first_nonupper hr hp
        rcases hd with h | h | h | h <;> cases hc : p.kind <;> simp_all [UKind.ix, UpsGen.upperKind]
      · omega
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [hchild j hjm]
    obtain ⟨q, hq, hrv⟩ := nativeInstance_RV recordId baseI hr hw hv base he j (by omega)
    rw [hrv, hmB]
    have hprev : run.parts[j]? = some q := hq
    by_cases hu : p.kind = .RDB ∨ p.kind = .RDE ∨ p.kind = .PT
    · simp [B, nativeMemoryBase, hp, hu, hprev]
    · have hwex : p.kind = .WEX := by
        rcases hd with h | h | h | h <;> cases hc : p.kind <;> simp_all [UKind.ix]
      obtain ⟨-, q', hq', hm⟩ := hW hwex
      simp only [Nat.add_sub_cancel] at hq'
      rw [hprev] at hq'
      cases hq'
      simp [B, nativeMemoryBase, hp, hu, hm]
  · -- SPB of the moved-node cases: part 0
    have hjm := (hplan k hk).jmS (by rw [hkind]; exact hs.1) hs.2
    rw [hchild 0 hjm]
    have hspb : p.kind = .SPB := by cases hc : p.kind <;> simp_all [UKind.ix]
    have hci : (nativeInstance recordId baseI root run v Qs).ci = run.terminal.ix := by
      simp [nativeInstance, signedInstance, positionedInstance, traceInstance]
    have hterm : run.terminal = .LSb ∨ run.terminal = .LSc ∨ run.terminal = .ESl0 ∨ run.terminal = .ESn0 := by
      have h2 := hs.2
      rw [hci] at h2
      cases hc : run.terminal <;> simp_all [UCase.ix]
    obtain ⟨q, hq, hm⟩ := hS hspb hterm
    obtain ⟨q', hq', hrv⟩ := nativeInstance_RV recordId baseI hr hw hv base he 0 (by
      have := List.getElem?_eq_some_iff.mp hq
      have hl := List.getElem?_eq_some_iff.mp hp
      omega)
    rw [hq] at hq'
    cases hq'
    rw [hrv, hmB]
    have hu : ¬(p.kind = .RDB ∨ p.kind = .RDE ∨ p.kind = .PT) := by rw [hspb]; simp
    simp [B, nativeMemoryBase, hp, hu, hm]

open Rcpt.Candidates.NodePostUpdate in
/-- `MemdLink` of a native reader instance. -/
theorem memdLink_of_origin {root : OccurrenceAddress} {run : TreeRun} {value : Bytes} {I : UpsInst}
    (origin : NativeReaderOrigin root run value I)
    (hr : traceUpsert root.tree [0,15] value=some run) (hw : root.tree.wf=true) (hv : value.length<2^24) :
    MemdLink I := by
  obtain ⟨B,base,Qs,he,rfl⟩ := origin
  have hemem : encodeNativeMemoryParts (pathRecordId (extendedAddresses root.nid root.vid root.depth root.tree [0,15]))
      root.tree run (nativeCidBase (pathRecordId (extendedAddresses root.nid root.vid root.depth root.tree [0,15])) run
        (nativeLengthBase run base))=some Qs := by
    unfold encodeNativeMemoryParts
    rw [←nativeSourceBase_asMemory]
    exact he
  exact nativeInstance_memdLink _ B hr hw hv _ hemem

open Rcpt.Candidates.NodePostUpdate in
/-- **`MemdPair` of an allocated native reader instance.** -/
theorem memdPair_of_origin {us : List SchedulerUpsertWitness} {tau : Nat} {u : SchedulerUpsertWitness}
    {I : UpsInst} (a : AllocatedNativeInstance us tau u I) {root : OccurrenceAddress}
    (origin : NativeReaderOrigin root u.run u.value I)
    (hr : traceUpsert root.tree [0,15] u.value=some u.run) (hw : root.tree.wf=true) (hv : u.value.length<2^24) :
    TrieUpsMemd.MemdPair I :=
  memdPair_of I a.2.2.2.2.1 a.2.2.2.2.2.2.2
    (fun k hk => by have := origin.room hr hw k hk; omega)
    (memdLink_of_origin origin hr hw hv)

end ZkFormal.NearV3.Assembly.TrieUpsMemdNative
