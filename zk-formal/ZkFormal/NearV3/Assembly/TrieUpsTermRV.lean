import ZkFormal.NearV3.Render.Ups.TreeTerminalMemory
import ZkFormal.NearV3.Render.Ups.NativeMemoryFamily

/-!
# ZkFormal.NearV3.Assembly.TrieUpsTermRV — the exact memory scalar of terminal parts

`traceUpsert_terminalRV`: for every non-upper part of a native upsert run, the encoded part's
memory scalar `RV` is the part's output memory `memD` (the per-case identities behind
`traceUpsert_terminalMemOk`, exported).
-/

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows

theorem trace_value_RV {source : PTrie} {key : List Nat} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert source key v=some run) (hw : source.wf=true)
    (hvterm : valueTerminal source key) (hk : key.length≤2) (hv : v.length<2^24)
    (baseI : UpsInst) {part : TreePart} (hp : part∈run.parts)
    (base : UpsPartI) {Q : UpsPartI} (he : encodeTreePart base part=some Q) :
    RV (traceInstance baseI run v) (withMemorySign (traceInstance baseI run v) Q)=(part.output.memD:Int) := by
  have hL : L (traceInstance baseI run v)<2^24 := by simpa [L,traceInstance] using hv
  cases source with
  | hash h => simp [valueTerminal] at hvterm
  | ext oldKey child mem => simp [valueTerminal] at hvterm
  | leaf oldKey old mem =>
    have hkey : oldKey=key := hvterm
    subst oldKey
    simp only [traceUpsert,ite_true,Option.some.injEq] at hr
    subst run
    simp only [terminalRun,List.mem_singleton] at hp
    subst part
    rw [treeRlp_memory _ base Q key old mem v he rfl hL]
    simp [newLeaf, PTrie.memD, PTrie.mem?]
  | branch old kids mem =>
    have hkey : key=[] := hvterm
    subst key
    simp only [traceUpsert,Option.some.injEq] at hr
    subst run
    simp only [terminalRun,List.mem_singleton] at hp
    subst part
    cases old with
    | none =>
      rw [treeRbv_memory _ base Q kids mem v (by simpa using he) hw rfl hL]
      simp [PTrie.memD, PTrie.mem?]
    | some old =>
      rw [treeRbr_memory _ base Q old kids mem v (by simpa using he) hw rfl hL]
      simp [PTrie.memD, PTrie.mem?]

theorem trace_insert_RV {value : Option Slot} {kids : Kids} {mem slot : Nat}
    {key : List Nat} {v : Bytes} {run : KidsRun}
    (hr : traceKids (.branch value kids mem) (slot::key) kids slot key v=some run)
    (hi : run.inserted=true) (hw : (PTrie.branch value kids mem).wf=true)
    (hkey : slot::key=[0,15] ∨ slot::key=[15]) (hv : v.length<2^24) (baseI : UpsInst)
    {part : TreePart} (hp : part∈(closeBranchRun value kids mem slot run).parts)
    (base : UpsPartI) {Q : UpsPartI} (he : encodeTreePart base part=some Q) :
    RV (traceInstance baseI (closeBranchRun value kids mem slot run) v)
      (withMemorySign (traceInstance baseI (closeBranchRun value kids mem slot run) v) Q)=(part.output.memD:Int) := by
  let I := traceInstance baseI (closeBranchRun value kids mem slot run) v
  have hd := traceKids_inserted _ _ _ _ _ _ _ hr hi
  have hshort : key.length≤1 := by
    rcases hkey with hh|hh
    · obtain ⟨rfl,rfl⟩ := List.cons.inj hh; decide
    · obtain ⟨rfl,rfl⟩ := List.cons.inj hh; decide
  have hL : L I<2^24 := by simpa [I,traceInstance,L] using hv
  have hparts := hp
  simp only [closeBranchRun,pushPart,hd.2.2,terminalRun,List.mem_append,List.mem_singleton] at hparts
  rcases hparts with rfl|rfl
  · exact (treeNlf_memory I base Q (.branch value kids mem) key v he hshort rfl hL).trans (by simp [newLeaf, PTrie.memD, PTrie.mem?])
  · have hencode : encodeTreePart base ⟨.RBI,.branch value kids mem,
        .branch value run.output (mem+leafMem key v.length),slot⟩=some Q := by
      simpa [hi,hd.1,hd.2.1] using he
    have ht := treeRbi_memory I base Q value kids run.output mem slot key v hencode hw hshort rfl hL
    simpa [hi,hd.1,hd.2.1,PTrie.memD,PTrie.mem?] using ht

mutual
/-- All terminal and split memory inputs are derived along the complete native path. -/
theorem traceUpsert_terminalRV : ∀ (t : PTrie) (key : List Nat) (v : Bytes) (run : TreeRun),
    traceUpsert t key v=some run → t.wf=true → FixedSuffix key → v.length<2^24 →
    ∀ (baseI : UpsInst) (p : TreePart), p∈run.parts → ∀ base Q,
    encodeTreePart base p=some Q → ¬upperKind p.kind → Q.mB=splitChildMemory run.matched p →
    RV (traceInstance baseI run v) (withMemorySign (traceInstance baseI run v) Q)=(p.output.memD:Int)
  | .hash _, _, _, _, hr, _, _, _, _, _, _, _, _, _, _, _ => by simp [traceUpsert] at hr
  | .leaf k s m, key, v, run, hr, hw, hk, hv, baseI, p, hp, base, Q, he, _, hm => by
    by_cases hkey : k=key
    · exact trace_value_RV hr hw hkey hk.length hv baseI hp base he
    · simp only [traceUpsert,hkey,ite_false,Option.some.injEq] at hr
      subst run
      rw [leafSplitRun_matched k s m key v hkey] at hm
      exact leafSplitRun_memory k s m key v hw hk hkey hv baseI p hp base Q he hm
  | .ext k c m, key, v, run, hr, hw, hk, hv, baseI, p, hpart, base, Q, he, hu, hmB => by
    cases hp : isPrefix k key with
    | false =>
      simp only [traceUpsert,hp,Bool.false_eq_true,ite_false,Option.some.injEq] at hr
      subst run
      rw [extSplitRun_matched] at hmB
      exact extSplitRun_memory k c m key v hw hk hp hv baseI p hpart base Q he hmB
    | true =>
      have hcwf : c.wf=true := by
        simp only [PTrie.wf,Bool.and_eq_true] at hw
        exact hw.1.1.2
      cases hm : c.mem? with
      | none => simp [traceUpsert,hp,hm] at hr
      | some cm =>
        cases hc : traceUpsert c (key.drop k.length) v with
        | none => simp [traceUpsert,hp,hm,hc] at hr
        | some inner =>
          simp only [traceUpsert,hp,ite_true,hm,hc,Option.some.injEq] at hr
          subst run
          simp only [pushPart,List.mem_append,List.mem_singleton] at hpart
          rcases hpart with hold|hnew
          · exact traceUpsert_terminalRV c (key.drop k.length) v inner hc hcwf (hk.drop _) hv baseI p hold base Q he hu hmB 
          · subst p
            exfalso; apply hu
            cases k <;> simp [upperKind]
  | .branch bv cs m, [], v, run, hr, hw, hk, hv, baseI, p, hp, base, Q, he, _, _ => by
    exact trace_value_RV hr hw rfl (by decide) hv baseI hp base he
  | .branch bv cs m, n::key, v, run, hr, hw, hk, hv, baseI, p, hpart, base, Q, he, hu, hmB => by
    have hcs : Kids.wf cs 16=true := by
      simp only [PTrie.wf,Bool.and_eq_true] at hw
      exact hw.1.2
    cases hc : traceKids (.branch bv cs m) (n::key) cs n key v with
    | none => simp [traceUpsert,hc] at hr
    | some inner =>
      simp only [traceUpsert,hc,Option.map_some,Option.some.injEq] at hr
      subst run
      cases hi : inner.inserted with
      | true =>
        have hkey : n::key=[0,15] ∨ n::key=[15] := by
          rcases hk with h|h|h
          · simp at h
          · exact Or.inr h
          · exact Or.inl h
        have hmb : base.mB<2^74 := by
          have hin := (traceKids_inserted _ _ _ _ _ _ _ hc hi).2.2
          have hparts := hpart
          simp only [pushPart,hin,terminalRun,List.mem_append,List.mem_singleton] at hparts
          have hb := encodeTreePart_mB he
          rcases hparts with rfl|rfl <;> simp [hi,splitChildMemory] at hmB <;> omega
        exact trace_insert_RV hc hi hw hkey hv baseI hpart base he
      | false =>
        simp only [pushPart,List.mem_append,List.mem_singleton] at hpart
        rcases hpart with hold|hnew
        · exact traceKids_terminalRV (.branch bv cs m) (n::key) cs 16 n key v inner hcs hc hi
            (by simpa using hk.drop 1) hv baseI p hold base Q he hu hmB 
        · subst p
          exact (hu (by simp [hi,upperKind])).elim

theorem traceKids_terminalRV : ∀ (source : PTrie) (wholeKey : List Nat) (cs : Kids) (width n : Nat)
    (key : List Nat) (v : Bytes) (run : KidsRun), Kids.wf cs width=true →
    traceKids source wholeKey cs n key v=some run → run.inserted=false → FixedSuffix key → v.length<2^24 →
    ∀ (baseI : UpsInst) (p : TreePart), p∈run.inner.parts → ∀ base Q,
    encodeTreePart base p=some Q → ¬upperKind p.kind → Q.mB=splitChildMemory run.inner.matched p →
    RV (traceInstance baseI run.inner v) (withMemorySign (traceInstance baseI run.inner v) Q)=(p.output.memD:Int)
  | _, _, .nil, _, _, _, _, _, _, hr, _, _, _, _, _, _, _, _, _, _, _ => by simp [traceKids] at hr
  | source, wholeKey, .none rest, _, 0, key, v, run, _, hr, hi, _, _, _, _, _, _, _, _, _, _ => by
    simp only [traceKids,Option.some.injEq] at hr
    subst run; cases hi
  | source, wholeKey, .some child rest, width, 0, key, v, run, hw, hr, hi, hk, hv, baseI, p, hp, base, Q, he, hu, hmB => by
    simp only [Kids.wf,Bool.and_eq_true,bne_iff_ne] at hw
    cases hm : child.mem? with
    | none => simp [traceKids,hm] at hr
    | some cm =>
      cases hc : traceUpsert child key v with
      | none => simp [traceKids,hm,hc] at hr
      | some inner =>
        simp only [traceKids,hm,hc,Option.some.injEq] at hr
        subst run
        exact traceUpsert_terminalRV child key v inner hc hw.1.2 hk hv baseI p hp base Q he hu hmB 
  | source, wholeKey, .none rest, width, n+1, key, v, run, hw, hr, hi, hk, hv, baseI, p, hp, base, Q, he, hu, hmB => by
    simp only [Kids.wf,Bool.and_eq_true,bne_iff_ne] at hw
    cases hc : traceKids source wholeKey rest n key v with
    | none => simp [traceKids,hc] at hr
    | some inner =>
      simp only [traceKids,hc,Option.map_some,Option.some.injEq] at hr
      subst run
      exact traceKids_terminalRV source wholeKey rest (width-1) n key v inner hw.2 hc hi hk hv baseI p hp base Q he hu hmB 
  | source, wholeKey, .some child rest, width, n+1, key, v, run, hw, hr, hi, hk, hv, baseI, p, hp, base, Q, he, hu, hmB => by
    simp only [Kids.wf,Bool.and_eq_true,bne_iff_ne] at hw
    cases hc : traceKids source wholeKey rest n key v with
    | none => simp [traceKids,hc] at hr
    | some inner =>
      simp only [traceKids,hc,Option.map_some,Option.some.injEq] at hr
      subst run
      exact traceKids_terminalRV source wholeKey rest (width-1) n key v inner hw.2 hc hi hk hv baseI p hp base Q he hu hmB 
end

/-- **Every native part's memory scalar is its output memory** (terminal and upper parts). -/
theorem nativeInstance_RV (recordId : PTrie→Nat) (baseI : UpsInst)
    {root : PTrie} {v : Bytes} {run : TreeRun} (hr : traceUpsert root [0,15] v=some run)
    (hw : root.wf=true) (hv : v.length<2^24) (base : Nat→UpsPartI) {Qs : List UpsPartI}
    (he : encodeNativeMemoryParts recordId root run base=some Qs) (k : Nat) (hk : k<Qs.length) :
    ∃ p, run.parts[k]?=some p ∧
      RV (nativeInstance recordId baseI root run v Qs) (part (nativeInstance recordId baseI root run v Qs) k)=
        (p.output.memD:Int) := by
  let I0 := positionedInstance recordId baseI root run v Qs
  let B := nativeMemoryBase run base
  obtain ⟨p,Q,hp,hQ,henc,hpart⟩ := nativeInstance_part recordId baseI hr B he k hk
  by_cases hu : upperKind p.kind
  · have hkpos : 0<k := by
      by_cases heq : k=0
      · subst k; exact (traceUpsert_first_nonupper hr hp hu).elim
      · omega
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k≠0 by omega)
    apply nativeInstance_upperRV recordId baseI hr hw hv base he j hk
    rw [hpart]
    change Q.kind=0 ∨ Q.kind=1 ∨ Q.kind=11
    rw [encodeTreePart_kind henc]
    cases hc : p.kind <;> simp_all [upperKind,UKind.ix]
  · have hm : Q.mB=splitChildMemory run.matched p := by
      rw [encodeTreePart_mB henc]
      simp [positionedPart,withPlanPosition,withDescentPosition,B,nativeMemoryBase,hp,
        show ¬(p.kind=.RDB ∨ p.kind=.RDE ∨ p.kind=.PT) from hu]
    have h := traceUpsert_terminalRV root [0,15] v run hr hw (Or.inr (Or.inr rfl)) hv
      I0 p (List.mem_of_getElem? hp) _ Q henc hu hm
    refine ⟨p, hp, ?_⟩
    have h' : RV I0 (withMemorySign I0 Q)=(p.output.memD:Int) := h
    rw [hpart]
    simpa only [nativeInstance,RV,TV,signedInstance_X1V,signedInstance_EinV] using h'

end ZkFormal.NearV3.Render.UpsGen
