import ZkFormal.NearV3.Assembly.TrieA7Repl
import ZkFormal.NearV3.Assembly.TrieA7Perm
import ZkFormal.NearV3.Assembly.TrieA7Cap

/-!
# ZkFormal.NearV3.Assembly.TrieA7Match — the replaced path nodes / overwritten value are `RPL`/`RPLV` ids (A7 (b), step 2)

Run level (no well-formedness needed):

* `termK` (`RLP/RBR/RBV/RBI/SPB`) / `upK` (`RDB/RDE/PT`) split `replK`; `replaced_split`;
* **`traceUpsert_term`**: `termCharge run ≤ |nodeEnc run.terminalSource|` (one terminal replacing part,
  whose source is the terminal source) and `oldValCharge run ≤ oldBound run` (the terminal source's own
  value for an `LP`/`BR` terminal, else `0`).

Instance level, for an allocated native instance `I` of a scheduler witness `u` at `τ` (the reader
origin `NativeReaderOrigin root u.run u.value I`, `InstOk I`, `NativeWalkProviders`):

* **`rpl_cover`**: `replacedCharge u.run ≤ Σ_{b ∈ upsRplMsgs I} LT b` (`LT` = serialized length of the
  forest node record named by `b`);
* **`rplv_cover`**: `oldValCharge u.run ≤ Σ_{b ∈ upsRplvMsgs I} LV b` (`LV` = length of the forest value
  named by `b`).
-/

namespace ZkFormal.NearV3.Assembly.TrieA7Match

open NearSpec Render Render.UpsGen ZkFormal.NearV3.Assembly TrieA7Post TrieA7Repl

/-! ## Run level -/

def termK : UpsRows.UKind → Bool
  | .RLP | .RBR | .RBV | .RBI | .SPB => true
  | _ => false

def upK : UpsRows.UKind → Bool
  | .RDB | .RDE | .PT => true
  | _ => false

def termCharge (run : TreeRun) : Nat :=
  (run.parts.map fun p => if termK p.kind then (NearSpecV3.nodeEnc p.source).length else 0).sum

def upCharge (run : TreeRun) : Nat :=
  (run.parts.map fun p => if upK p.kind then (NearSpecV3.nodeEnc p.source).length else 0).sum

theorem replaced_split (run : TreeRun) : replacedCharge run = termCharge run + upCharge run := by
  unfold replacedCharge termCharge upCharge
  induction run.parts with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    cases p.kind <;> simp [replK, termK, upK] <;> omega

/-- The overwritten own value allowed by the terminal case. -/
def oldBound (run : TreeRun) : Nat :=
  match run.terminal with
  | .LP | .BR => ((NearSpecV3.ownVals run.terminalSource).map List.length).sum
  | _ => 0

def TermOk (run : TreeRun) : Prop :=
  termCharge run ≤ (NearSpecV3.nodeEnc run.terminalSource).length ∧ oldValCharge run ≤ oldBound run

@[simp] theorem termCharge_push (r : TreeRun) (p : TreePart) :
    termCharge (pushPart r p) = termCharge r + (if termK p.kind then (NearSpecV3.nodeEnc p.source).length else 0) := by
  simp [termCharge, pushPart]

theorem termOk_push (r : TreeRun) (p : TreePart) (h : TermOk r) (h1 : termK p.kind = false) (h2 : oldK p.kind = false) :
    TermOk (pushPart r p) := by
  obtain ⟨a, b⟩ := h
  refine ⟨?_, ?_⟩
  · simp only [termCharge_push, h1, Bool.false_eq_true, ite_false, Nat.add_zero]; exact a
  · simp only [oldValCharge_push, h2, Bool.false_eq_true, ite_false, Nat.add_zero]; exact b

theorem termOk_wrap (src : PTrie) (p : List Nat) (r : TreeRun) (h : TermOk r) : TermOk (wrapRun src p r) := by
  cases p with
  | nil => exact h
  | cons a as => exact termOk_push r _ h rfl rfl

theorem leafSplit_term (k : List Nat) (s : Slot) (m : Nat) (key : List Nat) (v : Bytes) :
    TermOk (leafSplitRun k s m key v) := by
  unfold leafSplitRun
  generalize commonPrefix k key = p
  dsimp only
  cases h1 : k.drop p.length <;> cases h2 : key.drop p.length <;> simp only [] <;>
    first
    | (apply termOk_wrap)
    | skip
  all_goals
    simp [TermOk, termCharge, oldValCharge, oldBound, terminalRun, termK, oldK]

theorem extSplit_term (k : List Nat) (c : PTrie) (m : Nat) (key : List Nat) (v : Bytes) :
    TermOk (extSplitRun k c m key v) := by
  unfold extSplitRun
  generalize commonPrefix k key = p
  dsimp only
  cases h1 : k.drop p.length with
  | nil => simp [TermOk, termCharge, oldValCharge, oldBound, terminalRun]
  | cons x xs =>
    cases h2 : key.drop p.length <;> simp only [] <;> apply termOk_wrap <;>
      cases xs <;> simp [TermOk, termCharge, oldValCharge, oldBound, terminalRun, termK, oldK] <;> split <;> simp

/-- The kids invariant. -/
def KidsOk (source : PTrie) (run : KidsRun) : Prop :=
  (run.inserted = true → termCharge run.inner = 0 ∧ oldValCharge run.inner = 0 ∧
      run.inner.terminalSource = source ∧ run.inner.terminal = .BI) ∧
    (run.inserted = false → TermOk run.inner)

mutual
theorem traceUpsert_term : ∀ (t : PTrie) (key : List Nat) (v : Bytes) (run : TreeRun),
    traceUpsert t key v = some run → TermOk run
  | .hash _, _, _, _, hr => by simp [traceUpsert] at hr
  | .leaf k s m, key, v, run, hr => by
    by_cases he : k = key
    · simp only [traceUpsert, he, ite_true, Option.some.injEq] at hr
      subst run
      simp [TermOk, termCharge, oldValCharge, oldBound, terminalRun, termK, oldK]
    · simp only [traceUpsert, he, ite_false, Option.some.injEq] at hr
      subst run
      exact leafSplit_term k s m key v
  | .ext k c m, key, v, run, hr => by
    cases hp : isPrefix k key with
    | false =>
      simp only [traceUpsert, hp, Bool.false_eq_true, ite_false, Option.some.injEq] at hr
      subst run
      exact extSplit_term k c m key v
    | true =>
      cases hm : c.mem? with
      | none => simp [traceUpsert, hp, hm] at hr
      | some cm =>
        cases hc : traceUpsert c (key.drop k.length) v with
        | none => simp [traceUpsert, hp, hm, hc] at hr
        | some inner =>
          simp only [traceUpsert, hp, ite_true, hm, hc, Option.some.injEq] at hr
          subst run
          exact termOk_push _ _ (traceUpsert_term c _ v inner hc) (by split <;> rfl) (by split <;> rfl)
  | .branch bv cs m, [], v, run, hr => by
    simp only [traceUpsert, Option.some.injEq] at hr
    subst run
    cases bv <;> simp [TermOk, termCharge, oldValCharge, oldBound, terminalRun, termK, oldK, NearSpecV3.ownVals,
      NearSpecV3.optSlotVal]
  | .branch bv cs m, n :: key, v, run, hr => by
    cases hc : traceKids (.branch bv cs m) (n :: key) cs n key v with
    | none => simp [traceUpsert, hc] at hr
    | some inner =>
      simp only [traceUpsert, hc, Option.map_some, Option.some.injEq] at hr
      subst run
      have h := traceKids_term (.branch bv cs m) (n :: key) cs n key v inner hc
      cases hi : inner.inserted with
      | true =>
        obtain ⟨h1, h2, h3, h4⟩ := h.1 hi
        unfold TermOk
        rw [termCharge_push, oldValCharge_push]
        simp only [hi, ite_true, termK, oldK, h1, h2, Bool.false_eq_true, ite_false, Nat.zero_add, Nat.add_zero]
        exact ⟨by show _ ≤ (NearSpecV3.nodeEnc inner.inner.terminalSource).length; rw [h3]; exact Nat.le_refl _, Nat.zero_le _⟩
      | false =>
        exact termOk_push _ _ (h.2 hi) (by simp [termK]) (by simp [oldK])

theorem traceKids_term : ∀ (source : PTrie) (wholeKey : List Nat) (cs : Kids) (n : Nat)
    (key : List Nat) (v : Bytes) (run : KidsRun),
    traceKids source wholeKey cs n key v = some run → KidsOk source run
  | _, _, .nil, _, _, _, _, hr => by simp [traceKids] at hr
  | source, wholeKey, .none rest, 0, key, v, run, hr => by
    simp only [traceKids, Option.some.injEq] at hr
    subst run
    unfold KidsOk
    refine ⟨fun _ => ?_, fun h => Bool.noConfusion h⟩
    simp [termCharge, oldValCharge, terminalRun, termK, oldK]
  | source, wholeKey, .some child rest, 0, key, v, run, hr => by
    cases hm : child.mem? with
    | none => simp [traceKids, hm] at hr
    | some cm =>
      cases hc : traceUpsert child key v with
      | none => simp [traceKids, hm, hc] at hr
      | some inner =>
        simp only [traceKids, hm, hc, Option.some.injEq] at hr
        subst run
        unfold KidsOk
        exact ⟨fun h => Bool.noConfusion h, fun _ => traceUpsert_term child key v inner hc⟩
  | source, wholeKey, .none rest, n + 1, key, v, run, hr => by
    cases hc : traceKids source wholeKey rest n key v with
    | none => simp [traceKids, hc] at hr
    | some inner =>
      simp only [traceKids, hc, Option.map_some, Option.some.injEq] at hr
      subst run
      exact traceKids_term source wholeKey rest n key v inner hc
  | source, wholeKey, .some child rest, n + 1, key, v, run, hr => by
    cases hc : traceKids source wholeKey rest n key v with
    | none => simp [traceKids, hc] at hr
    | some inner =>
      simp only [traceKids, hc, Option.map_some, Option.some.injEq] at hr
      subst run
      exact traceKids_term source wholeKey rest n key v inner hc
end

/-! ## Forest record lengths -/

theorem viewNode_ser_length (nid vid : Nat) (t : PTrie) (hn : isNode t = true) (post : Bool) :
    ((viewNode nid vid t).ser post).length = (NearSpecV3.nodeEnc t).length := by
  rw [← enc_eq]
  cases t with
  | hash => simp [isNode] at hn
  | leaf key value mem => simp [viewNode, NodeV3.ser, nodeEnc, u32Bytes, ZkFormal.Near.hpN]
  | ext key child mem => simp [viewNode, NodeV3.ser, nodeEnc, u32Bytes, ZkFormal.Near.hpN]
  | branch value kids mem => cases value <;> simp [viewNode, NodeV3.ser, nodeEnc] <;> omega

/-- Serialized length of the forest node record `n`. -/
def LT (Ts : List PTrie) (n : Nat) : Nat := (((forestNodes 0 0 0 Ts).getD n default).v.ser false).length

/-- A part source of a native forest upsert names a forest record of its own encoded length. -/
theorem source_record {Ts : List PTrie} {tau : Nat} {root : OccurrenceAddress}
    (hroot : forestRootAt 0 0 Ts tau = some root) {value : Bytes} {run : TreeRun}
    (hr : traceUpsert root.tree [0,15] value = some run) {p : TreePart} (hp : p ∈ run.parts) :
    let rid := pathRecordId (extendedAddresses root.nid root.vid root.depth root.tree [0,15])
    rid p.source < (forestNodes 0 0 0 Ts).length ∧
      (∃ d vid, (forestNodes 0 0 0 Ts)[rid p.source]? = some (seedNodeView tau d (rid p.source) vid p.source)) ∧
      LT Ts (rid p.source) = (NearSpecV3.nodeEnc p.source).length := by
  intro rid
  obtain ⟨a, -, hat, hid, hview⟩ := forest_traceUpsert_extended_provider hroot hr hp
  simp only [forestStoreViews] at hview
  have hn : isNode p.source = true := (traceUpsert_nodeParts _ _ _ _ hr p hp).1
  have hlt := (List.getElem?_eq_some_iff.mp hview).1
  have hget : (forestNodes 0 0 0 Ts).getD a.nid default = seedNodeView tau a.depth a.nid a.vid p.source := by
    simp [List.getD_eq_getElem?_getD, hview]
  refine ⟨by simp only [rid, hid]; exact hlt, ⟨a.depth, a.vid, by simp only [rid, hid]; exact hview⟩, ?_⟩
  · simp only [LT, rid, hid, hget, seedNodeView]
    exact viewNode_ser_length _ _ _ hn false

/-! ## The `RPL` ids of an instance cover its replaced path nodes -/

private def dP : TreePart := ⟨.RDB, .hash [], .hash [], 0⟩

/-- The instance part facts of a native instance. -/
theorem native_parts {rid : PTrie → Nat} {B : UpsInst} {root : PTrie} {value : Bytes} {run : TreeRun}
    {base : Nat → UpsPartI} {Qs : List UpsPartI}
    (hr : traceUpsert root [0,15] value = some run) (he : encodeNativeParts rid root run base = some Qs) :
    nQ (nativeInstance rid B root run value Qs) = run.parts.length ∧
    ∀ k (hk : k < run.parts.length),
      (part (nativeInstance rid B root run value Qs) k).sN = rid (run.parts[k]).source ∧
      (part (nativeInstance rid B root run value Qs) k).kind = (run.parts[k]).kind.ix := by
  have hlen := encodeNativeParts_length rid hr base he
  refine ⟨by simp [nQ, nativeInstance, signedInstance, positionedInstance, hlen], ?_⟩
  intro k hk
  obtain ⟨p, Q, hp, -, henc, hpq⟩ := nativeInstance_part rid B hr base he k (by omega)
  have hpk : run.parts[k] = p := by
    rw [List.getElem?_eq_getElem hk] at hp
    exact Option.some.inj hp
  rw [hpk, hpq]
  have hpos := encodeTreePart_positions henc
  have hkind := encodeTreePart_kind henc
  refine ⟨?_, ?_⟩
  · simp only [withMemorySign]; rw [hpos.2.2.2.1]; simp [positionedPart]
  · simp only [withMemorySign]; exact hkind

theorem native_nD {rid : PTrie → Nat} {B : UpsInst} {root : PTrie} {value : Bytes} {run : TreeRun}
    {Qs : List UpsPartI} (hD : (nativeInstance rid B root run value Qs).D < 3) :
    TrieA7.nDOf (nativeInstance rid B root run value Qs) = rid run.terminalSource := by
  have ht := sourceLevelIds_terminal rid run
  have e1 : (nativeInstance rid B root run value Qs).D = descentCount run.parts := rfl
  have e2 : (nativeInstance rid B root run value Qs).N = sourceLevelIds rid run := rfl
  rw [e1] at hD
  unfold TrieA7.nDOf
  rw [e1, e2]
  rcases (show descentCount run.parts = 0 ∨ descentCount run.parts = 1 ∨ descentCount run.parts = 2 by omega)
    with h | h | h <;> rw [h] at ht <;> simpa [h, List.getD_eq_getElem?_getD] using ht

theorem terminal_part {root : PTrie} {value : Bytes} {run : TreeRun}
    (hr : traceUpsert root [0,15] value = some run) : ∃ p ∈ run.parts, p.source = run.terminalSource := by
  have hpos := trace_parts_positive hr
  have hT := traceUpsert_terminalSources _ _ _ _ hr
  have hnT := termPlan_positive run.terminal run.matched
  obtain ⟨p, ps, hps⟩ : ∃ p ps, run.parts = p :: ps := by
    cases h : run.parts with
    | nil => simp [h] at hpos
    | cons p ps => exact ⟨p, ps, rfl⟩
  refine ⟨p, by simp [hps], hT p ?_⟩
  rw [hps]
  obtain ⟨n, hn⟩ : ∃ n, (UpsRows.termPlan run.terminal run.matched).length = n + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos hnT).symm⟩
  rw [hn]
  simp

theorem upK_upper (k : UpsRows.UKind) (h : upK k = true) : (k.ix == 0 || k.ix == 1 || k.ix == 11) = true := by
  cases k <;> simp_all [upK, UpsRows.UKind.ix]

/-- **The node half of A7 (b) step 2, one instance.** -/
theorem rpl_cover {Ts : List PTrie} {tau : Nat} {root : OccurrenceAddress} {u : SchedulerUpsertWitness}
    {I : UpsInst} (hroot : forestRootAt 0 0 Ts tau = some root)
    (hr : traceUpsert root.tree [0,15] u.value = some u.run)
    (ho : Rcpt.Candidates.NodePostUpdate.NativeReaderOrigin root u.run u.value I) (hio : InstOk I)
    (hP : (forestNodes 0 0 0 Ts).length < ZkFormal.Algebra.P) :
    replacedCharge u.run ≤ ((TrieA7.upsRplMsgs I).map fun b => LT Ts (b.getD 0 0)).sum := by
  obtain ⟨B, base, Qs, he, rfl⟩ := ho
  obtain ⟨hnQ, hpart⟩ := native_parts (B := B) hr he
  have hnD := native_nD hio.D
  have hmod : ∀ x, x < (forestNodes 0 0 0 Ts).length → x % ZkFormal.Algebra.P = x :=
    fun x hx => Nat.mod_eq_of_lt (by omega)
  obtain ⟨p0, hp0, hp0s⟩ := terminal_part hr
  obtain ⟨hlt0, -, hL0⟩ := source_record hroot hr hp0
  rw [hp0s] at hlt0 hL0
  generalize hIdef : nativeInstance _ B root.tree u.run u.value Qs = I at hnQ hpart hnD hio ⊢
  unfold TrieA7.upsRplMsgs
  rw [List.map_cons, List.sum_cons, List.map_flatMap, TrieA7.sum_flatMap_nat, hnD, hnQ]
  simp only [List.getD_cons_zero, hmod _ hlt0, hL0]
  rw [replaced_split]
  have hterm := (traceUpsert_term _ _ _ _ hr).1
  have hup : upCharge u.run ≤ ((List.range u.run.parts.length).map fun k =>
      (((if TrieA7.upperB (part I k) = true ∧ 0 < (part I k).q.length then [[(part I k).sN % ZkFormal.Algebra.P]]
        else []).map fun b => LT Ts (b.getD 0 0)).sum)).sum := by
    unfold upCharge
    rw [← ZkFormal.NearV3.Render.ValGen.map_getD dP
      (fun p => if upK p.kind then (NearSpecV3.nodeEnc p.source).length else 0) u.run.parts]
    apply TrieA7.sum_le_sum_of_le
    intro k hk
    have hk' : k < u.run.parts.length := List.mem_range.mp hk
    have hg : u.run.parts.getD k dP = u.run.parts[k] := by simp [List.getD_eq_getElem?_getD, hk']
    rw [hg]
    by_cases hu : upK (u.run.parts[k]).kind = true
    · obtain ⟨hsN, hkind⟩ := hpart k hk'
      have hq := hio.q1 k (by omega)
      have hub : TrieA7.upperB (part I k) = true := by
        unfold TrieA7.upperB; rw [hkind]; exact upK_upper _ hu
      obtain ⟨hlt, -, hL⟩ := source_record hroot hr (List.getElem_mem hk')
      simp only [hu, ite_true, hub, true_and, show 0 < (part I k).q.length by omega, hsN, hmod _ hlt,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.getD_cons_zero, hL]
      omega
    · simp only [hu, Bool.false_eq_true, ite_false]
      exact Nat.zero_le _
  exact Nat.add_le_add hterm hup

/-! ## Value ids and lengths of the forest node views -/

/-- `(value id, value length)` of a node view. -/
def vlens (s : NodeS3) : Option (Nat × Nat) := s.v.value.map fun y => (y.1, y.2.1)

/-- `(id, length)` of consecutive values from id `v`. -/
def idxLens : Nat → List Bytes → List (Nat × Nat)
  | _, [] => []
  | v, b :: bs => (v, b.length) :: idxLens (v + 1) bs

theorem idxLens_append : ∀ (v : Nat) (a b : List Bytes), idxLens v (a ++ b) = idxLens v a ++ idxLens (v + a.length) b
  | v, [], b => by simp [idxLens]
  | v, x :: xs, b => by
    simp only [List.cons_append, idxLens, idxLens_append (v + 1) xs b, List.length_cons]
    rw [show v + 1 + xs.length = v + (xs.length + 1) by omega]

theorem mem_idxLens : ∀ (v : Nat) (bs : List Bytes) (i l : Nat), (i, l) ∈ idxLens v bs →
    v ≤ i ∧ (bs[i - v]?).map List.length = some l
  | _, [], _, _, h => by simp [idxLens] at h
  | v, b :: bs, i, l, h => by
    simp only [idxLens, List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | h
    · simp
    · obtain ⟨h1, h2⟩ := mem_idxLens (v + 1) bs i l h
      refine ⟨by omega, ?_⟩
      have : i - v = (i - (v + 1)) + 1 := by omega
      rw [this, List.getElem?_cons_succ]
      exact h2

mutual
theorem seedNodesT_vlens (tau : Nat) : ∀ d n v t,
    (seedNodesT tau d n v t).filterMap vlens = idxLens v (valsOf t)
  | _,_,v,.hash _ => by simp [seedNodesT, valsOf, occs, idxLens]
  | d,n,v,.leaf k s m => by
    cases s <;> simp [seedNodesT, List.filterMap_cons, vlens, seedNodeView, viewNode, viewSlot, NodeV3.value,
      valsOf_leaf, slotVal, idxLens]
  | d,n,v,.ext k c m => by
    simp [seedNodesT, List.filterMap_cons, vlens, seedNodeView, viewNode, NodeV3.value, valsOf_ext,
      seedNodesT_vlens tau (d+1) (n+1) v c]
  | d,n,v,.branch sv cs m => by
    have ih := seedKidsT_vlens tau (d+1) (n+1) (v+(optSlotVal sv).length) cs
    cases sv with
    | none =>
      simpa [seedNodesT, List.filterMap_cons, vlens, seedNodeView, viewNode, NodeV3.value, valsOf_branch,
        optSlotVal] using ih
    | some s =>
      cases s <;> simp [seedNodesT, List.filterMap_cons, vlens, seedNodeView, viewNode, viewSlot, NodeV3.value,
        valsOf_branch, optSlotVal, slotVal, idxLens] at ih ⊢ <;> exact ih
theorem seedKidsT_vlens (tau : Nat) : ∀ d n v cs,
    (seedKidsT tau d n v cs).filterMap vlens = idxLens v (kvals cs)
  | _,_,v,.nil => by simp [seedKidsT, kvals_nil, idxLens]
  | d,n,v,.none rest => by simpa [seedKidsT, kvals_none] using seedKidsT_vlens tau d n v rest
  | d,n,v,.some c rest => by
    simp [seedKidsT, kvals_some, seedNodesT_vlens tau d n v c,
      seedKidsT_vlens tau d (n+tsize c) (v+(valsOf c).length) rest, idxLens_append]
end

theorem forestNodes_vlens : ∀ tau nid vid ts,
    (forestNodes tau nid vid ts).filterMap vlens = idxLens vid (forestBytes ts)
  | _, _, _, [] => by simp [forestNodes, forestBytes, idxLens]
  | tau, nid, vid, t :: ts => by
    simp only [forestNodes, List.filterMap_append, seedNodesT_vlens, forestNodes_vlens, forestBytes,
      List.flatMap_cons, idxLens_append]

/-- Length of the forest value `t`. -/
def LV (Ts : List PTrie) (t : Nat) : Nat := ((forestBytes Ts).getD t []).length

theorem forest_value_len {Ts : List PTrie} {s : NodeS3} (hs : s ∈ forestNodes 0 0 0 Ts)
    {y : Nat × Nat × List Nat × List Nat × Bool} (hy : s.v.value = some y) :
    y.1 < (forestBytes Ts).length ∧ LV Ts y.1 = y.2.1 := by
  have hm : (y.1, y.2.1) ∈ (forestNodes 0 0 0 Ts).filterMap vlens :=
    List.mem_filterMap.mpr ⟨s, hs, by simp [vlens, hy]⟩
  rw [forestNodes_vlens] at hm
  obtain ⟨-, h⟩ := mem_idxLens 0 _ _ _ hm
  simp only [Nat.sub_zero] at h
  cases hb : (forestBytes Ts)[y.1]? with
  | none => rw [hb] at h; cases h
  | some b =>
    rw [hb] at h
    simp only [Option.map_some, Option.some.injEq] at h
    refine ⟨(List.getElem?_eq_some_iff.mp hb).1, ?_⟩
    simp [LV, List.getD_eq_getElem?_getD, hb, h]

/-- The view's revealed value length is the node's own value length. -/
theorem view_value_len (n vid : Nat) (t : PTrie) :
    (match (viewNode n vid t).value with | some y => y.2.1 | none => 0) =
      ((NearSpecV3.ownVals t).map List.length).sum := by
  cases t with
  | hash => simp [viewNode, NodeV3.value, NearSpecV3.ownVals]
  | leaf k s m => cases s <;> simp [viewNode, viewSlot, NodeV3.value, NearSpecV3.ownVals, NearSpecV3.slotVal]
  | ext k c m => simp [viewNode, NodeV3.value, NearSpecV3.ownVals]
  | branch v cs m =>
    cases v with
    | none => simp [viewNode, NodeV3.value, NearSpecV3.ownVals, NearSpecV3.optSlotVal]
    | some s => cases s <;> simp [viewNode, viewSlot, NodeV3.value, NearSpecV3.ownVals, NearSpecV3.optSlotVal,
        NearSpecV3.slotVal]

/-! ## The `RPLV` id of an instance covers its overwritten value -/

/-- **The value half of A7 (b) step 2, one instance.** -/
theorem rplv_cover {pairs : List (PTrie × PTrie)} {tau : Nat} {root : OccurrenceAddress}
    {u : SchedulerUpsertWitness} {I : UpsInst}
    (hroot : forestRootAt 0 0 (pairs.map Prod.fst) tau = some root)
    (hr : traceUpsert root.tree [0,15] u.value = some u.run)
    (ho : Rcpt.Candidates.NodePostUpdate.NativeReaderOrigin root u.run u.value I) (hio : InstOk I)
    (hwp : NativeWalkProviders pairs u.run I)
    (hPV : (forestBytes (pairs.map Prod.fst)).length < ZkFormal.Algebra.P) :
    oldValCharge u.run ≤ ((TrieA7.upsRplvMsgs I).map fun b => LV (pairs.map Prod.fst) (b.getD 0 0)).sum := by
  have hold := (traceUpsert_term _ _ _ _ hr).2
  generalize hTs : pairs.map Prod.fst = Ts at hroot hPV hwp
  cases hterm : u.run.terminal with
  | BV | BI | LSa | LSb | LSc | ESl0 | ESl1 | ESn0 | ESn1 =>
    simp only [oldBound, hterm] at hold
    omega
  | LP | BR =>
    have hci : I.ci = 0 ∨ I.ci = 1 := by
      obtain ⟨B, base, Qs, he, rfl⟩ := ho
      show u.run.terminal.ix = 0 ∨ u.run.terminal.ix = 1
      rw [hterm]; decide
    have hts : I.ts = 3 := by
      refine Decidable.byContradiction fun hne => ?_
      rcases hio.tsNib hne with h | h | h | h | h <;> omega
    have hmode : (step I 3).mode = 0 := by
      have := hio.walk.termCase.1.mpr hci
      rwa [hts] at this
    obtain ⟨a, s, -, hs, -, -, -, hdisj⟩ := hwp
    have he3 : (step I 3).e ∈ edgesOf3 a.nid s := by
      rcases hdisj with ⟨hbv, -⟩ | h
      · rcases hbv with h | h <;> rw [hterm] at h <;> cases h
      · rwa [hts] at h
    have hval := (hio.walk.stepE 3 (by decide) (by decide) hmode).2.2 rfl
    obtain ⟨he0, hsv⟩ := TrieA7.edge_val_id he3 hval
    have hlook := hio.walk.look 3 (by decide) (by decide) (by omega)
    have hD := hio.walk.termD
    rw [hts] at hD
    obtain ⟨p0, hp0, hp0s⟩ := terminal_part hr
    obtain ⟨-, ⟨d, vid, hview⟩, -⟩ := source_record hroot hr hp0
    rw [hp0s] at hview
    have hnid : a.nid = TrieA7.nDOf I := by
      have hnD : TrieA7.nDOf I = I.N.getD I.D 0 := by
        have := hio.D
        unfold TrieA7.nDOf
        rcases (show I.D = 0 ∨ I.D = 1 ∨ I.D = 2 by omega) with h | h | h <;> simp [h]
      rw [hnD, hD, ← hlook, he0]
    have hnD' : TrieA7.nDOf I = pathRecordId (extendedAddresses root.nid root.vid root.depth root.tree [0,15])
        u.run.terminalSource := by
      obtain ⟨B, base, Qs, he, rfl⟩ := ho
      exact native_nD hio.D
    simp only [forestStoreViews] at hs
    rw [hTs] at hs
    have hmemS : s ∈ forestNodes 0 0 0 Ts := List.mem_of_getElem? hs
    rw [hnid, hnD', hview] at hs
    have hseq := (Option.some.inj hs).symm
    have hb := view_value_len (pathRecordId (extendedAddresses root.nid root.vid root.depth root.tree [0,15])
      u.run.terminalSource) vid u.run.terminalSource
    have hsv' : s.v = viewNode (pathRecordId (extendedAddresses root.nid root.vid root.depth root.tree [0,15])
        u.run.terminalSource) vid u.run.terminalSource := by rw [hseq]; rfl
    unfold seedValueId at hsv
    cases hvv : s.v.value with
    | none => rw [hvv] at hsv; cases hsv
    | some y =>
      rw [hvv] at hsv
      have hy1 : y.1 = (step I 3).e.getD 3 0 := Option.some.inj hsv
      obtain ⟨hylt, hyl⟩ := forest_value_len hmemS hvv
      rw [← hsv', hvv] at hb
      simp only [oldBound, hterm] at hold
      unfold TrieA7.upsRplvMsgs
      rw [if_pos hmode, ← hy1, Nat.mod_eq_of_lt (by omega)]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.getD_cons_zero, hyl]
      dsimp only at hb
      omega

end ZkFormal.NearV3.Assembly.TrieA7Match
