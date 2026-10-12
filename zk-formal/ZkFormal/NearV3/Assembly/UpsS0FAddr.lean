import ZkFormal.NearV3.Assembly.SchedulerPriorValueId
import ZkFormal.NearV3.Assembly.SourceCoverage
import ZkFormal.NearV3.Render.Ups.NativeValueEdge

/-!
# Ups `S0F` contents of a native scheduler upsert (completeness side)

The ups table sends `S0F (τ, pres, vid)` with `pres = [step 3 is a present lookup]` and
`vid = (step 3).e[3]`.  For the native instance of a scheduler upsert of the pre tree at forest
position `τ` (`nativeInstance … (nativeWalkBase … (fun _ => a.vid) …)`, `a` the terminal source's
occurrence address):
* `step3_mode`: for any `InstOk` instance, step 3 is a present lookup iff the case is `LP`/`BR`;
* `trace_val_present`: an `LP`/`BR` terminal reads a present value (`find ≠ some none`);
* `trace_val_addr`: a present value gives an `LP`/`BR` terminal whose source's occurrence address
  (every one on the key path) carries the value id `root.vid + valueIndex t key`;
* **`s0f_vid`**: the instance's step-3 target is `priorValueId (ts.take τ) t` — the codec's value id.
-/
namespace ZkFormal.NearV3.Assembly.UpsS0F
open NearSpec NearSpecV3 ZkFormal.Near ZkFormal.NearV3.Render Render.UpsGen UpsRows ZkFormal.NearV3.Assembly
open ZkFormal.NearV3.Assembly.CodecDigest Rcpt.Candidates.NodePostUpdate

/-- A present-value terminal (`LP` or `BR`). -/
def IsVal (run : TreeRun) : Prop := run.terminal = .LP ∨ run.terminal = .BR

theorem ix_le_one (c : UCase) : c.ix ≤ 1 ↔ (c = .LP ∨ c = .BR) := by
  cases c <;> simp [UCase.ix]

/-- Step 3 of an `InstOk` instance is a present lookup iff its case is `LP`/`BR`. -/
theorem step3_mode (I : UpsInst) (h : InstOk I) : (step I 3).mode = 0 ↔ I.ci ≤ 1 := by
  obtain ⟨h1, h3⟩ := h.ts
  by_cases ht : I.ts = 3
  · have hc := h.walk.termCase.1
    rw [ht] at hc
    rw [hc]
    omega
  · have hci : 1 < I.ci := by rcases h.tsNib ht with h | h | h | h | h <;> omega
    have hts : (step I I.ts).mode ≠ 0 := fun hm => by
      have := h.walk.termCase.1.mp hm
      omega
    have hd := h.walk.drain
    have h3' : (step I 3).mode = 3 := by
      rcases (show I.ts = 1 ∨ I.ts = 2 by omega) with e | e
      · rw [e] at hts
        have h2 : (step I 2).mode = 3 := hd 1 (Nat.le_refl _) (by decide) hts
        exact hd 2 (by decide) (by decide) (by rw [h2]; decide)
      · rw [e] at hts
        exact hd 2 (by decide) (by decide) hts
    rw [h3']
    omega

theorem leafSplitRun_notVal (k : List Nat) (s : Slot) (m : Nat) (key : List Nat) (v : Bytes)
    (hne : k ≠ key) : ¬IsVal (leafSplitRun k s m key v) := by
  have hleft := commonPrefix_left k key
  have hright := commonPrefix_right k key
  unfold leafSplitRun
  generalize commonPrefix k key = p at *
  cases h1 : k.drop p.length <;> cases h2 : key.drop p.length <;> simp only [h1, h2]
  · simp only [h1, h2, List.append_nil] at hleft hright
    exact (hne (hleft.trans hright.symm)).elim
  all_goals cases p <;> simp [IsVal, terminalRun, wrapRun, pushPart]

theorem extSplitRun_notVal (k : List Nat) (c : PTrie) (m : Nat) (key : List Nat) (v : Bytes) :
    ¬IsVal (extSplitRun k c m key v) := by
  intro h
  unfold extSplitRun at h
  dsimp only at h
  generalize commonPrefix k key = p at h
  cases h1 : k.drop p.length with
  | nil => rw [h1] at h; simp [IsVal, terminalRun] at h
  | cons x xs =>
    rw [h1] at h
    cases h2 : key.drop p.length <;> rw [h2] at h <;> cases xs <;> cases p <;>
      simp [IsVal, terminalRun, wrapRun, pushPart] at h

mutual
/-- An `LP`/`BR` terminal reads a present value. -/
theorem trace_val_present : ∀ (t : PTrie) (key : List Nat) (v : Bytes) (run : TreeRun),
    traceUpsert t key v = some run → IsVal run → t.find key ≠ some none
  | .hash _, _, _, _, hr, _ => by simp [traceUpsert] at hr
  | .leaf k s m, key, v, run, hr, hval => by
    by_cases he : k = key
    · intro hf
      cases s <;> simp [PTrie.find, he, Slot.get] at hf
    · simp only [traceUpsert, he, ite_false, Option.some.injEq] at hr
      subst run
      exact (leafSplitRun_notVal k s m key v he hval).elim
  | .ext k c m, key, v, run, hr, hval => by
    cases hp : isPrefix k key with
    | false =>
      simp only [traceUpsert, hp, Bool.false_eq_true, ite_false, Option.some.injEq] at hr
      subst run
      exact (extSplitRun_notVal k c m key v hval).elim
    | true =>
      cases hm : c.mem? with
      | none => simp [traceUpsert, hp, hm] at hr
      | some cm =>
        cases hc : traceUpsert c (key.drop k.length) v with
        | none => simp [traceUpsert, hp, hm, hc] at hr
        | some inner =>
          simp only [traceUpsert, hp, ite_true, hm, hc, Option.some.injEq] at hr
          subst run
          have := trace_val_present c _ v inner hc hval
          simpa [PTrie.find, hp] using this
  | .branch bv cs m, [], v, run, hr, hval => by
    simp only [traceUpsert, Option.some.injEq] at hr
    subst run
    intro hf
    cases bv with
    | none => simp [IsVal, terminalRun] at hval
    | some s => cases s <;> simp [PTrie.find, Slot.get] at hf
  | .branch bv cs m, n :: key, v, run, hr, hval => by
    cases hc : traceKids (.branch bv cs m) (n :: key) cs n key v with
    | none => simp [traceUpsert, hc] at hr
    | some inner =>
      simp only [traceUpsert, hc, Option.map_some, Option.some.injEq] at hr
      subst run
      exact trace_kids_val_present _ _ cs n key v inner hc hval
theorem trace_kids_val_present : ∀ (source : PTrie) (wholeKey : List Nat) (cs : Kids) (n : Nat)
    (key : List Nat) (v : Bytes) (run : KidsRun), traceKids source wholeKey cs n key v = some run →
    IsVal run.inner → Kids.find cs n key ≠ some none
  | _, _, .nil, _, _, _, _, hr, _ => by simp [traceKids] at hr
  | source, wholeKey, .none rest, 0, key, v, run, hr, hval => by
    simp only [traceKids, Option.some.injEq] at hr
    subst run
    simp [IsVal, terminalRun] at hval
  | source, wholeKey, .some child rest, 0, key, v, run, hr, hval => by
    cases hm : child.mem? with
    | none => simp [traceKids, hm] at hr
    | some cm =>
      cases hc : traceUpsert child key v with
      | none => simp [traceKids, hm, hc] at hr
      | some inner =>
        simp only [traceKids, hm, hc, Option.some.injEq] at hr
        subst run
        exact trace_val_present child key v inner hc hval
  | source, wholeKey, .none rest, n+1, key, v, run, hr, hval => by
    cases hc : traceKids source wholeKey rest n key v with
    | none => simp [traceKids, hc] at hr
    | some inner =>
      simp only [traceKids, hc, Option.map_some, Option.some.injEq] at hr
      subst run
      exact trace_kids_val_present source wholeKey rest n key v inner hc hval
  | source, wholeKey, .some child rest, n+1, key, v, run, hr, hval => by
    cases hc : traceKids source wholeKey rest n key v with
    | none => simp [traceKids, hc] at hr
    | some inner =>
      simp only [traceKids, hc, Option.map_some, Option.some.injEq] at hr
      subst run
      exact trace_kids_val_present source wholeKey rest n key v inner hc hval
end

theorem optSlotVal_len (o : Option Slot) :
    (NearSpecV3.optSlotVal o).length = (ZkFormal.NearV3.optSlotVal o).length := by
  rcases o with _ | (_ | _) <;> rfl

theorem valsOf_len (t : PTrie) : (NearSpecV3.valsOf t).length = (ZkFormal.NearV3.valsOf t).length := by
  rw [native_valsOf_eq]

mutual
/-- **A present value's occurrence address.** A present read gives an `LP`/`BR` terminal, its source
has an occurrence address on the key path, and every such address carries the value id
`w + valueIndex t key`. -/
theorem trace_val_addr : ∀ (t : PTrie) (key : List Nat) (v : Bytes) (run : TreeRun),
    traceUpsert t key v = some run → (∃ b, t.find key = some (some b)) → ∀ n w d,
    IsVal run ∧ (∃ a ∈ sourceAddresses n w d t key, a.tree = run.terminalSource) ∧
    ∀ a ∈ sourceAddresses n w d t key, a.tree = run.terminalSource →
      w ≤ a.vid ∧ valueIndex t key = some (a.vid - w)
  | .hash _, _, _, _, hr, _ => by simp [traceUpsert] at hr
  | .leaf k s m, key, v, run, hr, hf => by
    intro n w d
    obtain ⟨b, hb⟩ := hf
    by_cases he : k = key
    · simp only [traceUpsert, he, ite_true, Option.some.injEq] at hr
      subst run
      cases s with
      | ref len hash => simp [PTrie.find, he, Slot.get] at hb
      | val bytes =>
        refine ⟨Or.inl rfl, ⟨⟨n, w, d, .leaf k (.val bytes) m⟩, by simp [sourceAddresses], by
          simp [terminalRun, he]⟩, ?_⟩
        intro a ha _
        simp only [sourceAddresses, List.mem_singleton] at ha
        subst a
        simp [valueIndex, he, slotValueIndex]
    · simp [PTrie.find, he] at hb
  | .ext k c m, key, v, run, hr, hf => by
    intro n w d
    obtain ⟨b, hb⟩ := hf
    cases hp : isPrefix k key with
    | false => simp [PTrie.find, hp] at hb
    | true =>
      cases hm : c.mem? with
      | none => simp [traceUpsert, hp, hm] at hr
      | some cm =>
        cases hc : traceUpsert c (key.drop k.length) v with
        | none => simp [traceUpsert, hp, hm, hc] at hr
        | some inner =>
          simp only [traceUpsert, hp, ite_true, hm, hc, Option.some.injEq] at hr
          subst run
          have hb' : c.find (key.drop k.length) = some (some b) := by simpa [PTrie.find, hp] using hb
          obtain ⟨hv, ⟨a0, ha0, he0⟩, hall⟩ := trace_val_addr c _ v inner hc ⟨b, hb'⟩ (n+1) w (d+1)
          refine ⟨hv, ⟨a0, ?_, he0⟩, ?_⟩
          · simp only [sourceAddresses, hp, ite_true]
            exact List.mem_cons_of_mem _ ha0
          · intro a ha hat
            simp only [sourceAddresses, hp, ite_true, List.mem_cons] at ha
            rcases ha with rfl | ha
            · have h1 := sourceAddresses_size _ _ _ _ _ a0 ha0
              have hat' : PTrie.ext k c m = inner.terminalSource := hat
              rw [he0, ← hat'] at h1
              simp only [tsize, occs, List.length_cons] at h1
              omega
            · obtain ⟨h1, h2⟩ := hall a ha hat
              refine ⟨h1, ?_⟩
              simp only [valueIndex, hp, ite_true]
              exact h2
  | .branch bv cs m, [], v, run, hr, hf => by
    intro n w d
    obtain ⟨b, hb⟩ := hf
    simp only [traceUpsert, Option.some.injEq] at hr
    subst run
    cases bv with
    | none => simp [PTrie.find] at hb
    | some s =>
      cases s with
      | ref len hash => simp [PTrie.find, Slot.get] at hb
      | val bytes =>
        refine ⟨Or.inr (by simp [terminalRun]), ⟨⟨n, w, d, .branch (some (.val bytes)) cs m⟩,
          by simp [sourceAddresses], by simp [terminalRun]⟩, ?_⟩
        intro a ha _
        simp only [sourceAddresses, List.mem_singleton] at ha
        subst a
        simp [valueIndex, optSlotValueIndex, slotValueIndex]
  | .branch bv cs m, j :: key, v, run, hr, hf => by
    intro n w d
    cases hc : traceKids (.branch bv cs m) (j :: key) cs j key v with
    | none => simp [traceUpsert, hc] at hr
    | some inner =>
      simp only [traceUpsert, hc, Option.map_some, Option.some.injEq] at hr
      subst run
      obtain ⟨hv, ⟨a0, ha0, he0⟩, hall⟩ := trace_kids_val_addr _ _ cs j key v inner hc hf
        (n+1) (w + (ZkFormal.NearV3.optSlotVal bv).length) (d+1)
      refine ⟨hv, ⟨a0, ?_, he0⟩, ?_⟩
      · simp only [sourceAddresses]
        exact List.mem_cons_of_mem _ ha0
      · intro a ha hat
        simp only [sourceAddresses, List.mem_cons] at ha
        rcases ha with rfl | ha
        · have h1 := kidSourceAddresses_size _ _ _ _ _ _ a0 ha0
          have hat' : PTrie.branch bv cs m = inner.inner.terminalSource := hat
          rw [he0, ← hat'] at h1
          simp only [tsize, ksize, occs, List.length_cons] at h1
          omega
        · obtain ⟨h1, h2⟩ := hall a ha hat
          refine ⟨by omega, ?_⟩
          show (kidValueIndex cs j key).map ((NearSpecV3.optSlotVal bv).length + ·) = _
          rw [h2, optSlotVal_len]
          simp only [Option.map_some, Option.some.injEq]
          omega
theorem trace_kids_val_addr : ∀ (source : PTrie) (wholeKey : List Nat) (cs : Kids) (j : Nat)
    (key : List Nat) (v : Bytes) (run : KidsRun), traceKids source wholeKey cs j key v = some run →
    (∃ b, Kids.find cs j key = some (some b)) → ∀ n w d,
    IsVal run.inner ∧ (∃ a ∈ kidSourceAddresses n w d cs j key, a.tree = run.inner.terminalSource) ∧
    ∀ a ∈ kidSourceAddresses n w d cs j key, a.tree = run.inner.terminalSource →
      w ≤ a.vid ∧ kidValueIndex cs j key = some (a.vid - w)
  | _, _, .nil, _, _, _, _, hr, _ => by simp [traceKids] at hr
  | source, wholeKey, .none rest, 0, key, v, run, hr, hf => by
    obtain ⟨b, hb⟩ := hf
    simp [Kids.find] at hb
  | source, wholeKey, .some child rest, 0, key, v, run, hr, hf => by
    intro n w d
    cases hm : child.mem? with
    | none => simp [traceKids, hm] at hr
    | some cm =>
      cases hc : traceUpsert child key v with
      | none => simp [traceKids, hm, hc] at hr
      | some inner =>
        simp only [traceKids, hm, hc, Option.some.injEq] at hr
        subst run
        exact trace_val_addr child key v inner hc hf n w d
  | source, wholeKey, .none rest, j+1, key, v, run, hr, hf => by
    intro n w d
    cases hc : traceKids source wholeKey rest j key v with
    | none => simp [traceKids, hc] at hr
    | some inner =>
      simp only [traceKids, hc, Option.map_some, Option.some.injEq] at hr
      subst run
      exact trace_kids_val_addr source wholeKey rest j key v inner hc hf n w d
  | source, wholeKey, .some child rest, j+1, key, v, run, hr, hf => by
    intro n w d
    cases hc : traceKids source wholeKey rest j key v with
    | none => simp [traceKids, hc] at hr
    | some inner =>
      simp only [traceKids, hc, Option.map_some, Option.some.injEq] at hr
      subst run
      obtain ⟨hv, ex, hall⟩ := trace_kids_val_addr source wholeKey rest j key v inner hc hf
        (n + tsize child) (w + (ZkFormal.NearV3.valsOf child).length) d
      refine ⟨hv, ex, fun a ha hat => ?_⟩
      obtain ⟨h1, h2⟩ := hall a ha hat
      refine ⟨by omega, ?_⟩
      show (kidValueIndex rest j key).map ((NearSpecV3.valsOf child).length + ·) = _
      rw [h2, valsOf_len]
      simp only [Option.map_some, Option.some.injEq]
      omega
end

/-- The value-id base of the forest root at position `i`. -/
theorem forestRootAt_vid : ∀ (n w : Nat) (ts : List PTrie) (i : Nat) (r : OccurrenceAddress),
    forestRootAt n w ts i = some r → r.vid = w + (forestBytes (ts.take i)).length
  | _, _, [], _, _, h => by simp [forestRootAt] at h
  | n, w, t :: ts, 0, r, h => by
    simp only [forestRootAt, Option.some.injEq] at h
    subst h
    simp [forestBytes]
  | n, w, t :: ts, i+1, r, h => by
    have ih := forestRootAt_vid _ _ ts i r h
    simp only [forestBytes, List.take_succ_cons, List.flatMap_cons, List.length_append] at ih ⊢
    omega

/-- The native step-3 target of a present-value terminal is the walk base's value id. -/
theorem nativeInstance_step3 (recordId : PTrie → Nat) (vid : Nat) (resolvedId : PTrie → Nat)
    (baseI : UpsInst) {root : PTrie} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert root [0,15] v = some run) (hfind : root.find [0,15] ≠ none) (hc : IsVal run)
    (Qs : List UpsPartI) :
    (step (nativeInstance recordId (nativeWalkBase recordId (fun _ => vid) resolvedId baseI root run v)
      root run v Qs) 3).e.getD 3 0 = vid := by
  let I := nativeInstance recordId baseI root run v Qs
  let target := nativeTerminalTarget (fun _ => vid) resolvedId run (recordId run.terminalSource)
  have hci : I.ci ≤ 1 := by rcases hc with hc | hc <;> change run.terminal.ix ≤ 1 <;> rw [hc] <;> decide
  have ht : I.ts = 3 := by
    have hn := (traceInstance_terminalCases hr baseI).2
    by_cases h : I.ts = 3
    · exact h
    · have hn' : I.ci = 3 ∨ I.ci = 4 ∨ I.ci = 6 ∨ I.ci = 9 ∨ I.ci = 10 := hn h
      omega
  change (step (withFourWalk I (terminalBitmap run) (terminalHasVal run)
    (nativePathEdgeKind run 0) (nativePathEdgeKind run (if walkEnter1 I then 1 else 0))
    target.1 target.2) 3).e.getD 3 0 = vid
  rw [fourWalk_value_terminal I _ _ _ _ _ _ ht hci]
  have hv := traceUpsert_valueTerminal root [0,15] v run hr hfind
  rcases hc with hc | hc
  · obtain ⟨key, bytes, mem, hs, -⟩ := hv.1 hc
    simp [target, nativeTerminalTarget, hc, hs]
  · obtain ⟨bytes, kids, mem, hs, -⟩ := hv.2 hc
    simp [target, nativeTerminalTarget, hc, hs]

/-- **The native `S0F` value id.** For the native instance of the upsert of `root.tree` (forest
position `τ` of `ts`), built on the terminal source's occurrence address `a`: on a present-value
terminal the step-3 target is the codec's `priorValueId (ts.take τ) root.tree`. -/
theorem s0f_vid {ts : List PTrie} {tau : Nat} {root : OccurrenceAddress}
    (hroot : forestRootAt 0 0 ts tau = some root) {value : Bytes} {run : TreeRun}
    (hr : traceUpsert root.tree [0,15] value = some run) (hf : root.tree.find [0,15] ≠ none)
    {a : OccurrenceAddress} (ha : a ∈ sourceAddresses root.nid root.vid root.depth root.tree [0,15])
    (he : a.tree = run.terminalSource) (hval : IsVal run)
    (recordId resolvedId : PTrie → Nat) (baseI : UpsInst) (Qs : List UpsPartI) :
    (step (nativeInstance recordId (nativeWalkBase recordId (fun _ => a.vid) resolvedId baseI root.tree run value)
      root.tree run value Qs) 3).e.getD 3 0 = priorValueId (ts.take tau) root.tree := by
  rw [nativeInstance_step3 recordId a.vid resolvedId baseI hr hf hval Qs]
  have hp := trace_val_present _ _ _ _ hr hval
  obtain ⟨b, hb⟩ : ∃ b, root.tree.find [0,15] = some (some b) := by
    cases h : root.tree.find [0,15] with
    | none => exact (hf h).elim
    | some x =>
      cases x with
      | none => exact (hp h).elim
      | some b => exact ⟨b, rfl⟩
  obtain ⟨-, -, hall⟩ := trace_val_addr root.tree [0,15] value run hr ⟨b, hb⟩ root.nid root.vid root.depth
  obtain ⟨h1, h2⟩ := hall a ha he
  have hv := forestRootAt_vid 0 0 ts tau root hroot
  unfold priorValueId
  rw [keyBwState_nibbles, h2]
  simp only [forestLookupVid]
  omega

/-- The ups `S0F` value id of a native scheduler instance: on a present-value terminal, the step-3
target is the codec's `priorValueId` over the instance's forest prefix. -/
def S0FVid (us : List SchedulerUpsertWitness) (tau : Nat) (u : SchedulerUpsertWitness) (I : UpsInst) : Prop :=
  IsVal u.run → (step I 3).e.getD 3 0 = priorValueId ((us.map SchedulerUpsertWitness.pre).take tau) u.pre

/-- The ups `S0F` payload `(pres, vid)` of an instance (`TrieUpsSched.presN`, `vidN`). -/
def s0fOf (I : UpsInst) : Nat × Nat :=
  (if (step I 3).mode = 0 then 1 else 0, if (step I 3).mode = 0 then (step I 3).e.getD 3 0 else 0)

/-- The codec's `S0F` payload `(pres, vid)` of the upsert of `pre` at forest prefix `before`. -/
def s0fPair (before : List PTrie) (pre : PTrie) : Nat × Nat :=
  match pre.find keyBwState with
  | some (some _) => (1, priorValueId before pre)
  | _ => (0, 0)

/-- **Per instance**: the ups `S0F` payload of a native scheduler instance is the codec's. -/
theorem s0fOf_native {us : List SchedulerUpsertWitness} {tau : Nat} {u : SchedulerUpsertWitness}
    {I : UpsInst} (hok : InstOk I) (hci : I.ci = u.run.terminal.ix) (hs : S0FVid us tau u I)
    (hv : u.Valid) :
    s0fOf I = s0fPair ((us.map SchedulerUpsertWitness.pre).take tau) u.pre := by
  have hm := step3_mode I hok
  rw [hci, ix_le_one] at hm
  have hr := hv.1
  obtain ⟨so, hsched, -⟩ := hv.2
  have hf := schedStep_write_known hsched
  by_cases hval : IsVal u.run
  · have hp := trace_val_present _ _ _ _ hr hval
    have hm0 : (step I 3).mode = 0 := hm.mpr hval
    cases h : u.pre.find keyBwState with
    | none => exact (hf h).elim
    | some x =>
      cases x with
      | none => exact (hp h).elim
      | some b =>
        simp only [s0fOf, s0fPair, h, hm0, ite_true]
        rw [hs hval]
  · have hm0 : ¬(step I 3).mode = 0 := fun h => hval (hm.mp h)
    cases h : u.pre.find keyBwState with
    | none => exact (hf h).elim
    | some x =>
      cases x with
      | none => simp [s0fOf, s0fPair, h, hm0]
      | some b =>
        exact (hval (trace_val_addr _ _ _ _ hr ⟨b, h⟩ 0 0 0).1).elim

end ZkFormal.NearV3.Assembly.UpsS0F
