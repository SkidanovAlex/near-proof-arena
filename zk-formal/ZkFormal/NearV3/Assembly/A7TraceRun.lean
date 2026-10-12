import ZkFormal.NearV3.Assembly.A7Match
import ZkFormal.NearV3.Extract.Ups.UpsLink
import ZkFormal.NearV3.Render.Ups.TreeTraceCorrect

/-!
# ZkFormal.NearV3.Assembly.A7TraceRun — `traceUpsert` one node at a time (run level, for (E1))

The instrumented upsert `traceUpsert`, node by node, given the facts the `upsV3` plan supplies
(`UpsUpsert` is the same for `PTrie.upsert`):

* **`trace_rdb`** / **`trace_ext`**: a descend through an occupied branch slot / an extension (pass-through
  for `[]`) pushes one part (`RDB` / `RDE` / `PT`) with the node as its source on the child's run;
* terminal nodes: **`trace_leaf_eq`** (`RLP`), **`trace_branch_nil`** (`RBR` / `RBV`), **`trace_rbi`** (`NLF` then
  `RBI`), and the split runs **`leafSplit_a/b/c`**, **`extSplit_l0/l1/n0/n1`**: their parts are the lower parts
  (`MVL`/`MVE`/`NLF`), the split branch `SPB`, and the wrapping extension `WEX` when the common prefix is
  non-empty (`wexL`); the run's output is `wrapExt p B`;
* **`trace_find_old`**: if the key's old value `w` is revealed (`find = some (some w)`), then
  `|w| ≤ oldValCharge run`;
* **`le_find_gap`**: for `LeTree a b` (same shape, `b`'s values no longer) and the values `wa`, `wb` found at the
  same key, `U b + |wa| ≤ U a + |wb|`.
-/

namespace ZkFormal.NearV3.Assembly.A7TraceRun

open NearSpec Render.UpsGen ZkFormal.NearV3.UpsSpec ZkFormal.NearV3.UpsRows TrieA7Post TrieA7Repl A7Post

/-! ## Descends -/

theorem kids_some : ∀ (src : PTrie) (wk : List Nat) (cs : Kids) (n : Nat) (key : List Nat) (v : Bytes)
    (c : PTrie) (cm : Nat) (run : TreeRun),
    kidAt cs n = some c → c.mem? = some cm → traceUpsert c key v = some run →
    ∃ kr, traceKids src wk cs n key v = some kr ∧ kr.inner = run ∧ kr.inserted = false
  | _, _, .nil, _, _, _, _, _, _, h, _, _ => by simp [kidAt] at h
  | _, _, .none r, 0, _, _, _, _, _, h, _, _ => by simp [kidAt] at h
  | src, wk, .some d r, 0, key, v, c, cm, run, h, hm, hr => by
    simp only [kidAt, Option.some.injEq] at h
    subst h
    exact ⟨⟨.some run.output r, cm, run.output.memD, run, false⟩, by simp [traceKids, hm, hr], rfl, rfl⟩
  | src, wk, .none r, n + 1, key, v, c, cm, run, h, hm, hr => by
    simp only [kidAt] at h
    obtain ⟨kr, hk, h1, h2⟩ := kids_some src wk r n key v c cm run h hm hr
    exact ⟨{kr with output := .none kr.output}, by simp [traceKids, hk], h1, h2⟩
  | src, wk, .some d r, n + 1, key, v, c, cm, run, h, hm, hr => by
    simp only [kidAt] at h
    obtain ⟨kr, hk, h1, h2⟩ := kids_some src wk r n key v c cm run h hm hr
    exact ⟨{kr with output := .some d kr.output}, by simp [traceKids, hk], h1, h2⟩

theorem kids_none : ∀ (src : PTrie) (wk : List Nat) (cs : Kids) (n : Nat) (key : List Nat) (v : Bytes),
    n < kidsLen cs → kidAt cs n = none →
    ∃ kr, traceKids src wk cs n key v = some kr ∧ kr.inserted = true ∧
      kr.inner = terminalRun src wk .BI 0 (newLeaf key v) [⟨.NLF, src, newLeaf key v, 0⟩]
  | _, _, .nil, _, _, _, hl, _ => by simp [kidsLen] at hl
  | src, wk, .none r, 0, key, v, _, _ => ⟨_, rfl, rfl, rfl⟩
  | _, _, .some d r, 0, _, _, _, h => by simp [kidAt] at h
  | src, wk, .none r, n + 1, key, v, hl, h => by
    simp only [kidAt] at h; simp only [kidsLen] at hl
    obtain ⟨kr, hk, h1, h2⟩ := kids_none src wk r n key v (by omega) h
    exact ⟨{kr with output := .none kr.output}, by simp [traceKids, hk], h1, h2⟩
  | src, wk, .some d r, n + 1, key, v, hl, h => by
    simp only [kidAt] at h; simp only [kidsLen] at hl
    obtain ⟨kr, hk, h1, h2⟩ := kids_none src wk r n key v (by omega) h
    exact ⟨{kr with output := .some d kr.output}, by simp [traceKids, hk], h1, h2⟩

/-- **A descend through a branch slot.** -/
theorem trace_rdb (bv : Option Slot) (cs : Kids) (m n : Nat) (rest : List Nat) (v : Bytes) (c : PTrie) (cm : Nat)
    (run : TreeRun) (hc : kidAt cs n = some c) (hm : c.mem? = some cm) (hr : traceUpsert c rest v = some run) :
    ∃ q : TreePart, traceUpsert (.branch bv cs m) (n :: rest) v = some (pushPart run q) ∧ q.kind = .RDB ∧
      q.source = .branch bv cs m := by
  obtain ⟨kr, hk, h1, h2⟩ := kids_some (.branch bv cs m) (n :: rest) cs n rest v c cm run hc hm hr
  exact ⟨⟨.RDB, .branch bv cs m, .branch bv kr.output (m + kr.newMem - kr.oldMem), n⟩,
    by simp [traceUpsert, hk, h1, h2], rfl, rfl⟩

/-- **A descend through an extension** (a pass-through for `k = []`). -/
theorem trace_ext (k : List Nat) (c : PTrie) (m : Nat) (key : List Nat) (v : Bytes) (cm : Nat) (run : TreeRun)
    (hk : key.take k.length = k) (hm : c.mem? = some cm) (hr : traceUpsert c (key.drop k.length) v = some run) :
    ∃ q : TreePart, traceUpsert (.ext k c m) key v = some (pushPart run q) ∧
      q.kind = (if k.isEmpty then .PT else .RDE) ∧ q.source = .ext k c m := by
  have hp : isPrefix k key = true := by
    rw [isPrefix_iff]; exact ⟨key.drop k.length, by conv => lhs; rw [← List.take_append_drop k.length key, hk]⟩
  exact ⟨⟨if k.isEmpty then .PT else .RDE, .ext k c m, qRDE k m run.output cm, 0⟩,
    by simp [traceUpsert, hp, hm, hr], rfl, rfl⟩

/-! ## Terminal nodes -/

theorem trace_leaf_eq (k : List Nat) (s : Slot) (m : Nat) (v : Bytes) :
    traceUpsert (.leaf k s m) k v = some (terminalRun (.leaf k s m) k .LP k.length (newLeaf k v)
      [⟨.RLP, .leaf k s m, newLeaf k v, 0⟩]) := by
  simp [traceUpsert]

theorem trace_branch_nil (bv : Option Slot) (cs : Kids) (m : Nat) (v : Bytes) :
    ∃ run, traceUpsert (.branch bv cs m) [] v = some run ∧
      run.parts = [⟨if bv.isSome then .RBR else .RBV, .branch bv cs m, run.output, 0⟩] :=
  ⟨_, rfl, rfl⟩

/-- **An empty branch slot**: the new leaf, then `RBI`. -/
theorem trace_rbi (bv : Option Slot) (cs : Kids) (m n : Nat) (key : List Nat) (v : Bytes)
    (hl : n < kidsLen cs) (hy : kidAt cs n = none) :
    ∃ run, traceUpsert (.branch bv cs m) (n :: key) v = some run ∧
      run.parts = [⟨.NLF, .branch bv cs m, newLeaf key v, 0⟩, ⟨.RBI, .branch bv cs m, run.output, n⟩] := by
  obtain ⟨kr, hk, h1, h2⟩ := kids_none (.branch bv cs m) (n :: key) cs n key v hl hy
  refine ⟨pushPart kr.inner ⟨if kr.inserted then .RBI else .RDB, .branch bv cs m,
    .branch bv kr.output (m + kr.newMem - kr.oldMem), n⟩, by simp [traceUpsert, hk], ?_⟩
  simp [h1, h2, pushPart, terminalRun]

/-- The wrapping extension part, when the common prefix is non-empty. -/
def wexL (src : PTrie) (p : List Nat) (B : PTrie) : List TreePart :=
  match p with
  | [] => []
  | _ :: _ => [⟨.WEX, src, wrapExt p B, 0⟩]

theorem wexL_length (src : PTrie) (p : List Nat) (B : PTrie) :
    (wexL src p B).length = if p = [] then 0 else 1 := by
  cases p <;> rfl

theorem wrapRun_term (src : PTrie) (p key : List Nat) (cs : UCase) (mt : Nat) (B : PTrie) (l : List TreePart) :
    (wrapRun src p (terminalRun src key cs mt B l)).parts = l ++ wexL src p B ∧
      (wrapRun src p (terminalRun src key cs mt B l)).output = wrapExt p B := by
  cases p <;> simp [wrapRun, terminalRun, wexL, pushPart, wrapExt]

theorem wrapExt_inj (p : List Nat) {a b : PTrie} (h : wrapExt p a = wrapExt p b) : a = b := by
  cases p with
  | nil => exact h
  | cons x xs => simp only [wrapExt, PTrie.ext.injEq] at h; exact h.2.1

/-- `LSa`: the leaf's key ends at the common prefix. -/
theorem leafSplit_a (k : List Nat) (s : Slot) (m : Nat) (key : List Nat) (v : Bytes) (y : Nat) (ys : List Nat)
    (h1 : k.drop (commonPrefix k key).length = []) (h2 : key.drop (commonPrefix k key).length = y :: ys) :
    ∃ B, (leafSplitRun k s m key v).parts =
        [⟨.NLF, .leaf k s m, newLeaf ys v, 0⟩, ⟨.SPB, .leaf k s m, B, 0⟩] ++ wexL (.leaf k s m) (commonPrefix k key) B ∧
      (leafSplitRun k s m key v).output = wrapExt (commonPrefix k key) B := by
  unfold leafSplitRun
  generalize commonPrefix k key = p at h1 h2 ⊢
  simp only [h1, h2]
  exact ⟨_, wrapRun_term _ _ _ _ _ _ _⟩

/-- `LSb`: the lookup key ends at the common prefix. -/
theorem leafSplit_b (k : List Nat) (s : Slot) (m : Nat) (key : List Nat) (v : Bytes) (x : Nat) (xs : List Nat)
    (h1 : k.drop (commonPrefix k key).length = x :: xs) (h2 : key.drop (commonPrefix k key).length = []) :
    ∃ B, (leafSplitRun k s m key v).parts =
        [⟨.MVL, .leaf k s m, .leaf xs s (leafMem xs s.len), 0⟩, ⟨.SPB, .leaf k s m, B, 0⟩] ++
          wexL (.leaf k s m) (commonPrefix k key) B ∧
      (leafSplitRun k s m key v).output = wrapExt (commonPrefix k key) B := by
  unfold leafSplitRun
  generalize commonPrefix k key = p at h1 h2 ⊢
  simp only [h1, h2]
  exact ⟨_, wrapRun_term _ _ _ _ _ _ _⟩

/-- `LSc`: the keys differ at the common prefix. -/
theorem leafSplit_c (k : List Nat) (s : Slot) (m : Nat) (key : List Nat) (v : Bytes) (x : Nat) (xs : List Nat)
    (y : Nat) (ys : List Nat)
    (h1 : k.drop (commonPrefix k key).length = x :: xs) (h2 : key.drop (commonPrefix k key).length = y :: ys) :
    ∃ B, (leafSplitRun k s m key v).parts =
        [⟨.MVL, .leaf k s m, .leaf xs s (leafMem xs s.len), 0⟩, ⟨.NLF, .leaf k s m, newLeaf ys v, 0⟩,
          ⟨.SPB, .leaf k s m, B, 0⟩] ++ wexL (.leaf k s m) (commonPrefix k key) B ∧
      (leafSplitRun k s m key v).output = wrapExt (commonPrefix k key) B := by
  unfold leafSplitRun
  generalize commonPrefix k key = p at h1 h2 ⊢
  simp only [h1, h2]
  exact ⟨_, wrapRun_term _ _ _ _ _ _ _⟩

/-- `ESl0`: the lookup key ends; the extension keeps nibbles after `x`. -/
theorem extSplit_l0 (k : List Nat) (c : PTrie) (m : Nat) (key : List Nat) (v : Bytes) (x x' : Nat) (xs : List Nat)
    (h1 : k.drop (commonPrefix k key).length = x :: x' :: xs) (h2 : key.drop (commonPrefix k key).length = []) :
    ∃ B, (extSplitRun k c m key v).parts =
        [⟨.MVE, .ext k c m, .ext (x' :: xs) c (extOwnMem (x' :: xs) + (m - extOwnMem k)), 0⟩,
          ⟨.SPB, .ext k c m, B, 0⟩] ++ wexL (.ext k c m) (commonPrefix k key) B ∧
      (extSplitRun k c m key v).output = wrapExt (commonPrefix k key) B := by
  unfold extSplitRun
  generalize commonPrefix k key = p at h1 h2 ⊢
  simp only [h1, h2]
  exact ⟨_, wrapRun_term _ _ _ _ _ _ _⟩

/-- `ESl1`: the lookup key ends one nibble before the extension's key. -/
theorem extSplit_l1 (k : List Nat) (c : PTrie) (m : Nat) (key : List Nat) (v : Bytes) (x : Nat)
    (h1 : k.drop (commonPrefix k key).length = [x]) (h2 : key.drop (commonPrefix k key).length = []) :
    ∃ B, (extSplitRun k c m key v).parts =
        [⟨.SPB, .ext k c m, B, 0⟩] ++ wexL (.ext k c m) (commonPrefix k key) B ∧
      (extSplitRun k c m key v).output = wrapExt (commonPrefix k key) B := by
  unfold extSplitRun
  generalize commonPrefix k key = p at h1 h2 ⊢
  simp only [h1, h2]
  exact ⟨_, wrapRun_term _ _ _ _ _ _ _⟩

/-- `ESn0`: the keys differ; the extension keeps nibbles after `x`. -/
theorem extSplit_n0 (k : List Nat) (c : PTrie) (m : Nat) (key : List Nat) (v : Bytes) (x x' : Nat) (xs : List Nat)
    (y : Nat) (ys : List Nat)
    (h1 : k.drop (commonPrefix k key).length = x :: x' :: xs) (h2 : key.drop (commonPrefix k key).length = y :: ys) :
    ∃ B, (extSplitRun k c m key v).parts =
        [⟨.MVE, .ext k c m, .ext (x' :: xs) c (extOwnMem (x' :: xs) + (m - extOwnMem k)), 0⟩,
          ⟨.NLF, .ext k c m, newLeaf ys v, 0⟩, ⟨.SPB, .ext k c m, B, 0⟩] ++ wexL (.ext k c m) (commonPrefix k key) B ∧
      (extSplitRun k c m key v).output = wrapExt (commonPrefix k key) B := by
  unfold extSplitRun
  generalize commonPrefix k key = p at h1 h2 ⊢
  simp only [h1, h2]
  exact ⟨_, wrapRun_term _ _ _ _ _ _ _⟩

/-- `ESn1`: the keys differ at the extension's last nibble. -/
theorem extSplit_n1 (k : List Nat) (c : PTrie) (m : Nat) (key : List Nat) (v : Bytes) (x : Nat)
    (y : Nat) (ys : List Nat)
    (h1 : k.drop (commonPrefix k key).length = [x]) (h2 : key.drop (commonPrefix k key).length = y :: ys) :
    ∃ B, (extSplitRun k c m key v).parts =
        [⟨.NLF, .ext k c m, newLeaf ys v, 0⟩, ⟨.SPB, .ext k c m, B, 0⟩] ++ wexL (.ext k c m) (commonPrefix k key) B ∧
      (extSplitRun k c m key v).output = wrapExt (commonPrefix k key) B := by
  unfold extSplitRun
  generalize commonPrefix k key = p at h1 h2 ⊢
  simp only [h1, h2]
  exact ⟨_, wrapRun_term _ _ _ _ _ _ _⟩

theorem trace_leaf_ne (k : List Nat) (s : Slot) (m : Nat) (key : List Nat) (v : Bytes) (h : k ≠ key) :
    traceUpsert (.leaf k s m) key v = some (leafSplitRun k s m key v) := by
  simp [traceUpsert, h]

theorem trace_ext_ne (k : List Nat) (c : PTrie) (m : Nat) (key : List Nat) (v : Bytes)
    (hne : key.take k.length ≠ k) :
    traceUpsert (.ext k c m) key v = some (extSplitRun k c m key v) := by
  have hp : isPrefix k key = false := by
    cases h : isPrefix k key with
    | false => rfl
    | true =>
      exfalso
      obtain ⟨r, hr⟩ := (isPrefix_iff k key).1 h
      apply hne; rw [hr]; simp
  simp [traceUpsert, hp]

/-! ## The overwritten value -/

mutual
theorem trace_find_old : ∀ (t : PTrie) (key : List Nat) (v : Bytes) (run : TreeRun) (w : Bytes),
    traceUpsert t key v = some run → t.find key = some (some w) → w.length ≤ oldValCharge run
  | .hash _, _, _, _, _, hr, _ => by simp [traceUpsert] at hr
  | .leaf k s m, key, v, run, w, hr, hf => by
    by_cases he : k = key
    · subst he
      simp only [traceUpsert, ite_true, Option.some.injEq] at hr
      subst run
      simp only [PTrie.find, ite_true] at hf
      cases s with
      | ref _ _ => simp [Slot.get] at hf
      | val w' =>
        simp only [Slot.get, Option.map_some, Option.some.injEq] at hf
        subst hf
        simp [oldValCharge, terminalRun, oldK, NearSpecV3.ownVals, NearSpecV3.slotVal]
    · simp [PTrie.find, he] at hf
  | .ext k c m, key, v, run, w, hr, hf => by
    cases hp : isPrefix k key with
    | false => simp [PTrie.find, hp] at hf
    | true =>
      simp only [PTrie.find, hp, ite_true] at hf
      cases hm : c.mem? with
      | none => simp [traceUpsert, hp, hm] at hr
      | some cm =>
        cases hc : traceUpsert c (key.drop k.length) v with
        | none => simp [traceUpsert, hp, hm, hc] at hr
        | some inner =>
          simp only [traceUpsert, hp, ite_true, hm, hc, Option.some.injEq] at hr
          subst run
          have h := trace_find_old c _ v inner w hc hf
          rw [oldValCharge_push]; omega
  | .branch bv cs m, [], v, run, w, hr, hf => by
    simp only [traceUpsert, Option.some.injEq] at hr
    subst run
    cases bv with
    | none => simp [PTrie.find] at hf
    | some s =>
      cases s with
      | ref _ _ => simp [PTrie.find, Slot.get] at hf
      | val w' =>
        simp only [PTrie.find, Slot.get, Option.map_some, Option.some.injEq] at hf
        subst hf
        simp [oldValCharge, terminalRun, oldK, NearSpecV3.ownVals, NearSpecV3.optSlotVal, NearSpecV3.slotVal]
  | .branch bv cs m, n :: key, v, run, w, hr, hf => by
    simp only [PTrie.find] at hf
    cases hc : traceKids (.branch bv cs m) (n :: key) cs n key v with
    | none => simp [traceUpsert, hc] at hr
    | some inner =>
      simp only [traceUpsert, hc, Option.map_some, Option.some.injEq] at hr
      subst run
      have h := kids_find_old (.branch bv cs m) (n :: key) cs n key v inner w hc hf
      rw [oldValCharge_push]; omega
theorem kids_find_old : ∀ (source : PTrie) (wholeKey : List Nat) (cs : Kids) (n : Nat)
    (key : List Nat) (v : Bytes) (run : KidsRun) (w : Bytes),
    traceKids source wholeKey cs n key v = some run → Kids.find cs n key = some (some w) →
    w.length ≤ oldValCharge run.inner
  | _, _, .nil, _, _, _, _, _, hr, _ => by simp [traceKids] at hr
  | _, _, .none rest, 0, _, _, _, _, _, hf => by simp [Kids.find] at hf
  | source, wholeKey, .some child rest, 0, key, v, run, w, hr, hf => by
    simp only [Kids.find] at hf
    cases hm : child.mem? with
    | none => simp [traceKids, hm] at hr
    | some cm =>
      cases hc : traceUpsert child key v with
      | none => simp [traceKids, hm, hc] at hr
      | some inner =>
        simp only [traceKids, hm, hc, Option.some.injEq] at hr
        subst run
        exact trace_find_old child key v inner w hc hf
  | source, wholeKey, .none rest, n + 1, key, v, run, w, hr, hf => by
    simp only [Kids.find] at hf
    cases hc : traceKids source wholeKey rest n key v with
    | none => simp [traceKids, hc] at hr
    | some inner =>
      simp only [traceKids, hc, Option.map_some, Option.some.injEq] at hr
      subst run
      exact kids_find_old source wholeKey rest n key v inner w hc hf
  | source, wholeKey, .some child rest, n + 1, key, v, run, w, hr, hf => by
    simp only [Kids.find] at hf
    cases hc : traceKids source wholeKey rest n key v with
    | none => simp [traceKids, hc] at hr
    | some inner =>
      simp only [traceKids, hc, Option.map_some, Option.some.injEq] at hr
      subst run
      exact kids_find_old source wholeKey rest n key v inner w hc hf
end

/-! ## The gap of a shorter value -/

mutual
theorem le_find_gap : ∀ {a b : PTrie} (key : List Nat) (wa wb : Bytes), LeTree a b →
    a.find key = some (some wa) → b.find key = some (some wb) →
    NearSpecV3.unfoldedBytesT b + wa.length ≤ NearSpecV3.unfoldedBytesT a + wb.length
  | _, _, _, _, _, .hash _, ha, _ => by simp [PTrie.find] at ha
  | _, _, key, wa, wb, .leaf k m hs, ha, hb => by
    have e := le_node_length (.leaf k m hs)
    rw [U_leaf, U_leaf]
    by_cases he : k = key
    · simp only [PTrie.find, he, ite_true] at ha hb
      cases hs with
      | ref => simp [Slot.get] at ha
      | val hl =>
        simp only [Slot.get, Option.map_some, Option.some.injEq] at ha hb
        subst ha; subst hb
        simp only [NearSpecV3.slotVal, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        omega
    · simp [PTrie.find, he] at ha
  | _, _, key, wa, wb, .ext k m hc, ha, hb => by
    have e := le_node_length (.ext k m hc)
    rw [U_ext, U_ext]
    cases hp : isPrefix k key with
    | false => simp [PTrie.find, hp] at ha
    | true =>
      simp only [PTrie.find, hp, ite_true] at ha hb
      have := le_find_gap _ wa wb hc ha hb
      omega
  | _, _, key, wa, wb, @LeTree.branch a b cs ds m ho hs, ha, hb => by
    have e := le_node_length (.branch m ho hs)
    rw [U_branch, U_branch]
    cases key with
    | nil =>
      have hk := le_UK hs
      cases ho with
      | none => simp [PTrie.find] at ha
      | some hs' =>
        cases hs' with
        | ref => simp [PTrie.find, Slot.get] at ha
        | val hl =>
          simp only [PTrie.find, Slot.get, Option.map_some, Option.some.injEq] at ha hb
          subst ha; subst hb
          simp only [NearSpecV3.optSlotVal, NearSpecV3.slotVal, List.map_cons, List.map_nil, List.sum_cons,
            List.sum_nil]
          omega
    | cons n rest =>
      simp only [PTrie.find] at ha hb
      have := leK_find_gap n rest wa wb hs ha hb
      have hv : ((NearSpecV3.optSlotVal b).map List.length).sum ≤ ((NearSpecV3.optSlotVal a).map List.length).sum := by
        cases ho with
        | none => exact Nat.le_refl _
        | some hs' => exact slotVal_le hs'
      omega
theorem leK_find_gap : ∀ {cs ds : Kids} (n : Nat) (key : List Nat) (wa wb : Bytes), LeKids cs ds →
    Kids.find cs n key = some (some wa) → Kids.find ds n key = some (some wb) →
    UK ds + wa.length ≤ UK cs + wb.length
  | _, _, _, _, _, _, .nil, ha, _ => by simp [Kids.find] at ha
  | _, _, 0, _, _, _, .none _, ha, _ => by simp [Kids.find] at ha
  | _, _, n + 1, key, wa, wb, .none hs, ha, hb => by
    simp only [Kids.find] at ha hb
    rw [UK_none, UK_none]
    exact leK_find_gap n key wa wb hs ha hb
  | _, _, 0, key, wa, wb, .some hc hs, ha, hb => by
    simp only [Kids.find] at ha hb
    rw [UK_some, UK_some]
    have := le_find_gap key wa wb hc ha hb
    have := le_UK hs
    omega
  | _, _, n + 1, key, wa, wb, .some hc hs, ha, hb => by
    simp only [Kids.find] at ha hb
    rw [UK_some, UK_some]
    have := leK_find_gap n key wa wb hs ha hb
    have := le_U hc
    omega
end

end ZkFormal.NearV3.Assembly.A7TraceRun
