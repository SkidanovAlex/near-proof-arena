import ZkFormal.NearV3.Assembly.TrieA7Post

/-!
# ZkFormal.NearV3.Assembly.TrieA7Repl — per-upsert unfolded-bytes accounting (A7 (b), step 1)

**`traceUpsert_replaced`**: for a well-formed trie `t` and a nibble key, a successful
`traceUpsert t key v = some run` satisfies the exact identity

`unfoldedBytesT t + outputByteCharge run + |v| = unfoldedBytesT run.output + replacedCharge run + oldValCharge run`

where `replacedCharge run` sums `|nodeEnc p.source|` over the parts of the REPLACING kinds
`RDB/RDE/PT/RLP/RBR/RBV/RBI/SPB` (each pre node on the path is the source of exactly one of these;
a split's source — shared by its `NLF/MVL/MVE/WEX/SPB` parts — is counted once, through `SPB`; the
`NLF` of a branch insert, whose source is the branch, is not counted), and `oldValCharge run` sums
the revealed own values of the sources of the value-overwriting kinds `RLP/RBR/RBV`.  Off-path
subtrees are copied unchanged.  (`traceKids_replaced`: the kids version, with `TrieA7Post.UK`.)
-/

namespace ZkFormal.NearV3.Assembly.TrieA7Repl

open NearSpec NearSpecV3 Render.UpsGen ZkFormal.NearV3.Assembly TrieA7Post

/-- The part kinds that replace their (pre-trie) source node. -/
def replK : UpsRows.UKind → Bool
  | .RDB | .RDE | .PT | .RLP | .RBR | .RBV | .RBI | .SPB => true
  | _ => false

/-- The part kinds that overwrite the revealed own value of their source. -/
def oldK : UpsRows.UKind → Bool
  | .RLP | .RBR | .RBV => true
  | _ => false

/-- Bytes of the replaced path nodes of a run. -/
def replacedCharge (run : TreeRun) : Nat :=
  (run.parts.map fun p => if replK p.kind then (NearSpecV3.nodeEnc p.source).length else 0).sum

/-- Bytes of the overwritten value of a run. -/
def oldValCharge (run : TreeRun) : Nat :=
  (run.parts.map fun p => if oldK p.kind then ((NearSpecV3.ownVals p.source).map List.length).sum else 0).sum

@[simp] theorem replacedCharge_push (r : TreeRun) (p : TreePart) :
    replacedCharge (pushPart r p) =
      replacedCharge r + (if replK p.kind then (NearSpecV3.nodeEnc p.source).length else 0) := by
  simp [replacedCharge, pushPart]

@[simp] theorem oldValCharge_push (r : TreeRun) (p : TreePart) :
    oldValCharge (pushPart r p) =
      oldValCharge r + (if oldK p.kind then ((NearSpecV3.ownVals p.source).map List.length).sum else 0) := by
  simp [oldValCharge, pushPart]

/-- The goal shape. -/
def ReplOk (t : PTrie) (run : TreeRun) (v : Bytes) : Prop :=
  unfoldedBytesT t + outputByteCharge run + v.length =
    unfoldedBytesT run.output + replacedCharge run + oldValCharge run

theorem wrapRun_repl (t src : PTrie) (p : List Nat) (r : TreeRun) (v : Bytes) (h : ReplOk t r v) :
    ReplOk t (wrapRun src p r) v := by
  cases p with
  | nil => exact h
  | cons a as =>
    unfold ReplOk at *
    simp only [wrapRun, outputByteCharge_push, replacedCharge_push, oldValCharge_push, enc_eq,
      pushPart_output, wrapExt, U_ext, replK, oldK, Bool.false_eq_true, ite_false]
    omega

theorem leafSplit_repl (k : List Nat) (s : Slot) (m : Nat) (key : List Nat) (v : Bytes)
    (hk : ∀ x ∈ k, x < 16) (hkey : ∀ x ∈ key, x < 16) :
    ReplOk (.leaf k s m) (leafSplitRun k s m key v) v := by
  have hd := @commonPrefix_diverge k key
  unfold leafSplitRun
  generalize commonPrefix k key = p at hd ⊢
  dsimp only
  cases h1 : k.drop p.length with
  | nil =>
    cases h2 : key.drop p.length with
    | nil =>
      simp only [h1, h2]
      simp only [ReplOk, outputByteCharge, replacedCharge, oldValCharge, enc_eq, terminalRun, List.map_cons,
        List.map_nil, List.sum_cons, List.sum_nil, U_newLeaf, U_leaf, replK, oldK, ite_true,
        NearSpecV3.ownVals]
      omega
    | cons y ys =>
      simp only [h1, h2]
      apply wrapRun_repl
      have hy := mem_drop_lt hkey h2
      simp only [ReplOk, outputByteCharge, replacedCharge, oldValCharge, enc_eq, terminalRun, List.map_cons,
        List.map_nil, List.sum_cons, List.sum_nil, U_branch, UK_kids1 y _ hy, U_newLeaf, U_leaf, replK, oldK,
        ite_true, Bool.false_eq_true, ite_false, NearSpecV3.optSlotVal]
      omega
  | cons x xs =>
    have hx := mem_drop_lt hk h1
    cases h2 : key.drop p.length with
    | nil =>
      simp only [h1, h2]
      apply wrapRun_repl
      simp only [ReplOk, outputByteCharge, replacedCharge, oldValCharge, enc_eq, terminalRun, List.map_cons,
        List.map_nil, List.sum_cons, List.sum_nil, U_branch, UK_kids1 x _ hx, U_leaf, replK, oldK,
        ite_true, Bool.false_eq_true, ite_false, NearSpecV3.optSlotVal, NearSpecV3.slotVal]
      omega
    | cons y ys =>
      have hy := mem_drop_lt hkey h2
      have hxy := hd h1 h2
      simp only [h1, h2]
      apply wrapRun_repl
      simp only [ReplOk, outputByteCharge, replacedCharge, oldValCharge, enc_eq, terminalRun, List.map_cons,
        List.map_nil, List.sum_cons, List.sum_nil, U_branch, UK_kids2 x y _ _ hx hy hxy, U_newLeaf, U_leaf,
        replK, oldK, ite_true, Bool.false_eq_true, ite_false, NearSpecV3.optSlotVal]
      omega

theorem extSplit_repl (k : List Nat) (c : PTrie) (m : Nat) (key : List Nat) (v : Bytes)
    (hk : ∀ x ∈ k, x < 16) (hkey : ∀ x ∈ key, x < 16) (hpre : isPrefix k key = false) :
    ReplOk (.ext k c m) (extSplitRun k c m key v) v := by
  have hd := @commonPrefix_diverge k key
  have hl := commonPrefix_left k key
  have hr := commonPrefix_right k key
  unfold extSplitRun
  generalize commonPrefix k key = p at hd hl hr ⊢
  dsimp only
  cases h1 : k.drop p.length with
  | nil =>
    exfalso
    rw [h1, List.append_nil] at hl
    rw [← hl] at hr
    have h := (isPrefix_iff k key).mpr ⟨_, hr⟩
    rw [hpre] at h; cases h
  | cons x xs =>
    have hx := mem_drop_lt hk h1
    cases h2 : key.drop p.length with
    | nil =>
      simp only [h1, h2]
      apply wrapRun_repl
      cases xs with
      | nil =>
        simp only [ReplOk, outputByteCharge, replacedCharge, oldValCharge, enc_eq, terminalRun, List.map_append,
          List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.nil_append, U_branch,
          UK_kids1 x _ hx, U_ext, replK, oldK, ite_true, Bool.false_eq_true, ite_false,
          NearSpecV3.optSlotVal, NearSpecV3.slotVal]
        omega
      | cons z zs =>
        simp only [ReplOk, outputByteCharge, replacedCharge, oldValCharge, enc_eq, terminalRun, List.map_append,
          List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.cons_append,
          List.nil_append, U_branch, UK_kids1 x _ hx, U_ext, replK, oldK, ite_true, Bool.false_eq_true,
          ite_false, NearSpecV3.optSlotVal, NearSpecV3.slotVal]
        omega
    | cons y ys =>
      have hy := mem_drop_lt hkey h2
      have hxy := hd h1 h2
      simp only [h1, h2]
      apply wrapRun_repl
      cases xs with
      | nil =>
        simp only [ReplOk, outputByteCharge, replacedCharge, oldValCharge, enc_eq, terminalRun, List.map_append,
          List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.nil_append, U_branch,
          UK_kids2 x y _ _ hx hy hxy, U_newLeaf, U_ext, replK, oldK, ite_true, Bool.false_eq_true, ite_false,
          NearSpecV3.optSlotVal]
        omega
      | cons z zs =>
        simp only [ReplOk, outputByteCharge, replacedCharge, oldValCharge, enc_eq, terminalRun, List.map_append,
          List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.cons_append,
          List.nil_append, U_branch, UK_kids2 x y _ _ hx hy hxy, U_newLeaf, U_ext, replK, oldK, ite_true,
          Bool.false_eq_true, ite_false, NearSpecV3.optSlotVal]
        omega

mutual
theorem traceUpsert_replaced : ∀ (t : PTrie) (key : List Nat) (v : Bytes) (run : TreeRun),
    traceUpsert t key v = some run → t.wf = true → (∀ x ∈ key, x < 16) → ReplOk t run v
  | .hash _, _, _, _, hr, _, _ => by simp [traceUpsert] at hr
  | .leaf k s m, key, v, run, hr, hw, hkey => by
    by_cases he : k = key
    · subst he
      simp only [traceUpsert, ite_true, Option.some.injEq] at hr
      subst run
      simp only [ReplOk, outputByteCharge, replacedCharge, oldValCharge, enc_eq, terminalRun, List.map_cons,
        List.map_nil, List.sum_cons, List.sum_nil, U_newLeaf, U_leaf, replK, oldK, ite_true, NearSpecV3.ownVals]
      omega
    · simp only [traceUpsert, he, ite_false, Option.some.injEq] at hr
      subst run
      exact leafSplit_repl k s m key v (nib_of_wf_leaf hw) hkey
  | .ext k c m, key, v, run, hr, hw, hkey => by
    have cw : c.wf = true := by simp only [PTrie.wf, Bool.and_eq_true] at hw; exact hw.1.1.2
    cases hp : isPrefix k key with
    | false =>
      simp only [traceUpsert, hp, Bool.false_eq_true, ite_false, Option.some.injEq] at hr
      subst run
      exact extSplit_repl k c m key v (nib_of_wf_ext hw) hkey hp
    | true =>
      cases hm : c.mem? with
      | none => simp [traceUpsert, hp, hm] at hr
      | some cm =>
        cases hc : traceUpsert c (key.drop k.length) v with
        | none => simp [traceUpsert, hp, hm, hc] at hr
        | some inner =>
          simp only [traceUpsert, hp, ite_true, hm, hc, Option.some.injEq] at hr
          subst run
          have h := traceUpsert_replaced c _ v inner hc cw (fun x hx => hkey x (List.mem_of_mem_drop hx))
          unfold ReplOk at h ⊢
          have hrk : replK (if k.isEmpty = true then UpsRows.UKind.PT else .RDE) = true := by split <;> rfl
          have hok : oldK (if k.isEmpty = true then UpsRows.UKind.PT else .RDE) = false := by split <;> rfl
          simp only [outputByteCharge_push, replacedCharge_push, oldValCharge_push, hrk, hok, ite_true,
            Bool.false_eq_true, ite_false, enc_eq, pushPart_output, UpsSpec.qRDE, U_ext]
          omega
  | .branch bv cs m, [], v, run, hr, hw, hkey => by
    simp only [traceUpsert, Option.some.injEq] at hr
    subst run
    have hrk : replK (if bv.isSome = true then UpsRows.UKind.RBR else .RBV) = true := by split <;> rfl
    have hok : oldK (if bv.isSome = true then UpsRows.UKind.RBR else .RBV) = true := by split <;> rfl
    simp only [ReplOk, outputByteCharge, replacedCharge, oldValCharge, enc_eq, terminalRun, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, U_branch, hrk, hok, ite_true, NearSpecV3.ownVals,
      NearSpecV3.optSlotVal, NearSpecV3.slotVal]
    omega
  | .branch bv cs m, n :: key, v, run, hr, hw, hkey => by
    have cw : Kids.wf cs 16 = true := by simp only [PTrie.wf, Bool.and_eq_true] at hw; exact hw.1.2
    cases hc : traceKids (.branch bv cs m) (n :: key) cs n key v with
    | none => simp [traceUpsert, hc] at hr
    | some inner =>
      simp only [traceUpsert, hc, Option.map_some, Option.some.injEq] at hr
      subst run
      have h := traceKids_replaced (.branch bv cs m) (n :: key) cs 16 n key v inner cw hc
        (fun x hx => hkey x (List.mem_cons_of_mem _ hx))
      have hrk : replK (if inner.inserted = true then UpsRows.UKind.RBI else .RDB) = true := by split <;> rfl
      have hok : oldK (if inner.inserted = true then UpsRows.UKind.RBI else .RDB) = false := by split <;> rfl
      simp only [ReplOk, outputByteCharge_push, replacedCharge_push, oldValCharge_push, hrk, hok, ite_true,
        Bool.false_eq_true, ite_false, enc_eq, pushPart_output, U_branch]
      omega

theorem traceKids_replaced : ∀ (source : PTrie) (wholeKey : List Nat) (cs : Kids) (width n : Nat)
    (key : List Nat) (v : Bytes) (run : KidsRun), Kids.wf cs width = true →
    traceKids source wholeKey cs n key v = some run → (∀ x ∈ key, x < 16) →
    UK cs + outputByteCharge run.inner + v.length =
      UK run.output + replacedCharge run.inner + oldValCharge run.inner
  | _, _, .nil, _, _, _, _, _, _, hr, _ => by simp [traceKids] at hr
  | source, wholeKey, .none rest, _, 0, key, v, run, _, hr, _ => by
    simp only [traceKids, Option.some.injEq] at hr
    subst run
    simp only [outputByteCharge, replacedCharge, oldValCharge, enc_eq, terminalRun, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, UK_some, UK_none, U_newLeaf, replK, oldK, Bool.false_eq_true, ite_false]
    omega
  | source, wholeKey, .some child rest, width, 0, key, v, run, hw, hr, hkey => by
    simp only [Kids.wf, Bool.and_eq_true, bne_iff_ne] at hw
    cases hm : child.mem? with
    | none => simp [traceKids, hm] at hr
    | some cm =>
      cases hc : traceUpsert child key v with
      | none => simp [traceKids, hm, hc] at hr
      | some inner =>
        simp only [traceKids, hm, hc, Option.some.injEq] at hr
        subst run
        have h := traceUpsert_replaced child key v inner hc hw.1.2 hkey
        unfold ReplOk at h
        simp only [UK_some]
        omega
  | source, wholeKey, .none rest, width, n + 1, key, v, run, hw, hr, hkey => by
    simp only [Kids.wf, Bool.and_eq_true, bne_iff_ne] at hw
    cases hc : traceKids source wholeKey rest n key v with
    | none => simp [traceKids, hc] at hr
    | some inner =>
      simp only [traceKids, hc, Option.map_some, Option.some.injEq] at hr
      subst run
      have h := traceKids_replaced source wholeKey rest (width - 1) n key v inner hw.2 hc hkey
      simpa only [UK_none] using h
  | source, wholeKey, .some child rest, width, n + 1, key, v, run, hw, hr, hkey => by
    simp only [Kids.wf, Bool.and_eq_true, bne_iff_ne] at hw
    cases hc : traceKids source wholeKey rest n key v with
    | none => simp [traceKids, hc] at hr
    | some inner =>
      simp only [traceKids, hc, Option.map_some, Option.some.injEq] at hr
      subst run
      have h := traceKids_replaced source wholeKey rest (width - 1) n key v inner hw.2 hc hkey
      simp only [UK_some]
      omega
end

end ZkFormal.NearV3.Assembly.TrieA7Repl
