import ZkFormal.NearV3.Assembly.UpsertOutputCost
import ZkFormal.NearV3.Assembly.NativeUnfold
import ZkFormal.NearV3.Assembly.SchedulerUpsertCost

/-!
# ZkFormal.NearV3.Assembly.TrieA7Post — the upsert's new parts and value lie in the native post trie

**`traceUpsert_unfolded`**: for a well-formed trie `t` and a nibble key, a successful
`traceUpsert t key v = some run` has `outputByteCharge run + |v| ≤ unfoldedBytesT run.output`:
every output part is a distinct occurrence of the post trie (the path from the new root, including
the node split off by a leaf/extension split), and the new value is one of its values.
(`traceKids_unfolded`: the kids version, with `UK` the unfolded bytes of a child list.)

**`ups_post_bound`** (A7 (b), ups part): for the scheduler witnesses `us` of an accepted chunk
(`us.map (pre, run.output) = (oldPost, m.result.trie) :: steps.map (pre, post)`), the new values and
parts total `Σ_u (|u.value| + outputByteCharge u.run) ≤ Σ_τ unfoldedBytesT post_τ ≤ unfoldBytes ≤ B0`.
-/

namespace ZkFormal.NearV3.Assembly.TrieA7Post

open NearSpec NearSpecV3 Render.UpsGen ZkFormal.NearV3.Assembly

/-- Unfolded bytes of a child list. -/
def UK (cs : Kids) : Nat :=
  ((NearSpecV3.kOccs cs).map (fun o => (NearSpecV3.nodeEnc o).length)).sum + (((NearSpecV3.kOccs cs).flatMap NearSpecV3.ownVals).map List.length).sum

theorem enc_eq (t : PTrie) : ZkFormal.NearV3.nodeEnc t = NearSpecV3.nodeEnc t := by
  cases t with
  | branch v cs m => cases v <;> rfl
  | _ => rfl

@[simp] theorem pushPart_output (r : TreeRun) (p : TreePart) : (pushPart r p).output = p.output := rfl

theorem U_leaf (k : List Nat) (s : Slot) (m : Nat) :
    unfoldedBytesT (.leaf k s m) = (NearSpecV3.nodeEnc (.leaf k s m)).length + ((NearSpecV3.slotVal s).map List.length).sum := by
  simp [unfoldedBytesT, NearSpecV3.occs, NearSpecV3.valsOf, NearSpecV3.ownVals, NearSpecV3.kOccs, NearSpecV3.slotVal, NearSpecV3.optSlotVal]

theorem U_ext (k : List Nat) (c : PTrie) (m : Nat) :
    unfoldedBytesT (.ext k c m) = (NearSpecV3.nodeEnc (.ext k c m)).length + unfoldedBytesT c := by
  simp [unfoldedBytesT, NearSpecV3.occs, NearSpecV3.valsOf, NearSpecV3.ownVals, NearSpecV3.kOccs, NearSpecV3.slotVal, NearSpecV3.optSlotVal, List.flatMap_cons, List.flatMap_append]
  omega

theorem U_branch (bv : Option Slot) (cs : Kids) (m : Nat) :
    unfoldedBytesT (.branch bv cs m) =
      (NearSpecV3.nodeEnc (.branch bv cs m)).length + ((NearSpecV3.optSlotVal bv).map List.length).sum + UK cs := by
  simp [unfoldedBytesT, UK, NearSpecV3.occs, NearSpecV3.valsOf, NearSpecV3.ownVals, NearSpecV3.kOccs, NearSpecV3.slotVal, NearSpecV3.optSlotVal, List.flatMap_cons, List.flatMap_append]
  omega

theorem UK_some (c : PTrie) (r : Kids) : UK (.some c r) = unfoldedBytesT c + UK r := by
  simp [UK, unfoldedBytesT, NearSpecV3.occs, NearSpecV3.valsOf, NearSpecV3.ownVals, NearSpecV3.kOccs, NearSpecV3.slotVal, NearSpecV3.optSlotVal, List.flatMap_append]
  omega

theorem UK_none (r : Kids) : UK (.none r) = UK r := by
  simp [UK, NearSpecV3.kOccs]

theorem U_newLeaf (k : List Nat) (v : Bytes) :
    unfoldedBytesT (newLeaf k v) = (NearSpecV3.nodeEnc (newLeaf k v)).length + v.length := by
  simp [newLeaf, U_leaf, NearSpecV3.slotVal]

theorem UK_kidsFrom0 : ∀ (n i : Nat) (f : Nat → Option PTrie), (∀ j, i ≤ j → f j = none) →
    UK (kidsFrom n i f) = 0
  | 0, _, _, _ => by simp [kidsFrom, UK, NearSpecV3.kOccs]
  | n + 1, i, f, h => by
    simp only [kidsFrom, h i (Nat.le_refl _), UK_none]
    exact UK_kidsFrom0 n (i + 1) f (fun j hj => h j (by omega))

theorem UK_kidsFrom1 (ca : PTrie) : ∀ (n i a : Nat) (f : Nat → Option PTrie), i ≤ a → a < i + n →
    (∀ j, i ≤ j → f j = if j = a then some ca else none) → UK (kidsFrom n i f) = unfoldedBytesT ca
  | 0, _, _, _, h1, h2, _ => by omega
  | n + 1, i, a, f, h1, h2, h => by
    by_cases hia : i = a
    · subst hia
      have z := UK_kidsFrom0 n (i + 1) f (fun j hj => by rw [h j (by omega), if_neg (by omega)])
      simp only [kidsFrom, h i (Nat.le_refl _), ite_true, UK_some, z, Nat.add_zero]
    · have ih := UK_kidsFrom1 ca n (i + 1) a f (by omega) (by omega) (fun j hj => h j (by omega))
      simp only [kidsFrom, h i (Nat.le_refl _), if_neg hia, UK_none]
      exact ih

theorem UK_kidsFrom2 (ca cb : PTrie) : ∀ (n i a b : Nat) (f : Nat → Option PTrie), i ≤ a → a < b → b < i + n →
    (∀ j, i ≤ j → f j = if j = a then some ca else if j = b then some cb else none) →
    UK (kidsFrom n i f) = unfoldedBytesT ca + unfoldedBytesT cb
  | 0, _, _, _, _, h1, h2, h3, _ => by omega
  | n + 1, i, a, b, f, h1, h2, h3, h => by
    by_cases hia : i = a
    · subst hia
      have o := UK_kidsFrom1 cb n (i + 1) b f (by omega) (by omega) (fun j hj => by
        rw [h j (by omega), if_neg (by omega)])
      simp only [kidsFrom, h i (Nat.le_refl _), ite_true, UK_some, o]
    · have ih := UK_kidsFrom2 ca cb n (i + 1) a b f (by omega) h2 (by omega) (fun j hj => h j (by omega))
      simp only [kidsFrom, h i (Nat.le_refl _), if_neg hia, show ¬ (i = b) by omega, ite_false, UK_none]
      exact ih

theorem UK_kids1 (x : Nat) (c : PTrie) (hx : x < 16) : UK (kids1 x c) = unfoldedBytesT c :=
  UK_kidsFrom1 c 16 0 x _ (Nat.zero_le _) (by omega) (fun _ _ => rfl)

theorem UK_kids2 (x y : Nat) (c d : PTrie) (hx : x < 16) (hy : y < 16) (hxy : x ≠ y) :
    UK (kids2 x c y d) = unfoldedBytesT c + unfoldedBytesT d := by
  unfold kids2
  rcases Nat.lt_or_gt_of_ne hxy with h | h
  · exact UK_kidsFrom2 c d 16 0 x y _ (Nat.zero_le _) h (by omega) (fun _ _ => rfl)
  · have e := UK_kidsFrom2 d c 16 0 y x
      (fun i => if i = x then some c else if i = y then some d else none) (Nat.zero_le _) h (by omega)
      (fun j _ => by
        by_cases hjx : j = x
        · simp [hjx, hxy]
        · by_cases hjy : j = y <;> simp [hjx, hjy, Ne.symm hxy])
    rw [e]; omega

/-- The goal shape of the whole development. -/
def PostOk (run : TreeRun) (v : Bytes) : Prop := outputByteCharge run + v.length ≤ unfoldedBytesT run.output

theorem wrapRun_ok (src : PTrie) (p : List Nat) (r : TreeRun) (v : Bytes) (h : PostOk r v) :
    PostOk (wrapRun src p r) v := by
  cases p with
  | nil => exact h
  | cons a as =>
    unfold PostOk at *
    simp only [wrapRun, outputByteCharge_push, enc_eq, pushPart_output, wrapExt, U_ext]
    omega

theorem mem_drop_lt {l : List Nat} (hl : ∀ x ∈ l, x < 16) {n x : Nat} {xs : List Nat}
    (h : l.drop n = x :: xs) : x < 16 := by
  have hm : x ∈ l.drop n := by rw [h]; exact List.mem_cons_self
  exact hl x (List.mem_of_mem_drop hm)

theorem leafSplit_ok (k : List Nat) (s : Slot) (m : Nat) (key : List Nat) (v : Bytes)
    (hk : ∀ x ∈ k, x < 16) (hkey : ∀ x ∈ key, x < 16) : PostOk (leafSplitRun k s m key v) v := by
  have hd := @commonPrefix_diverge k key
  unfold leafSplitRun
  generalize commonPrefix k key = p at hd ⊢
  dsimp only
  cases h1 : k.drop p.length with
  | nil =>
    cases h2 : key.drop p.length with
    | nil =>
      simp only [h1, h2]
      simp only [PostOk, outputByteCharge, enc_eq, terminalRun, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, U_newLeaf]
      omega
    | cons y ys =>
      simp only [h1, h2]
      apply wrapRun_ok
      have hy := mem_drop_lt hkey h2
      simp only [PostOk, outputByteCharge, enc_eq, terminalRun, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, U_branch, UK_kids1 y _ hy, U_newLeaf]
      omega
  | cons x xs =>
    have hx := mem_drop_lt hk h1
    cases h2 : key.drop p.length with
    | nil =>
      simp only [h1, h2]
      apply wrapRun_ok
      simp only [PostOk, outputByteCharge, enc_eq, terminalRun, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, U_branch, UK_kids1 x _ hx, U_leaf, NearSpecV3.optSlotVal, NearSpecV3.slotVal]
      omega
    | cons y ys =>
      have hy := mem_drop_lt hkey h2
      have hxy := hd h1 h2
      simp only [h1, h2]
      apply wrapRun_ok
      simp only [PostOk, outputByteCharge, enc_eq, terminalRun, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, U_branch, UK_kids2 x y _ _ hx hy hxy, U_newLeaf, U_leaf, NearSpecV3.optSlotVal]
      omega

theorem extSplit_ok (k : List Nat) (c : PTrie) (m : Nat) (key : List Nat) (v : Bytes)
    (hk : ∀ x ∈ k, x < 16) (hkey : ∀ x ∈ key, x < 16) (hpre : isPrefix k key = false) :
    PostOk (extSplitRun k c m key v) v := by
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
      apply wrapRun_ok
      cases xs with
      | nil =>
        simp only [PostOk, outputByteCharge, enc_eq, terminalRun, List.map_append, List.sum_append, List.map_cons,
          List.map_nil, List.sum_cons, List.sum_nil, List.nil_append, U_branch, UK_kids1 x _ hx,
          NearSpecV3.optSlotVal, NearSpecV3.slotVal]
        omega
      | cons z zs =>
        simp only [PostOk, outputByteCharge, enc_eq, terminalRun, List.map_append, List.sum_append, List.map_cons,
          List.map_nil, List.sum_cons, List.sum_nil, List.cons_append, List.nil_append, U_branch,
          UK_kids1 x _ hx, U_ext, NearSpecV3.optSlotVal, NearSpecV3.slotVal]
        omega
    | cons y ys =>
      have hy := mem_drop_lt hkey h2
      have hxy := hd h1 h2
      simp only [h1, h2]
      apply wrapRun_ok
      cases xs with
      | nil =>
        simp only [PostOk, outputByteCharge, enc_eq, terminalRun, List.map_append, List.sum_append, List.map_cons,
          List.map_nil, List.sum_cons, List.sum_nil, List.nil_append, U_branch, UK_kids2 x y _ _ hx hy hxy,
          U_newLeaf, NearSpecV3.optSlotVal]
        omega
      | cons z zs =>
        simp only [PostOk, outputByteCharge, enc_eq, terminalRun, List.map_append, List.sum_append, List.map_cons,
          List.map_nil, List.sum_cons, List.sum_nil, List.cons_append, List.nil_append, U_branch,
          UK_kids2 x y _ _ hx hy hxy, U_newLeaf, U_ext, NearSpecV3.optSlotVal]
        omega

theorem nib_of_wf_leaf {k : List Nat} {s : Slot} {m : Nat} (hw : (PTrie.leaf k s m).wf = true) : ∀ x ∈ k, x < 16 := by
  simp only [PTrie.wf, Bool.and_eq_true, nibblesOk, List.all_eq_true, decide_eq_true_eq] at hw
  exact hw.1.1.1

theorem nib_of_wf_ext {k : List Nat} {c : PTrie} {m : Nat} (hw : (PTrie.ext k c m).wf = true) : ∀ x ∈ k, x < 16 := by
  simp only [PTrie.wf, Bool.and_eq_true, nibblesOk, List.all_eq_true, decide_eq_true_eq] at hw
  exact hw.1.1.1

mutual
theorem traceUpsert_unfolded : ∀ (t : PTrie) (key : List Nat) (v : Bytes) (run : TreeRun),
    traceUpsert t key v = some run → t.wf = true → (∀ x ∈ key, x < 16) → PostOk run v
  | .hash _, _, _, _, hr, _, _ => by simp [traceUpsert] at hr
  | .leaf k s m, key, v, run, hr, hw, hkey => by
    by_cases he : k = key
    · simp only [traceUpsert, he, ite_true, Option.some.injEq] at hr
      subst run
      simp only [PostOk, outputByteCharge, enc_eq, terminalRun, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, U_newLeaf]
      omega
    · simp only [traceUpsert, he, ite_false, Option.some.injEq] at hr
      subst run
      exact leafSplit_ok k s m key v (nib_of_wf_leaf hw) hkey
  | .ext k c m, key, v, run, hr, hw, hkey => by
    have cw : c.wf = true := by simp only [PTrie.wf, Bool.and_eq_true] at hw; exact hw.1.1.2
    cases hp : isPrefix k key with
    | false =>
      simp only [traceUpsert, hp, Bool.false_eq_true, ite_false, Option.some.injEq] at hr
      subst run
      exact extSplit_ok k c m key v (nib_of_wf_ext hw) hkey hp
    | true =>
      cases hm : c.mem? with
      | none => simp [traceUpsert, hp, hm] at hr
      | some cm =>
        cases hc : traceUpsert c (key.drop k.length) v with
        | none => simp [traceUpsert, hp, hm, hc] at hr
        | some inner =>
          simp only [traceUpsert, hp, ite_true, hm, hc, Option.some.injEq] at hr
          subst run
          have h := traceUpsert_unfolded c _ v inner hc cw (fun x hx => hkey x (List.mem_of_mem_drop hx))
          unfold PostOk at h ⊢
          simp only [outputByteCharge_push, enc_eq, pushPart_output, UpsSpec.qRDE, U_ext]
          omega
  | .branch bv cs m, [], v, run, hr, hw, hkey => by
    simp only [traceUpsert, Option.some.injEq] at hr
    subst run
    simp only [PostOk, outputByteCharge, enc_eq, terminalRun, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, U_branch, NearSpecV3.optSlotVal, NearSpecV3.slotVal]
    omega
  | .branch bv cs m, n :: key, v, run, hr, hw, hkey => by
    have cw : Kids.wf cs 16 = true := by simp only [PTrie.wf, Bool.and_eq_true] at hw; exact hw.1.2
    cases hc : traceKids (.branch bv cs m) (n :: key) cs n key v with
    | none => simp [traceUpsert, hc] at hr
    | some inner =>
      simp only [traceUpsert, hc, Option.map_some, Option.some.injEq] at hr
      subst run
      have h := traceKids_unfolded (.branch bv cs m) (n :: key) cs 16 n key v inner cw hc
        (fun x hx => hkey x (List.mem_cons_of_mem _ hx))
      simp only [PostOk, outputByteCharge_push, enc_eq, pushPart_output, U_branch]
      omega

theorem traceKids_unfolded : ∀ (source : PTrie) (wholeKey : List Nat) (cs : Kids) (width n : Nat)
    (key : List Nat) (v : Bytes) (run : KidsRun), Kids.wf cs width = true →
    traceKids source wholeKey cs n key v = some run → (∀ x ∈ key, x < 16) →
    outputByteCharge run.inner + v.length ≤ UK run.output
  | _, _, .nil, _, _, _, _, _, _, hr, _ => by simp [traceKids] at hr
  | source, wholeKey, .none rest, _, 0, key, v, run, _, hr, _ => by
    simp only [traceKids, Option.some.injEq] at hr
    subst run
    simp only [outputByteCharge, enc_eq, terminalRun, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      UK_some, U_newLeaf]
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
        have h := traceUpsert_unfolded child key v inner hc hw.1.2 hkey
        unfold PostOk at h
        simp only [UK_some]
        omega
  | source, wholeKey, .none rest, width, n + 1, key, v, run, hw, hr, hkey => by
    simp only [Kids.wf, Bool.and_eq_true, bne_iff_ne] at hw
    cases hc : traceKids source wholeKey rest n key v with
    | none => simp [traceKids, hc] at hr
    | some inner =>
      simp only [traceKids, hc, Option.map_some, Option.some.injEq] at hr
      subst run
      have h := traceKids_unfolded source wholeKey rest (width - 1) n key v inner hw.2 hc hkey
      simpa only [UK_none] using h
  | source, wholeKey, .some child rest, width, n + 1, key, v, run, hw, hr, hkey => by
    simp only [Kids.wf, Bool.and_eq_true, bne_iff_ne] at hw
    cases hc : traceKids source wholeKey rest n key v with
    | none => simp [traceKids, hc] at hr
    | some inner =>
      simp only [traceKids, hc, Option.map_some, Option.some.injEq] at hr
      subst run
      have h := traceKids_unfolded source wholeKey rest (width - 1) n key v inner hw.2 hc hkey
      simp only [UK_some]
      omega
end

private theorem sum_le_map {α : Type} {l : List α} {f g : α → Nat} (h : ∀ x ∈ l, f x ≤ g x) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    have := h a (by simp)
    have := ih (fun x hx => h x (by simp [hx]))
    omega

/-- **The ups part of A7 (b)**: the new values and parts of the scheduler upserts fit `B0`. -/
theorem ups_post_bound {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    (hk : walkD0 cb = .ok k) (hw : decodeW wb = .ok w) (hc : checkD0a B0 cb wb = .ok ())
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes} (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    {oldPost : PTrie} (us : List SchedulerUpsertWitness)
    (hpairs : us.map (fun u => (u.pre, u.run.output)) = (oldPost, m.result.trie) :: steps.map (fun s => (s.pre, s.post)))
    (hgood : ∀ u ∈ us, u.Valid ∧ u.pre.wf = true) :
    (us.map (fun u => u.value.length + outputByteCharge u.run)).sum ≤ 2000000 := by
  have hr := triesD0_native_result hk hw hm hv
  have hh := (relD0a_iff B0 cb wb).mpr hc
  have hb : unfoldBytes cb wb ≤ B0 := by simpa only [a7, decide_eq_true_eq] using hh.2.2.2.2.1
  simp only [unfoldBytes, hr] at hb
  have h1 : (us.map (fun u => u.value.length + outputByteCharge u.run)).sum ≤
      (us.map (fun u => unfoldedBytesT u.run.output)).sum := by
    apply sum_le_map
    intro u hu
    obtain ⟨hval, hwf⟩ := hgood u hu
    have h := traceUpsert_unfolded u.pre _ u.value u.run hval.1 hwf (by
      rw [keyBwState_nibbles]; intro x hx; simp at hx; omega)
    unfold PostOk at h
    omega
  have h2 : (us.map (fun u => unfoldedBytesT u.run.output)).sum =
      ((us.map (fun u => (u.pre, u.run.output))).map (fun p => unfoldedBytesT p.2)).sum := by
    simp [List.map_map, Function.comp_def]
  rw [hpairs] at h2
  have h3 : (((oldPost, m.result.trie) :: steps.map (fun s => (s.pre, s.post))).map (fun p => unfoldedBytesT p.2)).sum ≤
      (((m.pre, m.result.trie) :: unfoldedPairs steps).map (fun p => unfoldedBytesT p.1 + unfoldedBytesT p.2)).sum := by
    simp only [List.map_cons, List.sum_cons, unfoldedPairs, List.map_map, Function.comp_def]
    have := sum_le_map (l := steps) (f := fun s => unfoldedBytesT s.post)
      (g := fun s => unfoldedBytesT s.pre + unfoldedBytesT s.post) (fun _ _ => Nat.le_add_left _ _)
    omega
  unfold B0 at hb
  omega

end ZkFormal.NearV3.Assembly.TrieA7Post
