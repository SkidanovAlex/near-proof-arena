import ZkFormal.NearV3.Assembly.LinkVBytes
import ZkFormal.NearV3.Spec.Absent

/-!
# ZkFormal.NearV3.Assembly.LinkPartial — runtime steps on a pruned partial trie

The native runtime runs on `partialTrie (store) root keys`, a hash-pruning (`refinedBy`) of the
record tree that the AIR's links speak about.  Generic bridge:

* **`PTrie.upsert_of_find`**: on a well-formed trie, `upsert` at a nibble key whose lookup is
  determined (`find ≠ none`) succeeds (every node on the path is revealed);
* **`schedStep_refined`**: if `P` refines `F`, `P`'s lookup of `0x0f` is determined and the
  scheduler step on `F` succeeds, then the step on `P` succeeds with the same output, and its
  result refines `F`'s (hence has the same root hash);
* **`applyMissingChunk_refined`**: the same for an implicit (missing-chunk) application, which
  additionally reads the delayed-receipt indices.
-/

namespace ZkFormal.NearV3.Assembly

open NearSpec NearSpecV3

namespace LinkPartial

theorem nibblesOk_drop {key : List Nat} (h : nibblesOk key = true) (n : Nat) :
    nibblesOk (key.drop n) = true := by
  unfold nibblesOk at *
  rw [List.all_eq_true] at *
  exact fun x hx => h x (List.mem_of_mem_drop hx)

theorem mem_of_find {c : PTrie} {key : List Nat} (h : c.find key ≠ none) : ∃ m, c.mem? = some m := by
  cases c with
  | hash => simp [PTrie.find] at h
  | leaf => exact ⟨_, rfl⟩
  | ext => exact ⟨_, rfl⟩
  | branch => exact ⟨_, rfl⟩

mutual
/-- **`upsert` succeeds where the lookup is determined.** -/
theorem PTrie.upsert_of_find : ∀ (t : PTrie) (key : List Nat) (v : Bytes), t.wf = true →
    nibblesOk key = true → t.find key ≠ none → ∃ t', t.upsert key v = some t'
  | .hash _, _, _, _, _, h => by simp [PTrie.find] at h
  | .leaf k s m, key, v, _, _, _ => by
    simp only [PTrie.upsert]
    split <;> exact ⟨_, rfl⟩
  | .ext k c m, key, v, hw, hk, h => by
    simp only [PTrie.upsert]
    by_cases hp : isPrefix k key = true
    · rw [find_ext] at h
      simp only [hp, ↓reduceIte] at h ⊢
      have hcw : c.wf = true := by simp only [PTrie.wf, Bool.and_eq_true] at hw; exact hw.1.1.2
      obtain ⟨c', hc'⟩ := PTrie.upsert_of_find c (key.drop k.length) v hcw (nibblesOk_drop hk _) h
      obtain ⟨cm, hcm⟩ := mem_of_find h
      rw [hcm, hc']
      exact ⟨_, rfl⟩
    · simp only [hp, Bool.false_eq_true, ↓reduceIte]
      exact ⟨_, rfl⟩
  | .branch bv cs m, [], v, _, _, _ => by
    simp only [PTrie.upsert]
    exact ⟨_, rfl⟩
  | .branch bv cs m, n :: rest, v, hw, hk, h => by
    simp only [PTrie.upsert]
    rw [find_branch_cons] at h
    have hcs : Kids.wf cs 16 = true := by simp only [PTrie.wf, Bool.and_eq_true] at hw; exact hw.1.2
    have hn := (nibblesOk_cons.1 hk)
    obtain ⟨r, hr⟩ := Kids.upsert_of_find cs 16 n rest v hcs hn.1 hn.2 h
    rw [hr]
    exact ⟨_, rfl⟩
theorem Kids.upsert_of_find : ∀ (cs : Kids) (cnt n : Nat) (key : List Nat) (v : Bytes),
    Kids.wf cs cnt = true → n < cnt → nibblesOk key = true → Kids.find cs n key ≠ none →
    ∃ r, Kids.upsert cs n key v = some r
  | .nil, cnt, n, _, _, hw, hn, _, _ => by
    simp only [Kids.wf, beq_iff_eq] at hw
    omega
  | .none r, _, 0, key, v, _, _, _, _ => by
    simp only [Kids.upsert]
    exact ⟨_, rfl⟩
  | .some c r, _, 0, key, v, hw, _, hk, h => by
    simp only [Kids.upsert]
    simp only [Kids.find] at h
    have hcw : c.wf = true := by simp only [Kids.wf, Bool.and_eq_true] at hw; exact hw.1.2
    obtain ⟨c', hc'⟩ := PTrie.upsert_of_find c key v hcw hk h
    obtain ⟨cm, hcm⟩ := mem_of_find h
    rw [hcm, hc']
    exact ⟨_, rfl⟩
  | .none r, cnt, i + 1, key, v, hw, hn, hk, h => by
    simp only [Kids.upsert]
    simp only [Kids.find] at h
    simp only [Kids.wf, Bool.and_eq_true, bne_iff_ne, ne_eq] at hw
    obtain ⟨x, hx⟩ := Kids.upsert_of_find r (cnt - 1) i key v hw.2 (by omega) hk h
    rw [hx]
    exact ⟨_, rfl⟩
  | .some c r, cnt, i + 1, key, v, hw, hn, hk, h => by
    simp only [Kids.upsert]
    simp only [Kids.find] at h
    simp only [Kids.wf, Bool.and_eq_true, bne_iff_ne, ne_eq] at hw
    obtain ⟨x, hx⟩ := Kids.upsert_of_find r (cnt - 1) i key v hw.2 (by omega) hk h
    rw [hx]
    exact ⟨_, rfl⟩
end

/-- **The scheduler step on a pruning** of a trie whose step succeeds. -/
theorem schedStep_refined {ctx : ApplyCtx} {P F Q : PTrie} {so : SchedOut}
    (hr : P.refinedBy F) (hw : P.wf = true) (hd : P.find keyBwState ≠ none)
    (hF : schedStep prims ctx F = .ok (Q, so)) :
    ∃ P', schedStep prims ctx P = .ok (P', so) ∧ P'.refinedBy Q := by
  obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp hd
  have hFx := PTrie.find_refinedBy P F _ x hr hx
  obtain ⟨P', hP'⟩ := PTrie.upsert_of_find P keyBwState so.state hw (by decide) hd
  unfold schedStep readKey at hF ⊢
  rw [hFx] at hF
  rw [hx]
  simp only [bind, Except.bind, pure, Except.pure] at hF ⊢
  split at hF
  · rename_i o ho
    split at hF
    · rename_i F' hF'
      simp only [Except.ok.injEq, Prod.mk.injEq] at hF
      obtain ⟨rfl, rfl⟩ := hF
      obtain ⟨F'', hF'', hrf⟩ := PTrie.upsert_refinedBy P F keyBwState o.state P' hr hP'
      rw [hF'] at hF''
      cases hF''
      rw [hP']
      exact ⟨P', rfl, hrf⟩
    · cases hF
  · cases hF

/-- **The missing-chunk application on a pruning** of a trie whose application succeeds. -/
theorem applyMissingChunk_refined {ctx : ApplyCtx} {P F Q : PTrie}
    (hr : P.refinedBy F) (hw : P.wf = true) (hd : P.find keyDelayedIdx ≠ none)
    (hb : P.find keyBwState ≠ none) (hF : applyMissingChunk prims ctx F = .ok Q) :
    ∃ P', applyMissingChunk prims ctx P = .ok P' ∧ P'.refinedBy Q := by
  obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp hd
  unfold applyMissingChunk at hF ⊢
  have hFx := PTrie.find_refinedBy P F _ x hr hx
  simp only [readKey, hFx, hx, bind, Except.bind] at hF ⊢
  split at hF
  · cases hF
  · rename_i r hs
    obtain ⟨Q', so⟩ := r
    simp only [pure, Except.pure, Except.ok.injEq] at hF
    subst hF
    obtain ⟨P', hP', hrf⟩ := schedStep_refined hr hw hb hs
    rw [hP']
    exact ⟨P', rfl, hrf⟩

end LinkPartial

end ZkFormal.NearV3.Assembly
