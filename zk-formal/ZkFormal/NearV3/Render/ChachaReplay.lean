import ZkFormal.NearV3.Candidates.ProcShuffleReplay
import ZkFormal.Chacha.Shuffle.Complete.Basic
import ZkFormal.NearV3.Sched.Spec.Loop

/-!
# ZkFormal.NearV3.Render.ChachaReplay — the scheduler's shuffle replay is the `shufV3` instance

The native run replays every round's shuffle with `replayShuffle key k vals` (the loop of
`ProcShuffleReplay.step`).  For the `shufV3` instance `I = ⟨lid, key, k, vals⟩`:

* **`replay_inst`**: a successful replay returns `(I.final, I.kBefore 0)` and every draw of the
  instance succeeds (`genAt 64 (q+1) key (kBefore q) = some _` for `1 ≤ q < L`);
* `kAt_mono` / `kBefore_le`: the stream positions increase along the draws, so every position of
  the instance lies in `[kstart, kBefore 0]`;
* `final_perm`: the shuffled list is a permutation of the input.
-/

namespace ZkFormal.NearV3.Render.ChachaBus

open NearSpecV3 ZkFormal.Chacha ZkFormal.Chacha.Shuffle.Gen ZkFormal.Chacha.Shuffle.Complete
open ZkFormal.NearV3.Candidates ZkFormal.NearV3.Sched.Gen

/-- The `shufV3` instance of one replayed shuffle. -/
def sinstOf (lid : Nat) (key : List Nat) (k : Nat) (vals : List Nat) : SInst := ⟨lid, key, k, vals⟩

/-- Every draw of `I` succeeds. -/
def Draws (I : SInst) : Prop :=
  ∀ q, 1 ≤ q → q < I.L → ∃ j k', genAt 64 (q + 1) I.key (I.kBefore q) = some (j, k')

theorem replay_loop (I : SInst) :
    ∀ count (l : List Nat), count ≤ I.L - 1 → ∀ res last,
      forIn (List.range' (I.L - 1 - count) count) (l, I.kBefore count)
          (ProcShuffleReplay.step (I.L - 1) I.key) = .ok (res, last) →
      (∀ q, 1 ≤ q → q ≤ count → ∃ j k', genAt 64 (q + 1) I.key (I.kBefore q) = some (j, k')) ∧
        res = fyLoop I.js count l ∧ last = I.kBefore 0
  | 0, l, _, res, last, h => by
    simp only [List.range'_zero, List.forIn_nil, Except.pure, pure] at h
    cases h
    exact ⟨fun q h1 h2 => by omega, rfl, rfl⟩
  | count + 1, l, hc, res, last, h => by
    rw [List.range'_succ, List.forIn_cons] at h
    have hstart : I.L - 1 - (I.L - 1 - (count + 1)) = count + 1 := by omega
    have hnext : I.L - 1 - (count + 1) + 1 = I.L - 1 - count := by omega
    simp only [ProcShuffleReplay.step, hstart] at h
    cases hg : genAt 64 (count + 1 + 1) I.key (I.kBefore (count + 1)) with
    | none => simp only [hg, bind, Except.bind] at h; cases h
    | some p =>
      obtain ⟨j, k'⟩ := p
      simp only [hg, bind, Except.bind, hnext] at h
      have hk : I.kBefore count = k' := by
        have := kBefore_pred (I := I) (q := count + 1) (by omega) (by unfold SInst.L at *; omega)
        rw [Nat.add_sub_cancel, hg] at this
        exact this
      have hj : I.js (count + 1) = j := by unfold SInst.js; rw [hg]; rfl
      rw [← hk] at h
      obtain ⟨hd, hr, hl⟩ := replay_loop I count _ (by omega) res last h
      refine ⟨?_, ?_, hl⟩
      · intro q h1 h2
        rcases Nat.lt_or_ge q (count + 1) with hq | hq
        · exact hd q h1 (by omega)
        · rw [show q = count + 1 by omega]; exact ⟨j, k', hg⟩
      · rw [hr, fyLoop, hj]

/-- **A successful replay is the `shufV3` instance**: it returns `(final, kBefore 0)`, and every
draw succeeds. -/
theorem replay_inst (lid : Nat) (key : List Nat) (k : Nat) (vals sh : List Nat) (kend : Nat)
    (h : replayShuffle key k vals = .ok (sh, kend)) :
    Draws (sinstOf lid key k vals) ∧ sh = (sinstOf lid key k vals).final ∧
      kend = (sinstOf lid key k vals).kBefore 0 := by
  let I := sinstOf lid key k vals
  rw [ProcShuffleReplay.replay_eq] at h
  cases hout : forIn (List.range (vals.length - 1)) (vals, k)
      (ProcShuffleReplay.step (vals.length - 1) key) with
  | error e => rw [hout] at h; cases h
  | ok out =>
    rw [hout] at h
    have hh : out = (sh, kend) := Except.ok.inj h
    subst hh
    have hL : vals.length = I.L := rfl
    rw [List.range_eq_range'] at hout
    have h0 : I.kBefore (I.L - 1) = k := kBefore_top
    rw [hL, ← h0, show (0 : Nat) = I.L - 1 - (I.L - 1) by omega] at hout
    obtain ⟨hd, hr, hl⟩ := replay_loop I (I.L - 1) vals (Nat.le_refl _) _ _ hout
    exact ⟨fun q h1 h2 => hd q h1 (Nat.le_sub_one_of_lt h2), hr, hl⟩

/-! ## Stream positions along the draws -/

theorem kAt_succ_ge {I : SInst} (hd : Draws I) {m : Nat} (hm : m + 1 < I.L) :
    I.kAt m + 1 ≤ I.kAt (m + 1) ∧
      ∃ j, genAt 64 (I.L - m) I.key (I.kAt m) = some (j, I.kAt (m + 1)) := by
  obtain ⟨j, k', hg⟩ := hd (I.L - 1 - m) (by omega) (by omega)
  have e : I.kBefore (I.L - 1 - m) = I.kAt m := by unfold SInst.kBefore; congr 1; omega
  rw [e, show I.L - 1 - m + 1 = I.L - m by omega] at hg
  have hk : I.kAt (m + 1) = k' := by rw [SInst.kAt, hg]; rfl
  obtain ⟨t, -, hk', -⟩ := (genAt_some_iff 64 _ _ _ _ _).1 hg
  exact ⟨by omega, j, by rw [hk]; exact hg⟩

theorem kAt_mono {I : SInst} (hd : Draws I) : ∀ m, m + 1 ≤ I.L → I.kstart + m ≤ I.kAt m
  | 0, _ => Nat.le_refl _
  | m + 1, h => by
    have := kAt_mono hd m (by omega)
    have := (kAt_succ_ge hd (m := m) (by omega)).1
    omega

theorem kAt_le_top {I : SInst} (hd : Draws I) : ∀ m d, m + d + 1 ≤ I.L → I.kAt m ≤ I.kAt (m + d)
  | _, 0, _ => Nat.le_refl _
  | m, d + 1, h => by
    have := kAt_le_top hd m d (by omega)
    have := (kAt_succ_ge hd (m := m + d) (by omega)).1
    rw [show m + (d + 1) = m + d + 1 by omega]
    omega

theorem kBefore_le {I : SInst} (hd : Draws I) {q : Nat} (hq : q < I.L) :
    I.kstart ≤ I.kBefore q ∧ I.kBefore q ≤ I.kBefore 0 := by
  unfold SInst.kBefore
  refine ⟨by have := kAt_mono hd (I.L - 1 - q) (by omega); omega, ?_⟩
  have := kAt_le_top hd (I.L - 1 - q) q (by omega)
  rwa [show I.L - 1 - q + q = I.L - 1 - 0 by omega] at this

/-! ## The shuffled list is a permutation -/

theorem fyLoop_perm (js : Nat → Nat) : ∀ (i : Nat) (l : List Nat), (fyLoop js i l).Perm l
  | 0, _ => List.Perm.refl _
  | i + 1, _ => (fyLoop_perm js i _).trans (ZkFormal.NearV3.Sched.swapAt_perm _ _ _)

theorem final_perm (I : SInst) : I.final.Perm I.vals := fyLoop_perm _ _ _

theorem final_length (I : SInst) : I.final.length = I.L := (final_perm I).length_eq

end ZkFormal.NearV3.Render.ChachaBus
