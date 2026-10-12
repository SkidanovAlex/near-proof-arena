import ZkFormal.NearV3.Assembly.PrepContext

/-!
# ZkFormal.NearV3.Assembly.LinkPrepCtx — the prepared context from the walked blocks (soundness)

`prepClaim_native_context` (`PrepContext`) under only the two block lookups (`k.blks[b2i]`,
`k.blks[b2i+1]`) instead of a whole `NativeValid` execution: the prepared claim's context and
header fields are those of the walked chunk (same proof; it uses only those two facts).
-/

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Sched

namespace LinkPrepCtx

private theorem mapError_ok_iff {ε ε' α : Type} (f : ε → ε') (x : Except ε α) (a : α) :
    x.mapError f = .ok a ↔ x = .ok a := by cases x <;> simp [Except.mapError]

set_option maxHeartbeats 4000000 in
theorem prepClaim_context_of {cb : Bytes} {pc : PrepC} {k : WalkD0}
    {m : MainExecutionV3}
    -- unused; keeps the automatic hypothesis names of the copied proof
    (w : StateWitness)
    (hp : prepClaim cb = .ok pc) (hw : walkD0 cb = .ok k)
    (hmb : k.blks[k.b2i]? = some m.block) (hmp : k.blks[k.b2i + 1]? = some m.previous) :
    NativePrepContext k m pc := by
  unfold prepClaim at hp
  repeat' (first
    | (obtain ⟨_, hs, hn⟩ := bind_ok hp; clear hp; have hp := hn; clear hn)
    | (split at hp)
    | (dsimp only at hp))
  all_goals try (cases hp; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals
    simp only [pure, Except.pure, Except.ok.injEq] at hp
    subst hp
    simp_all only [mapError_ok_iff, pure, Except.pure, Except.ok.injEq]
    unfold walkD0 at hw
    simp only [*, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hw
    repeat' (first
      | (have hh := hw; clear hw; obtain ⟨_, _, hw⟩ := bind_ok hh; clear hh)
      | (split at hw)
      | (dsimp only at hw))
    all_goals try (cases hw; done)
    all_goals try (exfalso; exact throw_ne (by assumption))
    all_goals
      simp only [pure, Except.pure, Except.ok.injEq] at hw
      subst hw
      expose_names
      have hb2 : w_23 = i_3 := by grind only
      have hslot : p_1.2 = w_31 := by
        rw [←hb2,heq_2] at heq_8
        simp only [Option.bind_some,heq_5,Option.some.injEq] at heq_8
        grind only
      constructor <;> dsimp only [MainExecutionV3.ctx] <;> grind only

theorem mapM_cons_ok {α β ε : Type} {f : α → Except ε β} {a : α} {l : List α} {s : List β}
    (h : (a :: l).mapM f = .ok s) : ∃ x xs, f a = .ok x ∧ s = x :: xs := by
  rw [List.mapM_cons] at h
  cases hf : f a with
  | error e => rw [hf] at h; cases h
  | ok x =>
    rw [hf] at h
    cases hl : l.mapM f with
    | error e => rw [hl] at h; cases h
    | ok xs =>
      rw [hl] at h
      cases h
      exact ⟨x, xs, rfl, rfl⟩

set_option maxHeartbeats 4000000 in
/-- The scheduler input of the main (B2) instance is the prepared context's. -/
theorem prepClaim_sched0 {cb : Bytes} {pc : PrepC} (h : prepClaim cb = .ok pc) :
    ∃ h0 : 0 < pc.sched.length, schedPub pc.ctxB2 = some pc.sched[0] := by
  unfold prepClaim at h
  repeat' (first
    | (obtain ⟨_, _, h⟩ := bind_ok h)
    | (split at h)
    | (dsimp only at h))
  all_goals try (cases h; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals
    simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
    obtain ⟨x, xs, hx, hs⟩ := mapM_cons_ok (by assumption)
    subst hs
    refine ⟨Nat.succ_pos _, ?_⟩
    dsimp only [List.getElem_cons_zero]
    split at hx
    · simp only [pure, Except.pure, Except.ok.injEq] at hx; subst hx; assumption
    · cases hx

end LinkPrepCtx

end ZkFormal.NearV3.Assembly
