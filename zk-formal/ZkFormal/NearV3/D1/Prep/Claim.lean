import ZkFormal.NearV3.D1.Prep.Spec
import ZkFormal.NearV3.Sched.Pub.Prep

/-!
# `ZkFormal.NearV3.D1.Prep.Claim` — scheduler facts of `prepClaimD1` and `prepD1` (P2)

Lane `v3-d1-phase2`, item P2 (for the generated link copies, L1).  D0a's
`prepClaim_sched` / `prepClaim_seed` / `prepClaim_len` (`Sched/Pub/Prep`), with the same proofs,
for `prepClaimD1` (`prepClaim` without the two transaction checks); then the `prepD1` forms
(`prepD1_sched`, `prepD1_seed`, `prepD1_len`, `prepD1_fwd_lt`, `prepD1_fwd_links`).
-/

namespace ZkFormal.NearV3.D1

open NearSpec NearSpecV3 NearSpecV3.Scheduler ZkFormal.NearV3.Sched ZkFormal.NearV3.D1.Public

set_option maxHeartbeats 4000000 in
theorem prepClaimD1_sched {cb : Bytes} {pc : PrepCD1} (h : prepClaimD1 cb = .ok pc) :
    ∀ sp ∈ pc.pc.sched, SchedPubOk sp := by
  unfold prepClaimD1 at h
  repeat' (first
    | (obtain ⟨_, _, h⟩ := bind_ok h)
    | (split at h)
    | (dsimp only at h))
  all_goals try (cases h; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals
    simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
    exact sched_close (by assumption) (by assumption) (by assumption) (by assumption)
      (by assumption) (fun ctx sp hc => by
        split at hc
        · simp only [pure, Except.pure, Except.ok.injEq] at hc; subst hc; assumption
        · cases hc)

set_option maxHeartbeats 4000000 in
theorem prepClaimD1_seed {cb : Bytes} {pc : PrepCD1} (h : prepClaimD1 cb = .ok pc) :
    ∀ sp ∈ pc.pc.sched, sp.seed.length = 32 := by
  unfold prepClaimD1 at h
  repeat' (first
    | (obtain ⟨_, _, h⟩ := bind_ok h)
    | (split at h)
    | (dsimp only at h))
  all_goals try (cases h; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals
    simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
    exact seed_close (by assumption) (by assumption) (by assumption) (by assumption)
      (by assumption) (by assumption) (by assumption) (fun ctx sp hc => by
        split at hc
        · simp only [pure, Except.pure, Except.ok.injEq] at hc; subst hc; assumption
        · cases hc)

set_option maxHeartbeats 4000000 in
theorem prepClaimD1_len {cb : Bytes} {pc : PrepCD1} (h : prepClaimD1 cb = .ok pc) :
    pc.pc.sched.length ≤ 33 := by
  unfold prepClaimD1 at h
  repeat' (first
    | (obtain ⟨_, _, h⟩ := bind_ok h)
    | (split at h)
    | (dsimp only at h))
  all_goals try (cases h; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals
    simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
    exact len_close (by assumption) (by assumption) (by assumption) (by assumption)

variable {cb : Bytes} {h : HintD1} {p : PrepD1}

theorem prepD1_sched (hp : prepD1 cb h = .ok p) : ∀ sp ∈ p.base.sched, SchedPubOk sp := by
  obtain ⟨w, hw, rfl⟩ := prepD1_spec hp
  exact prepClaimD1_sched hw.claim

theorem prepD1_seed (hp : prepD1 cb h = .ok p) : ∀ sp ∈ p.base.sched, sp.seed.length = 32 := by
  obtain ⟨w, hw, rfl⟩ := prepD1_spec hp
  exact prepClaimD1_seed hw.claim

theorem prepD1_len (hp : prepD1 cb h = .ok p) : p.base.sched.length ≤ 33 := by
  obtain ⟨w, hw, rfl⟩ := prepD1_spec hp
  exact prepClaimD1_len hw.claim

/-- `prepD1`'s forwarding demands are the link-keyed ones of the B2 context and the outgoing
receipts. -/
theorem prepD1_fwd_links (hp : prepD1 cb h = .ok p) :
    ∃ pc out, prepClaimD1 cb = .ok pc ∧ p.base.fwd = fwdLinks pc.pc.ctxB2 out := by
  obtain ⟨w, hw, rfl⟩ := prepD1_spec hp
  exact ⟨_, _, hw.claim, rfl⟩

theorem prepD1_fwd_lt (hp : prepD1 cb h = .ok p) : ∀ x ∈ p.base.fwd, x.2 < 2 ^ 24 := by
  obtain ⟨w, hw, rfl⟩ := prepD1_spec hp
  intro x hx
  have := List.all_eq_true.mp hw.fwdDemand x hx
  simp only [decide_eq_true_eq] at this
  unfold fwdDemandMax at this
  exact this

end ZkFormal.NearV3.D1
