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

/-- The D0a-shaped claim part of `prepClaimD1` (the generated link copies take
`prepClaimC cb = .ok pc` where D0a has `prepClaim cb = .ok pc`). -/
def prepClaimC (cb : Bytes) : Except String PrepC := (prepClaimD1 cb).map PrepCD1.pc

theorem prepClaimC_ok {cb : Bytes} {pc : PrepC} (h : prepClaimC cb = .ok pc) :
    ∃ r, prepClaimD1 cb = .ok r ∧ r.pc = pc := by
  unfold prepClaimC at h
  cases e : prepClaimD1 cb with
  | error _ => rw [e] at h; cases h
  | ok r => rw [e] at h; exact ⟨r, rfl, by simpa [Except.map] using h⟩

theorem prepClaimC_of {cb : Bytes} {r : PrepCD1} (h : prepClaimD1 cb = .ok r) : prepClaimC cb = .ok r.pc := by
  unfold prepClaimC; rw [h]; rfl

variable {cb : Bytes} {h : HintD1} {p : PrepD1}

theorem prepD1_claimC (hp : prepD1 cb h = .ok p) :
    ∃ pc, prepClaimC cb = .ok pc ∧ p.base.sched = pc.sched ∧ p.base.lists = pc.lists ∧
      p.base.bnds = pc.bnds := by
  obtain ⟨w, hw, rfl⟩ := prepD1_spec hp
  exact ⟨_, prepClaimC_of hw.claim, rfl, rfl, rfl⟩

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

/-! ## The body part (for the generated link copies)

D0a's link reads `prepD0` as `prepClaim cb = .ok pc` and `prepBody pc hint = .ok p`.  The copies
read `prepD1` as `prepClaimC cb = .ok pc` and `BodyD1 pc hint p` (`prepD1_split`); the
`prepBody_*` facts that hold verbatim in D1 are `bodyD1_*`. -/

/-- The body part of a successful `prepD1` whose claim part is `pc`. -/
def BodyD1 (pc : PrepC) (h : HintD1) (p : Prep) : Prop :=
  ∃ cb, ∃ w : PrepD1Run, w.Ok cb h ∧ w.pc = pc ∧ (w.prep h).base = p

theorem prepD1_split {cb : Bytes} {h : HintD1} {q : PrepD1} {p : Prep}
    (hp : prepD1 cb h = .ok q ∧ q.base = p) : ∃ pc, prepClaimC cb = .ok pc ∧ BodyD1 pc h p := by
  obtain ⟨hp, rfl⟩ := hp
  obtain ⟨w, hw, rfl⟩ := prepD1_spec hp
  exact ⟨w.pc, prepClaimC_of hw.claim, cb, w, hw, rfl, rfl⟩

section
variable {pc : PrepC} {h : HintD1} {p : Prep}

theorem bodyD1_sched (hb : BodyD1 pc h p) : p.sched = pc.sched := by
  obtain ⟨_, w, -, rfl, rfl⟩ := hb; rfl

theorem bodyD1_shape (hb : BodyD1 pc h p) :
    p.hdr.K = pc.hdr.K ∧ p.sched = pc.sched ∧ p.lists = pc.lists ∧
      p.hdr.prevStateRoot = pc.hdr.prevStateRoot ∧
      p.hdr.postStateRoot = pc.hdr.postStateRoot ∧ p.hdr.outcomeRoot = pc.hdr.outcomeRoot := by
  obtain ⟨_, w, -, rfl, rfl⟩ := hb; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem bodyD1_gasPrice (hb : BodyD1 pc h p) : p.hdr.gasPrice = pc.hdr.gasPrice := by
  obtain ⟨_, w, -, rfl, rfl⟩ := hb; rfl

theorem bodyD1_height (hb : BodyD1 pc h p) : p.hdr.height = pc.hdr.height := by
  obtain ⟨_, w, -, rfl, rfl⟩ := hb; rfl

theorem bodyD1_outcomeRoot (hb : BodyD1 pc h p) : p.hdr.outcomeRoot = pc.hdr.outcomeRoot := by
  obtain ⟨_, w, -, rfl, rfl⟩ := hb; rfl

theorem bodyD1_routing_intervals (hb : BodyD1 pc h p) : p.bnds = pc.bnds := by
  obtain ⟨_, w, -, rfl, rfl⟩ := hb; rfl

theorem bodyD1_source_owner (hb : BodyD1 pc h p) : p.hdr.own = pc.hdr.own := by
  obtain ⟨_, w, -, rfl, rfl⟩ := hb; rfl

end

end ZkFormal.NearV3.D1
