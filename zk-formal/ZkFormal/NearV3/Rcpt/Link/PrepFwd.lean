import ZkFormal.NearV3.Rcpt.Link.ForwardSound

/-!
# ZkFormal.NearV3.Rcpt.Link.PrepFwd — the native forwarding / compute checks of `prepBody`

`prepBody pc h = .ok p` decodes the hint body into the refund list and checks, natively,
(i) every refund routes to a status shard, (ii) `fwdGasOk`, (iii) each forwarding demand
`< 2^24`, and the compute guard `n = 0 ∨ (n − 1)·G < gas_limit`; it publishes the demands as
`p.fwd = fwdLinks ctx refunds` and `n` as `p.hdr.n`.  **`prepD0_fwd`** extracts these facts.
-/

namespace ZkFormal.NearV3.RcptLink

open NearSpec NearSpec.TransferV1 NearSpecV3 ZkFormal.NearV3.Sched

/-- What `prepBody` checks about the refunds and `n`. -/
structure PrepFwd (ctx : ApplyCtx) (h : Hint) (p : Prep) (refunds : List Receipt) : Prop where
  body : decodeBody h.body = .ok refunds
  status : (refunds.all fun r => (statusShards ctx).contains (ctx.layout.shardOf r.receiverId)) = true
  gas : fwdGasOk ctx refunds = true
  demand : ((fwdLinks ctx refunds).all fun (_, d) => decide (d < fwdDemandMax)) = true
  compute : h.n = 0 ∨ (h.n - 1) * Params.G < ctx.gasLimit
  fwd : p.fwd = fwdLinks ctx refunds
  n : p.hdr.n = h.n

theorem prepBody_fwd {pc : PrepC} {h : Hint} {p : Prep} (hp : prepBody pc h = .ok p) :
    ∃ refunds, PrepFwd pc.ctxB2 h p refunds := by
  unfold prepBody at hp
  obtain ⟨refunds, hb, hp⟩ := bind_ok hp
  obtain ⟨_, h1, hp⟩ := bind_ok hp
  obtain ⟨_, h2, hp⟩ := bind_ok hp
  obtain ⟨_, h3, hp⟩ := bind_ok hp
  obtain ⟨_, h4, hp⟩ := bind_ok hp
  iterate 8 (obtain ⟨_, _, hp⟩ := bind_ok hp)
  have c4 := check_ok h4
  dsimp only at hp
  cases hm : encodedMerkleRoot pc.rsData pc.rsTotal h.body with
  | none =>
    rw [hm] at hp
    obtain ⟨_, he, _⟩ := bind_ok hp
    exact absurd he (fun e => throw_ne e)
  | some el =>
    obtain ⟨emr, len⟩ := el
    rw [hm] at hp
    dsimp only at hp
    obtain ⟨_, _, hp⟩ := bind_ok hp
    obtain ⟨_, _, hp⟩ := bind_ok hp
    simp only [pure, Except.pure, Except.ok.injEq] at hp
    subst hp
    simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at c4
    exact ⟨refunds, hb, check_ok h1, check_ok h2, check_ok h3, c4, rfl, rfl⟩

/-- **The native forwarding / compute facts** of an accepted preparation. -/
theorem prepD0_fwd {cb : Bytes} {h : Hint} {p : Prep} (hp : prepD0 cb h = .ok p) :
    ∃ pc refunds, prepClaim cb = .ok pc ∧ PrepFwd pc.ctxB2 h p refunds := by
  obtain ⟨pc, hc, hb⟩ := bind_ok hp
  obtain ⟨refunds, hr⟩ := prepBody_fwd hb
  exact ⟨pc, refunds, hc, hr⟩

end ZkFormal.NearV3.RcptLink
