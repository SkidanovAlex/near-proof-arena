import ZkFormal.NearV3.Rcpt.Link.ForwardSound
import ZkFormal.NearV3.Rcpt.Link.OwnIntervals
import ZkFormal.NearV3.Sched.Link.GrantFwd
import ZkFormal.NearV3.Sched.Spec.CanonDup
import ZkFormal.NearV3.Sched.Pub.Prep

/-!
# ZkFormal.NearV3.Rcpt.Link.FwdLinks — the per-shard demand check from the link-indexed one (`hsz`)

`prepBody` publishes `p.fwd = fwdLinks ctx refunds`: one `(own·n + idx(s), demand(s))` per status
shard `s` that is a layout shard (status shards outside the layout are dropped).  The AIR checks
`fwdDemand p.fwd l ≤ grant(l)` per link `l < n²` (`Sched.codec_fwd`, lane v3-link).  This module
shows that this suffices for `hsz` (`∀ s ∈ statusShards, demand s ≤ so.grant own s`):

* a refund routes to `shardOf` = `shardIds[partitionPoint]` with `partitionPoint ≤ |boundaries|`,
  so under A12 (`|shardIds| = |boundaries| + 1`) every refund goes to a layout shard; a status
  shard outside the layout receives no refund (demand `0`);
* for a layout status shard `s = ids[r]`, `fwdDemand (fwdLinks …) (o·n + r) = demand s`.

**`hsz_of_links`**: A12 + `own ∈ shardIds` (as `indexOf ids own = some o`) + the link-indexed
check (with the link grant read as `grant own ids[r]`) ⇒ `hsz`.
-/

namespace ZkFormal.NearV3.RcptLink

open NearSpec NearSpec.TransferV1 NearSpecV3 ZkFormal.NearV3.Assembly

theorem shardOf_mem {l : Layout} (hwf : l.shardIds.length = l.boundaries.length + 1) (a : Bytes) :
    l.shardOf a ∈ l.shardIds := by
  have hk := (partitionPoint_spec l.boundaries a).1
  unfold Layout.shardOf
  exact ZkFormal.NearV3.Sched.getD_mem (by omega)

/-- The forwarding record of a layout status shard. -/
theorem fwdDemand_fwdLinks {ctx : ApplyCtx} {refunds : List Receipt} {o r s : Nat}
    (ho : Scheduler.indexOf ctx.layout.shardIds ctx.own = some o)
    (hr : Scheduler.indexOf ctx.layout.shardIds s = some r) (hs : s ∈ statusShards ctx) :
    ZkFormal.NearV3.Sched.fwdDemand (fwdLinks ctx refunds) (o * ctx.layout.shardIds.length + r) =
      demand ctx refunds s := by
  have hrl := (ZkFormal.NearV3.Sched.indexOf_spec hr).1
  have hmem : (o * ctx.layout.shardIds.length + r, demand ctx refunds s) ∈ fwdLinks ctx refunds := by
    simp only [fwdLinks, ho]
    apply List.mem_filterMap.mpr
    refine ⟨(s, demand ctx refunds s), ?_, by simp [hr]⟩
    simp only [fwdSizes, List.mem_map]
    exact ⟨s, hs, rfl⟩
  unfold ZkFormal.NearV3.Sched.fwdDemand
  cases hf : (fwdLinks ctx refunds).find? (·.1 == o * ctx.layout.shardIds.length + r) with
  | none =>
    exfalso
    have := List.find?_eq_none.mp hf _ hmem
    simp at this
  | some e =>
    have he := List.mem_of_find?_eq_some hf
    have hk := List.find?_some hf
    simp only [beq_iff_eq] at hk
    simp only [Option.map_some, Option.getD_some]
    -- `e` is the record of a status shard `s'` with `idx(s') = r' = r`, hence `s' = s`
    simp only [fwdLinks, ho, List.mem_filterMap] at he
    obtain ⟨⟨s', tot⟩, hst, he⟩ := he
    simp only [fwdSizes, List.mem_map] at hst
    obtain ⟨s'', -, hst⟩ := hst
    simp only [Prod.mk.injEq] at hst
    obtain ⟨rfl, rfl⟩ := hst
    cases hr' : Scheduler.indexOf ctx.layout.shardIds s'' with
    | none => simp [hr'] at he
    | some r' =>
      simp only [hr', Option.map_some, Option.some.injEq] at he
      subst he
      have hrl' := (ZkFormal.NearV3.Sched.indexOf_spec hr').1
      have hrr : r' = r := by
        simp only at hk
        have h1 : o * ctx.layout.shardIds.length + r' = o * ctx.layout.shardIds.length + r := hk
        omega
      subst hrr
      have := ZkFormal.NearV3.Sched.indexOf_inj hr' hr
      subst this
      rfl

/-- **`hsz` from the link-indexed forwarding check.** -/
theorem hsz_of_links {ctx : ApplyCtx} {refunds : List Receipt} {grant : Nat → Nat → Nat} {o : Nat}
    (hwf : ctx.layout.shardIds.length = ctx.layout.boundaries.length + 1)
    (ho : Scheduler.indexOf ctx.layout.shardIds ctx.own = some o)
    (hL : ∀ r, (hr : r < ctx.layout.shardIds.length) →
      ZkFormal.NearV3.Sched.fwdDemand (fwdLinks ctx refunds) (o * ctx.layout.shardIds.length + r) ≤
        grant ctx.own ctx.layout.shardIds[r]) :
    ∀ s ∈ statusShards ctx, demand ctx refunds s ≤ grant ctx.own s := by
  intro s hs
  by_cases hin : s ∈ ctx.layout.shardIds
  · obtain ⟨r, hr, hrl⟩ := ZkFormal.NearV3.Sched.indexOf_some_lt hin
    have hids := (ZkFormal.NearV3.Sched.indexOf_spec hr).2
    rw [← fwdDemand_fwdLinks ho hr hs]
    have := hL r hrl
    rwa [show ctx.layout.shardIds[r] = s by
      rw [List.getElem?_eq_getElem hrl] at hids; exact Option.some.inj hids] at this
  · have h0 : demand ctx refunds s = 0 := by
      unfold demand
      rw [List.filter_eq_nil_iff.mpr]
      · rfl
      · intro x _ hx
        simp only [beq_iff_eq] at hx
        exact hin (hx ▸ shardOf_mem hwf _)
    rw [h0]; exact Nat.zero_le _

set_option maxHeartbeats 4000000 in
/-- A12 from `prepClaim`: the context's layout has one boundary fewer than shard ids. -/
theorem prepClaim_layout_wf {cb : Bytes} {pc : PrepC} (h : prepClaim cb = .ok pc) :
    pc.ctxB2.layout.shardIds.length = pc.ctxB2.layout.boundaries.length + 1 := by
  unfold prepClaim at h
  repeat' (first
    | (obtain ⟨_, _, h⟩ := ZkFormal.NearV3.Sched.bind_ok h)
    | (split at h)
    | (dsimp only at h))
  all_goals try (cases h; done)
  all_goals try (exfalso; exact ZkFormal.NearV3.Sched.throw_ne (by assumption))
  all_goals
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    have := ZkFormal.NearV3.Sched.check_ok ‹check (Layout.numShards _ == List.length (Layout.boundaries _) + 1) _ = .ok _›
    simp only [beq_iff_eq, Layout.numShards] at this
    exact this

end ZkFormal.NearV3.RcptLink
