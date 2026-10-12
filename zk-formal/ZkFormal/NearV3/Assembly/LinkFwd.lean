import ZkFormal.NearV3.Assembly.LinkExec
import ZkFormal.NearV3.Sched.Link.FwdPrep

/-!
# ZkFormal.NearV3.Assembly.LinkFwd — the forwarding premise of `executions` (`hfwd`)

`fwdDemand p.fwd (oi·n + j) ≤ (schedOut o).grant own ids[j]` for the scheduler run `o` of instance
`0`, every `j < n` (`oi` = index of `own`):

* the AIR's τ = 0 check (`LinkSchedCore.schedCore_v3`): `fwdDemand p.fwd l ≤ G l` for every link
  `l < n²` (demands `< 2^24`: `prepD0_fwd_lt`), where the run's grant list is
  `(range n²).map (l ↦ ((ids[l/n], ids[l%n]), G l))`;
* `p.fwd = fwdLinks pc.ctxB2 refunds` (`prepD0_fwd_links`) is keyed by `o·n + indexOf ids s`,
  so a nonzero demand at `oi·n + j` has `j` the first index of `ids[j]` (`demand_first`);
* then `grant own ids[j]` (the first grant entry with that pair) is `G (oi·n + j)` (`grant_at`).
  (Shard ids need not be distinct: a later duplicate has demand `0`.)
-/

namespace ZkFormal.NearV3.Assembly

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near

namespace LinkFwd

open NearSpecV3 NearSpecV3.Scheduler

theorem go_first (x : Nat) : ∀ (ids : List Nat) (k i : Nat), indexOf.go x ids k = some i →
    ∀ i', k ≤ i' → i' < i → ids[i' - k]? ≠ some x
  | [], _, _, h => by simp [indexOf.go] at h
  | y :: ys, k, i, h => by
    intro i' h1 h2
    simp only [indexOf.go] at h
    split at h
    · simp only [Option.some.injEq] at h; omega
    · rename_i hy
      rcases Nat.eq_or_lt_of_le h1 with e | e
      · subst e; simpa using hy
      · have := go_first x ys (k + 1) i h i' (by omega) h2
        rwa [show i' - k = (i' - (k + 1)) + 1 by omega, List.getElem?_cons_succ]

/-- `indexOf` is the first occurrence. -/
theorem indexOf_first {ids : List Nat} {x i : Nat} (h : indexOf ids x = some i) :
    ∀ i', i' < i → ids[i']? ≠ some x := by
  intro i' hi
  have := go_first x ids 0 i h i' (Nat.zero_le _) hi
  simpa using this

/-- A nonzero forwarding demand at `o·n + j` is at a first occurrence `j`. -/
theorem demand_first {ctx : ApplyCtx} {refunds : List NearSpec.Receipt} {o j : Nat}
    (ho : indexOf ctx.layout.shardIds ctx.own = some o) (hj : j < ctx.layout.shardIds.length)
    (hd : ZkFormal.NearV3.Sched.fwdDemand (fwdLinks ctx refunds) (o * ctx.layout.shardIds.length + j) ≠ 0) :
    ∃ s, indexOf ctx.layout.shardIds s = some j := by
  unfold ZkFormal.NearV3.Sched.fwdDemand at hd
  cases hf : (fwdLinks ctx refunds).find? (·.1 == o * ctx.layout.shardIds.length + j) with
  | none => rw [hf] at hd; simp at hd
  | some e =>
    have he := List.mem_of_find?_eq_some hf
    have hk : e.1 = o * ctx.layout.shardIds.length + j := by simpa using List.find?_some hf
    unfold fwdLinks at he
    simp only [ho] at he
    obtain ⟨⟨s, tot⟩, -, hm⟩ := List.mem_filterMap.mp he
    cases hr : indexOf ctx.layout.shardIds s with
    | none => rw [hr] at hm; cases hm
    | some r =>
      rw [hr] at hm
      simp only [Option.map_some, Option.some.injEq] at hm
      subst hm
      have hrl := (ZkFormal.NearV3.Sched.indexOf_spec hr).1
      have hk' : o * ctx.layout.shardIds.length + r = o * ctx.layout.shardIds.length + j := hk
      have : r = j := Nat.add_left_cancel hk'
      exact ⟨s, this ▸ hr⟩

/-- The grant of the first matching link. -/
theorem grant_at {ids : List Nat} {own oi j : Nat} {st : NearSpec.Bytes} {prm : Params}
    {g : Nat → Nat} (hoi : indexOf ids own = some oi) (hj : j < ids.length)
    (hjf : ∀ j', j' < j → ids[j']? ≠ ids[j]?) :
    (schedOut ⟨st, (List.range (ids.length * ids.length)).map
      (fun l => ((ids.getD (l / ids.length) 0, ids.getD (l % ids.length) 0), g l)), prm⟩).grant
        own ids[j] = g (oi * ids.length + j) := by
  have hoil := (ZkFormal.NearV3.Sched.indexOf_spec hoi).1
  have hoiv := (ZkFormal.NearV3.Sched.indexOf_spec hoi).2
  have hof := indexOf_first hoi
  have hl : oi * ids.length + j < ids.length * ids.length := by
    have : (oi + 1) * ids.length ≤ ids.length * ids.length := Nat.mul_le_mul_right _ hoil
    rw [Nat.succ_mul] at this; omega
  have hdiv : (oi * ids.length + j) / ids.length = oi := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hj, Nat.zero_add]
  have hmod : (oi * ids.length + j) % ids.length = j := by rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hj]
  let F : Nat → (Nat × Nat) × Nat :=
    fun l => ((ids.getD (l / ids.length) 0, ids.getD (l % ids.length) 0), g l)
  have hn0 : 0 < ids.length := by omega
  have hf : List.find? (fun x => x.1 == (own, ids[j])) ((List.range (ids.length * ids.length)).map F) =
      some (F (oi * ids.length + j)) := by
    apply List.find?_eq_some_iff_getElem.mpr
    refine ⟨?_, oi * ids.length + j, by simpa using hl, by simp, ?_⟩
    · simp only [F, beq_iff_eq, Prod.mk.injEq]
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, hdiv, hmod, hoiv,
        List.getElem?_eq_getElem hj]
      simp
    · intro l' hl'
      simp only [F, List.getElem_map, List.getElem_range, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq,
        Prod.mk.injEq, not_and]
      intro h1 h2
      have hq : l' / ids.length ≤ oi := by
        apply Nat.le_of_lt_succ
        rw [Nat.div_lt_iff_lt_mul hn0, Nat.succ_mul]; omega
      have hql : l' / ids.length < ids.length := by omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hql] at h1
      rcases Nat.lt_or_eq_of_le hq with hq | hq
      · exact hof _ hq (by rw [List.getElem?_eq_getElem hql]; simpa using h1)
      · have hr : l' % ids.length < j := by
          have := Nat.div_add_mod l' ids.length
          rw [hq] at this
          rw [Nat.mul_comm] at this; omega
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (Nat.mod_lt _ hn0)] at h2
        apply hjf _ hr
        rw [List.getElem?_eq_getElem (Nat.mod_lt _ hn0), List.getElem?_eq_getElem hj]
        simpa using h2
  simp only [schedOut]
  rw [hf]
  rfl

/-- **`hfwd`** of `LinkExec.executions_holds`. -/
theorem hfwd_holds {cb : NearSpec.Bytes} {h : NearSpecV3.Hint} {p : NearSpecV3.Prep}
    {oh : Nat} {tr : Trace Fp} {r : V3Records} (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < ZkFormal.Algebra.P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    (pc : PrepC) (hc : prepClaim cb = .ok pc) (h0 : 0 < p.sched.length) (o : Output)
    (ho : runCore p.sched[0] (ZkFormal.NearV3.Sched.prevOf tr T_CODEC 0) = some o)
    (oi : Nat) (hoi : indexOf pc.ctxB2.layout.shardIds pc.ctxB2.own = some oi)
    (j : Nat) (hj : j < pc.ctxB2.layout.shardIds.length) :
    ZkFormal.NearV3.Sched.fwdDemand p.fwd (oi * pc.ctxB2.layout.shardIds.length + j) ≤
      (schedOut o).grant pc.ctxB2.own pc.ctxB2.layout.shardIds[j] := by
  obtain ⟨pc2, refunds, hc2, hfl⟩ := ZkFormal.NearV3.Sched.prepD0_fwd_links hp
  rw [hc] at hc2; cases hc2
  -- the scheduler input of instance 0
  obtain ⟨pc', hc', hb⟩ := ZkFormal.NearV3.Sched.bind_ok hp
  rw [hc] at hc'; cases hc'
  have hsched : p.sched = pc.sched := (prepBody_shape hb).2.1
  obtain ⟨h0c, hsp⟩ := LinkPrepCtx.prepClaim_sched0 hc
  have hctx : schedPub pc.ctxB2 = some p.sched[0] := by
    rw [hsp]; congr 1; simp only [hsched]
  have hids : p.sched[0].ids = pc.ctxB2.layout.shardIds := ZkFormal.NearV3.Sched.schedPub_ids hctx
  -- the AIR's τ = 0 check and the run's grant list
  obtain ⟨f, m, fc, -, -, -, -, -, -, -, -, -, H⟩ := LinkSchedCore.schedCore_v3 hp hsz hH T W h0
  obtain ⟨hrun, -, -, -, -, -, hfw⟩ := H
  rw [ho] at hrun
  cases hrun
  by_cases hd : ZkFormal.NearV3.Sched.fwdDemand p.fwd (oi * pc.ctxB2.layout.shardIds.length + j) = 0
  · rw [hd]; exact Nat.zero_le _
  obtain ⟨s, hs⟩ := demand_first hoi hj (by rwa [← hfl])
  have hsj := (ZkFormal.NearV3.Sched.indexOf_spec hs).2
  have hjf : ∀ j', j' < j → pc.ctxB2.layout.shardIds[j']? ≠ pc.ctxB2.layout.shardIds[j]? := by
    intro j' hj' e
    rw [hsj] at e
    exact indexOf_first hs j' hj' e
  have hl : oi * pc.ctxB2.layout.shardIds.length + j <
      pc.ctxB2.layout.shardIds.length * pc.ctxB2.layout.shardIds.length := by
    have hoil := (ZkFormal.NearV3.Sched.indexOf_spec hoi).1
    have : (oi + 1) * pc.ctxB2.layout.shardIds.length ≤
        pc.ctxB2.layout.shardIds.length * pc.ctxB2.layout.shardIds.length :=
      Nat.mul_le_mul_right _ hoil
    rw [Nat.succ_mul] at this; omega
  have hle := hfw rfl (oi * pc.ctxB2.layout.shardIds.length + j) (by rw [hids]; exact hl)
    (ZkFormal.NearV3.Sched.fwdDemand_lt (ZkFormal.NearV3.Sched.prepD0_fwd_lt hp) _)
  rw [hids] at hle ⊢
  rw [grant_at hoi hj hjf]
  exact hle

/-- **`executions`** from `HoldsP`, the routing premise and the header semantics. -/
theorem executions_holds' {cb : NearSpec.Bytes} {h : NearSpecV3.Hint} {p : NearSpecV3.Prep}
    {oh : Nat} {tr : Trace Fp} {r : V3Records} (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < ZkFormal.Algebra.P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    {k : NearSpecV3.WalkD0} (hw : NearSpecV3.walkD0 cb = .ok k) (hn : h.n = (flatR r.lists).length)
    {x : ExtV3} (hxn : x.nodes = r.nodes) (hxv : x.values = r.values)
    (hxh : x.heads = LinkImplicit.xHeads (r.ups.map ZkFormal.NearV3.UpsRows.upsE)) (hxr : x.receipts = r.lists)
    {block previous : NearSpecV3.Blk} (hmb : k.blks[k.b2i]? = some block)
    (hmp : k.blks[k.b2i + 1]? = some previous)
    (hroute : ∀ pc, NearSpecV3.prepClaim cb = .ok pc →
      ∀ y ∈ flatR r.lists, pc.ctxB2.layout.shardOf (ZkFormal.Near.toBytes y.v) = pc.ctxB2.own)
    (hhdr : ∀ bs out, (∃ v, (LinkImplicit.Fpre r 0).find NearSpecV3.keyBufferedIdx = some v ∧
        NearSpecV3.bufferedShards v = .ok bs) →
      NearSpecV3.applyNewChunk NearSpecV3.prims
        (NearSpecV3.blockCtx k.L k.H.shardId k.slotB2.gasLimit block previous.hdr.nextGasPrice)
        (LinkImplicit.Fpre r 0) x.applied = .ok out →
      HeaderSemanticsV3 k h p ⟨block, previous, bs, LinkImplicit.Fpre r 0, out⟩ k.H.prevStateRoot) :
    ∃ m last, m.Valid k x ∧ ImplicitRunV3 k x 1 m.result.trie.hashOf k.implicitBlks last ∧
      HeaderSemanticsV3 k h p m last :=
  LinkExec.executions_holds hp hsz hH T W hw hn hxn hxv hxh hxr hmb hmp hroute
    (fun pc hc h0 o ho oi hoi j hj => hfwd_holds hp hsz hH T W pc hc h0 o ho oi hoi j hj) hhdr

end LinkFwd

end ZkFormal.NearV3.Assembly
