import ZkFormal.NearV3.Assembly.Forward

/-!
# ZkFormal.NearV3.Rcpt.Link.ForwardSound — the forwarding split is sound

`prepBody` replaces the runtime's interleaved `tryForward` fold by three checks (PrepD0 module
doc, "Forwarding split", there only *tested*): (i) every refund routes to a status shard,
(ii) the gas-only simulation `fwdGasOk` passes, (iii) per status shard `s` the total capped size
of the refunds to `s` is at most the grant `grant(own, s)` ((i), (ii) native; (iii) the AIR's
`Prep.fwd` check).  This module proves the soundness direction:

* `forwardRun_sound` — from a gas-only success, existing limits and per-shard size demands
  below the current size limits, the exact runtime forwarding fold succeeds;
* **`forwardRun_of_split`** — at the initial limits of `applyNewChunk`, (i)–(iii) imply
  `forwardRun ctx limits0 rs = .ok ls'` (`Assembly.forwardRun`, the fold of `applyReceipts`).
-/

namespace ZkFormal.NearV3.RcptLink

open NearSpec NearSpec.TransferV1 NearSpecV3 ZkFormal.NearV3.Assembly

/-- The capped size `tryForward` charges. -/
def fsize (r : Receipt) : Nat := min r.encode.length maxReceiptSize

/-- Total capped size of the refunds routed to shard `s` (`fwdSizes`' summand). -/
def demand (ctx : ApplyCtx) (rs : List Receipt) (s : Nat) : Nat :=
  ((rs.filter fun r => ctx.layout.shardOf r.receiverId == s).map fsize).sum

/-- The initial forwarding limits of `applyNewChunk` for grants `grant`. -/
def limits0 (ctx : ApplyCtx) (grant : Nat → Nat → Nat) : List Limit :=
  ctx.statuses.map fun (s, ci, missed) =>
    ⟨s, if s == ctx.own then GASMAX else prims.outGas ci missed ctx.own, grant ctx.own s⟩

theorem demand_cons (ctx : ApplyCtx) (r : Receipt) (rs : List Receipt) (s : Nat) :
    demand ctx (r :: rs) s =
      (if ctx.layout.shardOf r.receiverId == s then fsize r else 0) + demand ctx rs s := by
  unfold demand
  by_cases h : ctx.layout.shardOf r.receiverId = s
  · simp [List.filter_cons, h]
  · simp [List.filter_cons, h]

theorem gasView_get' (ls : List Limit) (s : Nat) :
    (((gasView ls).find? (·.1 == s)).map (·.2)).getD GASMAX = (Limit.get ls s).gas := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
    simp only [gasView, List.map_cons, List.find?_cons, Limit.get] at *
    split <;> simp_all

theorem get_put_same (ls : List Limit) (l : Limit) (hex : ∃ x ∈ ls, x.shard = l.shard) :
    Limit.get (Limit.put ls l) l.shard = l := by
  have hany : ls.any (·.shard == l.shard) = true := by
    obtain ⟨x, hx, he⟩ := hex
    exact List.any_eq_true.mpr ⟨x, hx, beq_iff_eq.mpr he⟩
  simp only [Limit.put, hany, ↓reduceIte]
  clear hany
  induction ls with
  | nil => simp at hex
  | cons a rest ih =>
    by_cases ha : a.shard = l.shard
    · simp [Limit.get, ha]
    · have ht : ∃ x ∈ rest, x.shard = l.shard := by
        obtain ⟨x, hx, he⟩ := hex
        rcases List.mem_cons.mp hx with rfl | hx
        · exact False.elim (ha he)
        · exact ⟨x, hx, he⟩
      simpa [Limit.get, ha] using ih ht

theorem get_put_other (ls : List Limit) (l : Limit) (s : Nat) (hex : ∃ x ∈ ls, x.shard = l.shard)
    (hne : s ≠ l.shard) : Limit.get (Limit.put ls l) s = Limit.get ls s := by
  have hany : ls.any (·.shard == l.shard) = true := by
    obtain ⟨x, hx, he⟩ := hex
    exact List.any_eq_true.mpr ⟨x, hx, beq_iff_eq.mpr he⟩
  simp only [Limit.put, hany, ↓reduceIte]
  clear hany hex
  induction ls with
  | nil => rfl
  | cons a rest ih =>
    by_cases ha : a.shard = l.shard
    · simp [Limit.get, ha, Ne.symm hne] at *
      exact ih
    · by_cases hs : a.shard = s
      · simp [Limit.get, hs, hne]
      · simpa [Limit.get, ha, hs] using ih

/-- **One forwarding step**: the gas-only step succeeds and the size fits. -/
theorem tryForward_ok {ctx : ApplyCtx} {ls : List Limit} {r : Receipt} {gl : List (Nat × Nat)}
    (hg : gasForward ctx (gasView ls) r = some gl)
    (hs : fsize r ≤ (Limit.get ls (ctx.layout.shardOf r.receiverId)).size) :
    tryForward ctx ls r = some (Limit.put ls ⟨ctx.layout.shardOf r.receiverId,
      (Limit.get ls (ctx.layout.shardOf r.receiverId)).gas - refundCongestionGas r.receiverId,
      (Limit.get ls (ctx.layout.shardOf r.receiverId)).size - fsize r⟩) := by
  unfold gasForward at hg
  dsimp only at hg
  rw [gasView_get'] at hg
  split at hg
  · rename_i hc
    unfold tryForward
    dsimp only
    have hc2 : (Limit.get ls (ctx.layout.shardOf r.receiverId)).size ≥
        min r.encode.length maxReceiptSize := hs
    simp only [hc, hc2, decide_true, Bool.and_self, ↓reduceIte]
    rfl
  · cases hg

theorem forwardRun_sound (ctx : ApplyCtx) :
    ∀ (rs : List Receipt) (ls : List Limit),
      (rs.foldlM (gasForward ctx) (gasView ls)).isSome = true →
      (∀ r ∈ rs, ∃ l ∈ ls, l.shard = ctx.layout.shardOf r.receiverId) →
      (∀ s, demand ctx rs s ≤ (Limit.get ls s).size) →
      ∃ ls', forwardRun ctx ls rs = .ok ls'
  | [], ls, _, _, _ => ⟨ls, rfl⟩
  | r :: rs, ls, hg, hex, hd => by
    simp only [List.foldlM_cons] at hg
    cases hg1 : gasForward ctx (gasView ls) r with
    | none => rw [hg1] at hg; simp at hg
    | some gl =>
      rw [hg1] at hg
      have hsz : fsize r ≤ (Limit.get ls (ctx.layout.shardOf r.receiverId)).size := by
        have := hd (ctx.layout.shardOf r.receiverId)
        rw [demand_cons] at this
        simp only [beq_self_eq_true, ↓reduceIte] at this
        omega
      have ht := tryForward_ok hg1 hsz
      have hgv := tryForward_gas ht
      rw [hg1, Option.some.injEq] at hgv
      have hex0 := hex r List.mem_cons_self
      obtain ⟨ls', h'⟩ := forwardRun_sound ctx rs _ (by rw [← hgv]; exact hg)
        (fun r' hr' => by
          obtain ⟨l, hl, he⟩ := hex r' (List.mem_cons_of_mem _ hr')
          have hm : l.shard ∈ ls.map Limit.shard := List.mem_map.mpr ⟨l, hl, rfl⟩
          rw [← tryForward_shards ht] at hm
          obtain ⟨l', hl', he'⟩ := List.mem_map.mp hm
          exact ⟨l', hl', he'.trans he⟩)
        (fun s => by
          have hds := hd s
          rw [demand_cons] at hds
          by_cases hs : ctx.layout.shardOf r.receiverId = s
          · subst hs
            have := get_put_same ls ⟨ctx.layout.shardOf r.receiverId,
              (Limit.get ls (ctx.layout.shardOf r.receiverId)).gas - refundCongestionGas r.receiverId,
              (Limit.get ls (ctx.layout.shardOf r.receiverId)).size - fsize r⟩ hex0
            rw [this]
            simp only [beq_self_eq_true, ↓reduceIte] at hds
            dsimp only
            omega
          · rw [get_put_other ls _ s hex0 (Ne.symm hs)]
            have hb : (ctx.layout.shardOf r.receiverId == s) = false := by simpa using hs
            simp only [hb, Bool.false_eq_true, ↓reduceIte, Nat.zero_add] at hds
            exact hds)
      refine ⟨ls', ?_⟩
      unfold forwardRun
      simp only [List.foldlM_cons, ht, bind, Except.bind]
      exact h'

theorem foldl_bind' {α β : Type} (f : β → α → Option β) :
    ∀ (xs : List α) (acc : Option β),
      xs.foldl (fun a x => a.bind (f · x)) acc = acc.bind (xs.foldlM f)
  | [], acc => by cases acc <;> rfl
  | x :: xs, acc => by
    simp only [List.foldl_cons, List.foldlM_cons]
    rw [foldl_bind']
    cases acc <;> rfl

theorem get_limits0_size (ctx : ApplyCtx) (grant : Nat → Nat → Nat) (s : Nat) :
    ∀ (sts : List (Nat × Congestion × Nat)), s ∈ sts.map (·.1) →
      (Limit.get (sts.map fun (s, ci, missed) =>
        (⟨s, if s == ctx.own then GASMAX else prims.outGas ci missed ctx.own, grant ctx.own s⟩ : Limit))
        s).size = grant ctx.own s
  | [], h => by simp at h
  | (s', ci, m) :: sts, h => by
    by_cases hs : s' = s
    · subst hs; simp [Limit.get]
    · have h' : s ∈ sts.map (·.1) := by
        simp only [List.map_cons, List.mem_cons] at h
        rcases h with h | h
        · exact absurd h.symm hs
        · exact h
      have ih := get_limits0_size ctx grant s sts h'
      simpa [Limit.get, hs] using ih

/-- **Soundness of the forwarding split** at the initial limits of `applyNewChunk`. -/
theorem forwardRun_of_split {ctx : ApplyCtx} {grant : Nat → Nat → Nat} {rs : List Receipt}
    (hst : (rs.all fun r => (statusShards ctx).contains (ctx.layout.shardOf r.receiverId)) = true)
    (hgas : fwdGasOk ctx rs = true)
    (hsz : ∀ s ∈ statusShards ctx, demand ctx rs s ≤ grant ctx.own s) :
    ∃ ls', forwardRun ctx (limits0 ctx grant) rs = .ok ls' := by
  have hst' : ∀ r ∈ rs, ctx.layout.shardOf r.receiverId ∈ ctx.statuses.map (·.1) := by
    intro r hr
    have := List.all_eq_true.mp hst r hr
    exact (statusShards_mem ctx _).mp (List.contains_iff_mem.mp this)
  apply forwardRun_sound ctx rs
  · unfold fwdGasOk at hgas
    change (rs.foldl (fun acc r => acc.bind (gasForward ctx · r))
      (some (ctx.statuses.map fun (s, ci, missed) =>
        (s, if s == ctx.own then GASMAX else prims.outGas ci missed ctx.own)))).isSome = true at hgas
    rw [foldl_bind'] at hgas
    simp only [Option.bind_some] at hgas
    have he : gasView (limits0 ctx grant) = ctx.statuses.map (fun (s, ci, missed) =>
        (s, if s == ctx.own then GASMAX else prims.outGas ci missed ctx.own)) := by
      simp [gasView, limits0, List.map_map, Function.comp_def]
    rw [he]
    exact hgas
  · intro r hr
    obtain ⟨st, hst, he⟩ := List.mem_map.mp (hst' r hr)
    exact ⟨_, List.mem_map.mpr ⟨st, hst, rfl⟩, he⟩
  · intro s
    by_cases hs : s ∈ ctx.statuses.map (·.1)
    · unfold limits0
      rw [get_limits0_size ctx grant s _ hs]
      exact hsz s ((statusShards_mem ctx s).mpr hs)
    · have h0 : demand ctx rs s = 0 := by
        unfold demand
        have : rs.filter (fun r => ctx.layout.shardOf r.receiverId == s) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro r hr
          have := hst' r hr
          simp only [beq_iff_eq]
          intro he; exact hs (he ▸ this)
        rw [this]; rfl
      omega

end ZkFormal.NearV3.RcptLink
