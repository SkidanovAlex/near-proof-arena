import ZkFormal.NearV3.D1.PrepD1
import ZkFormal.NearV3.Assembly.PrepFacts

/-!
# `ZkFormal.NearV3.D1.Prep.Facts` — shape facts of a successful `prepD1` (P2, part 1)

Lane `v3-d1-phase2`, item P2.  `prepClaimD1` is `prepClaim` (D0a) without two checks; the
proofs here are D0a's `PrepFacts` ones for it (`prepClaim_roots`, `prepClaim_source_roots`).
`prepD1_base` writes the D0a-shaped part `p.base` of a successful `prepD1` in terms of the
claim part; then `prepD1_roots` (`RootsSized p.base`) and `prepD1_source_roots` follow, which
the D1 public bindings need (`D1/Public/Split`, `NewSegs`).
-/

namespace ZkFormal.NearV3.D1

open NearSpec NearSpecV3 Sched ZkFormal.NearV3.Assembly ZkFormal.NearV3.D1.Public

theorem forIn_post' {α β : Type} (P : β → Prop)
    (f : α → β → Except String (ForInStep β)) :
    ∀ (xs : List α) (b out : β), P b →
      (∀ a ∈ xs, ∀ b step, P b → f a b = .ok step →
        match step with | .done v => P v | .yield v => P v) →
      forIn xs b f = .ok out → P out
  | [], b, out, hb, _, h => by
    simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ hb
  | a :: xs, b, out, hb, hf, h => by
    rw [List.forIn_cons] at h
    obtain ⟨step, hs, h⟩ := bind_ok h
    have hp := hf a (by simp) b step hb hs
    cases step with
    | done v => cases h; exact hp
    | yield v =>
      exact forIn_post' P f xs v out hp (fun a ha => hf a (by simp [ha])) h

theorem shuffle_roots' {xs ys : List SrcList} {seed : Bytes}
    (hx : ∀ s ∈ xs, s.root.length = 32) (h : shuffleWithSeed xs seed = some ys) :
    ∀ s ∈ ys, s.root.length = 32 := by
  unfold shuffleWithSeed at h
  cases hs : shuffle xs (Rng.ofSeed seed) with
  | none => simp [hs] at h
  | some p =>
    have he : p.1 = ys := by simpa [hs] using h
    have hp := shuffle_perm hs
    intro s hmem
    apply hx s
    exact hp.mem_iff.mp (he ▸ hmem)

theorem slotSources_roots' (B : Blk)
    (hb : ∀ x ∈ B.slots, x.2.prevOutgoingReceiptsRoot.length = 32)
    {out : List SrcList}
    (h : (forIn B.slots [] fun x acc =>
      if x.1.heightIncluded == B.hdr.height then
        pure (.yield (acc ++ [⟨chunkHash x.1.inner x.2.encodedMerkleRoot,
          x.2.shardId, x.2.prevOutgoingReceiptsRoot⟩]))
      else pure (.yield acc) : Except String (List SrcList)) = .ok out) :
    ∀ s ∈ out, s.root.length = 32 := by
  apply forIn_post' (fun l => ∀ s ∈ l, s.root.length = 32) _ _ _ _ (by simp) ?_ h
  intro x hx acc step ha hs
  split at hs
  · cases hs
    intro s hmem
    rcases List.mem_append.1 hmem with hm | hm
    · exact ha s hm
    · simpa using (List.mem_singleton.1 hm ▸ hb x hx)
  · cases hs; exact ha

theorem sourceLists_roots' {blocks : List Blk}
    (hb : ∀ B ∈ blocks, ∀ x ∈ B.slots, x.2.prevOutgoingReceiptsRoot.length = 32)
    {out : List SrcList}
    (h : (forIn blocks [] fun B acc => do
      let srcs ← forIn B.slots [] fun x srcs =>
        if x.1.heightIncluded == B.hdr.height then
          pure (.yield (srcs ++ [⟨chunkHash x.1.inner x.2.encodedMerkleRoot,
            x.2.shardId, x.2.prevOutgoingReceiptsRoot⟩]))
        else pure (.yield srcs)
      let shuffled ← match shuffleWithSeed srcs B.hdr.prevHash with
        | some p => pure p
        | none => throw "invalid: shuffle fuel exhausted (probability < 2^-1024)"
      pure (.yield (acc ++ shuffled)) : Except String (List SrcList)) = .ok out) :
    ∀ s ∈ out, s.root.length = 32 := by
  apply forIn_post' (fun l => ∀ s ∈ l, s.root.length = 32) _ _ _ _ (by simp) ?_ h
  intro B hB acc step ha hs
  obtain ⟨srcs, hsrc, hs⟩ := bind_ok hs
  have hr := slotSources_roots' B (hb B hB) hsrc
  split at hs
  · rename_i p hp
    obtain ⟨shuffled, he, hs⟩ := bind_ok hs
    cases he
    cases hs
    intro s hmem
    rcases List.mem_append.1 hmem with hm | hm
    · exact ha s hm
    · exact shuffle_roots' hr hp s hm
  · obtain ⟨_, he, _⟩ := bind_ok hs
    cases he

theorem sourceBlocks_roots' {rs : List BlockRec} {blks : List Blk}
    (hm : rs.mapM decodeBlk = .ok blks) (start count : Nat) :
    ∀ B ∈ (blks.drop start).take count, ∀ x ∈ B.slots,
      x.2.prevOutgoingReceiptsRoot.length = 32 := by
  intro B hB x hx
  have hmem := List.mem_of_mem_drop (List.mem_of_mem_take hB)
  obtain ⟨r, _, hd⟩ := mapM_ok _ _ _ hm B hmem
  exact (decodeBlk_roots hd x.1 x.2 hx).2.2

theorem mapError_ok' {ε ε' α : Type} {x : Except ε α} {f : ε → ε'} {a : α}
    (h : x.mapError f = .ok a) : x = .ok a := by
  cases x <;> cases h
  rfl

theorem roots_close' {rs : List BlockRec} {blks : List Blk} {i idx : Nat}
    {b B2 : Blk} {pair : ChunkSlot × ChunkInner} {slot : ChunkInner}
    (hps : (pure pair.2 : Except String ChunkInner) = .ok slot)
    (hs : B2.slots[idx]? = some pair)
    (hpb : (pure b : Except String Blk) = .ok B2)
    (hb : blks[i]? = some b) (hm : rs.mapM decodeBlk = .ok blks) :
    slot.prevStateRoot.length = 32 := by
  cases hps
  cases hpb
  obtain ⟨r, _, hd⟩ := mapM_ok _ _ _ hm b (List.mem_of_getElem? hb)
  exact (decodeBlk_roots hd pair.1 pair.2 (List.mem_of_getElem? hs)).1

set_option maxHeartbeats 4000000 in
theorem prepClaimD1_roots {cb : Bytes} {pc : PrepCD1} (h : prepClaimD1 cb = .ok pc) :
    pc.pc.hdr.prevStateRoot.length = 32 ∧ pc.pc.hdr.postStateRoot.length = 32 ∧
      pc.pc.hdr.outcomeRoot.length = 32 := by
  unfold prepClaimD1 at h
  repeat' (first
    | (obtain ⟨_, _, h⟩ := bind_ok h)
    | (split at h)
    | (dsimp only at h))
  all_goals try (cases h; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals
    simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
    refine ⟨?_, ?_, ?_⟩
    · exact roots_close' (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
    · exact (decodeChunkInner_roots (mapError_ok' (by assumption))).1
    · exact (decodeChunkInner_roots (mapError_ok' (by assumption))).2.1

set_option maxHeartbeats 4000000 in
theorem prepClaimD1_source_roots {cb : Bytes} {pc : PrepCD1} (h : prepClaimD1 cb = .ok pc) :
    ∀ s ∈ pc.pc.lists, s.root.length = 32 := by
  unfold prepClaimD1 at h
  repeat' (first
    | (obtain ⟨_, _, h⟩ := bind_ok h)
    | (split at h)
    | (dsimp only at h))
  all_goals try (cases h; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals
    simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
    apply sourceLists_roots' ?_ (by assumption)
    exact sourceBlocks_roots' (by assumption) _ _

end ZkFormal.NearV3.D1

namespace ZkFormal.NearV3.D1

open NearSpec NearSpecV3 Sched ZkFormal.NearV3.Assembly ZkFormal.NearV3.D1.Public

set_option maxHeartbeats 4000000 in
/-- The D0a-shaped part of a successful `prepD1`: the claim part's roots and source lists. -/
theorem prepD1_base {cb : Bytes} {h : HintD1} {p : PrepD1} (hp : prepD1 cb h = .ok p) :
    ∃ pc, prepClaimD1 cb = .ok pc ∧ p.base.lists = pc.pc.lists ∧
      p.base.hdr.prevStateRoot = pc.pc.hdr.prevStateRoot ∧
      p.base.hdr.postStateRoot = pc.pc.hdr.postStateRoot ∧
      p.base.hdr.outcomeRoot = pc.pc.hdr.outcomeRoot := by
  unfold prepD1 at hp
  obtain ⟨pc, hc, hp⟩ := bind_ok hp
  refine ⟨pc, hc, ?_⟩
  repeat' (first
    | (obtain ⟨_, _, hp⟩ := bind_ok hp)
    | (split at hp)
    | (dsimp only at hp))
  all_goals try (cases hp; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals
    simp only [pure, Except.pure, Except.ok.injEq] at hp; subst hp
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem prepD1_roots {cb : Bytes} {h : HintD1} {p : PrepD1} (hp : prepD1 cb h = .ok p) :
    ZkFormal.NearV3.Public.RootsSized p.base := by
  obtain ⟨pc, hc, -, h1, h2, h3⟩ := prepD1_base hp
  obtain ⟨r1, r2, r3⟩ := prepClaimD1_roots hc
  exact ⟨h1 ▸ r1, h2 ▸ r2, h3 ▸ r3⟩

theorem prepD1_source_roots {cb : Bytes} {h : HintD1} {p : PrepD1} (hp : prepD1 cb h = .ok p) :
    ∀ s ∈ p.base.lists, s.root.length = 32 := by
  obtain ⟨pc, hc, hl, -⟩ := prepD1_base hp
  rw [hl]; exact prepClaimD1_source_roots hc

end ZkFormal.NearV3.D1
