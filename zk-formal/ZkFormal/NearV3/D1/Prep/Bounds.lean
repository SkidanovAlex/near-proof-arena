import ZkFormal.NearV3.D1.Prep.Facts

/-!
# `ZkFormal.NearV3.D1.Prep.Bounds` — the sizes of a successful `prepD1` (P2, part 2)

Lane `v3-d1-phase2`, item P2.  Each transaction adds at most one op, one outcome leaf and one
local receipt (`prepTx_growth`); each local receipt adds exactly one op and one leaf
(`prepLocals_growth`).  With `|txs| ≤ NT0 = 4096` this gives `M0 = |leaves| ≤ 2·NT0` and
`T0 = |ops| ≤ 2·NT0` (`prepD1_m0_t0`), the bounds `ExtOk` needs for `M0`, `T0`.
-/

namespace ZkFormal.NearV3.D1

open NearSpec NearSpecV3 Sched ZkFormal.NearV3.Assembly ZkFormal.NearV3.D1.Public

set_option maxHeartbeats 4000000 in
theorem prepTx_growth {ctx : ApplyCtx} {st st' : TxAcc} {t : Tx} {f : Bool}
    (h : prepTx ctx st t f = .ok st') :
    st'.ops.length ≤ st.ops.length + 1 ∧ st'.leaves.length ≤ st.leaves.length + 1 ∧
      st'.locals.length ≤ st.locals.length + 1 := by
  unfold prepTx at h
  repeat' (first
    | (obtain ⟨_, _, h⟩ := bind_ok h)
    | (split at h)
    | (dsimp only at h))
  all_goals try (cases h; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    (try simp only [List.length_append, List.length_cons, List.length_nil])
    omega

theorem prepTxs_growth {ctx : ApplyCtx} :
    ∀ {st st' : TxAcc} {txs : List (Tx × Bool)}, prepTxs ctx st txs = .ok st' →
      st'.ops.length ≤ st.ops.length + txs.length ∧ st'.leaves.length ≤ st.leaves.length + txs.length ∧
        st'.locals.length ≤ st.locals.length + txs.length
  | st, st', [], h => by
    simp only [prepTxs, Except.ok.injEq] at h
    subst h; simp
  | st, st', (t, f) :: rest, h => by
    simp only [prepTxs] at h
    obtain ⟨s1, h1, h2⟩ := bind_ok h
    have g1 := prepTx_growth h1
    have g2 := prepTxs_growth h2
    simp only [List.length_cons]
    omega

theorem prepLocals_growth {ctx : ApplyCtx} :
    ∀ {st st' : LocAcc} {rs : List Receipt}, prepLocals ctx st rs = .ok st' →
      st'.ops.length = st.ops.length + rs.length ∧ st'.leaves.length = st.leaves.length + rs.length
  | st, st', [], h => by
    simp only [prepLocals, Except.ok.injEq] at h
    subst h; simp
  | st, st', r :: rs, h => by
    simp only [prepLocals] at h
    cases hla : localApply ctx r with
    | none =>
      simp only [hla] at h
      exact absurd h (fun h' => throw_ne h')
    | some v =>
      obtain ⟨leaf, rf, burnt⟩ := v
      simp only [hla] at h
      obtain ⟨_, _, h⟩ := bind_ok h
      have g := prepLocals_growth h
      simp only [List.length_append, List.length_cons, List.length_nil] at g ⊢
      omega

set_option maxHeartbeats 4000000 in
/-- The transaction part of a successful `prepD1`. -/
theorem prepD1_txs {cb : Bytes} {h : HintD1} {p : PrepD1} (hp : prepD1 cb h = .ok p) :
    ∃ (pc : PrepC) (txValid : Bytes) (txs : List Tx) (st : TxAcc) (loc : LocAcc),
      decodeTxVec h.txs = .ok txs ∧ txs.length ≤ NT0 ∧
      prepTxs pc.ctxB2 { bits := h.bits } (txs.zip (txValid.map (· != 0))) = .ok st ∧
      prepLocals pc.ctxB2 ⟨st.ops, st.walks, st.leaves, [], st.tokens⟩ st.locals = .ok loc ∧
      p.m0 = loc.leaves.length ∧ p.t0 = loc.ops.length := by
  unfold prepD1 at hp
  obtain ⟨⟨pc, txValid, txRoot⟩, -, hp⟩ := bind_ok hp
  dsimp only at hp
  obtain ⟨txs, htxs, hp⟩ := bind_ok hp
  obtain ⟨_, _, hp⟩ := bind_ok hp
  obtain ⟨_, _, hp⟩ := bind_ok hp
  obtain ⟨_, hNT, hp⟩ := bind_ok hp
  obtain ⟨_, _, hp⟩ := bind_ok hp
  obtain ⟨_, _, hp⟩ := bind_ok hp
  obtain ⟨_, _, hp⟩ := bind_ok hp
  obtain ⟨st, hst, hp⟩ := bind_ok hp
  obtain ⟨_, _, hp⟩ := bind_ok hp
  obtain ⟨_, _, hp⟩ := bind_ok hp
  obtain ⟨loc, hloc, hp⟩ := bind_ok hp
  have hn : txs.length ≤ NT0 := by simpa using check_ok hNT
  refine ⟨pc, txValid, txs, st, loc, htxs, hn, hst, hloc, ?_⟩
  repeat' (first
    | (obtain ⟨_, _, hp⟩ := bind_ok hp)
    | (split at hp)
    | (dsimp only at hp))
  all_goals try (cases hp; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals
    simp only [pure, Except.pure, Except.ok.injEq] at hp
    subst hp
    exact ⟨rfl, rfl⟩

/-- **`M0` and `T0` of a successful `prepD1`** are at most `2·NT0`. -/
theorem prepD1_m0_t0 {cb : Bytes} {h : HintD1} {p : PrepD1} (hp : prepD1 cb h = .ok p) :
    p.m0 ≤ 2 * NT0 ∧ p.t0 ≤ 2 * NT0 := by
  obtain ⟨pc, txValid, txs, st, loc, -, hn, hst, hloc, hm, ht⟩ := prepD1_txs hp
  have g1 := prepTxs_growth hst
  have g2 := prepLocals_growth hloc
  have hz : (txs.zip (txValid.map (· != 0))).length ≤ txs.length := by
    rw [List.length_zip]; exact Nat.min_le_left _ _
  dsimp only at g1 g2
  simp only [List.length_nil, Nat.zero_add] at g1 g2
  rw [hm, ht]
  omega

end ZkFormal.NearV3.D1

namespace ZkFormal.NearV3.D1

open NearSpec NearSpecV3 Sched ZkFormal.NearV3.Assembly ZkFormal.NearV3.D1.Public

theorem leaf_len (x : OutD1) : x.leaf.length = 32 := by
  unfold OutD1.leaf; split <;> exact ArenaCore.sha256_length _

set_option maxHeartbeats 4000000 in
theorem prepTx_leaves {ctx : ApplyCtx} {st st' : TxAcc} {t : Tx} {f : Bool}
    (h : prepTx ctx st t f = .ok st') (hl : ∀ l ∈ st.leaves, l.length = 32) :
    ∀ l ∈ st'.leaves, l.length = 32 := by
  unfold prepTx at h
  repeat' (first
    | (obtain ⟨_, _, h⟩ := bind_ok h)
    | (split at h)
    | (dsimp only at h))
  all_goals try (cases h; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    intro l hm
    (try simp only [List.mem_append, List.mem_singleton] at hm)
    first
      | exact hl l hm
      | (rcases hm with hm | rfl
         · exact hl l hm
         · exact leaf_len _)

theorem prepTxs_leaves {ctx : ApplyCtx} :
    ∀ {st st' : TxAcc} {txs : List (Tx × Bool)}, prepTxs ctx st txs = .ok st' →
      (∀ l ∈ st.leaves, l.length = 32) → ∀ l ∈ st'.leaves, l.length = 32
  | st, st', [], h, hl => by
    simp only [prepTxs, Except.ok.injEq] at h
    subst h; exact hl
  | st, st', (t, f) :: rest, h, hl => by
    simp only [prepTxs] at h
    obtain ⟨s1, h1, h2⟩ := bind_ok h
    exact prepTxs_leaves h2 (prepTx_leaves h1 hl)

theorem localApply_leaf {ctx : ApplyCtx} {r : Receipt} {leaf : Bytes} {rf : List Receipt} {burnt : Nat}
    (h : localApply ctx r = some (leaf, rf, burnt)) : leaf.length = 32 := by
  unfold localApply at h
  dsimp only at h
  split at h
  · cases h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]; exact leaf_len _

theorem prepLocals_leaves {ctx : ApplyCtx} :
    ∀ {st st' : LocAcc} {rs : List Receipt}, prepLocals ctx st rs = .ok st' →
      (∀ l ∈ st.leaves, l.length = 32) → ∀ l ∈ st'.leaves, l.length = 32
  | st, st', [], h, hl => by
    simp only [prepLocals, Except.ok.injEq] at h
    subst h; exact hl
  | st, st', r :: rs, h, hl => by
    simp only [prepLocals] at h
    cases hla : localApply ctx r with
    | none =>
      simp only [hla] at h
      exact absurd h (fun h' => throw_ne h')
    | some v =>
      obtain ⟨leaf, rf, burnt⟩ := v
      simp only [hla] at h
      obtain ⟨_, _, h⟩ := bind_ok h
      apply prepLocals_leaves h
      intro l hm
      simp only [List.mem_append, List.mem_singleton] at hm
      rcases hm with hm | rfl
      · exact hl l hm
      · exact localApply_leaf hla

set_option maxHeartbeats 4000000 in
/-- The leaves of a successful `prepD1` are 32-byte digests. -/
theorem prepD1_leaves {cb : Bytes} {h : HintD1} {p : PrepD1} (hp : prepD1 cb h = .ok p) :
    ∀ l ∈ p.leaves, l.length = 32 := by
  unfold prepD1 at hp
  obtain ⟨⟨pc, txValid, txRoot⟩, -, hp⟩ := bind_ok hp
  dsimp only at hp
  obtain ⟨txs, -, hp⟩ := bind_ok hp
  obtain ⟨_, _, hp⟩ := bind_ok hp
  obtain ⟨_, _, hp⟩ := bind_ok hp
  obtain ⟨_, _, hp⟩ := bind_ok hp
  obtain ⟨_, _, hp⟩ := bind_ok hp
  obtain ⟨_, _, hp⟩ := bind_ok hp
  obtain ⟨_, _, hp⟩ := bind_ok hp
  obtain ⟨st, hst, hp⟩ := bind_ok hp
  obtain ⟨_, _, hp⟩ := bind_ok hp
  obtain ⟨_, _, hp⟩ := bind_ok hp
  obtain ⟨loc, hloc, hp⟩ := bind_ok hp
  have h1 := prepTxs_leaves hst (by intro l hl; simp at hl)
  have h2 := prepLocals_leaves hloc h1
  repeat' (first
    | (obtain ⟨_, _, hp⟩ := bind_ok hp)
    | (split at hp)
    | (dsimp only at hp))
  all_goals try (cases hp; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals
    simp only [pure, Except.pure, Except.ok.injEq] at hp
    subst hp
    exact h2

end ZkFormal.NearV3.D1
