import ZkFormal.NearV3.Spec.TrieOps
import ZkFormal.NearV3.Assembly.LinkPartial
import ZkFormal.NearV3.Qv.Reads

/-!
# ZkFormal.NearV3.Assembly.LinkRefine — reads and writes on a pruning of a trie

A pruned trie `P` (`P.refinedBy F`) answers every *revealed* lookup like `F`; a `set` at a
revealed key succeeds on `P` whenever it succeeds on `F`, and keeps the refinement:

* `get_eq_find` — `t.get key = (t.find key).bind id`;
* **`set_refined`** — `P.refinedBy F`, `P.find key = some (some x)`, `F.set key v = some F'` ⇒
  `∃ P', P.set key v = some P' ∧ P'.refinedBy F'`.
-/

namespace ZkFormal.NearV3.Assembly

namespace LinkRefine

open NearSpec

mutual
theorem PTrie.get_eq_find : ∀ (t : PTrie) (key : List Nat), t.get key = (t.find key).bind id
  | .hash _, _ => by simp [PTrie.get, PTrie.find]
  | .leaf k s m, key => by
    simp only [PTrie.get, PTrie.find, beq_iff_eq]
    split <;> cases s.get <;> simp
  | .ext k c m, key => by
    simp only [PTrie.get, PTrie.find]
    split
    · exact PTrie.get_eq_find c _
    · simp
  | .branch v cs m, [] => by
    simp only [PTrie.get, PTrie.find]
    cases v with
    | none => simp
    | some s => cases h : s.get <;> simp [h]
  | .branch v cs m, n :: rest => by
    simp only [PTrie.get, PTrie.find]; exact Kids.get_eq_find cs n rest
theorem Kids.get_eq_find : ∀ (cs : Kids) (n : Nat) (key : List Nat),
    Kids.get cs n key = (Kids.find cs n key).bind id
  | .nil, _, _ => by simp [Kids.get, Kids.find]
  | .none _, 0, _ => by simp [Kids.get, Kids.find]
  | .some c _, 0, key => by simp only [Kids.get, Kids.find]; exact PTrie.get_eq_find c key
  | .none r, i + 1, key => by simp only [Kids.get, Kids.find]; exact Kids.get_eq_find r i key
  | .some _ r, i + 1, key => by simp only [Kids.get, Kids.find]; exact Kids.get_eq_find r i key
end

theorem get_of_find {t : PTrie} {key : List Nat} {x : Bytes} (h : t.find key = some (some x)) :
    t.get key = some x := by
  rw [PTrie.get_eq_find, h]; rfl

theorem find_of_get {t : PTrie} {key : List Nat} {x : Bytes} (h : t.get key = some x) :
    t.find key = some (some x) := by
  rw [PTrie.get_eq_find] at h
  cases hf : t.find key with
  | none => simp [hf] at h
  | some o => cases o with
    | none => simp [hf] at h
    | some y => simp [hf] at h; rw [h]

theorem slot_val_of_get {s : Slot} {x : Bytes} (h : s.get = some x) : s = .val x := by
  cases s with
  | val y => simp [Slot.get] at h; rw [h]
  | ref => simp [Slot.get] at h

theorem slotRefines_val {s₁ s₂ : Slot} {x : Bytes} (hr : SlotRefines s₁ s₂) (h : s₁ = .val x) :
    s₂ = .val x := by
  rcases hr with rfl | ⟨v, rfl, rfl⟩
  · exact h
  · simp at h

mutual
theorem PTrie.set_refined : ∀ (t₁ t₂ : PTrie) (key : List Nat) (v x : Bytes) (t₂' : PTrie),
    t₁.refinedBy t₂ → t₁.find key = some (some x) → t₂.set key v = some t₂' →
    ∃ t₁', t₁.set key v = some t₁' ∧ t₁'.refinedBy t₂'
  | .hash _, _, _, _, _, _, _, hf, _ => by simp [PTrie.find] at hf
  | .leaf k s m, t₂, key, v, x, t₂', hr, hf, hs => by
    cases t₂ with
    | leaf k' s' m' =>
      simp only [PTrie.refinedBy] at hr
      obtain ⟨rfl, rfl, hsr⟩ := hr
      simp only [PTrie.find] at hf
      split at hf
      · rename_i e
        subst e
        have hsx : s.get = some x := by cases h : s.get <;> simp [h] at hf; rw [hf]
        have hs1 := slot_val_of_get hsx
        have hs2 := slotRefines_val hsr hs1
        subst hs1; subst hs2
        simp only [PTrie.set, beq_self_eq_true, ↓reduceIte, Slot.get, Option.map_some,
          Option.some.injEq] at hs
        subst hs
        refine ⟨.leaf k (.val v) m, by simp [PTrie.set, Slot.get], ?_⟩
        simp [PTrie.refinedBy, SlotRefines]
      · simp at hf
    | hash _ => simp [PTrie.refinedBy] at hr
    | ext => simp [PTrie.refinedBy] at hr
    | branch => simp [PTrie.refinedBy] at hr
  | .ext k c m, t₂, key, v, x, t₂', hr, hf, hs => by
    cases t₂ with
    | ext k' c' m' =>
      simp only [PTrie.refinedBy] at hr
      obtain ⟨rfl, rfl, hcr⟩ := hr
      simp only [PTrie.find] at hf
      split at hf
      · rename_i hp
        simp only [PTrie.set, hp, ↓reduceIte] at hs
        cases hc : c'.set (key.drop k.length) v with
        | none => simp [hc] at hs
        | some c₂' =>
          simp only [hc, Option.map_some, Option.some.injEq] at hs
          subst hs
          obtain ⟨c₁', h1, h2⟩ := PTrie.set_refined c c' _ v x c₂' hcr hf hc
          refine ⟨.ext k c₁' m, by simp [PTrie.set, hp, h1], ?_⟩
          simp [PTrie.refinedBy, h2]
      · simp at hf
    | hash _ => simp [PTrie.refinedBy] at hr
    | leaf => simp [PTrie.refinedBy] at hr
    | branch => simp [PTrie.refinedBy] at hr
  | .branch bv cs m, t₂, [], v, x, t₂', hr, hf, hs => by
    cases t₂ with
    | branch bv' cs' m' =>
      simp only [PTrie.refinedBy] at hr
      obtain ⟨rfl, hvr, hcr⟩ := hr
      simp only [PTrie.find] at hf
      cases bv with
      | none => simp at hf
      | some s =>
        have hsx : s.get = some x := by cases h : s.get <;> simp [h] at hf; rw [hf]
        have hs1 := slot_val_of_get hsx
        cases bv' with
        | none => simp [OptSlotRefines] at hvr
        | some s' =>
          simp only [OptSlotRefines] at hvr
          have hs2 := slotRefines_val hvr hs1
          subst hs1; subst hs2
          simp only [PTrie.set, Option.some.injEq] at hs
          subst hs
          refine ⟨.branch (some (.val v)) cs m, by simp [PTrie.set], ?_⟩
          simp [PTrie.refinedBy, OptSlotRefines, SlotRefines, hcr]
    | hash _ => simp [PTrie.refinedBy] at hr
    | leaf => simp [PTrie.refinedBy] at hr
    | ext => simp [PTrie.refinedBy] at hr
  | .branch bv cs m, t₂, n :: rest, v, x, t₂', hr, hf, hs => by
    cases t₂ with
    | branch bv' cs' m' =>
      simp only [PTrie.refinedBy] at hr
      obtain ⟨rfl, hvr, hcr⟩ := hr
      simp only [PTrie.find] at hf
      simp only [PTrie.set] at hs
      cases hc : Kids.set cs' n rest v with
      | none => simp [hc] at hs
      | some cs₂' =>
        simp only [hc, Option.map_some, Option.some.injEq] at hs
        subst hs
        obtain ⟨cs₁', h1, h2⟩ := Kids.set_refined cs cs' n rest v x cs₂' hcr hf hc
        refine ⟨.branch bv cs₁' m, by simp [PTrie.set, h1], ?_⟩
        simp [PTrie.refinedBy, hvr, h2]
    | hash _ => simp [PTrie.refinedBy] at hr
    | leaf => simp [PTrie.refinedBy] at hr
    | ext => simp [PTrie.refinedBy] at hr
theorem Kids.set_refined : ∀ (cs₁ cs₂ : Kids) (n : Nat) (key : List Nat) (v x : Bytes) (cs₂' : Kids),
    Kids.refinedBy cs₁ cs₂ → Kids.find cs₁ n key = some (some x) → Kids.set cs₂ n key v = some cs₂' →
    ∃ cs₁', Kids.set cs₁ n key v = some cs₁' ∧ Kids.refinedBy cs₁' cs₂'
  | .nil, _, _, _, _, _, _, _, hf, _ => by simp [Kids.find] at hf
  | .none _, _, 0, _, _, _, _, _, hf, _ => by simp [Kids.find] at hf
  | .some c r, cs₂, 0, key, v, x, cs₂', hr, hf, hs => by
    cases cs₂ with
    | some c' r' =>
      simp only [Kids.refinedBy] at hr
      obtain ⟨hcr, hrr⟩ := hr
      simp only [Kids.find] at hf
      simp only [Kids.set] at hs
      cases hc : c'.set key v with
      | none => simp [hc] at hs
      | some c₂' =>
        simp only [hc, Option.map_some, Option.some.injEq] at hs
        subst hs
        obtain ⟨c₁', h1, h2⟩ := PTrie.set_refined c c' key v x c₂' hcr hf hc
        exact ⟨.some c₁' r, by simp [Kids.set, h1], by simp [Kids.refinedBy, h2, hrr]⟩
    | nil => simp [Kids.refinedBy] at hr
    | none => simp [Kids.refinedBy] at hr
  | .none r, cs₂, i + 1, key, v, x, cs₂', hr, hf, hs => by
    cases cs₂ with
    | none r' =>
      simp only [Kids.refinedBy] at hr
      simp only [Kids.find] at hf
      simp only [Kids.set] at hs
      cases hc : Kids.set r' i key v with
      | none => simp [hc] at hs
      | some r₂' =>
        simp only [hc, Option.map_some, Option.some.injEq] at hs
        subst hs
        obtain ⟨r₁', h1, h2⟩ := Kids.set_refined r r' i key v x r₂' hr hf hc
        exact ⟨.none r₁', by simp [Kids.set, h1], by simp [Kids.refinedBy, h2]⟩
    | nil => simp [Kids.refinedBy] at hr
    | some => simp [Kids.refinedBy] at hr
  | .some c r, cs₂, i + 1, key, v, x, cs₂', hr, hf, hs => by
    cases cs₂ with
    | some c' r' =>
      simp only [Kids.refinedBy] at hr
      obtain ⟨hcr, hrr⟩ := hr
      simp only [Kids.find] at hf
      simp only [Kids.set] at hs
      cases hc : Kids.set r' i key v with
      | none => simp [hc] at hs
      | some r₂' =>
        simp only [hc, Option.map_some, Option.some.injEq] at hs
        subst hs
        obtain ⟨r₁', h1, h2⟩ := Kids.set_refined r r' i key v x r₂' hrr hf hc
        exact ⟨.some c r₁', by simp [Kids.set, h1], by simp [Kids.refinedBy, h2, hcr]⟩
    | nil => simp [Kids.refinedBy] at hr
    | none => simp [Kids.refinedBy] at hr
end

/-! ## Simulation on a key set -/

/-- `P` is a pruning of `F` answering every key of `ks` like `F`. -/
structure Sim (ks : List (List Nat)) (P F : PTrie) : Prop where
  ref : P.refinedBy F
  agree : ∀ k ∈ ks, P.find k = F.find k

theorem Sim.get {ks : List (List Nat)} {P F : PTrie} (s : Sim ks P F) {k : List Nat} {x : Bytes}
    (hk : k ∈ ks) (h : F.get k = some x) : P.get k = some x :=
  get_of_find (by rw [s.agree k hk]; exact find_of_get h)

theorem Sim.set {ks : List (List Nat)} {P F : PTrie} (s : Sim ks P F) {k : List Nat} (hk : k ∈ ks)
    {x v : Bytes} {F' : PTrie} (hx : F.find k = some (some x)) (h : F.set k v = some F') :
    ∃ P', P.set k v = some P' ∧ Sim ks P' F' := by
  obtain ⟨P', hP', hr⟩ := PTrie.set_refined P F k v x F' s.ref (by rw [s.agree k hk]; exact hx) h
  refine ⟨P', hP', hr, fun k' hk' => ?_⟩
  by_cases e : k' = k
  · subst e
    rw [ZkFormal.NearV3.PTrie.find_set_self _ _ _ _ hP', ZkFormal.NearV3.PTrie.find_set_self _ _ _ _ h]
  · rw [ZkFormal.NearV3.PTrie.find_set_ne _ _ _ _ _ hP' e, ZkFormal.NearV3.PTrie.find_set_ne _ _ _ _ _ h e,
      s.agree k' hk']

/-- **The scheduler step on a simulating pruning.** -/
theorem schedStep_sim {ks : List (List Nat)} {ctx : NearSpecV3.ApplyCtx} {P F Q : PTrie}
    {so : NearSpecV3.SchedOut} (s : Sim ks P F) (hwP : P.wf = true) (hwF : F.wf = true)
    (hk : NearSpecV3.keyBwState ∈ ks)
    (hF : NearSpecV3.schedStep NearSpecV3.prims ctx F = .ok (Q, so)) :
    ∃ P', NearSpecV3.schedStep NearSpecV3.prims ctx P = .ok (P', so) ∧ Sim ks P' Q := by
  have hd : P.find NearSpecV3.keyBwState ≠ none := by
    rw [s.agree _ hk]
    intro hn
    unfold NearSpecV3.schedStep NearSpecV3.readKey at hF
    rw [hn] at hF
    cases hF
  obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp hd
  have hFx : F.find NearSpecV3.keyBwState = some x := by rw [← s.agree _ hk]; exact hx
  have hn : nibblesOk NearSpecV3.keyBwState = true := by decide
  obtain ⟨P', hP'⟩ := LinkPartial.PTrie.upsert_of_find P NearSpecV3.keyBwState so.state hwP hn hd
  unfold NearSpecV3.schedStep NearSpecV3.readKey at hF ⊢
  rw [hFx] at hF
  rw [hx]
  simp only [bind, Except.bind, pure, Except.pure] at hF ⊢
  split at hF
  · rename_i o ho
    split at hF
    · rename_i F' hF'
      simp only [Except.ok.injEq, Prod.mk.injEq] at hF
      obtain ⟨rfl, rfl⟩ := hF
      obtain ⟨F'', hF'', hrf⟩ := PTrie.upsert_refinedBy P F NearSpecV3.keyBwState o.state P' s.ref hP'
      rw [hF'] at hF''
      cases hF''
      rw [hP']
      refine ⟨P', rfl, hrf, fun k' hk' => ?_⟩
      by_cases e : k' = NearSpecV3.keyBwState
      · subst e
        rw [PTrie.find_upsert_self _ _ _ _ hn hP', PTrie.find_upsert_self _ _ _ _ hn hF']
      · rw [PTrie.find_upsert_other _ _ _ _ _ hwP hn e hP', PTrie.find_upsert_other _ _ _ _ _ hwF hn e hF',
          s.agree k' hk']
    · cases hF
  · cases hF

/-! ## The receipts on a simulating pruning -/

/-- Two accumulators that differ only in their tries, the first a simulating pruning. -/
def AccSim (ks : List (List Nat)) (a₁ a₂ : TransferV1.Acc) : Prop :=
  Sim ks a₁.trie a₂.trie ∧ a₁ = { a₂ with trie := a₁.trie }

theorem applyReceipt_sim {ks : List (List Nat)} {c : TransferV1.Ctx} {a₁ a₂ a₂' : TransferV1.Acc}
    {r : Receipt} (hs : AccSim ks a₁ a₂) (hk : accountKeyPath r.receiverId ∈ ks)
    (h : TransferV1.applyReceipt c a₂ r = some a₂') :
    ∃ a₁', TransferV1.applyReceipt c a₁ r = some a₁' ∧ AccSim ks a₁' a₂' := by
  obtain ⟨hS, he⟩ := hs
  rw [he]
  unfold TransferV1.applyReceipt at h ⊢
  cases hg : a₂.trie.get (accountKeyPath r.receiverId) with
  | none => simp [hg] at h
  | some raw =>
    have hg1 := hS.get hk hg
    have hfx := find_of_get hg
    simp only [hg] at h
    simp only [hg1]
    split at h
    · cases h
    · rename_i a ha
      split at h
      · cases h
      · rename_i c1
        simp only [c1, ↓reduceIte]
        split at h
        · cases h
        · rename_i c2
          simp only [c2, ↓reduceIte]
          split at h
          · cases h
          · rename_i c3
            simp only [c3, ↓reduceIte]
            split at h
            · cases h
            · rename_i c4
              simp only [c4, ↓reduceIte]
              split at h
              · cases h
              · rename_i c5
                simp only [c5, ↓reduceIte]
                split at h
                · cases h
                · rename_i F' hF'
                  obtain ⟨P', hP', hS'⟩ := hS.set hk hfx hF'
                  simp only [hP']
                  simp only [Option.some.injEq] at h
                  subst h
                  exact ⟨_, rfl, hS', rfl⟩

theorem applySystemReceipt_sim {ks : List (List Nat)} {a₁ a₂ a₂' : TransferV1.Acc} {r : Receipt}
    (hs : AccSim ks a₁ a₂) (hk : accountKeyPath r.receiverId ∈ ks)
    (hak : (r.signerId == r.receiverId) = true → NearSpecV3.keyAccessKey r.receiverId r.signerPk ∈ ks)
    (h : NearSpecV3.applySystemReceipt a₂ r = .ok a₂') :
    ∃ a₁', NearSpecV3.applySystemReceipt a₁ r = .ok a₁' ∧ AccSim ks a₁' a₂' := by
  obtain ⟨hS, he⟩ := hs
  rw [he]
  unfold NearSpecV3.applySystemReceipt at h ⊢
  dsimp only at h ⊢
  rw [hS.agree _ hk]
  cases hfk : a₂.trie.find (accountKeyPath r.receiverId) with
  | none => rw [hfk] at h; cases h
  | some o =>
    cases o with
    | none => rw [hfk] at h; cases h
    | some raw =>
      rw [hfk] at h
      dsimp only [pure, Except.pure, bind, Except.bind] at h ⊢
      cases hd : Account.decode raw with
      | none => rw [hd] at h; cases h
      | some a =>
        rw [hd] at h
        dsimp only at h ⊢
        have fin : ∀ {F' : PTrie}, a₂.trie.set (accountKeyPath r.receiverId)
            ({ amount := a.amount + r.deposit, locked := a.locked, codeHash := a.codeHash,
               storageUsage := a.storageUsage } : Account).encode = some F' →
            ∃ P', a₁.trie.set (accountKeyPath r.receiverId)
              ({ amount := a.amount + r.deposit, locked := a.locked, codeHash := a.codeHash,
                 storageUsage := a.storageUsage } : Account).encode = some P' ∧ Sim ks P' F' :=
          fun hF' => hS.set hk hfk hF'
        split at h
        · cases h
        · rename_i c1
          rw [if_neg c1]
          split at h
          · cases h
          · rename_i c2
            rw [if_neg c2]
            split at h
            · cases h
            · rename_i c3
              rw [if_neg c3]
              split at h
              · rename_i hsr
                rw [if_pos hsr, hS.agree _ (hak hsr)]
                split at h
                · cases h
                · rename_i hn
                  split at h
                  · cases h
                  · rename_i F' hF'
                    obtain ⟨P', hP', hS'⟩ := fin hF'
                    simp only [hP']
                    cases h
                    exact ⟨_, rfl, hS', rfl⟩
                · rename_i ak hn
                  split at h
                  · cases h
                  · rename_i c4
                    rw [if_neg c4]
                    split at h
                    · cases h
                    · rename_i F' hF'
                      obtain ⟨P', hP', hS'⟩ := fin hF'
                      simp only [hP']
                      cases h
                      exact ⟨_, rfl, hS', rfl⟩
              · rename_i hsr
                rw [if_neg hsr]
                split at h
                · cases h
                · rename_i F' hF'
                  obtain ⟨P', hP', hS'⟩ := fin hF'
                  simp only [hP']
                  cases h
                  exact ⟨_, rfl, hS', rfl⟩

private theorem bok {α β ε : Type} {x : Except ε α} {f : α → Except ε β} {out : β}
    (h : x >>= f = .ok out) : ∃ v, x = .ok v ∧ f v = .ok out := by
  cases x with
  | error e => cases h
  | ok v => exact ⟨v, rfl, h⟩

theorem applyReceipts_sim {ks : List (List Nat)} {ctx : NearSpecV3.ApplyCtx} :
    ∀ (rs : List Receipt) (i : Nat) (a₁ a₂ : TransferV1.Acc) (ls : List NearSpecV3.Limit)
      (out : TransferV1.Acc × List NearSpecV3.Limit),
    AccSim ks a₁ a₂ → (∀ r ∈ rs, accountKeyPath r.receiverId ∈ ks) →
    (∀ r ∈ rs, (r.predecessorId == AccountId.system) = true → (r.signerId == r.receiverId) = true →
      NearSpecV3.keyAccessKey r.receiverId r.signerPk ∈ ks) →
    NearSpecV3.applyReceipts ctx i (a₂, ls) rs = .ok out →
    ∃ a₁', NearSpecV3.applyReceipts ctx i (a₁, ls) rs = .ok (a₁', out.2) ∧ AccSim ks a₁' out.1
  | [], i, a₁, a₂, ls, out, hs, _, _, h => by
    simp only [NearSpecV3.applyReceipts, Except.ok.injEq] at h
    subst h
    exact ⟨a₁, rfl, hs⟩
  | r :: rs, i, a₁, a₂, ls, out, hs, hA, hK, h => by
    have hA' : ∀ r ∈ rs, accountKeyPath r.receiverId ∈ ks := fun r' h' => hA r' (by simp [h'])
    have hK' : ∀ r' ∈ rs, (r'.predecessorId == AccountId.system) = true →
        (r'.signerId == r'.receiverId) = true → NearSpecV3.keyAccessKey r'.receiverId r'.signerPk ∈ ks :=
      fun r' h' => hK r' (by simp [h'])
    have hr1 : a₁.refunds = a₂.refunds := (congrArg TransferV1.Acc.refunds hs.2).trans rfl
    simp only [NearSpecV3.applyReceipts] at h ⊢
    split at h
    · cases h
    · rename_i c0
      rw [if_neg c0]
      split at h
      · rename_i hsys
        rw [if_pos hsys]
        obtain ⟨a₂', h1, h2⟩ := bok h
        obtain ⟨a₁', e1, hs'⟩ := applySystemReceipt_sim hs (hA r (by simp)) (hK r (by simp) hsys) h1
        obtain ⟨a₁'', e2, hs''⟩ := applyReceipts_sim rs (i + 1) a₁' a₂' ls out hs' hA' hK' h2
        exact ⟨a₁'', by rw [e1]; exact e2, hs''⟩
      · rename_i hsys
        rw [if_neg hsys]
        split at h
        · split at h <;> cases h
        · rename_i a₂' e2
          obtain ⟨a₁', e1, hs'⟩ := applyReceipt_sim hs (hA r (by simp)) e2
          have hr2 : a₁'.refunds = a₂'.refunds := (congrArg TransferV1.Acc.refunds hs'.2).trans rfl
          simp only [e1, hr1, hr2]
          obtain ⟨ls', hf, h⟩ := bok h
          rw [hf]
          obtain ⟨a₁'', e3, hs''⟩ := applyReceipts_sim rs (i + 1) a₁' a₂' ls' out hs' hA' hK' h
          exact ⟨a₁'', e3, hs''⟩

/-- The scheduler step changes no other key. -/
theorem schedStep_find_ne {ctx : NearSpecV3.ApplyCtx} {F Q : PTrie} {so : NearSpecV3.SchedOut}
    (hw : F.wf = true) (h : NearSpecV3.schedStep NearSpecV3.prims ctx F = .ok (Q, so))
    {k : List Nat} (hk : k ≠ NearSpecV3.keyBwState) : Q.find k = F.find k := by
  unfold NearSpecV3.schedStep NearSpecV3.readKey at h
  cases hx : F.find NearSpecV3.keyBwState with
  | none => rw [hx] at h; cases h
  | some x =>
    rw [hx] at h
    simp only [bind, Except.bind, pure, Except.pure] at h
    split at h
    · split at h
      · rename_i F' hF'
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact PTrie.find_upsert_other _ _ _ _ _ hw (by decide) hk hF'
      · cases h
    · cases h

/-- **The new-chunk application on a simulating pruning** of a trie whose application succeeds:
same outcomes, refunds, gas and tokens, and a post trie refining the full one. -/
theorem applyNewChunk_sim {ks : List (List Nat)} {ctx : NearSpecV3.ApplyCtx} {P F : PTrie}
    {rs : List Receipt} {out : NearSpecV3.MainOut}
    (s : Sim ks P F) (hwP : P.wf = true) (hwF : F.wf = true)
    (hD : NearSpecV3.keyDelayedIdx ∈ ks) (hB : NearSpecV3.keyBwState ∈ ks)
    (hBI : NearSpecV3.keyBufferedIdx ∈ ks) (hY : NearSpecV3.keyYieldIdx ∈ ks)
    (hG : ∀ v, F.find NearSpecV3.keyBufferedIdx = some v → ∀ sh, NearSpecV3.bufferedShards v = .ok sh →
      ∀ x ∈ sh, NearSpecV3.keyGroupsData x ∈ ks)
    (hA : ∀ r ∈ rs, accountKeyPath r.receiverId ∈ ks)
    (hK : ∀ r ∈ rs, (r.predecessorId == AccountId.system) = true → (r.signerId == r.receiverId) = true →
      NearSpecV3.keyAccessKey r.receiverId r.signerPk ∈ ks)
    (h : NearSpecV3.applyNewChunk NearSpecV3.prims ctx F rs = .ok out) :
    ∃ out', NearSpecV3.applyNewChunk NearSpecV3.prims ctx P rs = .ok out' ∧
      out'.trie.refinedBy out.trie ∧ out' = { out with trie := out'.trie } := by
  unfold NearSpecV3.applyNewChunk at h ⊢
  obtain ⟨delayed, hd, h⟩ := bok h
  obtain ⟨u1, hde, h⟩ := bok h
  obtain ⟨⟨mid, so⟩, hstep, h⟩ := bok h
  dsimp only at h
  obtain ⟨buffered, hb, h⟩ := bok h
  obtain ⟨shards, hbs, h⟩ := bok h
  obtain ⟨u2, hgroups, h⟩ := bok h
  obtain ⟨⟨acc, limits⟩, happly, h⟩ := bok h
  dsimp only at h
  obtain ⟨yielded, hy, h⟩ := bok h
  obtain ⟨u3, hye, h⟩ := bok h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  have hdP : NearSpecV3.readKey P NearSpecV3.keyDelayedIdx "DelayedReceiptIndices" = .ok delayed :=
    (Qv.readKey_iff _ _ _ _).mpr (by rw [s.agree _ hD]; exact (Qv.readKey_iff _ _ _ _).mp hd)
  obtain ⟨P', hstepP, s'⟩ := schedStep_sim s hwP hwF hB hstep
  have hbF := (Qv.readKey_iff _ _ _ _).mp hb
  have hbP : NearSpecV3.readKey P' NearSpecV3.keyBufferedIdx "BufferedReceiptIndices" = .ok buffered :=
    (Qv.readKey_iff _ _ _ _).mpr (by rw [s'.agree _ hBI]; exact hbF)
  have hbF0 : F.find NearSpecV3.keyBufferedIdx = some buffered := by
    rw [← schedStep_find_ne hwF hstep (by decide)]; exact hbF
  have hgF := Qv.groupReads_of_loop mid shards hgroups
  have hgP : forIn shards () (Qv.groupReadStep P') = .ok () :=
    Qv.groupReads_loop P' shards (fun x hx => by
      rw [s'.agree _ (hG buffered hbF0 shards hbs x hx)]; exact hgF x hx)
  obtain ⟨a₁', happlyP, hs''⟩ := applyReceipts_sim rs 0 ⟨P', [], [], 0, 0⟩ ⟨mid, [], [], 0, 0⟩ _ _
    ⟨s', rfl⟩ hA hK happly
  have hyP : NearSpecV3.readKey a₁'.trie NearSpecV3.keyYieldIdx "PromiseYieldIndices" = .ok yielded :=
    (Qv.readKey_iff _ _ _ _).mpr (by rw [hs''.1.agree _ hY]; exact (Qv.readKey_iff _ _ _ _).mp hy)
  refine ⟨⟨a₁'.trie, a₁'.outcomes, a₁'.refunds, a₁'.gasBurnt, a₁'.tokensBurnt⟩, ?_, hs''.1.ref, ?_⟩
  · simp only [hdP, hde, hstepP, hbP, hbs, bind, Except.bind]
    erw [hgP]
    simp only [happlyP, hyP, hye, pure, Except.pure]
  · obtain ⟨-, e⟩ := hs''
    cases a₁'
    simp only [TransferV1.Acc.mk.injEq] at e
    obtain ⟨-, e1, e2, e3, e4⟩ := e
    simp [e1, e2, e3, e4]

end LinkRefine

end ZkFormal.NearV3.Assembly
