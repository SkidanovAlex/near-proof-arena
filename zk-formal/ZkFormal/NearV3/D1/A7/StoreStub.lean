import ZkFormal.NearV3.Spec.StoreBuild

/-!
# `ZkFormal.NearV3.D1.A7.StoreStub` — `buildFor` over keys that end at a hash not in the store

Lane `v3-d1-a7b` (plan §5 R-5 → (B), the spec-level core of `A7D1Step`).  D0a's
`StoreBuild.buildFor_spec` needs every key's lookup to be **determined** in the stored trie `t`
(`t.find k ≠ none`).  `checkD1`'s main pre trie is built over `mainKeys ++ txKeys`, and an
unread transaction key may end at an unrevealed child or value of the record trie.  `walkU`'s
stub terminal proves that such a hash is **not in the store**; then `buildFor` stops there
too, and the built trie still refines `t`.

* `Stub s t k`: the lookup of `k` in `t` reaches a `.hash h` subtree, or an exactly matched
  `.ref` value slot of hash `h`, with `storeGet s h = none`;
* **`buildFor_spec_stub`**: if every key is determined in `t` or a stub, `buildFor s f t.hashOf
  keys` refines `t` (hence has its root hash) and answers `find` exactly as `t` on every
  determined key within fuel — D0a's `buildFor_spec` with the weaker key hypothesis.
-/

namespace ZkFormal.NearV3.D1

open NearSpec NearSpecV3 ZkFormal.NearV3

mutual
/-- The lookup of `key` in `t` ends at a hash (a child, or an exactly matched value) that the
store does not hold. -/
def Stub (s : Store) : PTrie → List Nat → Prop
  | .hash h, _ => storeGet s h = none
  | .leaf k v _, key => k = key ∧ ∃ len h, v = .ref len h ∧ storeGet s h = none
  | .ext k c _, key => isPrefix k key = true ∧ Stub s c (key.drop k.length)
  | .branch v _ _, [] => ∃ len h, v = some (.ref len h) ∧ storeGet s h = none
  | .branch _ cs _, n :: rest => KStub s cs n rest
def KStub (s : Store) : Kids → Nat → List Nat → Prop
  | .nil, _, _ => False
  | .none _, 0, _ => False
  | .some c _, 0, key => Stub s c key
  | .none r, i + 1, key => KStub s r i key
  | .some _ r, i + 1, key => KStub s r i key
end

/-- `mkSlot` on a stored slot whose wanted lookup is determined or a stub. -/
theorem mkSlot_spec' (s : Store) (v : Slot) (want : Bool) (hs : SlotStored s v)
    (hw : want = true → v.get ≠ none ∨ ∃ len h, v = .ref len h ∧ storeGet s h = none) :
    SlotRefines (mkSlot s v.len (slotHash v) want) v ∧
      (want = true → v.get ≠ none → mkSlot s v.len (slotHash v) want = v) := by
  cases v with
  | val b =>
    simp only [SlotStored, Found] at hs
    cases want
    · simp [mkSlot, SlotRefines, slotHash, Slot.len]
    · simp [mkSlot, slotHash, Slot.len, hs, SlotRefines]
  | ref len h =>
    cases want
    · simp [mkSlot, SlotRefines, slotHash, Slot.len]
    · rcases hw rfl with hn | ⟨len', h', he, hg⟩
      · simp [Slot.get] at hn
      · cases he
        refine ⟨?_, fun _ hn => by simp [Slot.get] at hn⟩
        simp [mkSlot, slotHash, Slot.len, hg, SlotRefines]

theorem kids_spec_stub (s : Store) (f : Nat) (g : Bytes → List (List Nat) → PTrie)
    (hg : ∀ (c : PTrie) (ks : List (List Nat)), c.wf = true → Stored s c →
      (∀ k ∈ ks, c.find k ≠ none ∨ Stub s c k) →
      (g c.hashOf ks).refinedBy c ∧ ∀ k ∈ ks, c.find k ≠ none → fdepth c k ≤ f →
        (g c.hashOf ks).find k = c.find k) :
    ∀ (cs : Kids) (i : Nat) (keys : List (List Nat)), Kids.all (fun c => c.wf = true) cs →
      KidsStored s cs →
      (∀ n rest, (i + n) :: rest ∈ keys → Kids.find cs n rest ≠ none ∨ KStub s cs n rest) →
      Kids.refinedBy (buildKidsWith g i (Kids.optHashes cs) keys) cs ∧
      ∀ n rest, (i + n) :: rest ∈ keys → Kids.find cs n rest ≠ none → kfdepth cs n rest ≤ f →
        Kids.find (buildKidsWith g i (Kids.optHashes cs) keys) n rest = Kids.find cs n rest
  | .nil, i, keys, _, _, _ => by
    refine ⟨by simp [Kids.optHashes, buildKidsWith, Kids.refinedBy], ?_⟩
    intro n rest _ _ _
    simp [Kids.optHashes, buildKidsWith]
  | .none r, i, keys, hw, hs, hp => by
    have ih := kids_spec_stub s f g hg r (i + 1) keys hw hs (fun n rest h => by
      have := hp (n + 1) rest (by rwa [show i + (n + 1) = i + 1 + n by omega])
      simpa [Kids.find, KStub] using this)
    refine ⟨by simpa [Kids.optHashes, buildKidsWith, Kids.refinedBy] using ih.1, ?_⟩
    intro n rest hm hn hd
    cases n with
    | zero => simp [Kids.optHashes, buildKidsWith, Kids.find]
    | succ n =>
      simp only [Kids.optHashes, buildKidsWith, Kids.find]
      exact ih.2 n rest (by rwa [show i + 1 + n = i + (n + 1) by omega]) (by simpa [Kids.find] using hn)
        (by simpa [kfdepth] using hd)
  | .some c r, i, keys, hw, hs, hp => by
    have ih := kids_spec_stub s f g hg r (i + 1) keys hw.2 hs.2 (fun n rest h => by
      have := hp (n + 1) rest (by rwa [show i + (n + 1) = i + 1 + n by omega])
      simpa [Kids.find, KStub] using this)
    let ks := (keys.filter (fun k => k.head? == some i)).map (·.drop 1)
    have hmem : ∀ k ∈ ks, i :: k ∈ keys := by
      intro k hk
      simp only [ks, List.mem_map, List.mem_filter, beq_iff_eq] at hk
      obtain ⟨key, ⟨hkey, hhd⟩, rfl⟩ := hk
      cases key with
      | nil => simp at hhd
      | cons x xs => simp at hhd; subst hhd; simpa using hkey
    have hmem' : ∀ k, i :: k ∈ keys → k ∈ ks := by
      intro k hk
      simp only [ks, List.mem_map, List.mem_filter, beq_iff_eq]
      exact ⟨i :: k, ⟨hk, rfl⟩, rfl⟩
    have hc := hg c ks hw.1 hs.1 (fun k hk => by
      have := hp 0 k (by simpa using hmem k hk)
      simpa [Kids.find, KStub] using this)
    refine ⟨?_, ?_⟩
    · simp only [Kids.optHashes, buildKidsWith, Kids.refinedBy]
      exact ⟨hc.1, ih.1⟩
    · intro n rest hm hn hd
      cases n with
      | zero =>
        simp only [Kids.optHashes, buildKidsWith, Kids.find]
        exact hc.2 rest (hmem' rest (by simpa using hm)) (by simpa [Kids.find] using hn)
          (by simpa [kfdepth] using hd)
      | succ n =>
        simp only [Kids.optHashes, buildKidsWith, Kids.find]
        exact ih.2 n rest (by rwa [show i + 1 + n = i + (n + 1) by omega]) (by simpa [Kids.find] using hn)
          (by simpa [kfdepth] using hd)

/-- **`buildFor` on a stored trie, over determined or stub keys.** -/
theorem buildFor_spec_stub (s : Store) : ∀ (f : Nat) (t : PTrie) (keys : List (List Nat)),
    t.wf = true → Stored s t → (∀ k ∈ keys, t.find k ≠ none ∨ Stub s t k) →
    (buildFor s f t.hashOf keys).refinedBy t ∧
    ∀ k ∈ keys, t.find k ≠ none → fdepth t k ≤ f → (buildFor s f t.hashOf keys).find k = t.find k := by
  intro f
  induction f with
  | zero =>
    intro t keys _ _ _
    refine ⟨by simp [buildFor, PTrie.refinedBy], ?_⟩
    intro k _ hn hd
    cases t with
    | hash h => exact absurd (find_hash_none h k) hn
    | leaf => simp [fdepth] at hd
    | ext k' c m => simp only [fdepth] at hd; split at hd <;> omega
    | branch v cs m => cases k <;> simp [fdepth] at hd
  | succ f ih =>
    intro t keys hw hs hp
    cases hke : keys.isEmpty with
    | true =>
      have : keys = [] := List.isEmpty_iff.1 hke
      subst this
      refine ⟨?_, by simp⟩
      simp [buildFor, PTrie.refinedBy]
    | false =>
    obtain ⟨k0, hk0⟩ : ∃ k0, k0 ∈ keys := by
      cases keys with
      | nil => simp at hke
      | cons a _ => exact ⟨a, by simp⟩
    cases t with
    | hash h =>
      have hg : storeGet s h = none := by
        rcases hp k0 hk0 with hn | hst
        · exact absurd (find_hash_none h k0) hn
        · simpa [Stub] using hst
      refine ⟨?_, fun k _ hn => absurd (find_hash_none h k) hn⟩
      simp [buildFor, PTrie.hashOf, hke, hg, PTrie.refinedBy]
    | leaf k v m =>
      rw [buildFor_leaf s f keys hke k v m hw hs.1]
      have hsl := mkSlot_spec' s v (keys.any (· == k)) hs.2 (by
        intro hw'
        obtain ⟨k', hk', he⟩ := List.any_eq_true.1 hw'
        have he' : k' = k := by simpa using he
        subst he'
        rcases hp k' hk' with hn | hst
        · left; simp only [PTrie.find, ↓reduceIte] at hn
          intro hv; simp [hv] at hn
        · right; exact hst.2)
      refine ⟨⟨rfl, rfl, hsl.1⟩, ?_⟩
      intro key hkey hn _
      simp only [PTrie.find] at hn ⊢
      by_cases e : k = key
      · subst e
        simp only [↓reduceIte] at hn
        rw [hsl.2 (List.any_eq_true.2 ⟨k, hkey, by simp⟩) (by intro hv; simp [hv] at hn)]
      · simp [e]
    | ext k c m =>
      rw [buildFor_ext s f keys hke k c m hw hs.1]
      have hcw : c.wf = true := (wf_ext hw).2
      let ks := (keys.filter (isPrefix k)).map (·.drop k.length)
      have ihc := ih c ks hcw hs.2 (by
        intro k' hk'
        simp only [ks, List.mem_map, List.mem_filter] at hk'
        obtain ⟨key, ⟨hkey, hpre⟩, rfl⟩ := hk'
        rcases hp key hkey with hn | hst
        · left; simpa [PTrie.find, hpre] using hn
        · right; exact hst.2)
      refine ⟨⟨rfl, rfl, ihc.1⟩, ?_⟩
      intro key hkey hn hd
      simp only [PTrie.find] at hn ⊢
      by_cases hpre : isPrefix k key = true
      · simp only [hpre, ↓reduceIte] at hn ⊢
        apply ihc.2
        · simp only [ks, List.mem_map, List.mem_filter]; exact ⟨key, ⟨hkey, hpre⟩, rfl⟩
        · exact hn
        · simp only [fdepth, hpre, ↓reduceIte] at hd; omega
      · simp [hpre]
    | branch bv cs m =>
      have hcw : Kids.wf cs 16 = true := wf_branch hw
      have hks := kids_spec_stub s f (buildFor s f) (fun c ks h1 h2 h3 => ih c ks h1 h2 h3) cs 0 keys
        (kids_all_wf cs 16 hcw) hs.2.2 (by
          intro n rest hm
          rcases hp (n :: rest) (by simpa using hm) with hn | hst
          · left; simpa [PTrie.find] using hn
          · right; simpa [Stub] using hst)
      cases bv with
      | none =>
        rw [buildFor_branch s f keys hke cs m hw hs.1]
        refine ⟨⟨rfl, trivial, hks.1⟩, ?_⟩
        intro key hkey hn hd
        cases key with
        | nil => simp [PTrie.find]
        | cons n rest =>
          simp only [PTrie.find] at hn ⊢
          exact hks.2 n rest (by simpa using hkey) hn (by simp only [fdepth] at hd; omega)
      | some v =>
        rw [buildFor_branchV s f keys hke v cs m hw hs.1]
        have hsl := mkSlot_spec' s v (keys.any (· == [])) hs.2.1 (by
          intro hw'
          obtain ⟨k', hk', he⟩ := List.any_eq_true.1 hw'
          have he' : k' = [] := by simpa using he
          subst he'
          rcases hp [] hk' with hn | hst
          · left; simp only [PTrie.find] at hn
            intro hv; simp [hv] at hn
          · right
            obtain ⟨len, h, he, hg⟩ := hst
            exact ⟨len, h, Option.some.inj he, hg⟩)
        refine ⟨⟨rfl, hsl.1, hks.1⟩, ?_⟩
        intro key hkey hn hd
        cases key with
        | nil =>
          simp only [PTrie.find] at hn ⊢
          rw [hsl.2 (List.any_eq_true.2 ⟨[], hkey, by simp⟩) (by intro hv; simp [hv] at hn)]
        | cons n rest =>
          simp only [PTrie.find] at hn ⊢
          exact hks.2 n rest (by simpa using hkey) hn (by simp only [fdepth] at hd; omega)

/-- The built trie has the stored trie's root hash. -/
theorem buildFor_hashOf_stub (s : Store) (f : Nat) (t : PTrie) (keys : List (List Nat))
    (hw : t.wf = true) (hs : Stored s t) (hp : ∀ k ∈ keys, t.find k ≠ none ∨ Stub s t k) :
    (buildFor s f t.hashOf keys).hashOf = t.hashOf :=
  PTrie.hashOf_refinedBy _ _ (buildFor_spec_stub s f t keys hw hs hp).1

end ZkFormal.NearV3.D1
