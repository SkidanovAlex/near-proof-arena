import ZkFormal.NearV3.Assembly.ValueIndex

/-!
# Every revealed value of a built partial trie sits at a listed key

`buildFor s f h keys` reveals a value slot only for a key exactly in `keys` (`mkSlot … want` with
`want = keys.any (· == k)`).  **`buildFor_vals_keys`**: every value occurrence `j` of the built trie
(`j < |valsOf t|`) is the `valueIndex` of some listed key.  Hence (with `valueIndex_key_unique`) the
value occurrences of a pre-trie are partitioned by the readers of its key list.
-/
namespace ZkFormal.NearV3.Assembly.VbytesKeys
open NearSpec NearSpecV3

/-- Every value occurrence of `t` is the value index of a key in `keys`. -/
def Good (t : PTrie) (keys : List (List Nat)) : Prop :=
  ∀ j, j < (NearSpecV3.valsOf t).length → ∃ k ∈ keys, valueIndex t k = some j

theorem good_hash (h : Bytes) (keys : List (List Nat)) : Good (.hash h) keys := by
  intro j hj
  simp [NearSpecV3.valsOf, NearSpecV3.occs] at hj

theorem mkSlot_val {s : Store} {len : Nat} {vh : Bytes} {want : Bool} {v : Bytes}
    (h : mkSlot s len vh want = .val v) : want = true := by
  unfold mkSlot at h
  cases want
  · simp at h
  · rfl

theorem good_leaf (s : Store) (len : Nat) (vh : Bytes) (k : List Nat) (mem : Nat) (keys : List (List Nat)) :
    Good (.leaf k (mkSlot s len vh (keys.any (· == k))) mem) keys := by
  intro j hj
  generalize hsl : mkSlot s len vh (keys.any (· == k)) = sl at hj ⊢
  cases sl with
  | ref => simp [NearSpecV3.valsOf, NearSpecV3.occs, NearSpecV3.ownVals, NearSpecV3.slotVal] at hj
  | val v =>
    have hw := mkSlot_val hsl
    simp only [List.any_eq_true, beq_iff_eq] at hw
    obtain ⟨k', hk', rfl⟩ := hw
    have hj0 : j = 0 := by
      simp [NearSpecV3.valsOf, NearSpecV3.occs, NearSpecV3.ownVals, NearSpecV3.slotVal] at hj; omega
    subst hj0
    exact ⟨k', hk', by simp [valueIndex, slotValueIndex]⟩

theorem good_ext (k : List Nat) (c : PTrie) (mem : Nat) (keys : List (List Nat))
    (hc : Good c ((keys.filter (isPrefix k)).map (·.drop k.length))) : Good (.ext k c mem) keys := by
  intro j hj
  have hv : NearSpecV3.valsOf (.ext k c mem) = NearSpecV3.valsOf c := by
    simp [NearSpecV3.valsOf, NearSpecV3.occs, NearSpecV3.ownVals]
  rw [hv] at hj
  obtain ⟨k', hk', hi⟩ := hc j hj
  obtain ⟨key, hkey, rfl⟩ := List.mem_map.mp hk'
  obtain ⟨hkeys, hpre⟩ := List.mem_filter.mp hkey
  exact ⟨key, hkeys, by simp [valueIndex, hpre, hi]⟩

theorem kidValues_some (c : PTrie) (r : Kids) :
    kidValues (.some c r) = NearSpecV3.valsOf c ++ kidValues r := by
  simp [kidValues, NearSpecV3.kOccs, NearSpecV3.valsOf, List.flatMap_append]

theorem kidValues_none (r : Kids) : kidValues (.none r) = kidValues r := by
  simp [kidValues, NearSpecV3.kOccs]

/-- The kids built by `buildKidsWith` from index `i`. -/
theorem good_kids (g : Bytes → List (List Nat) → PTrie) (hg : ∀ ch ks, Good (g ch ks) ks)
    (keys : List (List Nat)) :
    ∀ (hs : List (Option Bytes)) (i j : Nat), j < (kidValues (buildKidsWith g i hs keys)).length →
      ∃ n key, (i + n) :: key ∈ keys ∧ kidValueIndex (buildKidsWith g i hs keys) n key = some j
  | [], i, j, hj => by simp [buildKidsWith, kidValues, NearSpecV3.kOccs] at hj
  | none :: more, i, j, hj => by
    simp only [buildKidsWith, kidValues_none] at hj ⊢
    obtain ⟨n, key, hk, hi⟩ := good_kids g hg keys more (i + 1) j hj
    exact ⟨n + 1, key, by rw [show i + (n + 1) = i + 1 + n by omega]; exact hk, by simpa [kidValueIndex] using hi⟩
  | some ch :: more, i, j, hj => by
    simp only [buildKidsWith, kidValues_some, List.length_append] at hj ⊢
    by_cases hlt : j < (NearSpecV3.valsOf (g ch ((keys.filter (fun k => k.head? == some i)).map (·.drop 1)))).length
    · obtain ⟨k', hk', hi⟩ := hg ch _ j hlt
      obtain ⟨key, hkey, rfl⟩ := List.mem_map.mp hk'
      obtain ⟨hkeys, hhead⟩ := List.mem_filter.mp hkey
      cases key with
      | nil => simp at hhead
      | cons a key =>
        simp only [List.head?_cons, beq_iff_eq, Option.some.injEq] at hhead
        subst hhead
        exact ⟨0, key, by simpa using hkeys, by simpa [kidValueIndex] using hi⟩
    · obtain ⟨n, key, hk, hi⟩ := good_kids g hg keys more (i + 1)
        (j - (NearSpecV3.valsOf (g ch ((keys.filter (fun k => k.head? == some i)).map (·.drop 1)))).length)
        (by omega)
      refine ⟨n + 1, key, by rw [show i + (n + 1) = i + 1 + n by omega]; exact hk, ?_⟩
      simp only [kidValueIndex, hi, Option.map_some, Option.some.injEq]
      omega

theorem good_branch (g : Bytes → List (List Nat) → PTrie) (hg : ∀ ch ks, Good (g ch ks) ks)
    (h : Bytes) (v : Option Slot) (rest : Bytes) (keys : List (List Nat)) (mem : Nat)
    (hv : ∀ x, v = some (.val x) → [] ∈ keys) :
    Good (branchWith g h v rest keys mem) keys := by
  unfold branchWith
  dsimp only
  split
  · exact good_hash h keys
  · intro j hj
    have hvals : NearSpecV3.valsOf (.branch v (buildKidsWith g 0 (kidHashes 16 (leNat (rest.take 2)) (rest.drop 2)) keys) mem) =
        NearSpecV3.optSlotVal v ++ kidValues (buildKidsWith g 0 (kidHashes 16 (leNat (rest.take 2)) (rest.drop 2)) keys) := by
      simp [NearSpecV3.valsOf, NearSpecV3.occs, NearSpecV3.ownVals, kidValues]
    rw [hvals, List.length_append] at hj
    by_cases hlt : j < (NearSpecV3.optSlotVal v).length
    · cases v with
      | none => simp [NearSpecV3.optSlotVal] at hlt
      | some sl =>
        cases sl with
        | ref => simp [NearSpecV3.optSlotVal, NearSpecV3.slotVal] at hlt
        | val x =>
          have hj0 : j = 0 := by simp [NearSpecV3.optSlotVal, NearSpecV3.slotVal] at hlt; omega
          subst hj0
          exact ⟨[], hv x rfl, by simp [valueIndex, optSlotValueIndex, slotValueIndex]⟩
    · obtain ⟨n, key, hk, hi⟩ := good_kids g hg keys (kidHashes 16 (leNat (rest.take 2)) (rest.drop 2)) 0
        (j - (NearSpecV3.optSlotVal v).length) (by omega)
      refine ⟨(0 + n) :: key, hk, ?_⟩
      rw [Nat.zero_add]
      show (kidValueIndex _ n key).map ((NearSpecV3.optSlotVal v).length + ·) = some j
      rw [hi, Option.map_some, Option.some.injEq]
      omega

/-- **Every revealed value of `buildFor s f h keys` is at a listed key.** -/
theorem buildFor_good (s : Store) : ∀ (f : Nat) (h : Bytes) (keys : List (List Nat)),
    Good (buildFor s f h keys) keys := by
  intro f
  induction f with
  | zero => intro h keys; exact good_hash h keys
  | succ f ih =>
    intro h keys
    rw [buildFor]
    split
    · exact good_hash h keys
    · split
      · exact good_hash h keys
      · rename_i node _
        split
        · exact good_hash h keys
        · dsimp only
          split
          · split
            · split
              · exact good_hash h keys
              · exact good_leaf _ _ _ _ _ keys
            · exact good_hash h keys
          · split
            · split
              · exact good_hash h keys
              · exact good_ext _ _ _ keys (ih _ _)
            · exact good_hash h keys
          · exact good_branch _ (fun ch ks => ih ch ks) h none _ keys _ (by simp)
          · split
            · exact good_hash h keys
            · apply good_branch _ (fun ch ks => ih ch ks) h _ _ keys _
              intro x hx
              have := mkSlot_val (Option.some.inj hx)
              simpa using this
          · exact good_hash h keys

theorem partialTrie_vals_keys (ws : List Bytes) (root : Bytes) (keys : List (List Nat)) (j : Nat)
    (hj : j < (NearSpecV3.valsOf (partialTrie ws root keys)).length) :
    ∃ k ∈ keys, valueIndex (partialTrie ws root keys) k = some j :=
  buildFor_good (mkStore ws) trieFuel root keys j hj

end ZkFormal.NearV3.Assembly.VbytesKeys
