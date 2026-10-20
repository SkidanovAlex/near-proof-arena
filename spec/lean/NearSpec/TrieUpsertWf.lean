import NearSpec.TrieUpsertProofs

/-!
# `PTrie.upsert` preserves well-formedness — and why `wf` alone is not enough

`TrieUpsertProofs` proves `find_upsert_self` / `find_upsert_other` *given* `t.wf`, but never
carries `wf` through the upsert.  This module does that.

## `wf` alone is not enough

`UpsertPreservesWf` as stated in `ZkFormal.NearV3.D3.StateWrite` —

```
∀ (t u : PTrie) (account key v : Bytes), t.wf = true → cdUpsert t account key v = some u →
  u.wf = true
```

— is **false**.  `ZkFormal.NearV3.D3` proves two independent machine-checked counterexamples
(`not_upsertPreservesWf_valueLen`, `not_upsertPreservesWf_mem`):

* **the value's length.**  `wf` bounds the fields of `t`; the value `v` being written is an
  *argument*.  Upserting `2^32` bytes creates a fresh leaf whose `slotOk (.val v)` — which requires
  `v.length < 2^32` — is false.
* **the recomputed `memory_usage`.**  `upsert` recomputes every usage on the touched path from the
  *stored* ones (`m + c'.memD − cm`), and `wf` only bounds them by `2^64`.  A well-formed
  extension at `2^64 − 1` directly above a leaf overflows.

Neither is about the write's *result*: the post-state is the right key→value map
(`find_upsert_self`/`_other`).  They are about `wf` being a *local* predicate that does not carry
the global facts the recomputation needs.

## The corrected statement

`PTrie.upsert_wf` below: for a nibble-valid key, a `< 2^32` value and `< 2^32` hex prefix, and an
input satisfying

* `t.wf` — the local field bounds;
* `t.memOk` — the **canonical-usage invariant** (`wf` is missing it): every revealed node's stored
  usage is exactly what nearcore computes from its own fields and its revealed children's (so a
  descend's telescoping delta is exact, and each parent's usage is at least each child's);
* `t.memLe memHead` — every usage is below the **headroom** `memHead = 2^64 − 3·2^36`;

the upsert succeeds only as `some t'`, with `t'.wf`, `t'.memOk` and `t'.memLe (memHead + 2·small)`,
where `small = 2^36` bounds both a fresh node and one upsert's growth, so the result's every usage
is below `2^64`.

A real state trie satisfies all three: values are `≤ maxLengthStorageValue` (4 MiB), keys are far
below `2^33` nibbles, usages are the canonical ones, and they are far below `2^64`.
`ZkFormal.NearV3.D3.UpsertPreservesWfWithBounds` is this theorem at the `cdUpsert` entry point.
-/

namespace NearSpec

/-! ## Encoding lengths and `wf` fields -/

theorem packNibbles_length : ∀ l : List Nat, (packNibbles l).length = l.length / 2
  | [] => rfl
  | [_] => by simp [packNibbles]
  | _ :: _ :: rest => by
    simp only [packNibbles, List.length_cons]
    rw [packNibbles_length rest]; omega

theorem hexPrefix_length (k : List Nat) (b : Bool) : (hexPrefix k b).length = k.length / 2 + 1 := by
  unfold hexPrefix
  dsimp only
  split
  next n rest hpar =>
    rw [List.length_cons, packNibbles_length]
    simp only [List.length_cons] at hpar ⊢
    omega
  next nibs _ => rw [List.length_cons, packNibbles_length]

theorem hexPrefix_len_eq (k : List Nat) (b b' : Bool) :
    (hexPrefix k b).length = (hexPrefix k b').length := by
  rw [hexPrefix_length, hexPrefix_length]

theorem hexPrefix_false_of_true {k : List Nat} (hk : (hexPrefix k true).length < 4294967296) :
    (hexPrefix k false).length < 4294967296 := by
  rw [hexPrefix_len_eq k false true]; exact hk

theorem hexPrefix_length_drop_le (k : List Nat) (n : Nat) (b : Bool) :
    (hexPrefix (k.drop n) b).length ≤ (hexPrefix k b).length := by
  rw [hexPrefix_length, hexPrefix_length, List.length_drop]; omega

/-- Every suffix keeps the hex-prefix bound, in either flag. -/
theorem hexPrefix_drop_lt {k : List Nat} (hk : (hexPrefix k true).length < 4294967296)
    (n : Nat) (b : Bool) : (hexPrefix (k.drop n) b).length < 4294967296 := by
  refine Nat.lt_of_le_of_lt (hexPrefix_length_drop_le k n b) ?_
  rw [hexPrefix_length]; rw [hexPrefix_length] at hk; omega

theorem hexPrefix_true_of_false {k : List Nat} (hk : (hexPrefix k false).length < 4294967296) :
    (hexPrefix k true).length < 4294967296 := by
  rw [hexPrefix_len_eq k true false]; exact hk

theorem hexPrefix_drop_lt' {k : List Nat} (hk : (hexPrefix k false).length < 4294967296)
    (n : Nat) (b : Bool) : (hexPrefix (k.drop n) b).length < 4294967296 :=
  hexPrefix_drop_lt (hexPrefix_true_of_false hk) n b

theorem nibblesOk_commonPrefix {a b : List Nat} (ha : nibblesOk a = true) :
    nibblesOk (commonPrefix a b) = true := by
  have h := commonPrefix_left a b
  rw [h] at ha
  exact (nibblesOk_append.1 ha).1

theorem commonPrefix_len_le (k key : List Nat) : (commonPrefix k key).length ≤ k.length := by
  have h := commonPrefix_left k key
  have := congrArg List.length h
  simp only [List.length_append] at this
  omega

theorem nibblesOk_drop' : ∀ (l : List Nat) (n : Nat), nibblesOk l = true → nibblesOk (l.drop n) = true
  | [], _, _ => by simp [nibblesOk]
  | _ :: xs, 0, h => h
  | _ :: xs, n + 1, h => nibblesOk_drop' xs n (nibblesOk_cons.1 h).2

theorem nibblesOk_head {l : List Nat} (h : nibblesOk l = true) {x : Nat} {xs : List Nat}
    (hl : l = x :: xs) : x < 16 := by
  subst hl; exact (nibblesOk_cons.1 h).1

theorem slotOk_len {s : Slot} (h : slotOk s = true) : s.len < 4294967296 := by
  cases s <;> simp_all [slotOk, Slot.len]

theorem wf_leaf_parts' {k : List Nat} {s : Slot} {m : Nat} (h : (PTrie.leaf k s m).wf = true) :
    nibblesOk k = true ∧ slotOk s = true ∧ m < 18446744073709551616 ∧
      (hexPrefix k true).length < 4294967296 := by
  simp only [PTrie.wf, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem wf_ext_parts' {k : List Nat} {c : PTrie} {m : Nat} (h : (PTrie.ext k c m).wf = true) :
    nibblesOk k = true ∧ c.wf = true ∧ m < 18446744073709551616 ∧
      (hexPrefix k false).length < 4294967296 := by
  simp only [PTrie.wf, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem wf_branch_parts' {bv : Option Slot} {cs : Kids} {m : Nat}
    (h : (PTrie.branch bv cs m).wf = true) :
    (∀ s, bv = some s → slotOk s = true) ∧ Kids.wf cs 16 = true ∧
      m < 18446744073709551616 := by
  simp only [PTrie.wf, Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨?_, h.1.2, h.2⟩
  intro s hs
  rw [hs] at h
  simpa using h.1.1

/-! ## The two invariants

`memOk` is the structural fact `wf` is missing — the stored `memory_usage` is the canonical one
nearcore computes from the node's fields and its revealed children's.  `memLe c` bounds every
usage in the subtree by the constant `c`: this is how the *root* headroom reaches every node,
because `memOk` makes each node's usage at most its parent's plus a fresh node's. -/

/-- A branch's own usage: its node cost, plus the value's usage when it has one. -/
def branchOwn : Option Slot → Nat
  | some s => 50 + valueMem s.len
  | none => 50

/-- Sum of a child list's stored usages. -/
def Kids.memSum : Kids → Nat
  | .nil => 0
  | .none r => Kids.memSum r
  | .some c r => c.memD + Kids.memSum r

mutual
/-- **Canonical memory usage.**  Every revealed node's stored usage is the canonical one; above an
unrevealed child nothing is comparable (and `upsert` returns `none` there). -/
def PTrie.memOk : PTrie → Prop
  | .hash _ => True
  | .leaf k s m => m = leafMem k s.len
  | .ext k c m => (c.mem? = none ∨ m = extOwnMem k + c.memD) ∧ c.memOk
  | .branch v cs m => m = branchOwn v + Kids.memSum cs ∧ Kids.memOk cs
def Kids.memOk : Kids → Prop
  | .nil => True
  | .none r => Kids.memOk r
  | .some c r => c.memOk ∧ Kids.memOk r
end

mutual
/-- Every stored usage in the subtree is `< c`. -/
def PTrie.memLe : PTrie → Nat → Prop
  | .hash _, _ => True
  | .leaf _ _ m, c => m < c
  | .ext _ ch m, c => m < c ∧ ch.memLe c
  | .branch _ cs m, c => m < c ∧ Kids.memLe cs c
def Kids.memLe : Kids → Nat → Prop
  | .nil, _ => True
  | .none r, c => Kids.memLe r c
  | .some ch r, c => ch.memLe c ∧ Kids.memLe r c
end

/-- The root headroom: `2^64 - 2^39`.  A fresh node and one upsert's growth are each at most
`4·small = 2^38`, so the result stays below `2^64`. -/
def memHead : Nat := 18446742974197923840
/-- A fresh node's usage, and one upsert's growth, are below this: `2^36`. -/
def small : Nat := 68719476736

theorem memHead_eq : memHead = 18446742974197923840 := rfl
theorem small_eq : small = 68719476736 := rfl
/-- One upsert can grow a node's usage by at most this: `2^38`. -/
def budget : Nat := 343597383680

theorem memHead_room : memHead + 4 * small < 18446744073709551616 := by decide
theorem budget_eq_5small : budget = 5 * small := by decide
theorem memHead_budget : memHead + budget < 18446744073709551616 := by decide
theorem small_le_budget : small ≤ budget := by decide
theorem three_small_le_budget : 3 * small ≤ budget := by decide
theorem two_small_le_budget : 2 * small ≤ budget := by decide
theorem small_lt_memHead2 : small < memHead := by decide
theorem two_small_lt_budget : 3 * small < 2^42 := by decide
theorem small_lt_memHead : small < memHead := by decide

mutual
theorem PTrie.memLe_mono : ∀ (t : PTrie) (c c' : Nat), t.memLe c → c ≤ c' → t.memLe c'
  | .hash _, _, _, _, _ => trivial
  | .leaf _ _ m, _, _, h, hcc => Nat.lt_of_lt_of_le h hcc
  | .ext _ ch _m, c, c', h, hcc => ⟨Nat.lt_of_lt_of_le h.1 hcc, PTrie.memLe_mono ch c c' h.2 hcc⟩
  | .branch _ cs _m, c, c', h, hcc => ⟨Nat.lt_of_lt_of_le h.1 hcc, Kids.memLe_mono cs c c' h.2 hcc⟩
theorem Kids.memLe_mono : ∀ (cs : Kids) (c c' : Nat), Kids.memLe cs c → c ≤ c' → Kids.memLe cs c'
  | .nil, _, _, _, _ => trivial
  | .none r, c, c', h, hcc => Kids.memLe_mono r c c' h hcc
  | .some ch r, c, c', h, hcc => ⟨PTrie.memLe_mono ch c c' h.1 hcc, Kids.memLe_mono r c c' h.2 hcc⟩
end

theorem leafMem_lt_small {k : List Nat} {n : Nat} (hk : (hexPrefix k true).length < 4294967296)
    (hn : n < 4294967296) : leafMem k n < small := by unfold leafMem small; omega

theorem extOwnMem_lt_small {k : List Nat} (hk : (hexPrefix k false).length < 4294967296) :
    extOwnMem k < small := by unfold extOwnMem small; omega

theorem valueMem_lt_small {n : Nat} (hn : n < 4294967296) : valueMem n < small := by
  unfold valueMem small; omega

theorem small_lt_memHead' : small < memHead := by decide

theorem newLeaf_memOk (k : List Nat) (v : Bytes) : (newLeaf k v).memOk := rfl

theorem newLeaf_memLe {k : List Nat} {v : Bytes} (hk : (hexPrefix k true).length < 4294967296)
    (hv : v.length < 4294967296) : (newLeaf k v).memLe memHead :=
  Nat.lt_trans (leafMem_lt_small hk hv) small_lt_memHead'

/-! ## `Kids` structural results -/

theorem wf_kidsFrom : ∀ (n i : Nat) (f : Nat → Option PTrie),
    (∀ j, j < n → ∀ c, f (i + j) = some c → c.wf = true) → Kids.wf (kidsFrom n i f) n = true
  | 0, i, f, _ => by simp [kidsFrom, Kids.wf]
  | n + 1, i, f, h => by
    have hne : (n + 1 != 0) = true := by simp
    have ih := wf_kidsFrom n (i + 1) f (fun j hj d hd => h (j + 1) (by omega) d (by
      have : i + 1 + j = i + (j + 1) := by omega
      rwa [this] at hd))
    cases hf : f i with
    | some c =>
      have hgoal : Kids.wf (Kids.some c (kidsFrom n (i + 1) f)) (n + 1) = true := by
        show ((n + 1) != 0 && c.wf && Kids.wf (kidsFrom n (i + 1) f) n) = true
        rw [hne, Bool.true_and, Bool.and_eq_true]
        exact ⟨h 0 (by omega) c (by simpa using hf), ih⟩
      simpa [kidsFrom, hf] using hgoal
    | none =>
      have hgoal : Kids.wf (Kids.none (kidsFrom n (i + 1) f)) (n + 1) = true := by
        show ((n + 1) != 0 && Kids.wf (kidsFrom n (i + 1) f) n) = true
        rw [hne, Bool.true_and]
        exact ih
      simpa [kidsFrom, hf] using hgoal

theorem memOk_kidsFrom : ∀ (n i : Nat) (f : Nat → Option PTrie),
    (∀ j, j < n → ∀ c, f (i + j) = some c → c.memOk) → Kids.memOk (kidsFrom n i f)
  | 0, i, f, _ => by simp [kidsFrom, Kids.memOk]
  | n + 1, i, f, h => by
    have ih := memOk_kidsFrom n (i + 1) f (fun j hj d hd => h (j + 1) (by omega) d (by
      have : i + 1 + j = i + (j + 1) := by omega
      rwa [this] at hd))
    cases hf : f i with
    | some c =>
      have : Kids.memOk (Kids.some c (kidsFrom n (i + 1) f)) :=
        ⟨h 0 (by omega) c (by simpa using hf), ih⟩
      simpa [kidsFrom, hf] using this
    | none =>
      have : Kids.memOk (Kids.none (kidsFrom n (i + 1) f)) := ih
      simpa [kidsFrom, hf] using this

theorem memLe_kidsFrom : ∀ (n i : Nat) (f : Nat → Option PTrie) (c : Nat),
    (∀ j, j < n → ∀ ch, f (i + j) = some ch → ch.memLe c) → Kids.memLe (kidsFrom n i f) c
  | 0, i, f, c, _ => by simp [kidsFrom, Kids.memLe]
  | n + 1, i, f, c, h => by
    have ih := memLe_kidsFrom n (i + 1) f c (fun j hj d hd => h (j + 1) (by omega) d (by
      have : i + 1 + j = i + (j + 1) := by omega
      rwa [this] at hd))
    cases hf : f i with
    | some ch =>
      have : Kids.memLe (Kids.some ch (kidsFrom n (i + 1) f)) c :=
        ⟨h 0 (by omega) ch (by simpa using hf), ih⟩
      simpa [kidsFrom, hf] using this
    | none =>
      have : Kids.memLe (Kids.none (kidsFrom n (i + 1) f)) c := ih
      simpa [kidsFrom, hf] using this

theorem wf_kids1 {x : Nat} {c : PTrie} (hx : x < 16) (hc : c.wf = true) :
    Kids.wf (kids1 x c) 16 = true := by
  unfold kids1
  apply wf_kidsFrom
  intro j _ d hd
  by_cases hjx : j = x
  · subst hjx
    simp only [Nat.zero_add] at hd
    injection hd with hd; subst hd; exact hc
  · simp [hjx] at hd

theorem wf_kids2 {x y : Nat} {c d : PTrie} (hx : x < 16) (hy : y < 16)
    (hc : c.wf = true) (hd : d.wf = true) : Kids.wf (kids2 x c y d) 16 = true := by
  unfold kids2
  apply wf_kidsFrom
  intro j _ e he
  by_cases hjx : j = x
  · subst hjx
    simp only [Nat.zero_add] at he
    injection he with he; subst he; exact hc
  · by_cases hjy : j = y
    · subst hjy
      simp only [Nat.zero_add, if_neg hjx] at he
      injection he with he; subst he; exact hd
    · simp [hjx, hjy] at he

theorem memOk_kids1 {x : Nat} {c : PTrie} (hc : c.memOk) : Kids.memOk (kids1 x c) := by
  unfold kids1
  apply memOk_kidsFrom
  intro j _ d hd
  by_cases hjx : j = x
  · subst hjx
    simp only [Nat.zero_add] at hd
    injection hd with hd; subst hd; exact hc
  · simp [hjx] at hd

theorem memOk_kids2 {x y : Nat} {c d : PTrie} (hc : c.memOk) (hd : d.memOk) :
    Kids.memOk (kids2 x c y d) := by
  unfold kids2
  apply memOk_kidsFrom
  intro j _ e he
  by_cases hjx : j = x
  · subst hjx
    simp only [Nat.zero_add] at he
    injection he with he; subst he; exact hc
  · by_cases hjy : j = y
    · subst hjy
      simp only [Nat.zero_add, if_neg hjx] at he
      injection he with he; subst he; exact hd
    · simp [hjx, hjy] at he

theorem memLe_kids1 {x : Nat} {c : PTrie} {b : Nat} (hc : c.memLe b) : Kids.memLe (kids1 x c) b := by
  unfold kids1
  apply memLe_kidsFrom
  intro j _ d hd
  by_cases hjx : j = x
  · subst hjx
    simp only [Nat.zero_add] at hd
    injection hd with hd; subst hd; exact hc
  · simp [hjx] at hd

theorem memLe_kids2 {x y : Nat} {c d : PTrie} {b : Nat} (hc : c.memLe b) (hd : d.memLe b) :
    Kids.memLe (kids2 x c y d) b := by
  unfold kids2
  apply memLe_kidsFrom
  intro j _ e he
  by_cases hjx : j = x
  · subst hjx
    simp only [Nat.zero_add] at he
    injection he with he; subst he; exact hc
  · by_cases hjy : j = y
    · subst hjy
      simp only [Nat.zero_add, if_neg hjx] at he
      injection he with he; subst he; exact hd
    · simp [hjx, hjy] at he

end NearSpec

namespace NearSpec

/-! ## `wf` constructors and `wrapExt` -/

theorem newLeaf_wf' {k : List Nat} {v : Bytes} (hk : nibblesOk k = true)
    (hv : v.length < 4294967296) (hp : (hexPrefix k true).length < 4294967296) :
    (newLeaf k v).wf = true := by
  unfold newLeaf
  simp only [PTrie.wf, hk, slotOk, hv, decide_true, Bool.and_true, Bool.true_and]
  have hmem : leafMem k v.length < 18446744073709551616 := by
    have := leafMem_lt_small hp hv; unfold small at this; omega
  rw [show decide (leafMem k v.length < 18446744073709551616) = true from by
    simp [decide_eq_true_eq]; exact hmem]
  simp [hp]

theorem leaf_wf_of' {k : List Nat} {s : Slot} {m : Nat} (hk : nibblesOk k = true)
    (hs : slotOk s = true) (hm : m < 18446744073709551616)
    (hp : (hexPrefix k true).length < 4294967296) : (PTrie.leaf k s m).wf = true := by
  simp [PTrie.wf, hk, hs, hm, hp]

theorem branch_wf_of'' {v : Option Slot} {cs : Kids} {m : Nat}
    (hv : ∀ s, v = some s → slotOk s = true)
    (hcs : Kids.wf cs 16 = true) (hm : m < 18446744073709551616) :
    (PTrie.branch v cs m).wf = true := by
  cases v with
  | none => simp [PTrie.wf, hcs, hm]
  | some s => simp [PTrie.wf, hv s rfl, hcs, hm]

theorem ext_wf_of' {k : List Nat} {c : PTrie} {m : Nat} (hk : nibblesOk k = true)
    (hc : c.wf = true) (hm : m < 18446744073709551616)
    (hp : (hexPrefix k false).length < 4294967296) : (PTrie.ext k c m).wf = true := by
  simp [PTrie.wf, hk, hc, hm, hp]

/-- `wrapExt` preserves `wf` when the fresh extension's usage fits below `2^64`. -/
theorem wrapExt_wf' {p : List Nat} {b : PTrie} (hp : nibblesOk p = true)
    (hp2 : (hexPrefix p false).length < 4294967296) (hb : b.wf = true)
    (hadd : extOwnMem p + b.memD < 18446744073709551616) : (wrapExt p b).wf = true := by
  cases p with
  | nil => exact hb
  | cons x r => exact ext_wf_of' hp hb hadd hp2

theorem extOwnMem_plus_lt64 {p : List Nat} {m : Nat} (hp : extOwnMem p < small)
    (hm : m < memHead + 2 * small) : extOwnMem p + m < 18446744073709551616 := by
  have h1 : memHead = 18446742974197923840 := memHead_eq
  have h2 : small = 68719476736 := small_eq
  have := memHead_room
  omega

theorem small_plus_lt64 {a b : Nat} (ha : a < small) (hb : b < memHead + 2 * small) :
    a + b < 18446744073709551616 := by
  have h1 : memHead = 18446742974197923840 := memHead_eq
  have h2 : small = 68719476736 := small_eq
  have := memHead_room
  omega

/-- `50 + v + l < 2^64` for two fresh nodes of usage `< small`. -/
theorem two_small_lt64 {a b c' : Nat} (ha : a < 60) (hb : b < small) (hc : c' < small) :
    a + b + c' < 18446744073709551616 := by
  have h2 : small = 68719476736 := small_eq
  omega

/-- `50 + a + b < 2^64` with `a, b` fresh usages. -/
theorem fresh_lt64 {a b : Nat} (ha : b < small) (hb : (50:Nat) < 60) :
    b + 50 < 18446744073709551616 := by
  have h2 : small = 68719476736 := small_eq
  omega

theorem small_branch_lt64 {a b : Nat} (ha : a < small) (hb : b < small) :
    50 + a + b < 18446744073709551616 := by
  have h2 : small = 68719476736 := small_eq
  omega

theorem ext_plus_lt_memHead {e m : Nat} (he : e < small) (hm : m < memHead) :
    e + m < memHead + 2 * small := by
  have h1 : memHead = 18446742974197923840 := memHead_eq
  have h2 : small = 68719476736 := small_eq
  omega

/-- `e + b < 2^64` for a fresh extension over a fresh branch. -/
theorem ext_plus_lt64 {e m : Nat} (he : e < small) (hm : m < memHead) :
    e + m < 18446744073709551616 := by
  have h1 : memHead = 18446742974197923840 := memHead_eq
  have h2 : small = 68719476736 := small_eq
  have h3 := memHead_room
  omega

theorem small_branch_lt_memHead {a b : Nat} (ha : a < small) (hb : b < small) :
    50 + a + b < memHead := by
  have h1 : memHead = 18446742974197923840 := memHead_eq
  have h2 : small = 68719476736 := small_eq
  omega

/-! ## The split helpers preserve `wf`

`splitLeaf` and `splitExt` build one fresh branch (or a fresh leaf) under an extension over the
common prefix.  The two hypotheses `hv`/`hp` are about the *inserted* leaf, which did not exist in
the pre-state, so they cannot come from `t.wf`. -/

theorem splitLeaf_wf (k : List Nat) (s : Slot) (key : List Nat) (v : Bytes)
    (hk : nibblesOk k = true) (hs : slotOk s = true) (hkey : nibblesOk key = true)
    (hv : slotOk (.val v) = true)
    (hpk : (hexPrefix k true).length < 4294967296)
    (hpkey : (hexPrefix key true).length < 4294967296) :
    (splitLeaf k s key v).wf = true := by
  have hsv : s.len < 4294967296 := slotOk_len hs
  have hvv : v.length < 4294967296 := slotOk_len hv
  have hcpp : nibblesOk (commonPrefix k key) = true := nibblesOk_commonPrefix hk
  have hcppF : (hexPrefix (commonPrefix k key) false).length < 4294967296 := by
    rw [hexPrefix_length]; rw [hexPrefix_length] at hpk
    have := commonPrefix_len_le k key; omega
  have hcppT : (hexPrefix (commonPrefix k key) true).length < 4294967296 := hexPrefix_true_of_false hcppF
  unfold splitLeaf
  dsimp only
  generalize hkr : k.drop (commonPrefix k key).length = kr
  generalize hyr : key.drop (commonPrefix k key).length = yr
  have hkrOk : nibblesOk kr = true := hkr ▸ nibblesOk_drop' k _ hk
  have hyrOk : nibblesOk yr = true := hyr ▸ nibblesOk_drop' key _ hkey
  have hkrT : (hexPrefix kr true).length < 4294967296 := hkr ▸ hexPrefix_drop_lt hpk _ true
  have hyrT : (hexPrefix yr true).length < 4294967296 := hyr ▸ hexPrefix_drop_lt hpkey _ true
  have bndP : ∀ ys y, yr = y :: ys → (hexPrefix ys true).length < 4294967296 := by
    intro ys y hy
    have e1 : key.drop (commonPrefix k key).length = y :: ys := by rw [hyr]; exact hy
    have e3 : ys = key.drop ((commonPrefix k key).length + 1) := by
      have := congrArg (List.drop 1) e1
      simpa [List.drop_drop, Nat.add_comm] using this.symm
    rw [e3]; exact hexPrefix_drop_lt hpkey _ true
  have bndOk : ∀ ys y, yr = y :: ys → nibblesOk ys = true := by
    intro ys y hy
    have e1 : key.drop (commonPrefix k key).length = y :: ys := by rw [hyr]; exact hy
    have e3 : ys = key.drop ((commonPrefix k key).length + 1) := by
      have := congrArg (List.drop 1) e1
      simpa [List.drop_drop, Nat.add_comm] using this.symm
    rw [e3]; exact nibblesOk_drop' key _ hkey
  have bndPk : ∀ xs x, kr = x :: xs → (hexPrefix xs true).length < 4294967296 := by
    intro xs x hx'
    have e1 : k.drop (commonPrefix k key).length = x :: xs := by rw [hkr]; exact hx'
    have e3 : xs = k.drop ((commonPrefix k key).length + 1) := by
      have := congrArg (List.drop 1) e1
      simpa [List.drop_drop, Nat.add_comm] using this.symm
    rw [e3]; exact hexPrefix_drop_lt hpk _ true
  have bndOkk : ∀ xs x, kr = x :: xs → nibblesOk xs = true := by
    intro xs x hx'
    have e1 : k.drop (commonPrefix k key).length = x :: xs := by rw [hkr]; exact hx'
    have e3 : xs = k.drop ((commonPrefix k key).length + 1) := by
      have := congrArg (List.drop 1) e1
      simpa [List.drop_drop, Nat.add_comm] using this.symm
    rw [e3]; exact nibblesOk_drop' k _ hk
  cases kr with
  | nil =>
    cases yr with
    | nil => exact newLeaf_wf' hkey hvv hpkey
    | cons y ys =>
      have hy : y < 16 := nibblesOk_head hyrOk rfl
      have hysT := bndP ys y rfl
      have hysOk := bndOk ys y rfl
      refine wrapExt_wf' hcpp hcppF ?_ ?_
      · apply branch_wf_of''
        · intro s' hs'; cases hs'; exact hs
        · exact wf_kids1 hy (newLeaf_wf' hysOk hvv hysT)
        · exact small_branch_lt64 (valueMem_lt_small hsv) (leafMem_lt_small hysT hvv)
      · exact ext_plus_lt64 (extOwnMem_lt_small hcppF)
          (small_branch_lt_memHead (valueMem_lt_small hsv) (leafMem_lt_small hysT hvv))
  | cons x xs =>
    have hx : x < 16 := nibblesOk_head hkrOk rfl
    have hxsT := bndPk xs x rfl
    have hxsOk := bndOkk xs x rfl
    have holdwf : (PTrie.leaf xs s (leafMem xs s.len)).wf = true :=
      leaf_wf_of' hxsOk hs (by have h := leafMem_lt_small hxsT hsv; have h3 : small = 68719476736 := small_eq; omega) hxsT
    cases yr with
    | nil =>
      refine wrapExt_wf' hcpp hcppF ?_ ?_
      · apply branch_wf_of''
        · intro s' hs'; cases hs'; exact hv
        · exact wf_kids1 hx holdwf
        · exact small_branch_lt64 (valueMem_lt_small hvv) (leafMem_lt_small hxsT hsv)
      · exact ext_plus_lt64 (extOwnMem_lt_small hcppF)
          (small_branch_lt_memHead (valueMem_lt_small hvv) (leafMem_lt_small hxsT hsv))
    | cons y ys =>
      have hy : y < 16 := nibblesOk_head hyrOk rfl
      have hysT := bndP ys y rfl
      have hysOk := bndOk ys y rfl
      refine wrapExt_wf' hcpp hcppF ?_ ?_
      · apply branch_wf_of''
        · intro s' hs'; simp at hs'
        · exact wf_kids2 hx hy holdwf (newLeaf_wf' hysOk hvv hysT)
        · exact small_branch_lt64 (leafMem_lt_small hxsT hsv) (leafMem_lt_small hysT hvv)
      · exact ext_plus_lt64 (extOwnMem_lt_small hcppF)
          (small_branch_lt_memHead (leafMem_lt_small hxsT hsv) (leafMem_lt_small hysT hvv))

end NearSpec

namespace NearSpec

/-! ## The leaf step -/

theorem upsert_wf_leaf_step {k : List Nat} {s : Slot} {m : Nat} {key : List Nat} {v : Bytes}
    {t' : PTrie}
    (hw : (PTrie.leaf k s m).wf = true)
    (hk : nibblesOk key = true) (hv : v.length < 4294967296)
    (hp : (hexPrefix key true).length < 4294967296)
    (h : (PTrie.leaf k s m).upsert key v = some t') : t'.wf = true := by
  simp only [PTrie.upsert] at h
  by_cases e : k = key
  · simp only [e, ↓reduceIte, Option.some.injEq] at h; subst h
    exact newLeaf_wf' hk hv hp
  · simp only [e, ↓reduceIte, Option.some.injEq] at h; subst h
    obtain ⟨hn, hs, -, hpk⟩ := wf_leaf_parts' hw
    exact splitLeaf_wf k s key v hn hs hk (by simp [slotOk]; exact hv) hpk hp

end NearSpec

namespace NearSpec

/-! ## The lever: `kidsFrom` bounds and the split helpers' usage

Every node the split helpers build is a fresh leaf or a small branch over one or two fresh leaves,
so its usage is below `budget = 4·small`.  `memLe` is then propagated by a *monotone* bound, which
is exactly what the descend case needs (the new child's usage is below the old root's plus one
`budget`). -/

theorem splitLeaf_memD_budget (k : List Nat) (s : Slot) (key : List Nat) (v : Bytes)
    (hs : slotOk s = true) (hv : v.length < 4294967296)
    (hpk : (hexPrefix k true).length < 4294967296)
    (hpkey : (hexPrefix key true).length < 4294967296) :
    (splitLeaf k s key v).memD < budget := by
  have hsv : s.len < 4294967296 := slotOk_len hs
  have hcp : (hexPrefix (commonPrefix k key) false).length < 4294967296 := by
    rw [hexPrefix_length]; rw [hexPrefix_length] at hpk
    have := commonPrefix_len_le k key; omega
  have hown : extOwnMem (commonPrefix k key) < small := extOwnMem_lt_small hcp
  unfold splitLeaf
  dsimp only
  generalize hkr : k.drop (commonPrefix k key).length = kr
  generalize hyr : key.drop (commonPrefix k key).length = yr
  have hkrT : (hexPrefix kr true).length < 4294967296 := hkr ▸ hexPrefix_drop_lt hpk _ true
  have hyrT : (hexPrefix yr true).length < 4294967296 := hyr ▸ hexPrefix_drop_lt hpkey _ true
  have bndP : ∀ ys y, yr = y :: ys → (hexPrefix ys true).length < 4294967296 := by
    intro ys y hy
    have e1 : key.drop (commonPrefix k key).length = y :: ys := by rw [hyr]; exact hy
    have e3 : ys = key.drop ((commonPrefix k key).length + 1) := by
      have := congrArg (List.drop 1) e1
      simpa [List.drop_drop, Nat.add_comm] using this.symm
    rw [e3]; exact hexPrefix_drop_lt hpkey _ true
  have bndPk : ∀ xs x, kr = x :: xs → (hexPrefix xs true).length < 4294967296 := by
    intro xs x hx'
    have e1 : k.drop (commonPrefix k key).length = x :: xs := by rw [hkr]; exact hx'
    have e3 : xs = k.drop ((commonPrefix k key).length + 1) := by
      have := congrArg (List.drop 1) e1
      simpa [List.drop_drop, Nat.add_comm] using this.symm
    rw [e3]; exact hexPrefix_drop_lt hpk _ true
  have h50 : (50 : Nat) < small := by unfold small; omega
  have hsmall : small = 68719476736 := small_eq
  have hbud : budget = 343597383680 := rfl
  have h3s : 3 * small + 60 ≤ budget := by rw [hsmall, hbud]; omega
  cases kr with
  | nil =>
    cases yr with
    | nil =>
      show leafMem key v.length < budget
      have h := leafMem_lt_small hpkey hv
      have h2 : small = 68719476736 := small_eq
      have h3 : budget = 343597383680 := rfl
      omega
    | cons y ys =>
      show (wrapExt (commonPrefix k key) (.branch (some s) (kids1 y (newLeaf ys v))
        (50 + valueMem s.len + leafMem ys v.length))).memD < budget
      have h1 := leafMem_lt_small (bndP ys y rfl) hv
      have h2 := valueMem_lt_small hsv
      cases hcpe : commonPrefix k key with
      | nil =>
        show 50 + valueMem s.len + leafMem ys v.length < budget
        have h3 : small = 68719476736 := small_eq
        have h4 : budget = 343597383680 := rfl
        omega
      | cons a b =>
        show extOwnMem (a :: b) + (50 + valueMem s.len + leafMem ys v.length) < budget
        have h4 := extOwnMem_lt_small hcp
        have h5 : small = 68719476736 := small_eq
        have h6 : budget = 343597383680 := rfl
        have h7 : leafMem ys v.length < 68719476736 := by rw [← h5]; exact h1
        have h8 : valueMem s.len < 68719476736 := by rw [← h5]; exact h2
        have h9 : extOwnMem (a :: b) < 68719476736 := by
          rw [← hcpe, ← h5]; exact h4
        rw [h6]
        omega
  | cons x xs =>
    cases yr with
    | nil =>
      show (wrapExt (commonPrefix k key) (.branch (some (.val v)) (kids1 x (.leaf xs s (leafMem xs s.len)))
        (50 + valueMem v.length + leafMem xs s.len))).memD < budget
      have h1 := leafMem_lt_small (bndPk xs x rfl) hsv
      have h2 := valueMem_lt_small hv
      cases hcpe : commonPrefix k key with
      | nil =>
        show 50 + valueMem v.length + leafMem xs s.len < budget
        have h3 : small = 68719476736 := small_eq
        have h4 : budget = 343597383680 := rfl
        omega
      | cons a b =>
        show extOwnMem (a :: b) + (50 + valueMem v.length + leafMem xs s.len) < budget
        have h4 := extOwnMem_lt_small hcp
        have h5 : small = 68719476736 := small_eq
        have h6 : budget = 343597383680 := rfl
        have h7 : leafMem xs s.len < 68719476736 := by rw [← h5]; exact h1
        have h8 : valueMem v.length < 68719476736 := by rw [← h5]; exact h2
        have h9 : extOwnMem (a :: b) < 68719476736 := by
          rw [← hcpe, ← h5]; exact h4
        omega
    | cons y ys =>
      show (wrapExt (commonPrefix k key) (.branch none (kids2 x (.leaf xs s (leafMem xs s.len)) y (newLeaf ys v))
        (50 + leafMem xs s.len + leafMem ys v.length))).memD < budget
      have h1 := leafMem_lt_small (bndPk xs x rfl) hsv
      have h2 := leafMem_lt_small (bndP ys y rfl) hv
      cases hcpe : commonPrefix k key with
      | nil =>
        show 50 + leafMem xs s.len + leafMem ys v.length < budget
        have h3 : small = 68719476736 := small_eq
        have h4 : budget = 343597383680 := rfl
        omega
      | cons a b =>
        show extOwnMem (a :: b) + (50 + leafMem xs s.len + leafMem ys v.length) < budget
        have h4 := extOwnMem_lt_small hcp
        have h5 : small = 68719476736 := small_eq
        have h6 : budget = 343597383680 := rfl
        have h7 : leafMem xs s.len < 68719476736 := by rw [← h5]; exact h1
        have h8 : leafMem ys v.length < 68719476736 := by rw [← h5]; exact h2
        have h9 : extOwnMem (a :: b) < 68719476736 := by
          rw [← hcpe, ← h5]; exact h4
        rw [h6]
        omega


/-! ## The one-upsert delta

Every node on the touched path changes its usage by the *same* amount, the change in the
subtree's canonical usage — and that amount is below `budget`.  `memOk` is exactly what makes
this telescoping work: a leaf is `leafMem`, an extension is `extOwnMem + child`, a branch is
`branchOwn + Σ children`. -/

theorem memOk_leaf_memD {k : List Nat} {s : Slot} {m : Nat} (h : (PTrie.leaf k s m).memOk) :
    m = leafMem k s.len := h

/-- A descend's recomputation is exact: `m + c'.memD - cm` with `m = extOwnMem k + cm`. -/
theorem ext_descend_eq {k : List Nat} {c c' : PTrie} {m cm : Nat}
    (hmo : (PTrie.ext k c m).memOk) (hm : c.mem? = some cm) (hcm : m = extOwnMem k + cm) :
    m + c'.memD - cm = extOwnMem k + c'.memD := by
  rw [hcm]; omega



end NearSpec
