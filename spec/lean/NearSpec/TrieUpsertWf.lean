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
/-! ## Pre-resolved numeric bounds (all below `2^64`) -/

theorem valueMem_lt64 {n : Nat} (h : n < 4294967296) : valueMem n < 18446744073709551616 := by
  have := valueMem_lt_small h; have hs : small = 68719476736 := small_eq; omega

theorem leafMem_lt64 {k : List Nat} {n : Nat} (hk : (hexPrefix k true).length < 4294967296)
    (h : n < 4294967296) : leafMem k n < 18446744073709551616 := by
  have := leafMem_lt_small hk h; have hs : small = 68719476736 := small_eq; omega

theorem extOwnMem_lt64 {k : List Nat} (hk : (hexPrefix k false).length < 4294967296) :
    extOwnMem k < 18446744073709551616 := by
  have := extOwnMem_lt_small hk; have hs : small = 68719476736 := small_eq; omega

/-- A fresh branch over an old child at `m < memHead` with two fresh nodes `< small` fits. -/
theorem sub_branch_lt64 {m e c d : Nat} (hm : m < 18446742974197923840) (hc : c < 68719476736)
    (hd : d < 68719476736) : c + (m - e) + d < 18446744073709551616 := by
  have h := Nat.sub_le m e; omega

/-- A branch's own usage plus a fresh node fits (used for `branch_wf_of''`). -/
theorem branchOwn_plus_lt64 {c : Nat} (hc : c < 68719476736) {d : Nat} :
    50 + c + d < 18446744073709551616 ∨ 50 + c < 18446744073709551616 := Or.inr (by omega)

theorem valueMem_lt_of {n : Nat} (h : n < 4294967296) : valueMem n < 68719476736 := by
  have := valueMem_lt_small h; rwa [small_eq] at this

theorem leafMem_lt_of {k : List Nat} {n : Nat} (hk : (hexPrefix k true).length < 4294967296)
    (h : n < 4294967296) : leafMem k n < 68719476736 := by
  have := leafMem_lt_small hk h; rwa [small_eq] at this

theorem extOwnMem_lt_of {k : List Nat} (hk : (hexPrefix k false).length < 4294967296) :
    extOwnMem k < 68719476736 := by
  have := extOwnMem_lt_small hk; rwa [small_eq] at this

theorem memHead_lt_of {m : Nat} (h : m < memHead) : m < 18446742974197923840 := by
  rwa [memHead_eq] at h

/-! ## What is proved

Proved here (every `#print axioms` ⊆ `{propext, Classical.choice, Quot.sound}`):

* the encoding-length lemmas (`hexPrefix_length`, hence `hexPrefix_drop_lt`);
* the `wf` field projections (`wf_leaf_parts'` etc.) and `slotOk_len`;
* `memOk` / `memLe` for `kidsFrom`, `kids1`, `kids2`, `newLeaf`; `memLe` monotonicity;
* `extOwnMem`'s monotonicity in the prefix;
* `splitLeaf`'s `wf` (`splitLeaf_wf`) and usage bound (`splitLeaf_memD_budget`);
* the leaf upsert step (`upsert_wf_leaf_step`), which is the *whole* theorem when `t` is a leaf;
* `extOwnMem`'s monotonicity in the key length, and `splitExt_memD_le` (`splitExt`'s usage is
  `≤ m + budget`);
* `splitExt_wf` — the extension split preserves `wf`.  Its hypothesis is `m < memHead`, **not**
  `m < 2^64`: `splitExt` rebuilds the usage from the *stored* `m`, so the headroom is required (the
  `m < 2^64` form is false — `not_splitExt_wf_64`);
* `PTrie.upsert_memD_le` / `Kids.upsert_memD_le` — one upsert grows the usage by at most `budget`;
* **`PTrie.upsert_wf` / `Kids.upsert_wf` — the full induction:**

```
PTrie.upsert_wf :
  ∀ (t : PTrie) (key : List Nat) (v : Bytes) (t' : PTrie),
    t.wf = true → t.memOk → t.memLe memHead → nibblesOk key = true →
    v.length < 4294967296 → (hexPrefix key true).length < 4294967296 →
    t.upsert key v = some t' → t'.wf = true
```

For an `ext` node the descend is `m + c'.memD − cm = extOwnMem k + c'.memD` (`memOk` makes the
telescoping exact), below `2^64` because `cm < memHead` (`memLe` at the child) and
`c'.memD ≤ cm + budget` (`upsert_memD_le`).
-/



/-- `extOwnMem` is monotone in the key's length (its hex prefix is `|k|/2 + 1`). -/
theorem extOwnMem_le_of_length {k l : List Nat} (h : l.length ≤ k.length) :
    extOwnMem l ≤ extOwnMem k := by
  unfold extOwnMem; rw [hexPrefix_length, hexPrefix_length]; omega

/-- `p` followed by `x :: xs`: the two extensions' own usages are at most the combined one. -/
theorem extOwnMem_append_cons (p xs : List Nat) (x : Nat) :
    extOwnMem p + extOwnMem xs ≤ extOwnMem (p ++ x :: xs) + 52 := by
  unfold extOwnMem
  rw [hexPrefix_length, hexPrefix_length, hexPrefix_length, List.length_append]
  simp only [List.length_cons]
  omega

/-- `splitExt`'s usage is at most `m + budget`. -/
theorem splitExt_memD_le (k : List Nat) (c : PTrie) (m : Nat) (key : List Nat) (v : Bytes)
    (hv : v.length < 4294967296) (hpkey : (hexPrefix key false).length < 4294967296) (hpk : (hexPrefix k false).length < 4294967296) :
    (splitExt k c m key v).memD ≤ m + budget := by
  unfold splitExt
  dsimp only
  have hpk' : (hexPrefix k false).length < 4294967296 := by
    rw [hexPrefix_length]; rw [hexPrefix_length] at hpk; omega
  have hcp_le_key : (commonPrefix k key).length ≤ key.length := by
    have h := congrArg List.length (commonPrefix_right k key)
    rw [List.length_append] at h; omega
  have hp : (hexPrefix (commonPrefix k key) false).length < 4294967296 := by
    rw [hexPrefix_length]; rw [hexPrefix_length] at hpkey; omega
  have hkeyTf : (hexPrefix key false).length < 4294967296 := by
    rw [hexPrefix_length] at hpkey ⊢; omega
  have hown : extOwnMem (commonPrefix k key) < small := extOwnMem_lt_small hp
  have hkeyT : (hexPrefix key true).length < 4294967296 := by
    rw [hexPrefix_len_eq key true false]; exact hpkey
  generalize hkr : k.drop (commonPrefix k key).length = kr
  generalize hyr : key.drop (commonPrefix k key).length = yr
  -- key.length dropped-prefix relations
  have hylenk : (hexPrefix key false).length < 4294967296 := by
    rw [hexPrefix_length] at hpkey ⊢; omega
  have hylen : ∀ ys y, yr = y :: ys → leafMem ys v.length < small := by
    intro ys y hy
    apply leafMem_lt_small _ hv
    rw [hexPrefix_length]
    have e : key.drop (commonPrefix k key).length = y :: ys := by rw [hyr]; exact hy
    have h := congrArg List.length e
    rw [List.length_drop] at h
    simp only [List.length_cons] at h ⊢
    have h2 := congrArg List.length (commonPrefix_right k key)
    rw [List.length_append] at h2
    rw [hexPrefix_length] at hylenk
    omega
  have hbud : budget = 343597383680 := rfl
  have hsmall : small = 68719476736 := small_eq
  have hsmall' : small = 68719476736 := small_eq
  cases kr with
  | nil => show m ≤ m + budget; omega
  | cons x xs =>
    have hkk : k = commonPrefix k key ++ (x :: xs) := by
      have h := commonPrefix_left k key
      rw [hkr] at h
      exact h
    have hklp : (commonPrefix k key).length ≤ k.length := commonPrefix_len_le k key
    have hklen : k.length = (commonPrefix k key).length + ((x :: xs).length) := by
      have h := congrArg List.length hkr
      rw [List.length_drop] at h
      omega
    cases xs with
    | nil =>
      cases yr with
      | nil =>
        show (wrapExt (commonPrefix k key) (.branch (some (.val v)) (kids1 x c)
          (50 + valueMem v.length + (m - extOwnMem k)))).memD ≤ m + budget
        have hvv := valueMem_lt_small hv
        cases hcpe : commonPrefix k key with
        | nil =>
          show 50 + valueMem v.length + (m - extOwnMem k) ≤ m + budget
          unfold extOwnMem at *
          omega
        | cons a b =>
          show extOwnMem (a :: b) + (50 + valueMem v.length + (m - extOwnMem k)) ≤ m + budget
          have h4 : extOwnMem (a :: b) < small := by
            have e : commonPrefix k key = a :: b := by
              have := hcpe; exact this
            rw [← e]; exact hown
          have h5 : extOwnMem k < small := extOwnMem_lt_small hpk'
          have h6 : small = 68719476736 := small_eq
          have h7 : budget = 343597383680 := rfl
          unfold extOwnMem at *
          omega
      | cons y ys =>
        show (wrapExt (commonPrefix k key) (.branch none (kids2 x c y (newLeaf ys v))
          (50 + (m - extOwnMem k) + leafMem ys v.length))).memD ≤ m + budget
        have hyv := hylen ys y rfl
        cases hcpe : commonPrefix k key with
        | nil =>
          show 50 + (m - extOwnMem k) + leafMem ys v.length ≤ m + budget
          unfold extOwnMem at *
          omega
        | cons a b =>
          show extOwnMem (a :: b) + (50 + (m - extOwnMem k) + leafMem ys v.length) ≤ m + budget
          have h4 : extOwnMem (a :: b) < small := by rw [← hcpe]; exact hown
          have h5 : extOwnMem k < small := extOwnMem_lt_small hpk'
          have h6 : small = 68719476736 := small_eq
          have h7 : budget = 343597383680 := rfl
          unfold extOwnMem at *
          omega
    | cons a2 b2 =>
      have hxsk : extOwnMem (a2 :: b2) ≤ extOwnMem k := by
        apply extOwnMem_le_of_length
        have h := congrArg List.length hkk
        rw [List.length_append] at h
        simp only [List.length_cons] at h ⊢
        omega
      have hxsS : extOwnMem (a2 :: b2) < small := by
        apply extOwnMem_lt_small
        rw [hexPrefix_length]
        have h := congrArg List.length hkk
        rw [List.length_append] at h
        simp only [List.length_cons] at h ⊢
        rw [hexPrefix_length] at hpk'
        omega
      cases yr with
      | nil =>
        show (wrapExt (commonPrefix k key) (.branch (some (.val v)) (kids1 x
          (.ext (a2 :: b2) c (extOwnMem (a2 :: b2) + (m - extOwnMem k))))
          (50 + valueMem v.length + (extOwnMem (a2 :: b2) + (m - extOwnMem k))))).memD ≤ m + budget
        have hvv := valueMem_lt_small hv
        cases hcpe : commonPrefix k key with
        | nil =>
          show 50 + valueMem v.length + (extOwnMem (a2 :: b2) + (m - extOwnMem k)) ≤ m + budget
          have hxs6 : extOwnMem (a2 :: b2) < 68719476736 := by rw [← hsmall']; exact hxsS
          have hk6 : extOwnMem k < 68719476736 := by rw [← hsmall']; exact extOwnMem_lt_small hpk'
          have hv6 : valueMem v.length < 68719476736 := by rw [← hsmall']; exact hvv
          omega
        | cons a b =>
          show extOwnMem (a :: b) + (50 + valueMem v.length +
            (extOwnMem (a2 :: b2) + (m - extOwnMem k))) ≤ m + budget
          have h6 : extOwnMem (a :: b) < 68719476736 := by rw [← hsmall']; rw [← hcpe]; exact hown
          have hxs6 : extOwnMem (a2 :: b2) < 68719476736 := by rw [← hsmall']; exact hxsS
          have hk6 : extOwnMem k < 68719476736 := by rw [← hsmall']; exact extOwnMem_lt_small hpk'
          have hv6 : valueMem v.length < 68719476736 := by rw [← hsmall']; exact hvv
          omega
      | cons y ys =>
        show (wrapExt (commonPrefix k key) (.branch none (kids2 x
          (.ext (a2 :: b2) c (extOwnMem (a2 :: b2) + (m - extOwnMem k))) y (newLeaf ys v))
          (50 + (extOwnMem (a2 :: b2) + (m - extOwnMem k)) + leafMem ys v.length))).memD ≤ m + budget
        have hyv := hylen ys y rfl
        cases hcpe : commonPrefix k key with
        | nil =>
          show 50 + (extOwnMem (a2 :: b2) + (m - extOwnMem k)) + leafMem ys v.length ≤ m + budget
          have hxs6 : extOwnMem (a2 :: b2) < 68719476736 := by rw [← hsmall']; exact hxsS
          have hk6 : extOwnMem k < 68719476736 := by rw [← hsmall']; exact extOwnMem_lt_small hpk'
          have hy6 : leafMem ys v.length < 68719476736 := by rw [← hsmall']; exact hyv
          omega
        | cons a b =>
          show extOwnMem (a :: b) + (50 + (extOwnMem (a2 :: b2) + (m - extOwnMem k)) +
            leafMem ys v.length) ≤ m + budget
          have h6 : extOwnMem (a :: b) < 68719476736 := by rw [← hsmall']; rw [← hcpe]; exact hown
          have hxs6 : extOwnMem (a2 :: b2) < 68719476736 := by rw [← hsmall']; exact hxsS
          have hk6 : extOwnMem k < 68719476736 := by rw [← hsmall']; exact extOwnMem_lt_small hpk'
          have hy6 : leafMem ys v.length < 68719476736 := by rw [← hsmall']; exact hyv
          omega

/-! ## `splitExt` preserves `wf`

**The statement needs `m < memHead`, not `m < 2^64`.**  `splitExt` rebuilds the extension's usage
from the *stored* `m` (`extOwnMem xs + (m - extOwnMem k)`), and then wraps a fresh branch whose
usage is `50 + valueMem v + (m - extOwnMem k)` in an extension over the common prefix.  With only
`m < 2^64` that sum overflows: at `m = 2^64 - 1` the result's leaf-branch usage is
`2^64 + 99`, so `wf` is false (see `not_splitExt_wf_64`).  The headroom `m < memHead` is exactly
what the induction supplies (`memLe memHead` at an `ext` node), and it is enough. -/

/-- `50 + a + b < 2^64` for a fresh branch over an old child `b < memHead`. -/
theorem branch_subMem_lt64 {a b : Nat} (ha : a < small) (hb : b < memHead) :
    50 + a + b < 18446744073709551616 := by
  have h1 : memHead = 18446742974197923840 := memHead_eq
  have h2 : small = 68719476736 := small_eq
  omega

/-- `50 + a + b < 2^64` with the old child on the left. -/
theorem branch_subMem_lt64' {a b : Nat} (ha : a < memHead) (hb : b < small) :
    50 + a + b < 18446744073709551616 := by
  have h1 : memHead = 18446742974197923840 := memHead_eq
  have h2 : small = 68719476736 := small_eq
  omega

/-- `e + (50 + a + b) < 2^64` for a fresh extension `e` over a fresh branch. -/
theorem ext_branch_subMem_lt64 {e a b : Nat} (he : e < small) (ha : a < small)
    (hb : b < memHead) : e + (50 + a + b) < 18446744073709551616 := by
  have h1 : memHead = 18446742974197923840 := memHead_eq
  have h2 : small = 68719476736 := small_eq
  have h3 := memHead_room
  omega

/-- The other order: `e + (50 + a + b) < 2^64` with the old child on the left. -/
theorem ext_branch_subMem_lt64' {e a b : Nat} (he : e < small) (ha : a < memHead)
    (hb : b < small) : e + (50 + a + b) < 18446744073709551616 := by
  have h1 : memHead = 18446742974197923840 := memHead_eq
  have h2 : small = 68719476736 := small_eq
  have h3 := memHead_room
  omega

/-- `a + (m - b) ≤ max m a` when `a ≤ b`: either the subtraction is exact, or it is `0`. -/
theorem add_sub_le_max {a b m : Nat} (hab : a ≤ b) : a + (m - b) ≤ max m a := by
  by_cases h : b ≤ m
  · have : a + (m - b) = a + m - b := by omega
    rw [this]; omega
  · have : m - b = 0 := by omega
    rw [this, Nat.add_zero]; exact Nat.le_max_right _ _

/-- `splitExt` preserves `wf`, under the headroom `m < memHead` the induction supplies. -/
theorem splitExt_wf (k : List Nat) (c : PTrie) (m : Nat) (key : List Nat) (v : Bytes)
    (hk : nibblesOk k = true) (hkey : nibblesOk key = true) (hc : c.wf = true)
    (hm : m < memHead)
    (hv : v.length < 4294967296)
    (hpkey : (hexPrefix key true).length < 4294967296)
    (hpk : (hexPrefix k false).length < 4294967296) :
    (splitExt k c m key v).wf = true := by
  have hm64 : m < 18446744073709551616 := by
    have h1 : memHead = 18446742974197923840 := memHead_eq
    omega
  have hcppOk : nibblesOk (commonPrefix k key) = true := nibblesOk_commonPrefix hk
  have hcppF : (hexPrefix (commonPrefix k key) false).length < 4294967296 := by
    rw [hexPrefix_length]; rw [hexPrefix_length] at hpk
    have := commonPrefix_len_le k key; omega
  have hcppSmall : extOwnMem (commonPrefix k key) < small := extOwnMem_lt_small hcppF
  unfold splitExt
  dsimp only
  generalize hkr : k.drop (commonPrefix k key).length = kr
  generalize hyr : key.drop (commonPrefix k key).length = yr
  have hyrOk : nibblesOk yr = true := hyr ▸ nibblesOk_drop' key _ hkey
  have bndYs : ∀ ys y, yr = y :: ys → (hexPrefix ys true).length < 4294967296 := by
    intro ys y hy
    have e1 : key.drop (commonPrefix k key).length = y :: ys := by rw [hyr]; exact hy
    have e3 : ys = key.drop ((commonPrefix k key).length + 1) := by
      have := congrArg (List.drop 1) e1
      simpa [List.drop_drop, Nat.add_comm] using this.symm
    rw [e3]; exact hexPrefix_drop_lt hpkey _ true
  have bndOkYs : ∀ ys y, yr = y :: ys → nibblesOk ys = true := by
    intro ys y hy
    have e1 : key.drop (commonPrefix k key).length = y :: ys := by rw [hyr]; exact hy
    have e3 : ys = key.drop ((commonPrefix k key).length + 1) := by
      have := congrArg (List.drop 1) e1
      simpa [List.drop_drop, Nat.add_comm] using this.symm
    rw [e3]; exact nibblesOk_drop' key _ hkey
  cases kr with
  | nil => exact ext_wf_of' hk hc hm64 hpk
  | cons x xs =>
    have hx : x < 16 := nibblesOk_head (hkr ▸ nibblesOk_drop' k _ hk) rfl
    have hxsOk : nibblesOk xs = true := by
      have e1 : k.drop (commonPrefix k key).length = x :: xs := hkr
      have e3 : xs = k.drop ((commonPrefix k key).length + 1) := by
        have := congrArg (List.drop 1) e1
        simpa [List.drop_drop, Nat.add_comm] using this.symm
      rw [e3]; exact nibblesOk_drop' k _ hk
    have hxsF : (hexPrefix xs false).length < 4294967296 := by
      have e1 : k.drop (commonPrefix k key).length = x :: xs := hkr
      have e3 : xs = k.drop ((commonPrefix k key).length + 1) := by
        have := congrArg (List.drop 1) e1
        simpa [List.drop_drop, Nat.add_comm] using this.symm
      rw [e3]; exact hexPrefix_drop_lt' hpk _ false
    have hxs_le : extOwnMem xs ≤ extOwnMem k := by
      apply extOwnMem_le_of_length
      have h := congrArg List.length hkr
      rw [List.length_drop] at h
      simp only [List.length_cons] at h
      omega
    have hxsSmall : extOwnMem xs < small := extOwnMem_lt_small hxsF
    cases xs with
    | nil =>
      have hsubHead : m - extOwnMem k < memHead := Nat.lt_of_le_of_lt (Nat.sub_le _ _) hm
      cases yr with
      | nil =>
        show (wrapExt (commonPrefix k key) (.branch (some (.val v)) (kids1 x c)
          (50 + valueMem v.length + (m - extOwnMem k)))).wf = true
        have hbm : 50 + valueMem v.length + (m - extOwnMem k) < 18446744073709551616 :=
          branch_subMem_lt64 (valueMem_lt_small hv) hsubHead
        refine wrapExt_wf' hcppOk hcppF ?_ ?_
        · apply branch_wf_of''
          · intro s' hs'; cases hs'; simp [slotOk]; exact hv
          · exact wf_kids1 hx hc
          · exact hbm
        · exact ext_branch_subMem_lt64 hcppSmall (valueMem_lt_small hv) hsubHead
      | cons y ys =>
        have hy : y < 16 := nibblesOk_head hyrOk rfl
        have hysT := bndYs ys y rfl
        have hysOk := bndOkYs ys y rfl
        show (wrapExt (commonPrefix k key) (.branch none (kids2 x c y (newLeaf ys v))
          (50 + (m - extOwnMem k) + leafMem ys v.length))).wf = true
        have hbm : 50 + (m - extOwnMem k) + leafMem ys v.length < 18446744073709551616 :=
          branch_subMem_lt64' hsubHead (leafMem_lt_small hysT hv)
        refine wrapExt_wf' hcppOk hcppF ?_ ?_
        · apply branch_wf_of''
          · intro s' hs'; simp at hs'
          · exact wf_kids2 hx hy hc (newLeaf_wf' hysOk hv hysT)
          · exact hbm
        · exact ext_branch_subMem_lt64' hcppSmall hsubHead (leafMem_lt_small hysT hv)
    | cons a2 b2 =>
      have hsubHead : extOwnMem (a2 :: b2) + (m - extOwnMem k) < memHead := by
        have := add_sub_le_max (m := m) hxs_le
        have hsmallHead : small < memHead := small_lt_memHead'
        omega
      have hsubwf : (PTrie.ext (a2 :: b2) c (extOwnMem (a2 :: b2) + (m - extOwnMem k))).wf =
          true :=
        ext_wf_of' hxsOk hc (extOwnMem_plus_lt64 hxsSmall (by
          have h1 : memHead = 18446742974197923840 := memHead_eq
          have h2 : small = 68719476736 := small_eq
          omega)) hxsF
      cases yr with
      | nil =>
        show (wrapExt (commonPrefix k key) (.branch (some (.val v)) (kids1 x
          (.ext (a2 :: b2) c (extOwnMem (a2 :: b2) + (m - extOwnMem k))))
          (50 + valueMem v.length + (extOwnMem (a2 :: b2) + (m - extOwnMem k))))).wf = true
        have hbm :
            50 + valueMem v.length + (extOwnMem (a2 :: b2) + (m - extOwnMem k)) <
              18446744073709551616 :=
          branch_subMem_lt64 (valueMem_lt_small hv) hsubHead
        refine wrapExt_wf' hcppOk hcppF ?_ ?_
        · apply branch_wf_of''
          · intro s' hs'; cases hs'; simp [slotOk]; exact hv
          · exact wf_kids1 hx hsubwf
          · exact hbm
        · exact ext_branch_subMem_lt64 hcppSmall (valueMem_lt_small hv) hsubHead
      | cons y ys =>
        have hy : y < 16 := nibblesOk_head hyrOk rfl
        have hysT := bndYs ys y rfl
        have hysOk := bndOkYs ys y rfl
        show (wrapExt (commonPrefix k key) (.branch none (kids2 x
          (.ext (a2 :: b2) c (extOwnMem (a2 :: b2) + (m - extOwnMem k))) y (newLeaf ys v))
          (50 + (extOwnMem (a2 :: b2) + (m - extOwnMem k)) + leafMem ys v.length))).wf = true
        have hbm :
            50 + (extOwnMem (a2 :: b2) + (m - extOwnMem k)) + leafMem ys v.length <
              18446744073709551616 :=
          branch_subMem_lt64' hsubHead (leafMem_lt_small hysT hv)
        refine wrapExt_wf' hcppOk hcppF ?_ ?_
        · apply branch_wf_of''
          · intro s' hs'; simp at hs'
          · exact wf_kids2 hx hy hsubwf (newLeaf_wf' hysOk hv hysT)
          · exact hbm
        · exact ext_branch_subMem_lt64' hcppSmall hsubHead (leafMem_lt_small hysT hv)

/-- **The `m < 2^64` form of `splitExt_wf` is false.**  An extension at `m = 2^64 - 1` over a
small leaf, split by a sibling key, builds a branch whose usage is `≥ 2^64`. -/
theorem not_splitExt_wf_64 :
    (splitExt [1] (PTrie.leaf [] (.val []) 50) 18446744073709551615 [2] ([] : Bytes)).wf = false := by
  decide +kernel

end NearSpec

namespace NearSpec

/-! ## The usage gap: one upsert grows a node's usage by at most `budget`

This is the second half of the induction.  It is stated at `memD` rather than `wf`, and `wf` is
needed as a hypothesis: the *shape* of a split (`splitLeaf`/`splitExt`) depends on the stored slots
and key encodings, so a leaf's `slotOk` and an extension's key bound must come from `wf`. -/

theorem memD_of_mem? {t : PTrie} {cm : Nat} (h : t.mem? = some cm) : t.memD = cm := by
  simp [PTrie.memD, h]

theorem memD_branch_mem (bv : Option Slot) (cs : Kids) (m : Nat) :
    (PTrie.branch bv cs m).memD = m := rfl

theorem memD_leaf_mem (k : List Nat) (s : Slot) (m : Nat) :
    (PTrie.leaf k s m).memD = m := rfl

theorem memD_ext_mem (k : List Nat) (c : PTrie) (m : Nat) :
    (PTrie.ext k c m).memD = m := rfl

theorem memD_newLeaf (k : List Nat) (v : Bytes) : (newLeaf k v).memD = leafMem k v.length := rfl

theorem valueMem_le_budget {n : Nat} (h : n < 4294967296) : valueMem n ≤ budget := by
  have h1 := valueMem_lt_small h
  have h2 : small = 68719476736 := small_eq
  have h3 : budget = 343597383680 := rfl
  omega

theorem leafMem_le_budget {k : List Nat} {n : Nat} (hk : (hexPrefix k true).length < 4294967296)
    (h : n < 4294967296) : leafMem k n ≤ budget := by
  have h1 := leafMem_lt_small hk h
  have h2 : small = 68719476736 := small_eq
  have h3 : budget = 343597383680 := rfl
  omega

mutual
/-- One upsert grows a trie's stored usage by at most `budget`. -/
theorem PTrie.upsert_memD_le : ∀ (t : PTrie) (key : List Nat) (v : Bytes) (t' : PTrie),
    t.wf = true → (hexPrefix key true).length < 4294967296 → v.length < 4294967296 →
    t.upsert key v = some t' → t'.memD ≤ t.memD + budget
  | .hash _, _, _, _, _, _, _, h => by simp [PTrie.upsert] at h
  | .leaf k s m, key, v, t', hwf, hpkey, hv, h => by
    simp only [PTrie.upsert] at h
    obtain ⟨-, hs, -, hpk⟩ := wf_leaf_parts' hwf
    by_cases e : k = key
    · simp only [e, ↓reduceIte, Option.some.injEq] at h; subst h
      show (newLeaf key v).memD ≤ (PTrie.leaf key s m).memD + budget
      rw [memD_newLeaf, memD_leaf_mem]
      have := leafMem_le_budget hpkey hv
      omega
    · simp only [e, ↓reduceIte, Option.some.injEq] at h; subst h
      show (splitLeaf k s key v).memD ≤ (PTrie.leaf k s m).memD + budget
      rw [memD_leaf_mem]
      have h1 := splitLeaf_memD_budget k s key v hs hv hpk hpkey
      omega
  | .ext k c m, key, v, t', hwf, hpkey, hv, h => by
    simp only [PTrie.upsert] at h
    obtain ⟨-, hcwf, -, hpk⟩ := wf_ext_parts' hwf
    by_cases hp : isPrefix k key = true
    · simp only [hp, ↓reduceIte] at h
      cases hm : c.mem? <;> cases hu : c.upsert (key.drop k.length) v <;> simp [hm, hu] at h
      subst h
      show (PTrie.ext k _ (m + _ - _)).memD ≤ (PTrie.ext k c m).memD + budget
      rw [memD_ext_mem, memD_ext_mem]
      have hkp : (hexPrefix (key.drop k.length) true).length < 4294967296 :=
        hexPrefix_drop_lt hpkey _ true
      have ih := PTrie.upsert_memD_le c (key.drop k.length) v _ hcwf hkp hv ‹_›
      have hcm := memD_of_mem? hm
      omega
    · have hp' : isPrefix k key = false := by simpa using hp
      simp only [hp', Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h; subst h
      show (splitExt k c m key v).memD ≤ (PTrie.ext k c m).memD + budget
      rw [memD_ext_mem]
      exact splitExt_memD_le k c m key v hv (hexPrefix_false_of_true hpkey) hpk
  | .branch bv cs m, [], v, t', hwf, _, hv, h => by
    simp only [PTrie.upsert] at h
    simp only [Option.some.injEq] at h; subst h
    show (PTrie.branch _ cs _).memD ≤ (PTrie.branch bv cs m).memD + budget
    rw [memD_branch_mem, memD_branch_mem]
    have := valueMem_le_budget hv
    omega
  | .branch bv cs m, n :: rest, v, t', hwf, hpkey, hv, h => by
    simp only [PTrie.upsert] at h
    obtain ⟨-, hwfk, -⟩ := wf_branch_parts' hwf
    cases hu : Kids.upsert cs n rest v with
    | none => simp [hu] at h
    | some r =>
      simp only [hu, Option.map_some, Option.some.injEq] at h
      subst h
      show (PTrie.branch _ _ (m + r.2.2 - r.2.1)).memD ≤ (PTrie.branch bv cs m).memD + budget
      rw [memD_branch_mem, memD_branch_mem]
      have hrestP : (hexPrefix rest true).length < 4294967296 := by
        have := hexPrefix_drop_lt hpkey 1 true
        simpa using this
      have ih := Kids.upsert_memD_le 16 cs n rest v r.1 r.2.1 r.2.2 hwfk hrestP hv hu
      omega

/-- One upsert into a child slot grows that child's stored usage by at most `budget`; the pair
returned by `Kids.upsert` is `(old usage, new usage)`.  `N` is the slot count of `cs`. -/
theorem Kids.upsert_memD_le : ∀ (N : Nat) (cs : Kids) (n : Nat) (key : List Nat) (v : Bytes)
    (cs' : Kids) (a b : Nat),
    Kids.wf cs N = true → (hexPrefix key true).length < 4294967296 →
    v.length < 4294967296 → Kids.upsert cs n key v = some (cs', a, b) → b ≤ a + budget
  | _, .nil, _, _, _, _, _, _, _, _, _, h => by simp [Kids.upsert] at h
  | _, .none r, 0, key, v, cs', a, b, hw, hpkey, hv, h => by
    simp only [Kids.upsert] at h
    have hp : (Kids.some (newLeaf key v) r, 0, leafMem key v.length) = (cs', a, b) :=
      Option.some.inj h
    have ha : a = 0 := (congrArg (fun p : Kids × Nat × Nat => p.2.1) hp).symm
    have hb : b = leafMem key v.length := (congrArg (fun p : Kids × Nat × Nat => p.2.2) hp).symm
    rw [hb, ha]
    show leafMem key v.length ≤ 0 + budget
    have := leafMem_le_budget hpkey hv
    omega
  | N, .some c r, 0, key, v, cs', a, b, hw, hpkey, hv, h => by
    simp only [Kids.wf, Bool.and_eq_true, Nat.zero_add] at hw
    simp only [Kids.upsert] at h
    cases hm : c.mem? with
    | none => simp [hm] at h
    | some cm =>
      cases hu : c.upsert key v with
      | none => simp [hm, hu] at h
      | some c' =>
        simp only [hm, hu] at h
        have hp : (Kids.some c' r, cm, c'.memD) = (cs', a, b) := Option.some.inj h
        have ha : a = cm := (congrArg (fun p : Kids × Nat × Nat => p.2.1) hp).symm
        have hb : b = c'.memD := (congrArg (fun p : Kids × Nat × Nat => p.2.2) hp).symm
        rw [hb, ha]
        have ih := PTrie.upsert_memD_le c key v c' hw.1.2 hpkey hv hu
        have hcm := memD_of_mem? hm
        omega
  | N, .none r, i + 1, key, v, cs', a, b, hw, hpkey, hv, h => by
    simp only [Kids.wf, Bool.and_eq_true] at hw
    simp only [Kids.upsert] at h
    cases hu : Kids.upsert r i key v with
    | none => simp [hu] at h
    | some x =>
      simp only [hu, Option.map_some] at h
      have hp : (Kids.none x.1, x.2.1, x.2.2) = (cs', a, b) := Option.some.inj h
      have ha : a = x.2.1 := (congrArg (fun p : Kids × Nat × Nat => p.2.1) hp).symm
      have hb : b = x.2.2 := (congrArg (fun p : Kids × Nat × Nat => p.2.2) hp).symm
      rw [hb, ha]
      exact Kids.upsert_memD_le (N - 1) r i key v x.1 x.2.1 x.2.2 hw.2 hpkey hv hu
  | N, .some c r, i + 1, key, v, cs', a, b, hw, hpkey, hv, h => by
    simp only [Kids.wf, Bool.and_eq_true] at hw
    simp only [Kids.upsert] at h
    cases hu : Kids.upsert r i key v with
    | none => simp [hu] at h
    | some x =>
      simp only [hu, Option.map_some] at h
      have hp : (Kids.some c x.1, x.2.1, x.2.2) = (cs', a, b) := Option.some.inj h
      have ha : a = x.2.1 := (congrArg (fun p : Kids × Nat × Nat => p.2.1) hp).symm
      have hb : b = x.2.2 := (congrArg (fun p : Kids × Nat × Nat => p.2.2) hp).symm
      rw [hb, ha]
      exact Kids.upsert_memD_le (N - 1) r i key v x.1 x.2.1 x.2.2 hw.2 hpkey hv hu
end

/-! ## The full induction: `upsert` preserves `wf` -/

theorem memD_lt_of_memLe {t : PTrie} {cm c : Nat} (h : t.mem? = some cm) (hl : t.memLe c) :
    cm < c := by
  cases t with
  | hash _ => simp [PTrie.mem?] at h
  | leaf k s m => simp only [PTrie.mem?, Option.some.injEq] at h; rw [← h]; exact hl
  | ext k ch m => simp only [PTrie.mem?, Option.some.injEq] at h; simpa [← h] using hl.1
  | branch b cs m => simp only [PTrie.mem?, Option.some.injEq] at h; simpa [← h] using hl.1

theorem ext_descend_lt64 {e cm m' : Nat} (he : e < small) (hcm : cm < memHead)
    (hm' : m' ≤ cm + budget) : e + m' < 18446744073709551616 := by
  have h1 : memHead = 18446742974197923840 := memHead_eq
  have h2 : small = 68719476736 := small_eq
  have h3 : budget = 343597383680 := rfl
  have h4 := memHead_budget
  omega

mutual
theorem PTrie.upsert_wf : ∀ (t : PTrie) (key : List Nat) (v : Bytes) (t' : PTrie),
    t.wf = true → t.memOk → t.memLe memHead → nibblesOk key = true →
    v.length < 4294967296 → (hexPrefix key true).length < 4294967296 →
    t.upsert key v = some t' → t'.wf = true
  | .hash _, _, _, _, _, _, _, _, _, _, h => by simp [PTrie.upsert] at h
  | .leaf k s m, key, v, t', hw, _, _, hk, hv, hp, h =>
    upsert_wf_leaf_step hw hk hv hp h
  | .ext k c m, key, v, t', hw, hmo, hml, hk, hv, hp, h => by
    obtain ⟨hkn, hcwf, -, hpk⟩ := wf_ext_parts' hw
    simp only [PTrie.upsert] at h
    by_cases hpre : isPrefix k key = true
    · simp only [hpre, ↓reduceIte] at h
      cases hm : c.mem? with
      | none => simp [hm] at h
      | some cm =>
        cases hu : c.upsert (key.drop k.length) v with
        | none => simp [hm, hu] at h
        | some c' =>
          simp only [hm, hu, Option.some.injEq] at h
          subst h
          have hcmD : cm = c.memD := (memD_of_mem? hm).symm
          have hcmlt : cm < memHead := memD_lt_of_memLe hm hml.2
          have hmEq : m = extOwnMem k + cm := by
            rcases hmo.1 with hnone | heq
            · rw [hm] at hnone; cases hnone
            · rw [heq, hcmD]
          have hdrop : nibblesOk (key.drop k.length) = true := nibblesOk_drop' key _ hk
          have hdropT : (hexPrefix (key.drop k.length) true).length < 4294967296 :=
            hexPrefix_drop_lt hp _ true
          have hc'wf : c'.wf = true :=
            PTrie.upsert_wf c (key.drop k.length) v c' hcwf hmo.2 hml.2 hdrop hv hdropT hu
          have hm' := PTrie.upsert_memD_le c (key.drop k.length) v c' hcwf hdropT hv hu
          refine ext_wf_of' hkn hc'wf ?_ hpk
          show m + c'.memD - cm < 18446744073709551616
          have hown := extOwnMem_lt_small hpk
          have heq2 : m + c'.memD - cm = extOwnMem k + c'.memD := by rw [hmEq]; omega
          rw [heq2]
          exact ext_descend_lt64 hown hcmlt (by rw [hcmD]; exact hm')
    · have hpre' : isPrefix k key = false := by simpa using hpre
      simp only [hpre', Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h
      subst h
      exact splitExt_wf k c m key v hkn hk hcwf hml.1 hv hp hpk
  | .branch bv cs m, [], v, t', hw, _, hml, hk, hv, hp, h => by
    simp only [PTrie.upsert, Option.some.injEq] at h
    subst h
    obtain ⟨hbv, hcs, hmw⟩ := wf_branch_parts' hw
    refine branch_wf_of'' ?_ hcs ?_
    · intro s' hs'
      injection hs' with h'
      subst h'
      simp [slotOk]
      exact hv
    · show m + valueMem v.length - _ < 18446744073709551616
      have hv' := valueMem_lt_small hv
      have hmw' : m < 18446742974197923840 := hml.1
      have h2 : small = 68719476736 := small_eq
      omega
  | .branch bv cs m, n :: rest, v, t', hw, hmo, hml, hk, hv, hp, h => by
    simp only [PTrie.upsert] at h
    obtain ⟨hbv, hcswf, hmw⟩ := wf_branch_parts' hw
    cases hu : Kids.upsert cs n rest v with
    | none => simp [hu] at h
    | some r =>
      simp only [hu, Option.map_some, Option.some.injEq] at h
      subst h
      refine branch_wf_of'' ?_ ?_ ?_
      · intro s' hs'; exact hbv s' hs'
      · exact Kids.upsert_wf 16 cs n rest v r.1 r.2.1 r.2.2 hcswf hmo.2 hml.2
          (nibblesOk_cons.1 hk).2 hv (by simpa using hexPrefix_drop_lt hp 1 true) hu
      · show m + r.2.2 - r.2.1 < 18446744073709551616
        have hle := Kids.upsert_memD_le 16 cs n rest v r.1 r.2.1 r.2.2 hcswf
          (by simpa using hexPrefix_drop_lt hp 1 true) hv hu
        have h1 := memHead_budget
        have h2 := hml.1
        omega

theorem Kids.upsert_wf : ∀ (N : Nat) (cs : Kids) (n : Nat) (key : List Nat) (v : Bytes)
    (cs' : Kids) (a b : Nat),
    Kids.wf cs N = true → Kids.memOk cs → Kids.memLe cs memHead → nibblesOk key = true →
    v.length < 4294967296 → (hexPrefix key true).length < 4294967296 →
    Kids.upsert cs n key v = some (cs', a, b) → Kids.wf cs' N = true
  | _, .nil, _, _, _, _, _, _, _, _, _, _, _, _, h => by simp [Kids.upsert] at h
  | N, .none r, 0, key, v, cs', a, b, hw, hmo, hml, hk, hv, hp, h => by
    simp only [Kids.wf, Bool.and_eq_true] at hw
    simp only [Kids.upsert] at h
    have hp' : (Kids.some (newLeaf key v) r, 0, leafMem key v.length) = (cs', a, b) :=
      Option.some.inj h
    obtain ⟨rfl, -⟩ := Prod.mk.inj hp'
    show Kids.wf (Kids.some (newLeaf key v) r) N = true
    simp only [Kids.wf, hw.1, newLeaf_wf' hk hv hp, hw.2, Bool.and_true]
  | N, .some c r, 0, key, v, cs', a, b, hw, hmo, hml, hk, hv, hp, h => by
    simp only [Kids.wf, Bool.and_eq_true, Nat.zero_add] at hw
    simp only [Kids.upsert] at h
    cases hm : c.mem? with
    | none => simp [hm] at h
    | some cm =>
      cases hu : c.upsert key v with
      | none => simp [hm, hu] at h
      | some c' =>
        simp only [hm, hu] at h
        have hp' : (Kids.some c' r, cm, c'.memD) = (cs', a, b) := Option.some.inj h
        obtain ⟨rfl, -⟩ := Prod.mk.inj hp'
        show Kids.wf (Kids.some c' r) N = true
        have hc'wf := PTrie.upsert_wf c key v c' hw.1.2 hmo.1 hml.1 hk hv hp hu
        simp only [Kids.wf, hw.1.1, hc'wf, hw.2, Bool.and_true]
  | N, .none r, i + 1, key, v, cs', a, b, hw, hmo, hml, hk, hv, hp, h => by
    simp only [Kids.wf, Bool.and_eq_true] at hw
    simp only [Kids.upsert] at h
    cases hu : Kids.upsert r i key v with
    | none => simp [hu] at h
    | some x =>
      simp only [hu, Option.map_some] at h
      have hp' : (Kids.none x.1, x.2.1, x.2.2) = (cs', a, b) := Option.some.inj h
      obtain ⟨rfl, -⟩ := Prod.mk.inj hp'
      show Kids.wf (Kids.none x.1) N = true
      have := Kids.upsert_wf (N - 1) r i key v x.1 x.2.1 x.2.2 hw.2 hmo hml hk hv hp hu
      simp only [Kids.wf, hw.1, this, Bool.and_true]
  | N, .some c r, i + 1, key, v, cs', a, b, hw, hmo, hml, hk, hv, hp, h => by
    simp only [Kids.wf, Bool.and_eq_true] at hw
    simp only [Kids.upsert] at h
    cases hu : Kids.upsert r i key v with
    | none => simp [hu] at h
    | some x =>
      simp only [hu, Option.map_some] at h
      have hp' : (Kids.some c x.1, x.2.1, x.2.2) = (cs', a, b) := Option.some.inj h
      obtain ⟨rfl, -⟩ := Prod.mk.inj hp'
      show Kids.wf (Kids.some c x.1) N = true
      have := Kids.upsert_wf (N - 1) r i key v x.1 x.2.1 x.2.2 hw.2 hmo.2 hml.2 hk hv hp hu
      simp only [Kids.wf, hw.1, hw.1.2, this, Bool.and_true]
end

end NearSpec
