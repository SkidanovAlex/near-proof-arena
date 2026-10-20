import ZkFormal.NearV3.D3.StateWrite
import NearSpec.TrieUpsertWf

/-!
# `ZkFormal.NearV3.D3.UpsertWf` — `UpsertPreservesWf` is false, and what to prove instead

`StateWrite.lean` states

```
def UpsertPreservesWf : Prop :=
  ∀ (t u : PTrie) (account key v : NearSpec.Bytes),
    t.wf = true → cdUpsert t account key v = some u → u.wf = true
```

This module **disproves** it (two independent machine-checked counterexamples) and records the
corrected statement, `UpsertPreservesWfWithBounds`, now a **theorem** (see
`upsertPreservesWfWithBounds` below, discharged by `NearSpec.PTrie.upsert_wf`).

## Two independent failures

`nearcore`'s `GenericTrieUpdateInsertDelete::insert` (which `PTrie.upsert` renders) can write a
node or a value that the *pre-state's* `wf` says nothing about:

1. **The value's length.**  `wf` bounds a node's stored fields; the value being written is an
   *argument*, not a field of `t`.  Upserting `2^32` bytes makes a fresh leaf whose
   `slotOk (.val v)` (which requires `v.length < 2^32`) is false.  See
   `not_upsertPreservesWf_valueLen`.
2. **The recomputed `memory_usage`.**  `upsert` recomputes each node's stored usage on the touched
   path as `m + c'.memD - cm`, from the *stored* usages.  `wf` only bounds them by `2^64`, so a
   well-formed `ext` sitting at `2^64 - 1` directly above a leaf overflows to `≥ 2^64`.  See
   `not_upsertPreservesWf_mem`.

Neither failure is about the *write* being wrong: the post-state is the right key→value map
(`find_upsert_self`/`_other` hold).  They are about `wf` being a *local* predicate that does not
carry the two global facts the recomputation needs.

## The corrected statement

`NearSpec.PTrie.upsert_wf` (in `NearSpec.TrieUpsertWf`) proves, for a single upsert,

```
t.wf = true → t.memOk → t.memD < memHead → nibblesOk key = true →
v.length < 2^32 → (hexPrefix key true).length < 2^32 →
t.upsert key v = some t' → t'.wf = true ∧ t'.memOk ∧ t'.memD < memHead + small
```

where `memOk` is the **canonical-usage invariant** (`wf` is missing it): every revealed node's
stored `memory_usage` is exactly the one nearcore computes from its own fields and its revealed
children's, and `t.memD < memHead` is the **headroom** that lets one upsert's growth
(`≤ small`) stay below `2^64`.  `UpsertPreservesWfWithBounds` below is the same statement at the
`cdUpsert` entry point, spelled for `StateWrite`'s `applyLog`.
-/

namespace ZkFormal.NearV3.D3

open NearSpec

/-! ## Counterexample 1: the value's length -/

/-- The write path of the empty ContractData key (`account = [], key = []`). -/
theorem cdWriteKey_nil_path : NearSpec.nibbles (cdWriteKey [] []) = [0, 9, 2, 12] := by
  simp [cdWriteKey, contractDataPrefix, colContractData, accountDataSeparator]
  decide +kernel

/-- `t = leaf [0,9,2,12] (.val []) 50` is well formed. -/
theorem ce_leaf_wf : (PTrie.leaf [0, 9, 2, 12] (.val []) 50).wf = true := by decide +kernel

/-- Upserting `2^32` zero bytes at the write path rebuilds the leaf with that value. -/
theorem ce_upsert_long :
    ∀ (v : NearSpec.Bytes), v.length = 4294967296 →
      cdUpsert (PTrie.leaf [0, 9, 2, 12] (.val []) 50) [] [] v =
        some (PTrie.leaf [0, 9, 2, 12] (.val v)
          (50 + 2 * ((hexPrefix [0, 9, 2, 12] true).length) + (v.length + 50))) := by
  intro v hv
  unfold cdUpsert
  rw [cdWriteKey_nil_path]
  simp [PTrie.upsert, newLeaf, leafMem]

/-- The rebuilt leaf's `slotOk` fails: `v` is too long. -/
theorem ce_long_not_wf {v : NearSpec.Bytes} (hv : v.length = 4294967296) :
    (PTrie.leaf [0, 9, 2, 12] (.val v)
      (50 + 2 * ((hexPrefix [0, 9, 2, 12] true).length) + (v.length + 50))).wf = false := by
  simp [PTrie.wf, slotOk, hv]

/-- **`UpsertPreservesWf` fails on the value's length.** -/
theorem not_upsertPreservesWf_valueLen : ¬ UpsertPreservesWf := by
  intro h
  have hv : (List.replicate 4294967296 (0 : UInt8)).length = 4294967296 :=
    List.length_replicate ..
  have := h _ _ [] [] _ ce_leaf_wf (ce_upsert_long _ hv)
  rw [ce_long_not_wf hv] at this
  exact Bool.false_ne_true this

/-! ## Counterexample 2: the recomputed `memory_usage` -/

/-- A well-formed extension with usage `2^64 - 1` directly above a leaf. -/
theorem ce_ext_wf :
    (PTrie.ext [] (PTrie.leaf [0, 9, 2, 12] (.val []) 1) 18446744073709551615).wf = true := by
  decide +kernel

/-- Writing the empty value there overwrites the leaf and recomputes the extension's usage. -/
theorem ce_upsert_overflow :
    cdUpsert (PTrie.ext [] (PTrie.leaf [0, 9, 2, 12] (.val []) 1) 18446744073709551615) [] [] [] =
      some (PTrie.ext [] (PTrie.leaf [0, 9, 2, 12] (.val []) 106)
        (18446744073709551615 + 106 - 1)) := by
  have hleaf : (PTrie.leaf [0, 9, 2, 12] (.val []) 1).upsert [0, 9, 2, 12] [] =
      some (PTrie.leaf [0, 9, 2, 12] (.val []) 106) := by
    simp [PTrie.upsert, newLeaf, leafMem, hexPrefix, packNibbles]
  unfold cdUpsert
  rw [cdWriteKey_nil_path]
  simp only [PTrie.upsert, List.nil_append, List.drop_nil, isPrefix, beq_self_eq_true,
    Bool.true_and, PTrie.mem?, hleaf, reduceIte]
  simp [newLeaf, leafMem, hexPrefix, packNibbles, PTrie.memD, PTrie.mem?]

/-- The recomputed usage is `≥ 2^64`, so the result is not `wf`. -/
theorem ce_overflow_not_wf :
    (PTrie.ext [] (PTrie.leaf [0, 9, 2, 12] (.val []) 106)
      (18446744073709551615 + 106 - 1)).wf = false := by decide +kernel

/-- **`UpsertPreservesWf` fails on the recomputed `memory_usage`.** -/
theorem not_upsertPreservesWf_mem : ¬ UpsertPreservesWf := by
  intro h
  have := h _ _ [] [] [] ce_ext_wf ce_upsert_overflow
  rw [ce_overflow_not_wf] at this
  exact Bool.false_ne_true this

/-! ## The corrected statement

`UpsertPreservesWf` is false because `wf` is a *local* predicate.  The corrected obligation adds
two inputs the recomputation genuinely needs (both hold for real chunk state):

* the value's length and the inserted key's encoded length are `< 2^32` (the two facts a *fresh*
  leaf needs, which `t.wf` cannot supply because the leaf did not exist in `t`);
* the state trie is **canonical** (`NearSpec.PTrie.memOk`: each stored usage is what nearcore
  computes from the node's own fields and its children's) and has **headroom**
  (`NearSpec.PTrie.memLe NearSpec.memHead`).

`NearSpec.PTrie.upsert_wf` proves a single upsert preserves `wf` under exactly these.  The
statement below is that theorem at the `cdUpsert` entry point, so it is the form the write log
(`applyLog`) can consume instead of the false `UpsertPreservesWf`.  It is proved as
`upsertPreservesWfWithBounds` at the bottom of this file. -/

/-- The corrected write-path well-formedness obligation: `cdUpsert` preserves `wf` for a
ContractData key whose path and value are bounded, on a canonical trie (`PTrie.memOk`) with usage
headroom (`PTrie.memLe NearSpec.memHead`). -/
def UpsertPreservesWfWithBounds : Prop :=
  ∀ (t u : PTrie) (account key v : NearSpec.Bytes),
    t.wf = true → t.memOk → t.memLe NearSpec.memHead →
    v.length < 4294967296 →
    (NearSpec.hexPrefix (NearSpec.nibbles (cdWriteKey account key)) true).length < 4294967296 →
    cdUpsert t account key v = some u → u.wf = true

/-- **`UpsertPreservesWfWithBounds` is a theorem.**  The write path is a `PTrie.upsert` at the
ContractData nibble path, whose nibbles are canonical (`cdWriteKey_nibblesOk`), so
`NearSpec.PTrie.upsert_wf` applies directly. -/
theorem upsertPreservesWfWithBounds : UpsertPreservesWfWithBounds := by
  intro t u account key v hwf hmo hml hv hp hup
  unfold cdUpsert at hup
  exact NearSpec.PTrie.upsert_wf t _ v u hwf hmo hml
    (cdWriteKey_nibblesOk account key) hv hp hup

end ZkFormal.NearV3.D3
