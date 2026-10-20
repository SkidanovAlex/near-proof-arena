import ZkFormal.NearV3.D3.CdBus
import ZkFormal.NearV3.Assembly.ViewsV3

/-!
# `ZkFormal.NearV3.D3.StateRead` — the ContractData *read* path: `HoldsP` gives the stored value

The state half of a `storage_write` starts with a **read** of the pre-state at the
`TrieKey::ContractData` path.  This module states exactly what the state proof must produce and
proves the row/lookup lemmas that turn a `HoldsP` witness into "the stored value is `v`".

## Table shapes

A ContractData read is rendered by **the existing tables**, with the key nibbles entering on one
new bus:

| table | role in a ContractData read | shape |
|---|---|---|
| `cdWalkV3` (`walkV3` with `KEYNIB ↦ CDKEYNIB`) | the path walk of `[9]‖account‖[44]‖key` | one row per key symbol + `START` + `END`; one interaction per row on `CDKEYNIB` when it is a step |
| `nodeV3`, `headV3` | the path records of the pre-state trie | unchanged |
| `valV3` | the value record of an overwrite (`FK_VAL`) | unchanged: one row per value byte on `VBYTES` |
| `uniqV3`, `sizeV3` | uniqueness / counted bytes | unchanged |

**Bus messages**

```
CDKEYNIB  [w, t, sym, last]        cdWalkV3 receives (walkV3's KEYNIB, renamed)
FINAL     [w, τ, fk, k]            cdWalkV3 sends (unchanged): fk=0 VAL → k = value record id;
                                   fk=1 ABS → k = 0
EDGE / BMAP                        unchanged; nodeV3 and headV3 provide
VBYTES    [vid, pos, byte]         valV3 receives the value bytes (unchanged)
```

`cd_key_stream` (`CdBus.lean`) proves the `sym`s of a walk whose `key3` is
`contractDataPath account key` are exactly that path followed by `END`.

## What is proved here

* `CdReadRow` — the per-row content of a `CDKEYNIB` message, derived from `WalkWf3` (no new
  constraint).
* `cd_nib_symbols` — the `CDKEYNIB` symbols a walk emits are its `keyStream`, i.e. the
  ContractData path.
* `cd_read_value` — **the lookup lemma**: for a `cdWalkV3` walk of `contractDataPath account key`
  of an instance whose record trie is the chunk's pre-state trie, `FK_VAL` gives
  `find path = some (some old)` with `old` the *bytes of the value record `valV3` sent on
  `VBYTES`*, and `FK_ABS` gives `find path = some none` (a proven insertion).
* `cd_read_value_bytes` — the same value spelled as the `VBYTES` list `valV3` receives, so the
  state side's value bytes are literally the trie's value bytes.

## What is **not** proved

* That the `CDKEYNIB` messages come from `HOSTB` (the Wasm byte stream).  That is the HOST-chip
  side of the join, `E3`/`P6` of `results/pq-d3-join/README.md`.
* That the record trie is `RealStore`'s trie (see `StateWrite.lean`, `RealStoreMatchesTables`,
  stated).
-/

namespace ZkFormal.NearV3.D3

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3 ZkFormal.NearV3.Link3
  ZkFormal.V2

/-! ## Rows of the read -/

/-- One row of a ContractData walk, as the state side must be able to describe it: the walk id,
its instance, the key symbol consumed (or `START`/`END`), the row mode (`0` step, `1` absent by
key, `2` absent at a branch, `3` drain) and the `last` flag. -/
structure CdReadRow where
  w : Nat
  tau : Nat
  sym : Nat
  mode : Nat
  last : Bool
  deriving Repr, DecidableEq, Inhabited

/-- The rows of a walk, as `CdReadRow`s. -/
def cdReadRows (wv : WalkR) : List CdReadRow :=
  (List.range wv.steps.length).map fun i =>
    { w := wv.w, tau := wv.tau, sym := (wv.step i).sym, mode := (wv.step i).mode
      last := decide (i + 1 = wv.steps.length) }

/-- Every `mode` is one of the four `walkV3` modes (`WalkWf3.rows` → `StepOk.mode`). -/
theorem cdReadRow_mode {ws : List WalkR} (hW : WalkWf3 ws) {wv : WalkR} (hwv : wv ∈ ws)
    {i : Nat} (hi : i < wv.steps.length) : (wv.step i).mode ≤ 3 := by
  rw [WalkR.step, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  exact (hW.rows wv hwv i hi).mode

/-- The last row's symbol is `END` (`WalkWf3.rows` → `StepOk.lastEnd`). -/
theorem cdReadRow_last_end {ws : List WalkR} (hW : WalkWf3 ws) {wv : WalkR} (hwv : wv ∈ ws) :
    (wv.step (wv.steps.length - 1)).sym = SYM_END := by
  have hlen := hW.len wv hwv
  have hi : wv.steps.length - 1 < wv.steps.length := by omega
  have hlast : (wv.steps.length - 1 + 1 == wv.steps.length) = true := by
    simp; omega
  rw [WalkR.step, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  exact (hW.rows wv hwv (wv.steps.length - 1) hi).lastEnd hlast

/-- The first row is `START` at symbol index `0` (`WalkWf3.start`). -/
theorem cdReadRow_start {ws : List WalkR} (hW : WalkWf3 ws) {wv : WalkR} (hwv : wv ∈ ws) :
    (wv.step 0).mode = 0 ∧ (wv.step 0).sym = SYM_START ∧ (wv.step 0).e.getD 1 0 = wv.tau :=
  hW.start wv hwv

/-! ## The `CDKEYNIB` stream -/

/-- The `CDKEYNIB` messages of a walk are `[w, t, sym, last]` (`walkV3`'s `KEYNIB` receive with
the bus renamed; `cdKeynibMsgs` in `CdBus.lean`).  This is the traffic the state side's key
provider must emit. -/
theorem cd_nib_symbols (wv : WalkR) :
    (cdKeynibMsgs wv).map (·.getD 2 0) = keyStream wv :=
  cdKeynibMsgs_symbols wv

/-- **The bus content of a ContractData read.**  `wv`'s nibbles are exactly the ContractData
path, and each message is `[w, t, sym, last]`. -/
theorem cd_nib_is_path (wv : WalkR) (account key : NearSpec.Bytes)
    {ws : List WalkR} (hW : WalkWf3 ws) (hwv : wv ∈ ws)
    (hkey : wv.key3 = contractDataPath account key) :
    (cdKeynibMsgs wv).map (·.getD 2 0) = contractDataPath account key ++ [SYM_END] := by
  rw [cd_nib_symbols]
  exact cd_key_stream wv account key hkey (hW.len wv hwv) (cdReadRow_last_end hW hwv)

/-! ## The lookup lemma -/

/-- **`HoldsP` gives the stored value at a ContractData key.**

`wv` is a walk of the `cdWalkV3` table of the chunk (`hW`, from `cdWalkViewOfHolds`), its key is
`contractDataPath account key`, and the chunk's record trie is the instance's pre-state trie
(`walk3_find'`'s hypotheses, which the D0a/D1 extraction already supplies).  Then:

* `FK_VAL` — the trie has a value at the path, and it is `valOf V i` for `i` the value-record
  position the `FINAL` message names;
* `FK_ABS` — the trie has **no** value at the path (a proven insertion).

The value never comes from the write; it is the pre-state value the walk read. -/
theorem cd_read_value {vs : List NodeS3} {hs : List HeadE} {es : List ValE} {ws : List WalkR}
    (hw : NodeWf3 vs) (hhw : HeadWf hs) (hvw : ValWf es) (hW : WalkWf3 ws)
    (hb : ParentBal vs hs) (hvb : VParentBal vs es)
    (hE : Walk3.BusBal vs hs ws B_EDGE) (hB : Walk3.BusBal vs hs ws B_BMAP)
    (hbytes : ∀ s ∈ vs, ∀ x ∈ s.v.ser false, x < 256)
    (hsym : ∀ wv ∈ ws, ∀ i, 1 ≤ i → i < wv.steps.length → (wv.step i).sym ≠ SYM_START)
    {wv : WalkR} (hwv : wv ∈ ws) :
    ∃ h ∈ hs, h.tau = wv.tau ∧
      (wv.fk = FK_VAL →
        (fullTree (recsOf (vpos (vid0 es)) vs) (valsOf3 vs es) h.rid).find wv.key3 =
          some (some (valOf (valsOf3 vs es) (vpos (vid0 es) wv.k)))) ∧
      (wv.fk = FK_ABS →
        (fullTree (recsOf (vpos (vid0 es)) vs) (valsOf3 vs es) h.rid).find wv.key3 =
          some none) :=
  cdWalkFind hw hhw hvw hW hb hvb hE hB hbytes hsym hwv

/-- **The value bytes are the `VBYTES` bytes.**  A `FK_VAL` read of a value record at position
`t` returns exactly the bytes `valV3` receives on `VBYTES (vid, pos, byte)` — so the state side's
`HOSTB`/read answer and the trie value are the same list of bytes. -/
theorem valRecvs_vbytes (es : List ValE) :
    valRecvs es B_VBYTES = es.flatMap fun e => if e.vz then [] else
      (List.range e.bytes.length).map fun p => [e.vid, p, e.bytes.getD p 0] := by
  simp only [valRecvs, B_VBYTES, B_VPARENT, B_DUP, B_ENT]
  rfl

theorem cd_read_value_bytes {vs : List NodeS3} {es : List ValE} {t : Nat} (hvw : ValWf es)
    (ht : t < es.length) :
    valOf (valsOf3 vs es) t = toB es[t].bytes ∧
      (∀ p, p < es[t].bytes.length → [es[t].vid, p, es[t].bytes.getD p 0]
        ∈ valRecvs es B_VBYTES) := by
  refine ⟨by simp [valOf, valsOf3, ht], fun p hp => ?_⟩
  rw [valRecvs_vbytes, List.mem_flatMap]
  refine ⟨es[t], List.getElem_mem ht, ?_⟩
  by_cases hz : es[t].vz = true
  · rw [if_pos hz]
    have he := (hvw.shape _ (List.getElem_mem ht)).1 hz
    rw [he.2] at hp; simp at hp
  · rw [if_neg hz]
    exact List.mem_map.mpr ⟨p, List.mem_range.mpr hp, rfl⟩

end ZkFormal.NearV3.D3
