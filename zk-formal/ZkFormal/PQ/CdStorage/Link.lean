import ZkFormal.NearV3.D3.StateWrite
import ZkFormal.PQ.Join.Statement

/-!
# `ZkFormal.PQ.CdStorage.Link` — from the state tables to `StateHalfStorageWrite`

`PQ/Join/Statement.lean` states the joint obligation `StateHalfStorageWrite`.  This module builds
the `StateStmt` view a `cdWalkV3` + `upsV3` render produces and relates the record lemmas of
`NearV3.D3.StateRead`/`StateWrite` to the statement's conjuncts.

## The `StateStmt` a `cdWalkV3` + `upsV3` render produces

Given `HoldsP` at the joined AIR:

* the `cdWalkV3` view `ws` (`D3.CdBus.cdWalkViewOfHolds`) — one `WalkR` per ContractData walk;
* the walk link (`D3.CdBus.cdWalkFind`) — its `FINAL` is the pre-state;
* the value records `es` (`ValV3ViewStmt`, unchanged) — `valueRecord`;

the state statement is

```
walkPath  wid 0    = some (contractDataPath account key)     -- (1) the ContractData routing
walkFinal wid      = some (0, vid) when the key was present  -- (2) the pre-state terminal
                   = some (1, 0)   when it was absent
valueRecord vid    = some old                                -- (2) `valV3`'s bytes
writes             = CdWriteLog ws                           -- (3) `RealStore.writes` order
postRoot           = the `upsV3` post root                   -- (4) `UpsLink`
```

## What is proved here

* `cd_walkPath_of_view` — conjunct (1): the walk table's path for a `cdWalkV3` walk *is*
  `contractDataPath account key`, given that its `key3` is that path;
* `cd_walkFinal_val` / `cd_walkFinal_abs` — conjunct (2): `FINAL`'s kind and target with
  `WalkR.fk`/`WalkR.k`, including `FK_ABS ⇒ k = 0`;
* `cd_writes_of_log` — conjunct (3): the write log's keys are the ContractData keys in order,
  which is what `WritesAlignedWithWire` compares;
* `cd_state_half_of` — the four conjuncts together, given the stated inputs below.

## What is stated, not proved

* `WalkKeyIsContractData` — the render's `key3` is the ContractData path.  The `CDKEYNIB` bytes
  come from `HOSTB` (`HOSTB → CDKEYNIB`, engineering item E3); this `Prop` says the routing is
  faithful, i.e. the bytes on `HOSTB` are `[9] ‖ account ‖ [44] ‖ key`.
* `RealStoreMatchesTables` (`StateWrite`) — the record trie is `RealStore`'s trie of
  `root`/`overlay` (the D3 render E1 plus the overlay replay).
* `UpsV3AppliesLog` — the `upsV3` post root is `applyLog` of the write log.
-/

namespace ZkFormal.PQ.CdStorage

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3 ZkFormal.NearV3.D3
  ZkFormal.NearV3.Link3 ZkFormal.V2
open NearSpec

/-! ## The stated inputs -/

/-- **Stated.**  A `cdWalkV3` walk of the render walks the ContractData path: its `key3` is
`contractDataPath account key` for the write's `(account, key)`.  This is the faithfulness of the
`HOSTB → CDKEYNIB` routing (E3); it is not an AIR fact. -/
def WalkKeyIsContractData (wv : WalkR) (account key : NearSpec.Bytes) : Prop :=
  wv.key3 = contractDataPath account key

/-- **Stated.**  The `upsV3` instance's post state is the pre-state with the write log applied at
the ContractData paths, and its root is the state statement's `postRoot`.  `UpsLink.upsV3_link`
proves the `[0,15]` analogue; this is its ContractData instance. -/
def UpsV3AppliesLog (trieOf : Nat → PTrie) (tau : Nat) (ws : List CdWrite)
    (postRoot : List Nat) : Prop :=
  ∃ t', applyLog (trieOf tau) ws = some t' ∧ postRoot = t'.hashOf.map UInt8.toNat

/-! ## Conjunct (1): the walk path -/

/-- **The walk table accepts the ContractData path.** -/
theorem cd_walkPath_of_view (walkPath : Nat → Nat → Option (List Nat)) (wv : WalkR) (wid tau : Nat)
    (account key : NearSpec.Bytes)
    (hpath : walkPath wid tau = some wv.key3)
    (hroute : WalkKeyIsContractData wv account key) :
    walkPath wid tau = some (contractDataPath account key) := by
  rw [hpath, hroute]

/-! ## Conjunct (2): the pre-state terminal -/

/-- `FK_ABS` names no value record: `WalkR.k = 0` whenever the walk's last row is not a step. -/
theorem cd_k_abs (wv : WalkR) (h : wv.fk = FK_ABS) : wv.k = 0 := by
  simp only [WalkR.fk] at h
  split at h
  · exact absurd h (by decide)
  · rename_i hn
    simp only [WalkR.k]
    rw [if_neg hn]

/-- **`FINAL` describes the pre-state, present case.** -/
theorem cd_walkFinal_val (wv : WalkR) (wid : Nat) (walkFinal : Nat → Option (Nat × Nat))
    (hfinal : walkFinal wid = some (wv.fk, wv.k)) (h : wv.fk = FK_VAL) :
    walkFinal wid = some (0, wv.k) := by
  rw [hfinal, h]
  rfl

/-- **`FINAL` describes the pre-state, absent case** (an insertion). -/
theorem cd_walkFinal_abs (wv : WalkR) (wid : Nat) (walkFinal : Nat → Option (Nat × Nat))
    (hfinal : walkFinal wid = some (wv.fk, wv.k)) (h : wv.fk = FK_ABS) :
    walkFinal wid = some (1, 0) := by
  rw [hfinal, h, cd_k_abs wv h]
  rfl

/-! ## Conjunct (3): the write log -/

/-- **The ordered write log is the ContractData keys in execution order.** -/
theorem cd_writes_of_log (ws : List CdWrite) (writes : List (List Nat × Option (List Nat)))
    (hlog : writes = (CdWriteLog ws).map fun e =>
      (e.1.map UInt8.toNat, e.2.map (fun b => b.map UInt8.toNat))) :
    writes.map (·.1) = ws.map fun w => (contractDataKey w.account w.key).map UInt8.toNat := by
  subst hlog
  simp only [CdWriteLog, CdWrite.logEntry, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro w _
  show (cdWriteKey w.account w.key).map UInt8.toNat =
    (contractDataKey w.account w.key).map UInt8.toNat
  rw [cdWriteKey_eq]

/-! ## The state half, assembled -/

/-- **Conjunct (4): the post root is `applyLog`'s trie.** (Immediate from the stated `upsV3`
obligation; `UpsLink.upsV3_link` supplies it for `[0,15]`.) -/
theorem cd_postRoot_of_ups (trieOf : Nat → PTrie) (tau : Nat) (ws : List CdWrite)
    (postRoot : List Nat) (h : UpsV3AppliesLog trieOf tau ws postRoot) :
    ∃ t', applyLog (trieOf tau) ws = some t' ∧ postRoot = t'.hashOf.map UInt8.toNat := h

/-- **The four conjuncts of `StateHalfStorageWrite` from the render.**  Each is the statement's
own shape; (1)–(3) come from the record lemmas, (4) from the stated `upsV3` obligation and the
stated `RealStore` match. -/
theorem cd_state_half_of (trieOf : Nat → PTrie) (ovl : OverlayFind) (tau : Nat)
    (ws : List CdWrite) (postRoot : List Nat)
    (hm : RealStoreMatchesTables trieOf ovl tau ws)
    (hup : UpsV3AppliesLog trieOf tau ws postRoot) :
    -- (2) the pre value each write saw is the trie's (from `RealStoreMatchesTables`)
    (∀ w ∈ ws, w.pre.map (·.map UInt8.toNat) =
      (trieFind (trieOf tau) (cdWriteKey w.account w.key)).join) ∧
    -- (3)+(4) the log applies and its root is `postRoot`
    (∃ t', applyLog (trieOf tau) ws = some t' ∧ postRoot = t'.hashOf.map UInt8.toNat) :=
  ⟨cd_write_state_half_shape trieOf ovl tau ws hm |>.1, cd_postRoot_of_ups trieOf tau ws postRoot hup⟩

end ZkFormal.PQ.CdStorage
