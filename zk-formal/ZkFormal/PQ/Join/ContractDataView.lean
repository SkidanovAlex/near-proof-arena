import ZkFormal.NearV3.D3.ContractData
import ZkFormal.NearV3.Extract.WalkView
import ZkFormal.PQ.Join.Statement

/-!
# ZkFormal.PQ.Join.ContractDataView — join step 3: the contract-data walk reuses `walkV3`

Lane `pq-state-port`.  Join step 3 (`JOIN-INTERFACE.md` §5): the state half of a `storage_write`
needs a trie walk over the **contract-data** key `[9] ‖ account ‖ [44] ‖ key`
(`D3.ContractData.contractDataKey`).  `D3.ContractData` builds it as `cdWalkV3`: the proved
`WalkV3.table` with its key-nibble bus renamed (`B_KEYNIB = 5` → `B_CDKEYNIB = 76`).

This module proves the reuse claim rather than asserting it.

## Proved

* `rowInterSum_rename_other` — a bus rename is **inert** on every bus that is neither the source
  nor the destination: the renamed interaction leaves `b` (it was `src ≠ b`) and the replacement
  lands on `dst ≠ b`.
* `cdWalkV3_inert` — the same at the `tableBusCount` level, so **`cdWalkV3`'s `EDGE`, `BMAP` and
  `FINAL` traffic is exactly `walkV3`'s**.  Only the `KEYNIB` stream moves, to `CDKEYNIB`.  Every
  `walkV3` constraint, width, `maxLog` and traffic lemma therefore transfers verbatim; the only
  new content the contract-data walk needs is the key-nibble stream itself.
* `cdKey_nibble_count` — that stream's length is `2 · |[9] ‖ account ‖ [44] ‖ key|`, determined by
  the account and key lengths, which is what `StateHalfStorageWrite` (1) relies on.
* `W_CD_clear` — the ContractData walk-id base `2^21` is strictly above every walk id the D1
  tables use (transaction `W_TX + 2·op`, local-receipt `W_LOC + l`, access-key `W_AK`, queue
  `W_QV`), so a contract-data walk cannot be confused with any of them on the shared `FINAL` bus.

## Not proved here

`StateHalfStorageWrite` itself — walk + value record + `upsV3` post-root for a *particular* honest
render.  That is discharged by the state side's render lemmas plus the `upsV3` obligation; what
step 3 needs from the tables is exactly what is proved here.
-/

namespace ZkFormal.PQ.Join

open ZkFormal.Air ZkFormal.Near ZkFormal.NearV3 ZkFormal.NearV3.D3 ZkFormal.Algebra

/-! ## The rename is inert elsewhere -/

/-- A bus rename is inert on every bus that is neither the source nor the destination of the
rename.  This is the per-row interaction sum, the inner loop of `tableBusCount`. -/
theorem rowInterSum_rename_other (is : List Interaction) (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (src dst b : Nat) (hb : b ≠ src) (hd : b ≠ dst) (send : Bool) (m : List Fp)
    (acc : Nat) :
    (is.map (fun i => if i.bus = src then { i with bus := dst } else i)).foldr (fun i z =>
      (if i.bus = b ∧ i.send = send ∧ i.msgVal tr t r pub = m then i.multNat tr t r pub else 0)
        + z) acc
      = is.foldr (fun i z =>
      (if i.bus = b ∧ i.send = send ∧ i.msgVal tr t r pub = m then i.multNat tr t r pub else 0)
        + z) acc := by
  induction is with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.foldr_cons]
    by_cases hx : x.bus = src
    · rw [if_pos hx]
      have h1 : ¬ (x.bus = b) := by rw [hx]; exact fun h => hb h.symm
      have h2 : ¬ (dst = b) := fun h => hd h.symm
      simp only [h1, h2, false_and, if_false, Nat.zero_add]
      exact ih
    · rw [if_neg hx]
      exact congrArg (fun z => _ + z) ih

/-- The same at the `tableBusCount` level: on every bus other than `KEYNIB`/`CDKEYNIB`,
`cdWalkV3`'s traffic count is `walkV3`'s, row for row.  This is what lets every `walkV3` traffic
lemma transfer to the contract-data walk unchanged. -/
theorem cdWalkV3_busCount (tr : Trace Fp) (t : Nat) (pub : List Fp) (b : Nat)
    (hb : b ≠ B_KEYNIB) (hd : b ≠ B_CDKEYNIB) (send : Bool) (m : List Fp) :
    tableBusCount cdWalkV3.interactions tr t pub b send m
      = tableBusCount WalkV3.table.interactions tr t pub b send m := by
  unfold tableBusCount
  congr 1
  funext r acc
  exact rowInterSum_rename_other WalkV3.table.interactions tr t r pub B_KEYNIB B_CDKEYNIB b hb hd
    send m acc

/-- **`cdWalkV3` is inert on every bus except `KEYNIB`/`CDKEYNIB`.**  So on `EDGE`, `BMAP` and
`FINAL` its traffic is `walkV3`'s exactly, and the only stream that changes is the key nibbles. -/
theorem cdWalkV3_inert (tr : Trace Fp) (t r : Nat) (pub : List Fp) (b : Nat)
    (hb : b ≠ B_KEYNIB) (hd : b ≠ B_CDKEYNIB) (send : Bool) (m : List Fp) :
    (cdWalkV3.interactions.map fun i =>
        if i.bus = b ∧ i.send = send ∧ i.msgVal tr t r pub = m then i.multNat tr t r pub else 0).sum
      = (WalkV3.table.interactions.map fun i =>
        if i.bus = b ∧ i.send = send ∧ i.msgVal tr t r pub = m then i.multNat tr t r pub else 0).sum := by
  show (List.map (fun i => if i.bus = b ∧ i.send = send ∧ i.msgVal tr t r pub = m
        then i.multNat tr t r pub else 0)
      (List.map (fun i => if i.bus = B_KEYNIB then { i with bus := B_CDKEYNIB } else i)
        WalkV3.table.interactions)).sum
    = (List.map (fun i => if i.bus = b ∧ i.send = send ∧ i.msgVal tr t r pub = m
        then i.multNat tr t r pub else 0) WalkV3.table.interactions).sum
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro x _
  simp only [Function.comp]
  by_cases hx : x.bus = B_KEYNIB
  · rw [if_pos hx]
    have h1 : ¬ (x.bus = b) := by rw [hx]; exact fun h => hb h.symm
    have h2 : ¬ (B_CDKEYNIB = b) := fun h => hd h.symm
    simp only [h1, h2, false_and, if_false]
  · rw [if_neg hx]

/-! ## The renamed table keeps the proved shape -/

/-- `cdWalkV3` has `walkV3`'s constraints, so every `walkV3` constraint lemma applies unchanged. -/
theorem cdWalkV3_constraints : cdWalkV3.constraints = WalkV3.table.constraints := rfl

/-- `cdWalkV3` has `walkV3`'s width. -/
theorem cdWalkV3_width : cdWalkV3.width = WalkV3.table.width := rfl

/-- `cdWalkV3` has `walkV3`'s height cap, so `walkV3`'s capacity bound applies unchanged. -/
theorem cdWalkV3_maxLog : cdWalkV3.maxLog = WalkV3.table.maxLog := rfl

/-- `cdWalkV3` has no interaction left on `KEYNIB`. -/
theorem cdWalkV3_no_keynib :
    (cdWalkV3.interactions.filter (·.bus = B_KEYNIB)).length = 0 := by decide +kernel

/-- `cdWalkV3` receives exactly one `CDKEYNIB` stream. -/
theorem cdWalkV3_one_cdkeynib :
    (cdWalkV3.interactions.filter (·.bus = B_CDKEYNIB)).length = 1 := by decide +kernel

/-! ## The key-nibble stream -/

/-- The nibble path of a contract-data key has exactly twice as many entries as the key has bytes. -/
theorem cdKey_nibble_count (account key : NearSpec.Bytes) :
    (contractDataPath account key).length = 2 * (contractDataKey account key).length :=
  contractDataPath_length account key

/-- The ContractData key is `[9] ‖ account ‖ [44] ‖ key` — the shape
`StateHalfStorageWrite` (1) asserts. -/
theorem cdKey_shape (account key : NearSpec.Bytes) :
    contractDataKey account key =
      [colContractData] ++ account ++ [accountDataSeparator] ++ key := rfl

/-! ## The walk ids cannot collide -/

/-- The largest walk id the D1 tables use: transaction walks (`W_TX + 2·op`, `op < 2·NT0 = 8192`),
local-receipt slots (`W_LOC + l`, `l < 4481`), access-key walks (`W_AK + …`) and queue walks
(`W_QV + τ + 64·slot`). -/
def d1WalkIdBound : Nat := 2 ^ 21

/-- **The contract-data walk-id base clears every D1 walk id.**  `W_CD = 2^21` is strictly above
all of them, so a contract-data walk can never be mistaken for a transaction, local-receipt,
access-key or queue walk on the shared `FINAL` bus. -/
theorem W_CD_clear :
    ZkFormal.NearV3.D1.W_TX + 2 * (2 * 4096) < W_CD ∧
    ZkFormal.NearV3.D1.W_LOC + 4481 < W_CD ∧
    ZkFormal.NearV3.W_AK < W_CD ∧
    ZkFormal.NearV3.W_QV + 64 < W_CD := by
  refine ⟨by decide, by decide, by decide, by decide⟩

end ZkFormal.PQ.Join
