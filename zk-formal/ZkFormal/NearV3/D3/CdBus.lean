import ZkFormal.NearV3.D3.ContractData
import ZkFormal.NearV3.Link.Compose3
import ZkFormal.NearV3.Extract.WalkProof2
import ZkFormal.V2.Air
import ZkFormal.Chacha.Link

/-!
# `ZkFormal.NearV3.D3.CdBus` — `cdWalkV3` is `walkV3`, and every walk soundness lemma applies

`D3/ContractData.lean` defines `cdWalkV3 := renameBus B_KEYNIB B_CDKEYNIB WalkV3.table`, i.e.
`walkV3` with every interaction whose bus is `KEYNIB` moved to `CDKEYNIB`.  This module makes
that reuse *proof-carrying*:

* **`cdWalkLocal`** — `TableLocal cdWalkV3` gives `TableLocal WalkV3.table` (same width, same
  constraints, same `maxLog`; only one bus field of one interaction moves);
* **`cdWalkView`** — from `HoldsP` at a `cdWalkV3` table index, the `walkV3` view `WalkWf3 ws`
  (and its `2^21` row bound), with no traffic obligation;
* **`cdWalkFind`** — the walk link: every `cdWalkV3` walk of a chunk computes `find` / absent on
  the record trie of a head of its instance, ending at the value record `valOf V (vpos … k)`.
  This is what makes the *read* half (`HoldsP` ⇒ "the value actually stored") come out of the
  already-proved `walk3_find'`;
* **`keyStream`**, **`cd_key_stream`** — the `CDKEYNIB` nibble stream of a ContractData walk is
  the prefix path then the key's nibbles, then `END`: what the state side must produce.

The interaction bookkeeping (`renameOne`, `contrib_renamed`) is below the view; it is not used
by the walk link, and is kept only to show the rename moves exactly one bus.
-/

namespace ZkFormal.NearV3.D3

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3 ZkFormal.NearV3.Link3 ZkFormal.V2

/-! ## The rename of one interaction -/

/-- The rename of a single interaction: `bus = src` becomes `dst`; multiplicity and message are
untouched (so `multNat`/`msgVal` are unchanged). -/
def renameOne (src dst : Nat) (i : Interaction) : Interaction :=
  if i.bus = src then { i with bus := dst } else i

theorem renameBus_interactions (src dst : Nat) (T : ZkFormal.Air.Table) :
    (renameBus src dst T).interactions = T.interactions.map (renameOne src dst) := rfl

theorem renameOne_msgVal (src dst : Nat) (i : Interaction) {tr : Trace Fp} {t r : Nat}
    {pub : List Fp} : (renameOne src dst i).msgVal tr t r pub = i.msgVal tr t r pub := by
  unfold renameOne Interaction.msgVal
  split <;> rfl

theorem renameOne_multNat (src dst : Nat) (i : Interaction) {tr : Trace Fp} {t r : Nat}
    {pub : List Fp} : (renameOne src dst i).multNat tr t r pub = i.multNat tr t r pub := by
  unfold renameOne Interaction.multNat
  split <;> rfl

theorem renameOne_send (src dst : Nat) (i : Interaction) : (renameOne src dst i).send = i.send := by
  unfold renameOne; split <;> rfl

theorem renameOne_mult (src dst : Nat) (i : Interaction) : (renameOne src dst i).mult = i.mult := by
  unfold renameOne; split <;> rfl

theorem renameOne_bus (src dst : Nat) (i : Interaction) :
    (renameOne src dst i).bus = if i.bus = src then dst else i.bus := by
  unfold renameOne; split <;> simp_all

/-- The counting identity of the rename (one bus moves; the message and multiplicity do not). -/
theorem contrib_renamed (src dst : Nat) (i : Interaction) (hne : src ≠ dst)
    (hnd : i.bus ≠ dst) (tr : Trace Fp) (t r : Nat) (pub : List Fp) (b : Nat) (sd : Bool)
    (m : List Fp) :
    (if (renameOne src dst i).bus = b ∧ (renameOne src dst i).send = sd ∧
        (renameOne src dst i).msgVal tr t r pub = m
      then (renameOne src dst i).multNat tr t r pub else 0) =
      if b = dst then (if i.bus = src ∧ i.send = sd ∧ i.msgVal tr t r pub = m
          then i.multNat tr t r pub else 0)
      else if b = src then 0
      else (if i.bus = b ∧ i.send = sd ∧ i.msgVal tr t r pub = m then i.multNat tr t r pub else 0) := by
  rw [renameOne_bus, renameOne_send, renameOne_msgVal, renameOne_multNat]
  by_cases hb : i.bus = src
  · by_cases hbd : b = dst
    · by_cases hP : i.send = sd ∧ i.msgVal tr t r pub = m <;> simp_all [eq_comm, hne, Ne.symm hne]
    · by_cases hbs : b = src <;> by_cases hP : i.send = sd ∧ i.msgVal tr t r pub = m <;>
        simp_all [eq_comm, hne, Ne.symm hne]
  · by_cases hbd : b = dst
    · by_cases hP : i.send = sd ∧ i.msgVal tr t r pub = m <;> simp_all [eq_comm, hne, Ne.symm hne]
    · by_cases hbs : b = src <;> by_cases hP : i.send = sd ∧ i.msgVal tr t r pub = m <;>
        simp_all [eq_comm, hne, Ne.symm hne]

/-! ## Local legality and the `walkV3` view -/

theorem cdWalkV3_no_dst : ∀ i ∈ WalkV3.table.interactions, i.bus ≠ B_CDKEYNIB := by
  decide +kernel

/-- The `walkV3` constraints are `cdWalkV3`'s: the rename changes no constraint. -/
theorem cdWalkV3_constraints : cdWalkV3.constraints = WalkV3.table.constraints := rfl

theorem cdWalkV3_maxLog : cdWalkV3.maxLog = WalkV3.table.maxLog := rfl

theorem cdWalkV3_interactions :
    cdWalkV3.interactions = WalkV3.table.interactions.map (renameOne B_KEYNIB B_CDKEYNIB) := rfl

/-- **Local legality of a `cdWalkV3` table is local legality of `walkV3`.** -/
theorem cdWalkLocal {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (h : TableLocal cdWalkV3 tr t pub) : TableLocal WalkV3.table tr t pub where
  log_ge := h.log_ge
  log_le := h.log_le
  constr := h.constr
  bits := by
    intro r hr i hi b hb
    have hi' : renameOne B_KEYNIB B_CDKEYNIB i ∈ cdWalkV3.interactions := by
      rw [cdWalkV3_interactions]
      exact List.mem_map_of_mem hi
    have hb' : b ∈ (renameOne B_KEYNIB B_CDKEYNIB i).mult := by
      rw [renameOne_mult]; exact hb
    exact h.bits r hr _ hi' b hb'

/-- **The `walkV3` view of a `cdWalkV3` table.**  `WalkWf3 ws` and the `2^21` row bound; no
traffic statement is needed for the walk link. -/
theorem cdWalkView (tr : Trace Fp) (pub : List Fp) (t : Nat) (h : TableLocal cdWalkV3 tr t pub) :
    ∃ ws, WalkWf3 ws ∧ (ws.flatMap (·.steps)).length ≤ 2 ^ 21 := by
  obtain ⟨ws, hw, hrows, _⟩ := walk3_view_at 21 (by decide) tr pub t (cdWalkLocal h)
  exact ⟨ws, hw, hrows⟩

/-- The same from `HoldsP`, given the table index of `cdWalkV3` in the AIR. -/
theorem cdWalkViewOfHolds {AP : AirP} {pub : List Fp} {tr : Trace Fp} (hH : HoldsP AP pub tr)
    {t : Nat} (ht : t < AP.tables.length) (hT : AP.tables[t]! = cdWalkV3) :
    ∃ ws, WalkWf3 ws ∧ (ws.flatMap (·.steps)).length ≤ 2 ^ 21 := by
  have htab : AP.tables[t] = cdWalkV3 := by rw [← ZkFormal.Chacha.tables_get ht, hT]
  have hloc : TableLocal cdWalkV3 tr t pub := {
    log_ge := (hH.logBound t ht).1
    log_le := by rw [← htab]; exact (hH.logBound t ht).2
    constr := by
      intro r hr e he
      rw [← htab] at he
      exact hH.constr t ht r hr e he
    bits := by
      intro r hr i hi b hb
      rw [← htab] at hi
      exact hH.bits t ht r hr i hi b hb }
  exact cdWalkView tr pub t hloc

/-! ## The walk link (the read half) -/

/-- **Every `cdWalkV3` walk is a `walkV3` walk of the same chunk.**  From `HoldsP` at the
`cdWalkV3` index plus the chunk's node/head/value views, `EDGE`/`BMAP` balance, `PARENT`/DIGEST
structure, the record bytes and the `KEYNIB`-style key symbol hypothesis, a walk of the
ContractData table answers its key on the instance's record trie exactly as `FINAL` says:
kind `VAL` ⇒ the value record is `valOf V (vpos (vid0 es) wv.k)`; kind `ABS` ⇒ absent.

This is `walk3_find'` applied to the `cdWalkV3` view; there is no new soundness argument.  The
only difference from a `walkV3` call is that the key stream arrives on `CDKEYNIB`
(`cd_key_stream`). -/
theorem cdWalkFind {vs : List NodeS3} {hs : List HeadE} {es : List ValE} {ws : List WalkR}
    (hw : NodeWf3 vs) (hhw : HeadWf hs) (hvw : ValWf es) (hW : WalkWf3 ws)
    (hb : ParentBal vs hs) (hvb : VParentBal vs es)
    (hE : Walk3.BusBal vs hs ws B_EDGE) (hB : Walk3.BusBal vs hs ws B_BMAP)
    (hbytes : ∀ s ∈ vs, ∀ x ∈ s.v.ser false, x < 256)
    (hsym : ∀ wv ∈ ws, ∀ i, 1 ≤ i → i < wv.steps.length → (wv.step i).sym ≠ SYM_START)
    {wv : WalkR} (hwv : wv ∈ ws) :
    ∃ h ∈ hs, h.tau = wv.tau ∧
      (wv.fk = FK_VAL → (fullTree (recsOf (vpos (vid0 es)) vs) (valsOf3 vs es) h.rid).find wv.key3 =
        some (some (valOf (valsOf3 vs es) (vpos (vid0 es) wv.k)))) ∧
      (wv.fk = FK_ABS → (fullTree (recsOf (vpos (vid0 es)) vs) (valsOf3 vs es) h.rid).find wv.key3
        = some none) :=
  walk3_find' hw hhw hvw hW hb hvb hE hB hbytes hsym hwv

/-! ## The `CDKEYNIB` stream the state side must produce -/

/-- The key symbols a walk's key provider sends, in row order: one per row `1 … L-2`, then `END`. -/
def keyStream (wv : WalkR) : List Nat :=
  (List.range (wv.steps.length - 1)).map fun t => (wv.step (t + 1)).sym

/-- **The nibble stream of a ContractData walk is the ContractData path.** -/
theorem cd_key_stream (wv : WalkR) (account key : NearSpec.Bytes)
    (hkey : wv.key3 = contractDataPath account key)
    (hL : 2 ≤ wv.steps.length)
    (hlast : (wv.step (wv.steps.length - 1)).sym = SYM_END) :
    keyStream wv = contractDataPath account key ++ [SYM_END] := by
  obtain ⟨m, hm⟩ : ∃ m, wv.steps.length = m + 2 := ⟨wv.steps.length - 2, by omega⟩
  have h1 : m + 2 - 1 = m + 1 := by omega
  have h2 : m + 2 - 2 = m := by omega
  have hk : (List.range m).map (fun t => (wv.step (t + 1)).sym) = contractDataPath account key := by
    have := hkey
    unfold WalkR.key3 at this
    rwa [hm, h2] at this
  have hl : (wv.step (m + 1)).sym = SYM_END := by
    have := hlast
    rwa [hm, h1] at this
  unfold keyStream
  rw [hm, h1, show List.range (m + 1) = List.range m ++ [m] from List.range_succ]
  simp only [List.map_append, List.map_cons, List.map_nil, hk, hl]

/-- The `CDKEYNIB` messages of a walk (`walkV3`'s `KEYNIB` receive, with the bus renamed): one
per key symbol, `[w, t, sym, last]`, `t = 0 … L-2`, `last = 1` on the final `END`. -/
def cdKeynibMsgs (wv : WalkR) : List (List Nat) :=
  (List.range (wv.steps.length - 1)).map fun t =>
    [wv.w, t, (wv.step (t + 1)).sym, if t + 2 = wv.steps.length then 1 else 0]

theorem cdKeynibMsgs_symbols (wv : WalkR) : (cdKeynibMsgs wv).map (·.getD 2 0) = keyStream wv := by
  unfold cdKeynibMsgs keyStream
  rw [List.map_map]
  rfl

end ZkFormal.NearV3.D3
