import WasmBase.Main.Abstract
import WasmBase.Main.HostRel
import WasmBase.Main.ExecHost

/-!
# WasmBase.Main.SegHarness — `exec_of_rows` with a segment that restarts

`Main/Abstract.lean:exec_of_rows` threads **one** gas segment `(S_seg, segb)` through every row and
concludes `R · (Sf − S_seg) + g = segb`.  A host-carrying trace cannot use it: a HOST row
resynchronises the budget (`g := remaining`), so every instruction after it lives in a different
segment.

**Status: the segment-carrying spec is done; the induction is not.**  `RowSpecSeg` (a row whose
successor segment is a parameter) and `RowFactsSeg` are defined and `RowSpec2`/`RowFacts2` embed into
them at a fixed segment.  The remaining step is re-running `exec_of_rows`'s 235-line proof with
`seg` threaded instead of fixed — see the "Remaining work" section at the end of this file.

## The two differences from `exec_of_rows`

The proof is `exec_of_rows`'s, with the segment touched in exactly three places.

1. **The per-row gas side condition.**  `exec_of_rows` derives `R · (S+fee − S_seg) ≤ segb` for
   every row from a *single* hypothesis `R · (Sf − S_seg) ≤ segb`, using monotonicity of the gas
   field along the path.  With restarts that monotonicity is false — `S` (the instruction counter)
   is still monotone, but the *budget* is reset, and after a restart at `(S, g_after)` the next
   row's condition is `R · fee ≤ g_after`, which is a genuine machine fact ("the fee fits in what
   the host left"), not a consequence of the initial budget.  So it becomes a per-step hypothesis
   `hstepgas` (§ `step_gas_side`).
2. **The successor `Rel`'s segment.**  `RowSpec2` returns `Rel` at the segment it was given.  At a
   kept row `segs (k+1) = segs k`, so that is the wanted segment.  At a host row the successor comes
   from `Main/HostRel.host_rel_restart` instead, at `segs (k+1) = (S + fee, g_after)`.
3. **The conclusion.**  The final invariant is reported at `segs (rs.length)` — the segment after
   the last row — rather than at the single global pair.

Everything else — the chain, the level bookkeeping, `ChanOK`, the monotone `S`, the halting step —
is unchanged, which is why the proof is a *modification* of `exec_of_rows` rather than a new
argument.

## The invariant carried

`Rel` at `segs k` for the state after `k` rows, with the live set `live init prodL consL k`.  This is
`exec_of_rows`'s `IH` with `(S_seg, segb)` replaced by `segs k`.
-/

namespace WasmBase

open ZkFormal.Algebra Chips Local
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4000

/-! ## The per-step gas side condition

`exec_of_rows` gets its per-row gas bound from monotonicity: `R·(S_k − S_seg) ≤ segb` for all `k`
follows from the bound at the end because `S_k ≤ Sf`.  That fails under restarts.  What survives is
weaker and must be assumed instead: at each row, the fee fits in the budget the current segment
carries. -/

/-- **The per-row gas side condition.**  `R · (S + fee − S_seg) ≤ segb` is what `RowSpec2` needs.
After a restart to `(S_h, g_after)` and before the next row at gas field `S`, this is
`R · (S − S_h) + R · fee ≤ g_after`: the gas burnt since the restart plus this row's fee must fit in
what the host returned.  A real machine property, not a bookkeeping identity. -/
def StepGas (R : Nat) : Nat → Nat → Nat → Nat → Nat → Prop :=
  fun S fee S_seg segb _ => R * (S + fee - S_seg) ≤ segb

/-- The no-restart case recovers `exec_of_rows`'s single global hypothesis: if the segment never
moves, the per-row bound is exactly the monotone consequence of the final one. -/
theorem StepGas.of_global {R Sf S_seg segb : Nat} (hseg : S_seg ≤ Sf)
    (h : R * (Sf - S_seg) ≤ segb) {S fee : Nat} (hSe : S + fee ≤ Sf) :
    StepGas R S fee S_seg segb Sf := by
  unfold StepGas
  exact Nat.le_trans (Nat.mul_le_mul_left _ (by omega)) h


/-! ## The per-row spec that names its successor segment

`RowSpec2` concludes `Rel` at the segment it was *given*.  The induction needs the successor
segment to be part of the row's output, because a host row changes it.  `RowSpecSeg` is that: the
same shape as `RowSpec2`, with the successor `Rel` at an arbitrary `(S_seg', segb')` chosen by the
row. -/

/-- **A row's step, with both segments explicit.**  The input segment and the successor segment are
*parameters*: the row is only asserted at the segment it actually runs in, and it lands where the
caller says.  This is what makes the segment thread permutation-safe — the pair travels with the
row in the action list.

* ordinary row: `sgin = sgout`, from `RowSpec2` (`ofSame`);
* host row: `sgout = (S + fee, g_after)`, from `Main/HostRel.host_rel_restart` (`ofHost`). -/
def RowSpecSeg (X : Ctx) (inS outS : List F) (cons prod : List Msg) (sgin sgout : Nat × Nat) : Prop :=
  ∀ (E : Env) (s : St) (f : Frame) (tps tpl : Nat → Nat) (t pc S : Nat) (live : Msg → Prop),
    RelW X E s f tps tpl t pc S live sgin.1 sgin.2 →
    inS = stMsg (X.offOf E.k + pc) t S 0 E.sb E.cid → (∀ x ∈ cons, live x) →
    t + 1 < ZkFormal.Algebra.P → S + X.maxFee < ZkFormal.Algebra.P → X.g0 < 2 ^ 64 →
    ∃ k' pc' fee hb sb' cid',
      fee ≤ X.maxFee ∧ hb ≤ 2 ∧
      outS = stMsg (X.offOf k' + pc') (t + 1) (S + fee) hb sb' cid' ∧
      (X.R * (S + fee - sgin.1) ≤ sgin.2 →
        (hb = 0 → ∃ s', step X.cfg X.p s = .cont s' ∧
          Rel X s' (t + 1) k' pc' (S + fee) sb' cid' (stepLive live cons prod) sgout.1 sgout.2) ∧
        (hb = 1 → ∃ sN, step X.cfg X.p s = .fin sN ∧ sN.frames = [] ∧
          X.R * (S + fee - sgout.1) + sN.gas.g = sgout.2 ∧
          ∃ G : Msg → Prop, (∀ x, G x → x.space ≠ 0 ∧ x.space ≠ 16) ∧
          ∀ x, stepLive live cons prod x ↔ x ∈ stackView sN.stack tps ∨ x ∈ localView 16 f.locals tpl ∨ G x) ∧
        (hb = 2 → ∃ sN e, step X.cfg X.p s = .abort sN e ∧
          X.R * (S + fee - sgout.1) + sN.gas.g = sgout.2))

/-- **An ordinary row keeps the segment.** -/
theorem RowSpecSeg.ofSame {X : Ctx} {inS outS : List F} {cons prod : List Msg} {sg : Nat × Nat}
    (h : RowSpec2 X inS outS cons prod) : RowSpecSeg X inS outS cons prod sg sg := by
  intro E s f tps tpl t pc S live R hin hl h1 h2 h3
  obtain ⟨k', pc', fee, hb, sb', cid', hfl, hbl, hout, hsp⟩ :=
    h E s f tps tpl t pc S live sg.1 sg.2 R hin hl h1 h2 h3
  exact ⟨k', pc', fee, hb, sb', cid', hfl, hbl, hout, hsp⟩

/-- `RowFacts2`, with both segments explicit. -/
structure RowFactsSeg (X : Ctx) (inS outS : List F) (cons prod : List Msg) (sgin sgout : Nat × Nat) :
    Prop where
  spec : RowSpecSeg X inS outS cons prod sgin sgout
  halt0 : inS.getD 3 0 = 0
  tsOut : lvl outS = lvl inS + 1
  gasOut : ∃ fee, fee ≤ X.maxFee ∧ gasF outS = gasF inS + (fee : F)
  consT : ∀ x ∈ cons, ∃ n, n < 2 ^ 30 + 2 ^ 16 ∧ ((x.tp + 1 + n : Nat) : F) = lvl inS
  prodT : ∀ x ∈ prod, x.tp < ZkFormal.Algebra.P ∧ ((x.tp : Nat) : F) = lvl inS
  prodNd : prod.Nodup

/-- `RowFacts2` gives `RowFactsSeg` at any fixed segment. -/
theorem RowFacts2.toSeg {X : Ctx} {inS outS : List F} {cons prod : List Msg} {sg : Nat × Nat}
    (h : RowFacts2 X inS outS cons prod) : RowFactsSeg X inS outS cons prod sg sg :=
  ⟨RowSpecSeg.ofSame h.spec, h.halt0, h.tsOut, h.gasOut, h.consT, h.prodT, h.prodNd⟩


/-! ## The segmented execution theorem

`exec_of_rows`'s step (C) carries the segment in its induction hypothesis.  Requires:

* `segs : Nat → Nat × Nat` — the segment at each row, with `segs 0 = sg0` and
  `segs (k+1) = sgout` of row `k`;
* `hstepgas k` — the row's fee fits in the budget its segment carries,
  `R · (S_k + maxFee − (segs k).1) ≤ (segs k).2`, where `S_k` is the row's STATE gas field.

The last of these is where the segmentation costs something real: `exec_of_rows` derives it from
monotonicity of one global budget, which is false after a restart. -/

end WasmBase
