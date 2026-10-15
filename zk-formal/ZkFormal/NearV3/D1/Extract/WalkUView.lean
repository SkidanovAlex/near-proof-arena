import ZkFormal.NearV3.Extract.WalkView
import ZkFormal.NearV3.D1.Tables.WalkUDefs

/-!
# `ZkFormal.NearV3.D1.Extract.WalkUView` — the `walkU` view statement (table 30)

Lane `v3-d1-a7b` (plan §5 R-5 → (B)).  `walkU` is `walkV3` for the unread-key walks, with a fifth
row mode and no `FINAL`.  Its records are D0a's `WalkR` / `WStep3` (`Extract/WalkView.lean`):
* `mode` — `0` step, `1` absent by key, `2` absent at a branch, `3` drain (as `walkV3`), and
  `4` **stub** (`mT`): the walk's lookup position `(N, I) = (e[0], e[1])` is a stub window of
  `nodeD1`, and `e[2]` is its symbol slot `z` (`= sym`, or `SYM_WILD`);
* for a stub row `e[3 … 5]` are the row's (free) edge columns.

Traffic (`walkUTraffic`): on `EDGE` and `BMAP` exactly D0a's `walkSends3` / `walkRecvs3` of the same
records (a stub row is neither an edge row nor a `BMAP` row), so every D0a lemma about the walks'
`EDGE` / `BMAP` messages applies to `walkU`'s records unchanged; on `SEDGE` the stub rows'
`[N, I, z, u]` (received) and `[N, I, z, u + 1]` (sent); on `UKEYNIB` the key symbols, in D0a's
`KEYNIB` shape.  No `FINAL`, no `KEYNIB`.
-/

namespace ZkFormal.NearV3.D1

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3

/-- Facts about one `walkU` row (D0a's `StepOk`, with the stub mode). -/
structure StepOkU (st : WStep3) (isLast : Bool) : Prop where
  mode : st.mode ≤ 4
  elen : st.e.length = 6
  stepE : st.mode = 0 → st.e.getD 2 0 = st.sym ∧
    (isLast = false → st.e.getD 5 0 = EK_DOWN ∨ st.e.getD 5 0 = EK_KEY) ∧
    (isLast = true → st.e.getD 5 0 = EK_VAL)
  absK : st.mode = 1 → (st.e.getD 5 0 = EK_KEY ∨ st.e.getD 5 0 = EK_LEND) ∧ st.e.getD 2 0 ≠ st.sym
  absB : st.mode = 2 → st.e.getD 1 0 = 0 ∧ st.bm < 2 ^ 16 ∧ st.hv ≤ 1 ∧
    (isLast = true → st.hv = 0) ∧
    (isLast = false → st.sym < 16 ∧ st.bm / 2 ^ st.sym % 2 = 0)
  /-- stub: the symbol slot is the row's symbol, or the wildcard -/
  stub : st.mode = 4 → st.e.getD 2 0 = st.sym ∨ st.e.getD 2 0 = SYM_WILD
  lastEnd : isLast = true → st.sym = SYM_END

/-- A non-stub row of `walkU` satisfies D0a's `StepOk`. -/
theorem StepOkU.stepOk {st : WStep3} {isLast : Bool} (h : StepOkU st isLast) (h4 : st.mode ≠ 4) :
    StepOk st isLast :=
  ⟨by have := h.mode; omega, h.elen, h.stepE, h.absK, h.absB, h.lastEnd⟩

structure WalkUWf (ws : List WalkR) : Prop where
  len : ∀ wv ∈ ws, 2 ≤ wv.steps.length
  canon : ∀ wv ∈ ws, wv.w < P ∧ wv.tau < P ∧ ∀ st ∈ wv.steps,
    st.sym < P ∧ st.u < P ∧ st.ub < P ∧ ∀ x ∈ st.e, x < P
  rows : ∀ wv ∈ ws, ∀ i (hi : i < wv.steps.length), StepOkU wv.steps[i] (i + 1 == wv.steps.length)
  /-- the first row is the `START` step from the main instance's head (`τ = 0`) -/
  start : ∀ wv ∈ ws, (wv.step 0).mode = 0 ∧ (wv.step 0).sym = SYM_START ∧
    (wv.step 0).e.getD 1 0 = wv.tau ∧ wv.tau = 0
  /-- consecutive rows: after a step a lookup (no drain) at the step's target; after an absent
  or stub terminal, or a drain, a drain -/
  chain : ∀ wv ∈ ws, ∀ i, i + 1 < wv.steps.length →
    ((wv.step i).mode = 0 → (wv.step (i + 1)).e.take 2 = ((wv.step i).e.drop 3).take 2 ∧
      (wv.step (i + 1)).mode ≠ 3) ∧
    ((wv.step i).mode ≠ 0 → (wv.step (i + 1)).mode = 3)
  nrows : (ws.flatMap (·.steps)).length ≤ 2 ^ 22

/-- The `SEDGE` message of a stub row with use count `x`. -/
def _root_.ZkFormal.NearV3.WStep3.stubMsg (st : WStep3) (x : Nat) : Msg := [st.e.getD 0 0, st.e.getD 1 0, st.e.getD 2 0, x]

def walkUSends (ws : List WalkR) (b : Nat) : List Msg :=
  if b = B_EDGE ∨ b = ZkFormal.NearV3.B_BMAP then walkSends3 ws b
  else if b = B_SEDGE then
    ws.flatMap fun wv => (wv.steps.filter fun st => st.mode = 4).map fun st => st.stubMsg (st.u + 1)
  else []

def walkURecvs (ws : List WalkR) (b : Nat) : List Msg :=
  if b = B_EDGE ∨ b = ZkFormal.NearV3.B_BMAP then walkRecvs3 ws b
  else if b = B_SEDGE then
    ws.flatMap fun wv => (wv.steps.filter fun st => st.mode = 4).map fun st => st.stubMsg st.u
  else if b = B_UKEYNIB then walkRecvs3 ws B_KEYNIB
  else []

def walkUTraffic (ws : List WalkR) : Traffic := ⟨walkUSends ws, walkURecvs ws⟩

/-- **The `walkU` view statement** (any table index `t`). -/
def WalkUViewStmt : Prop :=
  ∀ (tr : Trace Fp) (pub : List Fp) (t : Nat), TableLocal WalkU.table tr t pub →
    ∃ ws, WalkUWf ws ∧ TableTraffic WalkU.interactions tr t pub (walkUTraffic ws)

end ZkFormal.NearV3.D1
