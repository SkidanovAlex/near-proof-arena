import ZkFormal.NearV3.D1.NearAirD1Defs
import ZkFormal.NearV3.D1.PrepD1
import ZkFormal.Udr.Rbr
import ZkFormal.Algebra.Fp
import ZkFormal.V2.VerifierDefs

/-!
# `ZkFormal.NearV3.D1.PrepD1Lemmas` — the phase-2 obligations of the D1 tier, stated

Lane `v3-d1-tables` (phase 1).  Statements only, as `Prop`-valued definitions (no proofs, no
`sorry`): what the D1a certificate needs about `prepD1` and `nearAirV3D1`, in the form of the
D0a obligations (`Assembly/NearAdmission.lean`: `ExtractV3StmtAt`, `RenderV3Stmt`).  Phase 2
(V3-D1-DESIGN §7: lanes D `v3-d1-factor`, E `v3-d1-views`, G `v3-d1-render`) proves them.

* `ExtractD1Stmt` — soundness: an accepted D1 prepared statement and a satisfying trace give a
  D1a witness (`RelD1a B0`).  Splits as in D0a into per-table views (`TxV3`/`AkmV3`/relays/
  `rcptV3D1`, the 23 unchanged tables' views reused), a link `GoodD1`, and a factor theorem
  `FactorSoundD1 : prepD1 cb h = .ok p → GoodD1 … → ∃ w, RelD1a B0 cb w`.
* `CompleteD1Stmt` — completeness: every `RelD1a B0` pair has a hint (`hintOfD1`), an accepted
  prepared statement and an honest trace with an admissible header.
* `PrepTxNativeStmt` — the native/AIR split of `processTxs` is exact: with the honest verdict
  bits, `prepTxs` reproduces `processTxs`'s outcome leaves, local / forwarded receipts, gas and
  tokens (steps 1–4 are the same spec functions, steps 5–8 are determined by `(stage, ok)` and
  the AIR-checked state reads).
* `PrepLocalNativeStmt` — a local receipt whose credit succeeds has `localApply`'s outcome
  leaf, refunds and burnt tokens (`TransferV1.applyReceipt` with the trie part factored out).
* `TxVerdictStmt` — the `txV3` verdict: `verifyAndCharge a k t c height ≠ none` iff
  `perm = fullAccess ∧ nonceOk ∧ amount ≥ C ∧ stake ok` (function-call and gas keys always
  fail, so the allowance is never needed).
* (not stated here: it needs a segment-trace vocabulary from the views lane) `akmV3`'s
  language: a single-segment trace with bytes `b` satisfies `AkmV3.table` iff
  `decodeAccessKey b ≠ none`, and then `fa = (perm = fullAccess)` and the `AKMEM` nonce lanes
  are the decoded nonce's bytes.
-/

namespace ZkFormal.NearV3.D1

open NearSpec NearSpec.TransferV1 NearSpecV3 ZkFormal.Air ZkFormal.V2 ZkFormal.Algebra

/-- Soundness obligation (at the challenge's A7 bound `B0`). -/
def ExtractD1Stmt : Prop :=
  ∀ (cb : Bytes) (h : HintD1) (p : Public.PrepD1) (tr : Trace Fp),
    prepD1 cb h = .ok p →
    (Public.preparedBytesD1 p 0).length < ZkFormal.Algebra.P →
    HoldsP nearAirV3D1 (ZkFormal.Udr.pubOf Fp (Public.preparedBytesD1 p 0)) tr →
    ∃ w, RelD1a B0 cb w

/-- Completeness obligation. -/
def CompleteD1Stmt : Prop :=
  ∀ (cb w : Bytes), checkD1a B0 cb w = .ok () →
    ∃ (h : HintD1) (p : Public.PrepD1) (tr : Trace Fp),
      prepD1 cb h = .ok p ∧
      HoldsP nearAirV3D1 (ZkFormal.Udr.pubOf Fp (Public.preparedBytesD1 p 0)) tr ∧
      h.encode.length < 256 ^ 4

/-- The verdict `txV3` recomputes is `verifyAndCharge`'s success. -/
def TxVerdictStmt : Prop :=
  ∀ (a : Account) (k : AccessKeyV) (t : Tx) (c : TxCost) (height : Nat),
    (verifyAndCharge a k t c height).isSome =
      (decide (k.perm = .fullAccess) &&
       (if t.strict then decide (t.nonce = k.nonce + 1) else decide (t.nonce > k.nonce)) &&
       decide (t.nonce < min (height * TxParams.nonceRangeMultiplier) (Params.two64 - 1)) &&
       decide (c.totalCost ≤ a.amount) &&
       decide (a.amount - c.totalCost + a.locked < Params.two128) &&
       (decide (Params.storageAmountPerByte * a.storageUsage ≤ a.amount - c.totalCost + a.locked) ||
        decide (a.storageUsage ≤ Params.zeroBalanceStorageLimit)))

/-- A local receipt's native part (`localApply`) is `applyReceipt`'s on success. -/
def PrepLocalNativeStmt : Prop :=
  ∀ (ctx : ApplyCtx) (st st' : Acc) (r : Receipt),
    applyReceipt ⟨ctx.height, ctx.gasPrice⟩ st r = some st' →
    ∃ leaf rf burnt, localApply ctx r = some (leaf, rf, burnt) ∧
      st'.refunds = st.refunds ++ rf ∧ st'.tokensBurnt = st.tokensBurnt + burnt ∧
      st'.gasBurnt = st.gasBurnt + Params.G

/-- The native transaction steps with the honest verdict bits reproduce `processTxs`. -/
def PrepTxNativeStmt : Prop :=
  ∀ (ctx : ApplyCtx) (st0 : TxSt) (txs : List (Tx × Bool)) (st : TxSt),
    processTxs ctx st0 txs = .ok st → st0.seen = [] → st0.outs = [] →
    st0.locals = [] → st0.fwd = [] → st0.gas = 0 → st0.tokens = 0 →
    ∃ bits acc, prepTxs ctx { bits } txs = .ok acc ∧ acc.bits = [] ∧
      acc.leaves = st.outs.map OutD1.leaf ∧ acc.locals = st.locals ∧ acc.fwd = st.fwd ∧
      acc.gas = st.gas ∧ acc.tokens = st.tokens

end ZkFormal.NearV3.D1
