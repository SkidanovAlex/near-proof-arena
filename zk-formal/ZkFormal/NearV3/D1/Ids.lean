import ZkFormal.NearV3.Rcpt.Ids

/-!
# `ZkFormal.NearV3.D1.Ids` — buses, walk ids and public offsets of the D1 tables

Lane `v3-d1-tables` (docs/zk-formal/V3-D1-DESIGN.md §2.2, D1-N; log
docs/logs/v3-d1-tables-2026-10.md).  Definitions only (verifier-model import rule,
docs/logs/v3-model-split-2026-10.md).  Nothing here changes a bus or offset of `nearAirV3`:
the D1 buses are new numbers (`64 … 69`, unused by `nearAirV3`, below `nearBuses = 77`), the
D1 public header extension lies after the segment metadata (the nine D0a segment descriptors
keep their offsets `202 + 8·i`).

## New buses

| # | bus | message | producers → consumers |
|---|---|---|---|
| 64 | `AKMEM` | `(vid, t, i, nonce_i, fa)` | `akmV3` (initial value at `t = 0`, final at `tlast`) ↔ `txV3` (read at `tprev`, write at `op + 1`), lanes `i < 8` |
| 65 | `TXP` | `(j, kind, strict, ok, tov, stage, cok, xN, xB, xC)` | public (one record per op lane, `j = 16·op + lane`) → `txV3` |
| 66 | `SIG` | `(op, valid)` | public (`sizeOk ∧ Ed25519.verify`, native under D1-N; a `sigV3` chip under D1-S) → `txV3` |
| 67 | `PKEY` | `(w₀, w₁, w₂, t, sym, last)` | public (the transaction walks' key nibbles) → `kibV3` |
| 68 | `PLEAF` | `(pos, d[32])` | public (transaction / local-receipt outcome leaves) → `plfV3` |
| 69 | `PRID` | `(j, byte)` | public (local receipt ids, `j = 32·l + i`) → `ridV3` |

Reused buses: `KEYNIB` (5, `kibV3` → `walkV3`), `FINAL` (6, `walkV3` → `txV3`), `MEM` (7,
`acctV3` ↔ `txV3`), `MPOS` (9) / `DIGEST` (1) (`plfV3` → `mrkV3`), `RIDS` (8, `ridV3` →
`sortV3`), `VBYTES` (21, `akmV3` → `valV3`), `VSLOT` (3) and `BYTES` (0, `VPOST`) (`akmV3` →
`nodeV3` / SHA), `AKC` (27, `akmV3` ↔ `rcptV3` refunds).

## Walk ids, receipt-id slots, message kinds

* transaction walks: `W_TX + 2·op` (signer account), `W_TX + 2·op + 1` (access key), with
  `W_TX = 2^20` (above `W_AK + r < 16384` and `W_QV + τ + 64·slot`);
* local receipt ids on `RIDS`: `W_LOC + l` (`rcptV3` uses `r < 4481`);
* public leaf message ids `mid K_PLF pos` (`K_PLF = 15`: no SHA job has kind 15, so the ids
  never meet a hashed message on `DIGEST`).

## Public header extension (after the 15 segment descriptors)

`E0 = 202 + 8·15 = 322`: `u32 M0` (outcomes before the incoming receipts: transaction outcomes
and local receipts), `u32 T0` (number of `txV3` ops = MEM time offset of `rcptV3`), `u32 O0`
(body offset of the incoming receipts' refunds), `u128 TOK0` (tokens burnt by transactions and
local receipts).  `numPub = 350`.
-/

namespace ZkFormal.NearV3.D1

open ZkFormal.Near

/-! ## Buses -/

def B_AKMEM : Nat := 64
def B_TXP : Nat := 65
def B_SIG : Nat := 66
def B_PKEY : Nat := 67
def B_PLEAF : Nat := 68
def B_PRID : Nat := 69

/-! ## Ids -/

/-- Base of the transaction walk ids (`W_TX + 2·op`, `W_TX + 2·op + 1`). -/
def W_TX : Nat := 1048576
/-- Base of the local receipt slots on `RIDS`. -/
def W_LOC : Nat := 1048576
/-- Message kind of the public outcome leaves (no SHA job uses it). -/
def K_PLF : Nat := 15

/-! ## Lanes -/

/-- Rows per `txV3` op (byte lanes, least significant first). -/
def LANES : Nat := 16

/-! ## Public header extension -/

/-- Number of public segments of `nearAirV3D1` (9 of D0a, 6 new). -/
def NSEG : Nat := 15
/-- Start of the D1 header extension. -/
def E0 : Nat := 202 + 8 * NSEG
/-- `u32 M0`: outcome leaves before the incoming receipts. -/
def E_M0 : Nat := E0
/-- `u32 T0`: `txV3` ops (MEM time offset of the incoming receipts). -/
def E_T0 : Nat := E0 + 4
/-- `u32 O0`: body offset of the incoming receipts' refunds. -/
def E_O0 : Nat := E0 + 8
/-- `u128 TOK0`: tokens burnt before the incoming receipts. -/
def E_TOK0 : Nat := E0 + 12
/-- Length of the extension. -/
def EXT_LEN : Nat := 28
/-- `numPub` of `nearAirV3D1`. -/
def numPubD1 : Nat := E0 + EXT_LEN

end ZkFormal.NearV3.D1
