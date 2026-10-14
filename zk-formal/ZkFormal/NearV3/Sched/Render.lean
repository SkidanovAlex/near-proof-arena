import ZkFormal.NearV3.Sched.Model
import ZkFormal.NearV3.Sched.Ids
import ZkFormal.NearV3.Sched.Spec.DistDefs
import ZkFormal.NearV3.Sched.Spec.CanonDup
import ZkFormal.NearV3.Sched.RenderDefs

/-!
# ZkFormal.NearV3.Sched.Render — the scheduler's public records (claim-only)

The verifier renders, from the prepared statement's scheduler data (one `InstPub` per applied
block τ, all with the same layout), the byte records that the public segments put on the
scheduler's buses. Every record is a list of bytes (`< 256`). Field values `< 2^24` are written
as three little-endian bytes (`b3`), indices `< 2^16` as two (`b2`).

| bus | records |
|---|---|
| `SPUBB` | key limbs `(τ, 3, k, lo, hi, 0, 0)` (16 per τ); `sha256(all_shards)` `(τ, 2, j, byte, 0, 0, 0)` (32 per τ); forwarding demands of instance 0 `(0, 4, l_lo, l_hi, t₀, t₁, t₂)` (every link) |
| `SPAR` | one shape `(τ, tag, f₀ … f₈)`: codec `(τ, 0, n, N₀, N₁, base₀..₂, fair₀..₂)`; scan params `(τ, 1, base₀..₂, D₀..₂, n, 0, 0)` (τ with requests); raw request `(τ, 2, bm₀ … bm₄, cid_lo, cid_hi, s, r)` per converted request; shard `(τ, 3, side, shard, links, B₀ (3 bytes), n, 0, 0)` per shard and side; link `(τ, 4, 0, 0, 0, 0, 0, 0, l_lo, l_hi, allowed)` per link |
| `SDL` | sends `(0, k_lo, k_hi, o, id byte)`, receives `(K + 1, …)` for every record `k` and `o < 16` |
-/

namespace ZkFormal.NearV3.Sched

open NearSpecV3 NearSpecV3.Scheduler

end ZkFormal.NearV3.Sched
