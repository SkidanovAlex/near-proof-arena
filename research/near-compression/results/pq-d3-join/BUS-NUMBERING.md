# HOST bus numbering: a live three-way conflict

Found 2026-10-20 while reconciling the three lanes that each picked HOST bus ids.

## The numbers

| lane | HOSTQ | HOSTR | HOSTB | HOSTT |
|---|---:|---:|---:|---:|
| `lane/pq-host-chip` (`WasmBase/HostChip.lean`) | 7 | 8 | — (not built) | 9 |
| `lane/pq-state-port` (`JOIN-INTERFACE.md`) | 200 | 201 | 202 | — |
| `lane/pq-d3-join` (`PQ/Join/Statement.lean`) | 208 | 209 | 210 | — |

## Why 200/201/202 is wrong

`JOIN-INTERFACE.md` says the shifted classical range is `128–199`. That is false.
`nearBuses = 77` covers buses `0..76`, and the real `nearAirV3D1` export uses up to
**bus 75** (buses 72, 73, 74, 75 all appear). After the port's `+128` the occupied range is
**128–203**, so:

* `HOSTQ = 200` collides with classical bus 72;
* `HOSTR = 201` collides with classical bus 73;
* `HOSTB = 202` collides with classical bus 74.

A colliding bus merges two unrelated multiset constraints; that is a soundness bug, not a
performance issue. This must be fixed before either join lane merges.

## Why 7/8/9 is *currently* safe but fragile

`HostChip.lean` uses 7/8/9 inside the Wasm family, which uses 0–6. Those ids are free, and the
state family starts at 128 after the shift, so they do not collide today. But the allocation
silently depends on the state side never shifting below 128, which is exactly the assumption that
just broke. It also cannot express `HOSTB`, which the design requires.

## Recommendation

Use **208 / 209 / 210** for `HOSTQ` / `HOSTR` / `HOSTB`, i.e. the `pq-d3-join` allocation:

* unambiguously above every shifted classical bus (max 203) and every Wasm bus (max 9);
* leaves 10–127 and 204–207 free for future Wasm and state additions;
* matches the number already written in `PQ/Join/Statement.lean`.

`HOSTT` is a *Wasm-internal* cached table, not a cross-proof bus, so it may stay at 9 — but then
it must be documented as Wasm-internal so that no state-side table claims 9.

## Actions

1. `lane/pq-host-chip`: renumber `busHostQ/R` to 208/209 (mechanical; no constraint changes).
2. `lane/pq-state-port`: correct `JOIN-INTERFACE.md` to `128–203` and 208/209/210.
3. `lane/pq-d3-join`: no change; this doc records why it is the reference.
