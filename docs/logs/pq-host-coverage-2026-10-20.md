# D3α host-function coverage: four parallel lanes and the merge they need

Date: 2026-10-20. Companion to `docs/HANDOVER.md` and `results/pq-host-*/`.

## The measured surface

`spec/lean/v3/NearSpecV3/Wasm/HostSigs.lean` lists **89** importable host functions. D3α excludes
15 curve functions (`alt_bn128_*`, `bls12381_*`, `ecrecover`, `ed25519_verify`, `p256_verify`) and
10 further out-of-domain ones (`oodHosts` in `D3/FunctionCall.lean`: state-init, global-contract and
gas-key families). **D3α target = 64 functions.**

Split by what each actually needs:

| family | count | needs |
|---|---:|---|
| context / state-read | 19 | no AIR: a context read returned on `HOSTR` |
| promise / receipt | 23 | **a receipt-construction AIR that does not exist** |
| storage | 8 | the ContractData walk (built) + iteration (new table) |
| log / panic | 5 | `HOSTB` payload bytes |
| register / return | 5 | the space-6 register space |
| hash (`sha256`, `keccak256/512`, `ripemd160`) | 4 | in-AIR hash chips; **none exist on the PQ stack** |

**The critical structural fact:** the Wasm-side HOST chip is *generic* — it never names a function.
It takes `(hid, np, ar)` from a fixed table and moves arguments/results through `HOSTQ`/`HOSTR` to
an in-trace oracle. So "covering a host function" is never writing a chip; it is (a) the `hostFns`
entry, (b) the state-side response, (c) a KAT. The exception is the hash family, which needs real
arithmetic AIRs that do not exist yet.

**The shared prerequisite:** the chip supported `np ≤ 2`, but real signatures reach `np = 9`. 28 of
the 64 need `np > 2`. Every lane depends on that widening, so it is a single shared change.

## What the four lanes delivered (all build standalone, all pushed)

| lane | commit | result |
|---|---|---|
| `pq-host-promise` | `5e03bf587` | **HOST chip widened to `np ≤ 9`**: argument columns 2→9, width 37→93, HOSTQ 8→22 fields (one wide message, not one per argument — fits the NV 128-field envelope). All HOST lemmas re-proved, none weakened; KAT **79/79** (+2 np=3/np=9 programs); two latent Rust bugs fixed (argument order reversed vs spec `popArgs`; producer time). Plus the 23-entry promise table and a priced design: no receipt AIR exists, ≈7–12 lane-weeks. |
| `pq-host-ctx` | `0594bba49` | 19 context/state-read functions; **no AIR needed**; arity agreement with the spec is a *kernel check* (`hostFns_arity_agrees`). KAT **83/83**. `gas` and `validator_stake` blocked (i32 tag / np=3 at the time). |
| `pq-host-logreg` | `fa1c478c2` | 8 of 10: log/panic + `input`/`read_register`/`register_len`/`value_return`. New `RegisterSpace.lean` + `REG` chip wired to `HOSTB`; `wasmBaseHostAir` byte-identical. KAT **81/81**; REG tamper 9/9. `abort`/`write_register` blocked on arity. |
| `pq-host-storage2` | `d35fc14b1` | `storage_read`/`has_key`/`remove`/`usage` **proved**; `storage_iter_*` **proved out of domain** (`iter_*_aborts`). `RealStoreMatchesTables` progressed to `_find_log`. |

## The merge conflict, precisely

Three lanes edited `HostChip.lean` and chose **three different id schemes**:

* `pq-host-promise` defines `hostFnsBase ++ promiseFns`, promise at **ids 8–30**, and the widened chip;
* `pq-host-ctx` replaces `hostFns` wholesale, context at **ids 8–21**;
* `pq-host-logreg` appends at **ids 8–15** (and puts `abort`/`write_register` in `hostFnsWide`).

Only ids `0..7` are actually pinned (they are what a cached `HOSTT` contains). Nothing in the proofs
indexes a host id numerically, so a single canonical table resolves all three. I generated one:

* ids `0..7` unchanged;
* ids `8..30` promise (as `pq-host-promise` wrote them);
* ids `31..63` everything else, sorted, arities taken from `hostSigs`.

**72 entries, max `np` 9.** That table is `tools/host-fns/canonical.txt` in this change.

Two further conflicts appeared and were **not** resolved:

1. `WasmBase/Main/HostChipBits.lean` (merged into main by another agent as `cb855f896`) hardcodes
   HOST interaction positions `22/25/28`, which the 9-argument widening invalidated. `Host.inters`
   now has 78 interactions and the CH positions are `recvBase + 2j` with `recvBase = 6 + 4 + 4 + 4·nArgs`.
2. The three Rust files (`tracegen.rs`, `main.rs`, `gen.py`, `refinterp.py`) each got independent
   host-program additions.

The merge branch was abandoned rather than promoted: accumulating unverified edits to another
agent's proof file is how a soundness argument gets silently weakened. Main is unchanged.

## What the next pass must do, in order

1. **Land `pq-host-promise` alone** (it is self-contained and carries the widened chip). Verify KAT
   79/79 and `pin-check` on main.
2. **Re-derive `HostChipBits.lean`** against `Host.recvBase`, proving the position formula rather
   than hardcoding it. This is the one file where the widening breaks a *proof*, not just a layout.
3. **Then** merge ctx/logreg/storage2 one at a time, each against the canonical `hostFns`, re-running
   KAT + `pin-check` per merge.
4. Only then attempt the receipt AIR (the largest remaining item) and the hash chips.
