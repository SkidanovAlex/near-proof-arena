# pq-state-port: the classical NEAR state tables as the post-quantum base layer

Lane `lane/pq-state-port`, from `lane/pq-d1-envelope` @ 7cd1a7135.  The decision this lane
executes (`docs/logs/pq-final-layer-model-2026-10-17.md`, 2026-10-19 entry): **port the proven
state tables, keep direct-Wasm for execution, join the two later.**  The envelope study
(`research/near-compression/results/pq-d1-envelope/README.md`) established that this is possible:
same base field, same row conventions, single-bit multiplicities.

Labels: **[M]** measured here, **[K]** kernel-checked in Lean, **[E]** estimate.

## Status

| # | milestone | status | evidence |
|---|---|---|---|
| 1 | D0a: all 25 `nearAirV3` tables, no stand-in, honest fixtures, prove + verify + tamper | **done** | §1 |
| 2 | Lean bridge: generic SWIRL⇒`HoldsP`, `multBoundP < p`, composition with `extractV3` | **done** | §2 |
| 3 | D1: all 30 tables, no stand-in, prove + verify + tamper | **done** | §4 |
| 4 | Ed25519 / hint design options | **written, not implemented** | §5 |
| 5 | Wasm join | **not started** (out of scope here) | §6 |

## 1. D0a port [M]

`research/near-compression/native/pq-state-port/` is the driver.  It reads the Lean export of
`nearAirV3` (`np-air-v2`, 25 tables), the honest trace dump of a real D0a fixture, and the
classical public messages, and runs them through the unified SWIRL backend unchanged.

**What changed from the D1 envelope demo.**  The envelope demo proved 23 of 30 D1 tables and
supplied the bus traffic of the 7 it left out through `EXT`, an unconstrained stand-in.  That is
not acceptable for a port, so:

* the driver **fails** if any of the 25 tables is missing;
* the bus balance is checked over the 25 tables plus the cached public tape only — there is no
  `EXT` table in this lane at all;
* bus ids are shifted by `BUS_OFFSET = 128`, so the direct-Wasm family (ids 0–4) can never
  collide with a classical bus when the two are joined;
* every table's height is checked against its own `maxLog` (M4), and each is required to be a
  power of two with at least 4 rows (the NV minimum).

**Heights.**  The classical renders use fixed heights as an artefact of the FRI roll-in (2^22 for
the scheduler and receipt tables, `padLog22` rounding elsewhere; 99.6 % of the classical cells).
`HoldsP` accepts any `1 ≤ log ≤ maxLog`, so `statedump.rs` re-cuts every table at its natural
height, with a floor of 4 rows, and **re-checks every classical constraint on the re-cut table**.
The PQ driver then re-checks every constraint and every bus again, so the result is an honest
`HoldsP` trace by check, not by assumption.

**Parameters.**  The seg-v1 shape at `n_stack` chosen per fixture, message length 2^6 (M7, the
classical maximum is 34 fields + bus) and interaction budget 2^30 (M8; D0a's worst case is
2^29.55, and 2^30 < p keeps mod-p LogUp exact).  Target 268 bits.

### Results

| fixture | cells | proof | prove | verify | peak RSS | bits |
|---|---:|---:|---:|---:|---:|---:|
| `00-h10004-s3` | 1,262,608 | **1,023,328 B** | 3.9 s | 0.08 s | 148 MB | 268.2 |
| `00-h10023-s2` | 4,787,824 | 1,262,946 B | 19.5 s | 0.09 s | 1.2 GB | 268.2 |
| `00-h10035-s3` | 156,624,112 | 1,602,144 B | 398.8 s | 0.10 s | 24 GB | 268.2 |

* 8 threads, `nice -n 10`.  The big fixture is the memory case: 25 GB peak, close to the 24 GB
  cap (the 2^22 renders dominate until they are re-cut; `rcpt` alone is 2^18 rows).
* **Tamper 19/19 rejected** on `00-h10004-s3`: one mutated cell in each table family (trie ×7,
  SHA-256 ×2, scheduler ×5, receipts, size, srcp), a forged public message in TAPE, and a changed
  header public value.  Every case is rejected at prove/verify (no case reaches V_d).
* **V_d statement check: OK** on every fixture.  The TAPE root recomputed from the public
  messages equals the proof's cached commitment, and every AIR's public values equal the claim's.
* Debug constraint checker: OK.
* LogUp soundness 329.3 bits, proximity 326.2, query 268.2; total 268.2.

Reproduce: `AIR=<nearAirV3.json> research/near-compression/native/pq-state-port/run_demo.sh <out>
prove` (and `tamper`).  Logs are in `logs/`.  The `nearAirV3.json` used has sha256
`fa599b3b0c2dc786c295959ce92cfbbe73d74c4414b77979b436512a8ae3b452` (the `np-lean-export-v3`
export, identical to the one in `v3-d1-tables`).

### Envelope for the joined system [M]/[C]

| quantity | D0a (this lane) | DESIGN-BASE §3 envelope | verdict |
|---|---:|---:|---|
| AIRs | 25 + TAPE = 26 | ≤ 32 | fits |
| max degree | 6 (`qv`) | ≤ 8 | fits |
| constraints total | 6,442 | ≤ 2^14 per AIR | fits |
| opened columns incl. rotation | 5,196 | ≤ 1,024 | **5× over**; SHA alone 1,085 |
| max message length | 34 + bus | ≤ 16 pinned | soft; 2^6 costs ~0 |
| interactions worst case | 2^29.55 | ≤ 2^28 | soft; 2^30 < p |
| cells at the fixture | 1.26 M (`10004`) / 156.6 M (`10035`) | — | fixed-height renders dominate |

The two hard overruns are the ones the envelope study already named: opened columns (SHA-256 is
1,085 by itself) and, for the largest fixtures, the 2^22 scheduler/receipt renders.

## 2. Lean bridge [K]

`zk-formal/ZkFormal/PQ/StatePort/`:

* `Swirl.lean` — the statement: the classical AIR read as SWIRL AIRs, the LogUp interactions with
  the bus offset, TAPE as the public-message table, `SwirlRel` (what the PIOP enforces,
  assumption P5) and `VdChecks` (what V_d checks explicitly, including `TapeNet`).
* `Bridge.lean` — the bridge's ingredients, **proved with no `sorry`**:
  * `nat_inj_of_lt` — a field equality of two naturals below `p` is their equality.  This is the
    mod-p ⇒ ℕ step, and it is why `multBoundP < p` matters.
  * `bits_of_swirl` — the booleanity constraints inside `allConstraints` give `0/1` multiplicity
    bits on every row of every table (`SwirlRel.constr` ⇒ `HoldsP.bits`).
  * `eval_eq_of_agree` — agreement on public inputs below an expression's `pubBound` propagates
    through the whole expression, so `VdChecks.pvAgree` turns each `pv` evaluation into the
    classical `pub` one.
  * `countF_eq_multNat` — **the key identity**: the LogUp field count `Σₖ 2^k·bₖ` is the cast of
    the classical natural multiplicity `Interaction.multNat`, for `0/1` bits of length ≤ 25.  The
    proof bounds the partial sum by `2^25`, so the `Nat` cast is injective at every step.
  * `rowSum_eq_sub`, `signed_eq` — a row's signed field sum is its send count minus its receive
    count.
  * `tablesSum_eq_flat` — `tablesSum` unrolls to tables × rows × interactions.
  * `busCount_le_multBound` — every trace side count is `≤ Air.multBound` when heights respect
    the per-table `maxLog`; this is what makes the mod-p equality an ℕ equality.
* `Bounds.lean` — **P2**, the two `decide +kernel` facts `nearAirV3_multBoundP_lt` and
  `nearAirV3D1_multBoundP_lt` (both `< p = 2,013,265,921`), in the style of `nearAirV3_wf`.
* `test/AuditPQStatePort.lean` — the axiom footprint: `[propext]` for the kernel facts,
  `[propext, Classical.choice, Quot.sound]` for the list lemmas, **no `sorryAx`**.

### The bridge is complete [K]

`holdsP_of_swirl` is proved with **no `sorry`** and standard axioms only
(`propext`, `Classical.choice`, `Quot.sound`).  The aggregation chain:

| step | lemma |
|---|---|
| a row's signed field sum = its send count − receive count | `rowSum_eq_sub`, `rowSide_eq` |
| a table's rows × interactions = its `tableBusCount` | `tableSide_eq`, `tableSide_sub` |
| the whole AIR = send side − receive side | `tablesSum_eq_sides` |
| the AIR's `busCount` = Σ tables, with `pv`/`pub` agreement | `busCount_eq_tables`, `tableBusCount_congr` |
| LogUp + TAPE `netF` + `< p` ⇒ the classical balance | `balance_step`, `eq_of_field` |
| **SWIRL ⇒ `HoldsP`** | **`holdsP_of_swirl`** |

And the composition the lane exists for, in `D0a.lean`:

* `pq_d0a_good` — a PQ base proof of the 25 classical tables (SWIRL relation + `V_d` checks +
  `multBoundP < p`) gives `∃ k x, GoodV3 B0 cb k hint p x`, by feeding the bridge into the
  existing `extractV3`;
* `pq_d0a_rel` — and through `relD0a_of_good`, `∃ k x, RelD0a B0 cb (witnessOfV3 k x)`.

So the D0a soundness statement now holds for the PQ backend, with the **same hypotheses**
`extractV3` already used, plus SWIRL's relation.  The classical certificate, the spec and the
challenges are untouched.

The remaining hypotheses are exactly the documented ones:

* `SwirlRel` — SWIRL's own soundness (**P5**), shared with every PQ AIR and not formalised;
* `multBoundP nearAirV3 < p` — **proved** (`nearAirV3_multBoundP_lt`, a kernel fact);
* `mult.length ≤ 25` and `width ≥ 1` — the exported AIR's static `Table.wf`, which the verifier
  checks.

Still engineering, not proof: the vk ⇔ Lean-AIR identity (P3) and the TAPE commitment binding
(P4).  The Rust demo already interprets the Lean export, which is the P3 content at the value
level.

## 3. D1 [M]

The same driver, driven by a `d0a|d1` variant flag, runs the 30-table `nearAirV3D1` export with
the `ORDER_D1` table order.  Nothing else changes: no stand-in table, the 30 tables plus the
cached tape, the same bus offset, the same height re-cut.

Measured on `public-d1/d1/00-h10007-s3` (13 transactions, 11 ops) with 8 threads:

| cells | proof | prove | verify | peak RSS | bits |
|---:|---:|---:|---:|---:|---:|
| 4,474,016 | **1,289,274 B** | 20.3 s | 0.10 s | 1.2 GB | 268.2 |

* **Pre-check**: every classical constraint on every row of all 30 tables; every bus balances
  over the 30 tables + tape (16,932 distinct messages).  The envelope demo could only do 23
  tables with an `EXT` stand-in.
* **Tamper 23/23 rejected**: one active cell in each table family plus the forged public message
  and the changed header byte.
* **V_d statement check OK**: the TAPE root recomputed from the public messages matches the
  proof's cached commitment, and the public values are the claim's.
* LogUp 329.3 bits; total 268.2.
* The D1 fixture has no local receipt ids, so `rid` is all-zero padding; the tamper suite reports
  that explicitly instead of claiming a vacuous rejection (see below).

The 30 tables here are at natural heights, so the six fixed-2^22 renders (codec, scandist, proc,
mem, cmp, rcpt) collapse to their used rows — the same mechanism as D0a.  On this fixture that is
4.5 M cells rather than the 2.5 G the fixed renders would need.

**One honest note on `rid`.**  `rid`'s interactions (`PRID` on bus 69, `RIDS` on bus 8) carry
multiplicity `c0`, and on a fixture with no local receipt ids every `c0` is `0`.  A mutation of
the payload column `c8` on such a row is then *legitimately* accepted: the interaction sends
nothing, so nothing constrains the payload.  That is the AIR as designed, not a port bug.  The
tamper suite now mutates a nonzero row and reports an all-zero table as skipped, so it cannot
silently pass on an inert table.

## 4. Ed25519 and the hint (design only, per the brief)

The classical D1 verifier receives a hint (raw transactions, new transactions, op bits, refunds)
and runs `prepD1` natively: SHA-512 and Ed25519 verification, about 15 s at 4,096 transactions.
That is incompatible with a succinct final verifier.  Options, with cost:

| option | what | cost [E] | verdict |
|---|---|---|---|
| **A. in-circuit Ed25519** | a `sigV3` chip: Ed25519 + SHA-512 AIRs, the planned V3-D3A item | weeks | the sound choice; also the largest circuit |
| **B. separate proof** | one recursion layer whose statement is "these signatures verify over these transactions", proved once per chunk | 5–10 days after A's AIRs exist; otherwise unbounded | middle ground; still needs the signature AIR somewhere |
| **C. statement design** | V_d takes the transactions from public chain data (chunk body, bound by the header's tx root) and keeps the native prep outside the proof | 3–5 days of statement work, then the verifier is not light (it re-runs Ed25519) | moves the cost to the verifier, which the ≤ 300 KB target and a light V_d rule out |

Recommendation: **A** if in-circuit signature verification is in scope for the next stage;
otherwise **B**, with the same AIRs.  Do not pick C for the succinct target.

## 5. Wasm join (not started)

The envelope study's plan still applies: one base proof, statement `ctx ‖ enc S_0 ‖ enc S_S`;
`rcptD1` (or a new `call` table) sends the CALL message that the Wasm boundary receives; Wasm
storage host calls answer on the existing trie buses; `BUS_OFFSET = 128` in this lane is the
reserved split.  The Lean side needs the D3α-style `runCall` fold over the D1 extraction and
`wasm_base_sound`.  Cost [E] 15–25 agent-days.

## 6. Files

* `research/near-compression/native/pq-state-port/` — the driver (`src/main.rs` with the `d0a|d1` variant, `src/air.rs`,
  `src/config.rs`), `setup.sh`, `run_demo.sh`.
* `examples/np-udr-stark-v2/source/examples/statedump.rs` — the honest trace dump with the
  natural-height re-cut (a cargo example, so the shipped package is unchanged).
* `zk-formal/ZkFormal/PQ/StatePort/{Swirl,Bridge,Bounds,D0a}.lean`,
  `zk-formal/test/AuditPQStatePort.lean`.
* `logs/` — the prove and tamper logs and the per-table height maps.

Nothing pinned was touched: `make pin-check` passes, and the spec, challenges, `nearAirV3` and the
D0a certificate are unchanged.
