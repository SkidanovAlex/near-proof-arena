# Ed25519 verification in-circuit: operation census and cost model

Lane `lane/pq-ed25519-air` @ `34a427692`. Sources read: `spec/lean/v3/NearSpecV3/Ed25519.lean`
(318 lines) and `spec/lean/v3/NearSpecV3/SHA512.lean` (178 lines). Every count below is
derived from those definitions by `census.py`, an **executable transcription that preserves
the Lean recursion structure** and is validated against the oracle fixtures.

Validation of the transcription (`logs/census-run.txt`):

```
fixtures: 7265 checked, 0 mismatches
accepting fixtures: 3543
executed F.mul: min 7850 avg 9414.8 max 9830
executed add/sub: min 4962 avg 6099.7 max 6402
executed Point.add: min 620 avg 762.2 max 800
```

It reproduces **all 7,265** `verify` verdicts in `oracle/fixtures/v3/ed25519/*.jsonl`
(cctv, djb_sign_input, edge, near_signed, rfc8032, speccheck, wycheproof), and its closed-form
counts match the instrumented execution on all 3,543 accepting fixtures (0 structural
mismatches). This is testing, not proof: the census is only as faithful as the transcription
and the Lean source it mirrors.

---

## Part 1 — Operation census

### 1.1 The functions and where the work happens

| Step | Lean function | Source lines | What it does |
|---|---|---|---|
| point decompression | `decode` | `Ed25519.lean:176-187` | `y²−1`, `d·y²+1`, then `sqrtRatio`, then `x·y` |
| square root | `F.sqrtRatio` | `Ed25519.lean:108-115` | `(u v³)(u v⁷)^((p−5)/8)`, branch on `±u`, `abs` |
| inversion | `F.inv` | `Ed25519.lean:97` | `a^(p−2)` = `powAux 256 a (p−2)` |
| field exponentiation | `F.powAux` / `F.pow` | `Ed25519.lean:87-94` | MSB-first, **fixed** 256 levels |
| complete addition | `Point.add` | `Ed25519.lean:136-145` | 11 mul, 8 add/sub per call |
| scalar multiplication | `smulAux` / `smul` | `Ed25519.lean:151-159` | MSB-first, **fixed** 256 levels |
| verification equation | `verifyWith` | `Ed25519.lean:207-213` | `Rb = encode(smul s B + smul k (−A))` |
| hash-to-scalar | `sha512` | `SHA512.lean:170-172` | `pillow`-free FIPS 180-4, `blocks`/`compress` |
| compression | `SHA512.compress` | `SHA512.lean:120-124` | 80 rounds, 128-byte block |
| point negation | `Point.neg` | `Ed25519.lean:148` | 2 `F.neg` |

Only **one** SHA-512 invocation is inside `verify`: `k = SHA-512(R ‖ A ‖ M) mod ℓ`
(`Ed25519.lean:212`). The second SHA-512 in a D1 transaction is the transaction hash
`sha256(borsh(Transaction))` (`TxD1.lean:77`), i.e. **SHA-256**, not SHA-512; it is outside
`Ed25519.verify` and outside this census. The task brief said "two SHA-512 invocations" —
there is exactly one in `verify`; the other hash in the D1 path is SHA-256 and is a different
chip (16× fewer rounds, 32-bit words).

### 1.2 Per-call costs read off the source

| Operation | Count per call | Source reference |
|---|---:|---|
| `Point.add` (complete, a = −1) | 11 `F.mul`, 8 `F.add`/`F.sub` | `Ed25519.lean:136-145` (`a`,`b`,`c`=3,`dd`=2, outputs 4) |
| `F.powAux 256 b e` | 256 squarings + `popcount(e)` extra muls | `Ed25519.lean:87-91` |
| `F.pow b (p−2)` | **509** muls | `popcount(p−2) = 253` |
| `F.pow b ((p−5)/8)` | **507** muls | `popcount((p−5)/8) = 251`; `(p−5)/8 = 2^252−3` |
| `F.sqrtRatio` | 516 muls (+1 if the `√−1` branch is taken) | `Ed25519.lean:109-114`; `v3`=2, `v7`=2, `u·v7`=1, pow=507, `(u v3)·…`=1, `v·r²`=2, `abs` 0/1 |
| `decode` | 519 or 520 muls, 1 sub, 1 add, 2 neg | `Ed25519.lean:180-187` |
| `smulAux 256 n P` | 256 `Point.add` doublings + `popcount(n)` more | `Ed25519.lean:151-156`; note it doubles **from `Point.zero`**, so all 256 levels run |
| `encode` | 511 muls (`inv` 509 + 2) | `Ed25519.lean:162-170` |
| `Point.neg` applied to `A` | 2 `F.neg` | `Ed25519.lean:148` |

### 1.3 Per-signature totals

Let `ps = popcount(s)`, `pk = popcount(k)`. `s < ℓ` (`Ed25519.lean:210`) and `k < ℓ`, and
`ℓ` has 253 bits, so `ps, pk ≤ 252`.

```
Point.add calls        = 512 + ps + pk + 1        (two smuls + the final add in verifyWith)
F.mul                  = 11·(512+ps+pk+1) + 519..520 + 511
F.add/F.sub            =  8·(512+ps+pk+1) + 2
F.neg                  =  2 (A.neg) + 1 (neg u) + 0..2 (abs, sign)
F.inv                  =  1     (Z^(p−2) in encode)   -- 509 of the muls above
F.sqrtRatio            =  1     (in decode)            -- 507 of the muls above
point additions        =  512 + ps + pk + 1
point doublings        =  512
```

| Row | Typical (`ps`=125, `pk`=126, mean over fixtures) | Worst case (`ps`=`pk`=252) | Where it comes from |
|---|---:|---:|---|
| field multiplications | **9,434** | **12,217** | 8,404 (Point.add) + 519 (decode) + 511 (encode) → worst 11,187+519+511 |
| field add/subtractions | **6,114** | **8,138** | 6,112 (Point.add) + 2 (decode) |
| field negations | 2–5 | 2–5 | `A.neg` 2, `neg u` 1, `abs` 0/1, decode sign flip 0/1 |
| inversions (`pow p−2`) | **1** | **1** | `Point.affine` inside `encode` |
| square roots (`sqrtRatio`) | **1** | **1** | `decode` |
| exponentiation `(p−5)/8` | **1** | **1** | inside `sqrtRatio` |
| point additions | **764** | **1,017** | `smulAux` bits + final add |
| point doublings | **512** | **512** | 2 × 256 |
| SHA-512 compressions | **1** (msg ≤ 63 B) … **10** (1087 B) | same | `sha512(R‖A‖M)`; 64 B prefix, so msg ≤ 63 B = 1 block |

Measured execution over the 3,543 accepting fixtures: `F.mul` 7,850–9,830 (mean 9,414.8),
add/sub 4,962–6,402 (mean 6,099.7), `Point.add` 620–800 (mean 762.2). The fixture minimum
(`F.mul` 7,850) is lower than the typical figure because some accepted vectors are low-order
points where `k` has very few set bits; the **structural** worst case is 12,217 muls, and that
is what a fixed-trace AIR must budget for unless the ladder is made value-independent.

Two structural remarks that matter for an AIR:

1. **The ladder is fixed-length**, so the only input-dependent variance is the two
   `popcount`s. A padded trace sized for `ps = pk = 252` covers every accepted signature.
2. **`decode` accepts non-canonical `y ∈ [p, 2^255)`** (`Ed25519.lean:178` takes `y mod p`)
   and **accepts `x = 0` with the sign bit set** (`Ed25519.lean:186`, `−0 = 0`). An
   in-circuit implementation must keep both quirks or it will disagree with nearcore on
   `edge.jsonl` / `cctv.jsonl`.

---

## Part 2 — Cost model

Measured SHA-512 AIR cost (`research/near-compression/results/pq384-sha-air3/README.md`):

```
83 columns × 128 rows = 10,624 cells per compression, 17 interactions/row = 2,176 per compression
```

**Assumption A1.** An `F_p` multiplication (`p = 2^255−19`) in a BabyBear-hosted emulation
costs **`N` cells**. `N` is swept, not asserted: `N ∈ {100, 120, 149, 200}`.
`N = 149` is not a guess: it is the **committed width of the prototype chip actually built in
Part 3** (`a` 15 + `b` 15 + `q` 15 + `r` 15 + `d` 29 + `cd` 30 + `ce` 30). So `N = 149` is the
one row of the table that corresponds to working code.

**Assumption A2.** A limbwise add/sub/neg costs **16 cells** (15 output limbs + 1 carry).
This is a small term; at `N = 149` it is 6,114 × 16 ≈ 98 k cells out of 1.51 M.

**Assumption A3.** Interactions: 2 per `F_p` mul (limb range checks + canonical-output bound),
1 per add/sub/neg. Not measured; the SHA figure (17/row) is measured and is used for the hash.

Cost formula (`cost_model.py`):

```
cells        = N·muls + 16·addsub + 16·negs + blocks·10,624
interactions = 2·muls + 1·addsub + 1·negs + blocks·2,176
```

| Case | muls | add/sub | SHA blocks | N=100 | N=120 | **N=149 (prototype)** | N=200 |
|---|---:|---:|---:|---:|---:|---:|---:|
| typical (125,126), D1 msg 32 B | 9,434 | 6,114 | 1 | 1,051,928 | 1,240,608 | **1,514,194** | 1,995,328 |
| typical, widest fixture (msg 1087 B) | 9,434 | 6,114 | 10 | 1,147,544 | 1,336,224 | **1,609,810** | 2,090,944 |
| worst case (252,252), D1 msg 32 B | 12,217 | 8,143 | 1 | 1,362,612 | 1,606,952 | **1,961,245** | 2,584,312 |

### Component breakdown at N = 149, typical D1 signature

| Component | Cells | Interactions | Derivation |
|---|---:|---:|---|
| field muls | 1,405,666 | 18,868 | 9,434 × 149 |
| field add/sub/neg | 97,904 | 6,119 | 6,119 × 16 |
| SHA-512 (1 compression) | 10,624 | 2,176 | 83 × 128; 17 × 128 |
| **total** | **1,514,194** | **27,163** | |

Worst case at N = 149: **1,961,245 cells**, 24,434 + 8,143 + 10,624 = field 1,950,621 plus
hash, and **34,753 interactions** (2·12,217 + 8,143 + 2,176).

Sanity checks on the model:

* The SHA-512 chip is **0.7 %** of the cells at N = 149 (10,624 / 1,514,194 = 0.70 %). The cost is entirely field
  arithmetic. Making the hash 10× cheaper would not matter; making the field mul 2× cheaper
  halves the total.
* One `F_p` mul cell is worth **9,434 cells per signature** (12,217 in the worst case). Any
  optimisation of the field chip has ~9.4 k cells of leverage per cell saved.
* The exponentiation muls alone (`509 + 507 = 1,016`) are 10.8 % of all multiplications and
  151 k cells at N = 149. An addition chain for `p−2` or a batch inversion would remove a
  large part of that; this is the single cheapest algorithmic win.

---

## Part 3 — Prototype of the `F_p` multiplication chip

Built and working: `FpChip.lean` (the chip), `Difftest.lean` (the exporter/harness),
`difftest.py` (independent re-check). Style follows
`research/near-compression/wasm-base-lean/` (a `Expr` node type with `c`/`v`/`+`/`−`/`*`,
JSON export in that tool's dialect, and `Local.*_sound`-style lemmas).

* **Representation.** 15 limbs of 17 bits (`B = 2^17`, `B^15 = 2^255`), 149 committed cells.
* **Relation.** Two base-`B` carry chains over the same reduced digits `d`:
  `conv_k + cd_k = d_k + B·cd_{k+1}`, `qp_k + r_k + ce_k = d_k + B·ce_{k+1}`,
  `cd_0 = ce_0 = 0`, `cd_29 = ce_29`, with `conv = a*b` and `qp = q*p` coefficients.
  Eliminating `d` gives `a·b = q·p + r`; with `r < p` this is `r = a·b mod p`.
* **Constraints.** 61 polynomial constraints, degree 2, `nconstraints` in the exported AIR.
* **Proved** (`#print axioms` = `[propext, Quot.sound]` only, no `sorry`/`native_decide`/
  `implemented_by`):
  * `B_pow`, `p_limbs`, `p_eq_spec` — kernel-checked, **no axioms at all**;
  * `value_of_chain` — the telescoping lemma;
  * `value_of_chain0` — its `c 0 = 0` corollary;
  * `mul_identity` — the constraint system implies `a·b = q·p + r`.
* **Not proved, and stated as hypotheses or tested** (explicitly marked in the file):
  * `RecombineConv` / `RecombineQP`: the two exact digit recombinations. These are *definitions
    used as hypotheses* of `mul_identity`, not axioms and not `sorry`;
  * `Row.gen` satisfies the constraints — this is the untrusted prover, differential-tested;
  * the final `r = a*b % p` uniqueness step;
  * completeness of the complete-addition law (not attempted here; it is already flagged
    "not proved" in `Ed25519.lean:54`).

### Test evidence (`logs/`)

| Check | Command | Result |
|---|---|---|
| chip compiles | `lake env lean results/pq-ed25519-air/FpChip.lean` | exit 0, `logs/build-fpchip.log` |
| Lean-side differential test | `lean --run …/Difftest.lean vectors 20261020 2000` | **2,153 vectors, 0 failures** (`logs/difftest-summary.txt`) |
| edges included | — | `0, 1, 2, p−1, p−2, p/2, 2^254, 2^255−20, B−1, B, B^14, p−B−1`, all 144 pairs |
| non-canonical rejection | — | `a,b ∈ {p, p+1, 2^255−1}`: **9/9 rejected** |
| independent AIR re-check | `python3 …/difftest.py air logs/air-export.jsonl` | **16 rows, 0 failures** (every constraint re-evaluated in Python + `a*b = q*p+r`) |
| carry bound | measured | max carry **1,966,045 < 2^21**, bound `2^23` is safe |

**Not completed in Part 3**: the chip is not wired into a full Ed25519 AIR, there is no Rust
interpreter consuming the exported JSON (the Python re-check stands in for it), and the
recombination identities are not machine-proved. Everything above is a working, tested
prototype of the multiplication gadget only.

---

## Part 4 — Recommendation

**Verdict: (b) a separate signature proof layer is better than folding Ed25519 verification
into the existing chunk-validation AIR — but the field chip itself is feasible, at
~1.5 M cells per signature.**

### Why not (a) prove it in the chunk-validation AIR

1. **Cells.** 1.51 M cells for a typical signature at N = 149, 1.96 M worst case, against a
   SHA-512 compression at 10,624. One signature is **≈ 143 compressions**. A chunk has many
   transactions; the existing O-2 final layer is ~300 KB for the whole chunk circuit. Even
   if the field chip is driven down to N = 100 (1.05 M cells), a handful of signatures per
   chunk dominate the trace. This is the opposite of the SHA work, where the hash was the
   *only* expensive thing and 10 k cells was acceptable.
2. **The work is 99 % field arithmetic, not hashing.** The SHA chip is 0.7 % of the cells.
   The existing SHA-512 AIR, its 6,321-mutation test suite and its faithfulness argument do
   not transfer; every cell of the 1.5 M is new, unaudited constraint surface.
3. **Algebraic structure favours a different proof system.** Ed25519 verification is a
   statement about a group over `F_p`, `p = 2^255−19`. Expressing it over BabyBear forces a
   9-limb (or 15-limb) emulation *before* the AIR even starts, so every `F_p` mul pays a
   ~149-cell penalty for the field mismatch. That is a 3–5× tax compared with proving the
   same relation over a curve defined natively over a 255-bit field (or over an extension
   that contains it).

### Why not (c) keep native verification

The existing pipeline already re-executes the transaction natively and the chunk-validation
relation `RelD1` includes `Ed25519.verify` (`TxD1.lean:132`). If the goal is only "the
validator did what nearcore did", (c) is correct today: `sigVerifEd25519 = 0` gas
(`TxD1.lean:56`) shows nearcore treats it as free. But (c) gives no succinct proof of the
signature predicate, so a light client cannot check a signed transaction without the key.
That is the gap (b) fills.

### Recommended shape of (b)

* **A dedicated Ed25519 proof layer** over a 255-bit-friendly field (or a native
  `p = 2^255−19` arithmetic argument), sharing only the SHA-512 chip (10,624 cells,
  already measured) and a recursion/aggregation step with the chunk circuit.
* **Reuse the census directly**: the layer must implement `decode` (519 muls), two
  `smulAux 256` ladders (fixed 512 doublings + variable bits), one `encode` (511 muls), and
  `sha512`. The fixed 1,016 exponentiation muls are the first optimisation target
  (addition chain / batch inversion).
* **Skip the 149-cell BabyBear emulation** except where a BabyBear-only recursion step
  forces it; if it is forced, N = 149 is the number the prototype has already paid for.

### Effort estimate

Agent-days, assuming the multiplication gadget is done (it is, modulo the recombinations):

| Piece | Agent-days | Basis |
|---|---:|---|
| field chip hardening: prove `RecombineConv`/`RecombineQP`, fix bounds | 3–5 | `value_of_chain` took one session; the reorder is routine but fiddly |
| `F_p` add/sub/neg + canonical compare chip | 2–3 | 16 cells, same style |
| `sqrtRatio` + `decode` trace and constraints | 4–6 | 520 muls, one branch; the `u=0` and sign quirks are the risk |
| fixed-length `smulAux` ladder chip (wiring only; the mul is done) | 2–3 | 1,017 `Point.add` per signature, no new algebra |
| `encode` + comparison | 1–2 | 511 muls, one inversion |
| SHA-512 wiring (reuse existing AIR) | 1–2 | already measured and tested |
| differential testing vs `Ed25519.verify` on the 7,265 fixtures | 3–5 | fixtures and the transcription already exist |
| **total** | **16–26 agent-days** | |

So: **(b) separate signature proof layer, ~1.5 M cells/signature at N = 149, 16–26
agent-days.** In-circuit in the chunk AIR is feasible but economically wrong at ~143
compressions per signature. Keeping it native is right only if no succinct signature proof
is required.

---

## Reproducing

```bash
python3 research/near-compression/results/pq-ed25519-air/census.py        # Part 1 (+ fixture check)
python3 research/near-compression/results/pq-ed25519-air/cost_model.py    # Part 2

cd research/near-compression
ELAN_TOOLCHAIN=leanprover/lean4:v4.34.1 lake env lean results/pq-ed25519-air/FpChip.lean
ELAN_TOOLCHAIN=leanprover/lean4:v4.34.1 lake env lean \
  -R results/pq-ed25519-air -o /tmp/fpolean/FpChip.olean -i /tmp/fpolean/FpChip.ilean \
  results/pq-ed25519-air/FpChip.lean
LEAN_PATH=/tmp/fpolean:$LEAN_PATH ELAN_TOOLCHAIN=leanprover/lean4:v4.34.1 \
  lake env lean --run results/pq-ed25519-air/Difftest.lean vectors 20261020 2000 \
  > results/pq-ed25519-air/logs/difftest-vectors.jsonl
python3 results/pq-ed25519-air/difftest.py lean results/pq-ed25519-air/logs/difftest-vectors.jsonl
python3 results/pq-ed25519-air/difftest.py air  results/pq-ed25519-air/logs/air-export.jsonl
```

Only `research/` was modified; `make pin-check` is unaffected.


## Part 3 status (Fp chip prototype)

`FpChip.lean` is a prototype of the `F_p` multiplication gadget only; it is not wired into a full
Ed25519 AIR and there is no Rust interpreter for it.

Proved with axioms `[propext, Quot.sound]` (verified by `#print axioms`): `B_pow`, `p_limbs`,
`value_of_chain`, `value_of_chain0`, `mul_identity`.

**Not proved:** the two exact recombination identities `recombine_conv` / `recombine_qp`. They are
hypotheses of `mul_identity`, not theorems. The `a·b = q·p + r` conclusion is therefore
conditional on them. Also not proved: that `Row.gen` satisfies the constraints (tested), and the
`r = a*b % p` characterisation (tested).

Tested: 2,153 vectors including 0, 1, p−1, p−2, p/2, 2^254, powers of B and full-width products;
9/9 non-canonical inputs rejected; an independent Python re-evaluation of every exported
constraint. No `sorry`, `native_decide` or `implemented_by`.
