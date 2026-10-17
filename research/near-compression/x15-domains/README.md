# ×15 BabyBear evaluation domains for WHIR: design, prototype, measurements

This is lane X of the PQ final-layer work. Gate 1 (the paper check) is in [SOUNDNESS.md](SOUNDNESS.md): it **passes with m = 3**.

This file covers Part 2 (design and prototype). Labels:
- **[measured]**: run on this host;
- **[modelled]**: extrapolated;
- **[design]**: not implemented.

## Design

### Domain and layout
- The RS domain of WHIR round i is the subgroup D_i of order c·2^(L−i), with c = 15 and L = log2(trace height) + log_blowup. D_i = ⟨ζ⟩ × H_(L−i), where ζ = GENERATOR^((p−1)/15).
- Storage is **coset-major**. Codeword row a·2^(L_i) + u holds the value at ζ^a·ω_(L_i)^u. Each block a is an ordinary radix-2 **coset LDE** with shift ζ^a, so 15 coset DFTs replace one big DFT and no mixed-radix NTT code is needed. With c = 1 this is exactly the upstream encoding.
- Fold cosets: the fibre of x = ζ^a·ω^(u0) under x ↦ x^(2^k) is x·μ_(2^k). These are rows u0 + j·2^(L_i−k) of block a, which is the upstream stride *inside one block*.

### Merkle tree
- Each block is hashed exactly as upstream: one row digest per row, then a 2^k-row mini-tree per fold coset, at stride 2^(L_i−k).
- The 15 query-digest layers are concatenated in block order. Leaf index i' = a·2^(L_i−k) + u0, so **each fold coset is one leaf** and each block is a complete subtree.
- The upper levels form a binary tree in which any odd-length layer is padded with the fixed digest H(""). Depth is L_i − k + ⌈log2 15⌉ = L_i − k + 4.
- Padding positions are never valid query indices: the verifier only derives indices < 15·2^(L_i−k).

### Folding across rounds
- WHIR queries are fresh in every round (there are no FRI-style linked positions), so the verifier needs only the map from index to point in each round. No index arithmetic is needed across rounds.
- Squaring maps ζ^a·ω_L^u to ζ^(2a)·ω_(L−1)^u. So D_(i+1) = D_i^(2) has the *same* 15 coset shifts ζ^a, with the order-15 part permuted (a → 2a mod 15).
- The round-(i+1) codeword is encoded on D_(i+1) with the same layout.
- The shift-query point is z = (ζ^a·ω^(u0))^(2^k) = ζ^(a·2^k)·ω_(L−k)^(u0). This is a bijection from indices onto D_i^(2^k), so a uniform index gives a uniform point.

### Query sampling
- Sample x from the SHA-384 transcript; the existing sampler is exactly uniform on [0, p).
- **Reject x = p − 1**, then take x mod (15·2^(L_i−k)). Since 15·2^(L_i−k) divides p − 1 = 15·2^27, the result is exactly uniform.
- Expected cost is 1 + 2^-31 draws per query.
- In-circuit alternative: reject the proof on x = p − 1, with completeness error ≈ q/p.
- The upstream `sample_bits` (residue 0 heavier by 1/p) is kept, unchanged, for c = 1.

### Parameter and binding
- `WhirConfig.domain_odd_factor`: default 1, which is byte-identical to upstream. Valid values are odd c dividing p − 1, i.e. 3, 5 or 15 for BabyBear.
- The field is `#[serde(skip)]`, so the VK pre-hash and postcard layout are unchanged.
- When c > 1, the WHIR prover and verifier `observe(c)` before the μ proof-of-work, so the transcript binds the domain.
- A deserialized VK reads c = 1. That fails closed: an ×15 proof does not verify under it.

## Prototype status [measured]

| item | result |
|---|---|
| Patch | [`patches/stark-backend-x15.patch`](patches/stark-backend-x15.patch), on top of the pinned d667af5 + native patch. New file `odd_domain.rs`; edits to the WHIR prover/verifier, `stacked_pcs`, proof shape, transcript (`sample_index_exact`), calculator, `WhirConfig`, and test utils. Applied by `setup_x15_deps.sh` into `$NEARPROOF_PQ_DEPS` (default `/data/illia/nearproof-deps/pq-x15`). It refuses `pq-native`. |
| Driver | [`crate/src/`](crate/src): SHA-384 / Ext12 config (the native `native_sha384_config.rs`, included verbatim). Built by `setup_x15_crate.sh` against the patched backend (`x15-proto`) and the unmodified backend (`x15-proto-base`). |
| Default unchanged | `ident`: Fib, interactions, preprocessed, cached, mixture and a wide AIR, all at c = 1, give **byte-identical** proofs on the base and patched backends ([`results/ident-*.txt`](results)). **gas-failure5** re-proved on the patched backend gives child.proof sha256 `ba042e71…`, which is identical, with the same calculator bits (268.76 / 331.58 / 320.93) ([`results/gas-failure5-identity.txt`](results/gas-failure5-identity.txt)). |
| ×15 end to end | Prove and verify succeed for Fib (c ∈ {3, 5, 15}, log_blowup 1–3, k 2–4), interactions, preprocessed, **cached (2 commitments)**, mixture, and a 40-column AIR. The ×15 domain is active in **every WHIR round**, not only the first. |
| Negative tests | **55/55 rejected** ([`results/selftest-adversarial.txt`](results/selftest-adversarial.txt)): opened row values (first and last query, last fold row), Merkle siblings at leaf level and at the padded top level, round-1 codeword value, sibling, commitment, OOD value, final polynomial, main commitment, and verifying an ×15 proof with a power-of-two VK. **Adversarial words with valid Merkle trees** are rejected by the fold/sumcheck checks (`FinalPolyConstraint`): cosets 1↔2 swapped; the power-of-two codeword repeated 15×; each coset mirrored (u → −u). |
| Calculator | Domain-aware for c > 1 (real-valued rate, n = 15·2^…, exact sampler). It still uses BCHKS25 like upstream; the contract numbers are in `rbr_x15.py`. |

## Measurements [measured]

Wide AIR (W = 64, next[j] = local[j] + local[j+1]), SHA-384 / Ext12, target 268, list decoding m = 3, k = 4. Runs used 8 threads on shared CPUs (8–15, 24–31), so expect ±30 % noise. Peak RSS is from `/usr/bin/time`.

| trace 2^16 × 64 | domain points / column | rate | queries | prove s | peak RSS | proof B |
|---|---:|---:|---|---:|---:|---:|
| ×1, log_blowup 2 | 2^18 | 1/4 | 345,118,71,51 | 2.7–2.8 | 0.39 GB | 1,987,209 |
| ×1, log_blowup 5 | 2^21 | 1/32 | 118,71,51,40 | 6.9–7.3 | 1.27 GB | 838,633 |
| ×1, log_blowup 6 | 2^22 | 1/64 | 97,63,47,37 | 11.3–11.9 | 2.34 GB | 724,633 |
| **×15, log_blowup 2** | 15·2^18 | 1/60 | 99,64,47,38 | 5.6–8.5 | 2.19–2.25 GB | 737,625 |
| ×5, log_blowup 3 | 5·2^19 | 1/40 | 110,69,50,39 | 4.7–6.0 | 1.49–1.53 GB | 806,201 |
| ×3, log_blowup 4 | 3·2^20 | 1/48 | 105,66,49,38 | 7.3–8.7 | 1.85–1.89 GB | 773,625 |

| trace 2^18 × 64 | prove s | peak RSS | proof B | commit: RS s / Merkle s |
|---|---:|---:|---:|---|
| ×15, log_blowup 2 (15·2^20) | 33.7, 45.7 | 8.59–8.73 GB | 762,153 | 7.29 / 4.56 |
| ×1, log_blowup 6 (2^24) | 59.6, 54.5 | 8.75 GB | 748,777 | 13.52 / 3.20 |

Readings:
- **Proof size.** At rate 1/60, the ×15 proof falls between the power-of-two proofs at rates 1/32 and 1/64, close to 1/64, as log2 60 = 5.91 predicts. The protocol gives the rate gain the model assumes, with no change in the 2-adic size.
- **Prover cost at equal rate (1/60 vs 1/64).** Memory scales with domain points: the same at equal size, 7 % less for ×15. Prover time is no worse; it was 15–45 % faster in these noisy runs. The 15 independent 2^L coset DFTs ran at 4.6–7.3 ns per point·column, against 9.8–13.3 for one 2^(L+4) DFT, because they are more cache- and parallelism-friendly. Merkle cost per point is the same within noise.
- The ×15 verifier is no slower (7–15 ms).

## Streamed LDE at the final-layer shape [modelled; design]

These are the models-C shapes at the measured c_sha = 19,448 ([`results/stream_estimate.out`](results/stream_estimate.out)). The prover of this layer commits W columns on 15·2^27 = 2^30.91 points:

| shape | LDE cells | materialised | resident coefficients | chunk (s = 0 / 3 / 7) | leaf digests |
|---|---:|---:|---:|---|---:|
| T ×15 final, W 151, h 20, b 7 | 2^38.15 | 1.22 TB | 0.59 GiB | 75.5 / 9.4 / 0.59 GiB | 45 GiB |
| T COMBO+E5 final, W 96 | 2^37.49 | 0.77 TB | 0.38 GiB | 48 / 6 / 0.38 GiB | 45 GiB |
| C-invention COMBO+E5, W 111, h 19, b 8 | 2^37.70 | 0.89 TB | 0.22 GiB | 55.5 / 6.9 / 0.43 GiB | 45 GiB |

How not to materialise the LDE [design]:
1. **Chunk by radix-2 sub-cosets.** Chunk (a, t) is the sub-coset ζ^a·ω_L^t·H_(2^(L−s)), with 15·2^s chunks. Each chunk is one coset DFT of size 2^(L−s) ≥ 2^h of the resident coefficients, so any s ≤ L − h works. Every chunk is closed under fibres (μ_(2^k) ⊆ H_(2^(L−s)) when L − s ≥ k), so it hashes to a **complete Merkle subtree**. To do this, generalise the leaf index to i' = (a·2^s + t)·2^(L−s−k) + v0, with point ζ^a·ω_L^t·ω_(L−s)^(v0). The implemented layout is the case s = 0. The change is a re-indexing, and soundness is unaffected because the map stays a bijection with uniform indices.
2. **Per-device working set** = resident coefficients + one chunk + hash buffers. That is ≤ 10 GiB at s = 3, so the work splits over 8 GPUs, or CPU sockets, by chunk with no communication beyond the 15·2^s subtree roots.
3. **Keep only a cap.** Keep the 15·2^s subtree roots, or all leaf digests at 45 GiB of host RAM. After the query indices are drawn, **recompute** the ≤ q0 ≈ 52 touched chunks to produce authentication paths. At s = 7 that is ≤ 2.7 % extra work.
4. **Opened rows need no LDE.** Evaluate the q0·2^k1 fibre points directly from the coefficients: ≈ 10^10 multiply-adds, seconds on CPU.
5. The round-1 Ext12 codeword (15·2^26 × 48 B = 45 GiB) streams the same way, from 2^19 Ext12 coefficients.

The bounded requirement is therefore O(W·2^h) coefficients + O(W·2^(L−s)) per worker, plus optional digest storage. Nothing scales with the full 0.8–1.2 TB.

Throughput [modelled]: linear extrapolation of the measured CPU constants (with the NTT log factor scaled 27/20) gives
- 30–73 min on 8 threads;
- about 1.3–3 min if scaled ideally to 192 cores.

GPU NTT/SHA throughput was not measured. The earlier "a few seconds per 8×H200" guess remains unverified.

## Blockers and next steps

1. **Recursion circuit.** The in-circuit verifier needs:
   - the exact sampler (reject-on-(p−1), 4-bit odd part);
   - the point ζ^a·ω^(u0) (a 15-entry table);
   - Merkle depth +4.

   None of this exists yet. It is needed for the penultimate layer's lever.
2. **Streaming commit.** Implement the generalised s-chunk layout and the cap/recompute path. Then measure at a real shape, which needs an 8×H200 or a large-RAM CPU host.
3. **m = 3** (or μ-PoW / fewer stacked columns) to meet 2^-268 under BCGM; see SOUNDNESS.md. The calculator should gain a BCGM mode for c > 1.
4. **Backends.** Port the patch to `cpu-backend` and `cuda-backend`. Until then they ignore c (fail closed). Update `memory_metering`.
5. **Write-up.** A written lemma "WHIR Thm 5.2 for c·2^K domains", for the security write-up.

## Reproduce

```sh
L=research/near-compression/x15-domains
NEARPROOF_PQ_DEPS=/data/illia/nearproof-deps/pq-x15 $L/setup_x15_deps.sh
NEARPROOF_PQ_DEPS=/data/illia/nearproof-deps/pq-x15 $L/setup_x15_crate.sh
cd /data/illia/nearproof-deps/pq-x15/x15-proto && CARGO_TARGET_DIR=../target cargo build --release --offline
../target/release/x15-proto selftest; ../target/release/x15-proto adversarial; ../target/release/x15-proto ident
../target/release/x15-proto bench 15 2 16 64 4 268     # odd log_blowup log_h W k bits
../target/release/x15-proto commit 15 2 16 64 4 3      # RS / Merkle split, best of 3
python3 $L/rbr_x15.py; python3 $L/stream_estimate.py
```

Run heavy jobs through `HEAVY_MEM=… taskset -c 8-15,24-31 /data/illia/nearproof-deps/bin/heavy`.
