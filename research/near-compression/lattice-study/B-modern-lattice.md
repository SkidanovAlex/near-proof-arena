# B. Modern lattice succinct arguments / folding (2024–2026) as a final "wrap" for a SWIRL/WHIR BabyBear STARK

Date: 2026-10-17. Read-only literature study. PDFs and text dumps are in `lattice/pdf/` (ePrint id with `_`, e.g. `2026_1983.txt` = Akita).
Tags: **[M]** = measured in the cited paper (with its hardware), **[E]** = the authors' own estimate or projection, no implementation, **[I]** = my inference for our setting.

## 0. Wrap requirements (from the task)

- Statement: "I know a penultimate SWIRL proof that the fixed SWIRL verifier accepts." Workload is about 2k–9k SHA-512-family compressions plus 1e5–1e6 BabyBear-Ext12 multiplications.
- Circuit size [I]: SHA-512 is roughly 50–70k constraints per compression with bit decomposition in a 31-bit field, which gives 1e8–6e8. Ext12 multiplications at about 150–200 constraints each give 1.5e7–2e8. Total is about **2^27–2^30 base-field witness elements**. Lookups would shrink this.
- Targets: proof ≤ 300 KB (≤ 100 KB ideal), cheap CPU verifier, near-real-time prover on a few 8×H200, PQ with soundness ≤ 2^-128 against 2^64 quantum RO queries, proven bounds preferred.

## 1. Per-scheme survey

### 1.1 Akita (Dao, Bodaghi, Khajehpour, Vitto, Badakhshan, Georghiades, Liu, Zhang, Thaler; ePrint 2026/1983; LayerZero + a16z)

- **What it is:** a multilinear PCS. It succeeds Hachi and Greyhound and is the PCS inside "Lattice Jolt" (released 2026-09-09).
- **Proof size [M]:**
  - 61–67 KB opening proofs for 2^27–2^35 committed bits, i.e. up to N = 2^30 coefficients of a 32-bit field.
  - Commitments are 128 B.
  - At 2^35 bits: 64.6 KB direct, 67.3 KB with setup offloading. The p64 and p128 profiles give 68–72 KB. (Table 8/9.)
- **Verifier [M]:**
  - 2^35 bits (N = 2^30, p32), 1 thread, Ryzen 9950X: 15.9 ms offloaded, 32.5 ms direct.
  - 2^29 bits: 8.1 ms.
  - That is 19–90× faster than Greyhound (155–1423 ms).
  - Asymptotically Õ(N^{1/K}) for any fixed K ≥ 2 ("constant-root"), **not polylog**. The verifier may keep an expanded setup prefix of size Õ(N^{1/K}).
- **Prover [M]:**
  - N = 2^30 (p32), 1 thread: commit 24.3 s, open 16.1–18.4 s, peak RAM 4.7 GiB.
  - 8 threads: commit 3.46 s, open 2.7–3.0 s.
  - Distributed proving is supported through response chunking (§11).
- **Full SNARK [M]:** Jolt-with-Akita proves SHA-256 chains (Table 10, M4 Max 16-core CPU).
  - T = 2^27 RISC-V cycles: prove 90.9 s, verify 39.8 ms, proof 98.1 KB.
  - T = 2^25: 29.5 s, 28.2 ms, 94.2 KB.
  - Every proof is below 100 KB.
  - The a16z blog also reports >10 MHz cycles on Apple Metal GPU [vendor claim, no paper numbers].
- **Fields:**
  - The implementation supports three primes: q = 2^32−99, 2^64−59 and 2^128−2^32+22537. Jolt uses the 128-bit profile.
  - It needs q ≡ 5 (mod 8) or another partially splitting configuration for the power-of-two ring X^d+1.
  - Extension fields F_{q^k} embed only for **k a power of two** dividing d/2. Openings are over a degree-4 extension.
  - **BabyBear is not supported** (see §2).
- **Assumptions:**
  - Standard Module-SIS. Compression maps are estimated at ≥147-bit quantum Core-SVP (ADPS16).
  - 128-bit statistical target via grinding.
  - Knowledge soundness is proven **only in the classical ROM. A QROM proof is explicitly future work** (§1.1, §14).
  - The response model used for later-fold schedules is heuristic. This affects completeness, not soundness.
- **Succinct by itself?** Yes as a PCS. As a SNARK it needs a PIOP (sum-check/Spartan, as in Jolt) on top. No decider is needed.
- **Maturity:**
  - Rust, AVX-512/NEON, integrated in Jolt (open source), with an offline parameter planner and an independent validator.
  - No audit is mentioned.
  - App. F lists security bugs found in *prior* artifacts: Greyhound/LaBRADOR truncated-output Ring-SIS, Greyhound's JL projection, RoKoko implementation errors, Hachi paper issues. This is a sign the area is still settling.

### 1.2 Hachi (Nguyen, O'Rourke, Zhang; ePrint 2026/156)

- **Design:** a multilinear PCS built from Greyhound plus Huang–Mao–Zhang ring switching. The verifier does no R_q multiplications. A generic reduction turns F_{q^k} evaluation claims into ring relations.
- **Proof size [E/M]:** about 55 KB (estimated composition with a Greyhound tail).
- **Verifier [M]:** about 227 ms at 2^30 (Õ(√N·λ)), 12.5× faster than Greyhound.
- **Prover [M]:** about 270 s (prototype).
- **Assumption:** MSIS.
- **Status:** superseded by Akita, its direct successor.

### 1.3 RoKoko (Klooß, Lai, Nguyen, Osadnik, Tucci; ePrint 2026/575) and its lineage: RoK, Paper, SISsors (2024/1972), RoK and Roll (2025/1220), SALSAA (2025/2124)

- **RoKoko design:** linear-time prover with **polylog communication and verifier**. It uses committed folding with large arity, recursive commitments and SALSAA-style sum-check.
- **RoKoko numbers [M]** (Table 1, 1 thread):
  - #Zq = 2^30: commit 18.1 s, prove 8.9 s, verify 13.1 ms, **157 KB**.
  - #Zq = 2^26: verify 7.5 ms.
  - Akita's re-measurement: 109–115 KB proofs, 4–7 ms verify, but 36.9 GiB RAM at 2^35 bits.
- **RoKoko ring and security:**
  - Ring: almost-splitting X^128+1 with q ≈ 2^50 (slots F_{q^2}).
  - **Assumption: vSIS (vanishing SIS)**, a newer structured assumption with less cryptanalysis.
  - Statistical soundness target is only **2^-100**.
  - Challenge invertibility is heuristic (estimated non-invertibility ≈ 2^-94).
- **RPS → RnR → SALSAA:** these are the earlier vSIS-based fully succinct arguments, with polylog verifier but large proofs at 2^30 [M, from RoKoko Table 1]:
  - RnR (KLNO25): 3.15 MB.
  - SALSAA: 1.46 MB, verify about 0.3 s (its own paper says < 7 ms with its own setup). SALSAA prove time is 108–440 s.
  - SALSAA also gives an AIR RoK and a folding scheme (about 60 KB per step).
- **Maturity:** Rust code is available (github.com/lattice-arguments/rokoko). Akita notes earlier RoKoko implementation errors that were later corrected upstream.

### 1.4 Grand Danois (Kallesøe, Khoshakhlagh; ePrint 2026/1196)

- **Design:** Hachi-style PCS with **polylog O(λℓ) verifier**, using vSIS, rotation-matrix row folding and an RnR-style structured JL norm proof.
- **Proof size [E]:** about 80 KB at 2^32 under vSIS.
- **Maturity:** no implementation. Akita App. F flags paper issues.

### 1.5 Maltese (Cheng, Nguyen, Tyagi; ePrint 2026/2067, ASIACRYPT 2026)

- **Design:** a Merkle tree of Ajtai hashes with sum-check norm management. It has **O(log^3 N) verifier ring operations and O(log^2 N) proof size under standard MSIS**, so it is the only standard-MSIS PCS with genuinely polylog verification.
- **Proof size [E]:** **335 KB at N = 2^30**, best parameter set 224–335 KB. These are composed estimates that include a Greyhound tail.
- **Fields:** 32-bit and 64-bit fields are parameterized.
- **Caveats:**
  - No full composed security bound.
  - The 128-bit challenge set needs a heuristic inversion bound.
  - No verifier timings and no implementation reported.

### 1.6 Neo (ePrint 2025/294) and Neo/SuperNeo (Nguyen, Setty; ePrint 2026/242, Microsoft Research)

- **Design:**
  - Lattice HyperNova: a folding scheme for CCS with pay-per-bit Ajtai commitments.
  - Sum-check and norm checks run **purely over a small field extension** (no ring arithmetic).
  - SuperNeo supports **CCS over any extension field L of the commitment field without NTT embedding**.
  - It uses **non-power-of-two cyclotomics** (e.g. Φ_81 = X^54+X^27+1) precisely to work with high-2-adicity fields.
- **Parameters [E]:**
  - Given for Goldilocks (d = 54, κ = 18, |C| ≈ 2^125, MSIS ≈ 129 bits), M61, and "Almost Goldilocks".
  - **None for 31-bit fields.**
- **Assumption:** MSIS (ℓ∞).
- **Succinct by itself?** **No.** It is a folding/IVC primitive. The final accumulator needs a decider: the authors suggest Spartan with FRI, or a lattice PCS.
- **Maturity:** no SuperNeo implementation in the paper. Neo is referenced from the Nexus zkVM context.
- **Relation to Cyclo:** Cyclo (Garreta, Lipmaa, Luhaäär, Osadnik; ePrint 2026/359, EUROCRYPT 2026) is "equivalent to Neo", with an amortized accumulator norm refresh. Its folding proofs are about 30 KB [E, with partial benchmarks].

### 1.7 Other folding schemes (all need a decider)

- **LatticeFold (2024/257) / LatticeFold+ (2025/247)** (Boneh, Chen):
  - Use ring sum-checks, power-of-two rings and large q.
  - LatticeFold+ folding proofs are about 100–200 KB [E].
  - Not small-field native: Goldilocks fully splits. Not pay-per-bit.
- **Lova (2024/1964):**
  - Plain SIS with power-of-two modulus. Subset-sum relation only.
  - About 3,000 s for 2^19 [M, as quoted by SuperNeo].
  - Not viable.
- **PikkuFold (Osadnik; 2026/1809):**
  - 5.5 KB per fold beyond input commitments, ms-scale verifier.
  - Rigorous fixed-weight challenge sampler and certified modular JL.
  - Folding only.
- **ProtogaLattice (Balbás, Nitulescu, Plançon; 2026/1317):**
  - Algebraic (non-sum-check) high-degree folding, 8.13 KB per iteration at 2^30 [E].
  - Smaller recursive verifier circuit.
- **Symphony (Chen; 2025/1905):**
  - High-arity lattice folding plus a compiler that avoids putting Fiat–Shamir in the circuit.
  - Polylog proof and verifier. Prover is dominated by about 3·2^32 Ajtai multiplications over a 64-bit q.
  - Proof estimated **< 200 KB [E]**, dominated by two inner SNARK proofs (WHIR or LaBRADOR). No implementation in the paper; Syscoin and 0xPARC report uses.
  - Built for *many uniform statements*, not one fixed circuit.
- **Orthus (IBM; 2026/398):** √N verifier for lattice relations (Falcon aggregation), MSIS.
- **Jindo (2026/044):** cube-root communication and verifier, for client-side ZK over a 255-bit field. Not relevant.
- **LUNA+ (2026/1639):** designated-verifier. Not relevant.

### 1.8 Asymptotically polylog standard-assumption PCSs (impractical sizes)

At 2^30, as quoted by Akita §1.2:

- Fenzi–Moghaddas–Nguyen: 8.3 MB.
- SLAP (2023/1469): 767 MB.
- Cini–Malavolta–Nguyen–Wee: 5.17 MB. This one has a knowledge-soundness proof against quantum adversaries.

## 2. BabyBear-native lattice commitments: the key compatibility finding

- **Power-of-two rings fully split [I, computed]:** p = 2^31−2^27+1 has p ≡ 1 (mod 2^27). So X^d+1 **splits completely** for every d ≤ 2^26 (verified: residue degree 1 for d = 16…256).
- **Consequence for the leading PCSs [I]:**
  - The LS18 short-challenge invertibility threshold becomes ~1, so the challenge sets of Greyhound, Hachi, Akita, LatticeFold and RoKoko do not transfer. The standard LS18 setting requires q ≡ 5 (mod 8); RoKoko's almost-splitting ring needs q ≢ 1 (mod 4·…).
  - Hachi/Akita embed F_{q^k} only for power-of-two k, so **Ext12 does not embed** even for a compatible q.
  - **No paper surveyed gives BabyBear parameters.**
- **Non-power-of-two cyclotomics do work [I, computed residue degrees mod p]:**
  - Φ_37 (d = 36) and Φ_41 (d = 40) are **inert**: R_q ≅ F_{p^36} or F_{p^40}, so every nonzero challenge difference is invertible.
  - Φ_81 (d = 54) has 2 factors of degree 27.
  - Φ_69 / Φ_92 (d = 44) have 2 factors of degree 22.
  - Notably F_{p^36} ⊃ F_{p^12}, so Φ_37 or Φ_111 rings contain our Ext12 as a subfield.
- **This is exactly SuperNeo's design space:** arbitrary cyclotomic, arbitrary extension L, field-native sum-check.
- **What is missing [I]:**
  - MSIS parameters at log q ≈ 31 with ℓ∞ binding (feasible: Akita runs MSIS at q = 2^32−99).
  - Norm-expansion constants for prime cyclotomics.
  - Re-deriving an Akita-style recursive opening (ring switching and trace embedding currently assume power-of-two d with q ≡ 5 mod 8).
  - This is a research project, not an off-the-shelf choice.
- **Practical alternative [I]: near-native emulation.**
  - Run the wrap SNARK over Akita's p64 or p128 field.
  - A BabyBear product a·b < 2^62 fits without wraparound, so a·b = c + k·p costs 1 constraint plus two 31-bit range checks (lookups).
  - In p128, an entire Ext12 multiplication can accumulate all 144 partial products and reduce once per output coefficient: about 144 mults + 12 reductions.
  - Overhead versus native BabyBear is roughly 1.1–1.5×, not 5–10×.
  - The verifier's arithmetic is then 64- or 128-bit prime-field arithmetic, which is cheap on CPU, rather than BabyBear.

## 3. Comparison table (large statements, about 2^30 elements)

| Scheme | Type | Proof @2^30 | Verify | Prover (CPU) | BabyBear-native | Assumption / FS model | Standalone succinct | Maturity |
|---|---|---|---|---|---|---|---|---|
| **Akita** | PCS (+PIOP = SNARK) | **64–72 KB [M]**; Jolt SNARK < 100 KB [M] | **16–33 ms, 1 thr [M]**; Õ(N^{1/K}) | 2^30 coeffs: 3.5 s commit + 3 s open on 8 thr [M]; Jolt 2^27 cycles 91 s M4 Max [M] | No (q ≡ 5 mod 8; p32/p64/p128) | MSIS; classical ROM only | Yes (with PIOP) | Rust, in Jolt, planner and validator; no audit |
| RoKoko | SNARK/PCS | 157 KB [M] (109–115 KB per Akita) | 7–13 ms [M]; polylog | 18 s commit + 9 s prove, 1 thr [M] | No (q ≈ 2^50, almost-split) | **vSIS**; 2^-100 stat.; heuristic challenges | Yes | Rust, open source; past impl bugs |
| Grand Danois | PCS | ~80 KB @2^32 [E] | polylog | – | No | vSIS + MSIS | Yes | paper only |
| Maltese | PCS | 224–335 KB [E] | polylog (log^3 N ring ops) | linear | 32-bit q parameterized; power-of-two-style rings | MSIS (+heuristic inversion) | Yes | paper only |
| Hachi | PCS | ~55 KB [E] | ~227 ms [M] | ~270 s [M] | No | MSIS | Yes | prototype |
| SALSAA | SNARK/folding | ~1.46 MB [M] | 0.3 s–7 ms | 100s of s [M] | No | vSIS | Yes | Rust |
| SuperNeo | Folding | n/a (per-fold small) | log-size verifier circuit | pay-per-bit commit | **Adaptable** (any cyclotomic/extension), no 31-bit params | MSIS; ROM | **No: needs decider** | no impl |
| Symphony | Folding→SNARK | < 200 KB [E] | polylog + inner SNARK | ~3·2^32 Ajtai mults [E] | 64-bit q | MSIS; ROM (no FS in circuit) | via inner SNARK | estimates; 3rd-party use |
| LatticeFold(+), Cyclo, PikkuFold, ProtogaLattice | Folding | 5–200 KB per fold | – | – | No / partial | MSIS (vSIS for some) | No | partial |

## 4. Recommendation

### Most promising: Akita as the PCS under a sum-check (Spartan/Jolt-style) PIOP, i.e. the "Lattice Jolt" stack, over Akita's p64 or p128 field with near-native BabyBear emulation

Why:

1. **It is the only lattice scheme with measured, implemented numbers at our scale that meet every size and verifier target.**
   - 64–72 KB PCS proofs at N = 2^30 [M].
   - Complete Jolt proofs under 100 KB up to 2^27 cycles [M].
   - 16–40 ms single-thread verify [M].
   - A projected wrap proof of about 80–120 KB [I] is inside the ≤ 300 KB bound and near the 100 KB ideal.
2. **Standard Module-SIS**, unlike the vSIS schemes (RoKoko, Grand Danois, SALSAA).
3. **Engineering maturity:** open-source Rust in a production-track zkVM, an automated parameter planner with an independent validator, distributed proving, and a vendor-reported Metal GPU path.
4. **Prover cost [I]:**
   - Commitment work is NTT-based Ajtai on small digits, which suits GPUs. 2^30 coefficients take about 6 s on 8 CPU threads.
   - A 2^28–2^30-constraint wrap should fit a "seconds to about a minute" budget on 8×H200 once ported.
   - No GPU lattice SNARK implementation exists yet. This is the main engineering cost.
5. **Fixed circuit:** the wrap circuit (repeated SHA-512 plus Ext12 blocks) is uniform. Its constraint MLEs can be evaluated by the verifier in polylog time, as in Jolt or Spartan for uniform R1CS. The total verifier is then dominated by Akita's ms-scale check.

Gaps to close:

- **QROM:** there is no QROM knowledge-soundness proof (the authors list it as future work). This misses "proven bounds vs 2^64 quantum queries"; the bound is classical-ROM only.
- **Field:** BabyBear is not native. Use p64 or p128 emulation (§2), or fund a BabyBear/Φ_37 variant.
- **Heuristics:** the completeness-side response model is heuristic.
- **Audit:** none.

### Runner-up: RoKoko

- **Strengths:** a genuinely **polylog verifier** (7–13 ms [M]), the fastest lattice prover measured (about 27 s single-thread at 2^30, commit plus prove), and 109–157 KB proofs [M]. It still fits ≤ 300 KB.
- **Why second:**
  - vSIS assumption.
  - Only a 100-bit statistical soundness target, which would need re-parameterization to reach 2^-128.
  - Heuristic challenge invertibility.
  - q ≈ 2^50, which is not BabyBear.
  - High RAM (about 37 GiB at 2^30).

### Research path worth tracking

**SuperNeo-style BabyBear-native Ajtai commitments** over Φ_37 or Φ_81-type rings (inert or 2-factor for BabyBear, with Ext12 ⊂ F_{p^36}). Combined with an Akita-style recursive opening, this would give a natively BabyBear plus Ext12 lattice PCS. Nobody has published this yet [I].

**Maltese** is the only standard-MSIS polylog-verifier PCS, but it is about 335 KB, estimates only, with no timings.

## 5. Caveats common to all lattice candidates

- **QROM:** none of the practical schemes (Akita, RoKoko, SALSAA, Neo, Maltese, Symphony) proves multi-round Fiat–Shamir knowledge soundness in the QROM. Only the MB-size CMNW construction claims quantum knowledge soundness. If proven PQ bounds are a hard requirement, hash-based WHIR/STIR wraps currently have the stronger story.
- **Concrete MSIS security** comes from lattice-estimator Core-SVP models (ADPS16 or MATZOV), not reductions with tight constants.
- **Bugs and recent corrections:** the area has had recent security-relevant fixes, including Akita App. F's list and "Soundness failures in LaBRADOR implementations from NTT-friendly rings" (Raikos–Wong). Budget for independent review.
