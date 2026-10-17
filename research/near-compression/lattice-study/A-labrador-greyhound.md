# LaBRADOR / Greyhound as a final wrap layer for a SWIRL/WHIR recursive STARK

Date: 2026-10-17. This is a read-only literature study. Sources are saved in this directory:
- `2022_1341.{pdf,txt}`: LaBRADOR, Beullens–Seiler, ePrint 2022/1341. Note: the Wayback copy is the **Oct 2022** revision, numbered sections 1–6. The CRYPTO'23 version moves R1CS to section 7. Table numbers are the same.
- `2024_1293.{pdf,txt}`: Greyhound, Nguyen–Seiler, CRYPTO'24, ePrint 2024/1293 (Aug 2024 revision).
- `2024_1846`: LaZer library (Lyubashevsky–Seiler–Steuer, CCS'24).
- `2026_1289`: ZK-LaBRADOR benchmarks in LaZer (Biasioli et al., 2026).
- `2026_2103`: LaBinius (Osadnik–Seiler, 2026). It uses LaBRADOR as a recursive compressor for SHA-256, Keccak and BLAKE3, and it is the closest thing to our use case.
- From the sibling `pdf/` directory: RoKoko (`pdf/2026_575`), Hachi (`pdf/2026_156`), AFK21 multi-round FS (`pdf/2021_1377`), DFM20 QROM measure-and-reprogram (`pdf/2020_282`).
- Web only: ICICLE v4 LaBRADOR (ingonyama.com/post/lets-labrador, github.com/ingonyama-zk/icicle-labrador, hackmd.io/@Ingonyama/fast-labrador-prover).

Labels used throughout: **[M]** = measured in a cited paper, **[P]** = paper's own estimate or formula, **[I]** = my inference or extrapolation.

---

## 0. Bottom line

1. **Proof size is not the problem.** LaBRADOR proofs are about 47–58 KB for anything from 2^10 to 2^25 constraints [M, Tables 1–2]. Size grows by roughly 1 KB per doubling, and the last recursion level alone is about 31 KB [M, Table 3]. With LaBRADOR as the compressor, LaBinius gets SHA-256 proofs of 86–100 KiB at a 100-bit target [M, LaBinius Tables 3, 6]. Even after re-parameterizing for our security contract, a 2^26–2^29-constraint statement should come in well under 300 KB, probably at 60–150 KB [I].
2. **The verifier is the problem.** LaBRADOR's verifier is linear in the statement, including the R1CS matrices. Greyhound's verifier is O(√N): 2.8 s at N=2^30 on one core [M, Greyhound Table 2]. LaBinius+LaBRADOR verifies 65K SHA-256 compressions in 0.73 s [M, Table 6]. Only the newer vSIS-based RoKoko reaches milliseconds: 13 ms at 2^30, with a 157 KB proof [M, RoKoko Table 1]. RoKoko is in the sibling agent's scope.
3. **The security contract is not met as published.**
   - "128-bit" means classical Core-SVP using the BDGL sieve (0.292β). Interactive knowledge error is 2^-125 per main-protocol invocation, plus a sum over the recursion levels (Thm 5.1, Lemma 3.7).
   - There is no QROM analysis. No analysis covers Fiat–Shamir with Q=2^64 queries either.
   - Generic multi-round FS loses (Q+1)^μ in the ROM (AFK21). That improves to a linear Q loss only for (k1..kμ)-special-sound protocols. In the QROM the loss is O(Q^{2n}) (DFM20).
   - Meeting 2^-128 at Q=2^64 therefore needs new parameters and a new proof [I].
4. **BabyBear cannot be native.** LaBRADOR, Greyhound and Hachi need q ≡ 5 (mod 8), a prime with low splitting, so that short challenge differences are invertible. BabyBear p ≡ 1 (mod 2^27) splits X^d+1 completely, so q = p_BB breaks the extraction lemma. Native mod-p arithmetic is possible only via newer decoupled-modulus designs (LaBinius-style), or via the composite-modulus route ICICLE took, which has no published proof [I].
5. **SHA-512 arithmetization cost.** In binary R1CS a SHA-512 compression costs about 5–6×10^4 constraints [I]. 2,000–9,000 compressions is therefore about 2^27–2^29 binary constraints. That is past the published q ≈ 2^32 parameter range: Thm 6.2 needs n+3k < 15q/128, i.e. k ≲ 2^26.9. BabyBear-Ext12 arithmetic emulated in binary or mod 2^64+1 R1CS adds about 2^27–2^30 more [I]. The total is about 2^28–2^30.5 constraints.

---

## 1. Proof size versus statement size

### 1.1 LaBRADOR closed form (2022/1341 §5.7)

One main-protocol level with Fiat–Shamir costs, in bits:

- Outer commitments: (κ1+κ2)·d·log q
- JL projection: 256·log(12β/√2)
- JL proof: ⌈128/log q⌉·d·log q
- Challenge seeds: 4·128

The last level also sends its full witness: masked opening z̃, inner commitments t_i, and garbage terms g_ij, h_ij, giving

n·d·log(12β√(τ/nd)) + r·κ·d·log q + (r²+r)/2·d·log(12√(2/(r²nd))β²) + (r²+r)/2·d·log q.

§5.6 reduces the last level to 2r−1 and 2ν+1 garbage terms. Each level shrinks the witness from |s| to O(|s|^{2/3}) (§1.1), so there are O(log log n) levels. In practice 6–7 levels are used.

Parameters used [P/M, §6.1]:

| Parameter | Value |
|---|---|
| Ring degree d | 64 |
| Modulus q | ≈ 2^32, X^64+1 splits into two factors |
| Challenges | 23 zeros, 31 coefficients ±1, 10 coefficients ±2 |
| Challenge norms | ℓ2 norm τ = 71, operator norm T ≤ 15 after rejection (about 6 samples on average) |
| Challenge set size | > 2^128 (§2) |
| Commitment ranks κ, κ1, κ2 | Chosen per level for 128-bit MSIS |

### 1.2 Measured tables [M]

**Table 1, R1CS mod 2^64+1 (KB):**

| Constraints | 2^10 | 2^12 | 2^14 | 2^16 | 2^18 | 2^20 |
|---|---|---|---|---|---|---|
| Proof size (KB) | 47 | 49 | 52 | 54 | 57 | 58 |

**Table 2, binary R1CS with n = k (KB):**

| Constraints | 2^20 | 2^21 | 2^22 | 2^23 | 2^24 | 2^25 |
|---|---|---|---|---|---|---|
| Proof size (KB) | 49.02 | 49.37 | 51.47 | 51.60 | 52.70 | 53.84 |

**Table 3, recursion levels for binary R1CS at 2^25:**

| Level | Witness | Output |
|---|---|---|
| R1CS→R | 4,096 KB | 0.5 KB |
| L1 (n=37,450, r=112) | 32,768 KB | 3.98 KB |
| L2 | 5,107 KB | 3.99 KB |
| L3 | 713 KB | 3.52 KB |
| L4 | 196 KB | 3.37 KB |
| L5 | 85 KB | 3.34 KB |
| L6 | 56 KB | 4.22 KB |
| L7 (last level, full witness sent) | 41 KB | 30.91 KB |
| **Total proof** | | **53.84 KB** |

### 1.3 Greyhound (2024/1293)

Greyhound is a PCS for f ∈ Z_q[X] of degree < N, with q ≈ 2^32 and d = 64.

| N | Proof size [M, Table 1] |
|---|---|
| 2^26 | 46 KB |
| 2^28 | 53 KB |
| 2^30 | 53 KB |

The Greyhound layer itself contributes 3.75–4.25 KB; the rest is LaBRADOR (§5, Table 4). The implementation uses only power-of-two decomposition bases and local per-layer optimization, so these sizes are "not the best possible" (§6).

### 1.4 What would 2^26–2^29 constraints cost? [I]

- **Raw extrapolation.** Size grows about 1 KB per doubling, so 2^26→2^29 gives about 55–58 KB at the paper's parameters.
- **Caveat 1: the norm/overflow conditions cap the statement size at q ≈ 2^32.**
  - Binary R1CS (Thm 6.2) needs n+3k < 15q/128 ≈ 5.0×10^8. With n = k, that means k ≲ 1.26×10^8 ≈ 2^26.9. So 2^27–2^29 binary constraints need log q ≈ 34–36, or the statement split across several witnesses or reductions.
  - R1CS mod 2^64+1 (Thm 6.3) needs (n+(3+l)k)·d < 0.3q with l = 8 and d = 64. That gives k ≲ 1.7×10^6 ≈ 2^20.7, which is why Table 1 stops at 2^20. For 2^26+ arithmetic constraints q must be about 2^40 or more.
  - Size scales roughly with log q in the final message, so expect +10–30%.
- **Caveat 2: re-parameterizing for 2^-128 after FS with Q = 2^64 (§2).** This needs larger challenge sets or extra repetitions and larger MSIS ranks. My guess is about +20–60% size.
- **Estimate.** 60–100 KB for pure LaBRADOR. 85–150 KB for a LaBinius/Greyhound-style PCS plus LaBRADOR stack. Both are well under 300 KB.
- **Does size depend on the modulus or ring degree?** Yes, through d·log q per ring element and through the MSIS ranks needed for a given norm. It hardly depends on N: the last level dominates and is roughly constant.

---

## 2. Security parameters

- **What "128-bit" means.** §6.1 estimates MSIS hardness "using the Core-SVP methodology [ADPS16] with the BDGL sieve [BDGL16]". That is the classical 2^{0.292β} cost model, with no quantum sieving.
  - Under the quantum Core-SVP exponent 0.265β, the same block size gives about 128·0.265/0.292 ≈ 116 bits [I].
  - LaBinius instead uses the Lattice Estimator with module-BKZ/subfield attacks [DEdP25] and targets **λ = 100** (§5.1.8).
  - RoKoko uses λ = 128 for SIS but FS/knowledge error κ = 2^-100 (§2.3).
- **Main protocol soundness (Thm 5.1).**
  - Knowledge-sound with ε0 = 2^-125 and norm slack √(128/30) ≈ 2.07. The extracted witness has norm ≤ 2.07β.
  - It needs MSIS hard for rank κ1 = κ2 at norm 2β′, and for rank κ at norm max(8T(b+1)β′, 2(b+1)β′ + 4T·2.07β′).
  - It needs β ≤ √(30/128)·q/125. This comes from the strengthened modular JL lemma, Lemma 4.2, which needs b ≤ q/125.
  - Remark 5.2: under recursion the MSIS norms must be scaled up by the slack again.
- **Composition (Lemma 3.7).** Soundness errors add, so 7 levels give ≈ 7·2^-125 plus the R1CS reduction error.
- **R1CS reduction soundness.**
  - Binary R1CS: 2^-l from l random F2 combinations (Thm 6.2), with the MSIS ℓ∞ bound equal to 1.
  - R1CS mod 2^64+1: 2·p^-l where p = 274177 (18 bits), so l = ⌈128/18⌉ = 8 repetitions (Thm 6.3).
- **Per-round components.**
  - Zq aggregation uses ⌈128/log q⌉ = 4 parallel combinations at q ≈ 2^32.
  - The JL projection has failure probability 2^-128 (Lemma 4.1).
  - The amortization challenge set has size about 2^128/6 after operator-norm rejection.
- **Heuristics.** Honest-norm estimates in §5.4 are heuristic, but the paper says this affects only completeness and size, not soundness.
- **Slack.** Extraction is relaxed:
  - LaBRADOR: weak openings (s*, c̄) with ‖c̄s*‖ ≤ β; binding needs MSIS at norm 4Tβ (§2).
  - Greyhound: relaxed relation R* (eq. 6) with ‖c_i·s_i‖ ≤ β̄ and ‖c_i‖₁ ≤ κ̄ = 2κ (Lemma 3.2).
  - Greyhound's knowledge error is r/|C| (§4.2).
- **Non-interactive security, which is what matters for our contract.**
  - Neither paper analyzes FS beyond "challenges expanded from seeds".
  - For (2μ+1)-move protocols, generic FS in the ROM loses (Q+1)^μ. For (k1..kμ)-special-sound protocols the loss is linear in Q (AFK21, abstract).
  - LaBRADOR mixes coordinate-wise-special-sound amortization with JL and Schwartz–Zippel-type steps, so whether it is cleanly (k1..kμ)-special-sound is unclear [I].
  - Even with a linear loss, Q = 2^64 gives 2^-125·2^64 ≈ 2^-61. That misses 2^-128 by 2^67. The interactive per-round error would need to be about 2^-192 [I].
  - In the QROM, the generic multi-round bound is O(Q^{2n}) (DFM20 §1). That is useless for LaBRADOR's roughly 20+ challenge rounds.
  - Quantum knowledge soundness for lattice protocols requires quantum rewinding (Lai–Malavolta–Spooner 2022/889, interactive only).
- **Conclusion [I].** A proven bound of 2^-128 against 2^64 QROM queries does not exist for LaBRADOR or Greyhound today. Getting there would need:
  - challenge sets of about 2^192 or more per amortization round (e.g. d = 128 challenges, or an extension-ring challenge);
  - ⌈192/log q⌉ aggregation repetitions;
  - a round-by-round or special-soundness QROM proof.

  The size cost of this is moderate; the proof work is not.

---

## 3. Verifier time and succinctness

- **LaBRADOR.** Prover and verifier are dominated by O(n) Zq multiplications (§1). For binary R1CS the verifier must compute δ_i = Lift(α_iA^T + β_iB^T + γ_iC^T) (Fig. 4), which is O(nnz(A,B,C)) per repetition. A uniform circuit does not help unless the matrices have an MLE-evaluable structure.
- **Measured verifier times.**

| Source | Workload | Verify time | Hardware |
|---|---|---|---|
| ZK-LaBRADOR in LaZer [M, 2026/1289 Table 1] | 2^16 polynomials of degree 512 ≈ 2^25 coefficients (LaBRADOR on a hash-like statement) | 9.3 s (not zk), 9.7 s (zk) | 1 Tiger Lake core |
| Greyhound [M, Table 2] | N = 2^26 / 2^28 / 2^30 | 0.49 / 1.15 / 2.80 s | 1 Sapphire Rapids core |
| Greyhound, re-measured [M, RoKoko Table 8] | N = 2^30 | 1.73 s | Xeon |
| LaBinius+LaBRADOR [M, Table 6] | 65,536 SHA-256 compressions under Flock | 731 ms | 1 core |
| LaBinius+LaBRADOR [M, Table 6] | 16,384 SHA-256 compressions under Flock | 393 ms | 1 core |
| LaBinius+LaBRADOR [M, Table 3] | SHA-256 under Binius | 0.36–3.2 s | 1 core (Binius verifier walks every constraint, non-succinct) |
| Hachi [M, abstract] | — | 12.5× faster than Greyhound, about 55 KB | — |
| RoKoko [M, Table 1] | N = 2^26 / 2^28 / 2^30 | 7.5 / 8.0 / 13.1 ms, 157 KB proof | laptop core |

  Greyhound's verifier is O(√N) (Table 3).

- **Getting a succinct verifier for a fixed uniform circuit [I].** LaBRADOR itself has no holography. Practical options:
  - **(a) Front-end plus lattice PCS (recommended shape).** Use a sumcheck-based PIOP over a uniform AIR or CCS (Spartan/HyperPlonk/Binius/Flock style). The verifier evaluates the uniform constraint polynomial at one random point in O(log N), and LaBRADOR (or Greyhound, Hachi, RoKoko) proves only the PCS opening. This is exactly LaBinius's architecture. The verifier is then √N with Greyhound/LaBRADOR (hundreds of ms to seconds) or polylog with RoKoko (ms).
  - **(b) Spartan-style computation commitments (SPARK).** Commit to the sparse A, B, C once in preprocessing with the lattice PCS. The verifier then checks evaluation proofs of the matrix MLEs instead of reading them.
  - **(c) Parallel verification.** The LaBRADOR verifier is a large matrix-vector product, so it parallelizes trivially. Even so, about 2^29 constraints means seconds on 64 cores, so this does not reach ms.

---

## 4. Prover time and memory

| System | Workload | Prover time | Hardware | Label |
|---|---|---|---|---|
| Greyhound | N = 2^26 | commit 4.37 s + prove 2.03 s | 1 core, Sapphire Rapids 3.2 GHz, AVX-512 | [M, Table 2] |
| Greyhound | N = 2^28 | 21.2 + 8.21 s | same | [M, Table 2] |
| Greyhound | N = 2^30 | 132 + 41.2 s | same | [M, Table 2] |
| Greyhound | N = 2^30 | 88 + 27 s | Xeon 8562Y+ | [M, RoKoko Table 8] |
| Greyhound and SALSAA | N = 2^30 | needed > 64 GiB RAM | — | [M, RoKoko Remark 6] |
| LaZer ZK-LaBRADOR | about 2^25 coefficients | 27.9 s zk / 26.6 s not zk | 1 core | [M, 2026/1289 Table 1] |
| LaZer ZK-LaBRADOR | 2^21 coefficients | 1.9 s | 1 core | [M, 2026/1289 Table 1] |
| LaBinius+LaBRADOR, SHA-256 (Flock) | 4,096 compressions | 0.44 s, 85.7 KiB | 1 core, EPYC 9R05 | [M, Table 6] |
| LaBinius+LaBRADOR, SHA-256 (Flock) | 16,384 compressions | 1.09 s, 99.3 KiB | same | [M, Table 6] |
| LaBinius+LaBRADOR, SHA-256 (Flock) | 65,536 compressions | 3.17 s, 96.5 KiB | same | [M, Table 6] |
| LaBinius+LaBRADOR, SHA-256 (Binius) | 72,628 compressions | 6.9 s, 97.7 KiB | same | [M, Table 3] |

Further notes:
- Greyhound's prover is O(N) (§4.3).
- In LaBinius, LaBRADOR's recursive part grows as about √N. The recursive mode costs < 1.5–2× the hash-based prover. All LaBinius numbers are at 100-bit security.
- LaBRADOR asymptotics: prover O(n) ring operations; garbage cross-terms cost O(r′n′²) = O(N^{2/3}) (Greyhound §4.3).
- Implementation (lattice-dogs/labrador): C with AVX-512, single-threaded, multi-modular NTT over 12–14-bit primes, explicit CRT (Greyhound §6). The paper suggests a further speedup of up to 16× from 52-bit IFMA NTTs (§6.3).

**GPU.**
- Ingonyama ICICLE v4 (July 2025) ships a CUDA/C++ LaBRADOR (`icicle-labrador` demo).
- It uses ring Z_q[X]/(X^64+1) with q = p_BabyBear·p_KoalaBear, the "Baby-Koala" ring.
- **No benchmark numbers are published in text.** The repo has only a chart.
- The hackmd write-up says the aggregation-step repetitions "should be repeated … for security, but this was omitted for simplicity". So it is **not at full soundness**.
- [I] Both prime factors split X^64+1 completely (p_BB ≡ 1 mod 2^27, p_KB ≡ 1 mod 2^24). The [LS18] invertibility of challenge differences that Thm 5.1 relies on therefore does not apply, and the soundness of this configuration is unproven.
- I found no other GPU LaBRADOR or Greyhound implementations.

**Projection for our wrap [I].**
- 2^28–2^30 binary-R1CS-equivalent constraints means a committed witness of about 2^30–2^32 small coefficients.
- Single-core Greyhound/LaBRADOR scaling suggests 200–1,000 core-seconds.
- The commit is a highly parallel Ajtai matrix-vector product (NTT plus pointwise), so with 100–400 cores or a GPU port, a few seconds is plausible. Memory needs are tens to hundreds of GB.
- The LaBinius route is much better. 9,000 SHA-512 compressions ≈ 22,500 SHA-256-equivalents by work (about 2.5×) gives about 1–1.5 single-core seconds for the hash part, before the BabyBear arithmetic.

---

## 5. Arithmetization

- **Principal relation (§5.1).** The witness is s1..sr ∈ R_q^n with Σ‖s_i‖² ≤ β². Constraints are quadratic dot-product functions Σ a_ij⟨s_i, s_j⟩ + Σ⟨φ_i, s_i⟩ − b, either required to vanish in R_q (family F) or only in the constant term (family F′, i.e. a Zq-quadratic constraint on coefficient vectors via the σ−1 automorphism, §2).
- **Front ends provided (§6).**
  - **Binary R1CS (Fig. 4).** Commit a, b, c, w as 0/1 coefficient vectors. Bitness is proven via ct⟨a, σ−1(a) − 1⟩ = 0 plus the norm bound. a∘b = c is proven via "a+b−2c is binary", a trick from GOS12. Linear F2 relations are proven via l random combinations with mod-2 checks. Each binary constraint costs about 3 witness bits, with no per-constraint ring multiplications.
  - **R1CS mod 2^d+1 (Fig. 5).** Uses the morphism X ↦ 2, NAF encodings with coefficients in {−1, 0, 1}, and l = 8 masked Hadamard checks.
  - **Mixed binary and mod 2^d+1** are proven in one execution (§6, "Mixing"), e.g. for hashing plus arithmetic in Dilithium.
- **SHA-512 compression in binary R1CS [I].** XOR and rotations are free (linear over F2). Ch and Maj cost 64 AND constraints each per round. Each 2-input 64-bit modular addition needs about 64 carry constraints (carry = maj(a, b, c_in)).
  - Per round: T1 needs 4 additions, plus T2, e, a, giving about 7 additions·64 + 128 ≈ 576 constraints. Over 80 rounds ≈ 46K.
  - Message schedule: 64 words × 3 additions × 64 ≈ 12K.
  - Feed-forward: 8×64.
  - Total: **≈ 5.5–6×10^4 binary constraints per compression**, or about 4.5×10^4 with carry-save multi-operand adders. Witness is about 3× that in bits.
  - For comparison, the same count for SHA-256 is about 2.3×10^4.
  - So 2,000–9,000 compressions ≈ 1.1×10^8–5.4×10^8 ≈ 2^26.7–2^29.0 constraints.
- **BabyBear (p = 2^31−2^27+1) arithmetic.**
  - **Native q = p_BB? No, not with LaBRADOR, Greyhound or Hachi.** The relation itself would work: ct-constraints mod q with digit-decomposed short witnesses (Greyhound's gadget G_b) give exact mod-p linear and quadratic constraints. The extraction argument is what fails. It needs X^d+1 to split into few factors mod q (LaBRADOR §2; Greyhound/Hachi use q ≡ 5 mod 8, [LS18] Lemma; Hachi q = 4294967197). BabyBear splits X^64+1 completely, so short challenge differences can be non-invertible (LaBinius §1 spells out this exact obstruction).
  - **Composite q = p_BB·q′.** This does not help: the p_BB component still splits.
  - **Decoupled-modulus designs.** LaBinius (commitment over an NTT-friendly composite modulus, extraction over the number field, evaluation field decoupled) or Akita/Hachi-style extension-field evaluation could in principle carry an F_{p^k} claim. LaBinius only instantiates F_{2^162} [I].
  - **Emulation in binary R1CS.** A 31×31 multiplication plus mod-p reduction costs about 1–2.5K constraints. An Ext12 multiplication needs 23 base multiplications using point-evaluation (2k−1) Karatsuba, plus reduction. That is about 3–5×10^4 constraints per Ext12 multiplication, and 10^5–10^6 multiplications give 2^31.5–2^35. **Infeasible at the high end** [I].
  - **Emulation in R1CS mod 2^64+1** (the integer product of 31-bit values fits without wrap). Use a·b = c + p·t with c and t range-checked by bit decomposition in the mixed binary system. That is about 23 product constraints plus 12 reductions of about 40 bits each, ≈ 500 constraints per Ext12 multiplication. 10^5–10^6 multiplications give about 2^25.6–2^29 constraints, and q must grow to about 2^40+ (Thm 6.3) [I].
  - **Binius64-style front ends** with native 64-bit integer multiplication constraints, combined with LaBinius, would make BabyBear multiplication a handful of constraints. That is the most promising route but has not been measured [I].

---

## 6. Assessment for the nearproof wrap [I]

- **Size: fine.** Even pessimistic re-parameterization lands at about 100–150 KB, versus about 400 KB for hash-only designs.
- **Verifier.** Pure LaBRADOR over 2^28–2^30 R1CS is seconds to tens of seconds: too slow and too large a statement. The viable shape is a uniform-AIR sumcheck front end, plus a lattice PCS, plus LaBRADOR compression (as in LaBinius). That gives about 0.3–1 s verify (√N) at about 100 KB. A ms verifier needs a RoKoko-class PCS at about 157 KB+, with vSIS and κ = 2^-100 as published.
- **Security.** Not available off the shelf for "2^-128 vs 2^64 QROM queries, proven". As published, LaBRADOR is 2^-125 interactive with no FS/QROM bound; LaBinius is 100-bit; RoKoko is κ = 2^-100. Re-parameterizing and writing a QROM argument is a research task.
- **Arithmetic mismatch.** SHA-512 wants a binary field, BabyBear wants F_p, and LaBRADOR wants q ≡ 5 mod 8. Any design needs either emulation (cost dominated by the Ext12 multiplications) or a two-domain or decoupled commitment.
