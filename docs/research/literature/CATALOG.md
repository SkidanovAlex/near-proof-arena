# Literature catalogue — entries

Companion to [INDEX.md](INDEX.md) (topic index), [OPPORTUNITIES.md](OPPORTUNITIES.md) and [refs.bib](refs.bib).

Each item appears once, under its primary topic; INDEX.md lists it under every topic it touches.

**Relevance codes:** U = used in our stack or proofs · E = evaluated, kept or on watch · R = evaluated and rejected · C = cited only (background or reading list) · N = not yet evaluated.

**Paths:** `branch:path` means the file is on that lane branch, not on main. A path without a prefix is on main. Lane paths are the first branch where the file was found; most lane files also exist on sibling PQ lanes.

**Numbers** are as reported by the source (or as measured by our lanes, where marked). "Proven" vs "conjectured" security is the source's own classification unless noted.


## T1. Hash-based IOPPs and polynomial commitments


### [CF26]

- **Citation:** Chai, Fan. *FRI Soundness Above Johnson via Threshold Halving*. ePrint 2026/858, 2026. <https://eprint.iacr.org/2026/858>
- **Topics:** T1, T2 · **Relevance:** R — evaluated-rejected (worse than Johnson per query at our rates)
- **Gives:** Error (1-delta/2)^q above Johnson; Lean claim.

### [LXYYZ26]

- **Citation:** Z. Li, C. Xing, Y. Yao, C. Yuan, R. Zhu. *How to Fold Linear Error-Correcting Codes with Optimal Proximity Gaps*. ePrint 2026/2133, 2026. <https://eprint.iacr.org/2026/2133>
- **Topics:** T1, T2 · **Relevance:** R — evaluated-rejected (more bytes/bit at our low rate)
- **Gives:** FRI-style folding IOPP for folded RS / multiplicity codes at radius 1-R-eps; needs folding m >= 4R(2-R)/eps^2.
- **Numbers:** Their tables: eps 0.25-0.35, m=16-32; smaller field, not smaller proofs.
- **Where in repo:** `lane/pq-native-hermetic:docs/logs/pq-final-layer-model-2026-10-17.md`, `docs/research/NOVEL-FINDINGS.md`

### [SWIRL]

- **Citation:** OpenVM team (Axiom). *SWIRL: the OpenVM 2.0 proof system (stark-backend v2: LogUp-GKR, zerocheck, stacking, WHIR)*. whitepaper, openvm.dev/swirl.pdf, 2026. <https://openvm.dev/swirl.pdf>
- **Topics:** T1, T6, T7 · **Relevance:** U — used (pinned stark-backend d667af5; SHA-384/Ext12 port)
- **Gives:** Our base proof system: heterogeneous-table stacking into one WHIR commitment, LogUp-GKR interactions, univariate-skip zerocheck.
- **Numbers:** OpenVM 2.0 beta claims <300 kB at 100-bit provable PQ (Poseidon2); Cor. 4.2.6 quantum bounds Theta(Q*eps) without constants.
- **Where in repo:** `lane/pq-native-hermetic:docs/logs/direct-wasm-pq-compression-2026-10.md`, `lane/pq-native-hermetic:docs/logs/pq-final-layer-model-2026-10-17.md`, `lane/pq-recursion-sha384:research/near-compression/results/pq-recursion-sha384/README.md`, `lane/pq-recursion-sha384:research/near-compression/results/pq-recursion-nv/README.md`, `lane/pq-final-soundness:research/near-compression/final-soundness/PROOF.md`

### [Ska26]

- **Citation:** C. Skatharoudis. *SoK: Hash-Based Polynomial Commitments and Low-Degree Tests: From FRI to Basefold, STIR, and WHIR*. ePrint 2026/1367, 2026. <https://eprint.iacr.org/2026/1367>
- **Topics:** T1, T3 · **Relevance:** C — cited (abstract only)
- **Gives:** Survey of hash-based PCS / LDT soundness.
- **Where in repo:** `lane/pq-weak-binding:research/near-compression/weak-binding/ANALYSIS.md`

### [GMW25]

- **Citation:** A. Garreta, N. Mohnblatt, B. Wagner. *A Simplified Round-by-round Soundness Proof of FRI*. ePrint 2025/1993, 2025. <https://eprint.iacr.org/2025/1993>
- **Topics:** T1, T9 · **Relevance:** N — not-yet-evaluated (template for WHIR rbr in Lean)
- **Gives:** Short rbr FRI proof; formalised in Lean (simple-rbr-fri).

### [HJRRR25-Jagged]

- **Citation:** T. Hemo, K. Jue, E. Rabinovich, G. Roh, R. D. Rothblum. *Jagged Polynomial Commitments (or: How to Stack Multilinears)*. ePrint 2025/917, 2025. <https://eprint.iacr.org/2025/917>
- **Topics:** T1, T7 · **Relevance:** E — evaluated (we implemented padding-free tight_heights instead)
- **Gives:** Commit all tables as one polynomial, paying only for used area (SP1 Hypercube).
- **Where in repo:** `lane/pq-native-hermetic:docs/logs/direct-wasm-pq-compression-2026-10.md`, `lane/pq-whir-levers:research/near-compression/results/pq-whir-levers/README.md`

### [Ligerito25]

- **Citation:** A. Novakovic, G. Angeris. *Ligerito: A Small and Concretely Fast Polynomial Commitment Scheme*. ePrint 2025/1187, 2025. <https://eprint.iacr.org/2025/1187>
- **Topics:** T1 · **Relevance:** N — not-yet-evaluated (255 KiB at 2^24: not smaller than WHIR)
- **Gives:** Linear-code PCS.
- **Numbers:** 255 KiB for 2^24.

### [SP1-Jagged]

- **Citation:** Succinct Labs. *Jagged polynomial commitments (SP1 Hypercube)*. docs.succinct.xyz/docs/sp1/hypercube/jagged, 2025. <https://docs.succinct.xyz/docs/sp1/hypercube/jagged>
- **Topics:** T1, T7 · **Relevance:** E — evaluated (relevant to stacking)
- **Gives:** Commit to many tables of different heights as one dense multilinear.
- **Where in repo:** `lane/pq-native-hermetic:docs/logs/direct-wasm-pq-compression-2026-10.md`

### [WHIR-rs]

- **Citation:** WizardOfMenlo / worldfnd. *whir (Rust reference implementation)*. GitHub, 2025. <https://github.com/worldfnd/whir>
- **Topics:** T1, T7 · **Relevance:** U — used (parameter regime cross-check)
- **Gives:** Reference WHIR code incl. params/regime.rs (unique, Johnson, capacity regimes).
- **Numbers:** Johnson agreement sqrt(rho)+eta, eta=sqrt(rho)/20; capacity cites STIR Conj. 5.6 (excluded).
- **Where in repo:** `lane/pq-native-hermetic:docs/logs/direct-wasm-pq-compression-2026-10.md`

### [ACFY24]

- **Citation:** G. Arnon, A. Chiesa, G. Fenzi, E. Yogev. *WHIR: Reed-Solomon Proximity Testing with Super-Fast Verification*. EUROCRYPT 2025; ePrint 2024/1586, 2024. <https://eprint.iacr.org/2024/1586>
- **Topics:** T1, T2 · **Relevance:** U — used (core PCS; Thm 5.2 consumed in PROOF.md Lemmas 4.3-4.7; x15 hypothesis edit)
- **Gives:** Constrained-RS IOPP and multilinear PCS; Thm 5.2 rbr soundness in unique/Johnson regimes; the PCS inside SWIRL.
- **Numbers:** Paper: ~63 KiB PCS example at 100-bit (conjectured). Ours: WHIR = 215-223 KB of the modelled 299-309 KB final layer.
- **Where in repo:** `lane/pq-final-soundness:research/near-compression/final-soundness/PROOF.md`, `lane/pq-x15-domains:research/near-compression/x15-domains/SOUNDNESS.md`, `lane/pq-native-hermetic:docs/logs/pq-final-layer-model-2026-10-17.md`, `lane/pq-whir-levers:research/near-compression/results/pq-whir-levers/README.md`, `docs/research/recursive-compression.md`, `docs/zk-formal/V3-D3A-STUDY.md`, `docs/zk-formal/V3-PERF-DESIGN.md`

### [ACY24-STIR]

- **Citation:** G. Arnon, A. Chiesa, E. Yogev. *STIR: Reed-Solomon Proximity Testing with Fewer Queries*. CRYPTO 2024; ePrint 2024/390, 2024. <https://eprint.iacr.org/2024/390>
- **Topics:** T1 · **Relevance:** R — evaluated-rejected (WHIR dominates for multilinear)
- **Gives:** Rate-shifting folding IOPP; fewer queries than FRI.
- **Where in repo:** `docs/zk-formal/V3-PERF-DESIGN.md`

### [ADK24]

- **Citation:** S. Atapoor, C. Delpech de Saint Guilhem, A. Kindi. *STARK-based Signatures from the RPO Permutation*. ePrint 2024/1553, 2024. <https://eprint.iacr.org/2024/1553>
- **Topics:** T1, T2 · **Relevance:** U — used (stark-plonky3 security table)
- **Gives:** Contains FRI rbr soundness theorems for unique-decoding (Thm 2) and Johnson (Thm 3) regimes used by Plonky3's ProvenSecurity calculator.
- **Numbers:** KoalaBear/Ext8, 104 queries, 20-bit PoW: proven UDR 102.5 bits, Johnson 128 (107 at q_H=2^64), conjectured 128.
- **Where in repo:** `examples/stark-plonky3/README.md`

### [BT24]

- **Citation:** A. R. Block, P. R. Tiwari. *On the Concrete Security of Non-interactive FRI*. ePrint 2024/1161, 2024. <https://eprint.iacr.org/2024/1161>
- **Topics:** T1, T3 · **Relevance:** C — cited (contract derivation)
- **Gives:** Concrete non-interactive FRI bounds; proven-vs-conjectured gap.
- **Where in repo:** `docs/research/recursive-compression.md`, `docs/zk-formal/V3-D3A-STUDY.md`, `docs/zk-formal/V3-PERF-DESIGN.md`

### [DP24-FRIBinius]

- **Citation:** B. E. Diamond, J. Posen. *Polylogarithmic Proofs for Multilinears over Binary Towers (FRI-Binius)*. ePrint 2024/504, 2024. <https://eprint.iacr.org/2024/504>
- **Topics:** T1 · **Relevance:** C — cited in pinned backend source (pcs-field-compatibility review)
- **Gives:** Ring-switching and FRI-Binius small-field multilinear PCS.
- **Where in repo:** `lane/pq-recursion-sha384:research/near-compression/results/swirl-security-review/pcs-field-compatibility/`

### [Zei24-BFLD]

- **Citation:** H. Zeilberger. *Basefold in the List Decoding Regime*. ResearchGate preprint, 2024. <https://www.researchgate.net/publication/387601318_Basefold_in_the_List_Decoding_Regime>
- **Topics:** T1, T2 · **Relevance:** C — cited (background)
- **Gives:** Basefold soundness up to Johnson.
- **Where in repo:** `lane/pq-native-hermetic:docs/logs/direct-wasm-pq-compression-2026-10.md`

### [DP23-Binius]

- **Citation:** B. E. Diamond, J. Posen. *Succinct Arguments over Towers of Binary Fields (Binius)*. EUROCRYPT 2025; ePrint 2023/1784, 2023. <https://eprint.iacr.org/2023/1784>
- **Topics:** T1, T8 · **Relevance:** E — evaluated (via Binius64 lane screen)
- **Gives:** Binary-tower PCS; efficient bitwise hashes.
- **Where in repo:** `lane/pq-native-hermetic:docs/logs/direct-wasm-pq-compression-2026-10.md`

### [ZCF23-Basefold]

- **Citation:** H. Zeilberger, B. Chen, B. Fisch. *BaseFold: Efficient Field-Agnostic Polynomial Commitment Schemes from Foldable Codes*. CRYPTO 2024; ePrint 2023/1705, 2023. <https://eprint.iacr.org/2023/1705>
- **Topics:** T1 · **Relevance:** N — not-yet-evaluated (WHIR chosen)
- **Gives:** Multilinear PCS from foldable codes (FRI-like with sumcheck).

### [GLSTW21]

- **Citation:** A. Golovnev, J. Lee, S. Setty, J. Thaler, R. S. Wahby. *Brakedown: Linear-time and field-agnostic SNARKs for R1CS*. CRYPTO 2023; ePrint 2021/1043, 2021. <https://eprint.iacr.org/2021/1043>
- **Topics:** T1 · **Relevance:** N — not-yet-evaluated (sqrt-size proofs; too large for final layer)
- **Gives:** Linear-time encodable-code (tensor) PCS; field-agnostic.

### [BBHR18]

- **Citation:** E. Ben-Sasson, I. Bentov, Y. Horesh, M. Riabzev. *Fast Reed-Solomon Interactive Oracle Proofs of Proximity (FRI)*. ICALP 2018, 2018. <https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ICALP.2018.14>
- **Topics:** T1 · **Relevance:** R — evaluated-rejected (superseded by WHIR in SWIRL)
- **Gives:** The FRI IOPP; folding-based RS proximity test underlying all STARK PCSs.
- **Where in repo:** `docs/research/recursive-compression.md`, `examples/stark-plonky3/README.md`

## T2. Proximity gaps, correlated agreement, list decoding


### [ABF26]

- **Citation:** G. Arnon, D. Boneh, G. Fenzi. *Open Problems in List Decoding and Correlated Agreement*. ePrint 2026/680, 2026. <https://eprint.iacr.org/2026/680>
- **Topics:** T2, T10 · **Relevance:** C — cited (formal-ecosystem ToyProblem §6) — prize problems = our capacity watch item
- **Gives:** Formalises the EF Proximity Prize grand challenges ($1M); MCA lower bound.
- **Where in repo:** `docs/research/formal-ecosystem.md`

### [DKT26]

- **Citation:** Q. Dao, S. D. Kominers, J. Thaler. *Reed-Solomon Codes Beyond Johnson: Efficient Decoding and Smaller Cryptographic Proofs*. ePrint 2026/2056, 2026. <https://eprint.iacr.org/2026/2056>
- **Topics:** T2 · **Relevance:** E — evaluated only as Plonky3 line-MCA citation — beyond-Johnson use NOT evaluated (see OPPORTUNITIES O-1)
- **Gives:** PROVEN RS list-decoding and MCA bounds below Johnson up to capacity (derivative method), needing large field characteristic; parameter certificates formally verified in ArkLib.
- **Numbers:** Reported savings at fixed security: ZisK final proof -13.2 KB (4.6 %), ProveKit -79.4 KB (11.1 %), LambdaVM subproofs -59.8 KB (4.9 %).
- **Where in repo:** `examples/stark-plonky3/README.md`

### [DKTZ26]

- **Citation:** Q. Dao, S. D. Kominers, J. Thaler, (Zheng). *Counterexamples to Beyond-Johnson Proximity Gaps over Binary Fields*. ePrint 2026/2424, 2026. <https://eprint.iacr.org/2026/2424>
- **Topics:** T2 · **Relevance:** N — not-yet-evaluated (confirms Johnson-only policy; affects binary-field Binius-type options)
- **Gives:** Beyond-Johnson proximity gaps fail over binary fields.

### [Gab26]

- **Citation:** A. Gabizon. *Linear list size bounds for Reed-Solomon beyond the Johnson radius*. ePrint 2026/2048, 2026. <https://eprint.iacr.org/2026/2048>
- **Topics:** T2 · **Relevance:** N — not-yet-evaluated (input to beyond-Johnson MCA)
- **Gives:** List size C(rho,alpha) n for agreement below sqrt(rho), large characteristic.

### [JLR26]

- **Citation:** F. G. Jeronimo, S. Liu, P. Rajpal. *Folded RS capacity proximity gaps (withdrawn)*. arXiv 2601.10047, 2026. <https://arxiv.org/abs/2601.10047>
- **Topics:** T2 · **Relevance:** R — evaluated-rejected (withdrawn)
- **Gives:** Withdrawn; subsumed by Goyal-Guruswami.
- **Where in repo:** `lane/pq-native-hermetic:docs/logs/pq-final-layer-model-2026-10-17.md`

### [Jer26]

- **Citation:** F. G. Jeronimo. *RS list decoding to 1-rho-gamma and MCA for curves*. arXiv 2609.05870 (unreviewed), 2026. <https://arxiv.org/abs/2609.05870>
- **Topics:** T2 · **Relevance:** R — evaluated-rejected (constants unusable)
- **Gives:** Capacity-regime RS result with error n^{O_gamma(1)}/q, constants unstated.
- **Where in repo:** `lane/pq-native-hermetic:docs/logs/pq-final-layer-model-2026-10-17.md`

### [Jo26]

- **Citation:** S. Jo. *Reed-Solomon Mutual Correlated Agreement Beyond the Johnson Radius*. ePrint 2026/1432, 2026. <https://eprint.iacr.org/2026/1432>
- **Topics:** T2 · **Relevance:** N — not-yet-evaluated (gain O(1/n) in radius: negligible for us)
- **Gives:** Deterministic MCA h integer steps past Johnson, error O(K^6/q), any evaluation set; Grand MCA Challenge entry.

### [KKH26]

- **Citation:** Krachun, Kazanin, U. Haböck. *Failure of proximity gaps close to capacity*. ePrint 2026/782, 2026. <https://eprint.iacr.org/2026/782>
- **Topics:** T2 · **Relevance:** N — not-yet-evaluated (confirms capacity exclusion)
- **Gives:** Counterexample near capacity over multiplicative subgroups of prime fields (our setting).

### [BCGM25]

- **Citation:** S. Bordage, A. Chiesa, Z. Guan, I. Manzur. *All Polynomial Generators Preserve Distance with Mutual Correlated Agreement*. CCC 2026 (LIPIcs 383); ePrint 2025/2051, 2025. <https://eprint.iacr.org/2025/2051>
- **Topics:** T2 · **Relevance:** U — used (Lemmas 4.2-4.3; ×15 domains)
- **Gives:** MCA for every polynomial generator up to 1-(1+1/2m)sqrt(rho), m>=3; explicit constant (Def 9.1/Thm 9.2), any evaluation set.
- **Numbers:** eps = sum_i (m+1/2)^7/(3 rho^1.5) d_i n^2/|F|: 2^-298 (m=3) at n=2^27, rho=2^-5, Ext12; 2^-279.7 at n=2^30.9 (×15).
- **Where in repo:** `lane/pq-final-soundness:research/near-compression/final-soundness/PROOF.md`, `lane/pq-native-hermetic:docs/logs/pq-final-layer-model-2026-10-17.md`, `lane/pq-x15-domains:research/near-compression/x15-domains/SOUNDNESS.md`, `lane/pq-x15-domains:research/near-compression/l4-study/C-invention.md`

### [BCHKS25]

- **Citation:** E. Ben-Sasson, D. Carmon, U. Haböck, S. Kopparty, S. Saraf. *On Proximity Gaps for Reed-Solomon Codes (improved Johnson-regime CA; negative results beyond Johnson)*. preprint Nov 2025 (math.toronto.edu/swastik); ePrint 2025/2055, 2025. <https://www.math.toronto.edu/swastik/rs-proximity-gaps-2025.pdf>
- **Topics:** T2 · **Relevance:** U — used (WHIR-rs and our backend calculator cite Thm 1.5; x15 check)
- **Gives:** Thm 1.5: CA up to Johnson with explicit (m+1/2)^5 constant for any evaluation set D; Thm 1.13: counterexamples on multiplicative subgroups beyond Johnson; Thm 4.6 exact-support form.
- **Numbers:** Error bound a > (2(m+1/2)^5 + 3(m+1/2)gamma*rho)/(3 rho^1.5) n + (m+1/2)/sqrt(rho).
- **Where in repo:** `lane/pq-x15-domains:research/near-compression/x15-domains/SOUNDNESS.md`, `lane/pq-native-hermetic:docs/logs/direct-wasm-pq-compression-2026-10.md`

### [CS25]

- **Citation:** E. Crites, A. Stewart. *On Reed-Solomon Proximity Gaps Conjectures*. ePrint 2025/2046, 2025. <https://eprint.iacr.org/2025/2046>
- **Topics:** T2 · **Relevance:** U — used (justifies excluding capacity regime)
- **Gives:** Counterexamples: capacity-regime proximity-gap / list-decoding conjectures used by 'conjectured' STARK security are false.
- **Where in repo:** `lane/pq-native-hermetic:docs/logs/pq-final-layer-model-2026-10-17.md`

### [DG25]

- **Citation:** B. E. Diamond, A. Gruen. *Proximity gaps result formalized in ArkLib (DG25)*. ePrint 2024/1351? [id unverified], 2025. <https://github.com/Verified-zkEVM/ArkLib>
- **Topics:** T2, T9 · **Relevance:** C — cited (formal status)
- **Gives:** Proximity-gap lemma (Diamond-Gruen) proven in ArkLib.
- **Where in repo:** `docs/research/formal-ecosystem.md`, `docs/research/checker-recommendations.md`

### [GG25]

- **Citation:** Z. Goyal, V. Guruswami. *Mutual correlated agreement for subspace-design codes (capacity regime)*. STOC 2026; ePrint 2025/2054, 2025. <https://eprint.iacr.org/2025/2054>
- **Topics:** T2 · **Relevance:** R — evaluated-rejected for proof size (NF-10)
- **Gives:** MCA up to list-decoding capacity for subspace-design (folded RS, multiplicity) codes.
- **Where in repo:** `lane/pq-native-hermetic:docs/logs/pq-final-layer-model-2026-10-17.md`

### [Hab25]

- **Citation:** U. Haböck. *A note on mutual correlated agreement for Reed-Solomon codes*. ePrint 2025/2110, 2025. <https://eprint.iacr.org/2025/2110>
- **Topics:** T2 · **Relevance:** C — cited (abstract only)
- **Gives:** Extends correlated agreement to MCA for RS; step used by our backend calculator.
- **Where in repo:** `lane/pq-native-hermetic:docs/logs/direct-wasm-pq-compression-2026-10.md`, `lane/pq-x15-domains:research/near-compression/x15-domains/SOUNDNESS.md`

### [ZKSEC-PROX25]

- **Citation:** zkSecurity. *The proximity conjecture (summary)*. blog.zksecurity.xyz, 2025-11-14, 2025. <https://blog.zksecurity.xyz/posts/proximity-conjecture/>
- **Topics:** T2, T10 · **Relevance:** C — cited
- **Gives:** Capacity conjecture disproved; proven region ~2x proof size vs conjectured.

### [BCIKS20]

- **Citation:** E. Ben-Sasson, D. Carmon, Y. Ishai, S. Kopparty, S. Saraf. *Proximity Gaps for Reed-Solomon Codes*. FOCS 2020; JACM 2023; ePrint 2020/654, 2020. <https://eprint.iacr.org/2020/654>
- **Topics:** T2 · **Relevance:** U — used (Johnson CA; ArkLib proves UDR part)
- **Gives:** Correlated agreement for RS up to unique decoding and Johnson radius (Thm 5.1).
- **Where in repo:** `lane/pq-final-soundness:research/near-compression/final-soundness/PROOF.md`, `docs/zk-formal/V3-PERF-DESIGN.md`, `examples/stark-plonky3/README.md`, `docs/research/formal-ecosystem.md`

## T3. Fiat–Shamir / BCS in the ROM and QROM; hashing, Merkle binding, grinding


### [AESgrind26]

- **Citation:** (authors not checked). *AES-Based Grinding for MPC-in-the-Head Signatures*. ePrint 2026/1625, 2026. <https://eprint.iacr.org/2026/1625>
- **Topics:** T3 · **Relevance:** N — not-yet-evaluated
- **Gives:** Classical grinding bound ~(4/3) eps Q/2^w.

### [BCG26]

- **Citation:** B. Bünz, B. Chen, Z. Guan. *It Takes Two: Proofs of Work for Fiat-Shamir*. ePrint 2026/2326, 2026. <https://eprint.iacr.org/2026/2326>
- **Topics:** T3 · **Relevance:** E — evaluated (abstract only, L4-A); classical — G-2 still needs a QROM statement
- **Gives:** Grinding needs non-amortizing PoW; XFS needs strong PoW; no single PoW is both with cheap verification; classical relativized ROM.
- **Where in repo:** `lane/pq-x15-domains:research/near-compression/l4-study/A-sequential-fs.md`, `docs/research/NOVEL-FINDINGS.md`

### [BHK26]

- **Citation:** C. Brzuska, P. Hubáček, Kalsta. *Simple Attacks Against (Extended) Fiat-Shamir*. PKC 2026 [unverified], 2026.
- **Topics:** T3, T6 · **Relevance:** N — not-yet-evaluated [unverified]
- **Gives:** Reported simpler GKR/PlonK FS attacks and an XFS counterexample.

### [CH26]

- **Citation:** A. Chiesa, Z. Hu. *Succinct Arguments for QMA in the Quantum Random Oracle Model*. ePrint 2026/2099, 2026. <https://eprint.iacr.org/2026/2099>
- **Topics:** T3 · **Relevance:** R — evaluated-rejected (abstract only; no weak binding)
- **Gives:** Quantum-state vector commitments.
- **Where in repo:** `lane/pq-weak-binding:research/near-compression/weak-binding/ANALYSIS.md`

### [CKMW26]

- **Citation:** T. Coratger, D. Khovratovich, B. Mennink, B. Wagner. *The Billion Dollar Merkle Tree*. CCS 2026; ePrint 2026/089, 2026. <https://eprint.iacr.org/2026/089>
- **Topics:** T3 · **Relevance:** N — not-yet-evaluated (classical; relevant to truncated-digest Merkle and weak binding)
- **Gives:** Position binding/extractability for Plonky3 Merkle trees with leaf pre-hashing even with non-CR compression.

### [Fen26]

- **Citation:** G. Fenzi. *How to Prove More False Statements: Fiat-Shamir Limitations on (Generated) R1CS*. ePrint 2026/1838, 2026. <https://eprint.iacr.org/2026/1838>
- **Topics:** T3, T6 · **Relevance:** N — not-yet-evaluated — relevant: chunk validation runs user contracts (generated statements)
- **Gives:** Extends KRS attacks to Spartan/Aurora with program-generated instances; mitigation: bind the generated statement before the first challenge.

### [HHMRS26]

- **Citation:** Huang, A. Hülsing, V. Maram, Ritsch, Saha. *Feistel Tools: Reprogramming and Query-Recording for QRPs*. ePrint 2026/146, 2026. <https://eprint.iacr.org/2026/146>
- **Topics:** T3 · **Relevance:** N — not-yet-evaluated (does not close G-1)
- **Gives:** QROM recording/reprogramming in the quantum random permutation model; post-quantum adaptive ZK (not soundness) for duplex-sponge FS.

### [HKKTW26]

- **Citation:** Herold, D. Khovratovich, Kudinov, S. Tessaro, B. Wagner. *Aborting Random Oracles: How to Build them, How to Use them*. CRYPTO 2026; ePrint 2026/016, 2026. <https://eprint.iacr.org/2026/016>
- **Topics:** T3 · **Relevance:** N — not-yet-evaluated (classical analogue for G-2)
- **Gives:** Grinding modelled as an aborting RO; clean classical grinding constants via indifferentiability.

### [MS26]

- **Citation:** C. Majenz, (Sharma). *Security of the Fischlin Transform in the Quantum Random Oracle Model*. arXiv 2602.17307, 2026. <https://arxiv.org/abs/2602.17307>
- **Topics:** T3 · **Relevance:** C — cited (abstract only) — compressed-oracle PoW counting: template for G-2
- **Gives:** QROM straight-line extraction for Fischlin.
- **Where in repo:** `lane/pq-lattice-qrom:docs/zk-formal/PQ-LATTICE-QROM-PLAN.md`

### [P3-CVE26]

- **Citation:** Plonky3. *CVE-2026-46654: FS transcript malleability in MultiField32Challenger*. CVE, 2026-06-10, 2026. <https://github.com/Plonky3/Plonky3>
- **Topics:** T3, T7 · **Relevance:** N — not-yet-evaluated (audit our SHA-384 absorption for injectivity; cf. GAPS G-9)
- **Gives:** Distinct transcripts gave identical challenges; fixed in 0.4.3/0.5.3.
- **Where in repo:** `lane/pq-final-soundness:research/near-compression/final-soundness/GAPS.md`

### [PFS26]

- **Citation:** (authors not checked). *Cryptanalysis of Poseidon-Based Fiat-Shamir Protocols*. ePrint 2026/409, 2026. <https://eprint.iacr.org/2026/409>
- **Topics:** T3, T8 · **Relevance:** C — cited (background)
- **Gives:** No FS forgeries found even with reduced-round Poseidon.

### [ACMT25]

- **Citation:** G. Alagic, J. Carolan, C. Majenz, S. Tokat. *The Sponge is Quantum Indifferentiable*. arXiv 2504.16887, 2025. <https://arxiv.org/abs/2504.16887>
- **Topics:** T3 · **Relevance:** E — evaluated (Poseidon2 / sponge option; not used)
- **Gives:** Sponge indifferentiability against quantum adversaries.
- **Where in repo:** `lane/pq-native-hermetic:docs/logs/direct-wasm-pq-compression-2026-10.md`

### [CDDGS25]

- **Citation:** A. Chiesa, M. Dall'Agnol, Z. Di, Z. Guan, N. Spooner. *Quantum Rewinding for IOP-Based Succinct Arguments*. TCC 2025; ePrint 2025/947 (arXiv 2411.05360 v2 withdrawn Oct 2025 — cite ePrint), 2025. <https://eprint.iacr.org/2025/947>
- **Topics:** T3 · **Relevance:** E — evaluated (interactive only)
- **Gives:** Post-quantum security of interactive Kilian arguments via quantum rewinding.
- **Where in repo:** `lane/pq-weak-binding:research/near-compression/weak-binding/ANALYSIS.md`, `lane/pq-lattice-qrom:docs/zk-formal/PQ-LATTICE-QROM-PLAN.md`

### [CDHZ25]

- **Citation:** A. Chiesa, Z. Di, Z. Hu, Y. Zheng. *How to Prove Post-Quantum Security for Succinct Non-Interactive Reductions*. EUROCRYPT 2026; ePrint 2025/2166, 2025. <https://eprint.iacr.org/2025/2166>
- **Topics:** T3 · **Relevance:** U — used (cross-check: 2^-130.4)
- **Gives:** Thm 11.3: adaptive straight-line QROM KS for one BCS step: 4k_sr+4k_ext+8k_off+4k_on.
- **Numbers:** One function call per round; no composition.
- **Where in repo:** `lane/pq-final-soundness:research/near-compression/final-soundness/PROOF.md`, `lane/pq-aic-research:research/near-compression/aic-research/REPORT.md`

### [CO25]

- **Citation:** A. Chiesa, M. Orrù. *A Fiat-Shamir Transformation from Duplex Sponges*. ePrint 2025/536, 2025. <https://eprint.iacr.org/2025/536>
- **Topics:** T3 · **Relevance:** E — evaluated (does not close G-1)
- **Gives:** Classical ideal-permutation analysis of duplex-sponge FS; QROM case listed open (§1.3).
- **Where in repo:** `lane/pq-final-soundness:research/near-compression/final-soundness/PROOF.md`, `lane/pq-final-soundness:research/near-compression/final-soundness/GAPS.md`, `docs/research/NOVEL-FINDINGS.md`

### [CF24-UC]

- **Citation:** A. Chiesa, G. Fenzi. *zkSNARKs in the ROM with Unconditional UC-Security*. ePrint 2024/724, 2024. <https://eprint.iacr.org/2024/724>
- **Topics:** T3 · **Relevance:** E — evaluated (classical only)
- **Gives:** Classical-style Merkle binding bounds.
- **Where in repo:** `lane/pq-x15-domains:research/near-compression/l4-study/B-openings.md`

### [CMNW24]

- **Citation:** V. Cini, G. Malavolta, N. K. Nguyen, H. Wee. *Polynomial Commitments from Lattices: Post-Quantum Security, Fast Verification and Transparent Setup*. ePrint 2024/281, 2024. <https://eprint.iacr.org/2024/281>
- **Topics:** T3, T5 · **Relevance:** C — cited (lattice plan)
- **Gives:** Extends quantum rewinding to coordinate-wise special soundness.
- **Where in repo:** `lane/pq-lattice-qrom:docs/zk-formal/PQ-LATTICE-QROM-PLAN.md`

### [CPZ24]

- **Citation:** J. Carolan, A. Poremba, M. Zhandry. *Quantum Indifferentiability and Pre-Computation*. arXiv 2410.16595, 2024. <https://arxiv.org/abs/2410.16595>
- **Topics:** T3 · **Relevance:** C — cited (background)
- **Gives:** Indifferentiability alone does not capture pre-computation.

### [DLS22]

- **Citation:** F. Dupuis, P. Lamontagne, L. Salvail. *Fiat-Shamir for proofs lacks a proof even in the presence of shared entanglement*. Quantum 8:1568 (2024); arXiv 2204.02265, 2024. <https://arxiv.org/abs/2204.02265>
- **Topics:** T3 · **Relevance:** C — cited (lattice C-security)
- **Gives:** Negative result for FS of proofs with entanglement.
- **Where in repo:** `lane/pq-lattice-qrom:research/near-compression/lattice-study/C-security.md`

### [MMW24]

- **Citation:** C. Majenz, G. Malavolta, M. Walter. *Permutation Superposition Oracles for Quantum Query Lower Bounds*. STOC 2025; ePrint 2024/1140, 2024. <https://eprint.iacr.org/2024/1140>
- **Topics:** T3 · **Relevance:** N — not-yet-evaluated (only for permutation hashes)
- **Gives:** Recording for two-sided random permutations; sponge preimage resistance.

### [RT24]

- **Citation:** L. Rotem, S. Tessaro. *Straight-Line Knowledge Extraction for Multi-Round Protocols*. ePrint 2024/1724, 2024. <https://eprint.iacr.org/2024/1724>
- **Topics:** T3 · **Relevance:** C — cited
- **Gives:** Cited in lattice QROM plan reading list.
- **Where in repo:** `lane/pq-lattice-qrom:docs/zk-formal/PQ-LATTICE-QROM-PLAN.md`

### [AFKR23]

- **Citation:** T. Attema, S. Fehr, M. Klooß, N. Resch. *The Fiat-Shamir Transformation of (Gamma_1..Gamma_mu)-Special-Sound Interactive Proofs*. JoC 2025; ePrint 2023/1945, 2023. <https://eprint.iacr.org/2023/1945>
- **Topics:** T3 · **Relevance:** C — cited (lattice QROM plan)
- **Gives:** Generalised special soundness FS.
- **Where in repo:** `lane/pq-lattice-qrom:research/near-compression/lattice-study/C-security.md`, `lane/pq-lattice-qrom:docs/zk-formal/PQ-LATTICE-QROM-PLAN.md`

### [BGKTTZ23]

- **Citation:** A. R. Block, A. Garreta, J. Katz, J. Thaler, P. R. Tiwari, M. Zając. *Fiat-Shamir Security of FRI and Related SNARKs*. ASIACRYPT 2023; ePrint 2023/1071, 2023. <https://eprint.iacr.org/2023/1071>
- **Topics:** T3, T1 · **Relevance:** N — not-yet-evaluated (template for rbr of WHIR/LogUp-GKR rounds)
- **Gives:** Round-by-round soundness of FRI, batched FRI and Plonk-like systems (delta-correlated protocols); ROM.

### [BGTZ23]

- **Citation:** A. R. Block, A. Garreta, P. Tiwari, M. Zając. *On Soundness Notions for Interactive Oracle Proofs*. ePrint 2023/1256, 2023. <https://eprint.iacr.org/2023/1256>
- **Topics:** T3 · **Relevance:** C — cited (contract)
- **Gives:** rbr soundness -> FS soundness transfer incl. QROM; soundness vs knowledge soundness.
- **Where in repo:** `docs/research/recursive-compression.md`, `docs/zk-formal/V3-D3A-STUDY.md`, `docs/zk-formal/V3-PERF-DESIGN.md`, `lane/pq-weak-binding:research/near-compression/weak-binding/ANALYSIS.md`, `lane/pq-lattice-qrom:research/near-compression/lattice-study/C-security.md`

### [Fai23]

- **Citation:** I. Faisal. *Interactive Oracle Arguments in the QROM and Applications to Succinct Verification of Quantum Computation*. ePrint 2023/421, 2023. <https://eprint.iacr.org/2023/421>
- **Topics:** T3 · **Relevance:** R — evaluated-rejected (not applicable)
- **Gives:** Checked for weak-binding QROM BCS; does not cover it.
- **Where in repo:** `lane/pq-weak-binding:research/near-compression/weak-binding/ANALYSIS.md`

### [Poseidon2]

- **Citation:** L. Grassi, D. Khovratovich, M. Schofnegger. *Poseidon2: A Faster Version of the Poseidon Hash Function*. AFRICACRYPT 2023; ePrint 2023/323, 2023. <https://eprint.iacr.org/2023/323>
- **Topics:** T3, T8 · **Relevance:** R — evaluated-rejected (U-7: SHA-384 throughout)
- **Gives:** Arithmetization-friendly permutation used by OpenVM/Plonky3.
- **Where in repo:** `lane/pq-native-hermetic:docs/logs/direct-wasm-pq-compression-2026-10.md`

### [SAFE23]

- **Citation:** J.-P. Aumasson, D. Khovratovich, B. Mennink, P. Quine. *SAFE: Sponge API for Field Elements*. ePrint 2023/522, 2023. <https://eprint.iacr.org/2023/522>
- **Topics:** T3 · **Relevance:** N — not-yet-evaluated (transcript-encoding reference)
- **Gives:** Sponge API / IO patterns for FS transcripts (heuristic).

### [AFK22]

- **Citation:** T. Attema, S. Fehr, M. Klooß. *Fiat-Shamir Transformation of Multi-Round Interactive Proofs*. TCC 2022; JoC 2023; ePrint 2021/1377, 2022. <https://eprint.iacr.org/2021/1377>
- **Topics:** T3 · **Relevance:** C — cited (lattice QROM plan)
- **Gives:** Tight classical ROM FS for (k1..kmu)-special-sound protocols.
- **Where in repo:** `lane/pq-lattice-qrom:research/near-compression/lattice-study/C-security.md`, `lane/pq-lattice-qrom:docs/zk-formal/PQ-LATTICE-QROM-PLAN.md`

### [DFMS22b]

- **Citation:** J. Don, S. Fehr, C. Majenz, C. Schaffner. *Efficient NIZKs and Signatures from Commit-and-Open Protocols in the QROM*. CRYPTO 2022; arXiv 2202.13730, 2022. <https://arxiv.org/abs/2202.13730>
- **Topics:** T3 · **Relevance:** C — cited (lattice plan)
- **Gives:** QROM security of commit-and-open Sigma protocols.
- **Where in repo:** `lane/pq-lattice-qrom:docs/zk-formal/PQ-LATTICE-QROM-PLAN.md`

### [HNY22]

- **Citation:** I. Haitner, D. Nukrai, E. Yogev. *Lower Bound on SNARGs in the Random Oracle Model*. CRYPTO 2022; ePrint 2022/178, 2022. <https://eprint.iacr.org/2022/178>
- **Topics:** T3 · **Relevance:** C — cited (L4-B: bound 100x below our paths)
- **Gives:** Conditional (rETH) ROM-SNARG length lower bound Omega(log t log(t/eps)/log q).
- **Where in repo:** `lane/pq-x15-domains:research/near-compression/l4-study/B-openings.md`

### [LMS22]

- **Citation:** R. Lai, G. Malavolta, N. Spooner. *Quantum Rewinding for Many-Round Protocols*. EUROCRYPT 2022; ePrint 2022/889, 2022. <https://eprint.iacr.org/2022/889>
- **Topics:** T3, T5 · **Relevance:** C — cited (lattice QROM obstruction NF-9)
- **Gives:** Quantum rewinding for multi-round (interactive) protocols.
- **Where in repo:** `lane/pq-lattice-qrom:research/near-compression/lattice-study/A-labrador-greyhound.md`, `lane/pq-lattice-qrom:docs/zk-formal/PQ-LATTICE-QROM-PLAN.md`, `lane/pq-recursion-sha384:docs/zk-formal/PQ-LATTICE-WRAP-STUDY.md`

### [BLZ21]

- **Citation:** J. Blocki, S. Lee, S. Zhou. *On the Security of Proofs of Sequential Work in a Post-Quantum World*. ITC 2021; arXiv 2006.10972, 2021. <https://arxiv.org/abs/2006.10972>
- **Topics:** T3 · **Relevance:** R — evaluated-rejected (sequential-work FS: KILL)
- **Gives:** Quantum PoSW bounds (sequential depth).
- **Where in repo:** `lane/pq-x15-domains:research/near-compression/l4-study/A-sequential-fs.md`

### [CFHL21]

- **Citation:** K.-M. Chung, S. Fehr, Y.-H. Huang, T.-N. Liao. *On the Compressed-Oracle Technique, and Post-Quantum Security of Proofs of Sequential Work*. EUROCRYPT 2021; ePrint 2020/1305; arXiv 2010.11658, 2021. <https://eprint.iacr.org/2020/1305>
- **Topics:** T3 · **Relevance:** U — used (PROOF.md lemmas; L4-A)
- **Gives:** Generic compressed-oracle framework (Lemma 4.3, Cor 4.2); PoSW in QROM.
- **Where in repo:** `lane/pq-final-soundness:research/near-compression/final-soundness/PROOF.md`, `lane/pq-x15-domains:research/near-compression/l4-study/A-sequential-fs.md`, `lane/pq-weak-binding:research/near-compression/weak-binding/ANALYSIS.md`

### [CMSZ21]

- **Citation:** A. Chiesa, F. Ma, N. Spooner, M. Zhandry. *Post-Quantum Succinct Arguments: Breaking the Quantum Rewinding Barrier*. FOCS 2021, 2021. <https://eprint.iacr.org/2021/334>
- **Topics:** T3 · **Relevance:** C — cited (lattice plan)
- **Gives:** State repair for quantum rewinding of Kilian.
- **Where in repo:** `lane/pq-lattice-qrom:docs/zk-formal/PQ-LATTICE-QROM-PLAN.md`

### [CY21a]

- **Citation:** A. Chiesa, E. Yogev. *Tight Security Bounds for Micali's SNARGs*. TCC 2021; ePrint 2021/188, 2021. <https://eprint.iacr.org/2021/188>
- **Topics:** T3 · **Relevance:** U — used (weak-binding basis)
- **Gives:** Micali soundness t*eps + C t/2^lambda with lambda >= 2 log t + 6 (collisions tolerated).
- **Where in repo:** `lane/pq-weak-binding:research/near-compression/weak-binding/ANALYSIS.md`, `lane/pq-x15-domains:research/near-compression/l4-study/B-openings.md`, `lane/pq-native-hermetic:docs/logs/pq-final-layer-model-2026-10-17.md`

### [CY21b]

- **Citation:** A. Chiesa, E. Yogev. *Subquadratic SNARGs in the Random Oracle Model*. CRYPTO 2021; ePrint 2021/281, 2021. <https://eprint.iacr.org/2021/281>
- **Topics:** T3 · **Relevance:** U — used (weak-binding Thm 4 adapts it to QROM BCS)
- **Gives:** Merkle-cap + permuted robust PCP: SNARG size O(log(t/eps) log t).
- **Numbers:** Table 1 at (2^64, 2^-128): Micali 346 KB vs 188 KB.
- **Where in repo:** `lane/pq-weak-binding:research/near-compression/weak-binding/ANALYSIS.md`, `lane/pq-x15-domains:research/near-compression/l4-study/B-openings.md`, `lane/pq-native-hermetic:docs/logs/pq-final-layer-model-2026-10-17.md`

### [DFMS22]

- **Citation:** J. Don, S. Fehr, C. Majenz, C. Schaffner. *Online-Extractability in the Quantum Random-Oracle Model*. EUROCRYPT 2022; ePrint 2021/280, 2021. <https://eprint.iacr.org/2021/280>
- **Topics:** T3 · **Relevance:** U — used (cited in PROOF.md)
- **Gives:** Straight-line extraction of hash-committed values in the QROM (Prop 3.5).
- **Where in repo:** `lane/pq-final-soundness:research/near-compression/final-soundness/PROOF.md`, `lane/pq-lattice-qrom:docs/zk-formal/PQ-LATTICE-QROM-PLAN.md`

### [LMS21]

- **Citation:** A. Lombardi, F. Ma, N. Spooner. *Post-Quantum Zero Knowledge, Revisited (collapsing Sigma-protocols)*. FOCS 2022; ePrint 2021/1543, 2021. <https://eprint.iacr.org/2021/1543>
- **Topics:** T3 · **Relevance:** C — cited
- **Gives:** Collapsing-based post-quantum ZK/rewinding.
- **Where in repo:** `lane/pq-lattice-qrom:docs/zk-formal/PQ-LATTICE-QROM-PLAN.md`, `lane/pq-lattice-qrom:research/near-compression/lattice-study/C-security.md`

### [Unr21]

- **Citation:** D. Unruh. *Compressed Permutation Oracles (And the Collision-Resistance of Sponge/SHA3)*. ePrint 2021/062, 2021. <https://eprint.iacr.org/2021/062>
- **Topics:** T3 · **Relevance:** C — cited (background)
- **Gives:** Compressed oracles for permutations (attempt).

### [CY20-barriers]

- **Citation:** A. Chiesa, E. Yogev. *Barriers for Succinct Arguments in the Random Oracle Model*. TCC 2020, 2020. <https://eprint.iacr.org/2020/1427>
- **Topics:** T3 · **Relevance:** C — cited (L4-B)
- **Gives:** Every ROM SNARG contains an IOP; query lower bounds.
- **Where in repo:** `lane/pq-x15-domains:research/near-compression/l4-study/B-openings.md`

### [DFM20]

- **Citation:** J. Don, S. Fehr, C. Majenz. *The Measure-and-Reprogram Technique 2.0: Multi-Round Fiat-Shamir and More*. CRYPTO 2020; ePrint 2020/282, 2020. <https://eprint.iacr.org/2020/282>
- **Topics:** T3 · **Relevance:** R — evaluated-rejected (loss useless at r=10-25 rounds)
- **Gives:** Multi-round FS in QROM with (2t+1)^{2r} loss.
- **Where in repo:** `docs/zk-formal/V3-D3A-STUDY.md`, `docs/zk-formal/V3-PERF-DESIGN.md`, `research/hash-recursion/README.md`, `lane/pq-lattice-qrom:research/near-compression/lattice-study/C-security.md`, `lane/pq-lattice-qrom:docs/zk-formal/PQ-LATTICE-QROM-PLAN.md`

### [HM20]

- **Citation:** Y. Hamoudi, F. Magniez. *Quantum Time-Space Tradeoff for Finding Multiple Collision Pairs*. TQC 2021; arXiv 2002.08944, 2020. <https://arxiv.org/abs/2002.08944>
- **Topics:** T3 · **Relevance:** U — used (weak-binding collision counting)
- **Gives:** Bounds for finding K collisions with t quantum queries.
- **Where in repo:** `lane/pq-weak-binding:research/near-compression/weak-binding/ANALYSIS.md`

### [CMS19]

- **Citation:** A. Chiesa, P. Manohar, N. Spooner. *Succinct Arguments in the Quantum Random Oracle Model*. TCC 2019; ePrint 2019/834, 2019. <https://eprint.iacr.org/2019/834>
- **Topics:** T3 · **Relevance:** U — used (template for PROOF.md Thm 6.4; source of digest-width rule)
- **Gives:** BCS in the QROM: O(t^2 eps_rbr + t^3/2^lambda), straight-line extractor (§8.5).
- **Numbers:** Thm 8.6 explicit 6(t^2 eps + 4t^3/2^lambda) -> 2^-137.5 cross-check.
- **Where in repo:** `lane/pq-final-soundness:research/near-compression/final-soundness/PROOF.md`, `lane/pq-weak-binding:research/near-compression/weak-binding/ANALYSIS.md`, `lane/pq-x15-domains:research/near-compression/l4-study/B-openings.md`, `docs/zk-formal/V3-D3A-STUDY.md`, `docs/zk-formal/V3-PERF-DESIGN.md`, `lane/pq-lattice-qrom:research/near-compression/lattice-study/C-security.md`

### [DFMS19]

- **Citation:** J. Don, S. Fehr, C. Majenz, C. Schaffner. *Security of the Fiat-Shamir Transformation in the Quantum Random-Oracle Model*. CRYPTO 2019; ePrint 2019/190, 2019. <https://eprint.iacr.org/2019/190>
- **Topics:** T3 · **Relevance:** C — cited (lattice QROM study)
- **Gives:** Measure-and-reprogram; FS of Sigma-protocols in the QROM with (2q+1)^2 loss.
- **Where in repo:** `lane/pq-lattice-qrom:research/near-compression/lattice-study/C-security.md`, `lane/pq-lattice-qrom:docs/zk-formal/PQ-LATTICE-QROM-PLAN.md`

### [LZ19]

- **Citation:** Q. Liu, M. Zhandry. *Revisiting Post-Quantum Fiat-Shamir*. CRYPTO 2019; ePrint 2019/262, 2019. <https://eprint.iacr.org/2019/262>
- **Topics:** T3 · **Relevance:** C — cited
- **Gives:** QROM FS for Sigma-protocols with collapsing/special soundness.
- **Where in repo:** `lane/pq-lattice-qrom:research/near-compression/lattice-study/C-security.md`

### [LZ19b]

- **Citation:** Q. Liu, M. Zhandry. *On Finding Quantum Multi-collisions*. EUROCRYPT 2019; arXiv 1811.05385, 2019. <https://arxiv.org/abs/1811.05385>
- **Topics:** T3 · **Relevance:** U — used (weak-binding)
- **Gives:** Quantum multi-collision query bounds.
- **Where in repo:** `lane/pq-weak-binding:research/near-compression/weak-binding/ANALYSIS.md`

### [Zha19]

- **Citation:** M. Zhandry. *How to Record Quantum Queries, and Applications to Quantum Indifferentiability*. CRYPTO 2019; ePrint 2018/276, 2018. <https://eprint.iacr.org/2018/276>
- **Topics:** T3 · **Relevance:** U — used (foundation of Thm 6.4)
- **Gives:** Compressed-oracle technique for QROM proofs.
- **Where in repo:** `lane/pq-final-soundness:research/near-compression/final-soundness/PROOF.md`, `research/hash-recursion/README.md`, `docs/zk-formal/V3-D3A-STUDY.md`

### [CGHSU17]

- **Citation:** J. Czajkowski, L. Groot Bruinderink, A. Hülsing, C. Schaffner, D. Unruh. *Post-Quantum Security of the Sponge Construction*. PQCrypto 2018; ePrint 2017/771, 2017. <https://eprint.iacr.org/2017/771>
- **Topics:** T3 · **Relevance:** C — cited (background; SHA-3 specific)
- **Gives:** Collapsing / quantum collision resistance of sponges.

### [Unr17]

- **Citation:** D. Unruh. *Post-Quantum Security of Fiat-Shamir*. ASIACRYPT 2017; ePrint 2017/398, 2017. <https://eprint.iacr.org/2017/398>
- **Topics:** T3 · **Relevance:** C — cited (background)
- **Gives:** First QROM FS results via reduction to quantum search.

### [BCS16]

- **Citation:** E. Ben-Sasson, A. Chiesa, N. Spooner. *Interactive Oracle Proofs*. TCC 2016-B; ePrint 2016/116, 2016. <https://eprint.iacr.org/2016/116>
- **Topics:** T3, T1 · **Relevance:** U — used (the compiler we analyse)
- **Gives:** IOP model and the BCS (Merkle + FS) compiler.
- **Where in repo:** `lane/pq-final-soundness:research/near-compression/final-soundness/PROOF.md`

### [FIPS180-4]

- **Citation:** NIST. *FIPS 180-4 Secure Hash Standard (SHA-2 incl. SHA-384/512)*. NIST, 2015. <https://doi.org/10.6028/NIST.FIPS.180-4>
- **Topics:** T3, T8 · **Relevance:** U — used (all hashing; U-7/U-10)
- **Gives:** SHA-384 = SHA-512 compression with distinct IV, truncated.
- **Where in repo:** `lane/pq-sha384-air:research/near-compression/results/pq384-sha-air/README.md`, `lane/pq-sha384-air2:research/near-compression/results/pq384-sha-air2/README.md`, `docs/zk-formal/V3-D3A-STUDY.md`

### [Zha15]

- **Citation:** M. Zhandry. *A Note on the Quantum Collision and Set Equality Problems*. QIC 2015; arXiv 1312.1027, 2015. <https://arxiv.org/abs/1312.1027>
- **Topics:** T3 · **Relevance:** U — used (digest-width rule t^3/2^336 = 2^-144)
- **Gives:** Tight generic quantum collision bound Theta(t^3/2^n).
- **Where in repo:** `docs/research/recursive-compression.md`, `docs/zk-formal/V3-D3A-STUDY.md`

### [TT05]

- **Citation:** R. Tamassia, N. Triandopoulos. *Computational Bounds on Hierarchical Data Processing with Applications to Information Security*. ICALP 2005, 2005. <https://doi.org/10.1007/11523468_14>
- **Topics:** T3 · **Relevance:** C — cited (L4-B)
- **Gives:** Omega(log n) membership proofs in hash-DAG model.
- **Where in repo:** `lane/pq-x15-domains:research/near-compression/l4-study/B-openings.md`

### [Mic00]

- **Citation:** S. Micali. *Computationally Sound Proofs*. SIAM J. Comput. 2000, 2000. <https://doi.org/10.1137/S0097539795284959>
- **Topics:** T3 · **Relevance:** C — background
- **Gives:** CS proofs: PCP + Merkle + RO.
- **Where in repo:** `lane/pq-x15-domains:research/near-compression/l4-study/B-openings.md`

### [BHT98]

- **Citation:** G. Brassard, P. Høyer, A. Tapp. *Quantum Algorithm for the Collision Problem*. LATIN 1998; arXiv quant-ph/9705002, 1998. <https://arxiv.org/abs/quant-ph/9705002>
- **Topics:** T3 · **Relevance:** C — cited
- **Gives:** Quantum collision finding in O(2^{n/3}).
- **Where in repo:** `lane/pq-native-hermetic:docs/logs/direct-wasm-pq-compression-2026-10.md`, `docs/zk-formal/V3-D3A-STUDY.md`

## T4. Recursion, PCD, accumulation, folding; impossibility and standard-model FS


### [AY25]

- **Citation:** G. Arnon, E. Yogev. *Towards a White-Box Secure Fiat-Shamir Transformation (XFS)*. CRYPTO 2025; ePrint 2025/329, 2025. <https://eprint.iacr.org/2025/329>
- **Topics:** T4 · **Relevance:** R — evaluated-rejected (A-IC research)
- **Gives:** Relativized ROM model where circuits contain oracle gates (Defs 4.1-4.2).
- **Where in repo:** `lane/pq-aic-research:research/near-compression/aic-research/REPORT.md`, `lane/pq-aic-research:research/near-compression/aic-research/LEMMA.md`

### [GY25]

- **Citation:** Z. Guan, E. Yogev. *Micali's SNARG, Function Vector Commitments, and Fiat-Shamir*. ePrint 2025/2328, 2025. <https://eprint.iacr.org/2025/2328>
- **Topics:** T4, T3 · **Relevance:** R — evaluated-rejected
- **Gives:** Thm 1: non-adaptive, iO-strength commitments.
- **Where in repo:** `lane/pq-aic-research:research/near-compression/aic-research/REPORT.md`

### [MMZ25]

- **Citation:** M. Maller, N. Mohnblatt, A. Zapico. *IVC in the Open-and-sign Random Oracle Model*. ePrint 2025/1663, 2025. <https://eprint.iacr.org/2025/1663>
- **Topics:** T4 · **Relevance:** R — evaluated-rejected (not hash-only)
- **Gives:** Classical, curve/lattice-based accumulation model.
- **Where in repo:** `lane/pq-aic-research:research/near-compression/aic-research/REPORT.md`

### [WARP25]

- **Citation:** B. Bünz, A. Chiesa, G. Fenzi, W. Wang. *Linear-Time Accumulation Schemes (WARP)*. ePrint 2025/753, 2025. <https://eprint.iacr.org/2025/753>
- **Topics:** T4, T1 · **Relevance:** R — evaluated-rejected (same final-layer floor; ~3.4k compressions/step)
- **Gives:** Linear-time accumulation for any linear code; QROM conjectured (fn 1).
- **Where in repo:** `docs/zk-formal/V3-PERF-DESIGN.md`, `lane/pq-native-hermetic:docs/logs/pq-final-layer-model-2026-10-17.md`, `lane/pq-final-soundness:research/near-compression/final-soundness/PROOF.md`, `lane/pq-aic-research:research/near-compression/aic-research/REPORT.md`

### [Arc24]

- **Citation:** B. Bünz, P. Mishra, W. Nguyen, W. Wang. *Arc: Accumulation for Reed-Solomon Codes*. CRYPTO 2025; ePrint 2024/1731, 2024. <https://eprint.iacr.org/2024/1731>
- **Topics:** T4, T1 · **Relevance:** R — evaluated-rejected (prover speed only; final layer unchanged)
- **Gives:** Accumulation of RS proximity claims (hash-based).
- **Where in repo:** `docs/zk-formal/V3-PERF-DESIGN.md`, `lane/pq-native-hermetic:docs/logs/pq-final-layer-model-2026-10-17.md`, `lane/pq-final-soundness:research/near-compression/final-soundness/PROOF.md`, `lane/pq-aic-research:research/near-compression/aic-research/REPORT.md`

### [BCG24]

- **Citation:** M. Barbara, A. Chiesa, Z. Guan. *Relativized Succinct Arguments in the ROM Do Not Exist*. TCC 2025; ePrint 2024/728, 2024. <https://eprint.iacr.org/2024/728>
- **Topics:** T4 · **Relevance:** U — used (motivates A-IC / U-11, U-12)
- **Gives:** Impossibility of succinct arguments for oracle-NP relative to a RO: hash-in-circuit recursion cannot be a ROM theorem.
- **Where in repo:** `lane/pq-final-soundness:research/near-compression/final-soundness/PROOF.md`, `lane/pq-aic-research:research/near-compression/aic-research/REPORT.md`, `lane/pq-aic-research:research/near-compression/aic-research/LEMMA.md`

### [BMNW24]

- **Citation:** B. Bünz, P. Mishra, W. Nguyen, W. Wang. *Accumulation without Homomorphism*. ITCS 2025; ePrint 2024/474, 2024. <https://eprint.iacr.org/2024/474>
- **Topics:** T4 · **Relevance:** R — evaluated-rejected
- **Gives:** Hash-based accumulation; §3.3: 'we do not know how to build secure PCD schemes in the ROM'.
- **Where in repo:** `lane/pq-final-soundness:research/near-compression/final-soundness/PROOF.md`, `lane/pq-aic-research:research/near-compression/aic-research/REPORT.md`

### [HyperNova]

- **Citation:** A. Kothapalli, S. Setty. *HyperNova: Recursive arguments for customizable constraint systems*. CRYPTO 2024; ePrint 2023/573, 2024. <https://eprint.iacr.org/2023/573>
- **Topics:** T4 · **Relevance:** R — evaluated-rejected (not PQ)
- **Gives:** CCS folding (curve-based).

### [Nebula24]

- **Citation:** (ICME / zkEngine). *Nebula: Efficient read-write memory and switchboard circuits for folding schemes*. ePrint 2024/1605, 2024. <https://eprint.iacr.org/2024/1605>
- **Topics:** T4, T12 · **Relevance:** R — evaluated-rejected (curve-based)
- **Gives:** Nova/NIVC folding scheme behind NovaNet zkWasm (zkEngine).
- **Where in repo:** `docs/research/wasm-formal-survey.md`

### [CCGOS23]

- **Citation:** M. Chen, A. Chiesa, T. Gur, J. O'Connor, N. Spooner. *Proof-Carrying Data from Arithmetized Random Oracles*. EUROCRYPT 2023; ePrint 2023/587, 2023. <https://eprint.iacr.org/2023/587>
- **Topics:** T4 · **Relevance:** R — evaluated-rejected (needs arithmetized oracle; no quantum)
- **Gives:** Unbounded-depth PCD in the AROM (classical, asymptotic).
- **Where in repo:** `lane/pq-final-soundness:research/near-compression/final-soundness/PROOF.md`, `lane/pq-aic-research:research/near-compression/aic-research/REPORT.md`, `docs/research/recursive-compression.md`

### [CGSY24]

- **Citation:** A. Chiesa, Z. Guan, S. Samocha, E. Yogev. *Security Bounds for Proof-Carrying Data from Straightline Extractors*. TCC 2024; ePrint 2023/1646, 2023. <https://eprint.iacr.org/2023/1646>
- **Topics:** T4 · **Relevance:** R — evaluated-rejected (closest analogue of Thm 7.4; classical)
- **Gives:** kappa_PCD <= kappa_ARG with no depth loss; proven only for weak relativized NARK (non-succinct).
- **Where in repo:** `lane/pq-final-soundness:research/near-compression/final-soundness/PROOF.md`, `lane/pq-aic-research:research/near-compression/aic-research/REPORT.md`, `lane/pq-aic-research:research/near-compression/aic-research/LEMMA.md`

### [HN23]

- **Citation:** M. Hall-Andersen, J. B. Nielsen. *On Valiant's Conjecture: Impossibility of Incrementally Verifiable Computation from Random Oracles*. EUROCRYPT 2023; ePrint 2022/542, 2023. <https://eprint.iacr.org/2022/542>
- **Topics:** T4 · **Relevance:** C — cited (A-IC research)
- **Gives:** IVC impossibility in the ROM (verifier linear in steps).
- **Where in repo:** `lane/pq-final-soundness:research/near-compression/final-soundness/PROOF.md`, `lane/pq-aic-research:research/near-compression/aic-research/REPORT.md`

### [ProtoStar]

- **Citation:** B. Bünz, B. Chen. *ProtoStar: Generic Efficient Accumulation/Folding for Special-sound Protocols*. ASIACRYPT 2023; ePrint 2023/620, 2023. <https://eprint.iacr.org/2023/620>
- **Topics:** T4 · **Relevance:** R — evaluated-rejected (not PQ)
- **Gives:** Generic folding for special-sound protocols (homomorphic commitments).

### [CCS22]

- **Citation:** M. Chen, A. Chiesa, N. Spooner. *On Succinct Non-Interactive Arguments in Relativized Worlds*. EUROCRYPT 2022; ePrint 2022/383, 2022. <https://eprint.iacr.org/2022/383>
- **Topics:** T4 · **Relevance:** C — cited
- **Gives:** Relativized SNARKs in a low-degree RO model.
- **Where in repo:** `docs/research/recursive-compression.md`

### [Nova]

- **Citation:** A. Kothapalli, S. Setty, I. Tzialla. *Nova: Recursive Zero-Knowledge Arguments from Folding Schemes*. CRYPTO 2022; ePrint 2021/370, 2022. <https://eprint.iacr.org/2021/370>
- **Topics:** T4 · **Relevance:** R — evaluated-rejected (not PQ)
- **Gives:** Folding-based IVC (curve-based, not PQ).
- **Where in repo:** `docs/research/wasm-formal-survey.md`

### [CJJ21]

- **Citation:** A. R. Choudhuri, A. Jain, Z. Jin. *SNARGs for P from LWE*. FOCS 2021; ePrint 2021/808, 2021. <https://eprint.iacr.org/2021/808>
- **Topics:** T4, T3 · **Relevance:** R — evaluated-rejected
- **Gives:** Standard-model SNARGs for P.
- **Where in repo:** `lane/pq-aic-research:research/near-compression/aic-research/REPORT.md`

### [HLR21]

- **Citation:** J. Holmgren, A. Lombardi, R. Rothblum. *Fiat-Shamir via List-Recoverable Codes (or: Parallel Repetition of GMW is not Zero-Knowledge)*. STOC 2021; ePrint 2021/286, 2021. <https://eprint.iacr.org/2021/286>
- **Topics:** T4, T3 · **Relevance:** R — evaluated-rejected
- **Gives:** CI-based FS; Remark 1.3: FS for Kilian open.
- **Where in repo:** `lane/pq-aic-research:research/near-compression/aic-research/REPORT.md`

### [BCLMS21]

- **Citation:** B. Bünz, A. Chiesa, W. Lin, P. Mishra, N. Spooner. *Proof-Carrying Data Without Succinct Arguments*. CRYPTO 2021; ePrint 2020/1618, 2020. <https://eprint.iacr.org/2020/1618>
- **Topics:** T4 · **Relevance:** R — evaluated-rejected
- **Gives:** Split accumulation; heuristic, constant depth.
- **Where in repo:** `lane/pq-aic-research:research/near-compression/aic-research/REPORT.md`

### [BCMS20]

- **Citation:** B. Bünz, A. Chiesa, P. Mishra, N. Spooner. *Proof-Carrying Data from Accumulation Schemes*. TCC 2020; ePrint 2020/499, 2020. <https://eprint.iacr.org/2020/499>
- **Topics:** T4 · **Relevance:** R — evaluated-rejected
- **Gives:** PCD from accumulation; ROM pieces, heuristic instantiation.
- **Where in repo:** `lane/pq-aic-research:research/near-compression/aic-research/REPORT.md`

### [JKKZ20]

- **Citation:** R. Jawale, Y. T. Kalai, D. Khurana, R. Zhang. *SNARGs for Bounded Depth Computations and PPAD Hardness from Sub-Exponential LWE*. STOC 2021; ePrint 2020/980, 2020. <https://eprint.iacr.org/2020/980>
- **Topics:** T4, T3 · **Relevance:** R — evaluated-rejected
- **Gives:** Standard-model FS for GKR (no PCS).
- **Where in repo:** `lane/pq-aic-research:research/near-compression/aic-research/REPORT.md`

### [BBHMR19]

- **Citation:** J. Bartusek, L. Bronfman, J. Holmgren, F. Ma, R. Rothblum. *On the (In)security of Kilian-Based SNARGs*. TCC 2019; ePrint 2019/997, 2019. <https://eprint.iacr.org/2019/997>
- **Topics:** T4, T3 · **Relevance:** C — cited (standard-model FS closed)
- **Gives:** An IOP whose FS-Kilian is unsound for every hash; CR of Merkle hash is insufficient.
- **Where in repo:** `lane/pq-aic-research:research/near-compression/aic-research/REPORT.md`

### [COS20]

- **Citation:** A. Chiesa, D. Ojha, N. Spooner. *Fractal: Post-Quantum and Transparent Recursive Proofs from Holography*. EUROCRYPT 2020; ePrint 2019/1076, 2019. <https://eprint.iacr.org/2019/1076>
- **Topics:** T4, T3 · **Relevance:** U — used (cross-check) / recursion part rejected
- **Gives:** Thm 10.1 adaptive QROM KS O(t^2 kappa + t^3/2^lambda); recursion only heuristic (Thm 11.5).
- **Where in repo:** `lane/pq-final-soundness:research/near-compression/final-soundness/PROOF.md`, `lane/pq-aic-research:research/near-compression/aic-research/REPORT.md`

### [PS19]

- **Citation:** C. Peikert, S. Shiehian. *Noninteractive Zero Knowledge for NP from (Plain) Learning With Errors*. CRYPTO 2019; ePrint 2019/158, 2019. <https://eprint.iacr.org/2019/158>
- **Topics:** T4, T3 · **Relevance:** R — evaluated-rejected
- **Gives:** CI hash from LWE.
- **Where in repo:** `lane/pq-aic-research:research/near-compression/aic-research/REPORT.md`

### [CCHLRR18]

- **Citation:** R. Canetti, Y. Chen, J. Holmgren, A. Lombardi, G. Rothblum, R. Rothblum, D. Wichs. *Fiat-Shamir: From Practice to Theory*. STOC 2019; ePrint 2018/1004, 2018. <https://eprint.iacr.org/2018/1004>
- **Topics:** T4, T3 · **Relevance:** R — evaluated-rejected (keyed CI hash; not SHA-384)
- **Gives:** Correlation-intractable hash FS for statistically sound protocols.
- **Where in repo:** `lane/pq-aic-research:research/near-compression/aic-research/REPORT.md`

### [BCCT13]

- **Citation:** N. Bitansky, R. Canetti, A. Chiesa, E. Tromer. *Recursive Composition and Bootstrapping for SNARKs and Proof-Carrying Data*. STOC 2013; ePrint 2012/095, 2013. <https://eprint.iacr.org/2012/095>
- **Topics:** T4 · **Relevance:** C — cited (background)
- **Gives:** PCD from SNARKs; polynomial extractor blowup per level (constant depth).

### [GW11]

- **Citation:** C. Gentry, D. Wichs. *Separating Succinct Non-Interactive Arguments From All Falsifiable Assumptions*. STOC 2011; ePrint 2010/610, 2010. <https://eprint.iacr.org/2010/610>
- **Topics:** T4 · **Relevance:** C — cited (A-IC is necessarily non-falsifiable)
- **Gives:** No black-box reduction of adaptive SNARG soundness to falsifiable assumptions.
- **Where in repo:** `lane/pq-aic-research:research/near-compression/aic-research/REPORT.md`, `lane/pq-aic-research:research/near-compression/aic-research/LEMMA.md`

### [CGH98]

- **Citation:** R. Canetti, O. Goldreich, S. Halevi. *The Random Oracle Methodology, Revisited*. STOC 1998; JACM 2004, 1998. <https://doi.org/10.1145/1008731.1008734>
- **Topics:** T4, T3 · **Relevance:** C — cited (A-IC caveat)
- **Gives:** Schemes secure in ROM but insecure for every instantiation.
- **Where in repo:** `lane/pq-final-soundness:research/near-compression/final-soundness/PROOF.md`

## T5. Lattice-based SNARKs, PCSs and folding


### [Akita26]

- **Citation:** Q. Dao, O. Bodaghi, A. Khajehpour, G. Vitto, M. Badakhshan, M. Georghiades, F. Liu, J. Zhang, J. Thaler. *Akita: A High-Performance Lattice-Based Polynomial Commitment Scheme*. ePrint 2026/1983, 2026. <https://eprint.iacr.org/2026/1983>
- **Topics:** T5, T7 · **Relevance:** E — evaluated (lattice wrap candidate)
- **Gives:** Multilinear PCS succeeding Hachi/Greyhound; constant-root verifier.
- **Numbers:** 61-67 KB openings at 2^27-2^35 bits; Jolt+Akita SHA-256 chain 2^27 cycles: 90.9 s prove (M4 Max CPU), 98.1 KB.
- **Where in repo:** `lane/pq-lattice-qrom:research/near-compression/lattice-study/B-modern-lattice.md`, `lane/pq-lattice-qrom:docs/zk-formal/PQ-LATTICE-QROM-PLAN.md`, `lane/pq-recursion-sha384:docs/zk-formal/PQ-LATTICE-WRAP-STUDY.md`

### [BBL26]

- **Citation:** B. Biasioli, M. Bolboceanu, V. Lyubashevsky, A. Merino-Gallardo, M. Osadnik, G. Seiler, P. Steuer. *A Toolkit for Succinct Lattice-Based Zero Knowledge Proofs*. ePrint 2026/1289, 2026. <https://eprint.iacr.org/2026/1289>
- **Topics:** T5 · **Relevance:** E — evaluated
- **Gives:** Benchmarks of (ZK-)LaBRADOR.
- **Numbers:** 2^25 coefficients: 9.3 s (not zk) on 1 Tiger Lake core.
- **Where in repo:** `lane/pq-lattice-qrom:research/near-compression/lattice-study/A-labrador-greyhound.md`

### [Cyclo26]

- **Citation:** A. Garreta, H. Lipmaa, Luhaäär, M. Osadnik. *Cyclo*. EUROCRYPT 2026; ePrint 2026/359, 2026. <https://eprint.iacr.org/2026/359>
- **Topics:** T5, T4 · **Relevance:** E — evaluated
- **Gives:** Neo-equivalent folding with amortized norm refresh.
- **Numbers:** ~30 KB folding proofs (estimate).
- **Where in repo:** `lane/pq-lattice-qrom:research/near-compression/lattice-study/B-modern-lattice.md`

### [GD26]

- **Citation:** Kallesøe, Khoshakhlagh. *Grand Danois (polylog-verifier lattice PCS)*. ePrint 2026/1196, 2026. <https://eprint.iacr.org/2026/1196>
- **Topics:** T5 · **Relevance:** E — evaluated (no implementation)
- **Gives:** Hachi-style PCS with O(lambda l) verifier under vSIS.
- **Numbers:** ~80 KB at 2^32 (estimate).
- **Where in repo:** `lane/pq-lattice-qrom:research/near-compression/lattice-study/B-modern-lattice.md`

### [Hachi26]

- **Citation:** N. K. Nguyen, O'Rourke, Zhang. *Hachi (lattice PCS with ring switching)*. ePrint 2026/156, 2026. <https://eprint.iacr.org/2026/156>
- **Topics:** T5 · **Relevance:** E — evaluated (superseded by Akita)
- **Gives:** Greyhound + ring switching; verifier with no R_q mults.
- **Numbers:** ~55 KB; 227 ms verify at 2^30; ~270 s prove.
- **Where in repo:** `lane/pq-lattice-qrom:research/near-compression/lattice-study/B-modern-lattice.md`, `lane/pq-lattice-qrom:research/near-compression/lattice-study/C-security.md`

### [Jindo26]

- **Citation:** (ePrint 2026/044). *Jindo*. ePrint 2026/044, 2026. <https://eprint.iacr.org/2026/044>
- **Topics:** T5 · **Relevance:** R — evaluated-rejected
- **Gives:** Cube-root lattice argument (client-side, 255-bit field).
- **Where in repo:** `lane/pq-lattice-qrom:research/near-compression/lattice-study/B-modern-lattice.md`

### [LUNA26]

- **Citation:** (ePrint 2026/1639). *LUNA+*. ePrint 2026/1639, 2026. <https://eprint.iacr.org/2026/1639>
- **Topics:** T5 · **Relevance:** R — evaluated-rejected
- **Gives:** Designated-verifier lattice SNARK.
- **Where in repo:** `lane/pq-lattice-qrom:research/near-compression/lattice-study/B-modern-lattice.md`

### [LaBinius26]

- **Citation:** M. Osadnik, G. Seiler. *LaBinius: lattice PCS with binary-field evaluations (Binius/Flock front ends)*. ePrint 2026/2103, 2026. <https://eprint.iacr.org/2026/2103>
- **Topics:** T5, T8 · **Relevance:** N — not-yet-evaluated (reference to beat on bytes for a PQ hash proof; classical-ROM FS; binary beyond-Johnson counterexamples apply to its params)
- **Gives:** Lattice PCS for binary-field front ends; SHA-256/Keccak/BLAKE3 proofs < 100 KiB with LaBRADOR compression, < 40 ms verify, 1.2-2x hash-based prover time.
- **Numbers:** < 100 KiB SHA-256 proof; self-described smallest quantum-safe proof of a standard hash.

### [Maltese26]

- **Citation:** Cheng, N. K. Nguyen, Tyagi. *Maltese (standard-MSIS PCS with polylog verifier)*. ASIACRYPT 2026; ePrint 2026/2067, 2026. <https://eprint.iacr.org/2026/2067>
- **Topics:** T5 · **Relevance:** E — evaluated
- **Gives:** Merkle tree of Ajtai hashes; O(log^2 N) proof.
- **Numbers:** 224-335 KB at 2^30 (estimate).
- **Where in repo:** `lane/pq-lattice-qrom:research/near-compression/lattice-study/B-modern-lattice.md`

### [Orthus26]

- **Citation:** (IBM). *Orthus (Falcon aggregation, sqrt N verifier)*. ePrint 2026/398, 2026. <https://eprint.iacr.org/2026/398>
- **Topics:** T5 · **Relevance:** R — evaluated-rejected
- **Gives:** Lattice relation proofs.
- **Where in repo:** `lane/pq-lattice-qrom:research/near-compression/lattice-study/B-modern-lattice.md`

### [PikkuFold26]

- **Citation:** M. Osadnik. *PikkuFold*. ePrint 2026/1809, 2026. <https://eprint.iacr.org/2026/1809>
- **Topics:** T5, T4 · **Relevance:** E — evaluated
- **Gives:** Small lattice fold (5.5 KB/fold).
- **Where in repo:** `lane/pq-lattice-qrom:research/near-compression/lattice-study/B-modern-lattice.md`

### [ProtogaLattice26]

- **Citation:** Balbás, Nitulescu, Plançon. *ProtogaLattice*. ePrint 2026/1317, 2026. <https://eprint.iacr.org/2026/1317>
- **Topics:** T5, T4 · **Relevance:** E — evaluated
- **Gives:** High-degree algebraic lattice folding.
- **Numbers:** 8.13 KB/iteration at 2^30 (estimate).
- **Where in repo:** `lane/pq-lattice-qrom:research/near-compression/lattice-study/B-modern-lattice.md`

### [RoKoko26]

- **Citation:** M. Klooß, R. Lai, N. K. Nguyen, M. Osadnik, Tucci. *RoKoko: linear-time lattice argument with polylog verifier*. ePrint 2026/575, 2026. <https://eprint.iacr.org/2026/575>
- **Topics:** T5 · **Relevance:** E — evaluated
- **Gives:** Committed folding with large arity + SALSAA sumcheck.
- **Numbers:** 2^30 Zq: 18.1 s commit, 8.9 s prove, 13.1 ms verify, 157 KB (1 thread).
- **Where in repo:** `lane/pq-lattice-qrom:research/near-compression/lattice-study/B-modern-lattice.md`, `lane/pq-lattice-qrom:research/near-compression/lattice-study/A-labrador-greyhound.md`, `lane/pq-lattice-qrom:research/near-compression/lattice-study/C-security.md`

### [SuperNeo26]

- **Citation:** W. Nguyen, S. Setty. *Neo and SuperNeo*. ePrint 2026/242, 2026. <https://eprint.iacr.org/2026/242>
- **Topics:** T5, T4 · **Relevance:** E — evaluated
- **Gives:** Arbitrary cyclotomic, field-native sumcheck lattice folding (fits BabyBear-friendly rings).
- **Where in repo:** `lane/pq-lattice-qrom:research/near-compression/lattice-study/B-modern-lattice.md`, `lane/pq-lattice-qrom:research/near-compression/lattice-study/C-security.md`

### [LatticeFoldP25]

- **Citation:** D. Boneh, B. Chen. *LatticeFold+: Faster, Simpler, Shorter Lattice-Based Folding*. ePrint 2025/247, 2025. <https://eprint.iacr.org/2025/247>
- **Topics:** T5, T4 · **Relevance:** E — evaluated
- **Gives:** Improved lattice folding.
- **Numbers:** Folding proofs ~100-200 KB (estimate).
- **Where in repo:** `lane/pq-lattice-qrom:research/near-compression/lattice-study/B-modern-lattice.md`, `lane/pq-lattice-qrom:research/near-compression/lattice-study/C-security.md`

### [Neo25]

- **Citation:** W. Nguyen, S. Setty. *Neo: Lattice-based folding scheme for CCS over small fields*. ePrint 2025/294, 2025. <https://eprint.iacr.org/2025/294>
- **Topics:** T5, T4 · **Relevance:** E — evaluated (not succinct alone)
- **Gives:** Small-field lattice folding; needs a decider.
- **Where in repo:** `lane/pq-lattice-qrom:research/near-compression/lattice-study/B-modern-lattice.md`, `lane/pq-lattice-qrom:research/near-compression/lattice-study/C-security.md`

### [RnR25]

- **Citation:** (Klooß, Lai, Nguyen, Osadnik). *RoK and Roll*. ePrint 2025/1220, 2025. <https://eprint.iacr.org/2025/1220>
- **Topics:** T5 · **Relevance:** E — evaluated
- **Gives:** Structured JL norm proof; vSIS.
- **Where in repo:** `lane/pq-lattice-qrom:research/near-compression/lattice-study/B-modern-lattice.md`, `lane/pq-lattice-qrom:research/near-compression/lattice-study/C-security.md`

### [SALSAA25]

- **Citation:** S. Kuriyama, R. W. F. Lai, M. Osadnik, L. Tucci. *SALSAA: Sumcheck-Aided Lattice-based Succinct Arguments and Applications*. ePrint 2025/2124, 2025. <https://eprint.iacr.org/2025/2124>
- **Topics:** T5 · **Relevance:** E — evaluated
- **Gives:** Lattice AIR reduction and folding (~60 KB/step).
- **Where in repo:** `lane/pq-lattice-qrom:research/near-compression/lattice-study/B-modern-lattice.md`

### [Symphony25]

- **Citation:** B. Chen. *Symphony (lattice high-arity folding)*. ePrint 2025/1905, 2025. <https://eprint.iacr.org/2025/1905>
- **Topics:** T5, T4 · **Relevance:** E — evaluated
- **Gives:** Folding with inner WHIR/LaBRADOR SNARKs.
- **Numbers:** <200 KB (estimate).
- **Where in repo:** `lane/pq-lattice-qrom:research/near-compression/lattice-study/B-modern-lattice.md`, `lane/pq-aic-research:research/near-compression/aic-research/REPORT.md`

### [Chen24]

- **Citation:** Y. Chen. *Quantum Algorithms for Lattice Problems (claimed; bug found)*. ePrint 2024/555, 2024. <https://eprint.iacr.org/2024/555>
- **Topics:** T5 · **Relevance:** C — cited (risk note)
- **Gives:** Claimed poly-time quantum LWE algorithm; withdrawn after a bug.
- **Where in repo:** `lane/pq-lattice-qrom:research/near-compression/lattice-study/C-security.md`

### [FMN24]

- **Citation:** N. Fleischhacker, M. Mohnblatt, (N. K. Nguyen)?. *Lattice-based polynomial commitments: towards asymptotic and concrete efficiency*. JoC 2024, 2024. <https://doi.org/10.1007/s00145-024-09511-8>
- **Topics:** T5, T3 · **Relevance:** C — cited
- **Gives:** Multi-round special-soundness FS for lattice PCS (§8).
- **Where in repo:** `lane/pq-lattice-qrom:research/near-compression/lattice-study/C-security.md`, `lane/pq-lattice-qrom:docs/zk-formal/PQ-LATTICE-QROM-PLAN.md`

### [LatticeFold24]

- **Citation:** D. Boneh, B. Chen. *LatticeFold: A Lattice-based Folding Scheme and its Applications to Succinct Proof Systems*. ASIACRYPT 2025; ePrint 2024/257, 2024. <https://eprint.iacr.org/2024/257>
- **Topics:** T5, T4 · **Relevance:** E — evaluated
- **Gives:** First lattice folding scheme.
- **Where in repo:** `lane/pq-lattice-qrom:research/near-compression/lattice-study/B-modern-lattice.md`, `lane/pq-lattice-qrom:research/near-compression/lattice-study/C-security.md`

### [Lova24]

- **Citation:** G. Fenzi, C. Knabenhans, N. K. Nguyen, D. T. Pham. *Lova: Lattice-Based Folding Scheme from Unstructured Lattices*. ePrint 2024/1964, 2024. <https://eprint.iacr.org/2024/1964>
- **Topics:** T5, T4 · **Relevance:** E — evaluated
- **Gives:** Unstructured-lattice folding.
- **Where in repo:** `lane/pq-lattice-qrom:research/near-compression/lattice-study/B-modern-lattice.md`, `lane/pq-lattice-qrom:research/near-compression/lattice-study/C-security.md`

### [NS24-Greyhound]

- **Citation:** N. K. Nguyen, G. Seiler. *Greyhound: Fast Polynomial Commitments from Lattices*. CRYPTO 2024; ePrint 2024/1293, 2024. <https://eprint.iacr.org/2024/1293>
- **Topics:** T5 · **Relevance:** E — evaluated (lattice wrap)
- **Gives:** Lattice PCS, O(sqrt N) verifier, LaBRADOR tail.
- **Numbers:** ~53 KB at N=2^30; 46-53 KB at 2^26-2^30.
- **Where in repo:** `lane/pq-lattice-qrom:research/near-compression/lattice-study/A-labrador-greyhound.md`, `lane/pq-lattice-qrom:research/near-compression/lattice-study/C-security.md`, `lane/pq-native-hermetic:docs/logs/pq-final-layer-model-2026-10-17.md`, `lane/pq-recursion-sha384:docs/zk-formal/PQ-LATTICE-WRAP-STUDY.md`

### [RPS24]

- **Citation:** (Klooß, Lai, Nguyen, Osadnik). *RoK, Paper, SISsors: toolkit for lattice-based succinct arguments*. ePrint 2024/1972, 2024. <https://eprint.iacr.org/2024/1972>
- **Topics:** T5 · **Relevance:** E — evaluated (large proofs)
- **Gives:** vSIS-based fully succinct arguments.
- **Where in repo:** `lane/pq-lattice-qrom:research/near-compression/lattice-study/B-modern-lattice.md`, `lane/pq-lattice-qrom:research/near-compression/lattice-study/C-security.md`

### [BBD23-EC-Dil]

- **Citation:** M. Barbosa, G. Barthe, et al.. *Fixing and Mechanizing the Security Proof of Fiat-Shamir with Aborts and Dilithium*. CRYPTO 2023; ePrint 2023/246, 2023. <https://eprint.iacr.org/2023/246>
- **Topics:** T5, T9 · **Relevance:** C — cited (adjacent formal work)
- **Gives:** EasyCrypt mechanised ROM proof of Dilithium.
- **Where in repo:** `lane/pq-lattice-qrom:research/near-compression/lattice-study/C-security.md`

### [SLAP23]

- **Citation:** (ePrint 2023/1469). *SLAP: succinct lattice-based polynomial commitments from standard assumptions*. ePrint 2023/1469, 2023. <https://eprint.iacr.org/2023/1469>
- **Topics:** T5 · **Relevance:** R — evaluated-rejected (767 MB)
- **Gives:** Standard-assumption polylog PCS.
- **Where in repo:** `lane/pq-lattice-qrom:research/near-compression/lattice-study/B-modern-lattice.md`

### [BS23-LaBRADOR]

- **Citation:** W. Beullens, G. Seiler. *LaBRADOR: Compact Proofs for R1CS from Module-SIS*. CRYPTO 2023; ePrint 2022/1341, 2022. <https://eprint.iacr.org/2022/1341>
- **Topics:** T5 · **Relevance:** E — evaluated (lattice final wrap; QROM obstruction NF-9)
- **Gives:** Recursive lattice proof for R1CS mod 2^64+1; size nearly constant.
- **Numbers:** ~58 KB at 128-bit (classical core-SVP) for 2^20 constraints; 49-54 KB binary R1CS 2^20-2^25.
- **Where in repo:** `lane/pq-lattice-qrom:research/near-compression/lattice-study/A-labrador-greyhound.md`, `lane/pq-lattice-qrom:research/near-compression/lattice-study/C-security.md`, `lane/pq-native-hermetic:docs/logs/pq-final-layer-model-2026-10-17.md`, `lane/pq-recursion-sha384:docs/zk-formal/PQ-LATTICE-WRAP-STUDY.md`

### [LS18]

- **Citation:** V. Lyubashevsky, G. Seiler. *Short, Invertible Elements in Partially Splitting Cyclotomic Rings*. EUROCRYPT 2018, 2018. <https://doi.org/10.1007/978-3-319-78381-9_8>
- **Topics:** T5 · **Relevance:** C — cited
- **Gives:** Invertibility of challenge differences.
- **Where in repo:** `lane/pq-lattice-qrom:research/near-compression/lattice-study/A-labrador-greyhound.md`, `lane/pq-lattice-qrom:docs/zk-formal/PQ-LATTICE-QROM-PLAN.md`

### [ADPS16]

- **Citation:** E. Alkim, L. Ducas, T. Pöppelmann, P. Schwabe. *Post-quantum Key Exchange - A New Hope*. USENIX Security 2016, 2016. <https://eprint.iacr.org/2015/1092>
- **Topics:** T5 · **Relevance:** U — used (MSIS sizing in lattice plan)
- **Gives:** Core-SVP hardness methodology (0.265 beta quantum).
- **Where in repo:** `lane/pq-lattice-qrom:docs/zk-formal/PQ-LATTICE-QROM-PLAN.md`, `lane/pq-lattice-qrom:research/near-compression/lattice-study/A-labrador-greyhound.md`

### [BDGL16]

- **Citation:** A. Becker, L. Ducas, N. Gama, T. Laarhoven. *New directions in nearest neighbor searching with applications to lattice sieving*. SODA 2016, 2016. <https://eprint.iacr.org/2015/1128>
- **Topics:** T5 · **Relevance:** C — cited
- **Gives:** Sieve cost 2^{0.292 beta}.
- **Where in repo:** `lane/pq-lattice-qrom:research/near-compression/lattice-study/A-labrador-greyhound.md`, `lane/pq-lattice-qrom:research/near-compression/lattice-study/C-security.md`

## T6. GKR, LogUp, sumcheck


### [DDBDT26]

- **Citation:** Q. Dao, J. DeStefano, S. Bagad, Y. Domb, J. Thaler. *Speeding Up Sum-Check Proving (Extended Version)*. ePrint 2026/587, 2026. <https://eprint.iacr.org/2026/587>
- **Topics:** T6 · **Relevance:** N — not-yet-evaluated (real-time prover lever)
- **Gives:** Merges 2024/1046, 2024/1210, 2025/1117; single reference for sumcheck prover speedups.

### [MoHW26]

- **Citation:** Mo, et al., B. Bünz, B. Reagen. *When Proofs Meet Hardware: NTT vs sumcheck under equal SRAM/bandwidth*. arXiv 2606.16146, 2026. <https://arxiv.org/abs/2606.16146>
- **Topics:** T6, T7 · **Relevance:** N — not-yet-evaluated (our degree-21 SHA AIR)
- **Gives:** Sumcheck beats NTT on hardware for high-degree constraints.

### [BDDT25]

- **Citation:** S. Bagad, Q. Dao, Y. Domb, J. Thaler. *Speeding Up Sum-Check Proving*. ePrint 2025/1117, 2025. <https://eprint.iacr.org/2025/1117>
- **Topics:** T6 · **Relevance:** N — not-yet-evaluated
- **Gives:** Small-value + eq optimizations, 2-3x on Spartan sumcheck.
- **Numbers:** 2-3x prover speedup (Jolt).

### [Expander]

- **Citation:** Polyhedra Network. *Expander GKR prover / Binary GKR*. GitHub PolyhedraZK/Expander, 2025. <https://github.com/PolyhedraZK/Expander>
- **Topics:** T6, T7, T8 · **Relevance:** N — not-yet-evaluated
- **Gives:** GKR prover; ~4,500 Keccak-f/s on M3 Max (vendor).

### [KRS25]

- **Citation:** D. Khovratovich, R. D. Rothblum, L. Soukhanov. *How to Prove False Statements: Practical Attacks on Fiat-Shamir*. CRYPTO 2025; ePrint 2025/118, 2025. <https://eprint.iacr.org/2025/118>
- **Topics:** T6, T3 · **Relevance:** E — evaluated (not applicable: we commit full traces; canonical lookup GKR not attackable per Remark 3)
- **Gives:** Any-hash attacks on FS-GKR when the circuit computes the FS hash of its own transcript.
- **Where in repo:** `lane/pq-aic-research:research/near-compression/aic-research/REPORT.md`

### [Sou25-logupstar]

- **Citation:** L. Soukhanov. *Logup*: faster, cheaper logup argument for small-table indexed lookups*. ePrint 2025/946, 2025. <https://eprint.iacr.org/2025/946>
- **Topics:** T6, T8 · **Relevance:** N — not-yet-evaluated (could drop committed Sigma/Ch/Maj outputs in SHA AIR)
- **Gives:** Indexed lookup T[I] with T[I] virtual; only indices committed.

### [Tha25]

- **Citation:** J. Thaler. *Sum-check Is All You Need: An Opinionated Survey on Fast Provers in SNARK Design*. ePrint 2025/2041, 2025. <https://eprint.iacr.org/2025/2041>
- **Topics:** T6 · **Relevance:** C — cited (background)
- **Gives:** Survey: virtual polynomials, sparse sumchecks, small values.

### [TwistShout]

- **Citation:** S. Setty, J. Thaler. *Twist and Shout: Faster memory checking arguments via one-hot addressing and increments*. ePrint 2025/105, 2025. <https://eprint.iacr.org/2025/105>
- **Topics:** T6, T7 · **Relevance:** N — not-yet-evaluated
- **Gives:** One-hot memory checking and lookups (>10x cheaper prover than log-proof memory checking).

### [BDT24]

- **Citation:** S. Bagad, Y. Domb, J. Thaler. *The Sum-Check Protocol over Fields of Small Characteristic*. ePrint 2024/1046, 2024. <https://eprint.iacr.org/2024/1046>
- **Topics:** T6 · **Relevance:** N — not-yet-evaluated (BabyBear->Ext12 prover speed)
- **Gives:** Keep prover work in the base field; Karatsuba-style tricks for extension fields.

### [Ceno24]

- **Citation:** T. Liu, Z. Zhang, Y. Zhang, W. Hu, Y. Zhang. *Ceno: Non-uniform, Segment and Parallel Zero-knowledge Virtual Machine*. ePrint 2024/387, 2024. <https://eprint.iacr.org/2024/387>
- **Topics:** T6, T7 · **Relevance:** N — not-yet-evaluated (GKR replacing committed columns)
- **Gives:** GKR zkVM committing only circuit I/O, data-parallel opcode circuits.

### [DT24]

- **Citation:** Q. Dao, J. Thaler. *More Optimizations to Sum-Check Proving*. ePrint 2024/1210, 2024. <https://eprint.iacr.org/2024/1210>
- **Topics:** T6 · **Relevance:** N — not-yet-evaluated
- **Gives:** Cheaper eq(w,x) handling, complementary to Gruen.

### [EH24]

- **Citation:** L. Eagen, U. Haböck. *Bypassing the characteristic bound in logUp*. ePrint 2024/2067, 2024. <https://eprint.iacr.org/2024/2067>
- **Topics:** T6 · **Relevance:** N — not-yet-evaluated (check B4: BabyBear p ~ 2^31 multiplicity bound)
- **Gives:** Removes the multiplicity-sum < p requirement of LogUp(-GKR).

### [Gru24]

- **Citation:** A. Gruen. *Some Improvements for the PIOP for ZeroCheck*. ePrint 2024/108, 2024. <https://eprint.iacr.org/2024/108>
- **Topics:** T6 · **Relevance:** U — used (Gruen GKR + batch-constraint rounds; Lemma 2.5 proves soundness)
- **Gives:** Degree-reduction trick for sumcheck round polynomials; univariate skip; soundness remark informal (App. A.3).
- **Numbers:** GKR 72L^2+264L+248 -> 48L^2+192L+152 B (29,960 vs 44,408 B at L=23).
- **Where in repo:** `lane/pq-final-soundness:research/near-compression/final-soundness/PROOF.md`, `lane/pq-final-soundness:research/near-compression/final-soundness/GAPS.md`, `lane/pq-whir-levers:research/near-compression/results/pq-whir-levers/README.md`, `lane/pq-native-hermetic:docs/logs/pq-final-layer-model-2026-10-17.md`

### [Lasso]

- **Citation:** S. Setty, J. Thaler, R. Wahby. *Unlocking the lookup singularity with Lasso*. EUROCRYPT 2024; ePrint 2023/1216, 2023. <https://eprint.iacr.org/2023/1216>
- **Topics:** T6 · **Relevance:** C — cited (background)
- **Gives:** Lookups into decomposable tables.

### [PH23]

- **Citation:** S. Papini, U. Haböck. *Improving logarithmic derivative lookups using GKR (LogUp-GKR)*. ePrint 2023/1284, 2023. <https://eprint.iacr.org/2023/1284>
- **Topics:** T6 · **Relevance:** U — used (Lemma 3.1-3.2; SWIRL)
- **Gives:** Fractional-sum GKR for LogUp; no committed helper columns.
- **Numbers:** Our measured GKR size: 48L^2+192L+152 B with Gruen (L = log2 interactions).
- **Where in repo:** `lane/pq-final-soundness:research/near-compression/final-soundness/PROOF.md`, `docs/zk-formal/V3-PERF-DESIGN.md`

### [Hab22]

- **Citation:** U. Haböck. *Multivariate lookups based on logarithmic derivatives (LogUp)*. ePrint 2022/1530, 2022. <https://eprint.iacr.org/2022/1530>
- **Topics:** T6 · **Relevance:** U — used (interactions/buses)
- **Gives:** LogUp lookup/permutation argument.
- **Where in repo:** `docs/zk-formal/V3-PERF-DESIGN.md`

### [HyperPlonk]

- **Citation:** B. Chen, B. Bünz, D. Boneh, Z. Zhang. *HyperPlonk: Plonk with Linear-Time Prover and High-Degree Custom Gates*. EUROCRYPT 2023; ePrint 2022/1355, 2022. <https://eprint.iacr.org/2022/1355>
- **Topics:** T6 · **Relevance:** C — cited (background)
- **Gives:** Multilinear zerocheck PIOP; baseline for Gruen's tweaks.

### [Virgo20]

- **Citation:** J. Zhang, T. Xie, Y. Zhang, D. Song. *Transparent Polynomial Delegation and Its Applications to Zero Knowledge Proof (Virgo)*. S&P 2020; ePrint 2019/1482, 2020. <https://eprint.iacr.org/2019/1482>
- **Topics:** T6, T1 · **Relevance:** C — cited (background)
- **Gives:** GKR with FRI-based commitment; transparent, PQ-plausible.

### [Libra19]

- **Citation:** T. Xie, J. Zhang, Y. Zhang, C. Papamanthou, D. Song. *Libra: Succinct Zero-Knowledge Proofs with Optimal Prover Computation*. CRYPTO 2019; ePrint 2019/317, 2019. <https://eprint.iacr.org/2019/317>
- **Topics:** T6 · **Relevance:** C — cited (background)
- **Gives:** Linear-time GKR prover for arbitrary circuits.

### [Spartan]

- **Citation:** S. Setty. *Spartan: Efficient and general-purpose zkSNARKs without trusted setup*. CRYPTO 2020; ePrint 2019/550, 2019. <https://eprint.iacr.org/2019/550>
- **Topics:** T6 · **Relevance:** C — cited (formal status)
- **Gives:** Sumcheck-based SNARK for R1CS.
- **Where in repo:** `docs/research/formal-ecosystem.md`

### [Thaler13]

- **Citation:** J. Thaler. *Time-Optimal Interactive Proofs for Circuit Evaluation*. CRYPTO 2013; ePrint 2013/351, 2013. <https://eprint.iacr.org/2013/351>
- **Topics:** T6 · **Relevance:** N — not-yet-evaluated (template for per-round SHA GKR)
- **Gives:** Linear-time GKR prover for data-parallel circuits.

### [GKR08]

- **Citation:** S. Goldwasser, Y. T. Kalai, G. N. Rothblum. *Delegating Computation: Interactive Proofs for Muggles*. STOC 2008; JACM 2015, 2008. <https://doi.org/10.1145/2699436>
- **Topics:** T6 · **Relevance:** U — used (via LogUp-GKR)
- **Gives:** The GKR interactive proof for layered circuits.

### [LFKN92]

- **Citation:** C. Lund, L. Fortnow, H. Karloff, N. Nisan. *Algebraic Methods for Interactive Proof Systems (sumcheck)*. JACM 1992, 1992. <https://doi.org/10.1145/146585.146605>
- **Topics:** T6 · **Relevance:** U — used
- **Gives:** The sumcheck protocol.

## T7. zkVMs, production provers and GPU provers


### [Airbender]

- **Citation:** Matter Labs (ZKsync). *ZKsync Airbender / Airbender Prime (RISC-V prover; GKR+WHIR in Prime)*. zksync.io/airbender, 2026. <https://www.zksync.io/blog/introducing-airbender-prime>
- **Topics:** T7 · **Relevance:** E — evaluated (direct-wasm lane used Airbender code)
- **Gives:** Fast GPU RISC-V prover; Prime announces GKR, WHIR, BLAKE2s.
- **Numbers:** 21.8 MHz on one H100 (cited).
- **Where in repo:** `docs/zk-formal/V3-PERF-DESIGN.md`, `lane/pq-native-hermetic:docs/logs/direct-wasm-pq-compression-2026-10.md`, `lane/pq-native-hermetic:research/near-compression/airbender/`

### [AirbenderPrime]

- **Citation:** Matter Labs. *Airbender Prime (GKR + WHIR + BLAKE2s, single GPU)*. zksync-airbender repo / announcement 2026-10-13, 2026. <https://github.com/matter-labs/zksync-airbender>
- **Topics:** T7, T10 · **Relevance:** N — not-yet-evaluated (latency bar; same GKR+WHIR family)
- **Gives:** 99 % of 7,200 blocks < 10 s on one RTX PRO 6000; 'post-quantum' (hash-based); security bits and size undisclosed.

### [ICICLE]

- **Citation:** Ingonyama. *ICICLE GPU acceleration library*. GitHub ingonyama-zk/icicle, 2026. <https://github.com/ingonyama-zk/icicle>
- **Topics:** T7 · **Relevance:** N — not-yet-evaluated (v4.0.0, last push 2025-11; no WHIR/BabyBear-Ext12 support found)
- **Gives:** GPU NTT/MSM/hash/sumcheck primitives.

### [Jolt]

- **Citation:** a16z crypto. *Jolt zkVM (Lasso/Twist/Shout; Dory and Akita backends)*. GitHub a16z/jolt, 2026. <https://github.com/a16z/jolt>
- **Topics:** T7, T6 · **Relevance:** R — evaluated-rejected (Dory EC; Akita = lattice track)
- **Gives:** Sumcheck/lookup-centric zkVM; Lattice-Jolt with Akita.
- **Numbers:** Lattice Jolt <100 KB proofs.
- **Where in repo:** `lane/pq-native-hermetic:docs/logs/direct-wasm-pq-compression-2026-10.md`, `docs/research/formal-ecosystem.md`, `lane/pq-lattice-qrom:research/near-compression/lattice-study/B-modern-lattice.md`

### [JoltLattice26]

- **Citation:** a16z crypto, LayerZero. *Lattice Jolt (Akita PCS)*. a16zcrypto.com, 2026-09-09, 2026. <https://a16zcrypto.com/posts/article/lattice-snarks-jolt-post-quantum-faster>
- **Topics:** T7, T5 · **Relevance:** E — evaluated (lattice long shot)
- **Gives:** Post-quantum lattice Jolt, < 100 KB, 2M cycles/s on CPU.
- **Where in repo:** `lane/pq-lattice-qrom:research/near-compression/lattice-study/B-modern-lattice.md`

### [Miden]

- **Citation:** 0xMiden. *Miden VM / compiler*. GitHub 0xMiden/compiler, 2026. <https://github.com/0xMiden/compiler>
- **Topics:** T7, T12 · **Relevance:** C — cited
- **Gives:** STARK VM with Wasm-to-Miden compiler.
- **Where in repo:** `docs/research/wasm-formal-survey.md`

### [Miden-VM]

- **Citation:** 0xMiden. *miden-vm*. GitHub 0xMiden/miden-vm, 2026. <https://github.com/0xMiden/miden-vm>
- **Topics:** T7 · **Relevance:** C — cited
- **Gives:** Goldilocks^2 FRI.
- **Numbers:** soundcalc 38 UDR / 55 JBR, 112/149 KiB.

### [Nexus]

- **Citation:** Nexus. *Nexus zkVM*. GitHub nexus-xyz/nexus-zkvm, 2026. <https://github.com/nexus-xyz/nexus-zkvm>
- **Topics:** T7 · **Relevance:** C — cited
- **Gives:** RISC-V zkVM (folding lineage).
- **Where in repo:** `docs/research/wasm-formal-survey.md`

### [OVM-AUD26]

- **Citation:** zkSecurity. *Audit report: OpenVM 2.0*. reports.zksecurity.xyz, 2026. <https://reports.zksecurity.xyz/reports/openvm.md>
- **Topics:** T7, T9 · **Relevance:** N — not-yet-evaluated
- **Gives:** Audit of OpenVM 2.0; recursive verifier is 39 AIRs on buses.

### [OVM2-blog]

- **Citation:** OpenVM team. *OpenVM 2.0 Beta announcement*. blog.openvm.dev, 2026. <https://blog.openvm.dev/2.0-beta>
- **Topics:** T7, T10 · **Relevance:** E — evaluated (not PQ128 under our model)
- **Gives:** Published claim <300 kB proof, 100-bit provable PQ security.
- **Where in repo:** `lane/pq-native-hermetic:docs/logs/direct-wasm-pq-compression-2026-10.md`, `lane/pq-native-hermetic:docs/logs/pq-final-layer-model-2026-10-17.md`

### [OVM2-prod]

- **Citation:** Axiom. *OpenVM 2.0 production release*. axiom.xyz/blog/openvm-2-production, 2026-07-10, 2026. <https://axiom.xyz/blog/openvm-2-production>
- **Topics:** T7, T10 · **Relevance:** E — evaluated
- **Gives:** SWIRL, BabyBear^4, 256-bit hash; P99 9.8 s on 8 GPUs, 6.3 s on 16; < 300 kB; 100-bit provable; GPU prover open.
- **Numbers:** Root soundcalc: log_blowup 4, WHIR queries [57,28,19], 20-bit grinding, 270 KiB, JBR.

### [OVM21]

- **Citation:** Axiom. *OpenVM 2.1 Preview (portable native recompilation, RV64IM)*. axiom.xyz/blog/2-1, 2026-07-29, 2026. <https://axiom.xyz/blog/2-1>
- **Topics:** T7 · **Relevance:** N — not-yet-evaluated (latency lever: native recompilation)
- **Gives:** 9.7 s P99 on 4x5090, 3.7 s on 16; guest compiled to C for native execution.

### [OpenVM]

- **Citation:** OpenVM contributors (Axiom, Scroll). *OpenVM (modular zkVM; v2.x stark-backend, recursion crate)*. GitHub openvm-org/openvm, 2026. <https://github.com/openvm-org/openvm>
- **Topics:** T7 · **Relevance:** U — used (pinned d667af5; recursion port)
- **Gives:** Our backend source; recursion crate ported to SHA-384/Ext12.
- **Numbers:** OpenVM 2.0 beta: <300 kB, 100-bit provable PQ (Poseidon2); ported 46-AIR verifier 3,481-3,923 columns.
- **Where in repo:** `lane/pq-recursion-sha384:research/near-compression/results/pq-recursion-sha384/README.md`, `lane/pq-recursion-sha384:research/near-compression/results/pq-recursion-nv/README.md`, `lane/pq-native-hermetic:docs/logs/direct-wasm-pq-compression-2026-10.md`, `docs/research/formal-ecosystem.md`

### [P3-recursion]

- **Citation:** Plonky3 contributors. *Plonky3-recursion (hashing architecture)*. plonky3.github.io/Plonky3-recursion, 2026. <https://plonky3.github.io/Plonky3-recursion/architecture_and_internals/hashing.html>
- **Topics:** T7, T4 · **Relevance:** C — cited
- **Gives:** Recursion design for Plonky3.
- **Where in repo:** `lane/pq-native-hermetic:docs/logs/direct-wasm-pq-compression-2026-10.md`

### [Plonky3]

- **Citation:** Polygon Zero / Plonky3 contributors. *Plonky3 toolkit (BabyBear/KoalaBear/M31, FRI, uni-stark, security calculator)*. GitHub Plonky3/Plonky3, 2026. <https://github.com/Plonky3/Plonky3>
- **Topics:** T7, T1 · **Relevance:** U — used (examples/stark-plonky3)
- **Gives:** STARK toolkit; our stark-plonky3 example prover; p3-security calculator.
- **Numbers:** stark-plonky3: 7.14 MB proof; proven UDR 102.5 bits.
- **Where in repo:** `examples/stark-plonky3/README.md`, `docs/research/formal-ecosystem.md`, `lane/pq-native-hermetic:docs/logs/direct-wasm-pq-compression-2026-10.md`

### [RISC0]

- **Citation:** RISC Zero. *RISC Zero zkVM (R0VM, recursion circuit, Groth16 wrapper)*. dev.risczero.com/proof-system, 2026. <https://dev.risczero.com/proof-system/>
- **Topics:** T7 · **Relevance:** E — evaluated (v1 verifier wrapped in RISC Zero 3.0.6 experiment)
- **Gives:** Succinct receipts aggregate segment proofs via recursion; Groth16 wrapper.
- **Numbers:** ~200 kB succinct receipts (cited); RISC Zero 1.1 MHz (PERF).
- **Where in repo:** `docs/research/recursive-compression.md`, `lane/pq-native-hermetic:docs/logs/direct-wasm-pq-compression-2026-10.md`

### [SP1]

- **Citation:** Succinct Labs. *SP1 / SP1 Hypercube zkVM (Jagged PCS, LogUp-GKR)*. GitHub succinctlabs/sp1; docs.succinct.xyz, 2026. <https://github.com/succinctlabs/sp1>
- **Topics:** T7 · **Relevance:** R — evaluated-rejected (EC global memory; Jagged PCS idea noted)
- **Gives:** RISC-V zkVM; Hypercube uses multilinear jagged PCS; retains EC assumptions for global memory.
- **Numbers:** SP1 Turbo 3.45 MHz (cited in PERF).
- **Where in repo:** `lane/pq-native-hermetic:docs/logs/direct-wasm-pq-compression-2026-10.md`, `docs/research/formal-ecosystem.md`, `docs/zk-formal/V3-PERF-DESIGN.md`

### [SP1-GPU]

- **Citation:** Succinct Labs. *sp1-gpu kernels (logup_gkr, zerocheck, jagged_sumcheck, merkle_tree, ntt, challenger)*. GitHub succinctlabs/sp1 (sp1-gpu/), 2026. <https://github.com/succinctlabs/sp1>
- **Topics:** T7 · **Relevance:** N — not-yet-evaluated (reference kernels for our H200 port)
- **Gives:** Open GPU kernels for LogUp-GKR / zerocheck.

### [Stwo]

- **Citation:** StarkWare. *S-two (Stwo) prover; Circle STARKs over M31; dedicated recursion circuit*. GitHub starkware-libs/stwo, 2026. <https://starkware.co/blog/minutes-to-seconds-efficiency-gains-with-recursive-circuit-proving/>
- **Topics:** T7 · **Relevance:** E — evaluated (supports narrow verifier circuit idea)
- **Gives:** Specialised verifier circuit replaces general Cairo verifier execution.
- **Numbers:** S-two 2.0.0 (2026-01-27); no L1 real-time or security-bit figures.
- **Where in repo:** `lane/pq-native-hermetic:docs/logs/direct-wasm-pq-compression-2026-10.md`

### [Stwo2]

- **Citation:** StarkWare. *S-two 2.0.0*. GitHub starkware-libs/stwo, 2026. <https://github.com/starkware-libs/stwo>
- **Topics:** T7 · **Relevance:** C — cited
- **Gives:** Circle STARK over M31.

### [Venus]

- **Citation:** Cysic. *Venus (ZisK fork with CUDA graphs, FPGA backend)*. GitHub cysic-labs/venus, 2026. <https://github.com/cysic-labs/venus>
- **Topics:** T7 · **Relevance:** N — not-yet-evaluated
- **Gives:** FPGA/ASIC path for Goldilocks STARKs.
- **Numbers:** 128 JBR, 269/313 KiB.

### [Ziren26]

- **Citation:** ZKM. *Ziren: MIPS zkVM with Jagged sumcheck and batched WHIR*. ePrint 2026/2330, 2026. <https://eprint.iacr.org/2026/2330>
- **Topics:** T7, T4 · **Relevance:** N — not-yet-evaluated (add union-bound term for composed shard proofs)
- **Gives:** Explicit composite-security accounting: union bound over 149-proof tree gives 93.5 bits.
- **Numbers:** 12.0 MHz 1x5090, 75.8 MHz on 8.

### [ZisK]

- **Citation:** Polygon / SilentSig. *ZisK zkVM (pil2-proofman GPU prover)*. GitHub 0xPolygonHermez/zisk, 2026. <https://github.com/0xPolygonHermez/zisk>
- **Topics:** T7 · **Relevance:** N — not-yet-evaluated
- **Gives:** Goldilocks^3 FRI Poseidon2; open GPU code; 128 JBR.
- **Numbers:** Final_Compressed 269/313 KiB at 128 JBR; 9.62 s P99 on 4x5090 (self-reported).

### [ZisK-GHSA26]

- **Citation:** ZisK. *Recursive aggregation soundness fix (GHSA-3j5v-j2rm-9c5f, v1.3.2-alpha)*. GitHub advisory, 2026. <https://github.com/0xPolygonHermez/zisk/security/advisories/GHSA-3j5v-j2rm-9c5f>
- **Topics:** T7, T4 · **Relevance:** N — not-yet-evaluated (lesson for cross-shard aggregation)
- **Gives:** Null-child proofs disabled aggregate checks; fix: canonical null children, >= 1 real child.

### [cuPQC]

- **Citation:** NVIDIA. *cuPQC SDK v0.6 (batched SHA-2/SHA-3 hashing, Merkle trees)*. NVIDIA developer docs, 2026-04-09, 2026. <https://docs.nvidia.com/cuda/cupqc/>
- **Topics:** T7, T8 · **Relevance:** N — not-yet-evaluated (fast H200 SHA-384 Merkle/grinding prototype; license check)
- **Gives:** GPU batched SHA-512 and Merkle trees (no SHA-384 Merkle mode; SHA-384 = SHA-512 compression + IV).
- **Numbers:** Poseidon2 Merkle 2^24 leaves in 39 ms on RTX PRO 6000.

### [leanVM]

- **Citation:** Ethereum Foundation (leanEthereum). *leanVM / leanMultisig*. GitHub leanEthereum/leanMultisig, 2026. <https://github.com/leanEthereum/leanMultisig>
- **Topics:** T7, T10 · **Relevance:** N — not-yet-evaluated (EF PQ team settles for 64-bit QROM; ours is far stricter)
- **Gives:** EF PQ VM: WHIR over 192-bit binary-ext field, Johnson regime via BCHKS25; claims 128-bit ROM / 64-bit QROM.
- **Numbers:** 2->1 recursion 200.5 KiB at rate 1/4, 0.29 s M4 Max.

### [powdr]

- **Citation:** powdr labs. *powdr (zkVM toolkit / autoprecompiles)*. GitHub powdr-labs/powdr, 2026. <https://github.com/powdr-labs/powdr>
- **Topics:** T7 · **Relevance:** C — cited
- **Gives:** zkVM compiler toolkit.
- **Where in repo:** `docs/research/wasm-formal-survey.md`

### [stark-backend]

- **Citation:** OpenVM contributors. *openvm-org/stark-backend v2.0.x (incl. cuda-backend)*. GitHub openvm-org/stark-backend, 2026. <https://github.com/openvm-org/stark-backend>
- **Topics:** T7, T1, T6 · **Relevance:** U — used (CPU path, pinned d667af5); CUDA backend not yet ported to SHA-384/Ext12
- **Gives:** Our pinned backend; CUDA kernels whir.cu, merkle_tree.cu, gkr.cu, zerocheck_round0.cu, stacked_reduction.cu (no SHA-2 Merkle kernel).
- **Where in repo:** `lane/pq-recursion-sha384:research/near-compression/results/pq-recursion-sha384/README.md`, `lane/pq-whir-levers:research/near-compression/results/pq-whir-levers/README.md`

### [whir-p3-metal]

- **Citation:** PSE. *whir-p3-metal (GPU WHIR on Metal)*. GitHub privacy-ethereum/whir-p3-metal, 2026. <https://github.com/privacy-ethereum/whir-p3-metal>
- **Topics:** T7, T1 · **Relevance:** N — not-yet-evaluated
- **Gives:** Fused NTT, Merkle and PoW on GPU.

### [zkDTVM]

- **Citation:** (owner unverified). *zkDTVM v0.8.0 (root_shrink: SWIRL+WHIR with SHA-256 Merkle root)*. soundcalc reports/zkdtvm.md, 2026. <https://github.com/ethereum/soundcalc>
- **Topics:** T7, T10 · **Relevance:** N — not-yet-evaluated (compare shape with our NV final layer)
- **Gives:** Closest public analogue of our final layer: SWIRL+WHIR root, JBR m=2, KoalaBear^5, SHA-256 Merkle at the root.
- **Numbers:** 128-bit classical, 200 KiB; log_blowup 4, queries [77,38,26], 20-bit grinding, 326 columns, 50 AIRs.

### [Binius64]

- **Citation:** Irreducible / binius-zk. *Binius64 (word-oriented binary-field prover)*. GitHub binius-zk/binius64, 2025. <https://github.com/binius-zk/binius64>
- **Topics:** T7, T8, T1 · **Relevance:** E — evaluated (lane: 341,716 B hash graph at 128-bit query budget; untested for SHA)
- **Gives:** Binary-field PCS/prover efficient for bitwise hashes.
- **Numbers:** Fixed hash graph 341,716 B @128-bit queries, 643,444 B @272.
- **Where in repo:** `lane/pq-native-hermetic:docs/logs/direct-wasm-pq-compression-2026-10.md`, `lane/pq-native-hermetic:docs/logs/pq-final-layer-model-2026-10-17.md`

### [Overhead]

- **Citation:** Succinct Labs. *succinctlabs/overhead (wasmi-in-SP1 overhead benchmark)*. GitHub, 2025. <https://github.com/succinctlabs/overhead>
- **Topics:** T7, T12 · **Relevance:** C — cited
- **Gives:** ~17 RV32 cycles per Wasm instruction for wasmi in SP1.
- **Where in repo:** `docs/research/wasm-formal-survey.md`

### [PicoPrism]

- **Citation:** Brevis. *Pico Prism*. GitHub brevis-network/pico, 2025. <https://github.com/brevis-network/pico>
- **Topics:** T7 · **Relevance:** N — not-yet-evaluated
- **Gives:** 99.6 % blocks < 12 s on 64x5090.
- **Numbers:** soundcalc: 53-bit JBR, 281 KiB (old params).

### [SP1-RT16]

- **Citation:** Succinct Labs. *Real-time proving with 16 GPUs*. blog.succinct.xyz, 2025. <https://blog.succinct.xyz/real-time-proving-16-gpus/>
- **Topics:** T7, T10 · **Relevance:** C — cited
- **Gives:** 99.7 % of blocks < 12 s on 16x5090 (SP1 Hypercube).
- **Numbers:** SP1 6.1: 100-bit UDR, 529/887 KiB before BN254 wrap.

## T8. Hash circuits (SHA-2 AIRs/chips, lookup designs)


### [BinSpartan26]

- **Citation:** S. Setty. *BinarySpartan*. ePrint 2026/1656, 2026. <https://eprint.iacr.org/2026/1656>
- **Topics:** T8, T6 · **Relevance:** N — not-yet-evaluated
- **Gives:** Spartan over binary fields with Ligerito + ring switching.
- **Numbers:** 401k SHA-256/s on 12 cores.

### [Cor26-sha]

- **Citation:** T. Coratger (unofficial note). *SHA-256 arithmetization survey (ZisK, Stwo rookie-numbers, SP1, RISC0)*. hackmd.io/@tcoratger/HJFGugU0Ze, 2026. <https://hackmd.io/@tcoratger/HJFGugU0Ze>
- **Topics:** T8 · **Relevance:** N — not-yet-evaluated
- **Gives:** Cells per SHA-256 compression across zkVMs; add3/add4 fusion tricks.
- **Numbers:** ZisK ~7,350; Stwo ~7,840; SP1 ~22-25k cells per SHA-256 compression.

### [Flock26]

- **Citation:** B. Bünz, R. D. Rothblum, W. Wang. *Flock: batched Boolean R1CS over binary fields*. ePrint 2026/1329, 2026. <https://eprint.iacr.org/2026/1329>
- **Topics:** T8, T6 · **Relevance:** N — not-yet-evaluated
- **Gives:** Batched Boolean R1CS with ring switching.
- **Numbers:** ~42k SHA-256 compressions/s on one M4 core (>9x Binius64).

### [NP-SHA-AIR1]

- **Citation:** NEAR Proof (lane/pq-sha384-air). *Narrow SHA-512-compression AIR on BabyBear (L3 milestone 1)*. internal, 2026.
- **Topics:** T8 · **Relevance:** U — used (superseded)
- **Gives:** 2 rounds/row, 44 rows x 442 columns.
- **Numbers:** 19,448 committed cells/compression; N=1,024 SHA-only proof 874,845 B, 67.7 s.
- **Where in repo:** `lane/pq-sha384-air:research/near-compression/results/pq384-sha-air/README.md`, `lane/pq-native-hermetic:docs/logs/pq-final-layer-model-2026-10-17.md`

### [NP-SHA-AIR2]

- **Citation:** NEAR Proof (lane/pq-sha384-air2). *Slim SHA-512-compression AIR: base-8 digits, bus residuals, polynomial carries*. internal, 2026.
- **Topics:** T8 · **Relevance:** U — used (current)
- **Gives:** Current SHA AIR for the narrow verifier.
- **Numbers:** 7,524 cells/compression (7,353 NF-7), 171+13 columns, degree 21, 14 interactions/row.
- **Where in repo:** `lane/pq-sha384-air2:research/near-compression/results/pq384-sha-air2/README.md`, `lane/pq-native-hermetic:docs/logs/pq-final-layer-model-2026-10-17.md`, `docs/research/NOVEL-FINDINGS.md`

### [OVM-SHA]

- **Citation:** OpenVM contributors. *OpenVM SHA-256 / SHA-512 chips (and openvm-fv proofs)*. GitHub openvm-org/openvm, 2026. <https://github.com/openvm-org/openvm>
- **Topics:** T8, T9 · **Relevance:** U — used (reference: ~12k cells per SHA-256 compression)
- **Gives:** Production SHA-2 chips; formally verified vs FIPS models in openvm-fv.
- **Numbers:** ~12k cells/compression SHA-256 (cited); SHA-512 ~2x.
- **Where in repo:** `lane/pq-native-hermetic:docs/logs/pq-final-layer-model-2026-10-17.md`, `docs/research/formal-ecosystem.md`

### [OVM-sha2air]

- **Citation:** OpenVM contributors. *openvm sha2-air crate (SHA-256/SHA-512 AIR)*. GitHub openvm-org/openvm crates/circuits/sha2-air, 2026. <https://github.com/openvm-org/openvm/tree/main/crates/circuits/sha2-air>
- **Topics:** T8 · **Relevance:** E — evaluated (our AIR2 is ~2.6x fewer cells)
- **Gives:** 4 rounds/row, a/e/w as bits; 21 rows x ~900 cols per SHA-512 block.
- **Numbers:** ~19k cells per SHA-512 compression (from columns.rs).
- **Where in repo:** `lane/pq-native-hermetic:docs/logs/pq-final-layer-model-2026-10-17.md`

### [P3-binsha]

- **Citation:** Plonky3 contributors. *Plonky3 binary-field SHA-256 AIR (PR #2207)*. GitHub Plonky3 PR #2207, 2026. <https://github.com/Plonky3/Plonky3/pull/2207>
- **Topics:** T8 · **Relevance:** N — not-yet-evaluated
- **Gives:** Stores only new a, e per round; degree 2; binary PCS.
- **Numbers:** 23,712 bit columns; 799-856 KB proofs at 96 bits.

### [Keccacheck25]

- **Citation:** Reilabs. *Keccacheck: sumcheck/GKR batching for Keccak*. ePrint 2025/1764, 2025. <https://eprint.iacr.org/2025/1764>
- **Topics:** T8, T6 · **Relevance:** N — not-yet-evaluated (evidence GKR cuts committed hash cells ~10x)
- **Gives:** < 4,000 constraints per Keccak permutation in batches.

### [P3-sha256air]

- **Citation:** Plonky3 contributors. *p3-sha256-air*. docs.rs/p3-sha256-air, 2025. <https://docs.rs/p3-sha256-air>
- **Topics:** T8 · **Relevance:** N — not-yet-evaluated
- **Gives:** One row per SHA-256 compression, degree <= 3, no lookups.
- **Numbers:** ~7,488 cells per SHA-256 compression.

### [SHA3-GKR24]

- **Citation:** (ePrint 2024/1212). *Layered SHA3 Merkle circuit for GKR*. ePrint 2024/1212, 2024. <https://eprint.iacr.org/2024/1212>
- **Topics:** T8, T6 · **Relevance:** N — not-yet-evaluated
- **Gives:** Layered hash circuit template for GKR.

### [Halo2-t16]

- **Citation:** Zcash. *Halo2 book: SHA-256 table16 (spread tables)*. zcash.github.io/halo2, 2021. <https://zcash.github.io/halo2/design/gadgets/sha256/table16.html>
- **Topics:** T8 · **Relevance:** N — not-yet-evaluated
- **Gives:** Spread/sparse lookup encoding for bitwise ops.

### [LLZ20-GKRhash]

- **Citation:** T. Liu, X. Liang, Y. Zhang. *Using GKR inside a SNARK to reduce the cost of hash verification down to 3 constraints*. ethresear.ch 7550, 2020. <https://ethresear.ch/t/using-gkr-inside-a-snark-to-reduce-the-cost-of-hash-verification-down-to-3-constraints/7550>
- **Topics:** T8, T6 · **Relevance:** N — not-yet-evaluated (our L4-C killed 'GKR-proven SHA' at full depth; per-round variant open)
- **Gives:** Commit only hash I/O, prove hash by GKR.
- **Where in repo:** `lane/pq-x15-domains:research/near-compression/l4-study/C-invention.md`

## T9. Formal verification of ZK systems


### [Aeneas]

- **Citation:** AeneasVerif. *Aeneas (Rust to Lean via Charon); hax*. GitHub AeneasVerif/aeneas; cryspen/hax, 2026. <https://github.com/AeneasVerif/aeneas>
- **Topics:** T9 · **Relevance:** E — evaluated
- **Gives:** Only realistic Rust->Lean route.
- **Where in repo:** `docs/research/formal-ecosystem.md`

### [ArkLib]

- **Citation:** Verified-zkEVM. *ArkLib: formally verified arguments of knowledge in Lean*. GitHub Verified-zkEVM/ArkLib, 2026. <https://github.com/Verified-zkEVM/ArkLib>
- **Topics:** T9 · **Relevance:** E — evaluated (style reused, not imported: DESIGN F4)
- **Gives:** IOP/IOR framework; sumcheck soundness, Johnson bound, BCIKS20 UDR proven; FS/FRI/WHIR largely sorry.
- **Numbers:** 171 real sorry in ArkLib/ (2026-10-02).
- **Where in repo:** `docs/research/formal-ecosystem.md`, `docs/research/checker-recommendations.md`, `lane/pq-lattice-qrom:docs/zk-formal/PQ-LATTICE-QROM-PLAN.md`, `lane/pq-lattice-qrom:research/near-compression/lattice-study/C-security.md`

### [Clean]

- **Citation:** Verified-zkEVM. *clean: Lean DSL for ZK circuits with soundness/completeness proofs*. GitHub Verified-zkEVM/clean, 2026. <https://github.com/Verified-zkEVM/clean>
- **Topics:** T9, T8 · **Relevance:** E — evaluated
- **Gives:** Circuit DSL used by sp1-lean.
- **Where in repo:** `docs/research/formal-ecosystem.md`

### [EF-SP1FV26]

- **Citation:** Ethereum Foundation. *On Formal Verification and a Bug in SP1 Hypercube*. zkevm.ethereum.foundation blog, 2026-05-20, 2026. <https://zkevm.ethereum.foundation/blog/sp1-fv>
- **Topics:** T9, T7 · **Relevance:** N — not-yet-evaluated (lesson: conformance tests beside Lean proofs)
- **Gives:** JALR completeness bug missed by FV (hypothesis assumed it away), found by conformance tests.

### [HOPSCOTCH]

- **Citation:** S. Dziembowski, et al.. *HOPSCOTCH: Game Hopping in Lean*. arXiv 2608.06261, 2026. <https://arxiv.org/abs/2608.06261>
- **Topics:** T9 · **Relevance:** N — not-yet-evaluated
- **Gives:** Lean 4 game-hopping framework.

### [LeanCheckers]

- **Citation:** leanprover, ammkrn, digama0. *lean4export, lean4checker, nanoda_lib, lean4lean, comparator*. GitHub, 2026. <https://github.com/leanprover/comparator>
- **Topics:** T9 · **Relevance:** U — used (judge checker recommendations)
- **Gives:** Independent kernel rechecking and statement comparison.
- **Where in repo:** `docs/research/checker-recommendations.md`, `docs/research/formal-ecosystem.md`

### [Mar26-IsaSTARK]

- **Citation:** D. Marmsoler. *Isabelle/STARK: query-bounded STARK soundness*. arXiv 2608.01965, 2026. <https://arxiv.org/abs/2608.01965>
- **Topics:** T9, T1 · **Relevance:** N — not-yet-evaluated (closest end-to-end mechanised STARK; no QROM)
- **Gives:** Mechanised STARK soundness with FRI CA, Merkle, adaptive FS game (classical ROM).

### [VCVio]

- **Citation:** Verified-zkEVM. *VCV-io: Lean library for oracle computations and ROM proofs*. GitHub Verified-zkEVM/VCVio, 2026. <https://github.com/Verified-zkEVM/VCVio>
- **Topics:** T9 · **Relevance:** E — evaluated
- **Gives:** Sorry-free ROM toolkit, forking lemma, FS for Sigma-protocols, Merkle extractability (ROM).
- **Where in repo:** `docs/research/formal-ecosystem.md`, `lane/pq-lattice-qrom:research/near-compression/lattice-study/C-security.md`

### [VCVio26]

- **Citation:** D. Tuma, Q. Dao, et al.. *VCV-io paper: verified cryptography via free-monad oracle computations*. ePrint 2026/899, 2026. <https://eprint.iacr.org/2026/899>
- **Topics:** T9 · **Relevance:** E — evaluated (with VCVio repo)
- **Gives:** Paper for VCV-io incl. LatticeCrypto library.
- **Where in repo:** `docs/research/formal-ecosystem.md`

### [VZK]

- **Citation:** Ethereum Foundation. *Verified zkEVM project (verified-zkevm.org)*. verified-zkevm.org, 2026. <https://verified-zkevm.org>
- **Topics:** T9, T10 · **Relevance:** E — evaluated
- **Gives:** EF formal-verification program: 3 tracks, 42 grants (ArkLib, Clean, zkLean, CertiPlonk...).
- **Where in repo:** `docs/research/formal-ecosystem.md`

### [openvm-fv]

- **Citation:** OpenVM. *openvm-fv: Lean verification of OpenVM chips*. GitHub openvm-org/openvm-fv, 2026. <https://github.com/openvm-org/openvm-fv>
- **Topics:** T9, T8 · **Relevance:** E — evaluated (model for our AIR proofs)
- **Gives:** 45 RV32IM opcodes + SHA-256/SHA-512/Keccak-f chips vs Sail/FIPS, axiom-clean, comparator CI.
- **Where in repo:** `docs/research/formal-ecosystem.md`

### [simple-rbr-fri]

- **Citation:** Y. Hirai (zkSecurity). *simple-rbr-fri: Lean 4 proof of FRI round-by-round soundness*. GitHub zksecurity/simple-rbr-fri, 2026. <https://github.com/zksecurity/simple-rbr-fri>
- **Topics:** T9, T1 · **Relevance:** N — not-yet-evaluated (reusable for our folding rbr in Lean)
- **Gives:** Lean rbr soundness of FRI; MCA taken as an axiom (BCGM25 would discharge it).

### [sp1-lean]

- **Citation:** Succinct Labs. *sp1-lean: Lean proofs of SP1 RV64IM chips*. GitHub succinctlabs/sp1-lean, 2026. <https://github.com/succinctlabs/sp1-lean>
- **Topics:** T9 · **Relevance:** E — evaluated
- **Gives:** 25 RV64IM chips proven; machine theorem has one sorry; proof system assumed.
- **Where in repo:** `docs/research/formal-ecosystem.md`

### [zkLean]

- **Citation:** Verified-zkEVM / Galois. *zkLean (Jolt extraction to Lean)*. GitHub Verified-zkEVM/zkLean, 2026. <https://github.com/Verified-zkEVM/zkLean>
- **Topics:** T9 · **Relevance:** E — evaluated
- **Gives:** Extract Jolt constraints to Lean.
- **Where in repo:** `docs/research/formal-ecosystem.md`

### [CertiPlonk]

- **Citation:** Nethermind. *CertiPlonk*. GitHub NethermindEth/CertiPlonk, 2025. <https://github.com/NethermindEth/CertiPlonk>
- **Topics:** T9 · **Relevance:** E — evaluated
- **Gives:** Lean Plonky3 constraint extraction.
- **Where in repo:** `docs/research/formal-ecosystem.md`

### [LZKC-P3]

- **Citation:** Nethermind. *LeanZKCircuit-Plonky3*. GitHub NethermindEth/LeanZKCircuit-Plonky3, 2025. <https://github.com/NethermindEth/LeanZKCircuit-Plonky3>
- **Topics:** T9 · **Relevance:** E — evaluated
- **Gives:** Plonky3 circuits in Lean.
- **Where in repo:** `docs/research/formal-ecosystem.md`

### [CertiK-zkWasm]

- **Citation:** CertiK. *zkwasm-fv: Coq proofs of zkWasm core circuits*. GitHub CertiKProject/zkwasm-fv, 2024. <https://github.com/CertiKProject/zkwasm-fv>
- **Topics:** T9, T12 · **Relevance:** E — evaluated
- **Gives:** 46.7k lines Coq; Halo2 circuit translation.
- **Where in repo:** `docs/research/wasm-formal-survey.md`

### [GBS24]

- **Citation:** A. Garvía Bosshard, J. Bootle, C. Sprenger. *Formal Verification of the Sumcheck Protocol*. CSF 2024; arXiv 2402.06093, 2024. <https://arxiv.org/abs/2402.06093>
- **Topics:** T9, T6 · **Relevance:** N — not-yet-evaluated
- **Gives:** Isabelle proof of sumcheck soundness (AFP).

### [Picus]

- **Citation:** Veridise. *Picus (underconstraint detection)*. GitHub Veridise/Picus, 2024. <https://github.com/Veridise/Picus>
- **Topics:** T9 · **Relevance:** E — evaluated
- **Gives:** Automated underconstrained-circuit detection.
- **Where in repo:** `docs/research/formal-ecosystem.md`

### [QED2]

- **Citation:** S. Pailoor, et al.. *Automated Detection of Under-Constrained Circuits in Zero-Knowledge Proofs (QED^2)*. PLDI 2023; ePrint 2023/512, 2023. <https://eprint.iacr.org/2023/512>
- **Topics:** T9 · **Relevance:** E — evaluated (with Picus)
- **Gives:** SMT check for under-constrained circuits.
- **Where in repo:** `docs/research/formal-ecosystem.md`

### [risc0-lean4]

- **Citation:** RISC Zero. *risc0-lean4*. GitHub risc0/risc0-lean4, 2023. <https://github.com/risc0/risc0-lean4>
- **Topics:** T9 · **Relevance:** E — evaluated
- **Gives:** Early Lean model of RISC Zero verifier (43 sorry).
- **Where in repo:** `docs/research/formal-ecosystem.md`

### [EC-ZK21]

- **Citation:** (arXiv 2104.05516). *Formalizing zero-knowledge proofs in EasyCrypt*. arXiv 2104.05516, 2021. <https://arxiv.org/abs/2104.05516>
- **Topics:** T9 · **Relevance:** C — cited
- **Gives:** EasyCrypt ZK formalization.
- **Where in repo:** `lane/pq-lattice-qrom:research/near-compression/lattice-study/C-security.md`

### [EasyPQC]

- **Citation:** M. Barbosa, G. Barthe, X. Fan, B. Grégoire, S.-H. Hung, J. Katz, P.-Y. Strub, X. Wu, L. Zhou. *EasyPQC: Verifying Post-Quantum Cryptography*. CCS 2021; ePrint 2021/1253, 2021. <https://eprint.iacr.org/2021/1253>
- **Topics:** T9, T3 · **Relevance:** N — not-yet-evaluated
- **Gives:** EasyCrypt extension for post-quantum (limited QROM) proofs.

## T10. Ethereum real-time proving and security standards


### [EF-8025]

- **Citation:** Ethereum Foundation. *EIP-8025: optional execution proofs*. zkevm.ethereum.foundation blog, 2026-05-14, 2026. <https://zkevm.ethereum.foundation/blog/eip-8025-optional-execution-proofs-hegota>
- **Topics:** T10 · **Relevance:** C — cited
- **Gives:** Gossiped optional execution proofs.

### [EF-SPRINT26]

- **Citation:** D. Khovratovich, A. Zapico, G. Kadianakis. *zkEVM Security Sprint: February Update*. zkevm.ethereum.foundation blog, 2026-02-11, 2026. <https://zkevm.ethereum.foundation/blog/cryptography-research-update>
- **Topics:** T10 · **Relevance:** E — evaluated
- **Gives:** M3 moved to early Dec 2026; whitepapers W1 (May 1), W2 (Sep 1), W3 (Dec 1: argument-of-knowledge sketch); soundcalc LogUp model.

### [ethproofs]

- **Citation:** Ethproofs. *ethproofs.org (real-time proving dashboard)*. ethproofs.org, 2026. <https://ethproofs.org>
- **Topics:** T10, T7 · **Relevance:** E — evaluated
- **Gives:** RTP-eligible = proofs <= 10 s; 2 of 9 eligible on 2026-10-18 (Axiom OpenVM 2.1 16x5090 99.99 %; ZisK 4x5090 99.90 %).

### [soundcalc]

- **Citation:** Ethereum Foundation. *soundcalc: zkVM soundness calculator*. GitHub ethereum/soundcalc, 2026. <https://github.com/ethereum/soundcalc>
- **Topics:** T10, T1, T2 · **Relevance:** N — not-yet-evaluated (add a nearproof TOML; O-4)
- **Gives:** Classical rbr security per circuit in UDR / JBR (BCHKS25); capacity regime removed after DG25/CS25; QROM deferred (cites CDHZ25). Has OpenVM2 (SWIRL/WHIR) and zkDTVM configs.
- **Numbers:** Summary: OpenVM2 100-bit 270 KiB; SP1 6.1 100-bit 529/887 KiB; ZisK/Venus 128 JBR 269/313 KiB; zkDTVM 128 200 KiB.

### [EF-BENCH25]

- **Citation:** Ethereum Foundation. *Benchmarking zkVMs for Ethereum*. zkevm.ethereum.foundation blog, 2025-10-22, 2025. <https://zkevm.ethereum.foundation/blog/benchmarking-zkvms>
- **Topics:** T10 · **Relevance:** N — not-yet-evaluated (state worst-case chunk latency)
- **Gives:** Worst-case EEST fixtures + P99 on historical blocks; worst-case blocks treated as DoS vectors.

### [EF-RTP25]

- **Citation:** S. Gold (Ethereum Foundation). *Shipping an L1 zkEVM #1: Realtime Proving*. blog.ethereum.org, 2025-07-10, 2025. <https://blog.ethereum.org/2025/07/10/realtime-proving>
- **Topics:** T10 · **Relevance:** E — evaluated (comparison in OPPORTUNITIES §EF)
- **Gives:** EF real-time proving target: P99 <= 10 s on mainnet blocks, <= $100k CAPEX, <= 10 kW, open source, >= 128-bit (100-bit interim), proof <= 300 KiB, no trusted setup (incl. wrappers). No PQ requirement.
- **Numbers:** 300 KiB = 307,200 B (ours 300,000 B); 10 s P99, not 12 s.

### [EF-SEC25]

- **Citation:** G. Kadianakis (Ethereum Foundation). *Shipping an L1 zkEVM #2: The Security Foundations*. blog.ethereum.org, 2025-12-18, 2025. <https://blog.ethereum.org/2025/12/18/zkevm-security-foundations>
- **Topics:** T10 · **Relevance:** E — evaluated
- **Gives:** Milestones: M1 soundcalc integration (Feb 2026); M2 100-bit provable + <= 600 KiB + recursion sketch (May 2026); M3 128-bit provable (soundcalc) + <= 300 KiB + formal recursion argument (end 2026). 'A bit of grinding' acceptable. Classical only.

## T12. Wasm semantics and zk-Wasm


### [Talos]

- **Citation:** Cajal Technologies. *Talos (Lean Wasm semantics)*. GitHub cajal-technologies/talos, 2026. <https://github.com/cajal-technologies/talos>
- **Topics:** T12, T9 · **Relevance:** E — evaluated
- **Gives:** Active Lean full-Wasm effort.
- **Where in repo:** `docs/research/wasm-formal-survey.md`

### [SpecTec]

- **Citation:** Wasm-DSL. *SpecTec (Wasm spec DSL) and spectec-lean*. GitHub Wasm-DSL/spectec, 2025. <https://github.com/Wasm-DSL/spectec>
- **Topics:** T12, T9 · **Relevance:** E — evaluated
- **Gives:** Official Wasm spec DSL with Lean backends.
- **Where in repo:** `docs/research/wasm-formal-survey.md`

### [WasmCert]

- **Citation:** WasmCert. *WasmCert-Coq and WasmCert-Isabelle*. GitHub WasmCert, 2025. <https://github.com/WasmCert/WasmCert-Coq>
- **Topics:** T12, T9 · **Relevance:** E — evaluated
- **Gives:** Mechanised Wasm semantics.
- **Where in repo:** `docs/research/wasm-formal-survey.md`

### [rWasm]

- **Citation:** Fluent Labs. *rWasm / fluentbase*. GitHub fluentlabs-xyz/rwasm, 2025. <https://github.com/fluentlabs-xyz/rwasm>
- **Topics:** T12, T7 · **Relevance:** E — evaluated
- **Gives:** Reduced Wasm IR for zk proving.
- **Where in repo:** `docs/research/wasm-formal-survey.md`

### [zkEngine]

- **Citation:** ICME Labs. *zkEngine (NovaNet zkWasm)*. GitHub ICME-Lab/zkEngine_dev, 2025. <https://github.com/ICME-Lab/zkEngine_dev>
- **Topics:** T12, T4 · **Relevance:** R — evaluated-rejected (curve-based)
- **Gives:** Folding-based zkWasm.
- **Where in repo:** `docs/research/wasm-formal-survey.md`

### [zkWasm]

- **Citation:** DelphinusLab. *zkWasm (Halo2/KZG zkVM for Wasm)*. GitHub DelphinusLab/zkWasm, 2024. <https://github.com/DelphinusLab/zkWasm>
- **Topics:** T12, T7 · **Relevance:** R — evaluated-rejected (KZG)
- **Gives:** Wasm zkVM; 4 ETable rows per instruction.
- **Numbers:** Logos test: 18 KB proof (Hept-100), 42.7 s CPU.
- **Where in repo:** `docs/research/wasm-formal-survey.md`

### [IrisWasm]

- **Citation:** Rao, Georges, Legoupil, Watt, et al.. *Iris-Wasm: Robust and Modular Verification of WebAssembly Programs*. PLDI 2023, 2023. <https://github.com/logsem/iriswasm>
- **Topics:** T12, T9 · **Relevance:** E — evaluated
- **Gives:** Separation-logic Wasm verification.
- **Where in repo:** `docs/research/wasm-formal-survey.md`
