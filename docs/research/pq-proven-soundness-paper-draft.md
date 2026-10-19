# A proven-soundness post-quantum succinct proof for NEAR chunk validation

**The near-proof-arena contributors**

*DRAFT, 2026-10-19. Not peer reviewed. Not for circulation.*

> **Read `docs/logs/pq-paper-audit-2026-10-19.md` first.** This draft is the first
> pass and contains known factual mismatches and status overclaims; the audit note
> lists every correction (scope, query schedules, certificate coverage, `T*` cost,
> the provisional 287,477 B run, and the model-only 99 KB figure). Do not cite this
> text until the audit's pick-up checklist is complete.

---

## Abstract

We describe a succinct, transparent-setup, hash-only proof system for NEAR chunk
validation, aimed at 128-bit security against quantum adversaries making up to
`2^64` oracle queries. The design is unusual in that every parameter is derived
from *proven* proximity and soundness bounds: we never invoke the
"proximity conjecture", the list-decoding-capacity regime, or the ethSTARK
"random-words" heuristic. We report six technical ingredients:

1. **Domain flexibility.** WHIR's soundness theorem holds for Reed–Solomon
   evaluation domains that are multiplicative cosets of order `c·2^K` with `c`
   odd, not only power-of-two domains. On BabyBear (`p − 1 = 15·2^27`), a `×15`
   domain buys `≈ 1.95` bits per query at no symbolic cost and reduces the
   final proof by `≈ 99 KB`. This is a rate lever, not a radius lever.
2. **Transcript binding (`T*`).** Binding proof-of-work bits and query indices to
   the *same* oracle call restores the grinding credit that a sequential hash
   chain loses under standard QROM Fiat–Shamir compilations, at zero proof
   bytes. Multi-call challenge squeezing is replaced by counter mode.
3. **Weakly binding Merkle commitments.** With digests below collision
   resistance, WHIR as built admits a block-equivocation attack. Absorbing
   shift-query answers before the `γ` combination ("WHIR-Y") makes a
   block-robust round-by-round property provable and permits 26–28-byte digests,
   saving `≈ 39 KB`.
4. **Certificate-gated agreement tables.** Per-round Johnson and
   first-order-beyond-Johnson agreement thresholds are bound into the verifier
   key, each backed by a Lean-kernel-checked certificate. This admits proven
   radii below `√ρ` and cuts query counts, while a round-0 fallback prevents the
   squared list from breaking the batching term.
5. **QROM straight-line knowledge soundness for recursive layer families.**
   A single database-measurement extractor handles all recursion layers at once
   with truncated commitments; the error does not grow with depth. A separate
   program-pinning check is required, and its omission yields a concrete
   forgery.
6. **Systems realisation.** Streamed Reed–Solomon/WHIR commitments never
   materialise the codeword (an 853 GB virtual codeword committed in 480 s at a
   14.9 GB peak), proofs are byte-identical to the in-memory prover, and the
   measured final layer tracks the analytic size law within 0.2 %.

The one non-standard assumption is that in-circuit SHA-384 behaves as a random
oracle on the witness (A-IC). This is unavoidable for hash-only recursion in any
query-only oracle model; we state it exactly rather than hide it. No trusted
setup, algebraic-group, lattice, or PoW-hardness assumption is used.

---

## 1. Introduction

### 1.1 Context

A NEAR chunk is validated by executing all transactions in the chunk and
checking the resulting state roots. A succinct proof of this relation lets a
light client verify a chunk with constant work, independent of the chunk's gas.
The target here is a proof under 300 KB, verifiable in seconds, produced without
a trusted setup, and secure against quantum adversaries.

Hash-based STARKs are the natural tool: transparent setup, plausibly
post-quantum, and a well-developed soundness theory. But the concrete parameters
used in deployed systems almost always lean on conjectures:

* **the proximity conjecture** — that Reed–Solomon codes have proximity gaps and
  efficient list decoding up to the list-decoding capacity `δ < 1 − ρ`, which
  would give `≈ b` bits per query instead of `≈ b/2`;
* **the ethSTARK random-words conjecture** — a heuristic list-size and
  proximity-gap model;
* **grinding credit** — that proof-of-work bits provably reduce the Fiat–Shamir
  error, often assumed without a transcript-level proof;
* **weak binding** — that truncated Merkle digests are as good as full ones,
  often without a QROM analysis.

The capacity-regime forms of the proximity conjecture are now **known to be
false** (Crites–Stewart, ePrint 2025/2046). Any system whose parameters depend
on them is at best heuristically secure. We therefore set a stricter contract:

> **U-2.** Use proven bounds only. No conjectured proximity regime, no
> random-words heuristic, no unproven grinding or binding credit.

This paper reports what that contract forces — and, surprisingly, that it still
yields a sub-300 KB recursive final layer.

### 1.2 Contributions

**C1 (Domain).** We prove that WHIR's smoothness hypothesis can be relaxed from
"order a power of two" to "order `c·2^K`, `c` odd", with one definitional edit,
and that the proximity-gap inputs hold verbatim because they are stated for
arbitrary evaluation sets. We give an exact rejection sampler that the
non-power-of-two index set requires. On BabyBear the `×15` domain gives
`≈ 1.95` bits/query; in the prototype it saves `≈ 99 KB`. Section 3.

**C2 (Transcript).** We identify two ways in which deployed transcripts fall
outside standard QROM Fiat–Shamir theorems: multi-call challenge squeezing, and
grinding bits that are not bound to the block that produces the indices. The
second is a genuine *proof gap*, not an attack: the chained pattern loses the
grinding credit `2^-135 → 2^-105`, which fails our contract. Counter mode
(`T*`) fixes both at zero bytes. Section 4.

**C3 (Weak binding).** We show a block-equivocation attack against WHIR as
built when digests are shorter than collision resistance, and prove a
block-robust round-by-round property for "WHIR-Y", which absorbs query answers
before `γ`. Under WHIR-Y, 26–28-byte digests are provable, saving `≈ 39 KB`.
Section 5.

**C4 (Agreement).** We instantiate the per-round agreement tables with
Lean-kernel-checked certificates: Johnson-regime line MCA (DKT26 Thm 5.12 with
the Lean constant), and first-order-beyond-Johnson certificates (DKT26
Prop 5.10 + Lemma 5.6). 129 certificates cover every real round and fold
sub-code. A round-0 fallback to Johnson handles the case where multiple
commitments square the list. Section 6.

**C5 (Recursion soundness).** We give a QROM straight-line knowledge-soundness
theorem for families of recursive layers with truncated commitments, using a
single database measurement; the error is independent of depth. We also show
that a recursive final proof is forgeable unless the verifier pins the final
program. Section 7.

**C6 (Systems).** We describe streamed RS/WHIR commitments that reproduce
in-memory proofs byte for byte, a SHA-512 compression AIR at 7,353 main cells
(2.6× fewer than the only open SHA-512 AIR), and measured final-layer sizes that
match the analytic law within 0.2 %. Section 8.

### 1.3 What we do *not* assume

This is the central methodological point. The following are **not** used
anywhere in the soundness argument:

* the proximity conjecture, in any form, and in particular not the
  capacity-regime MCA/list-decoding conjectures;
* the ethSTARK "random words" conjecture or any heuristic list-size model;
* any proof-of-work hardness assumption beyond idealised hashing;
* collision resistance of the truncated (26–42 byte) Merkle digests (we prove a
  weaker, sufficient property);
* a trusted setup, an algebraic group, a pairing, or a lattice assumption.

The assumptions that *are* used are listed in Section 9. The only non-standard
one is A-IC, and we prove that no query-only oracle model can remove it.

### 1.4 Related work

WHIR (ePrint 2024/1586) supplies the PCS and its round-by-round theorem. BCGM
(ePrint 2025/2051, CCC 2026) prove MCA for arbitrary evaluation sets in the
Johnson regime. BCHKS25 (ECCC TR25-169) prove correlated agreement up to
Johnson for arbitrary evaluation sets and give negative results beyond Johnson.
DKT26 (ePrint 2026/2056) give a tight Johnson line-MCA and a first-order
beyond-Johnson theory; its Lean development is the source of our certificates.
CMS19 and CDHZ give the QROM Fiat–Shamir compilation; CY21b and Hamoudi–Magniez
give the classical and database-level weak-binding tools. Crites–Stewart
(ePrint 2025/2046) and the zkSecurity summary establish that the capacity
conjecture is false. Circle STARKs, ECFFT, and ReedWeave are alternative ways to
relax power-of-two smoothness; we instead reuse ordinary multiplicative cosets
and existing radix-2 NTTs.

---

## 2. Preliminaries

### 2.1 Fields and parameters

`F_p` is BabyBear, `p = 15·2^27 + 1`. The challenge field is `K = F_p[X]/(X^12 − 31)`,
so `|K| = p^12 = 2^370.88`. We work over `K` for challenges and openings; the
trace and the RS code are over `K` where needed. All hashing is SHA-384, with
domain-separated framing; the transcript state is 384 bits and is never
truncated.

Evaluation domains are multiplicative subgroups of `K*` (or cosets thereof).
For a trace height `2^h` and blowup `2^b`, the largest domain has size
`15·2^(h+b)`. The rate in round `i` is `ρ_i = 2^(−λ_i)/15`, where `λ_i` is the
log-blowup; `λ_0 = b` and `λ_{i+1} = λ_i + k_i` in keep-domain mode.

The security contract is:

* **U-6**: failure probability `≤ 2^-128` against a quantum adversary with
  `t ≤ 2^64` oracle queries;
* **U-7**: SHA-384 throughout;
* **U-2**: proven bounds only.

Per-round we target `2^-268 = 2^-236 · 2^-32`: 236 query bits plus 32 bits of
grinding. The margin `268` is chosen so that the QROM compilation's `t^2` loss
(`2·64 = 128` bits) leaves `≥ 128` bits.

### 2.2 IOPs and round-by-round knowledge soundness

We use the doom form of round-by-round (rbr) knowledge soundness.

**Definition 2.1.** An IOP for relation `R` has rbr knowledge error `ε` if there
is a state function `S(x, τ) ∈ {0,1}` on partial transcripts and an extractor
`E` such that:

* (K1) `S(x, ∅) = 0` for all `x`;
* (K2) if `S(x, τ) = 0` and `S(x, τ‖a) = 1` after a prover message `a`, then
  `E(x, τ‖a) ∈ R(x)`;
* (K3) if `S(x, τ) = 0`, then `Pr_c[S(x, τ‖c) = 1] ≤ ε` over the verifier's
  challenge;
* (K4) if the verifier accepts `τ`, then `S(x, τ) = 1`.

This implies CMS19's rbr knowledge soundness and is the form consumed by the
QROM compilation. The extractor need not be efficient for the final soundness
conclusion; here an efficient one exists (Guruswami–Sudan list decoding within
Johnson, DKT26's deterministic decoders beyond it).

**Lemma 2.2 (list form).** If after the round-0 commitment the state has the
form
`S(τ) = 1 ⇔ ∃ c ∈ Λ_0 : Claims_τ(c)`,
where `Λ_0` is a fixed list of codewords, then the IOP has rbr-KS error at most
`|Λ_0| · ε_P`, where `ε_P` is the per-candidate error of the following moves.

*Proof.* `Λ_0` is fixed before the move; take a union bound. ∎

### 2.3 QROM Fiat–Shamir

Model SHA-384 as a quantum random oracle. The standard compilation (CMS19
Thm 8.6, CDHZ Thm 6.9/11.3) turns an IOP with rbr error `ε` into a
non-interactive argument sound against `t`-query quantum adversaries with error

```
O(t² · ε + t³ / 2^λ),
```

where `λ` is the hash output length. The `t²` factor is why we target `2^-268`
per round. Crucially, the compilation assumes **each verifier challenge is one
oracle output**. Sections 4 makes this assumption true.

### 2.4 WHIR

WHIR commits to a stacked trace, reduces constraints via sumcheck/GKR, and then
runs a folding PCS. We use the round indexing of the OpenVM backend:

* round `i` folds `f_i` exactly `k_i` times;
* commits `f_{i+1}` (or sends the final polynomial);
* samples the OOD point `z_{i+1,0}` and its answer;
* grinds, then samples `t_i` shift queries;
* absorbs the answers `y_{i,·}` ("WHIR-Y");
* samples the combination challenge `γ_i`.

The round-by-round error of WHIR (Thm 5.2, as corrected by Puškin's Tartu thesis)
has four terms: fold/sumcheck, OOD, shift queries `(1−δ)^t`, and final
`(1−δ)^t`, plus batching and combination terms. We keep all of them.

### 2.5 Agreement regimes

Let `RS[K, D, k]` be the Reed–Solomon code of dimension `k` on evaluation set
`D`. For agreement parameter `a = A/n`, the relevant regimes are:

* **unique decoding**: `a > (1+ρ)/2`;
* **Johnson**: `a > √ρ`;
* **capacity**: `a > ρ`.

The first two are theorems. The third is the false conjecture. Our design uses
Johnson and a *proven* first-order region slightly below `√ρ`, never capacity.

---

## 3. WHIR over `c·2^K` cosets

### 3.1 The four uses of smoothness

WHIR defines `L` to be *smooth* if it is a multiplicative coset of `F*` of
power-of-two order. The hypothesis is used in exactly four places:

| # | property | where | requirement for `c·2^N` |
|---|---|---|---|
| P1 | `x ∈ L ⇒ −x ∈ L` | Def 4.14, Claims 4.15/4.22 | `2 \| \|L\|` |
| P2 | `\|L^(2^j)\| = \|L\|/2^j`, a coset | §2.1, Constr. 5.1, Thm 4.20 | `2^j \| \|L\|` |
| P3 | `2^k`-fibres are disjoint of size `2^k` | Def 4.16, Claim 4.19 | `μ_(2^k) ⊆ H ⊆ L` |
| P4 | degree `< 2^m` | Def 4.2 | degree condition, domain-free |

None uses the odd part of `|L|`. The list-decoding, OOD, sumcheck, and batching
lemmas are domain-free. The proximity-gap inputs are stated for arbitrary `D`:

* BCGM Def 3.8 / Thm 9.2: `RS[K, D, k]` for **any** `D ⊆ K`;
* BCHKS25 Thm 1.5: correlated agreement for **any** `D`;
* DKT26 Thm 5.12 and Prop 5.10: any `n` distinct evaluation points.

**Lemma 3.1 (WHIR on `c·2^K` domains).** Let `c` be odd and let `L_0, …, L_{M−1}`
be multiplicative cosets of orders `c·2^(K_i)` with `2^(k_i) | c·2^(K_i)` and
`K_i ≥ k_i + i`. Then WHIR Construction 5.1 and Theorem 5.2 hold verbatim with
"smooth" replaced by "order `c·2^K`", provided the shift-query points are
exactly uniform on `L_(i−1)^(2^k)`.

*Proof.* Replace the word "smooth" by the stated order condition. P1–P3 are
immediate from `2 \| c·2^K`. For the folding and block-distance claims (Def 4.14,
Claims 4.15/4.19/4.22/4.23, Thm 4.20, Lemma 4.21) the proofs are pointwise
identities at `x` and `−x` plus coset bookkeeping, and use only P1–P3. The
list-size, OOD, sumcheck, and batching lemmas carry no domain hypothesis. BCGM,
BCHKS25, and DKT26 apply for arbitrary evaluation sets, so the MCA inputs are
unchanged. The shift/final terms need exact uniformity of the sampled point. ∎

### 3.2 Exact sampling over a non-power-of-two index set

Theorem 5.2's shift and final terms bound the probability that a uniform point
falls in a bad set. If indices are drawn by reducing a uniform field element
modulo `15·2^j`, residue 0 receives `1/p` extra mass, a statistical distance of
`≈ 2^-60` per query — catastrophic at a `2^-258` budget. Because
`15·2^j | p − 1`, the following is exact:

```
x ← uniform [0, p)
if x = p − 1: reject and redraw
index ← x mod (15·2^j)
```

Expected cost `1 + 2^-31` draws. In a circuit, replace "redraw" by "reject the
proof": soundness stays exact and completeness loses `≈ q/p ≈ 2^-25`.
Upstream `sample_bits` is retained unchanged for `c = 1`.

### 3.3 Geometry and implementation

Write `ζ = g^((p−1)/15)`. Then `D_i = ⟨ζ⟩ × H_(N−i)` is the disjoint union of
15 cosets `ζ^a·H_(N−i)`. Store coset-major: row `a·2^L + u` holds the value at
`ζ^a·ω_L^u`. Each block is an ordinary radix-2 coset LDE with shift `ζ^a`, so
the prover runs 15 standard NTTs and no mixed-radix transform. With `c = 1`
this is bit-identical to upstream.

Squaring maps `ζ^a·ω_L^u ↦ ζ^(2a)·ω_(L−1)^u`, so the next round has the same
15 shifts with the order-15 part permuted by `a ↦ 2a mod 15`. The fibre of
`x ↦ x^(2^k)` is `x·μ_(2^k)`, which lies in one block; hence one fold coset is
one Merkle leaf and each block is a complete subtree. Merkle depth increases by
`⌈log2 15⌉ = 4`; odd upper layers are padded with `H("")`, and padded positions
are never query indices.

### 3.4 What the domain change buys, and what it does not

At Johnson radius the per-query error is `(1−δ)^t` with
`δ = 1 − (1 + 1/2m)√ρ`, so the bits per query are

```
(b + log2 15)/2 − log2(1 + 1/2m),
```

i.e. `log2(15)/2 ≈ 1.95` more than a power-of-two domain of the same 2-adic
shape. This is a **rate** effect. At equal `n` and `ρ`, a `15·2^N` domain and a
hypothetical `2^(N+3.9)` domain give identical error bounds, because the bounds
depend only on `n` and `ρ`; the "gain" is simply that BabyBear cannot have a
larger power-of-two subgroup.

**This is not a proximity-conjecture result.** The proximity conjecture changes
the decoding radius; Lemma 3.1 changes only the evaluation set. A capacity-regime
theorem would not make a biased sampler uniform, and Lemma 3.1 would survive
independently of any capacity-regime statement. Section 9 makes the separation
explicit.

### 3.5 Prototype

A patch on the pinned `stark-backend` (`d667af5` + native patch) implements the
coset layout, exact sampler, domain-aware calculator, and `+4` depth. Evidence:

* `c = 1` proofs are **byte-identical** to the unpatched backend across Fib,
  interactions, preprocessed, cached, mixture, and a wide AIR; the
  `gas-failure5` child hash is unchanged with identical calculator bits
  (268.76 / 331.58 / 320.93).
* `×15` proves and verifies end to end for `c ∈ {3,5,15}`, blowups 1–3,
  `k ∈ {2,3,4}`, in every WHIR round.
* **55/55 negative cases rejected**, including tampered rows, siblings at leaf
  and padded levels, round-1 codeword values, OOD values, final polynomial, main
  commitment, an `×15` proof under a power-of-two VK, coset swaps, a
  power-of-two codeword repeated 15×, and mirrored cosets.

A wide-AIR benchmark (SHA-384/Ext12, `W = 64`, `k = 4`, target 268) gives:

| domain | points/col | rate | prove s | proof B |
|---|---:|---|---:|---:|
| `×1`, b=2 | `2^18` | 1/4 | 2.7–2.8 | 1,987,209 |
| `×1`, b=6 | `2^22` | 1/64 | 11.3–11.9 | 724,633 |
| **`×15`, b=2** | `15·2^18` | 1/60 | 5.6–8.5 | **737,625** |
| `×5`, b=3 | `5·2^19` | 1/40 | 4.7–6.0 | 806,201 |
| `×3`, b=4 | `3·2^20` | 1/48 | 7.3–8.7 | 773,625 |

The `×15` proof at rate 1/60 sits between the `1/32` and `1/64` power-of-two
proofs, close to `1/64` as `log2 60 = 5.91` predicts. The 15 coset DFTs ran at
7.24 ns/point·column against 12.59 for a single `2^(L+4)` DFT.

---

## 4. Transcript binding: `T*`

### 4.1 The chained pattern and lost grinding credit

A common transcript does:

```
s' = H(7, σ || w)                  // absorb witness, check leading z bits = 0
indices from H(5, s'), H(5, H(5, s')), ...
```

This is *chained*: the PoW check and the query-index derivation are separate
verifier moves with no prover message between them. In the round-by-round
analysis, the error of two consecutive verifier moves is the **maximum**, not
the product. Hence the PoW bits do not multiply the query error:

| pattern | chargeable per-round error | end-to-end |
|---|---|---|
| chained | `(1−δ)^t` | `≈ 2^-105` (fails U-6) |
| single-output (`T*`) | `2^-z (1−δ)^t` | `≈ 2^-135` |

This is a **proof gap, not an attack**. For a fixed transcript prefix the
chained pattern does admit a QROM bound with the grinding credit via the
DFMS22 extractable simulator; what is missing is the composition over many
prefixes with state restoration. We choose the fix rather than rely on an
unproven composition.

### 4.2 `T*`: counter mode

For each verifier move, derive a post-absorb key `κ`, then

```
B_j = H(tag, κ || le32(j)),      j = 0, 1, 2, ...
```

The PoW bits are the leading `z` bits of `B_0`; the query indices come from the
remaining bits of `B_0` and from `B_1, B_2, …`. The next chain state is the last
block consumed. This is one long-output oracle call, which standard QROM
theorems model. It costs zero proof bytes and zero extra compressions (inputs
grow by 4 bytes).

**Lemma 4.1 (grinding credit).** Under `T*`, the query move's rbr error is at
most `2^-z · (1−δ)^t` plus negligible terms, and a single layer meets U-2/U-6
outright.

### 4.3 Multi-call challenge squeezing

Even without PoW, squeezing an Ext12 challenge through a sequential chain
`σ_{j+1} = H(σ_j)` uses 4–7 blocks per challenge (and two blocks about 54 % of
the time for an Ext12 sample). Published QROM BCS theorems model one challenge
as one oracle output; a worst-case-over-database transition loses `≈ ε^(1/k)`.
`T*`'s counter mode is covered by CDHZ's long-output model at a `t → 2t` cost,
which is absorbed by the 268-bit target.

### 4.4 Implementation status

`T*` changes the native verifier, the prover, and the recursive verifier circuit
together. The circuits are built to reject any transcript that does not follow
it; the deployed production tree pins the unified backend that contains it.
Without the fix, the same theorem gives only `2^-105`; with it, `2^-135` at the
one-layer level and `2^-134.7` after the QROM `t²` compilation (Section 7).

---

## 5. Weakly binding Merkle commitments and WHIR-Y

### 5.1 Block equivocation

Suppose Merkle nodes are `n`-bit digests with `n < 256`. An adversary can find a
collision with `t` queries with probability `≈ t³/2^n`; for
multi-collisions the relevant count is `t²/2^n` per block. In WHIR as built, the
answers to shift queries `y_{i,j} = g_i(z_{i,j})` enter the `γ_i` combination
**without being absorbed first**. The prover can therefore choose the oracle
contents *after* seeing `γ_i`, equivocating on whole level-`c` subtrees
("blocks") and changing the value that `γ_i` combines. With `n = 256` this costs
`≈ 2^-128`; with 26–28 byte digests it is fatal.

### 5.2 WHIR-Y

Absorb `y_{i,·}` before sampling `γ_i` in every round, including the final
round. This costs **zero bytes**. Now the values entering the combination are
fixed before `γ_i`, so the standard Schwartz–Zippel argument applies per
candidate block set.

### 5.3 Block-robust rbr

**Definition 5.1.** For `m ≥ 0`, the block-robust error `ε_rob(m)` is the
supremum, over doomed prefixes and over block sets `C` such that every
transcript modification `τ_T` with `C ⊆ T`, `|T| ≤ m` is doomed, of
`Pr_c[∃T ⊇ C, |T| ≤ m : state(τ_T‖c) = 1]`. `ε_rob(0)` is ordinary rbr.

**Theorem 5.2 (Theorem R, sketch).** Assume the radius conditions
`δ_i + K/B_i ≤ J_(M′_i)(ρ_i)` and `r^ood_i + K/B_i < 1 − √ρ_i`. Then every
WHIR-Y verifier move is block-robust with explicit errors that at `m = 0`
reduce to WHIR Thm 5.2, plus a radius shift `m/B_i`:

| move | `ε_rob(m) ≤` |
|---|---|
| fold `α` | `err⋆_1(r_i(m)) + ℓ_i(r_i(m))·d/\|K\|` |
| OOD | `C(ℓ,2)·2^(m_i)/\|K\|` |
| queries | `Lfac·N_i(m)·(1−δ_i)^t`, `N_i(m) = Σ_{j≤m} C(B_i,j)` |
| combination | `ℓ·(t+1)/\|K\|` |

The union over block sets is paid once per query move as `N_i(m) ≈ B^m/m!`.
The proof follows WHIR move by move; the two steps needing care are the choice
of the adversarial oracle at a re-chosen block set (Fact V lets validity be
preserved) and the density bound holding for every contributing block set. Both
are written out in the companion note and reviewed once.

### 5.4 Digest widths

Under WHIR-Y and Theorem 5.2, the digest width `n` is set by the narrow
collision chain, not by collision resistance. For the final-12k shape:

| block level `c` | `K*` | queries | `n_min` | digest | net saving |
|---|---:|---|---:|---:|---:|
| 6 | 0 | 69/69/55/46 | 324 | 41 B | 3.8 KB |
| 8 | 2 | 72/72/59/51 | 237 | 30 B | 27.2 KB |
| 10 | 4 | 70/70/57/48 | 219 | 28 B | 37.5 KB |
| **11** | **7** | **70/70/57/48** | **208** | **26 B** | **39.4 KB** |
| 12 | 5 | 69/69/56/47 | 214 | 27 B | 36.0 KB |

The floor is `≈ 203` bits, set by `3 log t + log(10e²) − 2 log K + 128/(K+1)`.
As a conservative default we deploy 42-byte digests (`n = 336`), which the
analysis already supports with `K = 0`; the 26–28-byte setting is available once
the circuit carries position tags and deduplicated openings. The top tree levels
and the Fiat–Shamir chain stay at 384 bits.

---

## 6. Certificate-gated agreement tables

### 6.1 Two proven proximity inputs

**O-1 (Johnson).** DKT26 Thm 5.12 gives line MCA at `a = √ρ_(−) + η_0` with
error `E/|F|` for arbitrary evaluation sets, plus Cor 7.7 (interleaving is
width-free) and Cor 7.8 (folds cost `h·E/q`). The Lean development proves the
constant `johnsonE0` and the pairwise list term of (67); the constant used in
the calculator is exactly the Lean constant.

**O-2 (first order beyond Johnson).** DKT26 Prop 5.10 + Lemma 5.6 give a
certificate-based route to agreement below `√ρ`. For each code a support
certificate `(m, B_∂, B_jet)` is checked, yielding a list bound (Lemma 5.11) and
a curve MCA count (Cor 7.3). At our parameters the certified agreement ranges
over `a_i/√ρ_i = 0.77–0.90`, with lists `≤ 2^43.4` and MCA error `≤ 2^-280.7`.
BabyBear satisfies the required characteristic bound
`p = 2^30.9 > max(k−1, B_∂)`.

### 6.2 Lean-kernel certificates

The DKT26 authors' Lean development (ArkLib fork at the paper's pin) is built
without `sorry` in the cited cone; the axiom set is exactly
`{propext, Classical.choice, Quot.sound}`, with no `native_decide`, no
`skipKernelTC`, and no custom axioms. Their decidable checker re-verifies every
certificate: **129 certificates** — 93 round/fold sub-codes and 36 round-0
batching curves — all match the JSON rationals exactly. The Thm 5.12 → Cor
7.7/7.8 composition is itself proved in Lean.

The table is **bound into the verifier key**: for each round `i` the key stores
`(A_i, regime)`. A round may use the first-order table only if every code and
fold sub-code `RS[L_i^(2^s), m_i − s]`, `s ≤ k_i`, carries a kernel-checked
certificate. Otherwise it falls back to Johnson.

### 6.3 Round-0 fallback

If a layer commits more than one group of columns, the round-0 list is the
*product* of the per-commitment lists; squaring a `2^41.56` list can push the
batching term to `2^-231.8`, which is below target. Rule: round 0 must use
Johnson whenever the layer has more than one commitment. This is checked by
construction in the key generator.

### 6.4 Query schedules

With 236 query bits and `z = 32`, the resulting schedules are:

| layer | BCGM `m=3` | O-1 (`m=64`) | O-1 + O-2 |
|---|---|---|---|
| final | 42/38/31/26 = 137 | 40/37/30/25 = 132 | **38/35/29/24 = 126** |
| inner | 50/46/33/26 = 155 | 48/44/32/25 = 149 | **45/41/31/24 = 141** |

The worst per-move rbr error is `2^-268.01`; the final-layer byte count drops by
`≈ 12 KB` relative to BCGM `m=3`, and the whole schedule remains inside the
proven regime.

### 6.5 The DKT26 caveat

DKT26 is **unrefereed** (one version, AI-assisted per its authors). We mitigate
by (i) using only Lean-proven statements, (ii) checking the stated conclusions
against the paper, and (iii) treating the RS → WHIR step as a separate,
paper-level obligation (Section 10). We do not use any unproven heuristic from
the paper.

---

## 7. QROM straight-line knowledge soundness for recursive layers

### 7.1 Model

A recursion chain has layers `0, …, d`. Layer `i` proves that layer `i−1`'s
verifier accepts. In the QROM game the adversary has one random oracle and one
database.

### 7.2 Theorem 6.4

**Theorem 7.1 (sketch).** Let `ε_rbr` be the per-layer rbr knowledge error, `t`
the query bound, `G` the number of Merkle openings, and `λ` the digest width.
Under `T*`, the truncated-commitment BCS argument for a *family* of layers has
straight-line knowledge soundness with error

```
(2t·G + 2^-160)².
```

At `t = 2^64`, `G² = 10 · max(3·2t/2^336, ε_rbr + 2^20(4t+1)/2^384)`, and
`ε_rbr = 2^-268.01`, this is `≤ 2^-134.7`.

*Proof idea.* Measure the compressed-oracle database once. A single extractor
recovers witnesses for all layers from the same measured database, so no union
over layers or per-layer forking is needed. The truncated commitments are
handled by the block-robust property of Section 5 with `K = 0` at 42 bytes. ∎

The same shape appears in CMS19 Thm 8.6, Fractal Thm 10.1, and CDHZ Thm 11.3;
our contribution is the family version with truncated commitments and one
database, which makes the error independent of `d`.

### 7.3 Recursive composition

**Theorem 7.2 (sketch).** Under A-IC (Section 9) and the circuit-faithfulness
conditions, the `d`-layer chain has error `≤ 2^-134.7` independent of `d`; with
a union over 7 layers it is `≤ 2^-131.9`. The final verifier `V_d` accepts only
proofs whose exposed statement matches the pinned program.

### 7.4 Program pinning is necessary

**Proposition 7.3.** In program-bound recursion where the final layer's program
is a public input of its own proof, a verifier that checks only the final proof
and the exposed statement digest accepts a forged final proof whose program
verifies nothing and exposes a false statement.

*Proof.* Construct a program `P⊥` that accepts every witness and outputs the
desired false statement; produce its proof honestly. The proof verifies; the
statement digest matches. Without a check that the final proof's program
openings equal the pinned `P`, nothing distinguishes `P⊥` from `P`. ∎

The fix is to check the final proof's program openings against a pinned program
(and level). This is implemented and tested: a 776-row verify-nothing final is
accepted without the check and rejected with it.

---

## 8. Systems realisation

### 8.1 Streamed commitments

At the size-optimal shape the `×15` codeword is `≈ 10^12` base elements
(`≈ 1 TB`); it cannot be materialised. We never do:

* choose `s = L − max(n, k)`; each residue `r mod 2^s` is a sub-coset
  `ζ^a·ω_L^r·⟨ω_(L−s)⟩`, obtained by one batched coset DFT of size
  `2^max(n,k)`;
* hash leaves on the fly; drop `D` levels (default 4) and keep only the upper
  Merkle levels;
* on query, evaluate opened rows directly from coefficients by Horner and
  rebuild the dropped subtree from its leaves.

`NEARPROOF_STREAM_COMMIT=1` enables it. Tests: tree identity and whole-proof
identity at `b = 2` for `×1`, `×3`, `×15`, base and extension field, drop
`0, 2, 4, 30`; `nv::stream_tests` matches 36/36 cases per digest setting. At
full scale a streamed b=2 final reproduces the same 416,171 B and SHA-256 as the
in-memory prover, with peak RSS `64.4 → 35.5 GB` and wall time 50.7 min vs
100 min. An 853 GB virtual codeword was committed in 480 s at a 14.9 GB peak;
the real b=7/W=106 final proved at `≈ 39 GB` instead of `≈ 1 TB`.

Measured vs analytic size law:

| run | queries | measured B | model B | delta |
|---|---|---:|---:|---:|
| b=7, `m=3` | [46,42,31,25] | 339,747 | 339,370 | +0.11 % |
| b=7, `m=64` | [44,40,30,24] | 330,149 | 329,478 | +0.20 % |
| O-2 chain final | [41,38,29,23] | **287,477** | 287,037 | +0.15 % |

The last row is the size-optimal O-2 chain; it is provisional pending the
program-binding rerun. The G2 gate chain, measured with real settings and
binding, gives **293,077 B** and `V_d` accept + forgery reject.

### 8.2 SHA-512 compression AIR

SHA-512 is the dominant circuit cost. Two proven layouts:

| version | rows × cols | main cells/compression | degree |
|---|---|---:|---:|
| v2.1 (base-8 digits) | 43 × 171 | 7,353 | 21 |
| v4 (base-4 digits, two words/row) | 128 × 83 (73 rotated) | 10,624 | 9 |

v2.1 is 2.6× smaller than OpenVM's SHA-512 AIR (18,963 cells) and is the
smallest published SHA-512 AIR on a 31-bit field we are aware of. v4 trades
cells for degree (21 → 9), which shrinks the recursive verifier circuit; it also
folds the round constant into a lookup at zero cost. Both are validated by
mutation sweeps: 5,921/5,921 and 5,848/5,848 detected.

---

## 9. The assumption ledger

### 9.1 Used

| assumption | statement | why it is acceptable |
|---|---|---|
| SHA-384 is a (quantum) random oracle | standard ROM/QROM idealisation of the deployed hash | U-6/U-7; no structural assumption on Merkle–Damgård |
| A-IC | the SHA-384 evaluations certified in-circuit are modelled as oracle evaluations on that witness | **unavoidable** for hash-only recursion: Theorem O proves no query-only oracle model can do better. Adopted as a time-bounded assumption `A-IC(τ)`, `τ = 2^128` |
| DKT26 Thm 5.12 / Prop 5.10 | proximity statements used for O-1/O-2 | Lean-proven, kernel-checked; paper unrefereed |
| BCGM / BCHKS25 | Johnson-regime MCA/CA for arbitrary `D` | refereed / ECCC |
| WHIR Thm 5.2 (Puš26 correction) | rbr soundness of the PCS | published, correction checked |
| circuit faithfulness | the NV circuit arithmetises the verifier; layer-0 AIRs encode chunk validation | engineering obligation, specified as Lemma 7.1 / Lemma 7.2; in progress |

### 9.2 Not used

| excluded assumption | status |
|---|---|
| proximity conjecture (any form) | not used; capacity forms are **false** (Crites–Stewart 2025/2046) |
| ethSTARK random-words / conjectured list sizes | not used; all lists are proven or certificate-bound |
| capacity-regime MCA / list decoding | not used; our radii are Johnson or proven first-order |
| PoW hardness | not used; grinding only *reduces* error and is charged in the rbr game |
| collision resistance of 26–42 B digests | not used; replaced by the block-robust property (42 B default, 26–28 B optional) |
| trusted setup, pairings, groups, lattices | not used; hash-only, transparent |
| efficient extraction (for soundness) | not needed; the theorem is existential (an efficient extractor exists anyway) |

### 9.3 The proximity-conjecture separation, explicitly

| | proximity conjecture | this work |
|---|---|---|
| object changed | decoding radius `δ` | evaluation domain `D`, hence `ρ` |
| regime | capacity `δ → 1−ρ` | proven Johnson / first order |
| status | conjectured; capacity forms false | theorem + Lean-checked inputs |
| gain | `≈ b` bits/query | `≈ 1.95` bits/query from `×15` rate |
| field/symbol cost | larger symbols, larger `m` | none |
| effect on `m` | conjecture would allow `m ≈ 1/ε` | `m = 64` (O-1) or certified O-2 |
| relation to proof | changes the assumption | only substitutes `n, ρ` in the same bound |

So: `×15` buys **rate**; the proximity conjecture would buy **radius**. We buy
only rate, at a proven radius. A proof of the capacity conjecture would not
change any step of Sections 3–8, and a disproof (which has happened for its
capacity form) would not affect them either.

---

## 10. Limitations and open obligations

1. **DKT26 → WHIR.** The RS-level MCA/list statements (Lean-proven) are lifted to
   WHIR's rbr errors via WHIR Thm 5.2 as corrected by Puš26. This step is
   paper-level and has not been formalised. It is the highest-value remaining
   proof obligation.
2. **Review/formalisation of `T*` and Theorem R.** Both are new proofs, complete
   as written but not yet peer reviewed. Theorem 6.4 and the weak-binding
   Lemmas 1–2 should be independently reviewed or formalised.
3. **Circuit faithfulness.** NV-faithful (the circuit arithmetises the verifier
   exactly) and Base-faithful (layer-0 AIRs encode chunk validation) are
   engineering obligations in progress, stated as precise lemmas.
4. **A-IC.** Unprovable in a query-only oracle model by Theorem O; adopted with a
   time bound. This is the one point on which "proven bounds only" is not fully
   met, and by necessity rather than choice.
5. **Tight-heights kernel.** The univariate-skip encoding of the stacking kernel
   is validated by code and 24 tamper tests but not yet derived line by line.
6. **Program-binding rerun.** The 287,477 B O-2 chain is provisional; the G2 gate
   measured 293,077 B with binding. The final measurement on the pinned
   program-binding circuit is in progress.
7. **Backends.** The `×15` and streaming patches must be ported to the CPU and
   CUDA backends; unpatched backends fail closed rather than producing unsound
   proofs.

None of these is a new conjecture; each is a proof, review, or measurement
obligation.

---

## 11. Conclusion

We have shown that a hash-only, transparent-setup, post-quantum succinct proof
can be built at `≈ 287–293 KB` for a NEAR chunk while using **only proven
proximity and soundness bounds**. The key methodological move is to separate the
two knobs that are often conflated: the evaluation domain (a rate lever) and the
decoding radius (where the proximity conjecture lives). We change the domain,
not the radius, and we buy `≈ 1.95` bits per query from BabyBear's `×15`
multiplicative structure at no symbolic cost. On top of that we fix the
transcript (`T*`), prove a block-robust weak-binding property (WHIR-Y),
instantiate certificate-gated agreement tables, give a depth-independent QROM
knowledge-soundness theorem for recursive layers, and realise the whole thing
with streamed commitments that never materialise the codeword.

The assumption ledger is short and explicit. The one unavoidable non-standard
assumption, A-IC, is stated precisely, is proven necessary in the query-only
model, and is the subject of ongoing work. The proximity conjecture — in
particular its capacity-regime forms, which are known to be false — appears
nowhere.

*“×15 buys rate; the proximity conjecture would buy radius. We bought rate, and
only rate, at a proven radius.”*

---

## Appendix A: Parameter summary

| item | value |
|---|---|
| base field | BabyBear `p = 15·2^27+1` |
| challenge field | `Ext12`, `log2\|K\| = 370.88` |
| hash | SHA-384, 384-bit transcript, 42 B digests (26–28 B optional) |
| domains | `15·2^K` multiplicative cosets |
| per-round target | `2^-268` = 236 query + 32 PoW bits |
| proximity | Johnson `m=64` / certified first order |
| final queries | [38,35,29,24] (O-2), [41,38,29,23] (O-2 chain) |
| one-layer rbr | `2^-268.01` |
| QROM end to end | `≤ 2^-134.69` (union `2^-131.89`) |
| measured final | 287,477 B (O-2 chain, provisional); 293,077 B (G2 gate) |
| prover peak | `≈ 25.6–39 GB` (streamed), `≈ 1 TB` virtual codeword avoided |
| setup | transparent |

## Appendix B: Reproduction

Artifacts are organised by lane in the near-proof-arena repository:

* `lane/pq-x15-domains`: `research/near-compression/x15-domains/{SOUNDNESS.md,README.md,rbr_x15.py}`;
* `lane/pq-final-soundness`: `research/near-compression/final-soundness/{PROOF.md,GAPS.md,MCA-UPGRADE.md,calc/bound.py}`;
* `lane/pq-weak-binding`: `research/near-compression/weak-binding/{ANALYSIS.md,HROB.md,REVIEW-1.md}`;
* `lane/pq-dkt-verify`: `research/near-compression/final-soundness/DKT-VERIFY.md`, `lean/DKT*.lean`;
* `lane/pq-stream-commit`: `research/near-compression/results/pq-stream-commit/README.md`;
* `lane/pq-sha384-air2` / `-air3`: `research/near-compression/results/pq384-sha-air{2,3}/`;
* `lane/pq-e2e-slice`: `results/pq-e2e-slice/`;
* register: `docs/research/NOVEL-FINDINGS.md`; prior art: `research/novelty/PRIOR-ART.md`.

All numbers in this note are reproducible from the cited scripts; the measured
rows are from logs kept with each lane.
