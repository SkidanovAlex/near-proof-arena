# QROM game: ANALYSIS Lemmas 1 and 2, formalized with Mathlib

Status: 2026-10-20. Research package, **not** part of the gated `zk-formal` build.

## Why this package exists

`zk-formal` is bound by the challenge's `allowed_packages = [ArenaCore, NearSpec]`
(`docs/zk-formal/DESIGN.md` F4: **no Mathlib**). Every proof that must enter a certificate has to
be Mathlib-free. This package is separate so the QROM arguments can be developed with Mathlib
available; anything here that must enter a certificate still has to be re-proved in `zk-formal`.

`research/` is outside `make pin-check` (which covers `oracle/v3` only) and outside CI.

## What was proved

| file | content | ANALYSIS reference |
|---|---|---|
| `Qrom/Transition.lean` | `block_le_a`, `block_le_b`, `block_le_c` — the three cases of the one-query transition bound `‖A·cO·B‖²` | §3 **Lemma 1** |
| `Qrom/Path.lean` | `Ahat_step` (the recursion holds with equality, by Pascal's rule) and `path_bound` (the induction `a ≤ Â`, giving `‖Π_{κ≥K+1}ψ_t‖ ≤ A_t`) | §3 **Lemma 2** |
| `Qrom/Main.lean` | **`qrom_bound`** — the whole chain assembled: Lemma 1 bounds ⇒ operator norm ⇒ mass recurrence ⇒ Lemma 2 ⇒ Fact A | Thm 6.4 conclusion shape |
| `Qrom/FactA.lean` | `hits_le` / `fibre_card` (the finite counting step: hitting any of `ℓ` coordinates has `≤ ℓ·N^(t−1)`-many oracles) and `fact_a` (the square-root form, with the Zhandry/CFHL21 replacement as an explicit hypothesis) | §3 **Fact A** |
| `Qrom/Operator.lean` | `matL` (a matrix as a linear map), `restr`/`restr_idem` (level projection), `block_sq_le` and **`block_norm_le`** (entrywise bound ⇒ block operator norm) | §3 "the max over the block norms" |
| `Qrom/Instantiate.lean` | Hilbert-space model: `proj`/`projL`, `norm_proj_sq`/`norm_proj_le`/`norm_proj_mono`, `proj_idem`, `mass`, `mass_antitone`, **`mass_recurrence`** (block operator norms ⇒ the per-level recurrence), `instantiate` (Lemma 2 for a real state) | §3 "for diagonal Π, ‖Π_{≥j} cO Π_{=i}‖ is the max of the block norms", Lemma 2, step 6 |

Axioms: `propext`, `Classical.choice`, `Quot.sound` only. No `sorry`.

### Lemma 1 (one-query transition bound)

The compressed oracle's one-point unitary `cO_{xŷ}` is modelled by its squared entry bounds
(ANALYSIS Fact B, from CFHL21 Lemma 4.3): alphabet `Y = Fin M`, register `Ȳ = Option (Fin M)`
with `none = ⊥`, and

* `⊥ → ⊥` is `0`,
* `|γ_{⊥,r}|² = |γ_{u,⊥}|² = 1/M`,
* `|γ_{u,r}|² ≤ 9/M²`.

The operator norm is bounded by the Frobenius norm over the block (ANALYSIS step 1). The three
cases are proved directly on the double sum:

* **(a)** `⊥ ∉ A`: `blockSum ≤ |A|·(1/M + 9/M)`.
* **(b)** `⊥ ∈ A`, `⊥ ∉ B`: `blockSum ≤ 10·|B|/M`.
* **(c)** both avoid `⊥`: `blockSum ≤ 9·|A|·|B|/M²`.

### Lemma 2 (path lemma)

Stated and proved on `ℝ`-valued sequences, which is faithful: the compressed-oracle argument
supplies the recursion from Lemma 1 and the commutation of the adversary's unitaries with the
diagonal projectors, and nothing else about quantum mechanics enters.

* `Ahat_step`: `Â_{s+1}(j) = Â_s(j) + Σ_{i<j} G_{i,j}·Â_s(i)` — the recursion with **equality**,
  via Pascal's rule `C(s+1,m+1) = C(s,m) + C(s,m+1)`.
* `path_bound`: from `a_0 ≤ Â_0` and the recursion for `a`, induction on `s` gives `a_t ≤ Â_t`.

### Fact A (real oracle → measured database)

The counting content is proved: `fibre_card` (fixing one of `t` coordinates leaves `N^(t-1)`
free) and `hits_le` (union bound: at most `ℓ·N^(t-1)` oracles hit any of `ℓ` coordinates).
The Zhandry/CFHL21 *replacement* inequality is the genuinely quantum step and is kept as an
explicit hypothesis `Replace` in `fact_a`; only the square-root algebra around it is proved.

### Instantiation (Hilbert space)

The state lives in `EuclideanSpace ℝ ι`; `proj P` zeroes coordinates outside the level predicate
`P`. Proved: `norm_proj_sq` (`‖proj P x‖² = Σ_{i∈P} x_i²`), `norm_proj_le` (contraction),
`norm_proj_mono` (nested levels), `proj_idem` (it is a projector).

**`mass_recurrence`** is the step ANALYSIS states in one sentence ("for diagonal `Π`,
`‖Π_{≥j} cO Π_{=i} P_{≤s}‖` is the maximum over the block norms of Lemma 1"):

  `‖Π_j (cO ψ)‖ ≤ ‖Π_j ψ‖ + Σ_{i<j} g_i · ‖Π_i ψ‖`, given `‖Π_j ∘ cO ∘ Π_{=i}‖ ≤ g_i`.

**A hypothesis the prose omits.** The derivation is *false* without idempotence of `Π_{=i}`: the
block bound controls `cO` applied to `Π_{=i}ψ`, not to `ψ`, so the chain needs
`(Π_j cO Π_{=i})(Π_{=i}ψ) = (Π_j cO Π_{=i})ψ`. `mass_recurrence` therefore takes
`P i ∘L P i = P i` explicitly, and `proj_idem` discharges it for the concrete model.

`instantiate` then applies Lemma 2 to `mass lev ∘ ψ`, with nonnegativity supplied by
`mass_nonneg` rather than assumed.

## Status: the chain is closed except two cited modelling facts

The full chain is now proved and assembled in `Qrom/Main.lean:qrom_bound`:

```
Lemma 1 entrywise bounds   (block_le_a/b/c)          proved
  ⇒ block operator norm    (block_norm_le)           proved
  ⇒ per-level recurrence   (mass_recurrence)         proved (needs projector idempotence)
  ⇒ chain-sum bound        (path_bound)              proved
  ⇒ Fact A square roots    (fact_a)                  counting + algebra proved
  ⇒ qrom_bound                                        proved
```

**Two inputs remain cited, not derived.** They are named explicitly at the top of `Qrom/Main.lean`
and are not hidden behind vague hypotheses:

1. **`OracleModel`** (ANALYSIS Fact B / CFHL21 Lemma 4.3): that the compressed oracle's
   one-point transition has the matrix entries whose squared bounds `block_le_*` analyse. The
   *consequent* bounds are proved; that the entries are the right ones is the modelling step.
2. **`Replace`** (CFHL21 Cor 4.2): the real-oracle-to-measured-database inequality
   `√p ≤ √p' + √(ℓ/N)`. Its counting half (`hits_le`, `fibre_card`) and its square-root algebra
   (`sqrt_add_le`, `fact_a`) are proved; the inequality itself needs the compressed-oracle
   purification, which is not formalized here.

So this is **not** yet a proof of `PROOF.md` Theorem 6.4: the two cited facts are exactly the
places where the paper cites Zhandry and CFHL21. What the package does prove is that those two
citations are the *only* remaining gaps — every other step of Lemmas 1 and 2, the operator
assembly, and the final composition are machine-checked. The paper must keep saying the QROM
composition rests on CFHL21 Cor 4.2 and Fact B.

### Finding worth recording

The step ANALYSIS states in one sentence ("for diagonal `Π`, `‖Π_{≥j} cO Π_{=i} P_{≤s}‖` is the
maximum over the block norms of Lemma 1") is **false without idempotence** of the level operators:
the block bound controls `cO` applied to `Π_{=i}ψ`, not `ψ`. `mass_recurrence` therefore takes
`P i ∘L P i = P i` explicitly, and `proj_idem`/`restr_idem` discharge it.

## Build

```sh
cd research/qrom
lake build          # uses the Mathlib checkout at /data/illia/nearproof-deps/arklib-dkt/ArkLib
```

The `lakefile.toml` points `mathlib` at that checkout to avoid a second 7 GB copy. If it moves,
update the `path` there.
