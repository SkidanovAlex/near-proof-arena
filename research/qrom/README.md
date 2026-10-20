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
| `Qrom/FactA.lean` | `hits_le` / `fibre_card` (the finite counting step: hitting any of `ℓ` coordinates has `≤ ℓ·N^(t−1)`-many oracles) and `fact_a` (the square-root form, with the Zhandry/CFHL21 replacement as an explicit hypothesis) | §3 **Fact A** |
| `Qrom/Instantiate.lean` | `path_bound_state` (Lemma 2 for the `a` supplied by a real step structure) and `accumulation_bound` (`a 1 j ≤ 1 + j·G₀`, the `t·G` accumulation) | §3 Lemma 2 instantiation, step 6 |

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

### Instantiation

`Step` bundles the three structural facts the compressed-oracle argument supplies (nonnegativity,
the per-level transition bound, the initial condition) and `path_bound_state` applies Lemma 2 to
it. The bundled fields are the interface a Hilbert-space development must discharge; the file
does **not** construct them from projectors and unitaries.

## What is *not* proved (and why it matters for the paper)

1. **The Zhandry/CFHL21 replacement inequality itself** (`Replace` in `fact_a`). The counting and
   the square-root algebra are proved; the statement that the real oracle and the measured
   compressed database differ by `ℓ/N` in squared distance is cited, not derived.
2. **Constructing a `Step` from projectors and unitaries.** `path_bound_state` takes the three
   structural facts as a structure; building them for `ψ_s` and `Π_j` is not done.
3. **Theorem 4 / Theorem 6.4** end to end, and the weak-binding Theorem R.

So this package proves the two *quantitative* lemmas (Lemma 1, Lemma 2), the counting half of
Fact A, and the composition of Lemma 2 with a `Step` interface. It does not prove the QROM game
end to end, and the paper must keep saying the composition is hand-proved.

## Build

```sh
cd research/qrom
lake build          # uses the Mathlib checkout at /data/illia/nearproof-deps/arklib-dkt/ArkLib
```

The `lakefile.toml` points `mathlib` at that checkout to avoid a second 7 GB copy. If it moves,
update the `path` there.
