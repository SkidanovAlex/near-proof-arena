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

## What is *not* proved (and why it matters for the paper)

1. **Fact A** (Zhandry / CFHL21 Cor 4.2): `√p ≤ √p' + √(ℓ/N)`, the real-oracle-to-measured-database
   step. This is the remaining probabilistic bridge. It is a standard result but not formalized
   here.
2. **The quantum-mechanical instantiation**: that the compressed-oracle state `ψ_s` and the
   diagonal projectors `Π_{κ≥j}` actually satisfy `path_bound`'s hypotheses. `path_bound` is
   stated for an abstract `a`; connecting it to a Hilbert-space state is not done.
3. **Theorem 4 / Theorem 6.4** end to end, and the weak-binding Theorem R.

So this file proves the two *quantitative* lemmas the QROM game rests on, at the level a reviewer
can check, but not the game itself. The paper must keep saying the QROM composition is
hand-proved.

## Build

```sh
cd research/qrom
lake build          # uses the Mathlib checkout at /data/illia/nearproof-deps/arklib-dkt/ArkLib
```

The `lakefile.toml` points `mathlib` at that checkout to avoid a second 7 GB copy. If it moves,
update the `path` there.
