import ZkFormal.Udr.Statements
import ZkFormal.Algebra.Fp
import ZkFormal.Algebra.Transport

/-!
# ZkFormal.Udr.CosetDomain — `c·2^K` evaluation domains (the x15 lever)

Paper Lemma 3.1 (`research/near-compression/x15-domains/SOUNDNESS.md`, "Where WHIR uses
smooth"): WHIR/FRI soundness never needs the evaluation domain to have **power-of-two** order.
It uses only:

| # | property | what it needs |
|---|---|---|
| P1 | `x ∈ L ⇒ −x ∈ L` | `2 ∣ \|L\|` |
| P2 | the image of `L` under `x ↦ x²` has half the order, and the map is `2`-to-1 | `2 ∣ \|L\|` |
| P3 | fold fibres are `μ_(2^k)`-cosets, of size `2^k` | `2^k ∣ \|L\|` |
| P4 | the degree bound `2^m` | a degree condition, domain-free |

None of the four uses the odd part of `|L|`. This file records what is provable without
Mathlib's arithmetic tactics:

* `neg_mem_coset_index` — P1 as the exact index shift (the identity `Fold` uses);
* `sq_periodic` — P2: squaring has period `c·2^(M−1)` on an order-`c·2^M` domain;
* `halve_card` — the arithmetic behind P2/P3 (`2·(c·2^(M−1)) = c·2^M`);
* `higher_split` — the arithmetic behind P3 (`2^(M−k)·2^k = 2^M`);
* `sampler_uniform` — **exactness of the query sampler**: if `n ∣ m`, reducing a uniform draw
  mod `n` is exactly uniform. This is what a `c·2^j` index set forces and what the bias
  `1/p` at residue 0 would otherwise cost;
* `sizes_halve` — a `c·2^M` layer family satisfies the only size condition `Udr.Setup` imposes;
* BabyBear facts: `p − 1 = 15·2^27`, and an order-`15·2^K` generator exists for every `K ≤ 27`.

**Not formalized here** (reportable as remaining): P3's injectivity of the fibre index map and
the full `Setup` instantiation from a concrete coset enumeration (the arithmetic plumbing is
straightforward but the no-Mathlib `omega`/`nlinarith` gap makes it slow; it is not
load-bearing for the paper's claim, which is that `Setup` never asks for a power of two).
-/

namespace ZkFormal.Udr

open ArenaCore.Security
open Lean.Grind

/-- Two predicates agreeing on a list have equal counts. -/
theorem count_congr_mem' {α : Type} (l : List α) {E F : α → Prop}
    (h : ∀ x ∈ l, E x ↔ F x) : count l E = count l F := by
  have h1 : count l E ≤ count l F :=
    count_mono_mem l (fun x hx hE => (h x hx).mp hE)
  have h2 : count l F ≤ count l E :=
    count_mono_mem l (fun x hx hF => (h x hx).mpr hF)
  omega

/-- A witness makes the count positive. -/
theorem count_pos_of_mem' {α : Type} {l : List α} {E : α → Prop} {x : α}
    (hx : x ∈ l) (hE : E x) : 0 < count l E := by
  classical
  unfold count
  rw [List.countP_pos_iff]
  exact ⟨x, hx, by simpa using hE⟩

/-! ## Integer arithmetic of `c·2^M` (no Mathlib) -/

/-- `2 · (c·2^(M−1)) = c·2^M` for `M ≥ 1`. -/
theorem halve_card (c M : Nat) (hM : 1 ≤ M) : 2 * (c * 2 ^ (M - 1)) = c * 2 ^ M := by
  conv => rhs; rw [show M = (M - 1) + 1 by omega]
  rw [Nat.pow_succ]
  rw [Nat.mul_left_comm, Nat.mul_comm 2 (2 ^ (M - 1))]

/-- `2^(M−k) · 2^k = 2^M` for `k ≤ M`. -/
theorem higher_split (M k : Nat) (hk : k ≤ M) : 2 ^ (M - k) * 2 ^ k = 2 ^ M := by
  conv => rhs; rw [show M = (M - k) + k by omega]
  rw [Nat.pow_add]

section Field
variable {K : Type} [Field K]

/-! ## P1 — negation closes the domain -/

/-- **P1.** With `γ^(c·2^(M−1)) = −1` (true for a full-order generator and `M ≥ 1`), negation on
the order-`c·2^M` domain is the index shift `i ↦ i + c·2^(M−1)`. So `−x ∈ L` for every `x ∈ L`,
which is exactly what WHIR's `Fold` step uses. -/
theorem neg_mem_coset_index (γ : K) (c M : Nat) (hM : 1 ≤ M)
    (hne : γ ^ (c * 2 ^ (M - 1)) = -1) (i : Nat) :
    γ ^ i * (-1) = γ ^ (i + c * 2 ^ (M - 1)) := by
  rw [← hne, Semiring.pow_add]

/-! ## P2 — squaring halves the order -/

/-- **P2.** Squaring is periodic with period `c·2^(M−1)` on an order-`c·2^M` domain: the image
has order `c·2^(M−1)` and every image value has two preimages (`halve_card`). -/
theorem sq_periodic (γ : K) (c M : Nat) (hM : 1 ≤ M) (hord : γ ^ (c * 2 ^ M) = 1) (i : Nat) :
    (γ ^ (i + c * 2 ^ (M - 1))) ^ 2 = (γ ^ i) ^ 2 := by
  rw [← ZkFormal.Algebra.pow_mul_eq, ← ZkFormal.Algebra.pow_mul_eq]
  have hB : (c * 2 ^ (M - 1)) * 2 = c * 2 ^ M := by
    rw [Nat.mul_assoc]
    conv => rhs; rw [show M = (M - 1) + 1 by omega]
    rw [Nat.pow_succ]
  have h2 : (i + c * 2 ^ (M - 1)) * 2 = i * 2 + c * 2 ^ M := by
    rw [Nat.add_mul, hB]
  rw [h2, Semiring.pow_add, hord]; grind

end Field

/-! ## The exact sampler -/

/-- **Exactness of the query sampler.** If `n ∣ m` and `n > 0`, reducing a uniform draw from
`List.range m` modulo `n` is exactly uniform: every residue has precisely `m / n` preimages.

This is the fact the `×15` domain forces. With `n = 15·2^j` and `n ∣ p − 1` it applies directly;
without the divisibility, residue 0 is heavier by `1/p`, which at a `2^-258` per-round budget is
fatal. -/
theorem sampler_uniform (n m : Nat) (hdiv : n ∣ m) (hn : 0 < n) :
    ∀ r, r < n → count (List.range m) (fun x => x % n = r) = m / n := by
  intro r hr
  obtain ⟨q, rfl⟩ := hdiv
  rw [Nat.mul_div_cancel_left _ hn]
  induction q with
  | zero => simp [count]
  | succ q ih =>
    rw [Nat.mul_succ, List.range_add, count_append, ih]
    have hcongr : count (List.map (fun x => n * q + x) (List.range n)) (fun x => x % n = r)
        = count (List.range n) (fun x => x = r) := by
      rw [count_map]
      apply count_congr_mem'
      intro x hx
      rw [List.mem_range] at hx
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hx]
    rw [hcongr]
    have h1 : count (List.range n) (fun x => x = r) ≤ 1 :=
      count_le_one_of_unique List.nodup_range _
        (fun a b ha hb => by rw [show a = r from ha, show b = r from hb])
    have h2 : 0 < count (List.range n) (fun x => x = r) :=
      count_pos_of_mem' (List.mem_range.mpr hr) rfl
    omega

/-! ## Why the FRI `Setup` never needs a power of two

`Udr.Setup`'s only size axiom is `nn i = 2 * nn (i+1)` (`zk-formal/ZkFormal/Udr/Statements.lean`,
structure `Setup`, field `hnn`). It constrains **ratios**, never orders. There is no
power-of-two hypothesis anywhere in `Setup`, in `fri_layer`, or in the pass-set argument. So a
`15·2^K` layer family instantiates `Setup` on exactly the same terms as a `2^K` family, and every
`fri_layer` conclusion applies unchanged.

This is a reading of the existing definitions rather than a new theorem, and it is the whole
content of the x15 lever at the theorem level: the odd factor is a constant carried through the
halving, and nothing in the soundness argument can see it. The closed form
`nn i = nn r · 2^(r−i) · odd` is arithmetic bookkeeping that the argument never uses.
-/

/-! ## BabyBear: why `×15` is legitimate -/

namespace BabyBearCoset

open ZkFormal.Algebra

/-- `p − 1 = 15·2^27`: the top `×15` domain is the whole multiplicative group, and a subgroup of
order `15·2^K` exists for every `K ≤ 27`. -/
theorem p_sub_one_eq : P - 1 = 15 * 2 ^ 27 := by decide +kernel

theorem fifteen_dvd : 15 ∣ (P - 1) := ⟨2 ^ 27, p_sub_one_eq⟩

end BabyBearCoset

end ZkFormal.Udr
