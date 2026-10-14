import ZkFormal.Stark.Protocol
import ZkFormal.Stark.VerifierDefs

/-!
# ZkFormal.Stark.Verifier — the decision functions of `np-udr-stark-v1`

`Iop.verifier A prm : IopSpec F K` (schedule from `Protocol`, plus the
clear-text checks `global` and the per-position checks `check`), and the
deployed verifier model `verifier A prm : TreeVerifier`, its BCS compilation.

* **global** (DESIGN.md §4 step 4): for every table, the ALI identity at the
  out-of-domain point `z`,
  `Σ_j α_c^j · c_j(z) = (z^T - 1) · Σ_j z^{jT} · Q_j(z)`,
  where `c_j` ranges over `Table.allConstraints` and then the generated aux
  (grand-product) constraints, evaluated from the claimed OOD values; and the
  bus equation `∏ send finals = ∏ receive finals`.
* **check** at position `x`: the batched DEEP functions of every height class
  from the opened rows, then FRI: layer-0 and committed-layer leaf
  consistency, the folds `f' = (u₀+u₁)/2 + β·(u₀-u₁)/(2y)`, roll-ins
  `f ← f + γ_i·B_class`, and the final polynomial `p₀ + p₁·X`.

Selectors at `z` (table height `T`, trace generator `ω`):
`isFirst = (z^T-1)/(T(z-1))`, `isLast = (z^T-1)/(T(ωz-1))`,
`isTransition = 1 - isLast`.
-/

namespace ZkFormal.Stark

open ArenaCore Lean.Grind ZkFormal.Air

section
variable {F K : Type} [Field F] [Field K] [StarkField F K] [DecidableEq F] [DecidableEq K]

attribute [local instance] Semiring.natCast

/-- `x^n` by repeated squaring (`n` given by its bits). -/
def powK (x : K) (n : Nat) : K := x ^ n

end

/-- **The deployed verifier model**: the BCS compilation of `Iop.verifier`. -/
def verifier (F K : Type) [Field F] [Field K] [StarkField F K] [DecidableEq F] [DecidableEq K]
    (A : Air) (prm : Params) : ZkFormal.TreeVerifier :=
  ⟨fun pub cb pb => Bcs.compile (F := F) (Iop.verifier F K A prm) pub cb pb⟩

theorem verifier_eq_compile (F K : Type) [Field F] [Field K] [StarkField F K] [DecidableEq F]
    [DecidableEq K] (A : Air) (prm : Params) (pub cb pb : Bytes) :
    (verifier F K A prm).tree pub cb pb = Bcs.compile (F := F) (Iop.verifier F K A prm) pub cb pb :=
  rfl

end ZkFormal.Stark

namespace ZkFormal.Stark

/-- Admissible headers of the np IOP: `headerOk` and a query domain of at least `2^minQueryLog`. -/
theorem verifier_headerOk {F K : Type} [Lean.Grind.Field F] [Lean.Grind.Field K] [StarkField F K]
    [DecidableEq F] [DecidableEq K] {A : ZkFormal.Air.Air} {prm : Params} {hdr : List Nat}
    (h : (Iop.verifier F K A prm).headerOk hdr = true) :
    headerOk A prm hdr = true ∧ minQueryLog ≤ queryLog A prm hdr := by
  change (headerOk A prm hdr && decide (minQueryLog ≤ queryLog A prm hdr)) = true at h
  simpa only [Bool.and_eq_true, decide_eq_true_eq] using h

end ZkFormal.Stark
