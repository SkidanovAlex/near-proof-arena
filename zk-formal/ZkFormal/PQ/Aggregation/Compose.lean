import ZkFormal.PQ.Aggregation.Shape

/-!
# ZkFormal.PQ.Aggregation.Compose — tree induction for recursive composition

Lane `pq-base-aggregation`. The structural half of `Theorem 7.4-tree` (`DESIGN-BASE.md` §9.1,
obligations N3/N4 in `docs/logs/pq-arbitrary-aggregation-proof-obligations-2026-10-19.md`).

`PROOF.md` Theorem 7.4 composes an accepting final proof with a **linear** chain of layers: one
database `D`, one induction step per level, error independent of depth. For an aggregation
**tree** the induction runs over the tree instead of a chain. This file isolates and proves that
induction, so the only remaining obligation is the per-node extraction fact — where `Theorem 6.4`
is applied, once, to the whole family.

## The division of labour

* **Proved here.** If a tree is certified (leaves satisfy `Base`; every node satisfies the node
  step on its children's roots), then its root satisfies `Base`. The proof is induction on the
  certification derivation, so it holds for any arity and any depth, and it carries no
  probability — hence no per-node error accumulation.
* **Not proved here (a named premise).** That a verifying proof yields the node step and
  certified children. That is `PROOF.md` Theorem 6.4 applied once to the family of vks, plus
  NV-faithful (F1)–(F3). It is paper-level today (GAPS S-19/S-28).
-/

namespace ZkFormal.PQ.Aggregation

/-- A recursive proof tree over statements of type `S`.

A leaf is a base proof. A node has a statement and any finite list of children. -/
inductive ProofTree (S : Type) where
  /-- A base-layer proof of statement `s`. -/
  | leaf (s : S)
  /-- An inner proof of statement `s`, exposing children. -/
  | node (s : S) (children : List (ProofTree S))

namespace ProofTree

variable {S : Type}

/-- The root statement. -/
def root : ProofTree S → S
  | .leaf s => s
  | .node s _ => s

/-- All statements, root first. -/
def statements : ProofTree S → List S
  | .leaf s => [s]
  | .node s cs => s :: cs.flatMap statements

/-- Number of inner nodes. -/
def innerNodes : ProofTree S → Nat
  | .leaf _ => 0
  | .node _ cs => 1 + (cs.map innerNodes).sum

/-- Height. -/
def height : ProofTree S → Nat
  | .leaf _ => 1
  | .node _ cs => 1 + (cs.map height).foldr max 0

/-- **Certification.** An inductive predicate, so its derivation is the induction principle and
arbitrary arity is free.

* `leaf`: the base predicate holds.
* `node`: the node step holds for this statement and the children's roots, and every child is
  certified.

`NodeOK s children` abstracts the node's obligations (child proofs verify, levels advance, the
statement digest links them). In deployment it is derived from the QROM extraction premise. -/
inductive Certified (Base : S → Prop) (NodeOK : S → List S → Prop) : ProofTree S → Prop where
  | leaf {s : S} : Base s → Certified Base NodeOK (.leaf s)
  | node {s : S} {cs : List (ProofTree S)} :
      NodeOK s (cs.map root) →
      (∀ c ∈ cs, Certified Base NodeOK c) →
      Certified Base NodeOK (.node s cs)

/-- **Tree composition (N3, structural half).**

If the node step turns certified children into a certified parent, every certified tree has a
certified root. By induction on the certification derivation: arity and depth are arbitrary, and
no probability is carried, so a single-database premise is used once (N4). -/
theorem certified_root (Base : S → Prop) (NodeOK : S → List S → Prop)
    (hstep : ∀ s cs, NodeOK s cs → (∀ c ∈ cs, Base c) → Base s) :
    ∀ t : ProofTree S, Certified Base NodeOK t → Base t.root := by
  intro t hcert
  induction hcert with
  | leaf hb => simpa [root] using hb
  | node hnode _ ih =>
    simp only [root]
    refine hstep _ _ hnode ?_
    intro c hc
    rw [List.mem_map] at hc
    obtain ⟨t, ht, rfl⟩ := hc
    exact ih t ht

/-- **Root invariance (N4).** The composed predicate mentions only the root, so it is invariant
under changing anything below the root. -/
theorem base_root_of_eq {Base : S → Prop} {t₁ t₂ : ProofTree S}
    (h : t₁.root = t₂.root) (h₁ : Base t₁.root) : Base t₂.root := by
  rw [← h]; exact h₁

/-- **Any arity replays as binary.** Splitting a node's children into two nested nodes leaves the
root unchanged, so a circuit with a fixed binary node implements the statement for arbitrary
arity. -/
theorem arity_split (s : S) (a b : List (ProofTree S)) :
    (ProofTree.node s (a ++ b)).root
      = (ProofTree.node s [ProofTree.node s a, ProofTree.node s b]).root := rfl

/-- **Node count does not enter.** Trees with the same root have the same composed predicate,
whatever their number of inner nodes. -/
theorem node_count_irrelevant {Base : S → Prop} (t₁ t₂ : ProofTree S)
    (h : t₁.root = t₂.root) : Base t₁.root ↔ Base t₂.root := by
  rw [h]

end ProofTree

end ZkFormal.PQ.Aggregation
