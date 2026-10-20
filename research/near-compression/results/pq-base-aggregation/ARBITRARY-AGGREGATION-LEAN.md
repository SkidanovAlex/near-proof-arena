# Arbitrary-shape aggregation: the semantic half, proved

Status: 2026-10-20. Lane `pq-base-aggregation`. Lean, no `sorry`, axioms `⊆ {propext,
Classical.choice, Quot.sound}`.

This closes the semantic part of obligations **N3/N4** and **Z4/Z5** in
`docs/logs/pq-arbitrary-aggregation-proof-obligations-2026-10-19.md`, for the *relation* and the
*statement* a tree certifies. The proof-system half (QROM extraction across nodes, error
independence, byte-level size) is still open and listed at the end.

## 1. What was proved

Files (new, `zk-formal/ZkFormal/PQ/Aggregation/`, wired into `ZkFormal.lean`):

| file | contents |
|---|---|
| `Tree.lean` | `RangeTree` (arbitrary arity/depth), `leaves`, `run`; shape independence; regrouping; the certified-root theorem |
| `Statement.lean` | `Stmt` (native `RangeStmt` shape), `compose`/`composeFrom`, `Chainable`; compose = root; rejection; associativity |
| `Shape.lean` | combines the two: run, root and statement are shape-independent |

### 1.1 Execution (`Tree.lean`)

| theorem | statement |
|---|---|
| `RangeTree.run_eq_foldSegments` | for **every** tree `t`, `t.run = foldSegments t.leaves` |
| `RangeTree.run_node_split` | a node over `a ++ b` equals the binary node `node [node a, node b]` |
| `RangeTree.run_node_single` | a one-child node is a passthrough |
| `RangeTree.run_node_nil` | the empty node is a no-op |
| `RangeTree.run_witnesses` | locally valid, consecutively linked leaf witnesses compose to the last result |
| `RangeTree.certified_root` | for **any** tree, matching leaf witnesses + local validity + boundary links ⇒ `t.run input = output` |

`certified_root` is the tree form of `NearCompression.exact_chain`: the proof system supplies one
`LeafValid` witness per leaf and one `link` fact per adjacent pair; the tree contributes nothing
that can change the conclusion.

### 1.2 Statement (`Statement.lean`)

`Stmt` mirrors the native `RangeStmt` (`ctx, a, e, sa, se`) from
`native/recursion/patches/openvm-recursion-agg.patch`. `compose` mirrors `RangeStmt::compose`:
equal context, `b.a = a.e`, `b.sa = a.se`.

| theorem | statement |
|---|---|
| `Stmt.compose_eq_root` | on any chainable nonempty list, `compose` = `root` (first ctx/a/sa, last e/se) |
| `Stmt.compose₂_assoc` | composition is associative, so `k`-ary regrouping leaves the root unchanged |
| `Stmt.chainable_of_composeFrom_some` | **soundness**: if `composeFrom` succeeds, the list really chains |
| `Stmt.compose_from_eq_none` / `Stmt.compose_rejects` | **rejection**: a non-chainable list composes to `none`, so `V_d`'s statement check fails |

The rejection theorem is what rules out ragged trees, dropped children and swapped children at the
statement level: any such tree produces `none`, not the claimed root.

### 1.3 Shape independence (`Shape.lean`)

| theorem | statement |
|---|---|
| `Shape.tree_run_shape_irrelevant` | two trees with the same leaves have the same run |
| `Shape.tree_root_shape_irrelevant` | two trees with the same leaves have the same composed root (hence the same digest and the same `V_d` check) |
| `Shape.root_of_tree` | the root is `(f first).ctx/a/sa` to `(f last).e/se`; arity and depth do not appear |

Because the range digest is a fixed function of `Stmt`, `tree_root_shape_irrelevant` gives that the
verifier's expected digest is independent of the aggregation shape. That is Z4's statement-level
content. Z5 (a fixed point exists for every tree) follows because the final layer verifies an inner
proof of a shape that also does not depend on the tree.

## 2. What this does **not** prove

Still open, unchanged:

1. **N3 (`Theorem 7.4-tree`, proof-system level).** Per-node straight-line extraction from one QROM
   database over an arbitrary tree. The semantic induction is now available; the QROM composition is
   not.
2. **N4 (error independence from node count).** Needs N3 plus the single-database form of
   `PROOF.md` Thm 6.4; the per-node union bound still fails at ~295 proofs.
3. **Range-digest binding (tag 9).** `link` in `Tree.lean` is abstract; §1.2 assumes the digest is
   a function of `Stmt`. Collision resistance (or A-IC) is unchanged from `PROOF.md` §1.3.
4. **Byte-level size independence (Z4's cost half).** The final layer's *bytes* are argued in
   `DESIGN-BASE.md` §5.4; this file proves only that the *statement* checked does not depend on the
   tree.
5. **Base-faithful for a real `seg-v1` set** (B4/B11) and the join (J3). Untouched.

## 3. Reproduce

```sh
cd zk-formal
lake build ZkFormal.PQ.Aggregation.Shape
cat > /tmp/ax.lean <<'EOF'
import ZkFormal.PQ.Aggregation.Shape
open ZkFormal.PQ.Aggregation
#print axioms Shape.tree_run_shape_irrelevant
#print axioms Shape.tree_root_shape_irrelevant
#print axioms Shape.root_of_tree
#print axioms RangeTree.certified_root
#print axioms RangeTree.run_node_split
#print axioms Stmt.compose_eq_root
#print axioms Stmt.compose_rejects
EOF
lake env lean /tmp/ax.lean
```

Axes observed: `propext`, `Classical.choice`, `Quot.sound` only; no `sorry`, no `native_decide`.
