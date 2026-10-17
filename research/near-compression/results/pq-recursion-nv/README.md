# NV: narrow fixed-point verifier circuit (results)

Design: `DESIGN.md`. Code: `crates/recursion/src/nv/` in the `openvm-sha384` tree (patch
`native/recursion/patches/openvm-recursion-sha384.patch`). Tests: `cargo test --release -p
openvm-recursion-circuit --lib nv_`.

## Milestone b: NV v0 verifies a real child (measured)

NV v0 has 10 AIRs:
* ALU (104 columns);
* transcript hash/observe/sample (95 / 8 / 20);
* MerkleNv (100);
* SHA-512 compression (442);
* SHA table (18), block chaining (134), packer (45), byte table (2).

That is **968 columns** in total. The 37 verifier-logic AIRs of the port are replaced by
the one ALU.

* **Program.** `nv/verifier.rs` is the stark-backend SWIRL verifier written against a
  program builder (`nv/builder.rs`). The builder emits one ALU instruction per call and
  executes it at the same time.
  * The program's transcript ends in the same state as the native verifier's
    (`nv_program_fib`, `nv_program_interactions`).
  * A second proof of the same shape yields the identical instruction stream, so the
    program depends only on the vk, the params and the trace heights.
  * Tampering with any of 6 proof fields makes an in-program assertion fail.
* **Circuit.** The child is Fib 2⁵ (test params: l_skip 2, n_stack 8, k 3, queries
  [13, 7, 6], PoW 1–3 bits, checked in-circuit). The debug checker passes on all
  constraints and buses. An interactions child also passes. Size: ALU 2¹⁴ rows (7,405
  used, program incl. 544 reserved binding rows), 16.7M cells.
* **Tamper classes, all rejected by the circuit:**
  * Merkle sibling digest: Merkle root key lookup.
  * Opened value: ALU `ZERO` (WHIR final check). The Merkle root would also fail.
  * Transcript sample, row-consistent: slot bus against the ALU, state-word bus.
  * Commit limb: slot bus, unit bus.
  * An ALU result: ALU constraint.
* **Not yet active:** program-word tampering at one level is caught only by the next
  level's binding check (milestone c) or by the native final check. This is by design;
  see DESIGN §2.1.
