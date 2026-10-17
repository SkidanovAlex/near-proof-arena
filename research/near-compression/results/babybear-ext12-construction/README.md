# Concrete degree-12 BabyBear candidate

Candidate: F_p[X]/(X^12-31), p=2013265921. Degree12 provides margin beyond
the frozen-shape 268-bit screen and admits a simple binomial because 12 divides
p-1. This is a candidate, not a selected final field or a minimum-cost claim.

`construction.json` contains an independent polynomial irreducibility check,
complete factorization of p^12-1, a multiplicative generator, Frobenius constant,
compatible roots of unity and deterministic arithmetic vectors. SymPy1.14.0
checks irreducibility; a separate coefficient-convolution implementation checks
generator order, roots, inverses and produces vectors. All listed prime factors
are below2^64. These are computational checks, not a Lean field construction.

`plonky3-ext12.patch` adds degree12 constants to p3-baby-bear0.4.3 and a scalar
schoolbook multiplication case to p3-monty-310.4.3. Both patched crates live in
an isolated temporary Cargo project; neither the Cargo registry nor the native
OpenVM checkout is modified. The upstream generic Frobenius inversion path is
used. This is a correctness implementation, not an optimized arithmetic kernel.

Reproduction from the research worktree:

```sh
python3 -m venv /tmp/nearproof-field-venv
/tmp/nearproof-field-venv/bin/pip install sympy==1.14.0
/tmp/nearproof-field-venv/bin/python research/near-compression/airbender/direct-wasm/construct_babybear_ext12.py
python3 research/near-compression/airbender/direct-wasm/prepare_ext12_rust.py
cargo run --manifest-path /tmp/nearproof-ext12-rust/Cargo.toml --release -- "$PWD/research/near-compression/results/babybear-ext12-construction/construction.json"
```

The preparation script requires the pinned0.4.3 crate sources in the local Cargo
registry. Cargo.lock is retained here for dependency review/replay; copy it to
the temporary project and use `--locked` to reproduce the retained dependency set.
Rust checks24 independent vectors,30 roots, zero-inverse rejection and48-byte
canonical coefficient round trips. The decoder check covers valid vectors only.

From research/near-compression, run:

```sh
lake env lean NearCompression/BabyBearExt12Constants.lean
```

Lean proves base-field non-square/non-cube conditions and concrete coefficients.
The axiom audit is retained in lean-audit.log. Missing: a Lean irreducibility and
field construction theorem, Rust refinement, integration in the actual Wasm
child/parent, SHA-384 throughout, and complete quantum-security composition.
No proof-size or runtime claim at the target security follows from these tests.
