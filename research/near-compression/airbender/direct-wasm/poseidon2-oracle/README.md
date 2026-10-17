This executable is an independent permutation oracle for the Python AIR layout.
It calls the pinned Plonky3 width-32 BabyBear default permutation directly.
Input/output are one row of 32 canonical decimal field elements per line.
It is not a prover, sponge, quantum-security test, or production dependency.

From `research/near-compression`:

```sh
CARGO_TARGET_DIR=/tmp/near-poseidon2-target cargo build --release --locked --manifest-path airbender/direct-wasm/poseidon2-oracle/Cargo.toml
python3 airbender/direct-wasm/test_poseidon2_permutation_air.py --oracle /tmp/near-poseidon2-target/release/near-poseidon2-layout-oracle
```

The initial build used rustc/cargo 1.96.0. The report pins the executable SHA256,
which may vary with toolchain/platform, and retains its checked test vectors.
Cargo.lock pins the dependency graph. No upstream files are modified.
