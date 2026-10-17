# Native SHA-384/Ext12 prover: pinned dependencies

The direct-Wasm native child prover (`airbender/direct-wasm/native_sha384_*.rs`)
builds against research-patched copies of OpenVM `stark-backend` and Plonky3
`p3-baby-bear`/`p3-monty-31` 0.4.3 (degree-12 extension `X^12 - 31`). They used
to live in a mutated shared `~/.cargo/git` checkout and in `/tmp`. They are now
rebuilt from pinned sources:

| piece | source | patch |
|---|---|---|
| `stark-backend` | `github.com/openvm-org/stark-backend` @ `d667af5929d0` (v2.0.1) | `patches/stark-backend-d667af5.patch` (stark-backend verifier/keygen changes + cpu-backend diagnostic exports) |
| `p3-baby-bear`, `p3-monty-31` 0.4.3 | crates.io tarballs, sha256-pinned | `patches/plonky3-ext12.patch` |
| native crate lockfile | — | `crate/Cargo.lock` |

```sh
native/setup_native_deps.sh            # idempotent; verifies an existing tree
python3 airbender/direct-wasm/prepare_native_sha384.py --literal-source <input> --out <out>
cd $NEARPROOF_PQ_DEPS/native-sha384 && cargo build --release --locked
```

`NEARPROOF_PQ_DEPS` defaults to `/data/illia/nearproof-deps/pq-native`; all
scripts resolve paths through `native/native_paths.py`. The prepared crate is a
shared work directory: do not prepare two workloads against one root at once
(use a separate `NEARPROOF_PQ_DEPS` per concurrent run).

Validation (2026-10-17): from a fresh setup, `gas-failure5` re-proved with the
recorded profile gives a **byte-identical** `child.proof`
(sha256 `ba042e71…`, 378,849 B); transcript vectors are identical; the full
`check_native_sha384.py --oracle-fuel 1026` run (hidden-witness replay, six
public mutations, independent SHA-384 transcript, Lean eligibility and runCall)
passes. The regenerated Ext12 patch is byte-identical to the recorded one.

Retired diagnostic probes (Binius, Ext4/Poseidon OpenVM recursion) still name
their own `/tmp` scratch trees; they are below the security contract and not
part of this pipeline.

`sha384-air/` (L3 milestone 1, 2026-10-17): narrow SHA-512/384 compression AIR on
the same pinned backend and SHA-384/Ext12 config (`python3 sha384-air/prepare.py`,
then `cargo build --release --locked` there; standalone crate with its own lockfile).
Results: `results/pq384-sha-air/`.
