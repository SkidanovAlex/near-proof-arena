# Actual-key shape field sensitivity

This is a counterfactual calculator run, not a larger-field proof or a security
certificate. See report.json for exclusions and source hashes.

From the research worktree:

```sh
python3 research/near-compression/airbender/direct-wasm/generate_native_literal_recursion.py --out research/near-compression/results/native-literal-field-screen
```

Then from the patched, pinned `/tmp/nearproof-openvm` checkout:

```sh
NEARPROOF_LITERAL_FIELD_SCREEN=1 \
NEARPROOF_LITERAL_QUERY_BITS=128 \
NEARPROOF_LITERAL_LOG_BLOWUP=5 \
NEARPROOF_LITERAL_OUT=/data/illia/nearproof-wt/direct-wasm-whir/research/near-compression/results/native-literal-field-screen \
RAYON_NUM_THREADS=4 \
cargo test --locked --profile fast -p openvm-recursion-circuit tests::native_literal::nearproof_literal_slice_recursion -- --exact --nocapture
```

The 128 input setting constructs the measured baseline keys. The screen itself
rebuilds WHIR query schedules at 258 and 268 bits and varies only the calculator's
challenge-field cardinality. It asserts parity with the native actual-key
calculator at degree four. It does not build an extension field, replace hashes,
regenerate recursive AIRs for those primitives, or emit a new proof.
