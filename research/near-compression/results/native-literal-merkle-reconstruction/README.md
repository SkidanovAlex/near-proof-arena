# Executed Merkle reconstruction analysis

This is a measured reconstruction plan, not a new compressed proof format.
The source is the verified SHA384-v4/Ext12 all-list/blowup128 Wasm child.
A fresh native verifier run records only executed leaf and Merkle-node hashes:
2472leaf calls and8354node calls. Python/OpenSSL independently checks every hash.
The trace has9073distinct outputs;6191authentication occurrences contain4741
distinct digests.

Expanding all authentication targets through this captured graph gives:

* 4135frontier digests not derived by these captured hash operations;
* 2472leaf hashes with source bytes present outside all omitted auth slots;
* 6595derived internal hashes.

The analyzer zeroes ALL authentication slots, evaluates the plan using only
retained frontier digests and non-authentication proof bytes, restores every
slot, and checks exact equality to the original native proof. Thus it checks
actual reconstruction, not just a count of shared digest values. The source
proof hash and every trace output are checked independently.

For this fixed plan, frontier digests require198480bytes and the unchanged
non-authentication payload is215441bytes. With the919-byte request, that is
414840bytes BEFORE metadata. This is not a universal lower bound: other algebraic
structure, different leaf schedules, proof layouts, parameters or protocols
could change both terms.

A simple explicit plan representation (1-byte opcode,2-byte child IDs,4-byte
leaf offset/length) requires257838program bytes. With auth-reference tokens and
unchanged non-authentication bytes it would require491852bytes before framing,
versus the already verified450302-byte dictionary encoding. This representation
is therefore not adopted. No actual wire codec or verifier for it is claimed.

Retained files: deterministic gzip of the executed trace and topologically
ordered reconstruction plan; native replay log; instrumented source; report.
The trace is research evidence, not part of a claimed transmitted proof.

Reproduce from worktree after preparing the native Ext12 environment:

```sh
python3 research/near-compression/airbender/direct-wasm/prepare_native_sha384.py --out research/near-compression/results/native-literal-sha384-alllist-rate7
NEARPROOF_ALL_LIST=1 NEARPROOF_LOG_BLOWUP=7 NEARPROOF_REPLAY=1 NEARPROOF_MERKLE_TRACE="$PWD/research/near-compression/results/native-literal-merkle-reconstruction/merkle-trace.bin" NEARPROOF_LITERAL_OUT="$PWD/research/near-compression/results/native-literal-sha384-alllist-rate7" RAYON_NUM_THREADS=4 cargo run --locked --manifest-path /tmp/nearproof-native-sha384/Cargo.toml --release > /tmp/nearproof-merkle-trace.log 2>&1
python3 research/near-compression/airbender/direct-wasm/analyze_native_merkle_reconstruction.py
```

The analyzer also accepts the retained gzip when the raw trace is absent. Its
initial full-slice replay remains the authoritative acceptance check. There is
no new cryptographic/Lean soundness theorem, recursive parent or fullNEAR claim.
Decision: shared-path reconstruction alone does not close the gap in this plan;
retain dictionary transport and pursue an additional protocol-level reduction.
