# Native SHA384 Ext12: batched absorption and compact Merkle nodes

Actual retained193-instruction Wasm child, unchanged AIR/public inputs, Ext12,
WHIR268, blowup32, zero grinding. Version4 uses SHA-384 for every commitment and
transcript hash. Proof740881bytes, including public fields; plus request741800.
This is a direct child proof. No upgraded recursive parent or complete quantum
security certificate is supplied.

Changes relative to version2:

* Consecutive field observations append canonical u32LE words to a pending byte
  vector. Flush it with tag3 before a commitment observation or challenge draw;
  clear pending bytes and invalidate challenge leftovers. No merging across
  draws or commitments. Empty flush is a no-op. The existing challenge buffer
  uses all12words with rejection sampling.
* Merkle nodes hash exactly ASCII `NPQ4NODE` followed by the ordered pair of
  48-byte digests. The104-byte message takes one standard padded SHA384 block.
  No reduced-round or nonstandard hash compression is used. The node prefix
  begins with N, disjoint from the general framing's lowercase n prefix.
* All other framing uses `nearproof-native-sha384-ext12-v4`, one-byte tag and
  u64LE length-prefixed parts. Tags and byte layout otherwise follow the v2
  artifact README. This is a new protocol encoding, not compatible with old
  proofs. QROM/compiler applicability remains open.

Actual verification block counts:

| Profile | field absorption | Merkle nodes | all SHA384 blocks | proof bytes |
| --- | ---: | ---: | ---: | ---: |
| v2 | 31283 | 28642 | 64770 | 740881 |
| v3 batched | 1297 | 28642 | 34769 | 740881 |
| v4 batched+compact node | 1297 | 14321 | 20455 | 740881 |

The68.4% reduction is in measured hash compression workload, not proof size,
wall time or final recursive AIR size. Different transcript challenges account
for small changes in rejection sampling/draw counts.

Reproduce from worktree after preparing the degree12 patch:

```sh
python3 research/near-compression/airbender/direct-wasm/prepare_native_sha384.py
NEARPROOF_LITERAL_OUT="$PWD/research/near-compression/results/native-literal-sha384-ext12-compact" RAYON_NUM_THREADS=4 cargo run --locked --manifest-path /tmp/nearproof-native-sha384/Cargo.toml --release > /tmp/nearproof-native-sha384.log 2>&1
NEARPROOF_TRANSCRIPT_VECTORS=1 /tmp/nearproof-native-sha384/target/release/nearproof-native-sha384 > /tmp/nearproof-native-sha384-vectors.log
python3 research/near-compression/airbender/direct-wasm/check_native_sha384.py
python3 research/near-compression/airbender/direct-wasm/report_native_sha384_hash_cost.py
```

The saved Cargo.lock can be copied into the temporary crate before --locked.
Checks include fresh replay without trace/fixture files, six public mutations,
independent Lean runCall, exact artifact/input hashes, and Python/OpenSSL vectors
covering96samples, five rejections,13drawblocks, observation order and buffer
invalidation/exhaustion. The v3 artifact remains separately archived.

From research/near-compression run:

```sh
lake env lean NearCompression/NativeSha384Batching.lean
```

Lean proves buffer concatenation, exact ordered flush hash input and flush
idempotence for an arbitrary hash; node-frame injectivity for fixed left-digest
width;104-byte length;128-byte padding arithmetic; disjoint node/general domains.
These are operational model lemmas, not a Rust refinement, complete SHA384
circuit correctness, transcript injectivity theorem or quantum security proof.
Axiom audit retained. Source/profile constants are explicit byte lists in Lean.
