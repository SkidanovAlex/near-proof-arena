# Self-contained digest dictionary for the actual native Wasm proof

The retained native SHA384-v4/Ext12 proof is740881bytes. Its WHIR authentication
paths serialize10422SHA384 digests (500256bytes);7103are distinct. The native
proof remains unchanged. This experiment losslessly transports it in596750bytes,
including every dictionary entry. With the unchanged919-byte request:597669bytes.
No external dictionary, original proof, witness or other omitted proof data is
needed for verification. This does not establish the outstanding PQ security
claim and does not provide a recursive parent proof.

Encoding version NPDICT01:

* Eight magic bytes, u32LE reconstructed-byte count, u32LE dictionary count.
* Dictionary entries are full48-byte digests in lexicographic order. The encoder
  includes806digests that occur more than once among native authentication paths.
* The remaining token stream uses tag0 + u32LE length + literal bytes, or tag1 +
  u16LE dictionary index. It contains4125references. The encoder substitutes exact
  byte matches; the decoder does not assign cryptographic meaning to tokens.
* The Rust decoder bounds reconstruction to16MiB, dictionary count to65536,
  checks indices and lengths, rejects unknown tags/truncation/empty literal runs,
  and requires exact final length. Then the unchanged native proof decoder and
  verifier must accept, including expected public values and full consumption.

Python reconstructs the native proof byte-for-byte. Rust independently decodes
and verifies in a directory containing only compressed proof and public statement,
not source proof/trace/fixture. A modified live dictionary entry reaches native
verification and fails with WhirError(MerkleVerify). Eight malformed-format tests
exercise the exact Rust decoder source. Logs and source snapshots retained.
No new cryptographic or Lean soundness theorem is claimed for this transport.

Reproduction from worktree, with degree12 patches prepared:

```sh
python3 research/near-compression/airbender/direct-wasm/prepare_native_sha384.py
NEARPROOF_REPLAY=1 NEARPROOF_WHIR_CENSUS=1 NEARPROOF_LITERAL_OUT="$PWD/research/near-compression/results/native-literal-sha384-ext12-compact" RAYON_NUM_THREADS=4 cargo run --locked --manifest-path /tmp/nearproof-native-sha384/Cargo.toml --release > /tmp/nearproof-whir-census.log 2>&1
python3 research/near-compression/airbender/direct-wasm/check_digest_dictionary.py
```

The first run exports auth-digests.bin next to the original proof. The checker
retains a copy here; that census file is encoder input/evidence, NOT a verifier
input. Current source contains an optional NEARPROOF_DICTIONARY path for replay.
The standalone replay uses the same backend and field patches archived with the
native compact profile. All digests are still verified; deduplication removes
redundant transmitted bytes, not verification checks or soundness parameters.

The wire reduction is19.45%, not a sub300KB result. Deduplicating existing values
cannot alone close the gap. Next size experiments should evaluate shared Merkle
opening reconstruction or change WHIR opening parameters under the same explicit
security budget; no impossibility claim is established by this finite result.
