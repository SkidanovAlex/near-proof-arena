# Actual Wasm child with SHA-384 and BabyBear Ext12

This proves the retained193-instruction literal Wasm slice with the same public
statement, native AIR and trace inputs. It is a direct child proof, not a recursive
parent or fullNEAR state transition. Field is F_p[X]/(X^12-31), commitments and
transcript use SHA-384, WHIR query target268, blowup32, all grinding disabled.
The actual key's native minimum component estimate is268.525bits. This is NOT a
composed quantum-security certificate; custom transcript applicability and
recursive knowledge composition remain unresolved.

Actual binary proof740881bytes, including4891public fields. With the unchanged
919-byte request:741800bytes. Size census in report.json. Source-field extension
and hashing changes were actually executed; these are not extrapolated sizes.
No controlled prover-speed claim is made for this reference CPU backend.

Reproduction from the worktree (after constructing the Ext12 patch as documented
in ../babybear-ext12-construction/README.md):

```sh
python3 research/near-compression/airbender/direct-wasm/prepare_native_sha384.py
NEARPROOF_LITERAL_OUT="$PWD/research/near-compression/results/native-literal-sha384-ext12" RAYON_NUM_THREADS=4 cargo run --manifest-path /tmp/nearproof-native-sha384/Cargo.toml --release > /tmp/nearproof-native-sha384.log 2>&1
NEARPROOF_TRANSCRIPT_VECTORS=1 /tmp/nearproof-native-sha384/target/release/nearproof-native-sha384 > /tmp/nearproof-native-sha384-vectors.log
python3 research/near-compression/airbender/direct-wasm/check_native_sha384.py
```

Cargo.lock is retained; copy it into the temporary crate and add --locked for
exact dependency replay. backend.patch captures the local backend modifications
used in addition to pin d667af5929d0ea9e5194adf639d6bddeb8c10f9a. The generator
uses the preserved native literal AIR from the prior actual-key experiment.

The checker verifies independent Python/OpenSSL transcript outputs, fresh-process
proof replay with all witness/fixture files hidden, six public-value mutations
(from the proving run), exact public-output parity with independent Lean runCall,
and unchanged source inputs. It archives source, proof, logs, patches and hashes.

## Experimental transcript v2

All hash messages begin with ASCII `nearproof-native-sha384-ext12-v2`, a one-byte
tag, then each payload's u64 little-endian byte length followed by its bytes.
Tag0 hashes canonical u32LE field leaves; tag1 hashes ordered left/right48-byte
digests. Tag2 initializes the transcript, with no payload. Tag3 absorbs the prior
48-byte state plus a canonical field word; tag4 absorbs the state plus a digest.
Both observation operations discard unused challenge words. Tag5 hashes the
prior state to draw another48-byte buffer. Words are scanned in u32LE order;
reject words >=4026531842, otherwise reduce modulo2013265921. Exhausted buffers
rehash, with no retry cap or zero-fill fallback. All12words are available.
The generic backend's sample_bits still masks a base-field sample; its bias is
charged by the native calculator. The rejection sampler itself has two accepted
32-bit preimages per field residue (existing FieldRejectionSampler.lean).
Neither this arithmetic fact nor a matching oracle proves the full transcript's
QROM security or a Rust refinement theorem.

The initial one-word-per-hash prototype remains separately archived in
../native-literal-sha384-ext12-singleword/. Its transcript domain is v1 and its
proof must be replayed with its own archived source, not the v2 binary.

Single v2 engine.verify call (keygen and decoding excluded):64770SHA-384
compression blocks:4456leaf,28642Merkle-node,1init,31283field-observation,
14commit-observation,374challenge-draw blocks. Counters derive from actual hash
input lengths including SHA-384 padding. They are workload counts, not recursive
AIR sizes or timing measurements. Batch field absorption and authentication
paths need attention before implementing a complete SHA-384 recursive verifier.
