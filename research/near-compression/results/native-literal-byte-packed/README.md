# Byte-packed Wasm AIR candidate — refinement pending

This candidate changes the AIR. It is not yet a formally justified replacement
for the original bit-based relation. The same retained193-instruction execution,
request and4891public fields are used; independent Lean execution matches those
outputs. Native cryptographic verification proves the new AIR only.

Selected integer regions (stack,gas,difference,result,immediate,fee) pack eight
bits into one byte column. All packed columns send a bus4 lookup on every row.
A24-column table supplies values constructed from eight Boolean bits and16-bit
multiplicities. EXEC width605 ->157; CODE198 ->114; range table24: total803 ->295.
The transformer rejects any unhandled use of removed bit columns. It retains
ordinary constraints, replaces CODE inactive bit-zero constraints by byte-zero
constraints and adds mandatory range interactions. Original FN/PC bits and
control flags stay explicit. The unchanged default generator was regression
checked byte-for-byte against original inputs.

The range witness has256rows,19456lookups,max multiplicity15578. Native maximum
interaction count is raised from2^20 to2^26 to cover conservative weighted-height
bounds. This affects the key/soundness calculation; it is not assumed free.
Profile:Ext12,SHA384-v4,query268,all-list m3,blowup128,n_stack15,k3,zero grinding.
Native minimum component268.7638bits;LogUp331.5753,proximity320.9309. Uncertified.

Actual native proof412097bytes:22904GKR+31432relations+1840stacking+336260WHIR+
19661other. Lossless dictionary356150bytes; with request357069. These are
candidate measurements, not proof that the original Wasm relation has that size.
Prior unmodified-AIR baseline remains451221transmitted bytes.

Validation:

* Every honest packed row constraint evaluates to zero; all buses balance as
  exact natural counts. Source public values remain unchanged.
* Native proof verification, six public-output mutations, witness-independent
  replay (all three trace files hidden), preparation and independent Lean
  runCall checks pass.
* Replace first-row stack bytes[0,0] with[p-256,1]. The16-bit limb remains zero
  in Fp. ALL polynomial constraints still pass and only range bus4 is unbalanced.
  Native prover rejects with LogupZerocheck(NonZeroRootSum), before producing a
  proof. This is not a forged-proof verifier rejection test.
* PackedByteRange.lean proves natural range-balance support, canonical limb
  encoding and injectivity, plus the concrete invalid-byte arithmetic example.
  It does not prove native LogUp-to-integer balance, compiler correctness or
  packed-AIR-to-original-AIR refinement. That refinement is the next gate before
  adopting this candidate as a semantic replacement.

Reproduction from worktree after Ext12 setup:

```sh
python3 research/near-compression/airbender/direct-wasm/generate_native_literal_recursion.py --packed-bytes --no-install --out research/near-compression/results/native-literal-byte-packed-input
python3 research/near-compression/airbender/direct-wasm/prepare_native_sha384.py --literal-source research/near-compression/results/native-literal-byte-packed-input --out research/near-compression/results/native-literal-byte-packed
NEARPROOF_N_STACK=15 NEARPROOF_ALL_LIST=1 NEARPROOF_LOG_BLOWUP=7 NEARPROOF_INTERACTION_LOG=26 NEARPROOF_LITERAL_OUT="$PWD/research/near-compression/results/native-literal-byte-packed" RAYON_NUM_THREADS=4 cargo run --locked --manifest-path /tmp/nearproof-native-sha384/Cargo.toml --release > /tmp/nearproof-native-byte-packed.log 2>&1
NEARPROOF_TRANSCRIPT_VECTORS=1 /tmp/nearproof-native-sha384/target/release/nearproof-native-sha384 > /tmp/nearproof-native-sha384-vectors.log
python3 research/near-compression/airbender/direct-wasm/check_native_sha384.py --input-source research/near-compression/results/native-literal-byte-packed-input --out research/near-compression/results/native-literal-byte-packed --prove-log /tmp/nearproof-native-byte-packed.log
python3 research/near-compression/airbender/direct-wasm/check_packed_byte_air.py
```

From research/near-compression:

```sh
lake env lean NearCompression/PackedByteRange.lean
```

No fullNEAR, complete QROM security, upgraded recursive parent or controlled
performance result is established by this candidate.
