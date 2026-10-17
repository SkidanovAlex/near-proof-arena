# Actual WHIR parameter experiment on retained Wasm slice

Same literal193-instruction relation, field Ext12, SHA384-v4, target268 query
bits, zero grinding, l_skip2,n_stack16,k3. Three new actual proofs isolate larger
blowup, all-round list decoding, then their combination. All pass native verify,
six public mutations, witness-independent replay and independent Lean execution.

| Profile | blowup | first-round regime | native bytes | native min component bits |
| --- | ---: | --- | ---: | ---: |
| baseline | 32 | unique | 740881 | 268.5253 |
| rate7 | 128 | unique | 719329 | 268.9462 |
| alllist | 32 | list,m3 | 579185 | 268.7577 |
| combined | 128 | list,m3 | 512609 | 268.7638 |

The combined case has queries[82,63,51,43,37,33]. List-size penalties are included
in the native calculator: LogUp337.5753bits, proximity317.9309bits. These estimates
are not a concrete QROM certificate or a Lean soundness proof. List-decoding
bound applicability, transcript compiler losses and recursive composition remain
open. No conjectured-bound or security-certification flag is asserted.

Actual combined proof census:20408GKR+81248relations+1936stacking+389368WHIR+
19649other=512609. WHIR contains297168authentication bytes,2624initial base-field
values,87168codeword extension-field values. Standalone verification uses12474SHA384 compression blocks. These are counts,
not proving/verification timing or recursive AIR-size measurements.

Lossless dictionary transport is separately retained under
../native-literal-alllist-rate7-dictionary/:450302bytes, plus919request=451221.
Still fails strict sub300000. No global optimum or impossibility result claimed.
The higher blowup costs a larger evaluation domain; performance is not established.

Reproduction from worktree, after the degree12 patch setup:

```sh
python3 research/near-compression/airbender/direct-wasm/prepare_native_sha384.py --out research/near-compression/results/native-literal-sha384-alllist-rate7
NEARPROOF_ALL_LIST=1 NEARPROOF_LOG_BLOWUP=7 NEARPROOF_LITERAL_OUT="$PWD/research/near-compression/results/native-literal-sha384-alllist-rate7" RAYON_NUM_THREADS=4 cargo run --locked --manifest-path /tmp/nearproof-native-sha384/Cargo.toml --release > /tmp/nearproof-native-sha384-alllist-rate7.log 2>&1
NEARPROOF_TRANSCRIPT_VECTORS=1 /tmp/nearproof-native-sha384/target/release/nearproof-native-sha384 > /tmp/nearproof-native-sha384-vectors.log
python3 research/near-compression/airbender/direct-wasm/check_native_sha384.py --out research/near-compression/results/native-literal-sha384-alllist-rate7 --prove-log /tmp/nearproof-native-sha384-alllist-rate7.log
python3 research/near-compression/airbender/direct-wasm/report_native_whir_profiles.py
```

Current driver rejects before proving if the native minimum component estimate
falls below the requested query target. This numerical guard is not certification.
Other new profile artifacts have their matching sources,parameters,logs and
Cargo locks. Use their settings from report.json during replay. Historical
baseline settings remain the defaults; old proof artifacts are unchanged.
