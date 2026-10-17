# Direct-Wasm PQ research handover — 2026-10-17

## Read first

This records the research/direct-wasm-whir lane at the user's requested wrap-up.
The existing main D1 work remains separate: read `docs/HANDOVER.md`,
`docs/logs/v3-d1-a7b-2026-10.md` and `docs/logs/v3-d1-phase2-2026-10.md`.
Do not replace the signed challenge or its pinned oracle with this research slice.
The user's “hangover.md” request is handled by updating the existing HANDOVER.md and this log.

Security contract: V3-D3A-STUDY.md section D, proven bounds only, failure at most
2^-128 against at most 2^64 quantum hash queries, SHA-384, PQ end to end.
This is not a claim of 128-bit quantum attack cost. The proven target is 0.5–1 MB;
less than 300,000 bytes remains the stretch target. Neither a native 268-bit
component estimate nor hash-only architecture establishes the QROM contract.

## What is actually established

The prepared straight-line Wasm slice supports i32.const, i32.add, drop and end,
one function and at most eight stack slots. Byte packing reduces table widths
from 803 total to EXEC 157 + CODE 114 + RANGE 24 = 295.

Lean now proves the concrete packed AIR implies the original semantic HoldsP,
then prepared Wasm runCall correctness under explicit preparation, eligibility
and sufficient-fuel hypotheses. PackedLiteralFamily generalizes CODE length;
the source AIR identity is kernel checked. The closure uses only the standard
propext/Classical.choice/Quot.sound axioms, without sorry or native_decide.
The exporter checks that the actual input AIR equals this proved candidate.

Key modules under research/near-compression/NearCompression:
PackedByteRange/Lift, PackedExprRewrite, PackedByteMacro/Layout,
PackedConcreteRewrite, PackedRangeBus, PackedConstraintRefinement,
PackedBusRefinement, PackedHoldsRefinement, PackedLiteralData/Coverage,
PackedLiteralCertificate/Execution/Family. The final theorem is
packed_literal_family_public_run_call; packed_literal_family_holds is its
semantic AIR bridge. Coverage has 1,199 kernel witnesses over 6,609 shared AST nodes.

Missing: native Rust/compiler refinement, cryptographic acceptance-to-HoldsP,
full Lean field construction/refinement, concrete QROM applicability/constants,
recursive knowledge composition, a SHA-384/Ext12 recursive parent, and full
NEAR host/memory/control/state/chunk coverage. No full 1 Pgas performance claim.

## Measurements and validation

* 193-instruction packed child: native 412,097 bytes; lossless digest dictionary
  356,150 bytes + 919-byte request = **357,069 transmitted bytes**. Original
  unpacked AIR best dictionary+request was 451,221 bytes. Under 300,000 not met.
  Evidence: results/native-literal-byte-packed, its -input and -dictionary siblings.
* Boundary suite: 16 supported cases through 1,025 instructions, including
  wraparound, signed boundaries, gas exhaustion, empty/eight-slot stacks and
  padding boundaries 255/257/513/1025. Exact polynomial constraints, natural bus
  balances, exported family AIR, eligibility and independent runCall checked.
  Nine-slot rejection is a witness-generator check, not a forged-proof rejection.
* A 16-bit range multiplicity overflow at 1,025 instructions was fixed by splitting
  counts across repeated receiver rows (each <=65,535). Existing AIR and theorem
  allow repeats. Largest fixture uses 2,048 EXEC/CODE rows, 512 range rows and
  155,648 lookups. Original 193 inputs remain byte-identical.
* Final native extension: five-instruction gas-failure case, native proof 378,849
  bytes + request 198 = **379,047 bytes**, without dictionary compression.
  Prove 13.6879 s, successful verify 0.007466 s, keygen 0.000619 s;
  wall 13.69 s, peak RSS 1,666,132 KiB, RAYON_NUM_THREADS=4. Single observation
  on ReferenceDevice/CpuColMajorBackend, not a controlled throughput benchmark.
  Prove timing includes reading the fixture; verify excludes keygen/decoding.
  Fresh replay hid witness/spec/fixture files; six public mutations rejected.
  Independent SHA-384 transcript vectors (96 samples, five rejections), Lean
  eligibility and runCall all passed. See results/native-packed-scaling/gas-failure5.
  The 1,025-instruction fixture is staged in long1025; no native proof was run.

Historical packing.json formal_refinement_proved=false and older report exclusions
predate formal closure; consult closed-certificate-check.json, refinement-check.json,
Lean audits and the new report's closed_semantic_air field. Closure does not prove
the Rust implementation or cryptographic soundness.

## Resume and reproduce

From research/near-compression:

```sh
lake build NearCompression.PackedLiteralFamily
python3 airbender/direct-wasm/check_packed_literal_certificate.py
python3 airbender/direct-wasm/check_packed_refinement.py
python3 airbender/direct-wasm/check_packed_boundaries.py
```

Use the repository heavy-build wrapper and CPU reservations in HANDOVER.md for
heavy runs. Never share mutable .lake traces via hard links.

Native tools: generate_native_literal_recursion.py --packed-bytes --no-install
[--fixture PATH] --out PATH; prepare_native_sha384.py --literal-source PATH --out PATH;
then build the standalone crate. check_native_sha384.py accepts --input-source,
--out, --request and --prove-log. Its oracle currently has fuel 256: raise this
explicitly and validate the fuel requirement before using it for long workloads.
Preparing a workload overwrites /tmp/nearproof-native-sha384/src/literal.rs;
do not prepare workloads concurrently. At wrap-up the binary/source contain gas-failure5.

Profile: n_stack=15, k=3, log_blowup=7, all_list=1, interaction_log=26,
query target 268, no grinding. Set the corresponding NEARPROOF_* variables and
NEARPROOF_LITERAL_OUT, RAYON_NUM_THREADS=4. The checker reads transcript vectors
from /tmp/nearproof-native-sha384-vectors.log; refresh by running the binary with
NEARPROOF_TRANSCRIPT_VECTORS=1. Native component minimum 268.7638 bits is uncertified.

Dependencies are not hermetic: backend d667af5929d0ea9e5194adf639d6bddeb8c10f9a
at /home/illia/.cargo/git/checkouts/stark-backend-708f1155344bec0c/d667af5 has
research patches; p3-baby-bear and p3-monty-31 v0.4.3 patched copies live under
/tmp/nearproof-ext12-rust. Saved native results contain Cargo manifest/lock,
backend.patch, plonky3-ext12.patch and Rust sources. Preserve/reconstruct these;
do not reset the shared backend. Ext12 uses X^12-31 over BabyBear; independent
irreducibility/differential checks are not full Lean implementation refinement.
SHA-384 transcript v4 uses rejection sampling, batched field absorption and
104-byte NPQ4NODE framing. Do not silently revert it to an older experiment.

## Next priorities

1. Reconstruct a reproducible dependency setup, then measure native variable-length
   workloads with independent replay and proper oracle fuel; retain exact proof,
   request and transport byte accounting. No long proof is currently in progress.
2. Build the SHA-384/Ext12 recursive parent. Earlier Ext4/Poseidon recursion is only
   diagnostic, below the security contract and not a compression win.
3. Close acceptance-to-HoldsP and concrete QROM/composition obligations before
   calling the system post-quantum secure. Keep interface statements fixed before
   parallelizing Lean lemmas; avoid proving disconnected abstractions.
4. Broaden Wasm/NEAR coverage and integrate with main's existing semantic interfaces.
   Native slice benchmarks cannot establish full chunk capacity or 1 Pgas throughput.

Tests at the semantic, native verification, independent execution and transport
levels provide different evidence. Keep these claims separate. Avoid parameter
sweeps until a measured bottleneck and security-admissible hypothesis justify one.
