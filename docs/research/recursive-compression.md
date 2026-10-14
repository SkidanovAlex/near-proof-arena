# Recursive compression feasibility and validation

Research reopened on 2026-10-14 at the user's request, with a target of **less than
300,000 bytes for the complete transmitted proof**. This work evaluates recursive
compression; it does not change the frozen challenge, security profile, or the
historical R5 decision. The first implementation experiment wraps the existing v1
Rust reference verifier in RISC Zero 3.0.6. It is not a certificate for the v3
state-transition relation.

## Preferred direction: hash-based post-quantum compression

The user's updated target is a new hash-based scheme with no elliptic-curve
assumptions at any proof layer, aiming for 128-bit quantum attack cost and a
complete proof below 300,000 bytes. These are research targets, not established
properties of the current implementation. Pairing wrappers below are historical
comparisons and are outside this preferred direction.

Develop a dedicated algebraic verifier with Merkle-backed polynomial commitments,
using FRI as a baseline and WHIR as a candidate. Evaluate sumcheck/batched claims
to reduce wide trace openings as well as commitment query count. Include v3 hint
preprocessing inside the proved computation. Compare direct proving against one
level of recursive compression; direct proving provides a useful control when
the recursive composition theorem remains unresolved. Start with established
hash primitives; a new proof construction need not introduce a new hash function.

The security work must precede selecting final parameters:

1. Specify quantum oracle queries, adversary resources, recursion depth and
   adaptive statement counts. A 128-bit attack-cost target is different from
   failure probability at most 2^-128 under a fixed resource budget.
2. Replace or extend the classical oracle game in
   `formal-core/ArenaCore/Security/ROM.lean`. Its classical query transcript and
   lazy oracle table do not model superposition queries. Existing admission
   theorems do not establish quantum security.
3. Supply concrete quantum Fiat–Shamir bounds for the actual multi-round
   protocol, plus quantum extraction/composition and the commitment properties
   those reductions require. QROM soundness alone does not establish recursive
   knowledge soundness. The classical AROM result is not automatically a quantum
   composition result.
4. Account separately for algebraic errors, commitment binding, transcript and
   statement hashing, and all reduction losses. Generic quantum collision search
   on an ideal n-bit hash costs roughly 2^(n/3) queries: 384-bit outputs reach
   the nominal 128-bit collision-work threshold before losses. Consider 512-bit
   outputs as an initial candidate, not as a security certificate. Neither this
   estimate nor concatenating domain-separated SHA-256 outputs establishes the
   security of the actual construction. Collision and fixed-target preimage
   requirements must be distinguished.
5. Calculate serialized size using the resulting parameters, then implement and
   measure a small instance. Report proven bounds separately from conjectured
   proximity-testing bounds. Do not reuse classical or 100-bit benchmarks as
   evidence of 128-bit quantum security.

WHIR reports a 63 KiB polynomial-commitment example at 100-bit security. This
motivates investigation but is neither a complete NEAR proof nor a demonstration
of our quantum-security target. The source relation also retains NEAR's SHA-256
roots and Ed25519 signature checks: changing the proof system does not upgrade
the underlying chain's authentication against quantum attacks.

Sources:

- [WHIR](https://eprint.iacr.org/2024/1586): low-query hash-based commitments and a polynomial-IOP compiler.
- [On Soundness Notions for Interactive Oracle Proofs](https://eprint.iacr.org/2023/1256): quantum Fiat–Shamir soundness under specified conditions; distinguishes soundness from knowledge soundness.
- [A Note on the Quantum Collision and Set Equality Problems](https://arxiv.org/abs/1312.1027): tight generic quantum collision query complexity for random functions.
- [On the Concrete Security of Non-interactive FRI](https://eprint.iacr.org/2024/1161): concrete non-interactive bounds and the gap between proven and conjectured parameters.

## Architecture

The outer guest reads the inner proof privately and runs the inner verifier. Its
public journal binds the exact AIR, public tape and claim by three SHA-256 digests,
preceded by a versioned domain string. The verifier checks a locally pinned guest
image ID and compares the journal against independently supplied expected inputs.
It must not accept an AIR or image ID merely because the prover supplied it.

The experiment reuses eight Rust source modules verbatim through path imports:
`air`, `aux`, `field`, `hash`, `mmcs`, `protocol`, `transcript`, `verifier`. Their
source explicitly describes the Rust verifier as a reference implementation,
outside the Lean soundness argument. Successful execution therefore establishes
implementation feasibility, with the Rust-to-Lean connection still outstanding.

For v3, the required guest is larger:

```
private inputs: hint h, inner proof pi
statement: original claim cb, pinned protocol and public-artifact identity
guest:
  prepared = prep(cb, h) or reject
  verify_inner(prepared, pi) or reject
  commit(original claim and protocol identity)
```

Wrapping only the inner STARK while retaining the clear hint does not meet the
complete-size goal. `NearV3/Assembly/RenderV3Header.lean` bounds honest hints by
1,295,025 bytes. Hashing a hint and publishing its digest does not establish that
the hint was checked: preprocessing and its link to the inner statement must run
inside the guest. Public data needed by other validators remains a separate data
availability obligation; hiding it cannot remove that requirement.

## Security obligations

Two independent gaps must be closed before composing the existing certificate.

1. **Oracle instantiation.** The existing `RomSound` theorem concerns a verifier
   accessing a lazily sampled random oracle. The guest computes concrete SHA-256.
   Proving that concrete computation does not supply a reduction from its accepted
   proofs to the existing oracle-game guarantee.
2. **Knowledge and composition.** Ordinary soundness for the statement
   `exists pi, V_sha256(cb, pi) = accept` is insufficient by itself. Computational
   soundness of the inner argument says it is hard to produce an accepting false
   proof, not that such proofs do not exist. A composition proof needs extraction
   of the inner proof from an outer adversary, or another theorem that provides
   the equivalent reduction. The extractor's running time and oracle/prover query
   budgets must be accounted for.

A prospective bound, only after the reductions are supplied, has the form

```
failure <= outer extraction error
         + inner soundness at the extractor's resource budgets
         + statement-binding collision error
         + any model-emulation error
```

Multiple accepted inner statements, adaptive aggregation and further recursion
require explicit composition losses. Neither summing advertised security bits nor
adding the two protocols' unadjusted error bounds proves this inequality. Guest
execution correctness and its connection to the deployed outer verifier are also
required.

There is also a concrete **security-parameter mismatch**. The pinned
`risc0-zkp` 3.0.5 source (`src/prove/soundness.rs`, pulled by `risc0-zkvm` 3.0.6)
documents an on-chain verifier target of 97 bits of conjectured soundness at
2^20 segment cycles, falling to 95 at 2^24. Its toy-model calculation uses
50 FRI queries at rate 1/4 (`src/lib.rs`), alongside other error terms. These
figures do not certify the exact complete wrapper and do not match our 128-bit
profile with explicit Fiat–Shamir and honest-prover query budgets. The earlier
223 KB benchmark therefore cannot establish size feasibility at equal security.
Increasing query count alone would not close the other error terms or update the
recursion circuit automatically; that would require a separately parameterized
and analyzed implementation.

Three approaches deserve separate treatment:

| Approach | Guarantee to develop | Status |
|---|---|---|
| Concrete-hash composition profile | Explicit computational/extractability assumptions for the pinned inner and outer implementations | Practical research candidate; new assumptions |
| Arithmetized random oracle model | Model, emulator, extraction/composition theorem, concrete instantiation rationale | Foundational research; not a drop-in interpretation of the current ROM |
| Pairing-based SNARK wrapper | Outer knowledge soundness, setup/group assumptions, and the same concrete inner-hash bridge | Smaller final proof; does not eliminate the inner security gap |

The 2022 Chen–Chiesa–Spooner paper establishes results in the **low-degree random
oracle model** and a more general linear-code model. The 2023
Chen–Chiesa–Gur–O'Connor–Spooner paper introduces the **arithmetized random oracle
model**, with a plausible software instantiation and PCD construction. Neither
paper certifies this RISC Zero wrapper or gives an automatic SHA-256 composition
theorem. This corrects the earlier requirements document's loose attribution of
AROM to the 2022 paper.

Sources:

- [On Succinct Non-Interactive Arguments in Relativized Worlds, EUROCRYPT 2022](https://iacr.org/archive/eurocrypt2022/132760105/132760105.pdf).
- [Proof-Carrying Data From Arithmetized Random Oracles, EUROCRYPT 2023](https://eprint.iacr.org/2023/587).
- [RISC Zero proof system overview](https://dev.risczero.com/proof-system/): succinct receipts aggregate segment proofs through the recursion circuit; Groth16 is a further wrapper.
- Local contract: `docs/requirements/RECURSION_REQUIREMENTS.md`, sections 1–3;
  implementation: `formal-core/ArenaCore/Admission.lean` and
  `zk-formal/ZkFormal/V3/Hint.lean`.

## Experiment and acceptance criteria

Harness: `tools/recursion/compress/`. The installed local `r0vm` 3.0.6 subprocess
is selected explicitly; fake
receipts are rejected. Builds and executions use the existing `heavy` cgroup
wrapper, 16 GiB memory and CPUs 8–15,24–31. Guest sessions default to a 256 × 2^20
cycle cap; the execution-only follow-up sets `COMPRESSION_MAX_CYCLES=4294967296`.
The guest uses the RISC Zero SHA-256 patched crate; its hash
outputs must match the native implementation on accepted fixture proofs.

Measure native verification, guest execution cycles, segment count, outer proving
time, peak RSS, receipt bytes including its journal, and outer verification time.
Keep the receipt, input hashes, image ID, lockfiles and raw logs. A success claim
requires a real `Succinct` receipt, successful verification in a separate process,
and fewer than 300,000 serialized receipt bytes. The AIR/public artifacts are
preinstalled verifier context; claim transport is reported separately. No clear
inner proof or hint may be needed for outer verification.

Validation ladder:

1. Native versus guest acceptance for a small protocol fixture.
2. An inner proof already larger than 300 KB, then a NEAR v1 proof.
3. Actual recursive proving and independent receipt verification.
4. Reject corrupted inner proof, changed claim and changed public tape inside the
   guest; reject changed outer seal, journal, expected statement and image ID.
5. Extend to the complete v3 preprocessing-plus-verification path when available.

The 223 KB RISC Zero receipt in `checker-recommendations.md` is prior SHA workload
evidence only. It is not a new measurement for this wrapper. Current run results
are recorded below as they become available.

## Measured execution results

The unchanged verifier accepts all three inputs natively and inside the guest.
The outer journal matches the independent host calculation. Results are in
`tools/recursion/compress/results/2026-10-14/`, with input hashes, pinned image ID,
source/dependency identities, commands and logs.

| Fixture | Inner proof bytes | Guest user cycles | Padded cycles | Segments | Execution wall time |
|---|---:|---:|---:|---:|---:|
| Fresh two-table protocol fixture | 73,942 | 29,583,270 | 31,981,568 | 31 | 0.554 s |
| Synthetic segment with widths 150,16,16,16 | 844,173 | 304,434,317 | 328,466,432 | 314 | 6.693 s |
| Existing NEAR v1 transfer fixture | 3,468,847 | 1,450,726,224 | 1,572,339,712 | 1,500 | 33.131 s |

These are **execution timings, not proving timings**. Native reference verification
took 1.53 ms, 30.4 ms and 127.8 ms respectively in these contended runs. The larger
two initially exceeded the 268,435,456-cycle budget; the follow-up changed only the
execution ceiling, not guest code or security parameters. Those initial failures
are recorded as `CYCLE_LIMIT`, not invalid proofs.

The fresh small proof also passed the existing compiled Lean verifier (reported
705 ms). That binary used prebuilt dependencies; this is differential acceptance
evidence, not a clean certificate rebuild. The auxiliary NEAR check with that old
binary was stopped after over six minutes without a verdict.

Three changed inputs were rejected both natively and inside the guest: a flipped
inner-proof byte (`opening 2`), a changed claim and a changed public tape (both
`parse (openings)`). The guest failures came from verification, not resource caps.

Actual local recursive proving of the fresh 73,942-byte fixture was stopped by
the **600-second wall-time limit**, exit 124, with peak RSS **9,607,296 KiB**
(about 9.16 GiB). It used 3,796.08 CPU user seconds and produced no receipt.
The run used eight Rayon threads on a contended host; some of it overlapped the
initial build. This is a bounded cost result, not a proof of an intrinsic runtime
lower bound. Log: `results/2026-10-14/tiny-prove-timeout.log`.

Consequently, this experiment establishes native/guest compatibility and input
rejection, **not a sub-300 KB compressed NEAR proof**. The four outer-receipt
mutation checks are implemented but remain unexecuted because no new receipt
was produced. GPU proving and complete v3 preprocessing are also unmeasured.

## Next experiment

The first formal research milestone now lives in
`research/hash-recursion/` (Lean 4.34.1, Std only). It proves a logical wrapper
counterexample, conditional extraction-event inclusion, exact error-budget
allocation and reduction-loss arithmetic, and wire-size exclusions. In
particular, 216 unshared depth-22 Merkle paths with 64-byte digests alone exceed
300,000 bytes. These are foundational results, not a QROM security proof or a
new compression scheme. The package README records the missing quantum model,
protocol soundness, Fiat–Shamir and extraction reductions, and serializer bridge.

The follow-up adds coherent XOR-oracle semantics over generic amplitudes, proves
pairing/trace preservation and reversibility, and separates input dephasing from
coherent access. Finite-measure lemmas now supply the conditional extraction
union bound without requiring rational probabilities. An exact two-qubit density
example checks preserved coherence and shows that trace alone is insufficient.
`python3 research/hash-recursion/check.py` checks all 33 public theorem axiom
closures and the examples. Random-oracle sampling, complex-state positivity,
general adversary evolution and quantum extraction remain unformalized.

Following the post-quantum direction above, prioritize a concrete security and
wire-size model for a dedicated hash-based construction. Identify the exact
quantum composition theorem or state its absence before investing in larger
recursive proving runs. The RISC Zero harness remains a compatibility and cost
baseline; its current security parameters do not meet the updated target.

The following optimization experiments are secondary baseline work:

The current CPU baseline does not justify a larger proving run. Profile the
small guest first, then test a narrowly optimized verifier against the original
Rust and Lean acceptance behavior. Candidate improvements include batch inversion
of extension-field denominators, caching work repeated across FRI queries, and
avoiding dynamic AIR parsing/evaluation for a fixed verifier. These are hypotheses,
not measured hotspots. Preserve all statement bindings and invalid-proof rejection
while measuring cycle changes; source reuse alone no longer suffices once the
verifier implementation changes.

After reducing the cycle count, repeat a real proof with the same resource cap,
then prove the 844 KB and NEAR fixtures. In parallel, choose and analyze a
128-bit-capable outer protocol; the pinned RISC Zero configuration is only a
mechanical baseline. A dedicated recursive verifier or a differently parameterized
outer system may be necessary, but neither has been validated here.

## Decision criteria

Proceed to full v3 integration if an actual wrapped proof meets the wire-size
target and the measured guest cost is acceptable. A small receipt with excessive
proving time justifies optimizing the inner verifier arithmetic or evaluating a
dedicated recursion circuit; it does not establish economical NEAR validation.

Before changing admission, produce a concrete threat-model proposal with the
composition assumptions, security losses, fixed circuit identities and verifier
connection obligations. Research authorization does not itself adopt those
assumptions. No admission theorem is modified by this experiment.
