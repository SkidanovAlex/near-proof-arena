# Recursive compression feasibility and validation

Research reopened on 2026-10-14 at the user's request, with a target of **less than
300,000 bytes for the complete transmitted proof**. This work evaluates recursive
compression; it does not change the frozen challenge, security profile, or the
historical R5 decision. The first implementation experiment wraps the existing v1
Rust reference verifier in RISC Zero 3.0.6. It is not a certificate for the v3
state-transition relation.

## Preferred direction: hash-based post-quantum compression

The user's updated target is a new hash-based scheme with no elliptic-curve
assumptions at any proof layer, aiming for failure probability at most 2^-128
against at most 2^64 quantum hash queries and a complete proof below 300,000 bytes.
This is the recorded U-6 contract in [V3-D3A-STUDY](../zk-formal/V3-D3A-STUDY.md#d-user-decisions-2026-10-14-binding-and-what-they-change),
not a claim of 128-bit quantum attack cost. U-7 requires SHA-384 throughout. These are research targets, not established
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
   failure probability at most 2^-128 under a fixed resource budget. Use the
   recorded U-6 budget above for the current track.
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
   nominal 128-bit collision work before losses. The selected U-7 primitive is
   SHA-384; wider outputs are alternative research profiles, not the selected
   contract. Neither this
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

The active goal now explicitly requires the full 1 Pgas NEAR state transition.
`research/near-compression/` records the scope mismatch with the current
near-chunk-v3 D3α cap and classical profile. It imports actual NearSpecV3
segmentation and proves a hash-linked segment execution theorem with explicit
local-validity and boundary-decoding premises, or a collision on distinct bytes
at a supplied boundary. The follow-up finite-data representation removes the
function-valued backing store into a fixed context using the exact D3 store
adapter. Reconstruction, storage-host preservation and arbitrary segmentation
are proved against the actual interpreter. Eight hundred sixty-one public theorem axiom
closures are checked. The finite-data codec lifting theorem discharges full-state
reconstruction once a finite byte codec is supplied. The finite state payload
codec is now checked up to logical map equivalence. The whole-result codec is
integrated with actual run composition under explicit representability and
fixed-backing-store premises.
The map representation now follows observational equivalence: entry-list
reconstruction preserves accounting, recording and the actual storage read,
has-key and write/remove accounting operations, including error paths. Host result installation, overlay/write-log updates and sequential host
composition are now proved to preserve this relation, including error states.
The storage results now apply to arbitrary related stores, so updated maps from
prior operations can be used in continuation proofs. Direct real-store reads,
membership checks and the receipt proof-size observation also preserve the
relation, including their errors. Gas charging and the actual memory/register
read helpers now preserve it as well, including charge-before-bounds-check
ordering. The actual memory-write loop and register-write helper now preserve
it too, including optional charging and full-register-file replacement rejection.
Argument popping and return pushes now compose into a proof of the complete
`storage_has_key` dispatch branch, definitionally connected to `hostCall` and
covering real/mock storage and error paths. The complete `storage_read` branch
is also proved and definitionally connected, including its large-value surcharge,
register output and failure ordering. The complete `storage_write` and
`storage_remove` dispatch branches are now proved too, including mutable overlays,
write logs, recorder growth, storage-usage accounting and failure states. All four
core storage branches have definitional correspondence to actual dispatch code.
Observational segment/run composition and hash-link reduction now permit decoded
map representations to differ physically, provided they preserve the state
relation. The theorem exposes collisions on distinct bytes at checked boundaries,
retaining explicit whole-step simulation, local validity and codec premises.
Control-flow helpers, bulk memory copy/init and gas sync/charging now preserve
the relation. The step dispatcher is connected conditionally to instruction-body
simulation. The four core storage calls now include their surrounding VM gas
hooks, domain gate and error classification. Function entry is proved, including
stack and gas failures. Dispatch and actual direct/indirect call instructions
are proved conditional on simulation of the prepared program's imports; table
bounds, null entries and type errors are included. The actual integer numeric
executor and numeric instruction dispatch now preserve map equivalence, retaining
arithmetic traps and unsupported-opcode errors. Another grouped theorem covers
23 stack/control constructors, including structured control, branches, locals,
globals, references, drop/select and constants. Its coverage predicate is explicit
and does not narrow the challenge. Table access/growth, memory size/growth,
element/data drops and integer loads are now proved too, including bounds
failures and the existing sign extension. The float constructor only preserves
out-of-domain rejection, not floating-point execution. Stores, all bulk-memory
and bulk-table instructions are now proved. An exhaustive instruction theorem
and the step dispatcher reduce whole-step preservation to the prepared program's
imported-host simulation. All four hash hosts now preserve the relation with exact dispatch correspondence,
including RIPEMD block-count charges. Fifteen context hosts are now covered as well, preserving input
register charging and post-base-charge used gas. An executable check for these
65 host names (including register, balance/deposit, return, logging, panic, abort, Ed25519, promise-result/return and batch-create/then, promise-join, transfer-action and both function-call action dispatches and promise-create/then plus deploy-contract/create-account and full-access-key/delete-key/function-call-key and stake, refund-routing, delete-account and ordinary/explicit-ID yield-create, resume, gas, deprecated-iterator, validator-query, current-contract and explicit-ID yield-resume dispatches) discharges imported-host and whole-step preservation in an
instantiated run/hash-collision theorem. This is a sufficient coverage check,
not a new challenge restriction or a quantum hash-security theorem. Remaining
host coverage and byte encoding are still unfinished. This is not quantum extraction, full coverage or a
compressed proof. Authenticated memory and context commitments remain required.

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

Real-backend gate follow-up: `RealHostGate.lean` proves exact early rejection
for the ten gated names and direct-call preservation using a separate 75-name
wrapper check. It does not extend supported protocol semantics. `RealInstruction.lean` now proves indirect-call, exhaustive instruction and
one-step preservation under this checker. Whole-run integration and the
real-backend persistence invariant remain open.

`BackendPersistence.lean` supplies the separate backend-presence invariant for
synchronization, charging, entry, return, branches and result composition. The
backing-store invariant permits absent backends and cannot replace this proof.
Host and exhaustive instruction persistence remain open before full-run lifting.

`HostPersistence.lean` adds error-inclusive host composition and real-store/gas
persistence, plus conditional lifting through VM host/function-call wrappers.
Full imported-host persistence is still an explicit premise.

`HostDataPersistence.lean` covers argument loops, stack argument/results,
charged memory/register access and memory-or-register selection, including
errors. Full host-dispatch persistence remains to be composed.

`PromisePersistence.lean` covers receipt/promise mutations, fees, balances,
subsidies and account reads, including error states. Complete persistence is
also proved for full-access-key addition and key deletion; other dispatches
still require composition.

`FunctionPersistence.lean` proves real-backend persistence through U128 access
and the complete function-call action, including both weighted/unweighted
dispatches. `PromiseCallPersistence.lean` now composes promise-create/then and their
batch counterparts, including intermediate failures. Other dispatches remain.

`ActionPersistence.lean` proves backend persistence for complete deployment,
account-creation, staking and transfer dispatches, including error states.
Other dispatch persistence and whole-run lifting remain open.

`AccountPersistence.lean` adds backend persistence for refund routing, account
deletion and restricted access-key action construction, including validation
and fee failures. This does not establish later receipt application.

`PromiseObservationPersistence.lean` now proves real-backend persistence for
promise results, receipt returns, and dependency joins, including invalid-index,
joint-return, overflow and dependency-limit errors. The full bridge audit passes
501 public theorem axiom checks. Whole-run persistence and the quantum security,
full-state proof construction and sub-300,000-byte target remain open.

`ContextPersistence.lean` extends backend persistence to 15 context getters,
three register operations and four hash hosts, with actual dispatcher
correspondence. All 513 bridge theorem axiom checks pass. These execution
properties introduce no hash-security assumption and do not establish quantum
soundness; remaining host persistence and whole-run integration are still open.

`OutputPersistence.lean` adds error-inclusive backend persistence for balance
and deposit outputs, value returns, Ed25519 execution and validator stake queries.
The full audit passes 528 bridge theorem axiom checks. This is execution-level
integration work, not quantum security for Ed25519 or a complete compressed
state-transition proof. Whole-run persistence remains unfinished.

Backend persistence now includes contract-code queries, legacy gas/iterator
behavior and ordinary yield resumption, with both real-store lookups and the
marker write. The full audit passes 540 bridge theorem axiom checks. Remaining
raw host families are storage, logging/panic/abort and the three other yield
calls; whole-run lifting is not yet complete. No proof-size or quantum-security
result follows from this persistence audit.

`YieldCreationPersistence.lean` closes real-backend persistence for the remaining
three yield dispatches: ordinary creation, explicit-ID creation and explicit-ID
resumption. Duplicate detection, captured-state restoration, ordered index writes
and malformed-ID/action failures are covered. The full audit passes 555 public
bridge theorem axiom checks. Remaining raw-host persistence is storage plus
logging/panic/abort, followed by instruction and whole-run integration. These
results do not establish full 1 Pgas coverage or quantum proof security.

`LogPersistence.lean` closes logging/panic/abort backend persistence, including
UTF-8 and UTF-16 bounded scans, decoder failures and log-counter mutation before
limit errors. The full audit passes 584 bridge theorem axiom checks. Only the
four storage calls remain for raw-host persistence; instruction and whole-run
lifting remain separate obligations. This does not establish quantum soundness,
full 1 Pgas coverage, or the target transmitted proof size.

`StoragePersistence.lean` closes the four storage dispatches, including trie gas
failures, recording limits, mutations and evicted-value outputs.
`PersistenceCoverage.lean` proves `proved_host_keeps_real` for the entire existing
65-name ungated list; the full bridge audit passes 605 public theorem axiom
checks. This replaces an informal collection of host lemmas with one checked
coverage certificate. Real-gated wrapper rejection, instruction persistence and
whole-run lifting remain to be integrated. Full semantic coverage and concrete
quantum security/size targets remain unproved.

`CallPersistence.lean` now covers all 75 real-wrapper names, function dispatch
and direct/indirect calls. Gated hosts retain their rejection behavior.
`NumericPersistence.lean` covers successful numeric execution and numeric
instruction trap results. All 612 bridge theorem axiom checks pass. Other
instruction families and whole-run persistence remain unfinished; no full-scope
or quantum-security completion is implied.

`DataInstructionPersistence.lean` closes stack/control, memory/table access and
growth, segment-drop and load persistence, including bounds failures and existing
float rejection. All 615 public bridge theorem axiom checks pass. Stores and
bulk memory/table operations remain before step and whole-run lifting; full
semantic coverage, concrete quantum security and small-proof targets remain open.

`BulkPersistence.lean` proves backend persistence through stores, memory copy,
fill/initialization, and bulk table fill/copy/initialization. Exact byte-loop
invariants retain the real field, with original bounds failures preserved. The
full audit passes 625 public bridge theorem axiom checks. Instruction-family
aggregation, step lifting and whole-run integration remain; neither full-scope
coverage nor quantum security or proof-size completion is established.

`RunPersistence.lean` now aggregates all instruction families, proves real-backend
presence through steps and arbitrary fuel-bounded runs, and lifts map
representation equivalence to whole real-backed runs. The import-check premise
covers the existing 75-name wrapper list, including exact gated rejection.
All 630 public bridge theorem axiom checks pass. This closes the previously open
whole-run persistence/simulation obligation; authenticated segment-boundary
integration and byte encoding remain, as do full protocol coverage, quantum
soundness and measured sub-300,000-byte compression.

`RealSegments.lean` now proves checked real-run composition or a collision on
actual distinct encoded boundary bytes. Real-backend presence is propagated
through local execution and observationally equivalent links, with no separate
real-state assumption for every witness. All 638 bridge theorem axiom checks
pass. Concrete codec correctness and local cryptographic proof soundness remain
premises; this deterministic theorem does not provide quantum extraction,
full protocol coverage or measured small-proof compression.

`BoundaryWire.lean` adds an executable versioned result envelope with explicit
length bounds, distinct terminal tags, round-trip/injectivity proofs and strict
suffix rejection. Four kernel examples cover malformed domain/tag/truncation.
All 644 bridge theorem axiom checks pass. State payloads remain opaque bytes;
full state-field serialization and context binding are still required before
this can discharge the composition theorem's codec premise.

`ValueWire.lean` begins concrete state payloads with actual VM values, stack
arrays and promise references. Round-trip proofs preserve integer/reference and
receipt/joint tags and dependency order; injectivity is proved for values and
promises. The audit passes 649 public theorem axiom checks. Reference-index and
collection bounds are explicit codec premises, not proved reachable-state bounds
or changes to challenge scope. Remaining fields and context binding are open.

`FrameWire.lean` and `GasWire.lean` add concrete round-trip codecs for labels,
frames/frame lists and the complete gas record. Frame and gas encodings are
injective under explicit field/collection bounds. All 656 public bridge theorem
axiom checks pass. Remaining state fields, reachable-state bounds, context
binding and the full observational decoder theorem are still open.

`CollectionWire.lean` adds a reusable array round-trip theorem and concrete
byte-array collections, reference tables, element segments and registers.
The audit passes 664 public theorem axiom checks. These preserve contents,
order and multiplicity under explicit bounds; they do not establish a compact
memory commitment, full state serialization or transmitted proof size.

`StorageWire.lean` adds concrete optional-value, storage-entry, trie-array and
ordered-write-log codecs, using proved option and pair composition. Deletion
cannot alias an empty stored value, and write logs are injectively encoded on
the explicit well-formed domain. All 673 public theorem axiom checks pass.
Logical-map reconstruction and backing-store authentication remain open.

`MapWire.lean` connects encoded entries to logical HashMap reconstruction;
equal encodings imply equivalent lookups, without claiming canonical bucket
ordering. `AccountingWire.lean` covers caches/recorders and their counters up to
normalization. All 683 public theorem axiom checks pass. Immutable-store context
binding and complete state decoding remain open, alongside quantum soundness
and measured compressed-proof targets.

`RealStoreWire.lean` now serializes all finite real-store boundary fields and
proves normalized decoding, restored-store equivalence and encoding-alias
soundness under one fixed immutable backing store. Optional boundaries preserve
their presence tag through normalization. All 688 public theorem axiom checks
pass. Authenticating the immutable store, full state decoding and concrete
quantum compression/security remain open.

UTF-8 strings, promise outcomes and the complete CallCtx now have concrete
round-trip codecs; the context encoding is injective under explicit bounds.
The full audit passes 696 theorem axiom checks. Larger context elaboration uses
a finite module-local heartbeat budget without changing proof assumptions.
Context authentication, remaining state fields and full boundary reconstruction
remain open, as do quantum security and measured sub-300,000-byte compression.


`ActionWire.lean` and `StateWire.lean` now pass the full bounded audit: 705
public theorem axiom closures and boundary regressions. Action logs and optional
returns round-trip, and all 24 finite state fields decode with only logical
HashMap normalization. Restoring the decoded state under the same immutable
backing store preserves StateEquivalent. The failed restoration lemma was
repaired by explicitly rewriting the optional real-backend case; no axiom or
semantic definition was changed. Log: `/tmp/near-state-wire-repair-audit.log`.
The state proof uses a finite module-local budget of 8,000,000 heartbeats.

This is a full finite-state payload codec under explicit representability bounds,
not yet a complete result-envelope decoder or authenticated continuation scheme.
Bounds for all reachable states, external-context binding, AIR validity, full
1 Pgas coverage, quantum recursive security and measured sub-300,000-byte proofs
remain open.


`ResultWire.lean` now supplies the versioned whole-result codec, preserving
continuation, finish, abort and unmodeled tags and exact error strings. Its strict
decoder rejects appended outer bytes and requires complete payload consumption.
Round trips preserve ResultEquivalent under one fixed backing store. The concrete
`encoded_real_run_or_hash_collision` theorem replaces the generic decoding
premise with this implementation, retaining explicit boundary representability,
backing invariants, local execution validity and checked-wrapper scope.

The full audit passes 714 theorem axiom checks (log:
`/tmp/near-result-wire-audit.log`). This completes codec integration for the
existing semantic bridge, not full NEAR coverage or a cryptographic recursion
construction. Reachability bounds, context authentication, authenticated memory,
AIR validity, quantum security and measured proof size remain open.


`BackedWire.lean` connects concrete wire composition to the existing actual
segment backing-preservation theorem. Finite starts and public endpoints are
restored under the same supplied context; locally valid segment execution derives
the backing invariant for each finish. The resulting
`finite_start_wire_run_or_hash_collision` needs encoding bounds and local
execution validity, but no independent intermediate-finish backing assumption
or abstract decoder. The full audit passes 718 theorem axiom checks; log:
`/tmp/near-backed-wire-audit.log`.

This is a reduction in semantic premises, not authentication of the context or
verification of local execution by an AIR. Full scope, reachability/encoding
bounds, authenticated memory, quantum security and measured small proofs remain
unfinished.


`PageCommitment.lean` connects domain-tagged page commitments to the actual Wasm
`readByte` and `writeByte` functions. An opening matching the honest page-digest
directory yields the actual page/read or a collision between distinct supplied
page encodings. Writes preserve non-target directory entries and compute the
target digest from the modified page. Five new theorems pass the full 723-theorem
audit; log: `/tmp/near-page-commitment-audit.log`.

The inspected `ZkFormal.Bcs.Merkle` extraction theorem depends on recorded oracle
history, collision and inversion conditions; it is not imported here as a quantum
extraction result. The new directory is an honest reference, not yet an
authenticated root. Directory authentication, access proofs, bulk/grow integration,
full-state replacement and quantum composition remain required. No proof-size
or prover-speed measurement follows from these lemmas.


`PageTree.lean` adds a binary page commitment and a supplied-opening root
calculation. Length-prefixed child digests have a proved injective node encoding
under their size bounds. The opening theorem yields the actual page or a
collision explicitly located in the reference tree's messages and the supplied
opening's messages, assuming the path selects that page. Its hash-message count
is path length plus one. The full audit passes 726 theorem checks; log:
`/tmp/near-page-tree-audit.log`.

The path/shape correspondence is a premise, not yet derived from a canonical
balanced representation of `St.pages`. Directory construction, index/shape
binding, update proofs, boundary integration and quantum extraction/security
remain open. No compact proof or execution-cost benchmark is claimed.


`IndexedPageTree.lean` constructs balanced trees from actual page arrays and
proves numeric-index lookup correspondence at any supplied sufficient depth.
The indexed opening theorem uses that result to remove the previous arbitrary
path-to-page correspondence premise; it retains allocated-index, capacity and
encoding bounds. The executable opening generator produces the derived direction
sequence and reconstructs the root for an in-range page. The full audit passes
733 theorem axiom checks; log: `/tmp/near-indexed-page-audit.log`.

Page count/depth binding is still required because the builder pads with empty
bytes. Incremental updates, memory growth/bulk operations, boundary integration,
full 1 Pgas scope and quantum security/size evidence remain unfinished.


`MemoryDescriptor.lean` binds page count, depth and root with a domain-separated,
length-delimited encoding. A kernel-checked example shows why the bare tree root
is insufficient: empty allocation and one empty page share a depth-zero root.
The descriptor has a proved injective codec under bounds. Combining descriptor
binding with indexed openings now proves actual byte-read correctness or a
collision in the compared metadata/tree/opening messages. `checkMemoryPage`
implements the count/capacity/direction/root checks and has a proved equivalence
to the acceptance predicate. The full audit passes 740 theorem axiom checks;
log: `/tmp/near-memory-descriptor-audit.log`.

The enclosing commitment must still authenticate this descriptor alongside all
other state fields. Bounded operational parameters, update/grow/bulk proofs,
AIR integration, full 1 Pgas semantics, quantum security and measured small-proof
performance remain open.


`PageTreeUpdate.lean` proves subtree extensionality and preservation outside a
modified page index, then shows path-based leaf replacement equals rebuilding
from the actual modified array. The specialized `write_byte_root_from_opening`
proves that an honest original sibling path, reused with the modified page,
computes the root of NEAR's actual `writeByte` output. The full audit passes 747
theorem axiom checks; log: `/tmp/near-page-update-audit.log`.

These results justify an incremental root calculation, not yet an untrusted
update verifier or measured fast implementation. The reference generator can
rebuild sibling subtrees and full-page hashing remains work. Untrusted-path
binding, bulk/grow operations, boundary integration, full scope, quantum security
and proof-size/time measurements remain unfinished.


`UntrustedPageUpdate.lean` closes the supplied-path update reduction. An accepted
old root binds the original page and replacement root, or exposes a collision in
reference-tree and opening messages. The theorem is specialized to actual
`writeByte`. `checkedMemoryByteWrite` performs the executable count/capacity/path/
root check and returns an updated descriptor. Under the stated metadata
commitment and encoding bounds, its successful result is the actual post-write
descriptor or a collision in the compared messages. The full audit passes 750
theorem axiom checks; log: `/tmp/near-untrusted-page-update-audit.log`.

This does not yet cover whole-state commitment linkage, bulk/grow operations,
gas/failure behavior of complete instructions, AIR validity, quantum extraction,
full 1 Pgas scope or measured compression performance.


`MemoryWriteChain.lean` lifts checked byte updates to sequences. It proves page
bounds survive `ByteArray.set!` and actual `writeByte`, and derives descriptor
bounds from the unchanged allocation count/depth and bounded hash output. The
executable sequence checker threads each resulting descriptor into the next
access. Starting from the actual initial descriptor, successful verification
returns the descriptor of the sequential actual byte-write state or a collision
localized to one of the sequence's compared messages. Witness page/path bounds
remain explicit. Full audit: 754 theorem axiom checks; log:
`/tmp/near-memory-chain-audit.log`.

The sequence still needs a bridge to actual `writeBytes`/`writeLE` and bulk
instruction traces, plus whole-state commitment linkage. No additional protocol
coverage, quantum security or proof-size/performance result follows yet.


`WriteBytesBridge.lean` connects the actual dependent-index `writeBytes` loop to
ordered address/value requests without changing the interpreter. The witness
executor is proved equivalent when its projected requests match, and the
executable `checkWriteBytes` enforces that equality before checking the write
chain. Its successful output is the actual post-`writeBytes` descriptor or a
collision in the checked sequence. The full audit passes 759 theorem axiom
checks; log: `/tmp/near-write-bytes-audit.log`.

The theorem retains initial descriptor/bounds premises. It is not a completeness
claim for out-of-range helper calls, nor proof of surrounding host gas/error
semantics. Full-page witnesses remain expensive; batching, full-state/AIR
integration, full 1 Pgas scope, quantum security and measured compact proofs
remain open.


`PageBatch.lean` proves same-page ordered updates agree with the actual byte-write
request sequence, including repeated offsets. The executable checker validates
all offsets, authenticates one initial page/path, applies the updates locally,
and computes one final root. Its output equals the actual final memory descriptor
or yields a collision in the tree/opening messages. The full audit passes 765
theorem axiom checks; log: `/tmp/near-page-batch-audit.log`.

This is structural amortization of page authentication, not a measured prover
speedup or succinct-proof-size result. The checker begins from the actual
initial descriptor in its theorem. Multi-page composition, automatic grouping
of `writeBytes`, host observation/gas integration, full transition scope and
quantum proof security remain unfinished.


`PageBatchChain.lean` connects ordered page batches to actual `writeBytes` across
page boundaries. The checker threads updated descriptors and enforces exact
flattened address/value equality with the original operation. Accepted output
is the actual final memory descriptor or a collision localized to a batch;
intermediate page bounds follow from execution. The full audit passes 769
theorem axiom checks; log: `/tmp/near-page-batch-chain-audit.log`.

Lean wrapped the longest theorem's axiom report across lines. `check.py` now
parses complete multiline reports, retaining exact theorem coverage and the
same three-axiom allowlist. Synthetic multiline `sorryAx`, custom-axiom and
truncated-report cases were checked. No formal obligation was relaxed.

Batch grouping is supplied and checked, not yet generated by a proved maximal
constructor. This does not establish measured compression, a metered host/VM
trace, full 1 Pgas coverage or quantum recursive security.


The SHA-512 memory-batching microbenchmark is now measured, separately from the
Lean audit and succinct-proof target. For a 4 KiB same-page write, per-byte versus
batched checking used 65,536 versus 16 hash calls, processed 545,816,576 versus
133,256 hash-input bytes, and took approximately 397 ms versus 0.525 ms in one
shared-host run. Proposed witness transport dropped from 270,516,224 to 86,519
bytes. A sparse one-byte access still needs 66,044 bytes, while a batched 1 MiB
write across 17 pages uses 6,365,543 witness bytes with explicit update records.
These figures motivate finer-grained leaves for sparse access; they do not
measure or bound the final recursive proof size.

Artifact: `research/near-compression/results/memory-batch-sha512.json`; harness:
`research/near-compression/memory_batch_bench.py`. Both modes matched independent
flat-memory updates and a bottom-up root rebuild. Ten negative cases, including
stale openings and reordered/duplicate writes, were rejected. Initial metadata
is trusted in this experiment; tree construction and grouping are excluded from
timings. This Python implementation has no Lean refinement proof, and native
SHA-512 performance establishes neither AIR cost nor quantum security.


The leaf-size sweep now measures 256 B, 1 KiB, 4 KiB and 64 KiB blocks over the
same 8 MiB memory and identical request streams, three repetitions each. For 16
sparse writes, proposed witness bytes are respectively 21,056; 31,136; 78,080;
and 1,056,704. For a dense 64 KiB write, verifier hash calls are 8,192; 1,792;
384; and 16. This demonstrates a sparse-access versus dense-write tradeoff, not
one universally optimal leaf size. Retain 1 KiB and 4 KiB as candidates pending
actual VM access traces and AIR hash-cost measurements.

All 60 runs matched direct memory updates and independent root rebuilds; 40
mutation checks were rejected across layouts. Artifact:
`research/near-compression/results/memory-leaf-sweep-sha512.json`; harness:
`research/near-compression/memory_leaf_sweep.py`. Block size is domain-bound and
the domains differ from the formal page scheme. These layouts still need a
subpage-to-Wasm refinement proof and integration. Transport includes explicit
write records; native timings exclude request grouping and construction (the
latter measured separately). No succinct-proof-size or quantum-security result
is implied.


`SubpageRead.lean` proves a parameterized subpage read refinement against actual
Wasm memory. Positive block sizes satisfying `block * count = pageSize` select
an in-bounds slice of a full-sized page; that slice has exactly the block size,
and its local byte is the interpreter's `readByte` result. The page's presence
and full size remain explicit premises. Candidate 1 KiB and 4 KiB layouts have
kernel-checked arithmetic examples. Full audit: 774 theorem axiom checks; log:
`/tmp/near-subpage-read-audit.log`.

This connects byte reads, not the experimental block commitment protocol as a
whole. Subpage update refinement, global indexing, reachable-page invariants,
commitment/boundary integration and the full quantum-secure compression target
remain unfinished.


`SubpageWrite.lean` now proves bounded slice/write commutation, preservation of
slices outside the written byte, parameterized subpage update refinement, and
the connection to actual `writeByte` page lookup. Existing allocation semantics
are unchanged; presence of a full-sized page and a valid block partition remain
explicit premises. The full audit passes 778 theorem axiom checks; log:
`/tmp/near-subpage-write-audit.log`.

Global block indexing, commitment-tree and boundary integration, reachable-page
invariants, full 1 Pgas semantics and quantum-secure small-proof evidence remain
unfinished. These lemmas do not certify the exploratory Python block protocol.


`SubpageIndex.lean` proves global block/page/byte index correspondence and
constructs a finite directory from actual Wasm pages. Allocated byte addresses
select allocated blocks, directory reads equal actual `readByte`, and the target
block after `writeByte` equals the local subpage update. The full audit passes
788 theorem axiom checks; log: `/tmp/near-subpage-index-audit.log`.

Full-sized-page and valid-layout assumptions remain explicit. Non-target block
preservation and whole-directory update equality, block commitment integration,
full protocol coverage and quantum-secure compact proofs remain unfinished.


`SubpageDirectoryUpdate.lean` proves non-target block preservation and complete
directory update equality against actual `writeByte`. It handles both other
pages and disjoint subpages within the written page. Under the existing valid
layout/full-sized allocated-page premises, the resulting directory is exactly
one `Array.modify` at the global block index. The full audit passes 791 theorem
axiom checks; log: `/tmp/near-subpage-directory-audit.log`.

This closes the data-representation update for one byte, not block commitment
security or full VM execution. Reachable page invariants, block domain/shape
binding, authenticated state integration, full 1 Pgas coverage and the quantum
security/proof-size requirements remain unfinished.


`FullPages.lean` proves full-sized zero-page allocation/append and page-shape
preservation for actual `writeByte`, `writeBytes`, `writeLE`, `memCopy`, `memFill`
and `memInit`, including abort results. It derives page encoding bounds from
full page size. The full audit passes 803 theorem axiom checks; log:
`/tmp/near-full-pages-audit.log`.

The allocation and append expressions match instantiation and successful memory
growth, but a whole-instantiation/whole-instruction/host/run invariant theorem is
not yet supplied. This does not extend restricted challenge coverage or establish
quantum security, full 1 Pgas proving capacity or compact proof size.


`SubpageBounds.lean` derives finite-directory block sizes and byte-encoding bounds
from full pages and a valid layout. `SubpageCommitment.lean` adds a separate
block-size-prefixed hash domain, lifts collisions to explicit underlying hash
messages, and connects accepted block openings to actual Wasm `readByte`.
The full audit passes 810 theorem axiom checks; log:
`/tmp/near-subpage-commitment-audit.log`.

Allocation/layout/depth and full-page assumptions remain explicit; enclosing
metadata binding and block-write commitment integration are unfinished. The
formal domain layout differs from the exploratory Python sweep. This is a
finite-message deterministic binding reduction, not quantum extraction or a
full 1 Pgas/sub-300,000-byte proof result.


`SubpageCommitmentWrite.lean` proves the block tree after actual `writeByte` is
the corresponding leaf replacement, then connects untrusted accepted openings
to that new root or an explicit collision in underlying prefixed hash messages.
The full audit passes 812 theorem axiom checks; log:
`/tmp/near-subpage-commitment-write-audit.log`.

Layout/allocation/depth and full-page premises remain external. Metadata binding,
checked block-operation composition, full-state/AIR integration, full 1 Pgas
coverage and quantum-secure sub-300,000-byte proof evidence remain unfinished.


`BlockDescriptor.lean` now binds the block layout, allocation count, depth and
root in a round-tripping versioned encoding. `AuthenticatedBlockRead.lean` and
`AuthenticatedBlockWrite.lean` combine descriptor binding with the executable
opening check: accepted reads equal actual Wasm bytes, and opening-based updates
equal actual `writeByte` tree roots, or the finite supplied/reference messages
exhibit an underlying hash collision. The full audit passes 818 public theorem
axiom checks; log: `/tmp/near-authenticated-block-write-audit.log`.

These statements retain explicit full-page and representability bounds. The
reference descriptor still needs binding to the full state; checked block-trace
composition, AIR integration, full 1 Pgas coverage, quantum security and measured
sub-300,000-byte proofs remain unfinished. Root-update correctness alone is not
an executable descriptor-threading protocol.


`CheckedBlockWrite.lean` adds an executable optional descriptor update, proved
equal to the descriptor after actual Wasm `writeByte` or a localized hash
collision. `BlockWriteChain.lean` composes accepted updates over an arbitrary
supplied write list and preserves full-page/allocation invariants through actual
execution. The final descriptor equals the actual sequential-write descriptor,
or a step exposes a collision in its finite reference/opening messages. This
closes the descriptor-threading gap recorded above. The full audit passes 821
public theorem axiom checks; log: `/tmp/near-block-write-chain-audit.log`.

Initial full-state authentication, witness well-formedness enforcement in an
end-to-end verifier, bulk-operation integration, AIR constraints, full 1 Pgas
coverage, quantum security and measured compact proofs remain outstanding.


`BlockWriteBytes.lean` connects the descriptor-threaded block checker to the
actual `writeBytes` loop. The executable wrapper checks witness byte/path
encoding bounds and exact ordered address/value equality with the requested
payload; its correctness theorem no longer takes witness well-formedness as an
external premise. A second operational theorem rejects any different request
stream. The full audit passes 824 public theorem axiom checks; log:
`/tmp/near-block-write-bytes-audit.log`.

This is helper-level correctness, not complete host gas/bounds/failure handling.
Per-byte block openings still need batching for efficiency. Initial state
binding, AIR integration, full 1 Pgas coverage, quantum security and measured
sub-300,000-byte proofs remain outstanding.


`BlockBatch.lean` proves whole-directory and tree replacement for an ordered
list of actual Wasm byte writes contained in one allocated block. A single
accepted Merkle opening then computes the actual batch result root, or the
reference/opening messages expose a collision in the underlying hash. Duplicate
offsets retain their write order. The full audit passes 827 public theorem axiom
checks; log: `/tmp/near-block-batch-root-audit.log`.

This establishes the semantic basis for sharing one path across a block batch.
The batch theorem still takes layout/allocation/capacity and witness bounds as
premises; the executable descriptor-bound batch checker and composition across
batches remain outstanding. No measured succinct-proof or quantum security
claim follows, and full-state/AIR integration and full 1 Pgas coverage remain
unfinished.


`CheckedBlockBatch.lean` now checks layout, capacity, allocation, block size,
witness encoding bounds, offsets, path directions and root agreement before
returning the updated descriptor. Its correctness theorem derives those
conditions from executable acceptance and proves agreement with actual ordered
Wasm byte writes, or an underlying hash collision. A supporting theorem proves
that arbitrary byte-request lists preserve the allocated page count. The full
audit passes 829 public theorem axiom checks; log:
`/tmp/near-checked-block-batch-audit.log`.

The initial descriptor still requires full-state authentication; full-page
invariants remain a premise. Batch-sequence and `writeBytes` integration, AIR
constraints, full 1 Pgas coverage, quantum security and measured succinct proof
size remain unfinished. This is a single-opening batch checker, not yet the
end-to-end compressed transition verifier.


`BlockBatchChain.lean` composes descriptor updates across supplied block batches
and provides `checkBlockBatchedWriteBytes`. Exact equality of the flattened
address/value stream binds the batches to the requested byte payload; a separate
rejection theorem covers any mismatch. Accepted output descriptors agree with
actual `writeBytes`, or a checked batch exposes a localized hash collision. The
full audit passes 833 public theorem axiom checks; log:
`/tmp/near-block-batch-chain-audit.log`.

This closes batch composition and helper-level payload integration. Initial
state authentication and full-page invariants remain premises. Honest witness
generation/completeness, formal-checker performance measurements, host gas and
failure integration, AIR implementation, full 1 Pgas coverage, quantum security
and measured compact proofs remain outstanding.


`HonestBlockBatch.lean` constructs an honest single-batch witness and proves
unconditional acceptance with the exact descriptor of actual batch execution.
A supporting theorem proves generated Merkle paths satisfy encoding bounds under
the digest-size bound. The full audit passes 835 public theorem axiom checks;
log: `/tmp/near-honest-block-batch-audit.log`.

Completeness requires full pages, valid block layout/capacity, allocated block
and bounded offsets. The reference generator rebuilds trees; no performance
claim is made. Sequence generation, payload grouping, full-state/AIR integration,
full 1 Pgas scope, quantum security and measured compact proofs remain unfinished.


`HonestBlockSequence.lean` extends the honest constructor to arbitrary ordered
batch plans. Each opening is generated from the actual state after previous
writes. Theorems establish exact request-stream preservation and acceptance
with the actual final descriptor, including the `writeBytes` wrapper when a
valid supplied plan equals the payload requests. The full audit passes 838
public theorem axiom checks; log: `/tmp/near-honest-block-sequence-audit.log`.

Automatic payload grouping remains an obligation; the reference generator still
rebuilds trees. Full-state authentication, host gas/failure integration, AIR
constraints, full 1 Pgas coverage, quantum security and measured compact proofs
remain unfinished.


`BlockGrouping.lean` closes automatic payload grouping: consecutive same-block
requests merge while preserving their exact ordered address/value stream.
The grouping validity theorem feeds the honest sequence generator.
`honestWriteBytesWitness` now accepts actual state, layout, address and payload;
its completeness theorem proves exact checker acceptance for in-bounds payloads
under full-page/layout/capacity premises, without a supplied plan. The full audit
passes 843 public theorem axiom checks; log:
`/tmp/near-grouped-write-bytes-audit.log`.

The constructor is still a reference implementation that rebuilds trees per
batch. Compiled execution measurements, full-state/host/AIR integration, full
1 Pgas coverage, quantum-security bounds and measured compact proofs remain
outstanding.


The actual Lean block witness generator/checker is now exercised by
`BlockBatchSmoke.lean` and `run_block_smoke.py`, using `NearSpecV3.sha512` and
64 KiB memory, 4 KiB blocks, depth 4. Across three repetitions, all 12 acceptance
cases passed and 48 mutations were rejected (changed block/sibling, out-of-block
offset, omitted/reordered batches and unallocated memory). The SHA-512 `abc`
digest is checked independently with Python hashlib. Actual `writeBytes` memory
is compared with direct byte replacement, and output roots with full rebuilds.
The root rebuild shares formal tree code and is not an independent tree oracle.

Median interpreter checking times were 42 ms for a 256-byte same-block write,
83 ms for a 32-byte cross-block write, and 47 ms for a dense 4096-byte write.
Corresponding witness-generation medians were 256, 513 and 263 ms; initial
commitments took 277–280 ms. Explicit noinline IO boundaries prevent pure
computations from drifting between timing intervals. Timings exclude startup,
final oracle checks and mutations. These are shared-host `lake env lean --run`
measurements, not compiled-native, AIR or succinct-proof performance.

Results and source hashes: `results/block-checker-lean-smoke.json` (relative to
`research/near-compression`). Reproduce from the repository root with:

```sh
HEAVY_MEM=4G LEAN_NUM_THREADS=2 taskset -c 8 \
  /data/illia/nearproof-deps/bin/heavy python3 research/near-compression/run_block_smoke.py
```

The generator still rebuilds trees per batch. Cached tree updates and larger
representative traces need measurement; full-state/host/AIR integration, full
1 Pgas coverage, quantum security and sub-300,000-byte proofs remain unfinished.

`CachedPageTree.lean` now caches a digest at every subtree. Kernel-checked
correspondence proves cached roots equal reference roots, path replacement equals
caching the reference replacement, and a cached block-batch update equals a
fresh cache of the actual post-write tree. A further theorem proves cached
sibling paths exactly equal `buildPageOpening` on reference indexed trees.
Opening extraction reads cached digests; replacement hashes only the traversed
path. This is structural correspondence, not a measured speedup or a formal
runtime-cost bound. Arbitrary externally supplied cached trees are not trusted;
the correspondence applies to caches built and maintained by these operations.

The cache is not yet wired into the witness sequence generator. The full audit
passes 847 public theorem checks (`/tmp/near-cached-page-opening-audit.log`).

Cached witness-sequence integration and comparative measurements remain next;
full-state/host/AIR integration, full 1 Pgas scope, quantum security and measured
sub-300,000-byte proofs remain unfinished.


`CachedBlockSequence.lean` now generates batch witnesses using only the cached
tree and the plan. It reads each block from the cache, obtains cached sibling
hashes and updates the affected path. The exact-correspondence theorem proves
its entire witness list equals the actual-state reference generator for every
valid plan, including repeated block visits. A completeness theorem then proves
checker acceptance with the actual final memory descriptor. Full-page, valid
layout/capacity and allocated-offset premises remain explicit.

The full audit passes 850 public theorem checks; log:
`/tmp/near-cached-sequence-accepted-audit.log`. Comparative timings have not yet
been measured for this cache implementation; the earlier interpreter results
measure the rebuilding generator. Cached generation still needs the public
payload wrapper, benchmark integration and larger representative workloads.
Full-state/host/AIR integration, full 1 Pgas scope, quantum security and measured
compact proofs remain unfinished.


Cached witness generation is now measured against the reference generator in
`CachedBlockBench.lean`, orchestrated by `run_cached_block_bench.py`. Three
repetitions cover 12 cases / 123 batch witnesses with exact witness-field
parity, equal initial roots, accepted final descriptors equal to full actual-state
rebuilds, and direct-memory update checks. The root oracle shares reference tree
code. Both generators use the same SHA-512 implementation and supplied plan.

| Case | Reference generation ms | Cached generation ms | Reference init + generation ms | Cached init + generation ms |
|---|---:|---:|---:|---:|
| One batch, 64 KiB memory | 256 | 21 | 531 | 297 |
| 16 blocks, 64 KiB memory | 4,127 | 336 | 4,406 | 614 |
| 16 repeated block visits, 64 KiB | 4,136 | 336 | 4,417 | 616 |
| 8 sparse batches, 256 KiB memory | 8,945 | 188 | 10,083 | 1,319 |

These are medians from `lake env lean --run`, on one pinned CPU of a shared
host. Initialization-inclusive generation improves about 1.79x for one batch
and 7.17–7.64x for these multi-batch cases. Sums are medians of per-run totals,
so need not equal sums of column medians. Checking is unchanged: median 42,
675, 675 and 375 ms respectively. Plans are preconstructed; grouping, startup
and final validation are excluded from timings. Reference always runs before
cached; these results are not a broad hardware benchmark, compiled-native cost,
AIR cost, succinct-proof size or quantum-security evidence.

Artifact: `research/near-compression/results/cached-block-lean-bench.json`,
including source hashes. Reproduce from repository root:

```sh
HEAVY_MEM=4G LEAN_NUM_THREADS=2 taskset -c 8 \
  /data/illia/nearproof-deps/bin/heavy python3 research/near-compression/run_cached_block_bench.py
```

The measured improvement supports retaining the cache design. Larger traces,
full-state/host/AIR integration, full 1 Pgas coverage, quantum-security bounds
and measured sub-300,000-byte proofs remain outstanding.


`CachedWriteBytes.lean` now exposes `cachedWriteBytesWitness` for state, layout,
address and payload inputs. Its theorems derive a valid grouped plan from the
in-bounds range, prove exact equality with the reference payload witness and
prove checker acceptance with the actual `writeBytes` descriptor. Full pages,
valid layout and capacity remain premises. The full audit passes 853 public
theorem checks; log: `/tmp/near-cached-write-bytes-audit.log`.

The smoke harness now also compares the cached payload wrapper's complete
witness fields and result against the reference wrapper, outside the timed
intervals. All 12 cases passed and 48 mutations were rejected across three
repetitions. `results/block-checker-lean-smoke.json` has been refreshed with
these checks and source hashes; earlier smoke timing figures describe the
initial run. The cache comparison artifact remains a separate benchmark.

This closes cached payload-wrapper integration. Full host gas/bounds/failure
handling and full-state/AIR integration remain next; full 1 Pgas coverage,
quantum-security bounds and measured compact proofs remain unfinished.


`MemoryHostPhases.lean` proves exact equality between actual `writeMemH` and
an explicit base-charge, per-byte-charge, bounds-check, write decomposition.
Both gas failures retain the charged state; bounds failure retains both charges
without writing memory. The proof covers exact result tags, errors and whole
states, not only memory roots. It also proves full allocated pages survive the
actual host helper on success and failure. Symbolic cost lemmas avoid expanding
large concrete protocol costs during proof elaboration.

The full audit passes 857 public theorem checks; log:
`/tmp/near-memory-host-phases-audit.log`. The host phase model is not yet wired
to the compressed descriptor checker. That integration, full-state/AIR coverage,
full 1 Pgas validation, quantum security and measured compact proofs remain
outstanding.


`CheckedMemoryHost.lean` now connects descriptor checking to actual `writeMemH`.
The executable checker performs exact base and byte gas charges, returns their
errors before bounds checking, retains charged gas on bounds failure, and invokes
the batched memory checker only on success. Its accepted output equals the
actual helper projected to gas, exact success/error status and memory descriptor,
or a checked batch exposes a hash collision. Two supporting theorems prove
byte-request execution and actual `writeBytes` preserve gas.

The theorem starts with the actual gas and memory descriptor; authenticating
those inputs and binding other state fields remains an enclosing-statement
obligation. Failure paths do not consume write witnesses because no memory
write occurs. This is projected host correctness, not whole-state proof-system
soundness. The full audit passes 861 public theorem checks; log:
`/tmp/near-checked-actual-host-audit.log`. Host-checker completeness and executable
failure-case tests, full-state/AIR integration, full 1 Pgas proving, quantum
security and measured compact proofs remain unfinished.


`MemoryHostSmoke.lean` now passes eight actual-host/checker parity cases: success, base-gas failure, byte-gas failure, bounds failure, both gas-before-bounds cases, empty-at-end and empty-past-end. It compares all gas fields, exact status and descriptor, checks unchanged memory on failure and direct memory replacement on success. Burnt and host gas also match independently calculated expected totals. Evidence: `research/near-compression/results/memory-host-lean-smoke.json`. Reproduce with `lake env lean --run MemoryHostSmoke.lean` from the research package (use the bounded wrapper). This is executable helper validation, not full-state or AIR correctness.
