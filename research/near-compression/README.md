# Full NEAR compression: actual-semantics bridge

Active objective: **research compressing a succinct proof for the full NEAR state
transition at 1 Pgas for near-chunk-v3, quantum resistant, with Lean correctness**.
The inherited targets are less than 300,000 proof bytes and 128-bit quantum
security under an explicitly specified resource model. None is relaxed here.

This package imports the actual `NearSpecV3` sources read-only and adds a semantic
bridge for hash-linked execution segments. It is separate from the Std-only
quantum foundations in `../hash-recursion`. No challenge, admission declaration,
security profile or existing semantics is changed.

## Current scope conflict

The checked `NearSpecV3.D3.gAlpha` is **3,450,888,781,824 gas**, well below
1,000,000,000,000,000. The challenge explicitly excludes witnesses above this
function-call gas cap, floating-point Wasm, multiple host/action families and
other behaviors listed in `scope-report.json`. Its profile is classical.
Compressing the current restricted relation is therefore not completion of the
full objective. Research must develop a versioned semantic/security extension;
deployment/admission of that extension is separate work.

`Scope.checkD3Peta` is an executable research definition selecting the existing
checker's 1 Pgas function-call cap. **It retains every other D3 restriction**;
no full-coverage, cap-monotonicity or successful large-workload result is claimed.
It is not registered as a challenge. The ratio to the old cap rounds up to 290,
proved in Lean, but this is not a theorem that 290 traces cover any 1 Pgas chunk.
Gas is charged in blocks, some structural operators have zero cost, host work is
not one trace row, and non-Wasm transition work needs separate resource bounds.

## New checked bridge

The existing `NearSpecV3.Wasm.Segment.run_foldSegments` already proves exact
segmentation. `Segments.lean` reuses it rather than restating an abstract VM.

For supplied witnesses `(steps, start, finish)` and one fixed configuration and
prepared program, the new theorem `certified_run_or_hash_collision` proves:

1. If each local segment really executes from its stated start to finish;
2. if hashes agree at the initial, intermediate and final boundaries; and
3. if the finite boundary encoding decodes back to those actual states;

then the actual `Wasm.run` returns the composed result (with the stated fuel
suffix), **or a checked boundary contains distinct byte strings with equal hash**.

The collision comes from a supplied boundary pair, not from an unrelated
existential collision somewhere in the hash's domain. No global hash injectivity
is assumed. This theorem is deterministic and is not a quantum security theorem
or an efficient quantum witness-extraction algorithm.

The theorem binds whole `Res` objects, including `cont`, `fin`, `abort` and
`unmodeled` tags. Regression examples and `erased_tag_cannot_decode` demonstrate
that omitting the terminal tag cannot satisfy reconstruction. Otherwise a proof
could attempt to resume a returned execution.

## Finite boundary representation and its remaining obligations

`Boundary.lean` now gives a finite data representation of all machine-state
fields. Only the function-valued backing store is moved into a fixed execution
context, using the exact D3 `HStore` lookup adapter. Memory, overlay, gas,
accounting cache, recorder, output and terminal status remain represented.

Kernel-checked reconstruction and preservation theorems show that the finite
runner agrees with the actual interpreter for arbitrary segment lengths,
including storage-host steps and early termination. `different_backing_changes_state`
shows why the context must be bound: identical boundary data can otherwise
represent different executable states.

`finite_certified_run_or_hash_collision` connects this representation to the
original hash-linked execution theorem. Given locally valid segments, fixed
backing context and a round-trip byte codec for finite boundary data, the actual
interpreter returns the linked result or the supplied boundaries expose distinct
byte strings with equal hash. Intermediate output backing invariants follow from
execution preservation; they are not additional unproved assumptions.

The generic composition theorem retains a whole-result decoding premise.
`ResultWire.lean` now instantiates it with a concrete versioned codec, under
explicit representability and fixed-backing-store invariants. `MapBoundary.lean`
now chooses the observational-equivalence route for the three HashMap fields.
Rebuilding a map with `ofList toList` preserves lookups and insertion behavior,
without claiming structural equality of its buckets. A local, proved
`LawfulBEq ByteArray` instance supplies the missing Std precondition without
changing the interpreter's equality operation.

The following actual interpreter operations respect map normalization:

- accounting-cache touches and lists of touches, preserving both counters;
- recording nodes/values, preserving recorded size and membership;
- gas commits, including their order and failure result;
- storage reads, `storage_has_key`, and the shared write/remove accounting path;
- backing-store dereference and the receipt storage-proof limit check.

The storage-operation theorems preserve gas, old values, errors, counters and
recorder size, and relate output maps by logical entries. They cover arbitrary
inputs and failures, including the large-read surcharge and charges that fail
before committing counters. `HostBoundary.lean` now covers the subsequent `realOpH` installation of gas,
accounting and recorder state, on both successful and failing results. It also
covers full-key and prefix-qualified overlay writes (`realPutH`/`realSetH`),
preserving the ordered write log and deletion markers. A host bind theorem
preserves return values, errors and their associated states across sequential
composition.

`StorageEquivalence.lean` generalizes the storage proofs to **arbitrary related
stores**, not only a freshly normalized store and its original. This closes the
composition gap after earlier operations update maps. The general results cover
storage read, write/remove and has-key accounting and their `realOpH` host
installations. They also cover the actual direct `realGetH` and `realHasH` helpers,
missing-node/value errors, the +2000 removal recorder update, and `observeH`'s
receipt storage-proof limit failure. No map-normalization assumption is needed
at these continuation points.

`CoreHost.lean` adds compositional simulation rules, gas updates and the actual
`readMemH`, `regGetH` and `memOrRegH` helpers. Memory reads retain the original
ordering: both charges precede bounds checking. Return bytes, missing-register
errors, memory bounds failures and gas-failure states remain exact. Parameterized
charge sequences are instantiated at the actual protocol costs; these helpers
are definitionally the existing code, not replacement semantics. Proof
elaboration uses restricted transparency at concrete cost instantiations to
avoid reducing large gas numerals. No resource-limit increase or axiom was needed.

`WriteHost.lean` now proves the actual `writeMemH` and `regSetH` helpers preserve
the state relation. Memory writes use the original dependent-index byte loop;
its iteration proof preserves the relation without replacing the loop with a
new implementation. Register writes preserve metadata, optional byte charging,
size/usage errors and the full-register-file replacement rejection. Generic
cost sequences are instantiated at the actual protocol constants, with no
semantic or parameter change.

`StackHost.lean` now proves argument extraction and result pushes, including the
actual `popArgs` range loop, reversed argument vector and arity-error branch.
`StorageCalls.lean` composes these with the other helper proofs to establish the
**complete `storage_has_key` dispatch branch**. Its code correspondence theorem
is definitional equality with `hostCall "storage_has_key"`; no replacement
semantics is assumed. The simulation includes charges, key read/limit checks,
real and mock stores, recorder limits and output-stack changes.

The complete `storage_read` dispatch branch is now proved as well, with a
separate definitional correspondence theorem. The proof includes the real-store
path, mock trie lookup, large-value surcharge for values above 4000 bytes,
register writes, recorder-limit checks, missing-value return and all intermediate
failures. Its costs and order are exactly the current interpreter's.

`StorageMutations.lean` completes `storage_write` and `storage_remove` with
separate definitional correspondence theorems for both actual dispatch branches.
This includes replacement/insertion/deletion, the ordered real-store write log,
recorder growth on removal, storage-usage accounting, register/stack outputs,
key/value limits, both storage paths and the state retained on failures.

All four core storage dispatch branches now preserve the relation. The write
proof decomposition follows the actual do-elaborator's distributed store match;
no associativity assumption or replacement interpreter is needed to connect it.
Other host families remain missing. Instruction and step simulation are now proved
conditional on imported-host simulation, as described below. Completion
of these four branches does not establish whole-machine simulation, a byte codec,
a compressed proof or quantum security.

The state relation permits only the three maps' physical representations to
differ; every other machine field remains exact. A concrete normalized-state
entry point instantiates the storage-read helper theorem without an external
state-equivalence premise. The four core storage functions are covered, including their argument, limit
and stack logic. Other host families and whole-machine simulation remain open.

Entry-list normalization alone is not canonical byte serialization: enumeration
order can vary. A codec still needs framing, a deterministic ordering policy or
an appropriate noncanonical encoding theorem. The exact-state theorem above
cannot silently substitute observational equivalence for structural equality.

`Observational.lean` proves that the state/result relations are equivalence
relations and that segments, folds and fuel-bounded runs preserve them **if**
every interpreter step does. `StepPreservesMaps` names this still-unproved
whole-step obligation. `Instruction.lean` now derives it from imported-host
simulation. Terminal tags and abort errors remain exact.

`ObservedChain.lean` now supplies the observational composition theorem.
`observational_run_or_hash_collision` proves that a certified chain produces a
result equivalent to the actual interpreter's result (with the same fuel suffix),
or one of its checked boundaries exposes distinct encoded bytes with equal hash.
The decoder may reconstruct different map buckets. Its explicit premise requires
reconstruction equivalent to each actual boundary; the theorem derives that equal
encodings cannot conceal observably different states. Local segment validity,
whole-step preservation and observational decoding are still premises. This is a
deterministic semantic reduction, not quantum extraction or proof-system soundness.

`Control.lean` now proves the actual frame updates, returns, branches, bulk
memory copy and memory initialization preserve the relation. Gas synchronization
and instrumentation charging preserve it too, including overflow, exhaustion and
unmodeled hook-failure paths. The step dispatcher is proved conditional on
instruction-body preservation; this reduces the whole-step obligation but does
not discharge it. The actual host-call wrapper preserves the relation given a
host simulation, including its real-host domain gate, gas hooks and error
classification. `core_storage_call_equiv` instantiates that result for all four
core storage names with no additional host-simulation premise.

`Calls.lean` proves function entry, including invalid function indices, stack
exhaustion, gas synchronization failures, prologue charges and frame construction.
Function dispatch and both actual direct/indirect call instructions preserve the
relation conditional on `ImportsPreserveMaps` for the prepared program. The
indirect-call proof covers table bounds, null entries, unknown function/type and
signature mismatch branches. The import premise is still open for general
programs; it is not a claim that all host families are already covered.

`Numeric.lean` proves the actual `execNum` and `.num` instruction dispatch
preserve the state relation, including arithmetic traps and unsupported numeric
opcodes. A proved stack-pop identity keeps numeric value decoding separate from
state updates. Case analysis follows the existing opcode families and retains
the existing `Num` algorithms. This is a representation-preservation proof; it
does not independently establish the algorithms' Wasm specification correctness.

`StackControl.lean` groups 23 actual instruction constructors under an explicit
coverage predicate: unreachable/nop, blocks/loops/if/else/end, branches/return,
reference null/function/is-null, drop/select, local/global get/set (and local tee),
and integer constants. The simulation includes malformed-control errors and
stack effects. This predicate records proved cases, not a new challenge
restriction. Remaining instruction families still need proofs before applying
the whole-step composition theorem without its instruction-preservation premise.

`MemoryTable.lean` covers table get/set/size/grow, memory size/grow, element/data
drop, and integer loads. Growth limits, out-of-bounds traps, little-endian reads
and sign extension remain those of the actual interpreter. The float constructor
is covered only by preserving its existing out-of-domain rejection; floating
point execution is still absent from the relation. Memory stores and bulk
instruction composition are now proved in the modules below.

`BulkMemory.lean` proves the existing byte-store and fill loops and connects
store/copy/fill/initialize instructions to their helpers. `BulkTable.lean` proves
fill/copy/initialize table operations, including bounds failures and operand
consumption. No loop implementation is substituted.

`Instruction.lean` exhaustively cases on every existing `Instr` constructor and
composes the preceding results. `exec_equiv_of_imports` and
`step_preserves_maps_of_imports` now discharge instruction and step preservation
**conditional only on `ImportsPreserveMaps` for the prepared program**. Thus the
whole-step premise of observational segment composition reduces to imported-host
coverage. This still does not prove general host coverage, a byte codec, full
PV86 semantics, or cryptographic soundness. The float case continues to reject.

`HashHosts.lean` proves the four actual hash dispatches (`sha256`, `keccak256`,
`keccak512`, `ripemd160`), with definitional code correspondence. The proof
preserves memory/register inputs, per-byte or RIPEMD block-count charges,
register outputs, failures and VM gas hooks. The deterministic hash functions
remain exactly those of the interpreter. No hash-security property is assumed
or established by representation preservation.

`HostCoverage.lean` adds `checkProvedImports`, an executable sufficient check
for 65 names: four core storage, four hash, fifteen context, three register,
three balance/deposit hosts, value_return, panic, log_utf16, log_utf8, panic_utf8, abort, ed25519_verify, promise_result, promise_return, promise_batch_create, promise_batch_then, promise_and, promise_batch_action_transfer and both function-call action variants, promise_create, promise_then, deploy-contract, create-account, add-full-access-key, delete-key, function-call access-key, stake, refund-routing, delete-account, promise_yield_resume, promise_yield_create promise_yield_create_with_id, gas, three deprecated iterator both validator-query current_contract_code and explicit-ID yield-resume dispatches. A successful check discharges
`ImportsPreserveMaps` and hence whole-step preservation. The instantiated
`checked_imports_run_or_hash_collision` needs local segment validity and an
observational boundary codec, but no abstract host/step-simulation premise.
The check is conservative (even unused imported names must be covered) and is
not registered as a challenge restriction or admission rule. Other host families
remain work toward the full objective.

`ContextHosts.lean` proves fifteen exact dispatch branches: eight register-output
queries (account identifiers/public key, chain id, input and random seed) and seven
scalar queries (block index/time, epoch, storage usage, prepaid gas, used gas and promise-result count).
The input branch preserves `chargeBytes := false`; used gas is observed after
the base charge. Generic family proofs have kernel-checked correspondence for
each named branch and are integrated into the executable import check. Logs/panics, signatures and promise/action hosts
still require further coverage.

`RegisterHosts.lean` adds the actual `read_register`, `write_register` and
`register_len` dispatches to the executable coverage check. Code correspondence
is definitional, including argument order, base and byte charges, the missing
register sentinel, memory bounds failures and register-size/usage failures.
The write proof abstracts cost constants during composition, then instantiates
the exact protocol values; it changes neither costs nor execution behavior.

`BalanceHosts.lean` proves `account_balance`, `account_locked_balance` and
`attached_deposit`, and adds them to import coverage. Their outputs retain the
actual 16-byte little-endian encoding and memory-write charges/failures. The
actual `getU128H` and `setU128H` helpers also preserve the relation. These are
execution-preservation theorems, not balance conservation or economic proofs.

`ReturnHost.lean` proves the actual `value_return` branch and adds it to import
coverage. It preserves input reads, the maximum returned-data check, the ordered
receiver-dependent receipt-byte charge computation, overflow/gas failures and
installation of returned bytes. The theorem is definitionally connected to the
existing dispatch and does not assume return success or sufficient gas.

`LogHelpers.lean` proves log-count and log-length checks, appending, `pushLogH`
and guest-panic construction. In particular, the total length is incremented
before the size check, and the failure retains that updated counter and exact
error text. The explicit `panic` dispatch is proved and included in coverage.
UTF-8 decoding and abort are now proved below and included in import coverage.

`Utf16.lean` proves the actual UTF-16 host helper for explicit-length and
null-terminated inputs. The bounded scan preserves its early exit, read charges,
length and memory checks, odd-byte and decoder failures. Actual code correspondence
uses proved bind distribution, associativity and error absorption; helper code is
not silently substituted. The existing pure decoder is retained, not independently
proved Unicode-correct here. `LogHost.lean` composes this into the actual
`log_utf16` dispatch, now included in import coverage with its log-count check,
UTF-8 output-byte charges and final counter update.

`Utf8.lean` proves the actual UTF-8 helper, including its byte-by-byte bounded
null scan, early exit, terminator handling, per-byte charges and errors. It retains
the existing `String.fromUTF8?` decoder. Correspondence to `utf8H` is checked with
the same monad laws used for UTF-16. `Utf8Hosts.lean` connects this to the actual
`log_utf8` and `panic_utf8` dispatches, now included in import coverage. This
establishes representation preservation, not an independent Unicode theorem.

`AbortHost.lean` proves the actual `abort` dispatch and adds it to coverage.
Arguments retain their 32-bit truncation, pointer-underflow rejection, two
length-prefix reads and UTF-16 decoding. The exact diagnostic and log prefix,
charged byte count, log updates, guest-panic text and intermediate failures are
preserved. The proof does not assume that logging succeeds or the final panic
is reached.

`SignatureHost.lean` proves the actual `ed25519_verify` dispatch and includes it
in coverage. It preserves invalid signature-length errors, the encoding-invalid
return before message reads, per-message charges, public-key-length errors and
the existing verifier's return value. The deterministic Ed25519 computation is
retained; this theorem neither proves signature security nor upgrades NEAR
transaction authorization against quantum attacks. It requires no elliptic-curve
hardness assumption for representation preservation.

`PromiseResults.lean` proves `promise_result` and `promise_return`; the scalar
context family now also covers `promise_results_count`. Result retrieval retains
not-ready/success/failed outcomes, invalid indices and the successful result's
`chargeBytes := false` register write. Promise return preserves the receipt tag,
joint-promise rejection, invalid-index errors and both charges. These names are
included in coverage; further creation/action families remain unfinished.

`PromiseCreate.lean` proves account-ID reads/validation, receipt fee charging,
action appends, promise appends and the actual `promise_batch_create` dispatch.
The promise-limit check retains its append-before-failure semantics. Created
receipt/promise indices, receiver data and output-stack values remain exact.
The host is integrated into import coverage. Joins and
function-call/action construction still need proofs.

`PromiseThen.lean` proves the actual `promise_batch_then` dispatch, including
receipt/joint dependency selection, invalid-index errors, receiver-dependent
receipt fees, ordered action and promise appends, and output indices. The actual
`thenDataIdsH` increments the counter only for the real backend; both paths are
proved. The new host is integrated into the executable import check.

`PromiseAnd.lean` proves the actual `promise_and` dispatch against the existing
interpreter. It preserves ordered expansion of receipt and joint dependencies,
byte-count overflow, invalid indices, the dependency limit, gas and memory
charges, and promise insertion including failure state. The dispatch is included
in the executable import-coverage check.

`ActionTransfer.lean` proves the actual transfer-action dispatch, including
receipt validation, receiver-dependent fees, insufficient-balance failures and
ordered action insertion. Its shared lemmas cover receipt lookup, base and
per-byte action fees (including overflow), and balance deductions. Transfer
dispatch is integrated into the executable import-coverage check.

`FunctionAction.lean` proves `functionCallActionH` and its weighted and
unweighted batch dispatches. This covers ordered argument reads, empty-name
rejection, action fees and overflow, prepaid gas, balance deduction or one-yocto
subsidy, and real-backend UTF-8 validation before action insertion. Both dispatches
are connected to checked-import preservation. `PromiseCalls.lean` now integrates the higher-level promise-create and
promise-then dispatches, preserving dependency order, receipt fees, data-id
accounting and failures after partial receipt/promise construction. Both are
included in the executable coverage check.

`DeployAction.lean` proves local deploy-contract and create-account action
dispatches. It covers memory/register code reads, the contract-size limit,
receipt validation, base/per-byte fees and overflow, and ordered action
insertion. Both dispatches are included in checked-import preservation. These
are action-construction results, not proofs of subsequent contract preparation
or receipt application.

`KeyActions.lean` proves full-access-key addition and key-deletion action
construction. A shared parameterized proof preserves memory/register key reads,
receipt validation, fee charging before public-key validation, nonce encoding
and action insertion. Both dispatches are included in checked-import coverage.
Later receipt application remains open;
these semantic results do not establish quantum-resistant authorization.

`RestrictedKey.lean` proves function-call access-key action construction,
including allowance and receiver reads, method-list parsing, per-byte fees,
public-key validation and real-backend UTF-8 checks. The code-correspondence
theorem is definitional against the actual interpreter dispatch. It is included
in checked-import preservation; key cryptographic security is not established
by this simulation result.

`StakeAction.lean` proves the actual staking-action dispatch, preserving
amount/key read order, receipt validation, fees charged before invalid-key
rejection, exact amount/key encoding and ordered action insertion. The host is
included in checked-import coverage. This result concerns construction of the
action; subsequent stake application still needs its separate semantic bridge.

`AccountActions.lean` proves refund routing and account-deletion action
construction, including account reads/validation, invalid indices, distinct
joint-promise errors, deletion fees and ordered action insertion. Both dispatches
are connected to checked-import preservation. Later receipt application and
full account deletion are not established by these host-construction results.

`YieldResume.lean` proves the actual resume dispatch, including gas and read
order, payload limits, data-ID length validation, both real-store existence
checks, conditional action/status updates and 32-bit return. The distinct mock
action-list path is also covered. The host is included in checked-import
preservation.

`YieldCreate.lean` proves ordinary yield creation, including context-derived
data IDs, counter increment, real-store status insertion, receipt/promise
creation, fees, prepaid gas, method validation, register output and return.
The proof preserves intermediate state on failures and is connected to checked
imports. Code correspondence uses proved monad laws against the actual dispatch.
`YieldId.lean` also proves the explicit-ID creation variant, preserving duplicate
early return, three ordered real-store mappings, counter update, receipt
construction, prepaid gas, deposit/subsidy and method-name validation. It
includes the mock action-list duplicate check and is connected to coverage.

`LegacyHosts.lean` covers gas burning and the three deprecated iterator
dispatches. Iterator coverage proves their exact rejection behavior, not storage
iteration. `host_inventory.py`, run by `check.py`, evaluates the Lean coverage
and domain-gate lists and compares them with all 75 literal dispatcher branches.
The current 65-name coverage leaves no ungated dispatcher gaps. Ten additional names are real-backend
gated; completing their mock dispatch proofs would not supply excluded protocol
semantics. See `host-inventory.json` for names and source identities.

`ValidatorHosts.lean` proves validator-stake and total-stake queries,
including account parsing, first-match lookup with zero for missing accounts,
the exact total fold, gas order and 16-byte little-endian memory outputs with
failure state. Both are integrated into checked-import coverage. Authenticating
the supplied validator context remains a separate obligation.

`ContractCodeHost.lean` proves the current-contract query for absent and local
contracts. It preserves exact context bytes, charged register writes and errors
before the success return; it is included in checked-import coverage. This does
not prove that those bytes authenticate deployed code or its preparation.

`YieldIdResume.lean` proves explicit-ID resumption, including payload/ID
validation, stored ID resolution, missing-ID return, both status checks,
conditional action/status update, mock first-match lookup and 32-bit return.
All 65 ungated dispatcher names now have simulation coverage. Ten real-gated
names remain excluded by the current sufficient import check, even when unused.
This does not establish full protocol semantics, local proof validity, boundary
byte decoding or any quantum-security bound.

`RealHostGate.lean` adds a separate real-backend wrapper check accepting the
65 simulated names and ten gated names. Theorems preserve exact gate rejection
before gas synchronization and direct calls for related real states. This does
not prove raw mock dispatches for the gated names, implement their excluded
semantics, or yet propagate the weaker premise through full execution. The original general import checker remains unchanged.

`RealInstruction.lean` propagates the real-wrapper checker through indirect
calls, every existing instruction constructor and the gas/frame step dispatcher.
It proves that successful gas charges retain the real backend. Whole-run
composition still needs persistence of real-backend presence across arbitrary
steps; one-step simulation alone does not discharge that induction premise.

`BackendPersistence.lean` distinguishes backend presence from the existing
store-when-present invariant, which also permits a missing backend. It proves
presence preservation across synchronization, charging, entry, return, branching
and result-bind composition, including abort states. The host and exhaustive
instruction persistence proofs are still needed for full-run induction.

`HostPersistence.lean` defines one-way real-backend persistence including host
error states. Composition rules and gas/real-store read, accounting and update
helpers are proved. The VM host-call and function-call wrappers preserve the
invariant conditional on their imported hosts doing so. Instantiating that
premise for full dispatches remains necessary before whole-run lifting.

`HostDataPersistence.lean` proves backend persistence for argument loops,
argument/result stack handling, charged memory/register reads and writes, and
memory-or-register selection. The actual byte-update loop preserves the exact
real-backend field. These lemmas include failure states and support composing
the remaining full host-dispatch persistence proofs.

`PromisePersistence.lean` proves backend persistence for action/promise
insertion (including append-before-limit-error), receipt lookup, data-id counter,
balance/subsidy, fees and account reads. Full-access-key addition and key deletion
now have complete dispatch persistence proofs. The other dispatches still need
composition before the general wrapper premise is discharged.

`FunctionPersistence.lean` covers U128 reads/writes, function-call action
construction and both weighted/unweighted dispatches. Backend presence persists
through prepaid gas, deposit/subsidy updates, method-validation failures and
action insertion. Higher-level promise-create/then persistence is now composed below; other
full-dispatch persistence obligations remain.

`PromiseCallPersistence.lean` composes fresh and dependent receipt
continuations with function-call actions and return handling. It proves
persistence for promise-create/then and batch-create/then, including failures
after receipt or promise insertion and real-only dependency counter updates.
The generic host-wrapper premise still needs the remaining dispatches.

`ActionPersistence.lean` composes persistence for deployment, account creation,
staking and transfer dispatches. This includes size-limit rejection, validation
after fees, receiver-dependent transfer charges, balance errors and action
insertion. These are persistence results for construction, not later receipt
application. Other full-dispatch persistence obligations remain.

`AccountPersistence.lean` composes backend persistence for refund routing,
account-deletion actions and restricted function-call access keys. It includes
account and allowance reads, method-list parsing, fees and overflow, key
validation and real-backend UTF-8 validation, retaining presence on errors.
Remaining host dispatches still need persistence before whole-run composition.

`PromiseObservationPersistence.lean` establishes backend persistence for the
actual `promise_result`, `promise_return`, and `promise_and` dispatcher entries.
It covers register writes for successful results, not-ready and failed results,
invalid indices, joint-promise return rejection, and ordered dependency expansion
with integer-overflow and dependency-limit failures. These error-inclusive lemmas
close another prerequisite for whole-execution persistence; they do not yet
establish that invariant for every host or a complete state-transition proof.

`ContextPersistence.lean` covers the actual dispatcher entries for all 15
context getters, the three register operations, and four hash hosts (SHA-256,
Keccak-256, Keccak-512 and RIPEMD-160). Backend persistence includes the original
gas charges and memory/register error paths. The hash lemmas apply to arbitrary
deterministic byte functions: they establish execution persistence, not a
cryptographic security property or a choice of proof-system hash.

`OutputPersistence.lean` proves real-backend persistence for the three balance
and deposit queries, `value_return`, `ed25519_verify`, `validator_stake` and
`validator_total_stake`. Exact dispatcher correspondence retains charged U128
memory outputs, return-data length and receipt-fee overflow failures, and the
signature host's early encoding rejection. Signature verification is treated as
the existing deterministic computation, with no signature-security claim.

`LegacyPersistence.lean` covers `current_contract_code`, legacy gas charging and
the exact deprecated-iterator rejection behavior. `YieldPersistence.lean` covers
ordinary `promise_yield_resume`, including both real-store existence checks,
action append and the yield marker write, as well as payload and data-ID errors.

`YieldCreationPersistence.lean` closes persistence for `promise_yield_create`,
`promise_yield_create_with_id`, and `promise_yield_resume_with_yield_id`.
It includes counter updates, duplicate-ID short circuits, the three ordered
storage mappings, ID resolution, and error exits. Captured-state restoration
requires an explicit proof that the restored state has a real backend.

`LogPersistence.lean` closes `panic`, `log_utf16`, `log_utf8`, `panic_utf8`,
and `abort`, including bounded null-terminated scans, malformed encodings,
charged memory failures and the log counter update preceding limit rejection.
The proofs use the actual dispatcher definitions and preserve error states.

`StoragePersistence.lean` closes all four storage calls, retaining trie-operation
gas errors, recorded-storage limits, ordered updates, storage-usage changes and
old-value register writes. `PersistenceCoverage.lean` combines every host family
into `proved_host_keeps_real` over the same evaluated `provedHostNames` list used
by the simulation inventory: all 65 ungated dispatcher names now have a single
error-inclusive real-backend persistence certificate. The 10 real-gated names
still require wrapper rejection handling, not claims of implemented semantics. Instruction and whole-run persistence
must then be integrated, including real-backend rejection gates.

`CallPersistence.lean` lifts the coverage certificate through all 75 wrapper
names, imported/internal function dispatch, and direct/indirect call
instructions. The ten gated names are covered only by their exact rejection
behavior. `NumericPersistence.lean` proves that successful integer computations
retain the real field exactly and lifts this to numeric instructions, including
traps. `DataInstructionPersistence.lean` now covers stack/structured control flow,
memory/table access and growth, segment drops, and loads, including bounds
failures and the existing float rejection. `BulkPersistence.lean` now covers stores and all bulk memory/table operations,
including loop invariants and bounds failures. `RunPersistence.lean` combines all instruction families and proves backend
presence through steps and arbitrary fuel-bounded runs under
`checkRealWrapperImports`. `checked_real_run_equiv` now lifts logical map
representation equivalence to whole real-backed runs using this invariant.
This covers the existing interpreter including its rejection outcomes; it does
not implement excluded protocol features or prove serialized boundary binding.

`RealSegments.lean` connects real-backend persistence to observational
hash-linked segment composition. `checked_real_run_or_hash_collision` requires
the checked import list, a real initial state, locally valid segments, matching
boundary hashes, and observational decoding. It concludes whole-run equivalence
or a collision on distinct bytes at an actual supplied boundary link. Backend
presence at intermediate starts is derived, not separately assumed. This closes
the real-run segment-composition integration but leaves the concrete byte codec,
local proof-system soundness and quantum extraction/composition unimplemented.

`BoundaryWire.lean` implements a concrete `nearproof-boundary-v1` envelope
using existing proved Borsh byte parsers. Four distinct tags encode continuation,
completion, abort (state plus error bytes) and unmodeled errors. Round-trip and
injectivity hold under explicit per-payload length bounds below 2^32; decoding
rejects trailing bytes. Kernel examples reject missing input, invalid domain,
unknown tag and truncated abort payload. State bytes are still opaque: the full
StateBoundary codec, map normalization and immutable-context binding remain
unimplemented, so this envelope does not discharge ObservedBoundaryDecodes.

`ValueWire.lean` adds codecs for actual `Val`, arrays of values and `PromiseV`.
Round trips preserve integer width, null/reference tags, receipt/joint tags and
joint dependency order. Value and promise encodings are injective on their
explicit well-formed domains. Integer-value bounds follow from UInt32/UInt64;
reference indices require <2^64 and collection lengths <2^32. Reachable-state
bounds, remaining state fields and full boundary reconstruction remain open.

`FrameWire.lean` encodes every control label and frame field, with round trips
for labels, frames and frame lists and injectivity for frames. This includes
function/PC indices, exact locals, ordered labels, loop flags and stack base.
`GasWire.lean` encodes all gas fields, including host/action profiling, special
cost slots and send-compute usage, with round-trip and injectivity proofs.
Gas counters use explicit <2^128 bounds; frame indices use <2^64 and collection
lengths <2^32. These remain codec-domain obligations, not established invariants
for all executions. No production semantics or challenge bounds were changed.

`CollectionWire.lean` supplies a reusable ordered-array round-trip theorem and
concrete byte-array, byte-array collection, reference-table, element-segment and
register codecs. Byte-array collections serve pages, data segments and logs.
Order and multiplicity are retained; no sorting or deduplication is applied to
these observable fields. Fixed-width index and length bounds remain explicit.
These encodings serialize contents; they are not compact authenticated-memory
commitments and do not yet instantiate the full StateBoundary codec.

`StorageWire.lean` adds option/pair round-trip combinators and concrete codecs
for optional byte values, storage entries, mock trie arrays and ordered real
write logs. Deletion and a present empty value have distinct encodings. Write-log
injectivity preserves repeated writes and order. Logical-map reconstruction,
accounting/recorder fields and immutable backing-store authentication remain
separate obligations; these codecs alone do not authenticate storage contents.

`MapWire.lean` proves byte decoding rebuilds logical map entries and that equal
encoded bytes imply equivalent maps. It instantiates overlay and key-set codecs;
encoding is not claimed canonical across equivalent bucket layouts.
`AccountingWire.lean` encodes cache/recorder sets and all their counters, with
round trips to normalized structures and proved observational equivalence.
Counter bounds remain explicit (<2^128). These results do not authenticate the
immutable backing store or establish full-state decoding.

`RealStoreWire.lean` assembles every finite RealBoundary field into one codec:
root, overlay, accounting cache/counters, prefix, recorder/counter, recording
snapshot and ordered writes. Decoding yields the normalized boundary, and
restoration under the same immutable store is RealEquivalent to the original.
Equal encoded boundaries imply equivalent restored stores under that fixed
context. Optional real boundaries round-trip through normalization as well.
The backing function is deliberately supplied externally; proving its context
binding/authentication remains required, not discharged by these codec results.

`ContextValueWire.lean` proves UTF-8 string and promise-result round trips;
`ContextWire.lean` serializes all CallCtx fields and proves exact reconstruction
and injectivity. Identities, input, promise results, block/epoch information,
balances, gas/storage facts, random seed, receivers, validators and optional
contract/action hashes are retained. Context counters use explicit <2^128
bounds; strings and collections retain length premises. The larger context proof
uses a finite module-local elaboration budget of 4,000,000 heartbeats, with the
same kernel/axiom audit. These results serialize the context but do not prove
that its values are authenticated by the chain.

`ActionWire.lean` proves reconstruction of action logs, state-init payloads and
optional return values, including receipt-index versus byte-value tags.
`StateWire.lean` assembles codecs for all 24 finite state fields. Its parser
reconstructs the state up to logical map normalization and preserves any trailing
input for the enclosing parser. Restoration under the same fixed backing store
is proved StateEquivalent to the original. Field-size and integer-range bounds
remain explicit premises; these are not yet proved for every reachable state.
The state module uses a finite 8,000,000-heartbeat elaboration budget and passes
the same kernel/axiom audit. The complete audit passes 705 theorem checks.

`ResultWire.lean` integrates state payloads and error strings into the versioned
result envelope. It proves round-trip reconstruction up to ResultEquivalent for
all four result tags and rejection of appended outer bytes. Payload parsers also
require complete consumption. `encoded_real_run_or_hash_collision` instantiates
the actual run-composition theorem with this concrete codec: locally valid,
hash-linked segments give the corresponding execution result or a collision on
distinct supplied boundary bytes. Its remaining premises include representable
fields at each boundary, a common backing store, and checked real-wrapper scope.
It does not infer local validity from a cryptographic proof.

`BackedWire.lean` derives intermediate finish backing invariants from actual
segment execution. Its finite-start witness reconstructs each start under the
shared context; public endpoints are also restored from finite data. The
`finite_start_wire_run_or_hash_collision` theorem therefore needs no independent
backing premise at segment finishes or abstract decoder premise. Local validity,
checked real-wrapper scope and explicit encoding bounds remain. The shared
backing context is supplied, not cryptographically authenticated by this theorem.

`PageCommitment.lean` starts the connection to authenticated memory. It defines
domain-tagged page bytes and a page-digest directory from the actual `St.pages`.
Accepted page openings either reconstruct the actual page (and hence its
`readByte` value) or exhibit distinct supplied page encodings with the same hash.
The actual `writeByte` operation preserves every other directory entry and updates
its target using the modified page. These results assume an honest directory;
there is no authenticated directory root, access AIR, or quantum bound yet.
Encoding bounds remain explicit, and no hash injectivity axiom is introduced.

`PageTree.lean` adds binary tree roots and root-to-leaf openings with distinct
page/node message domains. Under the stated path lookup, page bounds and digest
bounds, an accepted opening gives the original page or a collision between a
message in the reference tree and one in the supplied opening. No global hash
injectivity is assumed. An opening hashes exactly one more message than its path
length. The follow-up balanced builder and numeric index correspondence are checked in
`IndexedPageTree.lean`; memory metadata binding follows in `MemoryDescriptor.lean` and honest updates
in `PageTreeUpdate.lean`; untrusted updates follow in `UntrustedPageUpdate.lean`,
while whole-boundary integration remains open. This deterministic
finite-message reduction is not a quantum extraction theorem.

`IndexedPageTree.lean` builds a balanced tree directly from the actual page array
at a supplied depth, using empty-byte padding. It proves that the path derived
from an in-range numeric index selects the corresponding array page. The
collision reduction now uses this correspondence, a capacity bound and an
allocated-page witness. An executable opening generator has proved direction
and root-reconstruction properties. Page count and depth are bound by the descriptor below; integration of that
descriptor into the whole-state commitment remains open. No
efficient incremental update implementation or measured proving result is implied.

`MemoryDescriptor.lean` binds allocation count, depth and tree root in a
domain-separated encoding. It proves descriptor injectivity under size bounds
and combines metadata binding with indexed page openings: an accepted read gives
the actual `readByte` result or a collision in the compared descriptor/tree/
opening messages. `checkMemoryPage` is an executable Boolean check with a proved
acceptance equivalence. A kernel example exhibits equal bare roots for an empty
allocation and one empty page, motivating the count check. This checker still
needs bounded operational parameters and linkage to the whole-state commitment;
it does not prove valid transitions, memory updates or quantum soundness.

`PageTreeUpdate.lean` proves that replacing a leaf on its numeric-index path
agrees with rebuilding the tree from `Array.modify`, including preservation of
subtrees outside the modified index. The actual `writeByte` tree and root follow:
reusing the original generated sibling path with the modified page computes the
new root. These are honest-update theorems under allocated-index/capacity premises;
the following module supplies the collision reduction for untrusted paths.
The reference opening generator builds sibling subtrees, so the theorem does not
establish a cached-tree implementation or measured speedup. Page hashing still
processes the page payload; the path argument does not eliminate that cost.

`UntrustedPageUpdate.lean` strengthens the opening reduction to bind both the
old page and the root after replacement. It locates any collision in the actual
reference-tree/supplied-opening messages. The specialized byte-write theorem
refines actual `writeByte`, and `checkedMemoryByteWrite` implements the descriptor
update after the Boolean page check. Its combined theorem gives the actual
post-write memory descriptor or a metadata/tree/opening collision. Size bounds,
the reference-state commitment and digest bounds remain explicit premises.
This covers a byte write, not bulk operations, growth, metering or full VM execution.

`MemoryWriteChain.lean` proves page encoding bounds survive actual byte writes
and derives descriptor well-formedness from count/depth/digest bounds. Its
executable `checkMemoryWrites` threads updated descriptors through a list of
supplied write witnesses. Successful verification starting at the actual initial
memory descriptor yields the descriptor of sequential actual `writeByte` calls,
or a collision in the metadata/tree/opening messages at a particular write.
Intermediate page bounds are derived, not supplied per state. Witness page/path
bounds remain premises. The `writeBytes` bridge follows below; `writeLE`, bulk instruction orchestration
and full metered execution remain separate.

`WriteBytesBridge.lean` proves the actual dependent-index `writeBytes` loop
executes exactly the ordered `(address + index, input byte)` requests. It connects
those requests to the memory-witness executor. `checkWriteBytes` checks that the
supplied request sequence matches exactly before checking its authenticated
writes. Success yields the actual `writeBytes` memory descriptor or a collision
localized to the checked sequence, under the established bounds and honest
initial descriptor premises. This does not establish completeness for arbitrary
out-of-range helper calls, host gas/error behavior, or a compact witness: each
write witness still contains a full page and sibling path.

`PageBatch.lean` proves ordered writes whose offsets remain within one page
can be applied to that page once while preserving the actual sequence of
`writeByte` state transitions. Repeated offsets retain their original order.
`checkPageBatch` checks all offsets and one page opening, applies the writes,
and computes one replacement root. Its successful result equals the descriptor
of the actual request sequence or exposes a collision in the tree/opening
messages. This reduces repeated authentication work structurally, but does not
justify reordering across pages or host observations. Automatic grouping of a
`writeBytes` request stream, multi-page composition and measurements remain open.

`PageBatchChain.lean` composes page batches in order, deriving intermediate
page bounds from actual byte execution. Its executable `checkBatchedWriteBytes`
checks the flattened request list exactly against the original `writeBytes`
input before validating the batch chain. Successful verification returns the
actual final memory descriptor or a collision localized to a checked batch.
Grouping remains supplied by the witness; this does not prove a maximal-group
constructor or measured performance. The axiom audit parser now accepts Lean's
multiline reports while retaining exact coverage and the unchanged allowlist;
synthetic forbidden-axiom and truncated-report cases were checked.

The SHA-512 microbenchmark in `memory_batch_bench.py` now compares cached-tree
per-byte authentication with ordered page batches. Results are saved in
`results/memory-batch-sha512.json` with source identity and environment details.
Both modes match independently updated flat memory and a bottom-up root rebuild;
ten malformed/stale/reordered witness cases are rejected. Page/node domain bytes
were checked against the Lean definitions, but Python-to-Lean equivalence is not
proved. This is not a prover or quantum-security benchmark.

| Workload | Per-byte witness bytes | Batched witness bytes | Verifier hash calls, before → after |
|---|---:|---:|---:|
| 1 byte | 66,044 | 66,044 | 16 → 16 |
| 256 bytes, same page | 16,907,264 | 67,319 | 4,096 → 16 |
| 4 KiB, same page | 270,516,224 | 86,519 | 65,536 → 16 |
| 4 KiB, crossing a page | 270,516,224 | 152,558 | 65,536 → 32 |
| 1 MiB, 17 pages | not run | 6,365,543 | not run → 272 |

The local witness transport includes full pages, sibling paths and explicit
address/value records, excluding the shared descriptor. It is not a final
succinct proof; input records may be derivable rather than transmitted. Timings
exclude tree construction and grouping and are single runs on a shared host.
A 4 KiB same-page verification took about 397 ms per-byte versus 0.525 ms batched;
these are native Python/SHA-512 measurements, not AIR proving times. Sparse
access still requires about 66 KB, motivating investigation of subpage leaves.

Reproduce the bounded microbenchmark from the repository root:

```sh
HEAVY_MEM=2G taskset -c 8 /data/illia/nearproof-deps/bin/heavy \
  python3 research/near-compression/memory_batch_bench.py \
  --output research/near-compression/results/memory-batch-sha512.json
```

`memory_leaf_sweep.py` measures exploratory 256 B, 1 KiB, 4 KiB and 64 KiB leaves
on identical requests over 8 MiB memory, with three repetitions per case. These
block layouts use distinct, size-bound hash domains and are **not** covered by
the current Wasm-page refinement proofs. All runs match direct memory updates
and independent root rebuilds; ten mutation cases are rejected for each layout.
Results and source/request hashes are in `results/memory-leaf-sweep-sha512.json`.

| Leaf bytes | Sparse 16-write witness bytes | Sparse verifier hash calls | Dense 64 KiB witness bytes | Dense verifier hash calls |
|---|---:|---:|---:|---:|
| 256 | 21,056 | 512 | 663,296 | 8,192 |
| 1,024 | 31,136 | 448 | 451,904 | 1,792 |
| 4,096 | 78,080 | 384 | 405,680 | 384 |
| 65,536 | 1,056,704 | 256 | 393,719 | 16 |

The transport includes explicit update records, so these are not final proof
sizes or intrinsic witness lower bounds. Small leaves help sparse access but
increase tree work on dense writes. Retain 1 KiB and 4 KiB as candidates for a
parameterized subpage refinement; do not select a production size from these
synthetic cases. Actual access traces and AIR hash costs are still needed.
Native verification medians and separate construction measurements are recorded;
update timings exclude construction and request grouping.

```sh
HEAVY_MEM=2G taskset -c 8 /data/illia/nearproof-deps/bin/heavy \
  python3 research/near-compression/memory_leaf_sweep.py \
  --output research/near-compression/results/memory-leaf-sweep-sha512.json
```

`SubpageRead.lean` provides the first semantic connection for smaller leaves:
for any positive block size that partitions a full 64 KiB page, extraction has
the expected block length and its local byte read equals the actual Wasm
`readByte`. The existing page-size and page-presence assumptions are explicit;
no allocation semantics change. The 1 KiB/64-block and 4 KiB/16-block layouts
have kernel-checked parameter examples. Subpage writes, global block indexing,
commitment integration and reachable full-page invariants remain required.

`SubpageWrite.lean` proves byte writes commute with extraction of a bounded
slice and that writes outside the slice preserve it. For a positive block size
partitioning a full Wasm page, the local subpage update matches extraction after
the full-page update. The final theorem connects this result to actual
`writeByte` and its page-array lookup. Allocation/page-size premises remain
explicit. This is byte-level refinement, not yet a block-tree commitment or
full-state transition implementation.

`SubpageIndex.lean` maps global block indices to Wasm page indices and local
block/byte offsets, and constructs a finite directory of extracted blocks. It
proves allocation bounds, exact lookup/read correspondence, and the target
entry's update under actual `writeByte`. These results work for any positive
block size partitioning a full page. Whole-directory update equality is established in `SubpageDirectoryUpdate.lean`
under the same allocation/layout premises. The directory is not yet an authenticated
block tree; page-size reachability and commitment/boundary integration remain open.

`SubpageDirectoryUpdate.lean` proves non-target blocks remain unchanged both
within the written Wasm page and across different pages. The whole finite
directory after actual `writeByte` is exactly its original directory with one
local block update at the global block index. No global hash-injectivity or
commitment assumption is used. This closes the single-byte representation
update, while reachable full-page invariants, block-specific commitment domains,
shape binding and whole-state integration remain required.

`FullPages.lean` proves the actual zero-page allocation and append construction
produce full 64 KiB pages. Actual `writeByte`, `writeBytes`, `writeLE`, `memCopy`,
`memFill` and `memInit` preserve that invariant, including bulk-helper abort
results. Full page size implies the existing page encoding bound. These results
cover memory construction and writers; they do not yet prove all successful
instantiations, host calls or whole runs preserve page shape. The successful
`memGrow` append expression is covered, not yet the entire metered instruction.

`SubpageBounds.lean` derives allocated block existence, exact block sizes and
encoding bounds from full Wasm pages and the valid partition. `SubpageCommitment.lean`
then uses a separate block-size-prefixed hash domain with the checked tree
machinery. An accepted indexed block opening gives actual `readByte` or a
collision located in the underlying hash's prefixed reference/opening messages.
Full-page shape, allocation, layout, depth capacity and witness bounds remain
explicit. The exact domains differ from the exploratory Python sweep, so those
measurements are not implementation validation of this protocol. Enclosing
metadata binding, block writes and whole-state integration remain open.

`SubpageCommitmentWrite.lean` connects exact subpage-directory updates to tree
replacement and proves accepted untrusted block openings compute the root after
actual `writeByte`, or expose a collision in the underlying prefixed hash
messages. This extends the block commitment connection from reads to one-byte
writes. The block layout, allocation, tree depth/capacity and full-page invariant
remain supplied premises; metadata binding and an integrated checked block-write
interface are still required.

Next: prove representability for full executions, authenticate the shared
program/configuration/backing context, and replace full memory data with
authenticated access proofs. Program/configuration and
backing-store identities must be bound by the enclosing statement. A state root
alone does not reconstruct memory or host continuation state. These theorems do
not prove AIR validity, quantum extraction or compact proof size.

## Remaining end-state requirements

| Requirement | Current evidence/status |
|---|---|
| Full 1 Pgas transition semantics | Existing D3 is restricted; research cap definition only |
| Honest workload-to-trace capacity | No gas-to-row theorem for all components |
| Concrete segment AIR and witness generation | Not connected to this bridge |
| Finite boundary representation | Whole-result codec and run composition checked under bounds/backing premises; authenticated memory missing |
| Quantum soundness and recursive extraction | Foundation only; reductions missing |
| Concrete hash instantiation | Not proved by an ideal-oracle theorem |
| Complete proof under 300,000 bytes | No full NEAR proof at this size |
| Measured 1 Pgas proving time/memory | No benchmark; earlier projections are estimates |
| Deployed verifier and Lean theorem connection | Not implemented for the new scheme |
| Challenge admission | No new admission claim |

## Authenticated block operations

`BlockDescriptor.lean` canonically encodes the block size, blocks per Wasm page,
allocated Wasm page count, tree depth and root. Its parser round-trip establishes
encoding injectivity under explicit representability bounds. `checkBlockOpening`
checks positive block size, page layout, capacity, allocation, claimed block size,
path directions and root agreement.

`AuthenticatedBlockRead.lean` and `AuthenticatedBlockWrite.lean` connect that
executable check and descriptor-hash equality to actual Wasm reads and byte
writes. An accepted read returns the actual byte, and an accepted write opening
computes the actual updated tree root, or the supplied descriptor/tree messages
exhibit a collision in the underlying hash. Layout and allocation premises are
now obtained from the authenticated descriptor check rather than separately
trusted opening metadata.

The reference descriptor still must be bound to the enclosing full-state
statement. Full-page, encoding and digest bounds remain explicit premises.
`CheckedBlockWrite.lean` now supplies the executable descriptor update and proves
it equals the descriptor of actual `writeByte`, or exhibits a localized hash
collision. `BlockWriteChain.lean` threads these updates through a supplied list
of byte writes. Its induction preserves full pages and allocation bounds; an
accepted final descriptor equals the actual sequential execution descriptor, or
one actual-state step exposes a collision. Witness byte/path well-formedness
remains a premise, and the initial descriptor must be authenticated externally.

`BlockWriteBytes.lean` now connects this chain to the actual dependent-index
`writeBytes` loop. Its executable wrapper checks block/path encoding bounds and
exact equality of the ordered address/value stream with the requested payload.
The end-to-end helper theorem therefore requires no separate witness-well-formedness
premise. A rejection theorem covers any different ordered request stream.

This helper does not include enclosing host gas or bounds checks, and still uses
one opening per byte rather than batched block updates. No quantum extraction,
AIR implementation or succinct-proof-size result follows from these reductions.
`BlockBatch.lean` now proves that an arbitrary ordered list of writes whose
offsets lie within one allocated block changes exactly that directory entry.
It connects the resulting tree to one leaf replacement, and proves that a
single accepted opening computes the actual batch result root or exposes an
underlying hash collision. Repeated offsets retain their original order; no
sorting of writes or movement across reads is justified. `CheckedBlockBatch.lean` now supplies an executable single-opening batch
checker. It validates positive block size, page layout, tree capacity,
allocation, claimed-block size, witness encoding bounds, all write offsets,
path directions and root agreement. Its accepted descriptor equals the actual
ordered batch execution descriptor or the checked messages expose a hash
collision. Page count preservation is proved for arbitrary byte-request lists.

The initial descriptor must be authenticated by the enclosing state statement,
and the current theorem requires full allocated Wasm pages.

`BlockBatchChain.lean` now threads descriptors through supplied block batches
and connects the resulting checker to actual `writeBytes`. The wrapper checks
that concatenating the batches' absolute address/value requests yields exactly
the requested payload sequence. A differing sequence is rejected. Accepted
outputs equal the actual final descriptor or expose a collision at a checked
batch; witness encoding bounds are checked inside the batch verifier, not
assumed by the composition theorem. The batch witness container is reused from
`PageBatchWitness`, with its index/page fields representing a block here.

`HonestBlockBatch.lean` now constructs a single batch witness from the actual
subpage directory and proves the checker accepts it with exactly the actual
post-write descriptor, without a collision alternative. It also proves generated
Merkle paths meet encoding bounds when hash outputs do. Completeness assumes
full pages, positive block size, valid page layout, sufficient tree capacity,
an allocated block and in-block offsets. The reference constructor rebuilds
trees and is not an optimized witness generator.

`HonestBlockSequence.lean` now generates witnesses for an ordered batch plan,
advancing actual Wasm memory before constructing each subsequent opening. It
proves preservation of the plan's request stream and exact checker acceptance
for every valid plan. The completeness result also reaches `writeBytes` when
the supplied plan exactly represents its payload; it requires no collision
assumption. Allocation and full-page invariants are preserved through execution.

`BlockGrouping.lean` now groups consecutive requests to the same block and
proves exact request-stream preservation and validity. `honestWriteBytesWitness`
takes the actual state, layout, address and payload directly. For an in-bounds
payload, full allocated pages and a valid layout/tree capacity, the checker
accepts this generated witness with the exact descriptor after actual
`writeBytes`, without any caller-supplied grouping premise or collision assumption.
The grouping never moves a write across another block's requests.

Interpreter measurements are recorded below; the generator still rebuilds
trees for each batch. No reordering across reads or host effects is justified.
The full audit passes 843 public theorem checks
(`/tmp/near-grouped-write-bytes-audit.log`).



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

`CachedBlockSequence.lean` now generates batch witnesses using only the cached
tree and the plan. It reads each block from the cache, obtains cached sibling
hashes and updates the affected path. The exact-correspondence theorem proves
its entire witness list equals the actual-state reference generator for every
valid plan, including repeated block visits. A completeness theorem then proves
checker acceptance with the actual final memory descriptor. Full-page, valid
layout/capacity and allocated-offset premises remain explicit.

The full audit passes 850 public theorem checks; log:
`/tmp/near-cached-sequence-accepted-audit.log`. Comparative interpreter timings are recorded below; the earlier smoke results
measure the rebuilding generator. Cached payload-wrapper integration is recorded below; larger representative
workloads remain outstanding.
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

## Reproduce

On this shared host, use the existing bounded build wrapper:

```sh
cd research/near-compression
HEAVY_MEM=8G LEAN_NUM_THREADS=2 taskset -c 8-15,24-31 \
  /data/illia/nearproof-deps/bin/heavy python3 check.py
```

The script builds against the actual NearSpec packages, checks all **991** public
theorem axiom closures and boundary regressions, then records the current scope
with source hashes. Only `propext`, `Classical.choice`, and `Quot.sound` are
allowed in theorem dependencies. No `sorry`, custom axiom or `native_decide` is
used. Existing upstream deprecation/unused-variable warnings are unrelated to
these proofs.


`MemoryHostSmoke.lean` now passes eight actual-host/checker parity cases: success, base-gas failure, byte-gas failure, bounds failure, both gas-before-bounds cases, empty-at-end and empty-past-end. It compares all gas fields, exact status and descriptor, checks unchanged memory on failure and direct memory replacement on success. Burnt and host gas also match independently calculated expected totals. Evidence: `research/near-compression/results/memory-host-lean-smoke.json`. Reproduce with `lake env lean --run MemoryHostSmoke.lean` from the research package (use the bounded wrapper). This is executable helper validation, not full-state or AIR correctness.


## First concrete Wasm addition AIR gadget

`NearCompression/InstructionAdd.lean` uses the existing `ZkFormal.Air.Expr`
and `Table` definitions and the executable BabyBear field. Its eight columns
hold two 16-bit limbs for each operand and output, plus two carries. Four
polynomial constraints enforce the two addition equations and boolean carries.
The five audited theorems show that vanishing constraints, **assuming all six
limbs are below 65536**, imply the actual `Num.binop 32 0` result and the
`execNum 0x6A` result with explicit operand stack-pop bindings. Bounded sums
are proved not to wrap modulo the field; the word result wraps modulo 2^32.

This table has no bus interactions. Limb range enforcement, stack consistency,
code fetch/opcode selection, execution sequencing, gas, and incorporation in
the assembled NEAR AIR remain integration obligations. In particular, its
`maxLog = 22` is a local table parameter, not evidence of 1 Pgas capacity.
The full audit currently passes 866 public theorem axiom closures
(`/tmp/near-instruction-add-audit.log`). This deterministic arithmetic result
provides no new proof-size measurement or quantum-security bound.


The instruction gadget now also includes an honest constructor for all pairs of
`UInt32` inputs, with universal proofs of constraint acceptance, limb ranges,
and exact input bindings. The full audit passes **870** theorem axiom closures
(`/tmp/near-instruction-add-complete-audit.log`). `InstructionAddSmoke.lean`
passes eight honest boundary cases and rejects 32 output/carry mutations.
A malformed row encoding input and output 2^32 satisfies the arithmetic
polynomials but disagrees with Wasm addition; the separate executable range
guard rejects it. This regression demonstrates why the missing AIR range
constraints are essential. Reproduce with `lake env lean --run
InstructionAddSmoke.lean` from this package. These tests are arithmetic checks,
not proof generation or proof-size benchmarks.


## Range-enforced instruction baseline

`InstructionAddRange.lean` extends the eight arithmetic columns with 96 boolean
bit columns. Six Horner reconstruction equations force the six operand/output
limbs into the 16-bit range. The resulting table has **104 columns and 106
constraints**, all of degree at most two. Its Lean soundness theorem derives
the range bounds from polynomial vanishing, so the Wasm addition result no
longer assumes an external range guard. A universal honest constructor is
proved to satisfy every arithmetic, reconstruction and boolean constraint.

`InstructionAddTrace.lean` proves that current-row expressions evaluated by
the gadget agree with the actual AIR trace evaluator. `InstructionRangeTrace.lean`
uses that bridge to derive the addition result from `Air.Holds` for a trace
containing the range-enforced table. Both tables use `maxLog = 22`; the original
arithmetic table's value of 24 violated the existing verifier's structural
limit and has been corrected. Explicit well-formedness theorems check column
bounds, degree and height limits.

This is a correctness baseline with a substantial width cost; no claim is made
that bit decomposition is the best proving implementation. Stack and code bus
bindings, opcode selection, PC/gas/frame transitions, other instructions,
full-state integration, 1 Pgas capacity, recursion and quantum-security bounds
remain open. The table has no bus interactions yet. A local height limit is
not evidence of sufficient full-transition capacity.


Validation: full audit passes **889** public theorem axiom closures
(`/tmp/near-instruction-range-audit.log`). `InstructionAddRangeSmoke.lean`
passes eight honest cases and rejects 1,600 mutations: incrementing each of
104 columns and flipping each of 96 boolean bits, for every case. The previous
range-omission forgery is rejected by polynomials alone. Reproduce with
`lake env lean --run InstructionAddRangeSmoke.lean` in this package. Results
and source hashes are in `results/instruction-add-range-lean-smoke.json`.
The scope reporter now uses named source paths instead of positional entries
for its challenge and gas-cap inputs, so adding sources cannot change those
inputs accidentally.


## Addition step semantics and execution checks

`InstructionAddStep.lean` connects a range-enforced arithmetic row to exact
`exec` and `step` results, including the whole post-state and PC increment.
It discharges operand-pop bindings for concrete i32 pushes, derives the
successful fast-gas decrement from sufficient-gas and no-overflow bounds,
and propagates gas failures before arithmetic. Overflow and insufficient-gas
lemmas retain exact synchronized/burned failure states, with explicit sync
and burn premises. Code fetch, prepared gas metadata and stack bindings are
still premises: this does not add their polynomial or bus enforcement.

`InstructionAddStepSmoke.lean` passes 24 successful actual-step cases, two gas
failures, three malformed-fetch rejections, and empty-frame termination.
The first group uses labeled synthetic Prepared fixtures. An additional valid
binary module goes through actual `prepare`, then executes two constants and
addition. Its result wraps to zero, PC advances by three, and the fast-gas
counter decreases by exactly 2,468,268 (= 3 × 822,756); burnt gas remains zero
until synchronization. Tests compare stack, frames and all gas fields, plus
selected unrelated fields; the formal successful-step theorem states exact
whole-state equality. The module test uses a manually constructed execution
state and does not establish instantiation or chunk replay correctness.

The full audit passes **900** public theorem axiom closures
(`/tmp/near-instruction-step-audit.log`). Reproduce the executable test with
`lake env lean --run InstructionAddStepSmoke.lean`; source hashes and outcomes
are in `results/instruction-add-step-lean-smoke.json`. Next integration work
must enforce the fetch, stack and gas relationships in the AIR. Full-state
coverage, 1 Pgas capacity and compact quantum-resistant proof generation remain
unestablished.


## Opcode, PC and stack-height constraints

`InstructionAddControl.lean` adds polynomial enforcement of opcode 106,
nonwrapping 32-bit PC increment, and stack-height decrement with height at
least two. Seven 16-bit values are bit-decomposed. Universal soundness and
honest completeness are proved; completeness covers `pc + 1 < 2^32` and
`2 ≤ height < 65536`. The resulting table has **225 columns, 231 constraints,
degree at most two, maxLog 22**. The 16-bit stack-height domain still needs a
proof connecting it to validated VM execution bounds.

`InstructionControlTrace.lean` lifts the constraints from actual `Air.Holds`
and proves that the row opcode and next-PC values yield the exact uncharged
Wasm step result when code-fetch and operand bindings hold. These are local
pre/post metadata values, not next-row references. Cross-row sequencing,
code/stack authentication and gas polynomial enforcement remain missing.

The independent test encoder matches the formal witness on every column in
six boundary cases. Polynomial checks reject 2,022 individual mutations,
24 coherent metadata forgeries (value and its bit decomposition changed
together), and five domain violations. The full audit passes **916** public
theorem axiom closures (`/tmp/near-instruction-control-audit.log`). Reproduce
with `lake env lean --run InstructionAddControlSmoke.lean`; results and hashes
are in `results/instruction-add-control-lean-smoke.json`.

The width is a performance concern: assuming packed four-byte field elements,
225 columns require 900 bytes per row, or 3.515625 GiB for 2^22 rows before
prover overhead. This is a layout calculation, not a measured allocation or
succinct-proof size. A shared range-check mechanism is a future optimization;
this bit-decomposition implementation is the correctness baseline. No full
1 Pgas run, sub-300 KB proof or quantum-security result follows from it.


## Noncyclic row sequencing

`InstructionSequence.lean` adds a generic list of post-column/next-pre-column
links using `isTransition * (post - nextPre)`. Actual trace evaluation enforces
these equalities on every nonfinal row; the final row is proved to impose no
cyclic wraparound constraint. The addition specialization links both PC limbs
and stack height, yielding **225 columns and 234 degree-at-most-two constraints**.
Lean proves PC(r)=PC(0)+r and height(r)+r=height(0).

The capacity theorem establishes traceHeight+1 ≤ initialHeight and log ≤15:
a contiguous addition-only segment with 16-bit heights cannot exceed 32,768
power-of-two rows, despite the table's configured maxLog22. This is a bound
on this specialized segment, not a VM or protocol gas bound. Mixed instructions,
padding and authenticated segment interfaces still need implementation.

`InstructionSequenceSmoke.lean` checks a four-row reduction against actual
`execNum`, rejects coherent PC/height discontinuities while verifying their
individual rows remain valid, and verifies all three final-row links vanish.
It deliberately reproduces the remaining operand-binding gap: a two-row trace
with correct PC/height continuity but a disconnected second operand passes
these constraints and claims9 where the connected stack computation gives7.
Therefore sequencing does not yet prove a stack-consistent execution trace;
operand-stack authentication is a required next step.

Full audit: **926** public theorem axiom closures pass
(`/tmp/near-instruction-sequence-audit.log`). Reproduce tests with
`lake env lean --run InstructionSequenceSmoke.lean`. Outcomes and hashes are
in `results/instruction-sequence-lean-smoke.json`. Full state transitions,
1 Pgas proving, compact proofs and quantum-security bounds remain unverified.


## Result-to-operand links

`InstructionOperandSequence.lean` adds two transition constraints linking
output limbs to the next row's right operand. The table now has **225 columns
and 236 constraints**, degree at most two. Actual AIR satisfaction implies
Wasm addition recurrence and accumulated output equal to the initial right
operand plus the supplied left-operand sum, modulo 2^32. This is arithmetic
soundness relative to that stream, not authentication of the stream.

`InstructionStackPair.lean` proves exact execution of two actual `execNum`
additions from a concrete typed initial stack when the left operands match
that stack and the intermediate result is linked. The equality preserves the
entire residual state. It does not incorporate fetch, PC or gas, and the
initial-stack bindings remain explicit premises.

`InstructionOperandSmoke.lean` accepts an honest four-row chain and rejects
the previous disconnected-right-operand trace plus three coherently encoded
variants. A forged left operand still passes: the trace claims102 while the
actual typed stack computes7 and preserves its prefix. This intentionally
retained counterexample identifies initial-stack/left-stream authentication
as the next missing constraint family. First-row right input, code, gas and
segment boundaries also require authentication/integration.

The full audit passes **935** public theorem axiom closures
(`/tmp/near-instruction-operand-audit.log`). Reproduce the executable checks
with `lake env lean --run InstructionOperandSmoke.lean`; results and hashes
are in `results/instruction-operand-lean-smoke.json`. The overall 1 Pgas,
sub-300 KB and quantum-security targets remain unverified.


## Initial-stack commitment baseline

`InstructionStackCommitment.lean` uses the domain `nearproof-stack-v1` and
the existing typed stack wire codec. A full-stack opening contains a prefix
and three i32 operands. Its executable checker verifies encoding bounds,
commitment equality, both rows' operand bindings and their initial heights.
Accepted openings give exact two-addition execution on the actual initial
state, or an explicit collision between two distinct encoded stack messages.
The expected root is assumed to be the commitment of that actual initial
stack; binding it into the enclosing state-transition statement is still
required. Encoding references requires indices below2^64 and stack lengths
below2^32, checked before acceptance.

`InstructionStackCommitmentSmoke.lean` passes the honest pair and a valid
reference opening, and rejects eleven forged/malformed cases: changed left
or initial-right operand, matching forged opening, type/prefix/order changes,
wrong domain, wrong row heights, and an out-of-range reference. The latter
encodes and hashes identically to a valid reference after u64 truncation,
so rejection specifically verifies the executable codec-bound guard.
A46-byte fixture's SHA-512 digest matches independent Python `hashlib`
with explicit little-endian encoding.

Full audit: **944** public theorem axiom closures pass
(`/tmp/near-instruction-stack-commitment-audit.log`). Reproduce with
`lake env lean --run InstructionStackCommitmentSmoke.lean`; source hashes
and independent fixture data are in
`results/instruction-stack-commitment-lean-smoke.json`.

This is full-stack opening validation **outside AIR**, not a succinct stack
authentication circuit. The arithmetic rows themselves still do not enforce
this hash check. Hash/AIR integration, arbitrary-length stack execution,
full-state root binding, code/gas authentication and the full 1 Pgas target
remain unfinished. No quantum-security bound follows from the deterministic
correctness-or-collision theorem.


## SHA-512 AIR dependency audit and 64-bit addition

Local source inspection finds a SHA-256 AIR in `ZkFormal/Sha` (544 columns,
1+17k rows for k padded blocks), but no `sha512`, `SHA512` or `SHA-512`
references anywhere in `zk-formal/ZkFormal`. The SHA-512 executable spec's
own status records differential tests and digest-length proofs, not a general
FIPS-equivalence proof. Source hashes and exact scope are recorded in
`results/hash-air-inventory.json`. Existing SHA-256 constraints cannot simply
be used to certify the SHA-512 stack commitments.

`InstructionAdd64.lean` now provides four-limb modular addition over BabyBear:
**208 columns, 212 constraints, degree at most two**. All twelve 16-bit limbs
and four carries are constrained. Universal soundness proves actual Wasm
`Num.binop 64 0` and `execNum 0x7C` results, with explicit stack bindings for
the latter; honest witness acceptance and input reconstruction are also proved.
`SHA512AddBridge.lean` proves the same rows implement the actual SHA-512
`add64` helper and composes seven additions into the two updated words of a
compression round. Sigma, choice and majority values remain explicit semantic
inputs, not constrained bit operations.

`InstructionAdd64Smoke.lean` passes eight carry/wraparound boundary cases,
rejects 3,200 individual-column/boolean-bit mutations, and checks four SHA-512
round-addition compositions totaling 28 rows. The full audit passes **960**
public theorem axiom closures (`/tmp/near-instruction-add64-audit.log`). Run
`lake env lean --run InstructionAdd64Smoke.lean` to reproduce. Results and
source hashes are in `results/instruction-add64-lean-smoke.json`.

The remaining hash-circuit work includes 64-bit rotations/XOR/choice/majority,
message schedule,80-round sequencing,feed-forward,padding/length and byte/digest
bindings, followed by stack-codec integration. The addition bridge does not
prove SHA-512 hashing or quantum soundness. Full state-transition coverage,
1 Pgas performance and sub-300 KB proofs remain unverified.


## SHA-512 bit-operation AIR

`SHA512BitSemantics.lean` adapts the existing bit-proof structure to the
actual 64-bit SHA-512 functions, proving rotation, sigma, choice, majority
and word bounds. Generic bit reconstruction lemmas are reused.
`SHA512Bits.lean` constrains three 64-bit input vectors and six output vectors:
bsig0(x),bsig1(x),ssig0(x),ssig1(x),ch(x,y,z),maj(x,y,z). All192 input bits are
constrained boolean, and384 output equations force the exact semantic bits.
The table has **576 columns,576 constraints,degree at most three,maxLog22**.
Universal soundness and honest witness acceptance are proved.

`SHA512BitsSmoke.lean` passes eight six-operation word cases,64 one-hot sigma
cases covering every rotation position, and rejects7,680 nonboolean-input or
corrupted-output mutations. A six-output fixture also matches independent
Python bit arithmetic. Arbitrary input-bit flips are not required to fail:
changing a legitimate input can leave choice/majority outputs unchanged.

The full audit passes **991** public theorem axiom closures
(`/tmp/near-sha512-bits-audit.log`). Reproduce with
`lake env lean --run SHA512BitsSmoke.lean`; results and source hashes are in
`results/sha512-bits-lean-smoke.json`.

The bit and addition tables still need explicit circuit wiring into rounds,
message schedule and compression chaining. Padding,length,byte/digest binding
and stack-commitment integration remain missing. This is not a complete SHA-512
AIR or a quantum-security proof. Full 1 Pgas proving and sub-300 KB proof size
remain unverified.


### Constrained SHA-512 round assembly

`SHA512Round.lean` now connects two bit-operation gadgets and seven 64-bit
addition gadgets with 40 polynomial limb equalities. Sixteen-bit limbs avoid
aliasing a 64-bit word modulo BabyBear. The assembled table has 2,608 columns,
2,676 constraints, degree at most three, and maxLog22. Its 16 new theorems
include equality of all eight decoded outputs to the actual specification's
`SHA512.round`; sigma, choice, majority and intermediate dependencies are
established by the constraints, with no external computational wiring premise.
`SHA512Relocate.lean` proves evaluation preservation for column relocation.

`SHA512RoundSmoke.lean` checks four honest rounds, the complete decoded inputs,
and an independent Python arithmetic fixture. It also replaces each wired
adder operand and recomputes an internally valid adder witness: all 40 such
forgeries satisfy the individual gadgets but fail the assembled constraints.
An independent assembly of the layout matches the formal constraint list.
The full audit passes 1,008 theorem axiom closures
(`/tmp/near-sha512-round-audit.log`). Reproduce the executable test with
`lake env lean --run SHA512RoundSmoke.lean`; source hashes and results are in
`results/sha512-round-lean-smoke.json`.

This closes round wiring, not full hashing. Universal assembled-witness
completeness remains to prove. The round constant and schedule word are still
inputs: their binding, schedule expansion, 80-round chaining, feed-forward,
padding, length, and byte/digest binding remain. The wide layout is a correctness
baseline, not an optimized prover benchmark. Neither a full 1 Pgas transition,
a proof below 300 KB, nor 128-bit quantum soundness has been demonstrated.


### Universal round witnesses and actual AIR traces

`SHA512RoundWitness.lean` closes the round-witness completeness gap above.
For any bounded eight-word state and 64-bit `k` and `w`, its executable witness
satisfies every round constraint and decodes to exactly those inputs. The proof
uses component completeness and exact bounded-limb uniqueness for all ten word
dependencies. `SHA512BitBinding.lean` supplies the reverse bit-to-limb binding.

`SHA512RoundTrace.lean` proves that the gadget's evaluator agrees with the actual
AIR evaluator for every constraint. Actual trace satisfaction therefore implies
the specification's full round result. Conversely, any family of bounded round
inputs constructs a satisfying isolated round trace at a legal height. These
rows are independent: no chaining or message schedule is asserted.

The executable checks compare the independent and formal constructors across
all 2,608 columns in four fixtures, evaluate actual AIR constraints on the first
and final rows, and retain the 40 coherent dependency-forgery regressions and
independent Python fixture. The full audit passes 1,032 theorem axiom closures
(`/tmp/near-sha512-witness-trace-audit.log`). Results and source hashes are in
`results/sha512-round-witness-trace.json`.

Next obligations are round-constant and message-schedule binding, round chaining,
feed-forward, padding, and byte/digest binding. This does not establish a full
hash, full Wasm execution, 1 Pgas proof, sub-300 KB proof size, or quantum soundness.


### Constrained cross-row SHA-512 state chaining

`SHA512RoundSequence.lean` adds 512 bit equalities between consecutive rounds.
These bind all eight output words to the next input state, including the two
words decoded from addition limbs. The table has 2,608 columns and 3,188
constraints of degree at most three. Actual AIR satisfaction implies exact
`SHA512.round` recurrence, and the final row is not linked cyclically to row zero.

`SHA512SequenceRun.lean` extends the one-step statement to every prefix and the
terminal output of the entire trace. The iterated inputs are the decoded per-row
`k` and `w`; this does not assert that they are the standard SHA-512 schedule.

`SHA512RoundSequenceSmoke.lean` passes two four-row traces and rejects 48 locally
valid state discontinuities (each of eight words at three boundaries in two
fixtures). It compares the independent and formal constraint layouts, checks all
eight terminal words against direct round iteration, and checks an independent
Python fixture. It also verifies final-row gating. Deliberate gap regressions
show that changing the final row's `k` or `w` is still accepted: constant and
schedule binding are not provided by state chaining. The full audit passes
1,043 theorem axiom closures (`/tmp/near-sha512-sequence-audit.log`). Results and
source hashes are in `results/sha512-sequence-lean-smoke.json`.

Next: bind round constants and schedule words, establish the 80-round block
boundary, and add feed-forward, padding and digest binding. Universal honest
sequence-trace completeness also remains. Initial-state authentication and the
full NEAR transition, 1 Pgas capacity, sub-300 KB proof and quantum-security
requirements are not established by this component.


### SHA-512 schedule expansion arithmetic

`SHA512Schedule.lean` constrains the computation of a new schedule word from
`w0,w1,w9,w14`, using two bit-operation gadgets, three modular-addition gadgets,
and sixteen limb wires. Its table has 1,776 columns and 1,804 constraints of
degree at most three. Soundness matches the actual `SHA512.nextWindow` formula;
universal witness completeness and exact four-input decoding are proved.
`SHA512ScheduleTrace.lean` connects this to actual AIR trace semantics in both
directions, for an isolated schedule-core table.

`SHA512ScheduleSmoke.lean` checks eight boundary fixtures, compares all 1,776
witness columns with an independent constructor, and rejects 32 internally valid
but incorrectly wired computations. Actual trace evaluation is checked on first
and final rows. Sixty-four software-linked expansions from seed words 0..15
match the specification and independent Python W79 = 7471377847041668307.
The independent constraint list matches the formal table. The full audit passes
1,073 theorem axiom closures (`/tmp/near-sha512-schedule-audit.log`); results and
source hashes are in `results/sha512-schedule-lean-smoke.json`.

This arithmetic core stores only the four source words needed for expansion.
The other twelve window words, temporal window links, and schedule-to-round
binding remain to constrain. A deliberate regression confirms that a valid row
with a disconnected source word still passes the isolated core. The 64-step test
supplies temporal links in software and is not evidence of their enforcement by
the AIR. Round constants, block boundaries, feed-forward, padding, digest binding,
and the full NEAR/proof-size/quantum-security objectives remain unfinished.


### Full schedule windows with temporal constraints

`SHA512ScheduleWindow.lean` adds storage for the twelve words missing from the
arithmetic core and 1,024 bit links between rows. Its full window table has
2,544 columns, 2,572 local constraints, and 3,596 constraints with temporal links,
of degree at most three. Actual AIR satisfaction implies exact specification
`nextWindow` recurrence. Final-row links vanish without wrapping to row zero.

`SHA512ScheduleWindowRun.lean` proves correctness of every prefix and of the
terminal output for the entire trace. This closes the software-only temporal
binding gap in the previous schedule-core test. A 64-row trace expands an
initial 16-word window through W79, including the final row's expansion.

`SHA512ScheduleWindowSmoke.lean` accepts two four-row traces, rejects 96 locally
valid window discontinuities (all sixteen words at three boundaries in two
fixtures), and validates a 64-row expansion trace against the specification and
independent Python W79 = 7471377847041668307. The independent constraint layout
matches the formal table, all sixteen terminal words match, and final-row gating
passes. Full audit: 1,083 theorem axiom closures
(`/tmp/near-sha512-window-audit.log`). Results and source hashes are in
`results/sha512-window-lean-smoke.json`.

Universal full-window witness completeness remains to prove. Initial message
bytes and consumption of schedule words by compression rounds are still unbound.
Round constants, 80-round block boundaries, feed-forward, padding, digest binding,
and the full NEAR/proof-size/quantum-security requirements remain unfinished.


### Combined schedule consumption and compression rounds

`SHA512Combined.lean` combines both sequence tables and adds 64 bit wires tying
the current window head to the current round's message-word input. Its table has
5,152 columns and 6,848 constraints of degree at most three. Component projection
preserves selectors and cyclic next-row semantics, allowing the existing actual
AIR proofs to compose. The final message-consumption wire remains enforced even
though the final temporal links are gated off.

`SHA512CombinedRun.lean` proves any nonempty trace segment, and the entire trace,
computes the actual specification's `SHA512.rounds` with the decoded per-row
constant list. Those constants are not yet identified with the fixed SHA-512 K.

`SHA512CombinedSmoke.lean` passes two four-row fixtures and rejects eight cases
where both component sequences are valid but the round chain consumes a different
message word. These forgeries recompute the subsequent round states, so their
rejection specifically tests the new schedule-consumption wiring. A 128-row trace
also matches the actual 80-round result at row79. With initial H0, empty-message
padding, fixed constants, the row79 endpoint and feed-forward supplied by the
test harness, the result matches Python hashlib's empty-message SHA-512 digest.
This fixture is not a proof that those surrounding steps are constrained.

Changing a round constant and recomputing the trace still passes, as expected
before constant binding. The independent layout matches the formal constraint
list. The full audit passes 1,097 theorem axiom closures
(`/tmp/near-sha512-combined-audit.log`). Results and source hashes are in
`results/sha512-combined-lean-smoke.json`.

Next obligations: constant and endpoint binding, initial message/state binding,
feed-forward, padding, digest and block chaining, and universal honest combined
trace completeness. The full NEAR, 1 Pgas, sub-300 KB and quantum-security targets
remain unverified.


### Fixed SHA-512 constants and the eighty-round endpoint

`SHA512Constants.lean` appends a 128-position phase sequence and four limb
bindings for the round constant. The first-row, transition and last-row
constraints force exactly 128 rows and a unique phase at each row. Every round
key equals `K.getD row 0`, so rows 0..79 consume the actual SHA-512 constants.
The resulting table has 5,280 columns, 7,109 constraints, degree at most three,
and maxLog7. Row79 is proved equal to the actual specification's full eighty
rounds on the decoded initial state and window, with no external constant-list
assumption. Rows 80..127 execute zero-key rounds; they are not no-op padding.

`SHA512ConstantsSmoke.lean` passes the honest 128-row fixture and rejects altered
keys at rows 0,1,79,80,127 even after the entire round-state sequence is recomputed
to satisfy the previous combined AIR. Five phase forgeries and a premature
64-row endpoint also fail. Every added constraint's field evaluation agrees
between the independent test expressions and the formal table, including their
different sum association. The full audit passes 1,110 theorem axiom closures
(`/tmp/near-sha512-constants-audit.log`). Results and source hashes are in
`results/sha512-constants-lean-smoke.json`.

This is a single compression-instance component. Initial message/state and public
output binding, feed-forward, padding, digest and block chaining remain, as does
universal honest combined/constant trace completeness. The full NEAR transition,
1 Pgas capacity, sub-300 KB proof and 128-bit quantum-security targets remain
unverified.


### SHA-512 feed-forward and single-block compression soundness

`SHA512FeedForward.lean` adds eight 64-bit addition gadgets. Their first operands
are tied to the initial round state and preserved across all rows; their second
operands are tied to the corresponding round outputs. The resulting table has
6,944 columns, 10,341 constraints, degree at most three, and exactly 128 rows.
The compression endpoint is row79; rows80..127 still execute zero-key rounds.

`SHA512WindowBounds.lean` derives Boolean window bits and bounded words from
actual AIR satisfaction. `SHA512BlockDecode.lean` decodes a 128-byte big-endian
block and proves its parsed words equal the initial schedule window.
`SHA512Compression.lean` composes these results: satisfying the actual AIR
forces row79's eight feed-forward outputs to equal `NearSpecV3.SHA512.compress`
on the decoded initial state and block. Every decoded byte is below256.
The theorem is universal over satisfying traces, not limited to test fixtures.

`SHA512FeedForwardSmoke.lean` checks two honest 128-row traces, for the padded
empty message and `abc`. Both match the actual specification and independently
computed Python hashlib digest words. Twenty-four coherent operand forgeries
are rejected: eight substituted initial words, eight middle-row changes to a
preserved operand, and eight substituted round-result words at row79. The
modified adders remain locally valid, testing the connecting constraints. The
independent full constraint list equals the formal table's constraint list.

The full audit passes 1,140 theorem axiom closures, including 30 new theorems
(`/tmp/near-sha512-feedforward-audit.log`). Source hashes and validation details
are in `results/sha512-feedforward-lean-smoke.json`. Symbolic feed-forward
identities keep the eighty-round computation opaque during proof checking.

Public initial state/message and endpoint output binding remain unimplemented.
Padding correctness, digest serialization, block chaining, and universal honest
full-trace completeness also remain. This does not establish a full NEAR state
transition proof, 1 Pgas capacity, a sub-300 KB proof, or 128-bit quantum security.


### Publicly bound SHA-512 compression

`SHA512Public.lean` binds initial state, message, and output using 128 public
16-bit limbs: 32 for the state, 64 for the block, and 32 for the result. Each word
uses four little-endian limbs; the message words preserve big-endian byte order.
Ninety-six first-row bindings fix the inputs, and 32 phase79 bindings fix the
compression output. The table adds no columns: 6,944 columns, 10,469 constraints,
degree at most three, and exactly 128 rows.

`sha512PublicClaim` explicitly requires exactly 128 public fields as well as
actual AIR satisfaction. This is necessary because the underlying AIR evaluator
defaults missing public entries to zero and ignores unused trailing entries.
The canonicality theorem proves all public limbs are below65536 and all decoded
words are below2^64. The compression theorem proves the public output equals
`NearSpecV3.SHA512.compress` of the public state and public block. No external
computational equality is assumed.

`SHA512Bytes.lean` proves canonical big-endian word serialization equals the
existing Boolean-trace byte decoder. The public block is thereby identified
with the constrained message block, with exactly 128 genuine byte values.

`SHA512PublicSmoke.lean` passes honest empty-message and `abc` fixtures against
the formal constraints. Independent binding expressions agree with the formal
ones on every row. The tests reject 256 substituted public limbs, 24 out-of-range
limbs, and two claims using row127's output. Short and overlong public lists fail
the explicit length gate; the test also confirms that unused trailing fields
pass the AIR constraints alone. Public decoders match the trace and actual
compression specification. The full audit passes 1,166 theorem axiom closures,
including 26 new theorems (`/tmp/near-sha512-public-audit.log`). Details and source
hashes are in `results/sha512-public-lean-smoke.json`.

Full-message padding, block chaining, digest serialization, and universal honest
full-trace completeness remain. No full NEAR transition proof, 1 Pgas capacity,
sub-300 KB proof, or 128-bit quantum-security result is established.


### Ordered block chains and full-message semantic binding

`SHA512Chain.lean` composes actual public compression AIR claims. Executable
boundary checks connect every output state to the next input state and bind the
exact ordered concatenation of public blocks. The proof derives each compression
equality from its AIR claim, then identifies the chain with the actual
`SHA512.blocks` function. It proves the exact block count and complete input
consumption, including the identity behavior of an empty chain.

A full-message wrapper checks the specification's padding, H0 initial state,
and digest serialization. Given all individual AIR claims and these checks,
`sha512_message_check_sound` proves equality to `NearSpecV3.sha512`. Padding and
serialization are verifier-side equalities here; this adds no AIR padding
gadget, multiblock bus, or recursive cryptographic proof. The public data and
number of instances still scale linearly with the number of message blocks.

`SHA512ChainSmoke.lean` checks four individually valid 128-row instances. An
honest two-block chain hashes the 128 bytes 0..127 and matches both the actual
specification and independent Python hashlib. Seven invalid transcripts fail
the formal boundary functions: disconnected state, changed message, reordered
instances, truncation, duplication, substituted output, and substituted initial
state. The changed-message fixture preserves valid state wiring, and both
malicious instances independently satisfy their compression constraints. A
zero-block padded-message claim and wrong digest also fail; empty-chain identity
is accepted. The full audit passes 1,177 theorem axiom closures, including 11 new
theorems (`/tmp/near-sha512-chain-audit.log`). Results and source hashes are in
`results/sha512-chain-lean-smoke.json`.

Universal honest full-trace completeness, AIR-level multiblock integration, and
cryptographic proof composition remain. This establishes neither full NEAR
transition proving nor 1 Pgas capacity, sub-300 KB proofs, or 128-bit quantum
security.


### Universal schedule-window witness completeness

`SHA512WindowInvariant.lean` proves that actual `nextWindow` preserves the
16-word length and 64-bit bounds, and gives exact shift and final-word formulas.
`SHA512ScheduleWindowWitness.lean` constructs the full 2,544-column witness from
any valid window. It proves all local constraints, including the 768 added
Boolean constraints, exact word and bit decoding, and all 1,024 temporal bit
links. The resulting trace satisfies actual `Air.Holds` for every supported
log size from 1 through 22, with no assumed local satisfaction or wire-equality
premises. Each row decodes to iteration of the actual specification's update.

`SHA512ScheduleWindowWitnessSmoke.lean` checks four 128-row fixtures (zero, maximum,
sequential, and mixed boundary words) and one two-row fixture. All 2,544 columns
match the independent constructor, and every formal constraint is evaluated on
every fixture row. Samples from the formal trace constructor agree with the
materialized trace. The mixed input's terminal window matches an independently
computed Python 128-step schedule. Forty-eight coherently reconstructed row
mutations remain locally valid but fail the temporal links at rows1,64,127.
The final temporal links remain gated.

The full audit passes 1,206 theorem axiom closures, including 29 new theorems
(`/tmp/near-window-witness-audit.log`). Results and source hashes are in
`results/sha512-window-witness-lean-smoke.json`. The supported log-size theorem
is a semantic result, not a measured runtime or memory-capacity claim.

Universal completeness of the combined round/constant/feed-forward/public
compression trace remains. Multiblock chaining and padding still use verifier
checks; no recursive cryptographic proof is added. Full NEAR transitions,
1 Pgas capacity, sub-300 KB proofs, and 128-bit quantum security remain unverified.


### Universal combined schedule-and-round witness completeness

`SHA512RoundInvariant.lean` proves bounded state preservation under actual
round iteration, supplies all round-witness input bounds, and proves the actual
H0 and K/default-zero inputs satisfy those bounds. `SHA512CombinedWitness.lean`
constructs a 5,152-column combined trace and proves actual AIR satisfaction for
every bounded initial state, valid 16-word window, bounded key stream, and log
size from 1 through 22. The constructor's decoded state, window, and key equal
the supplied inputs. Schedule, round-state, and message-consumption links are
proved at the bit level; no local satisfaction or wire equalities are assumed.

`SHA512CombinedWitnessSmoke.lean` passes two 128-row fixtures and one two-row
fixture. Every column matches the independent constructor, and every formal
constraint is checked on every row. Input/output decoding and sampled formal
trace cells agree with the materialized trace. Three wrong-message traces
recompute all subsequent rounds and satisfy both component sequence AIRs, but
fail message-consumption wiring. Eight changed state words produce locally
valid rows but fail incoming temporal links. The standard empty-message row79
endpoint plus feed-forward supplied by the test matches Python hashlib; this
combined table does not itself add feed-forward or fix the constants.

The full audit passes 1,224 theorem axiom closures, including 18 new theorems
(`/tmp/near-combined-witness-audit.log`). Results and source hashes are in
`results/sha512-combined-witness-lean-smoke.json`. Supported log sizes are formal
semantic coverage, not measured proving capacity.

Universal witness completeness for the fixed-constant phase, feed-forward, and
public binding tables remains next. Full NEAR transitions, 1 Pgas capacity,
sub-300 KB proofs, and 128-bit quantum security remain unverified.

### Fixed-constant witness completeness (1240 audited theorems)

The explicit SHA-512 constants trace now satisfies the actual Constants AIR for valid initial states and windows. Two 128-row fixtures match all 5280 independently constructed columns; five coherent wrong-key traces, five phase forgeries, and a short trace are rejected. The full audit passes 1240 theorems and boundary examples. Feed-forward/public witness completeness and cryptographic security remain separate obligations. Evidence: `results/sha512-constants-witness-lean-smoke.json`.

### Direct Wasm layered compiler and Airbender kernel experiment

The local AIR fragment now has a Lean compiler into depth-indexed arithmetic gates, with 13 new theorems preserving actual evaluation and connecting range-enforced i32.add to Wasm semantics. The full audit passes 1253 theorems and boundary examples. Exported actual Lean constraints (106 constraints, 104 columns) execute in the pinned Airbender quadratic kernel without RISC-V execution: eight honest rows pass and 832 cell mutations reject. Both paths agree on 88,192 source/polynomial evaluations. This is a compiler/kernel experiment, not a fresh GKR/WHIR proof. Rust refinement, global execution arguments, recursion and quantum soundness remain. Evidence: `results/instruction-layer-circuit-lean-smoke.json` and `results/direct-wasm-airbender-kernel.json`. Reproduce the backend experiment with `python3 airbender/direct-wasm/run_kernel.py <pinned-airbender-checkout>`.

### Direct Wasm witness commitment baseline

The actual eight-row, 104-column Lean addition witness is now committed by the pinned backend as a rate-1/4 Reed–Solomon codeword with full-round BLAKE2s. Independent Python arithmetic verifies all 3328 codeword values from the original witness using a Boolean-hypercube Mobius transform and polynomial evaluation. Python hashlib validates all 16 Merkle openings; 64 mutations to values, sibling hashes, indices or canonical field encodings reject. This diagnostic reads the whole witness: it is not a WHIR proximity proof or succinct verifier. GKR/WHIR composition, recursion and concrete quantum security remain. Reproduce with `python3 airbender/direct-wasm/run_commitment.py <pinned-airbender-checkout>`. Evidence: `results/direct-wasm-commitment-check.json`.

### Standalone WHIR opening generation and partial independent checks

The direct-Wasm witness commitment now feeds the pinned WHIR folding prover directly, without a RISC-V execution layer. A fresh eight-row opening artifact is generated with full-round BLAKE2s, two single-variable folding rounds, eight queries per round and zero grinding. These toy parameters have no claimed security level. Independent extension-field arithmetic recomputes all 104 opening claims, their batch and the initial sumcheck identity; eight base openings verify and 104 altered claims reject. Full transcript replay, intermediate oracle verification, OOD terms and final folding remain unchecked, so the artifact is explicitly marked unverified. Its 11315-byte bincode serialization is not a NEAR proof-size result. Reproduce with `python3 airbender/direct-wasm/run_whir.py <pinned-airbender-checkout>`. Evidence: `results/direct-wasm-whir-handoff-check.json`.

### Independent fixed-profile WHIR verification

The previously generated eight-row WHIR artifact now passes an independent Python verifier using only the proof and a trusted root. It reconstructs statement/transcript challenges, batches the claims, checks both sumchecks, incorporates OOD and in-domain contributions, verifies the base/intermediate Merkle paths and query indices, checks final leaf folding and evaluates the final sumcheck. No witness or complete codeword is used. 286 negative cases reject, including recomputed handoff metadata for a false claim and a sumcheck mutation preserving its first identity. This is an experimental verifier for one fixed toy schedule, not a formally verified WHIR implementation or security certificate. Its opening claim still needs connection to a GKR constraint proof, and no full NEAR execution is proved. Evidence: `results/direct-wasm-whir-verified.json`, `results/direct-wasm-whir-negative-tests.json`. The existing `run_whir.py` runner now reproduces these checks as well.
