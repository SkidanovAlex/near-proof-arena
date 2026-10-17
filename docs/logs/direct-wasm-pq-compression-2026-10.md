# Direct Wasm and hash-based compression research — 2026-10-15

This checkpoint belongs to the long-term PQ/recursion research track. It does
not change a signed challenge, its measurement rules, or the frozen oracle.
The current user target is a complete NEAR state transition at 1 Pgas with a
proof below 300,000 bytes and a machine-checked correctness/security argument.
That target is not achieved.

Worktree: `research/direct-wasm-whir`, based on main
`9116a4da95f2d17cfddecc1618ccc0daaa9ba37d`. The research implementation and
evidence live under `research/near-compression/`. Main's D1 phase-2 semantic
obligations in `v3-d1-phase2-2026-10.md` remain separate obligations; generating
a proof of the 33-table AIR does not discharge them.

## Measured complete diagnostic proof

The SHA-384 profile commits all source roots before bus challenges, generates
fresh auxiliary witnesses under those challenges, commits auxiliary roots and
finals before table mixing, and verifies table constraints, cyclic-next
reductions and global bus fingerprints. It uses Q8/BabyBear Ext4 diagnostic
parameters. Neither exact natural bus balance nor 128-bit quantum security
follows from these tests alone.

The first complete binary was 1,151,130 bytes. Joint openings reduce obligations
at different points and with different degrees to one folding chain. The
resulting complete binary is **522,596 bytes**, including source commitments:

| Component | Bytes |
| --- | ---: |
| AIR, roots, bus finals and claim vectors | 256,422 |
| Joint opening length | 8 |
| Joint reduction, fold headers and terminal | 2,614 |
| Original source leaves and authentication | 218,320 |
| Shared later-fold leaves and authentication | 45,232 |

The statement, source roots and AIR reductions were compared to the previously
verified workload. Exact binary roundtrip and fresh-process verification pass.
The full workload rejects 259 semantic/binding mutations; both reference and
shared binary verifiers reject 178 transport/authentication mutations.
These tests are not soundness bounds. Evidence:

- `results/pq384-joint-bus-d1/integration.json`
- `results/pq384-joint-bus-d1/binding-regressions.json`
- `results/pq384-shared-joint-codec/report.json`

Authenticating each shared Merkle stage once reduces reference joint binary
verification from 76,228 to 42,972 SHA-384 compression blocks. These are measured
software operation counts, not recursive circuit constraints or proof timings.
Evidence: `results/pq384-joint-verifier-work.json`.

## Formal semantics and security boundaries

The latest audit at this checkpoint passes 1,758 declarations. The bounded Wasm
slice now derives actual outer `runCall` and published stack/gas/error status
from source AIR, exact `HoldsP`, and an executable eligibility checker. The
checker runs actual preparation, loading charges, linking, method resolution,
instantiation and function lookup. Preparation is still verifier-side. This
slice retains 16 code slots and eight i32 stack slots; it excludes start
functions and curve imports, and uses `real = none`. It is not full Wasm/NEAR.

Five actual-byte fixtures pass; 905 setup/input mutations and 35 output-relation
mutations reject. The executable smoke does not itself test AIR acceptance.
Evidence: `PreparedRunCallSmoke.lean`, `results/prepared-run-call-smoke.json`.

For folding, checked results include exact query-chain mass accounting,
weighted consistency projection/gating, polynomial normalization/interleaving,
and the actual coefficient residual equation. `WeightedFoldComposition.lean`
composes one weighted fold **conditional on** `WeightedFoldExtraction`.
That contract is an explicit unproved hypothesis, not an axiom or a proved
concentration theorem. Its quantifiers permit challenge-dependent next oracles
and candidates. Merkle binding, finite-field instantiation, nonlinear extraction,
joint initial batching and QROM compilation remain open.

## Next measured changes

Root reproduced an expected-Q8 packing sweep: 39,990.72 bytes saved in the joint
opening, maximum degree reduced from 262,144 to 131,072, and padded coefficient
slots halved. A new proof with new commitments and fresh auxiliaries is needed
to measure actual bytes. Evidence: `results/pq384-joint-packing-analysis.json`.

Root also reproduced a public-constant-folded and balanced terminal circuit:
81,176 live nodes, depth 41, and 152,565 nodes after relay accounting. Its outputs
match the canonical evaluator on all 33 tables. A prospective layered GKR proof
is estimated at 35,296–41,616 bytes, **excluding** final input-opening machinery.
No GKR proof or compiler-refinement theorem is established by that analysis.
Evidence: `results/pq384-terminal-circuit-analysis/report.json`.

Next work is actual optimized packing, a terminal-circuit prover with bound input
queries, scalable authenticated code/stack tables, and the missing nonlinear
weighted extraction theorem. Full state-transition coverage, secure parameters,
recursion, the 300,000-byte bound and the 1 Pgas benchmark remain required.

## Later checkpoint: actual optimized packing

The optimized complete joint proof independently verifies at **510,836 bytes**,
a saving of **11,760 bytes** on the same source rows, AIR, public inputs and
row schedule. All source commitments were regenerated and auxiliaries were
generated under the new challenges. Expected savings were 39,990.72 bytes;
actual transcript-dependent Merkle overlap differs. No selective retries were
used. Root verified the fresh 33-table proof, exact joint binary roundtrip and
shared verifier. Evidence: `results/pq384-optimized-joint-bus/integration.json`.

The balanced terminal circuit also passes 231 independent table-output checks
over original, zero, one and four arbitrary Ext4 input vectors. These tests
support implementation review, not a formal compiler theorem.
Evidence: `results/pq384-terminal-circuit-analysis/differential.json`.

Further formal results decompose accepted global queries into a concrete
false-to-true candidate transition and provide a finite interactive union
bound with a separate conditional bound at every prior transcript. They do
not turn an interactive bound into a Fiat–Shamir or QROM bound.


### Scalable CODE-table complete diagnostic integration

Root regenerated the actual Lean prepare/step fixture and matched all fixture JSON,
then regenerated and matched the 193-instruction spec and both traces. Numeric PCs
and an authenticated CODE table remove the old CODE16 limit; stack depth8 and the
const/add/drop/end instruction subset remain. Both tables have256 rows.

The complete SHA384 global-bus proof independently verifies. Binary transport is
121,982 bytes including source commitments; exact roundtrip, shared verification,
fresh-process verification and18 altered-proof/public-input rejections pass.
Public CODE is outside this proof:4,891 public elements (19,564 bytes at fixed u32),
and the current full AIR/public/shape statement JSON is223,788 bytes. These figures
must not be presented as full NEAR,1Pgas or128-bit quantum-secure results. The new
CODE-table semantic refinement is pending; previous CODE16 theorems do not cover it.

Artifacts:research/near-compression/results/pq384-code-table-long193/.
Agent prototype evidence also records704 negative cases and exact Lean/Python
parity for1,069,948 residuals and4,462 interactions; root did not repeat that entire
sweep. Root integrated the frozen exporter, AIR generator and replay/test sources.
The prior indexed-fold full audit passed1,768 checks.


### GKR reduction integration and obligation review

Integrated the frozen terminal GKR, dual-Mobius coefficient-weight mapping and
small test suite. Root reproduced72 algebra checks and40 negative checks. Added
32 independent constant/padding/private-obligation cases: direct DAG evaluation
agrees with the layered circuit, public constant mutations reject, and changing a
nonzero-weight private slot violates the mandatory final linear-functional claim.
Root independently verified the actual41-layer reduction against its public
circuit without loading witness values. Its35,680 field-message bytes exclude
framing and the mandatory PCS opening. The current circuit uses fixed analysis
rho; it does not establish random aggregation of all AIR terminal claims. A new
transcript profile and generalized PCS integration remain required. No whole
protocol or quantum-security claim follows from these tests.

Artifacts:research/near-compression/results/pq384-terminal-gkr/ and
results/pq384-terminal-circuit-analysis/gkr-obligation-review.json.


### CODE uniqueness and repeated-query formal integration

Integrated eight PreparedCodeOrder theorems. From actual TableLocal plus literal
constraint membership, Boolean/limb bounds and two-limb carry equations imply
active-row PC equals the natural row index; active CODE keys are injective.
Root exported and exactly matched all233 source expressions against the actual
Python CODE AIR. This is an executable AST parity check, not a verified parser.
The exact natural-bus fetch/authentication bridge remains in progress.

Integrated six IndependentQueryBudget theorems. Exact Cartesian counts include
repeated queries and q=0. The conditional interactive budget combines adaptive
round errors with (B/|Q|)^q for nonempty sampling alphabets. This does not supply
the nonlinear extraction bounds, cryptographic oracle binding or QROM compiler.
Full root audit passes1,782 checks. Evidence:results/code-order-query-integration.json.


### Dynamic GKR terminal compiler review

Reviewed the new all-zerocheck → fresh terminal batching → GKR → mandatory
weighted PCS path in the protocol worktree. Root differential test replays its
small two-table public transcript, then checks the newly compiled aggregate DAG
against independent canonical AIR evaluation for20 combinations of private
inputs and rho(actual transcript,zero,one,random). All pass; compiler SHA256 is
recorded in results/pq384-terminal-gkr/dynamic-compiler-review.json. Constant-only
compiler outputs now receive an explicit relay layer, avoiding a zero-layer
verifier edge case. No formal compiler correctness claim is made. The new full
profile and its compact codec remain pending root integration and verification.


### Authenticated numeric-PC fetch and fixed-curve concentration

Root integrated11 PreparedCodeBus theorems. Under actual HoldsP for the concrete
2-table/4-bus skeleton and literal CODE constraints, the decoded EXEC PC selects
an active CODE row; its25-field descriptor equals the fetch and a public CODE
record. Every active matching row has that same index. Multiplicity/balance are
natural counts, not field aggregates. Actual prepare-to-public provenance and
new execution-table refinement remain separate obligations.

Root source comparison passes for all5 interactions,3public segments,table shapes,
25inactive-count expressions and29export-added multiplicity Boolean expressions.
The latter come from HoldsP.bits and were explicitly checked before comparing the
parameterized skeleton. The source comparison is executable evidence, not a
verified parser/exporter theorem.

Integrated3 SharedCurveConcentration theorems: for one fixed candidate curve,
more than domain.length distinct successful challenges preserve the exact
weighted threshold;3residual successes give the formal quadratic identity when
sent.DegLt3. Shared-curve extraction from adaptive candidates remains unproved.
Full audit passes1,796checks. Evidence:results/code-bus-concentration-integration.json.


### Complete33-table GKR-plus-opening diagnostic:318,996 bytes

Integrated the frozen new protocol, dynamic compiler, runner and shared-path
binary codecs. The new chronology commits sources and fresh auxiliaries, finishes
all zerocheck messages, draws a fresh terminal batching challenge, runs GKR and
verifies the mandatory weighted polynomial opening. It no longer discloses the
current/next/final column vectors. Static AIR/config and fixed-width public/shapes
are bound by a new statement digest/profile. Source roots, source trace hashes,
AIR, public input and row/packing schedule match the previous optimized run.

Root fresh-process JSON and binary verification PASS. Root independent compiler
checks pass20 cases on all33tables;7whole-profile changes reject (missing/empty
opening, source leaf, final GKR input, last-table constraint, public input, source
root). Agent exact binary roundtrip/fresh verification and2full binary mutations
also pass. Full proof318,996 bytes includes1,584 source commitment bytes and all
framing. Prior optimized diagnostic510,836 bytes. Remaining to300,000:18,996 bytes.
Breakdown:28,086 prefix;35,680 GKR;8frame;2,470 openingheader;28,864 sourceleaves;
181,632 sourcesiblings;3,904 foldleaves;38,352 foldsiblings.

Full agent run259.17s,peak490,056KiB, fresh verifier7.972s. These are prototype
measurements, not full NEAR or1Pgas throughput. Q8/Ext4 remains diagnostic; GKR,
weighted joint opening, concentration and QROM composition are not certified.
Artifacts:results/pq384-gkr-bus-full and results/pq384-gkr-bus-codec-full.


### Stricter-regime adaptive extraction and lossless coefficient algebra

Integrated WeightedThreeCandidate:4theorems prove adaptive candidate alignment
and weighted extraction under2W+B(D−1)<3T, whereWis total point weight andBis its
pointwise cap. Two candidates reconstruct a curve; weighted triple intersection
and RS uniqueness force every other successful candidate onto it. The integrated
fixed-curve theorem then preserves the original threshold and derives the formal
quadratic residual identity. This stricter theorem no longer assumes nonlinear
concentration. Actual indexed domain/cap/mass instantiation is still in progress;
it is not full protocol or quantum security.

Added SumcheckLinearCodec:3theorems prove exact recovery of c1 from endpoint claim,
c0 and higher coefficients, over any field; this supports lossless wire omission
but does not formally refine the Python parser. Root audit passes1,803checks.

Exact conditional query-tail sensitivity: if good-transcript accepting fraction
is bounded by3/4, the query term requires309queries for2^-128 and617for2^-256.
Q8 gives upper-bound term6561/65536. These are not selected security parameters;
other errors and QROM losses are excluded. See results/unique-regime-query-tail.json.


### Actual prepare provenance and existential extraction count

Integrated8 PreparedCodeProvenance theorems. Executable checker obtains the real
prepared/resolved function from preparedRunCallSetup, validates all25 CODE fields
and canonical count/length, then composes exact natural-bus fetch to identify a
live actual instruction and gas entry.32-bit PC replaces the old16instruction cap.
Root reran7real fixtures: all public fields match the Lean builder;6,173bad cases
reject. This is provenance, not the full new EXEC step/refinement theorem.

Integrated2 WeightedUniqueExtraction theorems: successful candidates remain
existential inside the challenge count; outside a constructed valid outcome,
at most max(domain.length,2) distinct challenges succeed under the stricter
separation and quadratic-degree conditions. Full audit passes1,813checks.

Added query-cost sensitivity for the actual66branch GKR layout. Exact occupancy
expectations validated on12small exhaustive cases yield expected full transport
~310,067B atQ8,~3.85MB atQ309,~6.14MB atQ617. Higher counts illustrate only the
conditional(3/4)^q tail; field size and other soundness losses are unchanged, so
these are NOT secure proof sizes or selected parameters. Hash authentication
dominates. Reaching300,000B under certified parameters requires further protocol
or recursive-verifier work beyond lossless serialization. Evidence:
results/pq384-gkr-query-cost.json and pq384-code-table-long193/provenance-smoke.json.


### Lossless diagnostic transport under300,000 bytes

Compact transport is298,961 bytes, saving20,035 from318,996 and leaving1,039bytes
below the decimal300,000 target. Includes1,584sourcecommitment bytes and framing.
It omits954recoverable linear coefficients, packs canonical field words in31bits,
uses canonical zero tags for leafwords and reconstructs the constant terminal
root/openings. No prover rerun, changed root, changed transcript or query retry.
Root fresh-process binary verification PASS; independent root decode exactly
equals the original full proof JSON. Root independent bit-list reference matches
100mixed field/raw/alignment cases. Agent reports80bit roundtrips,3primitive
negative checks and2full-proof negative checks. SHA256:
f3788eec6c02371bbdf417199f2ed2a367e1c883a0d2d78af10c535579c21e8e.

This satisfies ONLY a diagnostic transport milestone. Q8/Ext4, fullNEAR1Pgas,
whole new EXEC refinement and128-bit quantum security remain unachieved. Higher
query authentication cost motivates full recursive-verifier work; agent now
measures actual GKR-verifier hash/arithmetic costs before new transcript work.
Artifacts:results/pq384-gkr-bus-compact-full/{proof.bin,report.json,root-review.json}.

Integrated4 FiniteIndexTransport theorems: finite injective field-point maps
preserve distinctness, weighted events and total mass exactly. Full audit passes
1,817checks. The indexed extraction instantiation is next for root review.


### Indexed extraction assumption discharged in stricter regime

Integrated IndexedUniqueExtraction2theorems: actual IndexedFoldExtraction and
indexedFoldBad count≤max(N,2) are proved from finite child-domain injectivity,
distinct challenge alphabet, point cap, sent polynomial degree<3 and exact
weighted separation. No extraction hypothesis remains in this theorem.
Integrated GlobalChainWeightBounds4theorems: actual recursively gated weights
have cap2^stage; projected pairs have cap2^(stage+1), mass≤initial domain size.
All adversarial gates are allowed. Full audit passes1,823checks.

Conditional arithmetic for the measured profile: initial degree131072,initial
domain524288,17folds, sum of these per-stage error counts524284. Dividing by
2013265921^4 gives an isolated interactive extraction bound certifying104integer
bits, insufficient to certify128bits by this route. Extension degrees5/7/9 are
arithmetic minima for this term alone at128/192/256bits. They are not implemented
field selections and exclude other soundness errors, sampler refinement andQROM
losses. Evidence:results/indexed-extraction-field-budget.json. This reinforces
that the298,961B diagnostic result is not a128bit secure proof-size result.


### Recursive-verifier work profile independently reproduced

Root reviewed/integrated profile_pq384_gkr_verifier.py and reran the exact actual
33table proof and298,961byte compact transport. Every profiler count matches the
agent run. Expanded verifier:86,662SHA384 compression blocks,13,700hash calls,
2,990,519Ext4 multiplications. Compact decode/authenticate/verify:151,459blocks,
23,804calls due to repeated replay/authentication. These are operation counts,
not circuit gates or recursive proof measurements.

Largest expanded hash costs: generated GKRlayout27,502blocks, Merkle nodes26,203,
staticAIR13,441, derivedweightJSON3,523. New separately versioned seed-bound profile
is under development to bind deterministic derived data via its full transcript
inputs instead of serializing/hashing it repeatedly. It must retain complete
statement/compiler binding; oldprofile and its measured proof remain unchanged.

Existing SHA512PublicTable (6,944columns,128rows) and SHA512Compression/Chain/Bytes
formal modules are available for a SHA384-IV compression fixture. Root owns this
next actual hash-prover baseline; no SHA384 recursive circuit completeness is
claimed from the SHA512 modules alone. Profile evidence:
results/pq384-gkr-verifier-work.json.

Integrated GlobalChainUniqueRegime2theorems: one condition2*N0+D0<3*T discharges separation at every actual halving stage, giving indexed bad-count≤max(childSize,2) with no extraction assumption. Domain/root injectivity and degree certificates remain explicit. Root audit passes1,825checks.


### Actual SHA384-IV compression proving baseline

Added SHA384CompressionFixture.lean using the existing proved SHA512 compression
AIR and formal combined witness constructor. Fixed empty/abc one-block fixtures
use SHA384 IV; all formal AIR constraints evaluate to zero and source compression
matches. Independent Python hashlib.sha384 comparison of the first6output words
passes both fixtures. This does not prove a general SHA384 padding/truncation or
recursive verifier refinement.

The empty fixture now has a complete SHA384 hash-based global-bus proof, fresh
JSON verification, exact binary roundtrip and fresh binary verification. Binary
367,492bytes with the older full-column transport; this is not the compact GKR
profile. Three public mutations (IV,block,output) reject. Table6,944columns×128rows.
Measured native stages:zerocheck0.404s,shift0.255s,openings0.677s; commitment and
other setup are separate in report.json. The block is public; no privacy claim.
Artifacts:results/sha384-compression-baseline. Full recursion still needs batching,
framing/padding bindings, all verifier arithmetic and certified soundness.


### Composed ideal fold count and EXEC source adapters

Integrated InteractiveUniqueFoldSoundness: literal ideal challenge-transcript×query
accepted-count bound with adaptive prefix snapshot causality, quadratic messages,
actual geometry/residual/terminal certificates, and initial candidate absence.
No extraction hypothesis remains under2*N0+D0<3*T. This version requires certified
completed transcripts at all sampled leaves; rejecting/aborting implementation
refinement remains explicit and is being addressed separately. No commitment,
initialAIR reduction orQROM conclusion follows yet.

Integrated PreparedExecAdapter7theorems and PreparedExecPC3theorems. The adapter
proves local Expr substitution and zero/one normalization, selected stack operand
arithmetic, and natural numericPC transitions; ghost oldPC selectors do not impose
a bound on actualPC. Exact normalized AST comparison matches34expressions spanning
SP,depth,status,carry,subtract,gas,stack and numericPC constraints. No arbitrary
polynomial reassociation or whole-trace equivalence is assumed. Full new EXEC
step refinement remains in progress. Root audit passes1,836checks.


### Seed-bound profile independently integrated and measured

Reviewed the deterministic dependency chain: configuredAIR/compiler, canonical
public/shapes, source+freshaux commitments, all zerochecks and freshrho determine
the compiledGKRlayout; finalGKRseed determines the mandatory PCS parent and
verifier-derived input weights. No arbitrary caller-selected circuit/weights
soundness is claimed for the low-level helpers. Integrated6newfiles, exact frozen
hashes checked. Root fresh33tableverify PASS with identical trustedstatement and
source roots. Root profiler reproduces all agent counts exactly:41,542SHA384blocks
per proof versus86,662old; configuration13,442 separately, total54,984.
Ext4mul remains2,990,519. This reduces hash work, not all recursive arithmetic.
Newprofile has no measured compactbinary yet;298,961B belongs to previousprofile.
Artifacts:results/pq384-seed-gkr-bus-full and pq384-seed-gkr-verifier-work.json.

Integrated CheckedInteractiveFoldSoundness3theorems. Actual checked acceptance
rejects invalid prefixes/terminal checks even forq=0. The ideal Cartesian count
bound now permits rejected/aborted branches, with no all-leaves-valid or extraction
premise. Initial candidate absence remains external on check-passing paths;
commitment, initialAIR/GKR/virtualsource reduction andQROM remain open. Root audit
passes1,839checks.

## EXEC interpreter and initial virtual-oracle integration

Integrated PreparedExecTransition (9), PreparedExecWasm (4), and WeightedVirtualInitial (7) after source review. Full `check.py` passes 1,859 public theorems with only the standard allowed axioms. Exact source parity now checks 36 normalized expressions, all 605 Boolean constraints, and absence of first-row selectors in matched source constraints. These include the const/drop depth guards.

The interpreter bridge supplies add/const/drop local steps without the old real-PC limit, but authenticated code/gas/state composition and whole execution remain open. The virtual-oracle theorem discharges the actual initial candidate predicate only under a fixed jointly close tuple and wrong residual. It does not establish joint proximity from per-lane proximity or commitments. Agent analysis found equal-weight cancellation obstructing an unrestricted far-source extraction statement; this is not yet a false-claim protocol attack.

Evidence: `results/exec-virtual-integration.json`, `results/weighted-virtual-initial-reduction.json`, and `results/pq384-code-table-long193/exec-adapter-parity.json`. No full-goal completion or quantum security claim.

## Framed SHA384 and EXEC gas integration

Reviewed and integrated the actual 376-byte Merkle-node hash chain: four canonical SHA512 compression traces with SHA384 IV and 48-byte truncation. Root independently regenerated all Lean traces, matched each public claim and exact binary decode, freshly verified the complete chain, reproduced the source-verifier capture, and rejected 16 boundary mutations. `NearCompression/SHA384Chain.lean` now contains the audited chain theorem. Evidence: `results/sha384-framed-chain/root-review.json`. The 1,478,464 bytes are the sum of four transported block proofs, excluding outer framing/public statement. This is not compression or a recursive verifier; padding and links remain external checks.

Integrated PreparedExecGas: six theorems derive exact limb subtraction/borrow, successful gas debit, exhaustion freeze, and authenticated prepared fee metadata from CODE provenance. Combined audit passes 1,866 public theorems. Source checks include eight literal gas AST memberships in addition to prior normalized constraints and 605 Boolean memberships. Whole-call state composition remains open.

## Authenticated EXEC state step and structured batching obstruction

Integrated PreparedExecState (3) and PreparedExecStack (3): authenticated addition now composes actual HoldsP, CODE provenance, instruction decoding, fee/gas, arithmetic, and numeric-PC update into actual Wasm.step. Const/drop now have authenticated immediate decoding and TableLocal wrappers. Current-state interpretation/function lookup still explicit; post-state SP/DONE closure, terminal cases, whole-call induction and formal instantiation of source certificates remain open.

Integrated StructuredBatchKernel (7). Independently reproduced both weighted-joint profiles using committed X^128 and -X^128 on 512 points, with equal nonzero lane weights. Both accept the true zero claim and reject a changed claim of one. Formal distance proves the lanes cannot be jointly close to degree<128 polynomials, despite exact scalar cancellation. Thus universal joint-source extraction is false; this is not a false-claim attack. The corrected research contract must use one representative fixed across randomness and ALL AIR/GKR/bus opening obligations, or introduce separately analyzed vector proximity. Per-opening representatives alone are insufficient.

Combined audit passes 1,879 public theorems. Evidence: `results/state-stack-kernel-integration.json`, `results/structured-batch-kernel/root-review.json`, and `results/structured-batch-kernel-obstruction.json`. No complete NEAR, secure-parameter, or recursive compression claim.

## Addition state closure and hash reuse measurement

PreparedExecClosure (7) now proves full next-row PreparedExecState preservation for authenticated successful addition, including derived next stack pointer and DONE=FAIL=0. Full audit passes 1,886 public theorems. Source checks cover 45 expressions, 605 Boolean memberships, eight literal gas expressions, and the literal SP-choice expression. Const/drop closure, terminal cases and whole-call induction remain open.

Measured the unchanged configured seed verifier with exact full-input hash-call keys: 13,698 calls, 11,181 distinct inputs; 41,542 SHA384 compression blocks, 32,587 needed for distinct inputs. Thus 8,955 blocks (21.6%) are repeated computation. Every per-tag total agrees with the earlier independent operation profiler. This is a potential recursive DAG optimization, not an implemented cached verifier or gate estimate: all reused inputs/outputs must be constrained equal, routing costs excluded. Evidence: `results/pq384-seed-hash-reuse.json`.

Next applicability task: generate a literal Lean table from canonical JSON, export it back for exact parity, and construct source certificates with kernel-checked finite membership proofs. This closes the distinction between generic conditional source theorems and the actual exported EXEC/CODE tables.

## Concrete literal tables and shared functional representative

Generated `NearCompression/PreparedLiteral.lean` from canonical executable ASTs, with individually named expressions for source-membership certificates. It compiles in Lean. Exact full exported parity passes for 726 EXEC and 473 CODE user constraints, 29 automatic multiplicity constraints, all five interactions and all public segments. The comparison uses code length193; constraints and interactions are independent of this public-length parameter. Evidence: `results/prepared-literal-parity.json`. Source-certificate construction is the next formal applicability step; this comparison is not a verified parser theorem.

Integrated FunctionalBatchRepresentative (8): functional equivalence preserves each requested coefficient functional; one fixed tuple shared across all obligations/challenges suffices for scalar-candidate uniqueness and noInitialCandidate under explicit proximity/residual assumptions. Far-case existence/extraction, exact sparse-lift/GKR correspondence and global AIR assignment remain open.

Integrated SHA384MultiBlock's compression projection theorem (1). The new fixed-length table definitions constrain message/padding bytes, SHA384 IV, final digest and tagged intermediate-state bus messages. Full bus-to-chain semantics and independent fullproof review remain outstanding. Combined audit: 1,895 public theorems pass.

## Terminal semantics, multiblock proof review, and vector extraction

Integrated PreparedExecStackClosure (2) and PreparedExecTerminal (3). Authenticated const/drop preserves the next state; exhaustion derives actual failure gas/error with explicit no-host gas context; end derives actual final-frame return with explicit label context. All use actual CODE/fee provenance. End-depth source parity passes, for 46 checked execution expressions. Whole-call entry/induction and concrete source certificates remain open.

Root regenerated the canonical multiblock AIR from the captured message, reused its independently generated compression traces, and reproduced full verification, exact binary roundtrip, 75,776 boundary checks and 12 negatives. Binary is 1,508,054 bytes including source roots, excluding the public statement. Public inputs contain 424 byte-valued field elements. This moves full-message checks into AIR, not recursive compression. Full bus-to-chain semantic theorem remains open, including tag injectivity under an explicit block-count < field modulus bound. Evidence: `results/sha384-multiblock/root-review.json`.

Integrated VectorAffineExtraction (3): joint vector concentration, adaptive candidate extraction and finite bad-count ≤max(domain length,2), preserving the same threshold/degree/weight cap independently of vector dimension under the stated separation. Multi-coordinate recurrence, residual/shared-assignment composition and cryptographic/QROM binding are not proved by this lemma. Combined audit passes 1,903 public theorems.

## Literal source certificates and tensor far-source bound

PreparedLiteralCertificates (10) passed root kernel build and axiom audit. Boolean, CODE ordering/inactive multiplicity, PC, gas, local transitions, closure, const/drop and end guards are now formally instantiated against PreparedLiteral's exact ASTs with ordinary decide and a computable recursive noFirst decision instance. No native_decide/parser trust added. Entry/public-boundary composition and whole-call induction remain open.

VectorTensorExtraction (3) passed review and audit: finite-grid success count for a fixed tensor without a joint low-degree representative is bounded by n*max(N,2)*|S|^(n-1). The per-coordinate threshold, degree and cap do not deteriorate. Exact actual beta contraction, common original-lane reconstruction and residual/global-AIR composition remain separate obligations. Combined public audit: 1,916.

Exact conditional arithmetic for current N=524288,n=17 gives tensor numerator8912896 and fold numerator524284, sum9437180 over p^4. This isolated union supports100integerbits, not128; minimum extension degrees for the isolated128/192/256 targets are5/7/10. These exclude query tail, all other algebraic/commitment/sampler errors and QROM losses and are not parameter certification. Evidence: `results/tensor-security-accounting.json`.

Main alignment recheck: local main44b2891196883ca980b7341b480502f56cb88403 is an ancestor117commits behind research base9116a4da95f2d17cfddecc1618ccc0daaa9ba37d. The requested D1 logs exist at the research base but not that older main ref. No downgrade/rebase/ref mutation was performed; contribution must preserve the newer D1 dependencies.

## Exact SHA384 padding bridge and recursive hash layout cost

Root proved SHA384Padding: exact general padded length, every padded byte (message, marker, zero region and 16-byte big-endian length), and equality of the corresponding AIR expression evaluation to the actual NearSpecV3.SHA512.pad byte under explicit public-message binding. Three public theorems pass the combined1,919theorem audit. Private list/byte lemmas reproduce existing generic helpers without importing the unrelated SHA256 pipeline. This is the missing padding interface for the ongoing full multiblock semantic composition, not by itself the full hash theorem.

Exact accounting using measured configured seed-verifier calls and current canonical128×6944 SHA384 block layout yields147,695,435,776bytes (137.55GiB) of dense u32 source trace, or115,857,473,536bytes (107.90GiB) with all identical hash inputs shared. These are data-volume products, not peak RAM, gate count, timing, or secure proof-size estimates. They excludeFFT/aux/commitments, nonhash verifier arithmetic, trusted setup and secure parameter changes. Evidence: `results/recursive-hash-trace-accounting.json`. Width/row reduction and reusable call routing need priority after semantic correctness.

## Actual literal-AIR execution run and shared lane reconstruction

Integrated SharedLaneInterpolation (7): weighted mass is converted to at leastD distinct common points, and the SAME points interpolate every original lane. Every compressed row then equals its corresponding polynomial linear combination by degree/root uniqueness. No individual source proximity is asserted, and pre-GKR witness timing is not inferred from post-GKR weights.

Integrated PreparedExecContinue (3) and PreparedLiteralRun (2). Literal AIR plus checked PFunc and an interpreted active state implies actual Wasm.run terminates within the remaining trace-height fuel. Success preserves real gas context; terminal witnesses retain the actual preterminal state, exact fin/abort result, synchronization, and terminal-row flags. No assumed transition certificate. Scope remains single function, stack8, const/add/drop/end; entry/public header and final public output/padding remain separate.

Added sha384_word_bytes to the padding module, connecting actual big-endian8byte serialization to the compression semantics' decoded word bytes. Combined audit passes1,932publictheorems. Evidence: `results/literal-run-interpolation-integration.json`.

## Exact 27-field public boundary authentication

PreparedExecBoundary (5) now proves actual natural bus balance binds complete27field entry/exit records, while CODE buses2/3 cannot discharge boundary traffic. Four independently authenticated gas limbs reconstruct the exact64bit value. The count checker explicitly requires one public record on each boundary bus. Combined audit passes1,937publictheorems.

Root independently compared publicheader gas and counts to all7existing actual prepare/step/runCall fixtures, including exactgas andexhaustion: entry/exit gas matched and allgaslimbs canonical16bit. Evidence: `results/exec-boundary-integration.json`. This does not yet construct the initial AIR state from actualenter or link terminal state throughpadding tofinalpublicoutput; those remain under development.

## Structured beta extraction and actual outer runCall

StructuredWeightTensor (9) connects genericRowMLE-derived lane weights exactly to tensor contraction, reconstructs one original tuple and proves a far-family adaptive-candidate count bound. A shared Boolean agreement set works at every later point. Multiple obligations require simultaneous joint agreement; single opening is the Unit specialization. Concrete sparse-lift/current-next weight implementation mapping, weighted-sumcheck composition and pre-GKR witness timing remain open.

PreparedLiteralEntry (3) and PreparedLiteralRunCall (2) derive initialrowState from actualenter plus executable27field/prologue checks, then actual outerrunCall from actualprepare/loading/link/resolve/instantiate. Preparation is computed verifier-side; this is not a PREPAIR proof. No caller-supplied initialrowgas/executioncertificate is required. Root smoke accepts7real fixtures and rejects91entryheader/functionindex mutations. Finalpublicoutput binding throughDONE padding remains open. Combined audit:1,951publictheorems. Evidence: `results/entry-structured-integration.json` and `results/literal-entry-smoke.json`.

Agent reports completed full multiblock SHA384 semantic theorem; pending root source review and integration. It is not counted or claimed as integrated here.

## Full SHA384 message semantics and checked weighted sumcheck integration

Root reviewed and integrated SHA384MultiBlockSemantics (26 public theorems), then authored SHA384Message (3). Actual multiblock HoldsP with the concrete message-plus-digest public layout implies the actual SHA384 digest equals the public 48-byte digest, under the explicit block-count < field-modulus bound. Padding, IV, compression, state linking and digest extraction are derived from the AIR; they are not caller correctness assumptions. The fixture now uses the proved public layout; independently regenerated canonical statement is unchanged. This completes the hash AIR semantic bridge, not cryptographic proof acceptance or QROM soundness. Audit passed 1,980.

Root also reviewed and integrated AdaptiveWeightedSumcheck (8), WeightedSumcheckTerminal (8), and PreparedExecPadding (6). Checked adaptive sumcheck has an exact finite challenge-path error bound; its initial dot is the coefficient-table functional and actual lane folds give the terminal weighted MLE expression. The equality-weight residual join and full folding composition remain open. DONE padding preserves the literal execution snapshot through arbitrary suffix length; final public-output composition remains in progress. Combined audit passes 2,002 checks. Evidence and source hashes: `results/hash-sumcheck-padding-integration.json`.

## Verified column quotient and equality-weight bridge

ColumnQuotient (8) and ColumnQuotientSHA384 (1) prove that rewriting every constraint and interaction through a column map preserves original HoldsP and SHA384 digest semantics. Root reviewed all seven frozen source files, copied the implementation/artifacts, and independently reran binary verification against the root original canonical SHA384 AIR plus six negative cases. The 4-block proof is 1,390,406 bytes (117,648 bytes below 1,508,054); width is 6,336 instead of 6,944, with no constraints removed. Evidence: `results/sha384-column-quotient/root-review.json`. Agent preparation evidence additionally checks all honest witness cells and arbitrary invalid expression assignments; root has not separately rerun that preparation script.

EqualityWeightResidual (3) proves the exact little-endian equality-weight residual equals the coefficient MLE without degree or nonzero-factor assumptions. Combined audit through these integrations: 2,014. Full adaptive sumcheck/folding composition remains in progress. The column quotient remains a diagnostic proof; its dense deduplicated hash source estimate is still 98.45 GiB, excluding auxiliary/FFT/commitment costs. Next optimization work targets endpoint-only feed-forward and batched rounds, not a claim of practical recursive proving yet.

PreparedExecPublicOutput (6) is root reviewed and integrated. Exact exit bus and DONE suffix now publish final status, fast gas, canonical SP and live i32 stack, conditional on PreparedExecFinalRow at the first DONE row. The remaining TerminalWitness-to-FinalRow bridge is actively under development. PreparedLiteralRun now retains its already-proved frame-label invariant in TerminalWitness; both constructors use the existing induction hypothesis, with no added caller premise. Full audit passes 2,020. Source hashes: `results/quotient-output-integration.json`.

## Actual public runCall result and initial functional-opening reduction

Root reviewed and integrated PreparedExecFinalRow (3): the actual terminal witness now derives the first DONE-row representation for both successful end and gas exhaustion, then exact bus/padding composition yields published status, fast gas, canonical SP and complete live i32 stack. `prepared_literal_public_run_call` starts from actual executable preparation/entry eligibility and literal HoldsP; it no longer assumes final-state representation. Seven actual fixtures match the public decoder, and 49 output-header mutations are detected by that decoder. This regression is not a cryptographic negative-proof test. Scope remains one straight-line function, stack8 and executable verifier-side preparation. Branch/nested-block support is now the next instruction slice.

CloseFamilySumcheck (3), FunctionalOpeningReduction (1) and EqualityWeightAppend (1) are reviewed/integrated. For fixed source oracles and weight tables before sumcheck challenges, absence of a correct functional representative bounds checked initial scalar-candidate paths by (n*max(N,2)+2n)/|S|, under explicit distinctness, shape and radius/separation hypotheses. This joins far-family extraction and the actual close-case quadratic sumcheck/equality residual; no extraction premise is assumed. It is not a pre-GKR AIR-witness or cryptographic soundness theorem. EqualityWeightAppend proves the precise iterative ordering used by Python eq_weights. Root executable Lean/Python parity passes55cases/10,235weights including0,1,-1,mixed points;14cases detect reversed coordinate order.

SHA384EndpointSplit (5) introduces a separate batched addition table and proves core80round, add64 and last-tag interfaces. Full routing/digest composition and concrete proof measurement remain agent work at this checkpoint. Combined root audit passes2,033. Evidence: `results/functional-terminal-integration.json`, `results/literal-output-smoke.json`, `results/equality-weight-parity.json`.

Conditional parameter accounting now includes the first weighted sumcheck's34 numerator term: functional8912930 +fold524284 =9437214 over p^4. The isolated bound still supports only100integer bits; minimum extension degrees for this arithmetic alone remain5/7/10 for128/192/256bits. Query tails, other GKR/bus errors, commitment and QROM losses remain excluded; this is not a security certificate.

## Complete ideal opening/folding count and endpoint proof review

FunctionalOpeningFold (2) is root reviewed/integrated. Initial virtual oracle, equality-weight residual and claim are assigned by construction; accepted triples count checked weighted sumcheck, checked folding and with-replacement queries. The ideal probability bound is (A+E)/|S|+((T−1)/N)^q, A=n*max(N,2)+2n and E=sum max(child size,2), under explicit geometry and causal snapshot/challenge identities. Candidate absence/extraction is derived, not assumed. This remains a fixed post-GKR functional relation; authenticated actual source evaluations, sampler/FiatShamir and pre-GKR shared witness are not established.

Root authored SparseLiftMLE (4): exact stride-block sparse coefficient and repeated-weight semantics, coefficient MLE low-zero-factor scaling and weight MLE invariance. Root executable parity against actual branch_words and native quadratic/fold operations passes75cases,300rounds,2,883lifted cells, including0/1challenge factors. The test covers base-field embeddings; generic field algebra is separately proved. Evidence: `results/sparse-lift-parity.json`.

Root regenerated the endpoint-only SHA384 canonical fixture from its captured376byte message, projected independently regenerated original traces, verified the binary in a fresh process and reran all8negative checks. The fresh duplicate-tag malformed proof passes local AIR/PCS verification and is rejected by global bus verification. Binary1,289,410bytes vs1,508,054 original; sourcecells2,710,032 vs3,555,328. Runtime components roughly unchanged, not a speedup result. Durable evidence: `results/sha384-endpoint/root-review.json`. SHA384EndpointCoreSemantics (13) derives actual core rounds, byte padding and IV semantics; full endpoint routing-to-digest composition remains open.

PreparedControlStep (7) now authenticates expanded29field CODE descriptors including actual prepared endOf targets and proves actual interpreter block/br_if/nested-end steps. New control AIR semantic refinement remains open; this is not yet an extension of the full literal public runCall theorem. Combined root audit:2,059. Source hashes/limits: `results/fold-sparse-endpoint-integration.json`.

## Exact control literal circuit and current/next functional bridge

Root generated PreparedControlLiteral from frozen prepared_control_air.py, with individually named870 EXEC and543 CODE constraints, full interactions and public segments. Lean whole export exactly matches Python after explicit automatic multiplicity constraints (+3/+26). This is the exact AST target for upcoming membership/semantic certificates; it is not yet a new AIR-to-Wasm theorem. Actual fixtures independently regenerated; reference suite accepts13cases including7legacy and rejects1,054mutations. Actual prepared CODE checker accepts6control fixtures and rejects2,034descriptor/config mutations.

Root generated a new full global-bus diagnostic proof for the taken branch:88,614binary bytes including source roots, with385public fields separate. Fresh binary process verification passes and7changed-public/framing cases reject. This is Q8/Ext4, not secure compression or full NEAR. Evidence: `results/prepared-control/`.

DualMobiusWeights (13) is root reviewed/integrated. Generic-field dual zeta, inverse Mobius, cyclic predecessor reindexing and current/next coefficient functional are proved. Both terms refer to the same original source table. Root Lean/Python parity checks36cases/2,044coefficient entries and108optimized borrow-DP versus explicit MLE comparisons, including0/1/−1challenges; these executable checks do not prove the mutable loop or optimized DP. Packed-column and implementation refinements remain active work. Combined audit:2,072. Evidence: `results/control-literal-mobius-integration.json`, `results/dual-mobius-parity.json`.

## Control condition/provenance, packed weights and endpoint routing

PreparedControlCondition (11) is reviewed/integrated: kernel-checked membership of actual Boolean/onehot/inverse constraints proves selector681=0 iff the selected actual32bit stack word is zero, avoiding a32bit field alias. Root authored PreparedControlBus (16), adapting exact natural lookup/public records to29fields with generated-AIR definitional equality and CODE order/inactive kernel certificates. Root PreparedControlProvenance (3) combines literalHoldsP and actual executable CODE checking: numeric EXEC PC is live, actual instruction/fee/prepared endOf target are supplied, and every fetched field is authenticated. No caller live-PC or fetch-equation premise remains. Full new control transition/runCall theorem still pending.

PackedDualMobiusWeights (8) is reviewed/integrated: exact row-low/column-high full Mobius transform, tensor current/next coefficient functional and weight-MLE factorization. Root executable parity against actual lane_weights/lane_weight_mle passes48cases/675positions including partial lanes and0/1challenges. Python mutable transform and optimized borrow-DP proofs remain separate.

SHA384EndpointRouting (13) is reviewed/integrated. Natural receive matching derives tagged core input/output limbs; field tag injectivity uses explicit blockcount<P. Active endpoint output equals actual tagged core compression, and its output binds the next core initial state. Final publicdigest/message composition remains in progress; no standalone routing premise was added. Combined audit passes2,123. Evidence/source hashes: `results/control-provenance-packed-routing-integration.json`.

## Optimized endpoint message semantics complete

Root reviewed/integrated SHA384EndpointMessage (8): exact natural public-count matching selects the final active endpoint, the last-tag zero test identifies the last block, and actual add64 bit decoding, routed block chain, IV and padded bytes yield SHA384(message). No standalone compression/routing/final-digest premise remains. Root SHA384EndpointPublic (4) supplies the concrete message||digest||[1,0,0,0] layout and proves digest equality, assuming only actual HoldsP,48byte digest shape and blockcount<P. The fixture now uses this proved public constructor; root regenerated canonical statement is unchanged. Existing1,289,410byte proof remains the same statement; no redundant full proof rerun was needed. Cryptographic extraction toHoldsP remains separate.

PreparedControlBranch (6) is reviewed/integrated: actual literal jump constraints bind nextPC limbwise to the saved target; opcodeonehot removes other flags and takenbranch clears nestedlabel/savedheight/target. Root PreparedControlSetup (2) binds actualprepare/link/load/resolve to the proved29field authenticatedfetch, rather than accepting caller PFunc. Runtime setup smoke accepts6fixtures, reruns2,034CODErejections and adds18setup invalid-input rejections. Whole controlrun semantics remains open.

Combined audit passes2,143. Evidence/sourcehashes: `results/endpoint-public-control-setup-integration.json`. Upcoming reviewed-but-not-integrated candidates include control stack truncation and optimized row-weight borrow-DP; batched80round hashing is experimental definitions only at this checkpoint.


### Batched SHA-384 prototype independently integrated

Root reviewed and hash-checked all four frozen sources, regenerated the canonical Lean statement (exact JSON equality), reran 134,688 boundary residual checks and 14 negative tests, and verified the binary in a fresh process. Proof: 406,974 bytes, SHA-256 4c46270564d18b43bd611944123672e82463e2f7b8e11c07a8b5930946e38de8. Additional derived setup: 1,184 bytes (408,158 combined; full public tape 724 field values). Full integrated audit remains 2,143 PASS; new core module supplies definitions, not a completed semantic proof. Artifacts: `research/near-compression/results/sha384-batched/`.

Reduction from endpoint baseline is 68.44% in proof bytes; four-block source-cell reduction is only 0.87%. No runtime improvement is claimed. Batched reset/gating refinement is assigned to protocol agent. Internal recursive padding/input routing, full recursive verifier, full NEAR coverage, 1 Petagas capacity and 128-bit quantum security remain open.


### Optimized terminal-weight implementation refinement

Root reviewed and integrated DualBorrowWeightMLE (10 theorems) and UpperZetaBitPass (8). The former proves the exact current accumulator and cyclic-predecessor borrow DP equal upper-zeta weight MLEs, including wraparound and empty dimensions. The latter proves sequential current-state writes in ascending bit/index order equal recursive upperZeta, establishing source nonaliasing and the literal bitmask guard. Full integrated audit: 2,161 PASS. Executable Lean/Python parity: 72 cases, dimensions 0..5, zero/one/minus-one/mixed coordinates, 756 transformed entries. Evidence: results/optimized-weights-{parity,integration}.json. Generic field theorems do not substitute for concrete native PCS or quantum-security refinement.


### Control stack/gas/branch composition integrated

Root reviewed and integrated PreparedControlStack (6), PreparedControlGas (8), PreparedControlSequential (5), then authored PreparedControlChargedBranch (2). Full audit: 2,182 PASS. Taken branches now derive saved stack height and preserved prefix with zero padding; gas equations derive affordability or exhaustion independently of sequential-PC assumptions. Charged branch wrappers derive success from natural affordability, composing gas, PC, status, labels and taken stack. Untaken projection composes PC/status/label retention; its stack pop remains separate.

Evidence: `results/control-charged-integration.json`. Remaining whole-run obligations include label provenance, block/end/untaken projections, ordinary-opcode equations under changed literal control AST, and initial/final binding. The current local projections do not establish full control interpreter refinement or full NEAR execution.


### Batched hash active-prefix refinement

Reviewed and integrated SHA384BatchedPhase (19 theorems), authored SHA384BatchedPadding (2). Full audit: 2,203 PASS. Under actual HoldsP and N<P, constraints derive exactly80N active rows, canonical phase/tag, capacity, and no restart. Padding has zero phases and no first-row selector; field tags uniquely recover block indices. No external phase/reset premise. This closes the phase_and_active_prefix obligation of the frozen batched profile. Round-gadget extraction, compression, public-message decoding, natural routing, recursive input binding and cryptographic soundness remain open. Evidence: `results/sha384-batched/phase-integration.json`.


### Batched public layout centralized

Added SHA384BatchedPublic with exact deterministic padded-limb, IV and count definitions used by the exporter. Five public lemmas prove component lengths, full n+92+64N layout and exact message/digest prefix. Fixture now calls the shared definition; regenerated statement is exactly identical to the canonical four-block statement (724 values). Full audit: 2,208 PASS. Remaining payload word/count decoding and natural bus composition are explicit. Evidence: `results/sha384-batched/public-layout-integration.json`; original frozen source-files manifest is historical, and this report records current changed-source hashes.


### Heterogeneous opening projection connected to formal oracle

Root reviewed and integrated HeterogeneousSourcePair (8), full audit2,216 PASS. The exact source-pair beta accumulator and smaller-domain duplicate-side rule equal bindFunctionalOpening initial-oracle values at canonical ±points, with explicit root geometry and exact leaf-binding premises. Runtime regression uses actual check_opening with authenticated paths,900pairs over16shapes and mixed Ext4 beta, plus16altered-leaf rejections. This is algebra/implementation evidence, not Merkle security or pre-GKR witness extraction. Sparse coefficient polynomial-evaluation refinement is the next assigned bridge. Reports: results/heterogeneous-source-pair-{parity,integration}.json.


### Batched 80-round compression proved

Root reviewed and integrated SHA384BatchedSlice (8) and SHA384BatchedCompression (6); audit2,230 PASS. Kernel shape checking classifies all6,848original combined constraints as current-only or exact transition links. Two-row snapshot extraction preserves row gadgets and within-block recurrence while exempting the phase79 reset. Actual fixed K limbs and induction establish all80rounds and compression feed-forward arithmetic from batched HoldsP, N<P and valid block index. Independent captured-witness check:12snapshots,164,352residual evaluations,12broken-transition rejections. Evidence: results/sha384-batched/{compression-integration,snapshot-review}.json. Public payload decoding, endpoint routing, IV/digest composition, recursive routing and security remain open.


### Batched public payload index refinement

Added four kernel-checked lemmas in SHA384BatchedPayloadIndex. Generic fixed-width concatenation indexing derives exact padded-message16bit limbs, IV limbs, and actual public offset n+52+64block+4word+limb (digest length48). Audit2,234 PASS. This removes assumed lookup/index equalities; field casts, word reconstruction and bus matching still need composition. Evidence: results/sha384-batched/payload-index-integration.json.


### Sparse source polynomial bridge integrated

Root reviewed SparseLiftPolynomial (7), full audit2,241 PASS. Proves exact stride array evaluates to f(x^(2^k)), weighted branch accumulation, common degree bound and composition with authenticated heterogeneous source pairs. Covers short/zero-padded lanes and x=0. New executable Lean parity compares actual branch_words across48cases/675coefficient cells;48additional mixed Ext4 beta evaluation checks pass. Reports: results/sparse-polynomial-{parity,integration}.json. Native FFT correctness, cryptographic leaf binding and pre-GKR shared-witness extraction remain open.


### Actual block and nested-end state preservation

Root reviewed and integrated Untaken3, Block4, FrameStack2 and State3; added charged_untaken_stack composition. Full audit2,254 PASS. Actual Wasm.step block/nested-end preserves decoded state and label relation, with explicit actual CODE/endOf/charge/fee premises. Untaken branch derives nonempty stack, zero condition, SP decrement and exact popped-slot clearing; gas wrapper removes assumed success flag. No full-control-run claim: authenticated provenance discharge, branch actual-step composition, ordinary-op adapters and whole-run binding remain. Evidence: results/control-state-integration.json.


### Batched state routing and canonical IV bound

Reviewed/integrated SHA384BatchedRouting10 and PublicRouting4; root authored IVLayout4. Audit2,272 PASS. Natural bus balance derives endpoint inputs/output and compression-to-next-state linkage. High-bus receives derive actual public records. Canonical public layout count/content lemmas discharge IV premises: sha384_batched_public_initial now derives decoded initial state=SHA384IV directly from canonical HoldsP, digest length48 and N<P. No caller routing/IV correctness premise. Message payload word decoding, final digest binding, whole-message composition, recursive input routing and cryptographic soundness remain. Evidence: results/sha384-batched/routing-iv-integration.json.


### Public payload field and byte decoding

Added SHA384BatchedPayloadField5, audit2,277 PASS. All padded-byte lookups (including fallback) are <256, paired limbs <65536, field public lookup preserves the exact natural tape, and actual indexed payload limbs decode without modular wraparound. Div/mod256 recover their original high/low bytes. Remaining: bus4 record/tag matching to trace, decoded block composition and full digest theorem. Evidence: results/sha384-batched/payload-field-integration.json.


### Batched message receive bound to public payload

Added SHA384BatchedMessageRouting3, audit2,280 PASS. Actual bus4receive matches actual indexed public record; bounded index/tag conversion proves record index equals block. Ordered64payload and individual schedule-limb equalities follow. Explicit public count≤P premise remains pending canonical layout discharge (assigned); no assumed routing match. Trace byte/block decoder and final digest composition remain. Evidence: results/sha384-batched/message-routing-integration.json.


### Full batched SHA384 semantic theorem complete

Reviewed MessageCount4 and Message12; root authored TraceBytes5 and Soundness1. Full audit2,302 PASS. `sha384_batched_message_sound` derives sha384ChainDigest(message)=digest from actual batched HoldsP on canonical public expansion, digest length48 and N<P. Message decoding, counts, phases/resets, constants, compression, IV, natural state/public routing and final digest binding are all derived, with no separate semantic premises. Regenerated canonical four-block statement matches exactly; fresh binary verifier passes unchanged406,974-byte proof. Evidence: results/sha384-batched/semantic-soundness-integration.json.

This completes semantic refinement of the batched hash AIR, not cryptographic security. Proof acceptance→HoldsP, internal recursive input routing, complete recursive verifier,128-bit quantum security, fullNEAR/1Petagas and secure sub300000-byte proof remain open. Earlier batched reports describing semantic gaps are historical and superseded for the specific obligations closed here.


### Authenticated control steps integrated

Root reviewed Authenticated4, BranchState1, BranchBounds3 and TakenState1, then authored BranchContinue1. Audit2,312 PASS. Actual preparation plus whole literal AIR/CODE binding now derives actual instruction, gas charge and block target for actual block/end/branch step refinement; no supplied fee/target/operand equality remains. Unified affordable br_if theorem derives condition case and preserves successor frame fn. Explicit initial-state/root-label, resolved fn binding, active/selected row and affordability remain. Ordinary-op adapters, failure/root-return cases, whole-run boundaries and fullNEAR remain open. Evidence: results/authenticated-control-integration.json.


### Functional FFT stage proof integrated

Reviewed RadixTwoFFTStages4; audit2,316 PASS. Functional DIT stage invariant proves natural-order polynomial evaluations and ±x leaf ordering, including zero padding, under explicit root half-order certificate. Root executable parity:24cases,108stage arrays,765native outputs,381plus/minus pairs and765mixedExt4 outputs allPASS. Library hash recorded. Native bit-reversal swaps, mutable writes and modular arithmetic are not formally proved yet; regression is not a substitute. Reports: results/fft-stages-{parity,integration}.json.


### Ordinary-opcode semantic adapter integrated

Reviewed LegacyAdapter9 and authored LegacyProjection1; audit2,326 PASS. Exact new control constraints specialize to existing stack/arithmetic semantic interfaces under current BRIF=0, with kernel source certificates. Authenticated ordinary opcode derives that condition. No old constraint-membership assertion is assumed. Evidence: results/control-legacy-integration.json.

Separately reviewed/copied/built definitions-only SHA384CommittedInput to unblock experimental exporter. Four-table profile routes private byte table through padding into hash core,88public fields; no semantic/security theorem claimed. Root review requested trusted fixed-index/byte validation and truncated-padding negative tests. Captured376B instance only until generalized; expected input root and recursive producer routing are separate obligations.


### Authenticated ordinary successors and FFT bit reversal

Reviewed/integrated PreparedControlLegacyLocal5, PreparedControlLegacyState4, FFTBitReversal8. Full audit2,343 PASS. Actual authenticated const/add/drop steps preserve exact successor gas, stack, PC and control labels; immediate and opcode are derived from CODE binding. FFT natural-index reversed carry, counter and sequential conditional swaps now compose to bit-reversed input. Sequential butterflies and machine-word arithmetic remain open. Evidence: results/control-fft-integration.json.

### Committed-input hash prototype reviewed

Verified all six frozen source hashes, copied source and durable proof/statement/receipt/reports, and independently ran the mandatory-root full verifier successfully. Proof796,630B; public352B; external receipt719B; total797,701B. This is a size regression from the public-expanded-payload component, despite only0.377%more source cells. Agent negative report12PASS includes fresh valid alternate-input proof rejected by expected-root check, and locally valid truncated padding rejected by global bus; root reviewed report but did not rerun suite. New AIR semantic refinement, recursive producer-to-input-root binding and128-bit quantum security remain open. Evidence: results/sha384-committed/root-review.json.


### Committed-input padding selector schedule proved

Root authored SHA384CommittedPadPhase6; full audit2,349 PASS. Actual committed-input HoldsP derives first/shift equations and exact selector(row,block)=1 iff row=block. Selectors vanish past the declared block count. Actual selected padding equations imply the expected constant-byte field value. These hold for existing rows; enough rows must still be derived from global bus matching, consistent with the truncated-padding negative test. Input byte decoding/bus6 routing and full new hash semantic refinement remain open. Evidence: results/sha384-committed/pad-phase-integration.json.


### Control termination, gas context, and committed padding bus metadata

Reviewed/integrated Terminal5 and GasContext2; root added pad sum/tag2. Full audit2,358 PASS. Authenticated root end derives empty stack and actual .fin; insufficient gas derives actual .abort and exact failure gas/error plus DONE/FAIL. Actual supported exec continuation preserves gas before charge; actual prepared step preserves gas context. Padding bus multiplicity is exactly one on declared rows, zero after; tag is field row index while active, zero after. No field-cast injectivity or sufficient capacity silently assumed. Evidence: results/control-terminal-pad-integration.json.

Protocol agent byte accounting locates338,304B (86.82%) of389,656B committed-proof growth in extra current/next/final column vectors;753new interactions create3012 auxiliary coordinates despite only10128new source cells. Assigned existing terminal GKR plus weighted joint PCS adaptation with unchanged AIR/expected-root contract and diagnostic parameters; no improvement claimed until measured. Whole-control-run handoff pending review; entry/public-output derivation assigned.


### Whole supported control execution and committed byte bounds

Reviewed/integrated PreparedControlRun2 and root authored SHA384CommittedBytes7. Full audit2,367 PASS. Actual Wasm.run follows by fuel/remaining-row induction through all six supported opcodes with authenticated code, gas context, branch/root-label states, root return and gas failure. Active final-row impossibility is derived from literal terminal constraint. Initial state/fn/context and sufficient fuel remain explicit until entry wrapper; terminal public-output binding is also pending. No per-step correctness certificate is assumed. Committed input/padding actual bit constraints derive canonical byte bounds<256; fixed framing first-row equations yield field equality. Private message bus matching and capacity remain open. Evidence: results/control-run-bytes-integration.json.


### Full modeled mutable FFT composition

Reviewed/integrated FFTButterflyWrites6 and FFTMutableSchedule4; root added committed-byte natural decoding3. Full audit2,380 PASS. Sequential pair writes preserve original u/v, disjoint offsets/blocks preserve inputs, twiddle accumulator equals powers, and each complete mutable stage refines functional stage. Composition includes exact modeled bit-reversal initialization and yields natural polynomial evaluations/plus-minus commitment pairs under root and shape premises. This is a mathematical field/state-update model; native word arithmetic and pointer-memory refinement remain open. Lower-Mobius implementation assigned next. Fixed byte-sized framing and padding constants now recover exact natural bytes rather than only field values. Evidence: results/fft-mutable-integration.json.


### Actual control call entry and outer runCall

Reviewed/integrated Boundary4, Entry3, RunCall2. Full audit2,389 PASS. Natural boundary bus balance binds27field entry/exit record and entry gas, disjoint from CODE buses. First-row literal constraints derive PC0, empty stack and no nested label. Executable preparedControlRunCallCheck combines actual preparation/CODE check with public entry/prologue check; accepted check plus full HoldsP and fuel≥height yields actual outer runCall .done terminal witness. No supplied initial state, gas equality or per-step correctness premise remains. Final published output binding is pending. Preparation remains verifier-computed, not PREP AIR. Profile still stack8, one defined function and one nested void block; fullNEAR/1Pgas and quantum-secure recursion remain open. Evidence: results/control-entry-integration.json.


### Lower-Mobius implementation and private routing foundation

Reviewed/integrated LowerMobiusBitPass7; root authored SHA384CommittedRouting2. Full audit2,398 PASS. Exact ascending bit/index current-state subtraction loop refines mobiusCoefficients, proving source noninterference and mask/XOR addressing. Coefficient-list→FFT composition assigned. Actual committed HoldsP implies every non-IV receive has an internal matching send; actual input-table active send has row0 and its indexed byte field payload. Cross-table bus6 sender classification, bounded index matching and sufficient padding capacity remain open. Evidence: results/lower-mobius-routing-integration.json.


### Committed private byte routing closed for existing rows

Root added byte_sender and pad_input_byte; full audit2,400 PASS. Exhaustive actual four-table interaction classification excludes core/endpoint/pad as bus6 senders. Natural balance plus selector activity identifies input row0; message tags under n≤P identify exactly index128*block+offset. Thus every existing selected real padding byte equals committed input byte with no assumed routing match. Sufficient rows and full new hash semantic refinement remain open. Evidence: results/sha384-committed/byte-routing-integration.json.

Protocol agent proposed a next fixed376B layout removing separate pad table/bus6: input table directly sends four constrained padded-block bus4 records as expressions over committed bits/constants. Authorized separate prototype after current GKR evidence; expected input commitment shape/context/root retained, canonical AIR digest explicitly changes. Estimated old-wire saving205136B before PCS is a hypothesis, not a measured proof. This may eliminate753new interactions and avoid their auxiliary columns.


### Packed source pipeline and canonical committed message

Reviewed/integrated PackedSourceExecution11; root authored SHA384CommittedMessage4. Full audit2,415 PASS. Packed allocation/population, mutable lower-Mobius with unchanged zero tail, complete mutable FFT, source leaf pairs and beta combination refer to the same computed polynomial family, whose degree and packed current/next functional are proved. Native arithmetic/memory and adversarial pre-GKR common-witness timing remain open; assigned exact missing theorem/counterexample investigation next. Actual committed message is decoded from input row; every existing padding row byte equals canonical SHA384 pad of that message. Row capacity/full hash composition remain. Evidence: results/packed-source-message-integration.json.

GKR component preliminary report: binary123145B, JSON435759B, gkr_and_weighted_pcs468.752s, independent JSON verifier23.644s. Fresh binary wrapper/negative tests still pending agent handoff; no final size/security certification.


### Supported control slice public-output closure

Reviewed/integrated Quiet3, Padding2, PublicOutput3, FinalRow3. Full audit2,426 PASS. Quiet DONE transitions preserve physical stack/SP/PC/gas/status even if padding fetch is BRIF. Terminal witness derives actual first-DONE binding, natural boundary routing yields published status/fast gas/live i32 stack. prepared_control_public_run_call composes actual runCall with public output from literal HoldsP, executable setup/CODE/entry checker and fuel≥height; no supplied initial/final-state relation or step certificate remains. Scope one defined function,stack8,one nested void block; verifier-side PREP and fullNEAR/proof-system security remain separate. Evidence: results/control-public-integration.json.

### Compressed committed-input component independently verified

Root checked3frozen source hashes, copied durable binary/statement/receipt/reports, confirmed entire original statement and receipt byte-identical, and independently fresh-process verified mandatory-root compact GKR binary. Proof123145B +public352B +receipt719B=124216B, versus797701B original total. Canonical AIR JSON1758033B is reusable verifier configuration excluded from transport, explicitly accounted. GKR+PCS468.752s; full agent run596.536s includes multiple verifies. Negative suite still running. Q8/Ext4 diagnostic only, captured376B component; no fullNEAR,complete recursion or128-bit quantum security claim. Evidence: results/sha384-committed-gkr/root-review.json.


### Common-input quantifier boundary and direct padded expressions

Reviewed/integrated GKRCommonInputBoundary6 and definitions-only SHA384DirectInput; root authored SHA384DirectSemantics4. Full audit2,436 PASS. Universal final GKR equality weights separate any one fixed input; explicit adaptive kernel shows why changing existential quantifier order is invalid, not an authenticated PCS attack. Shared input must be fixed before GKR, and same source/aux polynomial family before zerocheck row challenges. Concrete challenge-dependent constant folding/layout also prevents assuming a single fixed-dimension multilinear map without proof. Security extraction/counting/QROM remain open.

Direct three-table design retains input constraints and root shape but sends padded-block expressions directly on bus4. Root proved generic direct byte/limb expressions equal canonical padding of decoded actual input and actual AIR Boolean constraints bound message bytes<256. No pad-row capacity or byte-bus routing premise is needed for these expression identities. Full direct core routing/hash semantics and measured proof still pending. Evidence: results/common-input-direct-integration.json.


### Independent control checker regression

Root reviewed/copied PreparedControlRunCallSmoke, regenerated all6 prepared fixtures, reran reference AIR and exact whole literal export parity, then reran smoke. PASS:2052 setup/CODE/entry mutations rejected,44 output decoder mutations detected,433 reference AIR negatives rejected;2310public fields across6actual runCall outcomes checked. Export includes870/543 user constraints plus3/26 automatic multiplicity constraints, not a profile change. Updated test report metadata to reflect completed semantic theorem while preserving cryptographic limitation. Durable evidence: results/prepared-control-runcall/.

Terminology correction: committed input is witness data omitted from public tape, not proven private or zero knowledge. Diagnostic PCS openings may reveal linear witness information. Earlier private-input wording refers only to the public/witness split, not a confidentiality guarantee.


### Joint row/GKR separation and direct block routing

Reviewed/integrated GKRRowSlotSpanning4; root authored SHA384DirectRouting4. Full audit2,444 PASS. Equality for all rowpoints and GKR weights forces every cell of two fixed represented source tables equal; exact coefficient functional connects to this family. This does not establish sampled transcript extraction or causal/quantum soundness. Direct AIR natural bus balance, sender classification and first-row multiplicity bind every active block receive to input row0, tagged with a declared block and ordered64limbs; no separate padding table capacity needed. Assigned direct-to-batched HoldsP projection to reuse full existing SHA384BatchedSoundness. Evidence: results/row-slot-direct-routing-integration.json.


### Canonical direct public layout

Root authored SHA384DirectPublic8; full audit2,452 PASS. Canonical direct public tape has88fields: digest48,count4,standard IV32,count4. Exact byte lookups, counts1, digest and IV records proved, plus direct-to-batched IV record equality. This avoids proving a generalized arbitrary-IV hash relation by accident. Exact bus4/public count substitution and full batched HoldsP projection remain underway. Evidence: results/direct-public-integration.json.

Direct3table diagnostic experiment preliminary binary99382B (23763B below four-table GKR), wrapper/fresh verification pending; no final result/security certification inferred.


### Exact first-row counts and structural direct projection

Root authored DirectCounts3; reviewed/integrated DirectProjection6 (normalized one leading theorem whitespace so exact audit discovery includes it). Full audit2,461 PASS. First-row sends contribute one each independently of traceheight; input table bus4count is exact count of declared paddedblock records. Retained core/endpoint expressions have pubBound0, so constraints and natural traffic unaffected by public replacement. Structural projection transfers direct HoldsP to old batched HoldsP on same first2trace tables, with exact public-count replacement and pubFit explicitly pending. Actual direct message converts toUInt8 without truncation. Evidence: results/direct-count-projection-integration.json.

Agent direct full fresh verification and12negative tests reportedPASS,total100450B (99382proof+352public+716receipt); root frozen handoff review pending.


### Direct prototype independent review and canonical block records

Root verified8frozen source hashes, copied durable artifacts, independently regenerated canonical Lean export with exactJSON equality, reran6174input constraints/four padded block records/exact six-bus natural balance, and fresh-process full binary verification plus all12negative tests. Total100450B includes99382proof+352public+716receipt; reusable canonical verifier configuration excluded. Committed witness input has no ZK guarantee; Q8/Ext4 has no128-bit quantum soundness claim. Evidence: results/sha384-direct/root-review.json.

Root authored SHA384DirectRecords2; full audit2,463 PASS. Each input-row padded block equals old canonical batched public record, and complete direct record list equals message segment msgs, including multiplicity/order. Full pubCount substitution and final hash composition remain. Evidence: results/direct-records-integration.json.

## Direct SHA384 semantic closure and joint-weight degree audit

Root audit passed 2,479 actual-semantics bridge theorems and boundary regression examples (`/tmp/root-gkr-degree-audit.log`). `sha384_direct_message_sound` now derives standard SHA384 of decoded input bytes from actual direct AIR `HoldsP`, canonical public digest/IV/count layout, and the block-count bound. Routing, padding, compression and exact natural message-count replacement are discharged internally. This is not cryptographic acceptance-to-HoldsP extraction.

Integrated and reviewed nine `GKRWeightCoordinateDegree` lemmas: the actual universal batching coefficient has individual degree below two in each independent rowpoint, left/right GKR, gamma and PCS coordinate. Full tensor realization, causal accepted-event inclusion, source extraction and QROM security remain open.

Executable review found the frozen captured376 wrapper only checks public length, not standard SHA384 IV/counts or byte canonicality. Existing recorded artifacts use canonical values and retain their independent verification evidence; arbitrary wrapper acceptance is not yet linked to the semantic theorem. The new bounded-length profile and a Lean public-layout checker bridge are being developed in parallel.

Copied the agent's completed16-negative committed-GKR report, including fresh valid alternate-root proof rejection and locally valid truncated-padding proof rejection by the global check. Root independently verified the honest proof previously; root has not rerun those expensive fresh-negative proofs. Full accounting uses409,870B for the original batched proof plus all public bytes, and100,450B for direct proof plus public bytes and receipt, excluding reusable AIR configuration. Both are Q8/Ext4 diagnostics. See `results/direct-soundness-degree-integration.json`.

## Canonical public input gap closed in captured376 wrapper

Hardened `verify_sha384_direct.py` to require exact88-field public layout:48 canonical integer digest bytes, count1, standard SHA384 IV in32 low-to-high16-bit limbs, and count1. Rejects Python boolean/float/string aliases. Existing proof/AIR/receipt remain unchanged; original `source-files.json` is historical, and `public-hardening.json` records current source hashes.

Root independently reverified the full binary proof and passed59 rejection tests, including47 direct layout-check rejections tested separately from transcript verification. Integrated `SHA384DirectPublicCheck.lean`: five lemmas prove honest completeness and checker acceptance plus actual HoldsP implies the standard SHA384 digest. Full audit PASS2484; no acceptance-to-HoldsP cryptographic or quantum-security claim.

## Tensor realization and independent public-check parity

Integrated five `MultiaffineTensorRealization` lemmas, full audit PASS2489. Coordinate-affinity now derives exact Boolean tensor interpolation; an explicit adaptive scalar candidate event inherits the existing far-case counting bound. Fixed prechallenge function, product sampling, far-case and separation premises remain explicit. Actual heterogeneous beta instantiation, verifier-acceptance inclusion, near-case image recovery and QROM security remain open.

Root reviewed and independently executed Lean/Python public-check parity on the actual direct statement:187 canonical-field cases agree (49 accepted,138 rejected), plus20 raw aliases/types rejected separately. Valid altered digest bytes are syntax-valid and intentionally remain accepted by the layout checker. Durable evidence: `results/sha384-direct/public-check-parity/`.

Re-read D1 a7b/phase2 log tails from existing `origin/main` f025caf6 because local main44b28911 lacks those files. No production files changed and no remote freshness claimed. Report: `results/tensor-realization-parity-integration.json`.

## Source commitment construction memory review

Reviewed existing mmap `SourceCache`, `FlatTree` prover and native `rs_commit.rs`. Cache reads already avoid materializing complete cache files, but cache construction retains serde JSON input, decoded rows, all leaves and all Merkle layers. Lane FFT runs before tree construction, so their payload peaks must not be summed.

Added `inspect_source_memory.py` with source-derived phase-aware payload accounting, explicitly excluding serde allocations, vector headers, allocator overhead, auxiliaries and simultaneous jobs. For captured376 core:10,719,232B decoded row payload,42,991,616B leaves,2,097,152B lane FFT buffer,12,582,864B Merkle digests; retained construction payload lower bound66,293,712B. This is not measured peak RSS. All three tables' calculated cache file sizes were independently checked against the existing generated cache files and match exactly. Evidence `results/sha384-direct/source-memory-accounting.json`.

A future disk-backed writer must preserve exact context/root/leaf order/openings while replacing JSON row input, leaf transpose buffers and in-memory tree layers. Merely using the existing mmap reader does not solve writer memory. Total unique compression work remains a separate bottleneck. Agent protocol is evaluating shared-core/streamed alternatives.

## Concrete joint tensor candidate bound and fixed-envelope prototype

Reviewed/integrated five `GKRJointTensorCandidate` lemmas; full audit PASS2494. Actual one-table beta uses distinct concatenated row/left/right/gamma/PCS blocks, with derived multiaffinity and tensor identity. General fixed coefficient/source lists reconstruct common lane polynomials; far-case adaptive-candidate counting follows. Heterogeneous multi-table offsets, causal accepted-event inclusion, sparse-lift image and cryptographic reductions remain open.

Added isolated `pq384_fixed_gkr_layout.py`: trusted input log caps the first input vector, rejects overflow and remaps only first-layer zero references to the new final slot. Existing GKR layout hashing binds the new profile and cap. Actual GKR prove/verify tests with1,2,5 live constants preserve circuit outputs and input functional obligations; all share16input slots/eight final-input quadratic rounds. Wrong-cap proof verification and invalid/overflow caps reject. This prototype is not integrated into the complete AIR/PCS profiles, and carries no security certification. Evidence `results/fixed-gkr-layout-regression.json` and `results/joint-candidate-fixed-envelope-integration.json`.

## Bounded hash family independent review and ideal far-fold closure

Copied/reviewed eight frozen bounded-family source files, exact SHA256 hashes matched. Root independently regenerated canonical Lean267B AIR/public/shape JSON, checked4428input residuals/three padded records/six natural bus counts, and fully verified binary proof using mandatory external receipt. Proof93,937B +public352B +receipt1,322B =95,611B; reusable AIR excluded. Root checked binary SHA256 `915ff49c7d9ff57ee57eeb244fbfe8830ad03e0c160944b6e7e741a79a045926`. Agent's28negative tests and8export-boundary checks reviewed, not independently rerun. Endpoints1/1024 are export/contract checks, not extra proved traces. Evidence `results/sha384-family267/`.

Reviewed/integrated `JointSourceFarFold` two lemmas; root full audit PASS2496. Literal stage-zero indexed candidates imply the explicit joint scalar event; actual ideal `checkedFoldAccept` acceptance in the far branch is bounded by joint-candidate, adaptive-fold and query-survival terms. Initial oracle is fixed by definition; no honest-polynomial or initial-candidate-absence premise. Causality, fixed product sampling and parameter regime remain explicit. Full upstream/multi-table mapping, near-case image recovery and commitment/QROM reductions remain open.

## Disk-backed Merkle construction prototype verified

Added prover-only `pq384_disk_tree.py`, streaming fixed-width leaf records and writing/reading each Merkle layer on disk. Uses exclusive creation, exact source-cache layout, identical context/level/index framing and immutable leaf-input contract. Does not modify existing commitments or frozen profiles.

Independent reference tests at8power-of-two sizes and all3existing captured376source caches PASS. Complete tree bytes/root match original native builder; selected openings authenticated through unmodified `SourceCache` match exactly. Core131072-leaf tree12,582,864B built in1.883s, Python-traced peak15,514B. This measures Python tracked allocations only, not RSS, OS page cache or full prover memory. Leaves/coefficients already exist; leaf transpose and JSON row loading remain in-memory upstream. Evidence/source hashes `results/disk-tree-parity.json`. No formal native/memory refinement or cryptographic claim added.

## Wasm locals interface integration and independent reference replay

Reviewed/copied isolated `prepared-locals-v1` sources; actual prepare/runCall fixture regenerated by root matches six frozen locals cases. Root independently replayed12reference cases (six locals, six control) and740adversarial rejections, including coherent field-alias indices. Local index constraints use separate16-bit limb equalities. Exact-gas and first/late local.get exhaustion included. Seven additional old straightline cases, including193instructions, have agent-only evidence copied separately. Source hashes/fixtures/specs/rows/reports in `results/prepared-locals/`.

Integrated five `PreparedLocalsStep` lemmas; full audit PASS2501. They extend state decoding with frame.locals and prove actual interpreter get/set/tee and prepared gas charging. They do not establish new AIR→step refinement. Lean literal AIR/source parity, PREP/CODE/local-count provenance and whole-run/output extension remain active work. Bounds remain stack8, zero parameters, one function, at most four i32 locals and one nested void block. Prior control profile unchanged.

## Lane-at-a-time disk leaf generation verified

Added `pq384_disk_leaves.py`: read one existing coefficient lane, embed in Ext4 native FFT input, evaluate4xLDE, transpose into an on-disk leaf file in257-leaf test tiles. Preserves source-cache little-endian lane-pair order. File creation is exclusive; existing caches unchanged.

Root tested all3captured376source caches end to end: entire leaf files, entire disk-generated tree files, roots and selected authenticated openings match the original native builder exactly. Core42,991,616B leaf file generated in1.664s in this run, without retaining it as one explicit memory buffer. FFT input/output arrays total5,242,880B during FFT, plus tile/IO/runtime overhead; no RSS bound or controlled throughput claim. Upstream witness→coefficients still requires work. Native library SHA256 recorded, existing FFT algebra/refinement scope unchanged. Evidence `results/disk-leaves-parity.json`.

## Heterogeneous source mapping composed into checked-fold FAR bound

Reviewed/integrated eight `HeterogeneousGKRWeights` lemmas and authored `HeterogeneousFarFold.heterogeneous_far_checked_count` by composing the concrete affinity family with `joint_source_far_checked_count`. Full root audit PASS2510, allowed axiom closures only. Concrete mapping includes current/next source/aux offsets, packed group and partial-lane padding, per-table row coordinates, shared ru/rv/gamma, shortened PCS point and power-projected source domains.

The theorem bounds actual ideal checked-fold acceptance in the FAR branch for the explicit heterogeneous family. Arbitrary beta-affinity and tensor-identity premises are removed. Fixed metadata/source inputs, shape bounds, FAR absence, domain/parameter regime and raw fold causality remain explicit. Compiler-generated metadata parity, upstream causal tape, near-case sparse-lift image and commitment/QROM security are not established. Agent next work targets captured compiler metadata and actual implementation weight parity. Evidence `results/heterogeneous-far-fold-integration.json`.

## Independent full-state compression reuse validation

Root reviewed/copied/hashchecked3frozen block-inventory sources, rebuilt the OpenSSL measurement adapter, and independently replayed all11,181saved framed hash inputs to22,474exact `(full512-bit input state,128-byte block,full512-bit output state)` records. All final digests agree with hashlib; eight corruption/index/digest/record mutations rejected. Independently compared three267BLean-exported compression states. Frequency provenance41,542observed calls still comes from agent's accepted-verifier capture, not this artifact replay.

Exact whole-input dedup requires32,587compressions; full-state/block reuse reduces this to22,474. Block-only dedup would yield14,682and is invalid:102block byte strings occur with multiple input states, causing7,792incorrect merges. Shared compression AIR must authenticate all8state words, call multiplicities/order, IV and padding provenance; SHA384's48-byte digest is insufficient as internal compression state. The observed graph is acyclic with16,911edges, a property of this capture rather than a universal hash claim. Durable artifacts and root evidence `results/sha384-block-dag/`. No full recursive verifier or quantum-security claim.

## Literal locals AIR, source index and actual operand bridge

Root reviewed/copied generated `PreparedLocalsLiteral`, four `PreparedLocalsIndex` lemmas and export/generator/parity tools. Independent Lean export exactly matches Python AIR for all supported local counts0..4, including every constraint, interaction, public segment and automatic multiplicity bit constraint. Generated source reproduces exactly.

Authored `PreparedLocalsOperand.prepared_locals_operand`: actual TableLocal constraints plus active local opcode and existing frame-state relation yield an in-range selected index, decoded immediate equality and actual interpreter frame.locals lookup. This discharges an arbitrary lookup premise, but does not prove next-state transitions. Full audit PASS2515. PREP/CODE/local-count provenance, bit/natural-word transitions and whole-run extension remain. Evidence `results/prepared-locals/literal-index-operand-integration.json` and `literal-parity.json`.

## Actual locals setup provenance and captured batching metadata

Integrated six `PreparedLocalsCode` and three `GKRMetadataValidity` lemmas; full root audit PASS2524. Locals checker uses actual prepare/link/load/resolve and checks local count/types, zero params/results, exact32field CODE descriptors, gas entries and public count/length. Root independently ran six setup fixtures:3648exact CODE fields and3774malformed metadata/public mutations checked. Whole newAIR→runCall remains open.

Root independently replayed captured old33table and267Bhash metadata/weight parity:601betas,29,596private-slot values,216sampled lane-weight positions,45partial lanes,26malformed metadata rejections. Generated Lean numerical certificates independently pass33+3tables. New metadata lemmas turn executable certificate acceptance into every generated lane's WellFormed bounds. Compiler/export equality remains executable evidence, not formal Python semantics; captured input dimensions do not establish fixed-envelope deployment or causal sampling. Agent-only seed33 evidence remains separate. Evidence `results/locals-code-metadata-integration.json`, `results/prepared-locals/code-smoke.json`, `results/heterogeneous-metadata/`.

## Natural CODE-bus authentication for locals literal AIR

Authored `PreparedLocalsBus` by adapting the audited control bus interface to exact32field descriptors, EXECwidth818/CODEwidth235 and count-parameterized locals literal constraints. Sixteen lemmas derive fetch matching from exact natural bus balances, active CODE rows, source-proved PC ordering, publication to public records and exact literal-AIR identity. Full root audit PASS2540.

`prepared_locals_literal_fetch` requires only actual literal AIR HoldsP and valid EXECrow; it derives a CODErow at the exact numeric EXEC PC, active status, matched descriptor and an exact public record. No caller fetch equation, active-row witness or CODE uniqueness assumption remains. Next root step composes this with actual PreparedLocalsCode checker to bind interpreter instruction/charge. Local update and full-run refinement remain separate active work. Evidence `results/prepared-locals/bus-integration.json`.

## Locals prepared-instruction provenance and literal write equations

Authored three `PreparedLocalsProvenance` lemmas composing literal natural-bus authentication with executable PreparedLocalsCodeCheck. Actual fetched public record is shown to have the execution row's numeric PC, yielding live prepared instruction, actual gas charge, local-index bounds, block target and all32descriptor fields. No caller live-PC/fetch equation or CODE uniqueness premise.

Reviewed/integrated four `PreparedLocalsUpdate` lemmas: all817Boolean columns excluding inverse, eight literal local-write source equations, exact nonfinal-row limb update and16-bit local/operand limb bounds. Full root audit PASS2547. Selected-stack operand, local-array transition, full state step and whole-run theorem remain active. Evidence `results/prepared-locals/provenance-update-integration.json`.

Shared compression prototype design reviewed and implementation assigned: twoactual267Bcalls/sixlogicalblocks/fiveunique fullstate nodes; six tables with natural fanout/call sequencing/input commitments. This tiny fixture has no paddedcore row saving; its purpose is validated reuse semantics, with full-workload scalability and secure succinct aggregation still open.

## Literal first-row locals initialization

Authored four `PreparedLocalsInitialization` lemmas. Exact literal first-row constraints yield all128local bits zero, each16bit local limb zero, every decoded32bit localword zero, and decoded local array equal to count copies of i32zero. Requires actual TableLocal and positiveheight, plus count≤4 forarray; no supplied initialization witness or zero-bit assumption. Full root audit PASS2551. Actual setup-frame and whole-run composition remain separate work. Source/evidence `results/prepared-locals/initialization-integration.json`.

## Projected-source recovery and locals array/gas integration

Reviewed/integrated eight `ProjectedSourceRecovery` lemmas: arbitrary power-projected source symmetry plus rotation-closed distinct domain and unique-decoding distance force off-stride coefficients to zero; explicit recovery has original degree bound. Exact root-order and per-lane proximity/domain certificates remain premises. Existing strict agreement regime is sufficient algebraically; concrete Boolean lane separation and canonical disjoint/nonempty metadata remain active before applying this to the shared witness. Duplicate-lane cancellation is a boundary counterexample, not an attack on canonical compiler output.

Reviewed/integrated four `PreparedLocalsArray` lemmas deriving exact local Array.set! from actual source write equations with selected stack/index and successful-charge premises. Authored `PreparedLocalsGas` certificate for exact first682Boolean constraints, four gas subtraction and four gas update constraints; generic proved gas semantics now apply to the locals table. Authenticated fee decode and full next-state/whole-run composition remain. Full root audit PASS2564. Evidence `results/recovery-locals-gas-integration.json`.

## Actual prepared fee reconstructed from locals descriptor

Extended `PreparedLocalsGas` with two authenticated fee theorems. Literal AIR plus actual prepared CODE check supplies descriptor fields10..13; their four16-bit limbs reconstruct the actual prepared range charge at the numeric EXEC PC, with u64bound derived internally. ActualSetupCheck corollary uses the function obtained by real prepare/link/load/resolve. No supplied fee equality/bound or independently selected PFunc in that corollary. Full root audit PASS2566. Full local state-step/whole-run remains active. Evidence `results/prepared-locals/fee-integration.json`.

### Boolean lane separation and common agreement set

Integrated GKRBooleanLaneSeparator (12 public lemmas) and GKRJointLaneSeparation (7). Full root check.py passes 2,585 audited checks. Actual heterogeneous joint beta has a Boolean selector for each lane under explicit natural slot geometry; a single joint representative therefore supplies simultaneous per-lane agreement on the same domain points, rather than separate witnesses. Independent root live-slot enumeration passed all 1,052 lanes in three captured layouts (33-table, hash267, seed33), rejecting 12 duplicate/overlap/empty/envelope mutations. Evidence: results/lane-separation-integration.json and results/heterogeneous-metadata/lane-separation.json. Captured geometry checks do not establish universal compiler layout validity or cryptographic/QROM soundness. Executable Lean geometry certificates and sparse recovery composition remain pending.

### Executable slot certificates and authenticated locals writes

Root integrated GKRSlotCertificate (1 theorem), PreparedLocalsFrameWrite (3), and PreparedLocalsAuthenticated (3). Full root audit passes 2,592 checks. Lean executable checker regenerated lanes from captured table metadata, compared all seven fields to recorded lanes, accepted 1,052 lanes across three captures, and rejected 12 malformed geometries. This is executable evaluation plus an audited checker implication theorem, not a closed kernel proof of each concrete capture. Locals authenticated CODE now determines the actual get/set/tee instruction, immediate, and one-hot selector; set/tee actual Wasm execution uses the next locals array derived from literal AIR. Full successor PC/SP/stack/gas relation and locals whole-call composition remain pending. Evidence: results/selectors-locals-integration.json and results/heterogeneous-metadata/lean-selectors.json. No full-NEAR, recursion, or quantum-security completion claim.

### Projected recovery and independently verified shared-hash component

Integrated GKRProjectedRepresentative (2 public theorems); full root audit passes 2,594 checks. A single universal joint representative gives per-lane proximity, then original-degree sparse polynomial recovery without honest-source/image assumptions. Domain distinctness, rotation closure/root order, power projection and unique-decoding inequality remain explicit. Concrete domain instantiation is next.

Root independently matched the canonical Lean shared AIR export, verified 3,659,896 source residuals, six exact padded records and natural bus multiplicities, rejected 15 witness forgeries, and verified the complete compact binary in a fresh process against both external input receipts. Proof112,786B +public384B +receipt2,494B =115,664B. Five unique full-state compression nodes certify six ordered blocks for two267-byte inputs. No padded core-row saving in this fixture; no sharing-only size comparison has been established. Q8/Ext4 diagnostic only, not recursion or128-bit quantum security. Evidence: results/projected-representative-integration.json and results/sha384-shared/root-review.json. Fresh valid-proof negative suite remains agent-owned pending.

### Natural RS domain and locals control/depth transitions

Root reviewed and integrated ProjectedRSDomain (6), PreparedLocalsSequential (5) and PreparedLocalsDepth (2), passing the full 2,607-check audit. Recovery on natural rate1/4 RS domains now derives domain distinctness, branch-root order and rotation permutation from one original primitive-root certificate, including identity-lift L=1. The actual Python verifier uses omega=440564289^((2^27)/(4*degree)); binding that implementation to the existing BabyBear root proofs is the next obligation. Locals source constraints now yield natural get/set/tee depth changes and overflow/underflow guards, sequential PC addition without field wrap, and status/label preservation. Opcode exclusions and active/charged hypotheses remain explicit pending full authenticated successor-state composition. Evidence: results/rs-domain-locals-integration.json. No full NEAR or cryptographic/QROM completion claim.

### Native root certificate and shared-hash formal foundation

Root integrated SHA384SharedCore (5) and PowerTwoRootOrder (10); full audit passes 2,622 checks with allowed axioms only. The exact native generator440564289, modular period and half-order equations are kernel checked; supported power-of-two roots now have exact-order and domain-distinctness theorems, with the actual rate-four root value expression. Challenge-extension embedding and native modular exponentiation implementation refinement remain separate boundaries. Shared AIR namespace extraction is text-identical to the frozen exporter; imported-module exporter is byte-identical on the actual fixture. Actual shared endpoint constraints imply all eight canonical Add64 operations. Complete independent compression/routing semantics are still pending.

Root independently verified the fresh alternate-input-commitment full binary (SHA25678fd18e22f407bbe84f22dba44822b64f88b9d529a846b731cd07861a227c2ca) and confirmed the original expected receipt rejects it specifically for the ordered external root mismatch. This is a valid alternate proof, not corrupted wire. Evidence: results/shared-root-order-integration.json and results/sha384-shared/root-fresh-input-binding.json. The fresh fanout forgery proof remains agent-owned and running. No quantum-security/full-NEAR completion claim.

### Independent compression arithmetic, locals stack, and recovered evaluations

Root reviewed/integrated SHA384SharedCompression (29) and PreparedLocalsStack (3), then proved RecoveredProjectedEvaluation (3). Full audit passes 2,657 checks. Shared compression derives exact active segment metadata and all80rounds from a local constraint-only contract discharged by actual five-node AIR; it does not import old-chain bus or inter-node state continuity assumptions. The output theorem still needs record/endpoint/call routing to certify complete shared hashes. Locals stack writes now follow exact literal constraints for all8physical slots and both limbs, including pop clearing; final authenticated state/whole-call composition remains pending. Recovered power-of-two-stride coefficients now reproduce the exact sparseLiftPolynomial storage and its evaluation at every field point, including zero, without honest-source assumptions. Evidence: results/shared-stack-recovery-integration.json. Security/recursion/full-NEAR target remains open.

### Authenticated locals successor and entry components

Integrated StackState1, SuccessState1 and AuthenticatedState2. Root added PreparedLocalsBoundary4 and PreparedLocalsEntryFrame1. Full audit passes 2,666 checks. Actual setup acceptance and literal HoldsP determine local opcode, immediate, selector and fee; successful get/set/tee derive full successor state without caller code/fee/next-state certificates. Current state, frame-function tie, selected local tag, nonlast row and enough gas remain explicit. New boundary proofs use exact natural balance to bind full public entry/exit records and gas. Actual prepared frame defaults match the constrained initial locals array, using checked types/count. Whole entry and ordinary/control/end/exhaustion run composition remain open. Evidence: results/prepared-locals/authenticated-state-entry-integration.json.

Root independently verified the fresh fanout2-to1 proof: local/GKR/PCS acceptance, then full verifier rejection specifically at randomized bus fingerprint product. Evidence: results/sha384-shared/root-fresh-fanout.json. Agent complete suite reports26negatives (24wrapper cases plus2freshproofs); only the two freshproof outcomes were independently rerun here, not all24wrapper mutations. No cryptographic-security claim follows from these tests.

### Actual locals entry and exact shared routing foundation

Root added PreparedLocalsEntry3: exact literal first-row constraints derive PC0/SP0/active/root-label state; actual enter plus preparedLocalsCodeCheck and public entry/prologue checks yield full initial PreparedLocalsState and gas context. Final setup wrapper uses actual prepare/link/load/resolve provenance, with no caller initial-state or initial-gas equality. Whole run induction remains pending.

Reviewed/integrated SharedRouting5 and SharedPrefix15. Exact natural bus balance binds every active call row to a full177field record (nodeID,A32,M64,C32,D48) and preserves exact per-message fanout counts. Prefix AIR derives canonical active interval, numerical IDs, capacity and uniqueness without caller uniqueness assumptions. Node records still need linkage to certified compression/endpoint outputs before complete shared-message soundness. Full audit passes 2,689 checks. Evidence: results/locals-entry-shared-routing-integration.json. No full-NEAR/recursion/128-bit-QROM claim.

### Certified diagnostic Ext4 bridge and conditional legacy adapter

Root reviewed/integrated DiagnosticExt4Embedding12 and PreparedLocalsLegacyAdapter9. Full audit passes 2,710 checks. Flat [c0,c1,c2,c3] arithmetic maps to certified Fp4 tower[[c0,c2],[c1,c3]], including universal multiplication for the actual nested accumulation and descending X^4=11 reduction schedule. Root order/domain embedding and projected recovery are specialized without assumed field/root certificates. Root independent executable parity passes320canonical operand pairs/1,280operations across basis, modular boundary and mixed coordinates against actual Python add/sub/mul. Parser and native machine refinement remain separate; Ext4 security unchanged. Legacy adapter specializes actual current-row local/branch/const flags on both source and target expressions, deriving old arithmetic/stack interfaces without assuming old global TableLocal. Ordinary/control whole-call composition is pending. Evidence: results/ext4-legacy-integration.json and results/diagnostic-ext4-parity/report.json.

### Shared node certification and ordinary locals-profile steps

Reviewed/integrated SHA384SharedNodes11 and PreparedLocalsLegacyLocal4/ControlDecode1/LegacyState2. Full root audit passes 2,728 checks. Shared-node A32 and M64 records are routed to the same uniquely tagged core; endpoint B is tied to that node phase79 output; endpoint feedforward equals its compression, and record C32+D48 equals endpoint output/digest expressions. Hidden state words6/7 are included. All matching and ID facts derive from actual natural AIR balance/prefix constraints. Call phase/order, canonical message block and public digest composition remain pending.

Actual locals-profile setup+HoldsP now derive full const/add/drop successor states, authenticating immediate/fee/control tags and proving local tags zero, then preserving locals through the instruction. Current state relation, selected opcode, nonlast row and gas sufficiency remain explicit as step interfaces. Control/end/exhaustion and whole-call induction remain pending. Evidence: results/nodes-ordinary-integration.json. No full NEAR/recursion/PQ128 completion claim.

### Fixed recovered table and locals terminal semantics

Reviewed/integrated RecoveredGKRTable8, PreparedLocalsTerminal5 and PreparedLocalsCondition2. Full root audit passes 2,743 checks. Arbitrary recovered coefficients deterministically decode via lowerZeta to one table; inverse Mobius, packed current/next, GKR private functional, sparse coefficient/repeated weight and heterogeneous lane functionals are proved exactly. This does not assert equality to arbitrary committed source tables or acceptance of adversarial claims. Near-case checked sumcheck composition remains next.

Locals root return and gas-exhaustion now use actual setup/CODE/fee authentication and interpreter semantics, with trace terminal flags/gas derived from literal constraints. Branch-condition zero equivalence is instantiated from the new literal profile. Block/branch successor and whole-call induction remain pending. Evidence: results/recovery-terminal-integration.json. No full NEAR/recursion/128-bit quantum security claim.

### Joint near-case count and first locals-enabled diagnostic proof

Root reviewed/integrated JointRepresentativeNearCase2; full audit passes 2,745 checks. One actual joint representative and slot geometry derive simultaneous proximity for arbitrary functional families using the same tuple/agreement set. Checked quadratic weighted sumcheck residual-candidate count is bounded by2*n/|S|; tables/strategy are fixed before that sumcheck and the tuple is fixed, with explicit uniqueness inequality/domain hypotheses. This does not yet compose upstream AIR/GKR randomness or cryptographic Fiat-Shamir/QROM.

Root ran the full existing GKR/PCS pipeline on the actual locals-taken fixture (two32-row tables, widths818/235), generated compact binary, verified in a fresh process and rejected six wire mutations. Proof38,499B +public2,696B =41,195B; SHA2561f9161b69b12b45a186df104b1623d2d099f37e9097eabdfa664c37ba5e15d34. Canonical AIR is verifier config excluded from accounting. Q8/Ext4 diagnostic only, not128bit security, fullNEAR, recursion or the still-pending whole-call semantics theorem. Evidence: results/joint-near-case-integration.json and results/prepared-locals/diagnostic-proof/root-review.json.

### Shared call/input and complete record decoding integration — 2026-10-15

Root reviewed and integrated frozen SharedCalls (22) and SharedInputRouting (8), then proved SharedDecode (6) and SharedBlockDecode (3). The full `check.py` build, theorem/axiom inventory and scope checks pass at 2784. Call phases, six-row active prefix, full 32-limb IV resets/state links and final public digest indexing follow from actual shared AIR. Record A/C decode all eight state words; M decodes all sixteen actual schedule words, and D is exactly the 48-byte truncation. Source hashes and scope are in `research/near-compression/results/shared-record-decoding-integration.json`.

Remaining: compose call-to-record transfers and canonical input matching into full shared-message soundness. This milestone does not prove verifier acceptance implies AIR validity, recursive compression, quantum soundness, or full NEAR/1Pgas capacity. Existing reduced-security sizes are unchanged.

### Canonical shared-message block decoding — 2026-10-15

Root integrated InputMatch3, CallRecords5, CallState3 and Chain1; proved PairedByteDecode2 and SharedPaddedBlock2. Full build/axiom/scope audit PASS2800. The generic decoder proves unique low/high bytes from field limbs using explicit bounds and Boolean source bits. Its concrete shared-AIR instantiation discharges those bounds and matches actual call/block input and node record, yielding exactly the selected128-byte canonical padded committed-message slice. Full state initialization/chaining and public digest transfer also compile. Report/source hashes: `research/near-compression/results/shared-padded-block-integration.json`.

The Chain helper explicitly takes an internal compression equation; final shared-message theorem must discharge it, and is pending in the protocol agent lane. Root inspected the new actual runCall theorem (setup+entry checks, AIR, sufficient fuel), but its dependency chain and published terminal binding remain pending root integration. None of these results upgrades reduced-security benchmark parameters or proves full NEAR/1Pgas or quantum soundness.

### Bounded locals runCall and shared SHA384 component soundness — 2026-10-15

Root reviewed and integrated the19-module locals control/run dependency chain (47public theorems) plus SharedMessage4. Full `check.py` build/axiom inventory/scope PASS2851, only propext/Classical.choice/Quot.sound in checked closures. Source hashes and exact assumptions: `research/near-compression/results/locals-run-shared-message-integration.json`.

`prepared_locals_public_run_call` derives actual outer runCall and published DONE/failure boolean, fast gas and live i32 stack from literal AIR, executable setup/CODE+entry checks and sufficient fuel. Both taken/untaken branches, local get/set/tee, block/end, gas exhaustion, terminal sync and DONE suffix are composed. ExitPC remains metadata. Scope is the single-function stack8/locals4 supported control profile, preparation outside AIR; no general memory/host/call semantics. The earlier41195-byte diagnostic artifact is unchanged and remains Q8/Ext4; this theorem closes its profile's semantic composition gap, not cryptographic acceptance-to-AIR.

`sha384_shared_message_sound` now derives standard SHA384 of each actual decoded267-byte input equals its public48-byte slice using only shared AIR HoldsP and call<2. It discharges all internal matching, padding, full eight-word IV/chaining and compression premises. Root binding and cryptographic verifier soundness remain separate. Five-node/two-call specialization remains; no secure size, recursion or full NEAR capacity claim follows.

Next agent work: measured-workload-driven instruction coverage extension; configurable shared compression chunks with global node IDs/fanout; concrete causal GKR layer sumcheck identities. Root still needs to integrate the completed compiler-private-vector coverage/ownership modules and check all-support canonical metadata certificates.

### Compiler-indexed recovered assignment and round arithmetic — 2026-10-15

Root reviewed/integrated9modules (31public theorems), full build/axiom/scope PASS2882. Coverage uses actual ceil-packed source/aux columns; all-support interval separation gives distinct keys for the entire current/next live enumeration. Scatter reads each uniquely owned decoded-table MLE and zeros absent slots; its full GKR functional equals the lifted PCS coefficient functional under explicit degree/sparsity. Polynomial ownership is selected before rowpoint/next choices. This constructs a fixed decoded assignment, not AIR satisfaction or committed-source equality. Source hashes: `research/near-compression/results/compiler-private-vector-integration.json`.

Root extended `generate_lane_certificate.py --all-slots` and ran executable Lean checks on three canonical metadata captures (451+451+150=1052lanes). All full-support checks passed. Each capture rejects4overlap mutations plus a synthetic interior-overlap case that passes the old first-slot selector check; existing4malformed selector checks also pass. Report: `results/heterogeneous-metadata/all-supports.json`. These are executable evaluations paired with audited generic checker implications, not closed kernel instance certificates.

Root compared GKRHonestRound definitions against actual `pq384_seed_gkr.prove` axis/index/weight/folded-value arithmetic. Exact quadratic gate-term evaluation, endpoint sums and degree bounds are proved; a checked false round can repair on at most2challenge values, and a false terminal wiring claim on at most1fresh gamma after both inputs are fixed. Concrete cross-round state linkage, full causal GKR count, AIR/commitment binding and QROM remain open. No security or secure proof-size upgrade follows.

### Adaptive GKR bit rounds and complete axis identities — 2026-10-15

Root integrated RoundState6, authored GKRAdaptiveRounds4, and reviewed/integrated AxisExecution7+AxisHistory3. Full build/axiom/scope PASS2902. Exact index-halving, affine input folding and gate-weight update determine the honest next claim. Prefix-only adversarial polynomial/claim strategies receive an ideal checked-path error bound2*r/|S| with no assumed honest polynomial or endpoint linkage; malformed branches are excluded by actual degree/endpoint/claim-update checks. Initial values and terms are fixed before the challenge path.

Complete-axis folding equals MLE; weighted terms accumulate equality-basis factors. Left-axis endpoint equals right-axis reset claim, and right-axis endpoint equals verifier wiring on honest input MLEs. History/point conversion preserves little-endian challenge order. All gate index bounds and axis-length equalities are explicit. Source hashes/report: `research/near-compression/results/gkr-adaptive-axis-integration.json`.

Remaining: combine both axes and fresh gamma into full layer error bound, compose layers/terminal compiler/AIR semantics, establish commitment and QROM reductions. These are ideal finite counting results, not a cryptographic128-bit claim. Agent scalable11-node source-cell savings and typed-i64 gadget work are preliminary and await independent root review.

### Two-axis false-claim persistence and conditional gamma — 2026-10-15

Root added GKRLayerSoundness2 and exposed the adaptive axis bad-path count in GKRAdaptiveRounds (+1). Full build/axiom/scope PASS2905. Two actual checked axes compose via the proved reset and wiring identities, with right messages allowed to depend on the full left path and only prior right challenges. Outside explicit left/right bad events, a false initial weighted gate claim reaches terminal wiring still false; both sent input evaluations are fixed before the at-most1bad fresh gamma. No assumed honest wiring/polynomial premise enters this composition.

Report: `research/near-compression/results/gkr-two-axis-soundness-integration.json`. The unconditional full-layer count must still combine both axis budgets and gamma; multilayer/compiler/AIR/commitment/QROM composition remains open. Pending independent review: frozen typed-i64 gadgets/fixtures, configurable11-node chunk witness/checker, output-weight/signed-balancing compiler lemmas. Protocol agent launched one full chunk diagnostic job; no proof-size result is claimed yet.

### Complete ideal GKR layer repair bound — 2026-10-15

Root proved GKRLayerBudget3: conditional scaled finite-sum bound, adaptive two-axis+fresh-challenge Cartesian budget, and concrete `gkr_layer_repair_count`. Full build/axiom/scope PASS2908. The final bound is(4*m+1)/|S| for mquadratic rounds in each axis and1freshgamma. The cross-multiplied theorem handles exact nested finite counts without division; sample is distinct and draws are ideal uniform with replacement.

The actual checked repair event includes degree<3, endpoint sums, claim updates, axis reset, terminal wiring and equality of next claim to the honest input functional. Initial values/gates are fixed before the layer; right strategies may depend on the whole left path, and a/b may depend on both completed axis paths but not gamma. Both axis bad-event budgets are now included unconditionally. Source hash and exact scope: `research/near-compression/results/gkr-layer-budget-integration.json`.

This closes the single-layer ideal repair-count gap, not whole-proof acceptance soundness. Multilayer composition, compiler/AIR connection, commitment binding and QROM remain open; no PQ128/fullNEAR/secure-size claim follows.

### Independently verified configurable11-node compression diagnostic — 2026-10-15

Root hash-matched and copied all6frozen exporter/checker/runtime sources, regenerated byte-identical canonical spec and all4witness tables from caller config, reran7,300,624canonical residuals, all5natural buses and21routing/binding negatives. Fresh ordered-use reordering preserves local/natural relations but is rejected against the original external commitment. Root separately reran10exporter dimension/range/capacity/output negatives, all rejected before trace export.

Fresh-process compact binary verification with preexisting expected-use receipt PASS. Archived package `research/near-compression/results/sha384-node-chunk/`: proof111051B including4source commitments, public0B, receipt732B, total111783B. Proof SHA256807ae1d1fff863ceabcf87134b60b2cbe3394c225f2ba82fd2c6c4abef587675. Static canonical AIR/spec (~1.14MB) remains verifier configuration external to payload and digest-bound by receipt. Root replay report `root-review.json`; full agent timings preserved:331.40s after fixedreceipt, including repeated verifier work, not a controlled throughput benchmark.

Root recomputed source-cell comparison from actual old267 spec:5independent core+endpoint calls6732880cells; new4tables5392192cells; saving1340688=19.9125486%. Input/call provenance excluded both sides; this is not measured proof-size saving. Old endpoint width1668, correcting estimator1666 by40cells. Shapes1024x5234,16x1666,16x191,16x179. Chunk interval13208..13218,15declared unique-call-step uses,13fanoutbits.

Scope: compression records only, Q8/Ext4 diagnostic. Ordered-use root/context externally fixed before proof; full call-chain/IV/padding/digest provenance, cross-chunk coverage and aggregation are open. Existing shared semantic theorem is fixed5node/two-call; configurable chunk Lean correctness is next agent task, not yet proved. No quantum128, fullNEAR/1Pgas, or secure<300000B completion claim.

### Terminal DAG certificates and configurable chunk foundation

Root audit PASS: 2,933 actual-semantics bridge theorems and boundary regression examples. Integrated output-query weights, signed balancing, DAG execution and structural layer certificates, followed by eight configurable chunk local-contract lemmas. Chunk AIR definitions exactly match the frozen measured exporter. Root replayed compiler certificate generation and validation on two 81,268-node/41-layer captures and one 99,201-node/59-layer capture; all passed JSON roundtrip and all 27 malformed certificates were rejected. Capture validation is Python evidence, not a closed Lean proof or source AIR-to-emitter refinement. Configurable full compression composition and whole-protocol quantum security remain open. Evidence: research/near-compression/results/terminal-dag-chunk-integration.json and results/terminal-dag-certificates/report.json.

### Typed arithmetic and configurable chunk routing

Root audit PASS: 2,954 actual-semantics bridge theorems and boundary regression examples. Added PreparedTypedValue9/PreparedTypedStep5: four-limb bounds, no-wrap limb-sum eqz, exact typed i64 const/add/eqz execution and prepared charging. Root freshly generated actual Lean fixtures and AIR AST; independent replay passed three actual prepared runs, 251 gadgets, 1,890 constraint mutations and 11 type-transition rejections. Added SHA384NodeChunkRouting7: complete 177-field use/record matching and exact natural bus multiplicity conservation. Global-base cancellation is a field-level injectivity result; natural range/no-wrap must remain explicit where required. Full typed EXEC composition, generalized chunk compression and quantum security remain open. Evidence: results/typed-routing-integration.json and results/prepared-typed/root-review.json.

### Source-program to physical-layer composition

Root reviewed and integrated six reconstruction modules (15 public theorems), then added TerminalProgramLayer.terminal_program_layer_value: structural source rebuilding plus DAG-to-layer certificates derive exact source ABI register / physical circuit output equality. Explicit source slot binding and certificate premises remain; no assumed compiler-output equality. Actual rebuilding certificate generation and AIR AST-to-ABI semantics remain open. Also integrated SHA384NodeChunkNodes11 tying bounded configurable nodes through actual natural bus balance to standard compression and full output records. Final audit PASS: 2,981 actual-semantics bridge theorems and boundary regression examples. Evidence: results/program-layer-chunk-integration.json. No full NEAR capacity or quantum security certification.

### Configurable declared-use semantics and full typed source replay

Root reviewed/integrated ChunkDecode9 and ChunkUse5: actual HoldsP plus numeric count/use bounds and explicit base+count≤P imply every declared use has a bounded natural ID, exact full state A, a canonical128-byte block M, full output C=standard compression(A,M), and D=48-byte truncation. No caller routing/compression premise. Cross-chunk coverage, call chain and commitment binding remain open. Root integrated frozen typed literal source and Code7 provenance checker after verifying all nine source hashes. Fresh Lean exports match Python AST exactly at local counts0..4. Fresh actual PREP checker:7 cases,5439 fields,5614 malformed inputs rejected. Full typed source replay: 19 cases, 747 rejected mutations. Typed whole-call formal refinement remains open. Audit PASS:3002 actual-semantics bridge theorems and boundary regression examples. Evidence: results/chunk-use-typed-profile-integration.json and results/prepared-typed/profile/.

### Independent captured reconstruction and imported-definition parity

Root independently replayed rebuilding certificates for all three captured compiler runs:62420,62420,82795 retained source registers. Added explicit finite nonnegative integer index and Boolean sign checks to align Python certificate domains with Lean Nat/Bool. Final rerun rejected42 malformed certificates, including swapped current/next inputs and invalid index types;14 arithmetic-route examples cover all10 constructors and reject14 wrong results. Certificates roundtrip through JSON. These are executable structural-premise checks, not kernel-checked capture instances or AIR-expression lowering correctness. Fresh root exporter importing the audited configurable chunk definitions reproduces the historical11-node spec and all four traces byte-identically. Audit unchanged3002; no new theorem added this milestone. Evidence: results/rebuild-imported-parity-integration.json; results/terminal-rebuild-certificates/report.json; results/sha384-node-chunk/imported-definition-parity.json.

### AIR-expression composition, ordinal coverage and typed source bounds

Root integrated AIRProgramLowering3 and added AIRLayerComposition.air_layer_expression_value composing exact Expr evaluation with ABI execution, optimized DAG rebuilding and physical layer routing. Structural certificates and explicit input/environment bindings remain; no AIR satisfaction or non-Boolean-point/trace-row identification assumed. Integrated ChunkOrdinalCoverage8: deterministic interval owner and ordered ordinal filtering give exact unique finite chunk/local coordinates and reconstruct arbitrary original values including duplicates. Ordered-use commitment binding remains separate. Integrated PreparedTypedSource6: exact literal membership derives all Boolean columns excluding both inverse witnesses, SP onehot, local public type equality, stack limb<2^16 and word<2^64. Audit PASS3020 actual-semantics bridge theorems and boundary regression examples. Evidence: results/air-layer-coverage-typed-integration.json. Full target remains unachieved.

### Unequal adaptive layer budget and final chunk bounds

Root added AdaptiveLayerBudget2: finite challenge-block tree failure count is at most total mass, and count*commonScale≤sum(per-layer errors)*totalMass under causal per-history scaled bounds. Layers may use different sample lengths and retain multiplicity. This prepares but does not itself instantiate the full multilayer GKR repair/acceptance theorem, nor Fiat–Shamir/QROM. Integrated ChunkIntervalBounds3 for exact min(capacity,total−base) node count, positive owner interval, global range and remainder/local-coordinate reconstruction, covering short final chunks without fictitious nodes. Audit PASS3025 actual-semantics bridge theorems and boundary regression examples. Evidence: results/adaptive-layer-interval-integration.json.

### Exact GKR layer blocks and actual AIR-program certificates

Root added GKRChallengeBlock3: Cartesian layer blocks have exactly |S|^(2m+1) entries; event count equals the earlier nested ru/rv/gamma count; single-layer false-claim repair bound is (4m+1)/|S| in the block form needed by AdaptiveLayerBudget. Full causal multilayer protocol instantiation remains open. Integrated AIRProgramAccumulation3 for literal ordered mixing and final register copy. Root replayed actual AST/mixing certificates against fresh compile_weighted outputs for all69tables/30432expression roots, with415 malformed/synthetic rejections. Added explicit complete table count check before zip. Auxiliary residual formulas and kernel capture instances remain open. Audit PASS3031 actual-semantics bridge theorems and boundary regression examples. Evidence: results/gkr-block-air-accumulation-integration.json and results/air-program-certificates/report.json.

### Typed stack values and unconditional per-strategy repair bound

Root integrated PreparedTypedStackValues4/PreparedTypedEqzSource3, deriving canonical i32/i64 stack values and actual selected-word eqz from literal source constraints. Positive SP/onehot explicit until opcode-guard refinement; no full successor assertion. Added GKRStrategyRepair.gkr_strategy_repair_bound: explicit causal layer-strategy structure and guarded false-to-true repair event get unconditional bound (4m+1)/|S|, including already-correct incoming claims where the event is empty. This prepares but does not finish multi-layer acceptance composition. Audit PASS3039 actual-semantics bridge theorems and boundary regression examples. Evidence: results/typed-stack-gkr-strategy-integration.json.

### Actual adaptive GKR repair union and global chunk composition

Root added GKRAdaptiveLayers2: strategy at each layer boundary depends on all prior layer challenge blocks; exact within-layer causal strategy types and proven single-layer bounds discharge every conditional error bound. Ideal finite repair-event union count obeys count*|S|≤sum_i(4m_i+1)*totalChallengeMass for arbitrary layer axis lengths. No caller per-layer soundness premise. Still not whole-proof acceptance, commitment binding or Fiat–Shamir/QROM. Integrated SHA384ChunkComposition3, deriving each declared global ordered use standard compression from actual component HoldsP and explicit SHA384ChunkUseBinding. Integrated PreparedTypedEqzGuard2: actual active/charged/opcode source guards derive nonempty selected i64 operand and correct eqz. Audit PASS3046 actual-semantics bridge theorems and boundary regression examples. Evidence: results/multilayer-chunk-guard-integration.json.

### Independent full DAG use coverage and payload consistency

Root replayed check_sha384_chunk_coverage.py on actual hash-call-map/compression-records:32587 declared unique-call-step uses,22474 nodes,899 chunks with final24nodes, all256 A/M/C bytes preserved,10 malformed partition/payload mutations rejected. Original occurrence-step frequency count41542 is separate; original chronology is not recovered from this map. Integrated SHA384ChunkConsistency2: repeated global node IDs imply identical full176-field payloads from actual AIR and explicit ordered-use binding. Integrated BusAuxiliarySemantics6: exact square/pi chain equations and Boolean multiplicity bits imply fingerprint^multiplicity, including zero fingerprint. Actual captured interactions are one-bit, so longer chain executable evidence remains separate. Audit PASS3054 actual-semantics bridge theorems and boundary regression examples. Evidence: results/bus-coverage-consistency-integration.json.

### Checked GKR path implies a counted repair event

Root added GKRCheckedPath3. Explicit checked sumcheck/wiring predicates and correct next-input functional yield guarded repair; adjacent correctness equivalence follows from named transmitted-claim/fixed honest-functional identities. Induction proves a false initial claim reaching a checked correct terminal functional must contain a repair event. Empty/mismatched paths rejected. Adjacent circuit/query identities remain explicit and must be discharged against the full fixed circuit before claiming cryptographic acceptance soundness. Audit PASS3057 actual-semantics bridge theorems and boundary regression examples. Evidence: results/gkr-checked-path-integration.json. Parallel chronology/auxiliary handoffs await independent root review/replay.

### Independent chronological replay and auxiliary program formulas

Root replayed the saved configured seed verifier in11.48s with exact input proof/statement/record provenance checks, capturing13698 hash invocations and41542 ordered occurrence steps. All keys, returned digests, first-seen11181unique-call IDs and frequency histograms match. Both chronology output files byte-identical to independent agent run. Structural checker reconstructs all899chunk subsequences and rejects9mutations; coordinated alternative ordering is distinguished by replay provenance, not structural histogram checks alone. Unique-call-step count32587 remains a separate space. Integrated BusProgramFormulas5/GateSoundness3. Root fresh formula replay:1596 real residual matches/rejections;8synthetic0/1/2/4bit and zero/mixed-field cases give64 independent aux.evaluate comparisons and64 wrong-formula rejections. Captures only exercise1bit interactions. Audit PASS3065 actual-semantics bridge theorems and boundary regression examples. Evidence: results/chronology-bus-program-integration.json. Commitment binding, call chaining and PQ security remain open.

### Full-state observed call chains and typed eqz stack writes

Root independently replayed certify_sha384_occurrence_chains.py:11181unique framed hash inputs have canonical pad/IV/full512state links/final48digest, independently checked compression states and hashlib; all13698observed occurrences map to41542ordered uses. Eleven chain/padding/state/order mutations rejected; both certificate files byte-identical to agent run. Executable provenance only, not commitment binding or Lean capture refinement. Integrated PreparedTypedOpcode1 and PreparedTypedEqzStack4: source opcode onehot excludes unrelated flags; literal writes derive every next stack limb/tag and exact top i32 eqz result while preserving other typed slots. Full state and CODE37 provenance remain open; parallel lanes assigned to each. Audit PASS3070 actual-semantics bridge theorems and boundary regression examples. Evidence: results/call-chain-typed-stack-integration.json.

### Linked checked-path budget and full semantic compositions

Root reviewed/integrated SHA384ChunkCallChain4: actual component AIR yields each canonical block compression through word equality; exact128-byte consumption and explicit standardIV/full-state links compose to SHA384 digest. Commitment binding, ordered call-item provenance and framing remain explicit. Integrated WeightedTerminalSemantics4/TerminalBooleanRowSemantics2 for exact weighted source+aux residual equality through accumulation and DAG rebuilding, with separate concrete-row specialization. No mixedzero→allzero inference. Root added GKRPathCount3: full Cartesian path length and repair-event count equal recursive mass/tree counts; linked checked-path acceptance count*|S|≤sum(4m+1)*totalMass. Adjacent fixed-circuit linkage and correct final PCS input are still explicit relation premises; this is ideal random-challenge soundness, not cryptographic acceptance/Fiat–Shamir. Audit PASS3083 actual-semantics bridge theorems and boundary regression examples. Evidence: results/linked-budget-call-terminal-integration.json.

### Canonical hash framing and fixed-circuit adjacent GKR link

Integrated SHA384HashFraming5: canonical24-byte prefix, u32 tag/count, u64 part lengths, exact total size and bounded decoding. Root fresh Lean exporter parity against actual Python hash_parts updates passed11181captured unique calls+5edgecases,2987143bytes,7type/length rejections. Root added GKRFixedLayerLink2: next weighted gate functional equals previous input functional from exact [(ru,1),(rv,gamma)] queries and fixed circuit gate evaluation, requiring equality only on finite padded layer domain. This discharges the abstract honest-functional identity in adjacent correctness; transmitted claim binding remains explicit. Audit PASS3090 actual-semantics bridge theorems and boundary regression examples. Evidence: results/framing-fixed-link-integration.json and results/sha384-hash-framing/report.json.

### Typed authenticated eqz and framing decoder integration

Integrated ten frozen modules (43 public theorems); full root check.py PASS with 3,133 audited theorems. CODE natural bus/public record provenance now derives actual prepared instruction and gas charge. The successful i64.eqz theorem derives actual Wasm.step and complete next typed state from literal HoldsP, actual setup check, current typed state, function agreement, active opcode and sufficient gas. Entry initialization, other opcode cases and whole-call composition remain open. SHA384 bounded frame decoder proves exact tag/ordered-part recovery, framing injectivity and trailing-byte rejection; this is not hash injectivity. Evidence: research/near-compression/results/typed-eqz-framing-integration.json; /tmp/root-typed-eqz-framing-audit.log. No quantum-security or full-NEAR proof-size certification.

### Fixed-circuit GKR path composition

Added GKRCircuitPath.lean with two public theorems, root check.py PASS3135. A recursive relation fixes circuit values/wiring independently of transcript history, requires actual next-query weighting and transmitted claim equality, and uses exact terminal MLE evaluations. It derives all adjacent correctness links and the existing ideal independent-uniform challenge path bound sum(4*m+1)/|S| (cross-multiplied counting form). This closes the abstract adjacent-link interface for structurally linked circuit paths; actual Python verifier refinement, PCS authentication and FS/QROM remain open. Source inspection confirms query/claim updates in pq384_seed_gkr.py:63 and pq384_terminal_gkr.py:157 match this interface; inspection alone is not a refinement proof. Evidence: results/gkr-circuit-path-integration.json and /tmp/root-gkr-circuit-path-audit.log.

### False root output and strict decoded hash-call composition

Root audit PASS3141. Added GKRRootOutput2: Boolean selected actual gate output mismatch implies wrong initial claim and the fixed-circuit path budget, with distinct input/output dimensions. Corrected GKRCircuitPath terminal interface after inspecting actual verifiers: requires the combined query functional returned by obligation(), rather than unnecessarily requiring separate correct a/b openings. Added SHA384HashDecodeSound4: arbitrary successful decoder input equals canonical framing, then actual chunk AIR/compression chain proves its hash. Actual PCS binding and transcript operand wiring remain explicit. Evidence: results/root-output-decoder-integration.json; /tmp/root-output-decoder-combined-audit.log. Prior circuit-path source hash is historical and superseded by this report.

### Recovered terminal opening and typed initial state

Root audit PASS3155 (14 new public theorems). GKRRecoveredTerminal proves exact sequential known-constant subtraction as used by obligation(), and equivalence between its recovered PCS coefficient opening claim and full combined GKR input functional. Degree, sparse-image and lane-validity premises remain explicit; no commitment binding claim. PreparedTypedBoundary/Initialization/Entry derive51-field natural public boundary binding and actual enter plus full initial typed state from SetupCheck, entry check and literal HoldsP, including tagged zero locals and initial gas. No initial-state correctness premise. Scope remains bounded prepared-typed-v1; full instruction run and NEAR1Pgas are open. Evidence: results/recovered-terminal-entry-integration.json; /tmp/root-recovered-terminal-entry-audit.log.

### Authenticated typed constant and transcript commit

Root audit PASS3165 (10 added theorems). Four Const modules derive literal stack/tag writes, bounded SP increment, full actual i64.const successor and actual setup/code/fee authentication. SHA384TranscriptCommit derives the domain-separated commit transition from chunk AIR plus explicit ordered seed/label/payload operand check. Root independently ran Python-vs-Lean parity:3 sequential actual commits match SHA384 outputs and8 seed/domain/operand/framing mutations reject. Per-instance transcript wiring still must be enforced in recursive AIR; no chronological single-instance assumption. Evidence: results/const-transcript-integration.json; results/sha384-transcript-commit/report.json; /tmp/root-const-transcript-audit.log. Full NEAR capacity, commitment authentication and128-bit quantum security remain open.

### GKR versus terminal authentication failure decomposition

Root audit PASS3167. GKRTerminalFailure2 removes unconditional terminal correctness from the protocol-check relation. Accepted false-root paths split into checked-to-correct-input paths or accepted incorrect combined terminal openings. The counting theorem bounds total acceptance by the proved ideal GKR term plus the explicitly retained accepted-terminal-failure count. It does not assert PCS binding or hide its error as zero. Evidence: results/gkr-terminal-failure-integration.json; /tmp/root-gkr-terminal-failure-audit.log.

### Typed terminal and quiet-row semantics

Integrated PreparedTypedTerminal5, QuietStack3 and QuietControl2; root audit PASS3177. Actual setup/code/fee provenance plus current typed state now derives gas-exhaustion abort with real synchronization/error semantics, and root-end completion with empty stack/frame return/refund. Literal constraints derive quiet stack limbs/tags/values, SP, PC and label preservation. Quiet locals, repeated padding and whole-call composition remain in the instruction lane; gas-context propagation has been flagged explicitly for composition. No fullNEAR/security/size completion claim. Evidence: results/typed-terminal-integration.json; /tmp/root-typed-terminal-audit.log.

### Typed padded public exit

Root audit PASS3190 (13 new theorems). Integrated QuietLocals3, Padding6 and GasContext2. Added PreparedTypedPaddedExit2: actual public boundary balance identifies final status bits and repeated DONE preservation connects any reached terminal row to public exit gas/failure/status. Snapshot includes all four stack limbs and type tags, so no lossy field-packed64 equality is assumed. The theorem does not assume or establish that arbitrary execution reaches DONE; opcode coverage and whole-call composition remain pending. Actual continuation gas-context preservation is now available to compose future exhaustion steps. Evidence: results/typed-padded-exit-integration.json; /tmp/root-typed-padded-exit-audit.log.

### Draw sampler semantics and failure snapshot

Root audit PASS3205. Integrated SHA384TranscriptDraw14 with exact request/squeeze/ratchet/result tags, bounded counters, LE32 rejection sampling, exact accepted-vector length/range and failure seed preservation. Root independently passed12 Python-vs-Lean cases including real hashes, scripted reject/crossblock/exhaustion, invalid dimensions, and one wrong hash-input mutation. No hash-uniformity or FS/QROM inference. Integrated PreparedTypedExhaustion1: actual authenticated abort plus complete frozen pre-trap row payload, explicitly distinct from synchronized failure gas. Evidence: results/draw-exhaustion-integration.json; results/sha384-transcript-draw/report.json; /tmp/root-draw-exhaustion-audit.log.

### Draw budget and counter encoding bounds

Root audit PASS3208. Added SHA384DrawBounds3: scan accepted/rejected consumption is bounded by input word count; successful loop returns a block count strictly above starting counter and at most counter+fuel, with consumed words≤12*(blocks-counter). Successful public requests derive block count≤maxBlocks, u64 bounds for final counter/count/coefficients and count*coefficients+rejections≤12*blocks. This is deterministic resource/encoding bookkeeping only, not hash-uniformity or probabilistic termination. Evidence: results/draw-bounds-integration.json; /tmp/root-draw-bounds-audit.log.

### Authenticated i64.add integration

Reviewed and integrated six Add modules,15 public theorems; root audit PASS3223. Actual literal type guards derive≥2 live i64 operands; four carry equations plus source bounds establish exact modular64 Num.binop. Literal writes, depth, PC/gas and preserved locals/labels compose into actual authenticated Wasm.step successor. No supplied arithmetic result, instruction/fee equality or successor certificate. Remaining arithmetic/drop work delegated separately from local/control lane. Merkle lane review explicitly requires collision witness in concrete queried path messages, not merely globally existential hash collision. Evidence: results/typed-add-integration.json; /tmp/root-typed-add-audit.log.

### Typed local source constraints

Root audit PASS3230. Integrated LocalIndex2, LocalUpdate4 and LocalDepth1. Literal constraints derive onehot selector within declared local count, exact two-limb immediate index, type-matched four-limb store with other locals preserved, and natural get/set/tee stack updates including capacity/nonempty guards. Intermediate opcode/selected-SP premises remain explicit pending full authenticated successor composition. No whole-call or fullNEAR certification. Evidence: results/typed-local-source-integration.json; /tmp/root-typed-local-source-audit.log.

### Full terminal claim to recovered PCS near case

Root audit PASS3231. GKRTerminalNearCase connects an incorrect full GKR input functional to the recovered heterogeneous near-case sumcheck bound through exact executable constant subtraction. The full input and PCS side use the SAME polynomial tuple, and no caller-supplied private-claim mismatch is needed. Bound remains conditional on a fixed joint proximity representative, sparse recovery/geometry and separation; far-case, actual proximity/commitment verification, and FS/QROM remain open. Evidence: results/gkr-terminal-near-integration.json; /tmp/root-gkr-terminal-near-audit.log.

### Concrete supported Merkle collision reduction

Root audit PASS3235. Reviewed/integrated SHA384MerklePath4. Conflicting accepted leaves at fixed root/context/count/index imply a collision with one framed byte input in each actual verification query list, rather than a globally existential collision. Exact support length depth+2. Root independently reran14 honest paths,16 mutated paths,22 nonempty exact hash-input query sequences against Python; PASS. Shape-rejected paths have no Python queries; fixture enumerates abstract candidate path queries separately. No collision probability/QROM/security-level certification; fixed committed source tree model/correctness now assigned to protocol lane. Evidence: results/merkle-path-integration.json; results/sha384-merkle-path/report.json; /tmp/root-merkle-path-audit.log.

### Typed i32.const and mixed drop

Root audit PASS3249. Reviewed/integrated eight modules with14 public lemmas. i32.const authenticates exact immediate and actual successor while preserving arbitrary existing mixed stack tags. Drop derives positive depth, removes actual arbitrary Val, preserves mixed prefix and produces full typed successor without an all-i32 assumption. Literal source memberships, code/charge authentication, PC/gas/local/label changes all checked. Remaining i32.add, locals/control and whole-call composition continue; fullNEAR/PQ128/sub300KB not claimed. Evidence: results/const32-drop-integration.json; /tmp/root-const32-drop-audit.log.

### Typed i32.add/local.get and fixed-source Merkle binding

Root audit PASS3279, adding30 public lemmas in12 modules. Authenticated i32.add derives input types, underflow exclusion, modulo32 arithmetic and complete mixed successor; local.get derives selected local and exact typed stack push from literal AIR and authenticated CODE/fee. Fixed-source Merkle construction proves honest path folding/acceptance and arbitrary accepted leaf equality or a collision in actual arbitrary/source path query supports. Independent root parity PASS:56 layer digests,4 roots,30 paths;30 changed source leaves rejected in BOTH Python and Lean (root strengthened the fixture beyond agent Python-only negatives). Evidence: results/instruction-merkle-source-integration.json, results/sha384-merkle-source/report.json, /tmp/root-instruction-merkle-audit.log. Store and execution-shape handoffs await review; control and whole-call composition continue. No unknown-root extraction, QROM bound, fullNEAR capacity or secure sub300KB claim.

### Typed local stores and execution shape

Root audit PASS3288. Integrated9 public lemmas: actual authenticated local.set/local.tee successors preserve complete mixed TypedState with exact local Array.set! and stack pop/preservation; opcode totality and active-nonlast are derived from literal AIR (lastDONE source index1618+66*(4-count), kernel verified). Type guards feed the actual local-value write theorem; no selected-local or successor certificate is assumed. Nine non-control operations now have authenticated typed successors; root end/exhaustion separately checked. Mixed block/br_if/nested-end and whole-call induction remain in progress. Evidence: results/typed-store-shape-integration.json, /tmp/root-store-shape-audit.log. FullNEAR/1Pgas/recursive aggregation/PQ128/sub300KB remain unachieved.

### Terminal public output and runCall eligibility

Root audit PASS3291. Root added PreparedTypedTerminalPublic2: actual successful root-return step carries public exit gas/status through arbitrary DONE padding; actual exhaustion abort has public failure status and public gas equal to the pretrap fast-gas snapshot. The latter is deliberately not equated to synchronized abort gas. Integrated agent TerminalWitness (structure separates raw/final/sync) and RunCallCheck1 (actual setup+entry check decomposition). Evidence: results/typed-terminal-public-integration.json; /tmp/root-terminal-public-audit.log. Concrete whole-call induction awaits authenticated mixed control wrappers; a separately reported conditional interface check is not counted as concrete driver completion.

### Authenticated typed block and nested end

Root audit PASS3301. Reviewed/integrated5 modules/10 public lemmas for block entry and nested-end actual successor states. All four stack limbs and type tags are preserved; no all-i32 prefix restriction. Actual SetupCheck/CODE37 provenance derives opcode, gas charge and endOf target. Block guard derives absence of an existing inner label; this remains the bounded single-void-block profile, not general nested control. br_if is the sole remaining opcode successor case. Whole-call draft conditional composition is not a completed concrete proof. Evidence: results/typed-block-end-integration.json; /tmp/root-block-end-audit.log. Reviewed pending SHA384PackedSourceBinding5; independent root parity/integration remains next.

### Packed-source bytes to verifier lane pairs

Root audit PASS3306. Integrated SHA384PackedSourceBinding5: canonical LE32 injectivity, entire authenticated source word vector equality or supported Merkle collision, and exact projected beta pair equality or collision. Root parity independently PASS on actual Python source_tree FFT degree128/3lanes:all256 leaf encodings/root,6 full-domain positions with nonbase Ext4 beta weights,11 Python mutation rejects. Root additionally strengthened Lean fixture to reject all6 changed lane slots; PASS. Evidence: results/packed-source-binding-integration.json; results/sha384-packed-source/report.json; /tmp/root-packed-source-audit.log. Fixed source root and canonical words are explicit; source semantics/native refinement, packing-context theorem and adversarial shared representative recovery remain open. No quantum collision bound or secure proof-size claim.

### Terminal witness publication and computed-source authentication

Root audit PASS3312. Reviewed/integrated WitnessPublic1 and SHA384ComputedSource5. Terminal witness publishes padded status/error and piecewise affordable-debit/pretrap gas, explicitly excluding synchronized abort-gas equality and full live-stack decoding. Computed-source theorem derives canonical words from Fp pairs and composes Merkle binding with the modeled packed Möbius/FFT schedule, yielding the same sourceWideLeaf polynomial semantics or a collision in actual path-query supports. Removed external received-leaf/source semantic equality premise for a fixed computed root. Native implementation refinement and adversarial-root recovery remain separate. Evidence: results/witness-computed-source-integration.json; /tmp/root-witness-computed-audit.log. FullNEAR/1Pgas/PQ128/sub300KB remain unachieved.

### Computed-source implementation parity underway

Added SHA384ComputedSourceFixture.lean and test_sha384_computed_source.py. Four source-table shapes compare all packed coefficients, source words and SHA384 roots to actual Python source_tree and an independent nested-interpolation oracle;3 partial final lanes included. Check launched in exec session68201 (Lean PID2773524); verified live and CPU-active, no result yet. Log /tmp/root-computed-source-parity.log; progress results/computed-source-validation-progress.json. Resume this exact process before claiming PASS or restarting.

### Branch prerequisites and public mixed-stack decode

Root audit PASS3331. Integrated19 lemmas: branch condition i32 tag/zero test, saved-height strictly below condition operand, exact taken/untaken PC/labels/depth, live mixed-prefix preservation and Array.extract semantics; public boundary51 decodes depth and all tag/four-limb values and transports any DONE stack through padding. Actual authenticated branch wrapper now agent-frozen but not yet root-integrated; interpreter terminal-stack linkage and concrete runCall next. Evidence: results/branch-public-stack-integration.json; /tmp/root-branch-stack-audit.log. Computed-source parity remains running under same session68201; no result claimed.

### Concrete twelve-opcode whole-call composition

Root audit PASS3343. Reviewed/integrated BranchState1/ControlContinue1 plus Run2/RunCall4/PublicRunCall1/TerminalStack3. Literal AIR and actual executable setup/entry checks now prove actual Wasm.run/callEntry/runCall outcome through all12 supported opcode tags, with no conditional branch/step contract. Fuel bounds trace height; terminal function index invariant retained. Public status/AIR gas linked; actual success empty-stack and exhaustion pretrap-stack linkage separately proved, sync preserves stack. Final combined witness-stack packaging remains pending. Scope stays prepared-typed-v1 (stack8,locals≤4,single function/noargs/noresults,single inner void label), no fullNEAR/memory/general calls/loops/hosts. Evidence: results/typed-run-call-integration.json; /tmp/root-typed-run-audit.log. Computed-source parity session68201 remains live after5minCPU; do not infer success or restart. Next instruction lane assigned real memory semantics/consistency interface to expand beyond bounded profile.

### Canonical packing context and certified root

Root audit PASS3352. Reviewed/integrated Context7 and NativePackedSource2. Exact197-byte context is injective in supported n/width/p; fixed computed-source opening theorem now derives half-order, capacity and context-length rather than assuming them. Root independently checked all315 supported n/p pairs at widths1/35/2^20:945 exact Python byte matches and6 invalid shapes rejected. Evidence: results/packing-context-integration.json; results/sha384-packing-context/report.json; /tmp/root-packing-context-audit.log. Native naming denotes literal root formula, not machine refinement. Computed-source parity session68201/PID2773524 verified CPU-active at7min; no PASS or restart. Adversarial root recovery/PQ128/fullNEAR/sub300KB remain open.

### Whole-call result with public mixed stack

Root audit PASS3354. WitnessStack1 derives terminal root-end opcode/absence or exhaustion from actual constraints and combines public stack decoding with interpreter terminal/sync semantics. PublicStackRunCall1 combines actual runCall, public DONE/FAIL, AIR gas snapshot and exact synchronized final stack, without extra terminal-opcode/stack assumptions. Bounded profile and verifier-side setup remain explicit; public PC/locals not claimed. Evidence: results/public-stack-run-integration.json; /tmp/root-public-stack-run-audit.log. Composition agent reassigned to concrete multi-component hash-only aggregation prototype/cost baseline; memory lane expanding beyond bounded profile. Source parity session68201 stillCPU-active8min39s, no result.

### Actual scalar memory semantics and checked stores

Root audit PASS3361. Reviewed/integrated MemoryScalar3/MemoryExec4: exact actual readLE/writeLE loops lowered to ordered byte requests; scalar loads preserve sign-extension/tagging and natural effective address/trap semantics; stores preserve operand pop order and narrowing. Accepted scalar subpage batches identify actual store successor descriptor or collision supported on source-tree/opening messages. Initial actual-memory descriptor, full pages and hash output well-formedness remain explicit. No scalar AIR/gas/CODE/event-bus wiring claimed. Evidence: results/memory-scalar-integration.json; /tmp/root-memory-scalar-audit.log. Multi-component verifier capture correctly identified as a prerequisite, not yet an outer recursive proof. Source parity session68201 remains CPU-active10min with no result.

### Certified evaluation makes computed-source parity executable

Root audit PASS3363. Added SHA384EvaluatedSource2 proving polynomial-evaluation source words/list equal the existing mutable FFT source under the same half-order condition. Evaluated fixture checks literal certified root. Independent parity PASS4 table shapes/76leaves/3partial lanes, all coefficients and roots, against actual Python source_tree plus direct nested interpolation. Source trace update closures caused impractical replay; runtime performance is not prover throughput. Original session68201/PID2773524 intentionally terminated after12min31s only after equivalent evaluator audit/parity passed; session terminal exit1 from SIGTERM, NOT a direct mutable runtime PASS. Evidence: results/evaluated-source-integration.json; results/sha384-evaluated-source/report.json. Old RUNNING progress updated to SUPERSEDED_TERMINATED.

### Verifier source projection and native executable parity

Root audit PASS3365 for NativeProjectedSource2. Fixed computed-source authentication now transfers canonical words into arbitrary challenge-field weighted/lifted pairs; no field homomorphism or Ext4 polynomial evaluation equality is inferred. Root independently reran native rs_commit against certified evaluated source:4cases/76leaves, exact coefficients/leaves/tree/context/root and opening paths. Strengthened agent harness to compare path lists exactly, not merely verify them. Evidence: results/native-projected-integration.json; results/sha384-evaluated-native/report.json; /tmp/root-native-projected-audit.log. Native binary/source hashes recorded; this is bounded runtime parity, not machine refinement. Root rejected initial MemoryRead global existential collision conclusion; agent revised to actual finite queried-source/opening support; revised modules await root review/integration.

### Supported multibyte read collision reduction

Root audit PASS3367. Reviewed corrected MemoryRead1/MemoryLoad1: accepted scalar byte openings imply actual readLE/typed load successor or finite supported collision in source-tree/descriptor and a specific queried opening message list. The prior globally existential collision version was never integrated. Width/bounds/exact opening count checked; subpage/page crossings allowed. Initial honest memory descriptor/fullPages/shape remain explicit; gas/PREP/MEM/hash AIR wiring pending. Evidence: results/memory-read-integration.json; /tmp/root-memory-read-audit.log. Agent two-proof capture preliminarily found423939 compression blocks, substantially worse than previous different seed profile; requested full-chaining-state dedup validation and nontrivial verifier-check compilation before root acceptance.

### Ordered store service refinement

Root audit PASS3369. Reviewed/integrated StoreService2: successful checker implies exact consecutive request clocks and root-chained refinement of actual sequential writeLE, or collision on the relevant intermediate tree/opening support. Clock/event authentication remains explicit; a malicious caller cannot be prevented from relabeling unauthenticated requests by this theorem alone. Store-only sequence is not yet a unified MEM timeline; mixed reads/writes assigned next. Evidence: results/memory-service-integration.json; /tmp/root-memory-service-audit.log. Aggregation agent clarified215216 count is compression blocks summed across distinct whole hash inputs, NOT full-state deduplicated compression nodes; switching sample from codec-reconstructed endpoints to actual fold consistency.

### Concrete extension-field polynomial bridge

Root audit PASS3383, adding14 reviewed lemmas. Canonical Fp word embedding now commutes with actual Fp4 polynomial evaluation and packed Mobius transformation; fixed native source projection concludes genuine challenge-field polynomial values or a finite supported path collision. Root reran flat/tower parity:4 source shapes,7 points each,70 lane evaluations including nonbase points and partial lanes. Evidence: results/ext4-polynomial-integration.json and results/sha384-ext4-polynomial/report.json. Arbitrary-root extraction and FS/QROM remain open.

Strengthened actual-memory smoke completed with exit0: different page patterns and distinct store bytes,16 authenticated reads,4 stores,6 traps, malformed openings/order negatives. Evidence: results/memory-smoke-integration.json. Mixed read/write timeline is being developed separately.

### Mixed read/write service refinement

Root audit PASS3385 after reviewing/integrating PreparedMemoryService2. Accepted checker sequences derive exact intermediate-state read values and final actual-memory descriptor, or a finite collision supported by the intermediate tree/opening/batch messages. Root independently reran real-SHA384 smoke: empty sequence and five read/write events pass; eleven stale/future-root, wrong-value, clock/order and stale-write cases reject. Evidence: results/mixed-memory-service-integration.json. EXEC request authentication, concrete memory AIR, initial-root provenance and bulk/grow/host events remain open. Instruction agent assigned concrete versioned scalar-access constraints.

Reviewed actual two-component capture: original verifiers and disclosed inputs remain necessary; sampled fold residual sum is explicitly diagnostic, not conjunction or recursion. Next full fold certificate must derive row coverage independently and bind domain/nonzero, source pairs, and transcript provenance. No recursive proof or security/size claim added.

### Independent recursive layout cost audit

Root independently recomputed all15627 distinct captured SHA384 hash calls across32829 occurrences and canonical-decoded both layout payloads. Of423939 compression occurrences,273060 (64.41%) hash layout JSON alone; two layouts are7117494 and10358025 bytes. Prior273068 tag-wide count also includes8 statement/claim initialization blocks. Removing only layout calls leaves150879; this is counterfactual accounting, not measured new verifier performance or unique-node accounting. Evidence: results/recursive-layout-cost.json; executable analyzer analyze_recursive_layout_cost.py. Reviewed configured seed verifier: trusted AIR/compiler config, verifier-derived layout, bound public shape/challenges/finals, final seed PCS handoff. Migration requires newly generated versioned proofs and preserving component trusted-input obligations. No recursion, security, or size claim.

### Fixed representative and actual seed migration run

Root audit PASS3389, integrating FixedJointSourceRepresentative4 after source review: coefficient/normal-form uniqueness from universal representatives and explicit RS separation; coefficient identity preserves recovered table; mathematical selection has no later-challenge parameter. Existence/root extraction and acceptance-to-proximity remain open. Evidence: results/fixed-representative-integration.json.

Started actual same-component migration using exact prior sha384-direct spec/packings and original source rows; native commitments/fresh auxiliaries/three constraint tables completed, GKR/PCS still running in session32321 (/tmp/root-direct-seed-prover.log). Added verify_sha384_direct_seed.py preserving mandatory external input receipt and AIR digest checks before trusted config construction; prepared mutation regression test_sha384_direct_seed.py. No new proof/test success claimed. Progress: results/sha384-direct-seed/progress.json.

### Scalar-memory AIR address bridge

Root audit PASS3392 after reviewing first memory-access AIR stage:460 columns,741 degree-at-most2 constraints,19 integer opcodes. Exact Lean/Python AST parity PASS463 expressions covering Boolean/address subset. Root reran380 honest cases,3040 bit mutations,141 coherent mutations and4 invalid-bounds constructor cases. Three Lean lemmas prove Boolean ranges and natural33-bit addition; full successful bounds/result/request refinement remains pending. EXEC and MEM interactions are declared open interfaces, not yet authenticated composition. Evidence: results/memory-address-integration.json. Actual seed migration session32321 remains active in GKR/PCS generation; no restart or result claim.

### Complete fold/source arithmetic certificate replay

Root reviewed and integrated recursive_fold_trace.py and recursive_source_batch_trace.py with source-manifest hash validation, then independently reran full fixed-header certificate verification and26 mutation tests. All256 fold rows/768 independent residuals plus3440 source lane pairs/32 linked outputs covered; no residual sum. Merkle and transcript/beta/terminal evaluation still native; caller-fixed PCS headers still require authenticated original GKR derivation. Root replay did not recapture original wrappers. Evidence: results/recursive-arithmetic-integration.json. Disclosed certificate is not recursive compression. Configured same-component seed prover remains CPU-active (session32321, no restart).

### Actual configured-profile component regenerated

Seed migration session32321 completed exit0: same sha384-direct source rows, exact statement/spec/roots preserved by root regression. Independent core verifier and wrapper17 mutation tests PASS. Expanded proof365463B; GKR/PCS316.67s. Core configured verifier18839 SHA384 compression blocks plus11373 config setup; wrapper canonical AIR digest check additional. Old same-component expanded core profiling still running session23088, no speedup ratio claimed yet. Artifacts results/sha384-direct-seed/. No recursive aggregation/security claim.

Root audit PASS3398 for ChosenGKRSourceRecovery2/RateFourRepresentativeThreshold4;228 boundary calculations independently rerun. At N=4D, near requires T>=ceil(5D/2), far T>=3D. Existing conditional D131072/T393217 passes; runtime acceptance-to-agreement remains open. Evidence results/chosen-recovery-integration.json.

Same-component expanded core profiling completed: old93909 compression blocks, new30212 including config setup (67.83% fewer). Both exclude wrapper AIR digest check. Evidence: results/sha384-direct-seed/comparison.json. Counts are not measured runtime/circuit savings.

### Full literal memory table to natural bounds

Root audit PASS3401 for Bounds2/Source1 and generated full literal table. Exact exported Lean/Python parity PASS741 source constraints+2 automatic multiplicity checks+both EXEC/MEM interactions; bounds subset4 expressions equal. Actual TableLocal satisfaction derives selected legal width and natural address+offset+width<=decodedPages*65536. Actual state page identity and result semantics/service attachment remain pending. Evidence results/memory-bounds-integration.json.

Second actual seed migration running session31649, four table zerochecks complete, GKR/PCS still active; progress results/sha384-committed-seed/progress.json. New committed wrapper preserves trusted receipt and adds canonical SHA384 public checks, not yet runtime validated.

Threshold scope correction: prior rate-four T=3D satisfies near/tensor far conditions only. Agent found existing checked fold regime requires strict2N+D<3T, hence T>=3D+1. Current accounting393217 fits; fullheight example786432 does NOT fit fold regime and requires786433. Formal separate threshold bridge pending; no security claim follows from either arithmetic report.

### Complete residual vector ideal counting bound

Root added RecursiveResidualConjunction2, auditPASS3403. For fixed full list zero-padded to cube: all-zero evaluation completeness and nonzero-lane zero-count bound via existing packed-grid theorem. At800 outputs padded1024, conditional ideal loss10/|sample|. No executable compiler equivalence, commitment/GKR, FS/QROM or quantum-security claim. Evidence results/recursive-residual-integration.json.

Reviewed agent conjunction implementation: binds complete trace before output point, all800 outputs, no host residual checks in verifier. Agent reports6 negatives including recommitted wrong odd witness passing binding but rejected by GKR; root independent replay pending frozen handoff. Full3.70MB disclosure remains, so182763B GKR alone is not sub300KB recursion. Second seed component session31649 still running, no restart.

### Actual signed-load bit conversion

Root implemented PreparedMemorySignExtension1 and full auditPASS3404. Generic bit-sum/padding helpers plus exact legal-width Int wrapping derive ofBits sign replication equals actual Num.extendS for8/16/32-bit inputs into32/64-bit targets. Handed frozen helper to instruction agent for composing actual result equations. Evidence results/memory-sign-extension-integration.json. Second configured component session31649 confirmed CPU-active7min, no restart. Conjunction replay manifest received; root independent replay remains next.

### Both configured components and conjunction root replay

Second seed migration and independent verifier completed; wrapper18negativesPASS, exact statement preserved. Four-table core125704→33867 SHA384blocks including setup (73.06% reduction). Pair219613→64079 including setup (70.82%); configured core alone38969. Three shared roots and context shapes/publicvalues preserved. Excludes outer wrapper AIR digest from both comparisons; not timing or recursive-size evidence. Artifacts results/sha384-committed-seed and results/seed-component-pair.json.

Root independently replayed all6 conjunction negatives plus5 derived-header negatives, full original-GKR-header→conjunction acceptance PASS. Host residual evaluators disabled on successful verification; recommitted false witness passes binding but old proof rejected. Evidence results/recursive-conjunction-integration.json. Full disclosure/native inner checks remain.

Root auditPASS3416:12 reviewed exact result-bit/word lemmas cover all12integer loads and7stores. Service/EXEC composition pending. Evidence results/memory-values-integration.json.

### Concrete weighted PCS replay extraction interface

Root review/auditPASS3426 for WeightedPCSReplay8/RateFourFoldThreshold2. Exact endpoint/terminal tests derive scale/equality-weight chain and FoldTranscriptChecks; candidate-or-small-passing-set-or-indexed-extraction-event theorem has no supplied close candidate. Root reran26 Python/Lean parity cases:7honest,16rejects,3 zero-scale terminal mutations accepted by residual-only checks as expected. No division by equality scale; terminal authentication and query checks remain necessary.178threshold boundary checksPASS; combined rate-four minimum3D+1, fullheight786433 (786432fails fold). Conditional Q8 query term6561/65536 is not a security certificate or measured attack probability. Evidence results/weighted-replay-integration.json. Query/extraction counting composition assigned next; root extraction/adaptive FS/QROM remain open.

### Actual load/store execution from decoded service acceptance

Root auditPASS3430 for LoadService2/StoreBridge2. Literal AIR plus exact singleton decoded memory request acceptance implies actual interpreter post-stack/PC and descriptor equality, or finite supported read/batch collision. No assumed raw/result equality; prior word/sign proofs compose. Operand selection/CODE/gas/clock provenance remains explicit; input state is arbitrary state with decoded operands pushed. Evidence results/memory-exec-service-integration.json. Root actual configured-pair hash capture live session23343; first component verified, second in progress. Full-state node accounting pending; no duplicate savings claimed.

Configured-pair capture23343 completed; full512bit state/block analyzerPASS.15594 distinct full hash inputs,17042 occurrences,64079 compression calls,59604 blocks across unique inputs,56354 unique full-state nodes, only95shared acrosscomponents.20028block-byte reencounters had different states and cannot merge. Matches prior64079core+setup total exactly. Evidence results/seed-pair-hash-nodes/report.json, hashed binary/map/capture artifacts retained under/tmp. No circuit routing proof/dedup soundness inferred; comparison to old compact-wrapper211947unique nodes is different verification entry path and not a fair measured node-reduction ratio.

### Ideal replay bound and actual memory fixture replay

Root auditPASS3432 for WeightedPCSReplayBound2. Accepted replay+queries without fixed-source candidate is counted under explicit source/terminal/geometry/causality/ideal sampling conditions. Root arithmetic confirms E=N-4, currentExt4 isolated extraction104integerbits (fullheight103); Q8 conditional query term dominates. This sufficient bound does not certify128, not an attack claim. Evidence results/weighted-replay-bound-integration.json.

Root independently reran76 actualexec vsAIR cases (19ops×4addresses), strengthened checker to entire15fieldMEM and23fieldEXEC tuples. Corrected earlier agent description25fields to actual23. Mixed stack prefix, PC, sign/tag, crosspage/offset and independentlyflattened storebytes pass. Evidence results/memory-air-fixture-integration.json. Not prepare/gas/fullrunCall or globalbus authentication.

### Root replay of configured outer GKR plus packed PCS

Root reviewed/copied hash-frozen configured engine/PCS mapping and independently replayed12negatives and196608coefficient comparisons. Core accepts with operand-packing and host residual evaluation disabled; full native linked wrapper also passes. No omitted high private-zero bit. Proof338021B plus caller-verifieddependency500508B=838529B actual core inputs. Native linked wrapper with separate trace+trustedheaders+proof totals6145238B (expanded file sum, not lowerbound or minimum encoding); original header derivation dependencies additional. Evidence results/recursive-pcs-integration.json and results/recursive-pcs-root/input-accounting.json. SingleRSroot fixed-operand residual profile assigned next to remove cross-root disclosure, not native inner verification.


### Prefix-strategy causality and executable memory sender integration

Root independently reviewed and integrated `WeightedPCSPrefixStrategy.lean` (six theorems). Full `check.py` passes 3,438 public theorem audits. Prefix-indexed current oracles and quadratics derive fixed initial source and snapshot causality, including historical query mass. Child oracle may depend on the just-drawn challenge. This is an ideal interactive fixed-oracle model; adversarial commitment extraction and Fiat–Shamir/QROM correspondence remain open. Evidence: `results/weighted-prefix-integration.json`.

Root reproduced actual prepared execution fixture and memory sender tests: 795 columns, 2,243 constraints, four actual adjacent memory instructions after a real constant prologue; exact 23-field EXEC attachment; 20 locally valid adapter substitutions and 24 source/transition mutations rejected. Fixture checks actual runCall final memory, stack and gas. Separate memory-only segment profile; CODE authentication, gas provenance, public boundaries and last-row successor remain open. Regression evidence does not establish formal sender refinement. Evidence: `results/memory-sender-integration.json`.

Neither increment establishes full NEAR coverage, complete recursive verification, PQ128 security or a complete sub-300,000-byte proof.


### Recursive operand coordinate algebra

Root added `RecursiveOperandCoordinates.lean`: reconstruction in actual flat [1,v,v²,v³] order, arbitrary weighted lane contribution equality, and finite weighted functional equality. Full audit PASS 3,441 public theorems. This establishes the coordinate algebra used in GKR-to-PCS mapping; executable row/group indexing, complete PCS binding and full recursive composition remain separate. Evidence: `results/operand-coordinates-integration.json`.


### Independently replayed single-commitment recursive arithmetic

Root reviewed source manifest and dependency hashes, copied four new profile files, and independently replayed the public verifier and all 13 negative cases. Honest proof succeeds with old disclosed-trace, cross-root reconstruction, and host residual evaluators disabled. Fresh committed attack satisfies all original 800 residuals but violates fixed operand equalities; new aggregate is nonzero and old proof fails under fresh root. Exact fixed slot coverage is derived, with only 512 e/o witness slots free. Outer proof 342,047 bytes, no extra transmitted dependency. Actual current API file inputs total 4,358,562 bytes including original expanded proofs and trusted statements. Native inner transcript/GKR/hash/Merkle processing remains outside recursion. Evidence: `results/recursive-single-root-integration.json`.

Root also reran exact rational parameter search and executable Rabin checks: `results/pq128-parameter-routes.json`. Ext5 with 309 queries meets only isolated replay 128-bit bound; no full security certification.


### Formal memory sender source binding

Root reviewed and integrated 13 sender lemmas; full audit PASS 3,454 public theorems. Literal table implies nonempty stack/op onehots, store depth, exact selected address/value message limbs, i32 address type, matching store operand type, and canonical zero high i32 bits. Root regenerated literal export and independently checked exact 2,243+2 constraint AST and both message interactions against Python. Global bus pairing, sender/adapter natural-value composition, transition and boundary authentication remain open. Evidence: `results/memory-sender-formal-integration.json`.


### Certified Ext8 arithmetic integration

Root inspected existing Fp8 field/tower/cardinality certificates, integrated five replay/root-order lemmas, and passed full audit (3,459 public theorems). Root strengthened actual Lean arithmetic fixtures with all 64 ordered basis pairs. Independent Python comparison PASS 104 cases/728 operations, 62 FFT-vs-naive evaluations, 15 quadratic/fold identities and five malformed encodings. Exact kernel arithmetic bounds isolated replay by 2^-130 for E=1,048,572 and 314 queries; no full protocol/QROM certification follows. New separately versioned PCS migration remains in progress. Evidence: `results/ext8-parameters-integration.json`.


### Lossless recursive path dictionary experiment

Measured current Q8/Ext4 single-root proof: 1,360 path hash occurrences, 985 unique digests. A binary digest dictionary plus canonical JSON skeleton reconstructs byte-identical original canonical proof and reduces 342,047 bytes to 260,024 bytes. Three framing corruption cases reject. Raw digest deduplication accounts for 18,000 bytes; remaining savings mostly remove hex encoding. This is an experimental container, not a verifier-accepted profile or cryptographic compression claim. Full current API inputs would still total 4,276,539 bytes. No high-query Ext8, full recursion or PQ128 size claim. Evidence: `results/recursive-path-sharing/report.json`.


### Exact recursive packed functional and Ext8 PCS replay

Root reviewed/integrated eight packing lemmas; full audit PASS 3,467 theorems. The final identity includes the 12 low row bits, two group bits, four coordinate lanes and every extra zero-padding bit. Valid at zero/one challenges, without inverses or supplied map equality. Evidence `results/operand-packing-integration.json`.

Root reviewed the separately versioned Ext8 scalar PCS and independently reran prove/verify, fresh-process verification and all 26 negatives at D32 with314queries. Measured complete JSON envelope1,527,170bytes; hash count18,568calls/37,140blocks. The source commitment is specific to the full config (including point/claim), not a reusable prechallenge source cache. This is a scalar coefficient-MLE opening only; packed/joint integration, adversarial-root extraction, QROM and total upstream error composition remain open. Evidence `results/ext8-pcs-root/report.json`.


### Realistic high-query multiproof geometry

Root implemented independent minimal sibling-frontier counting with exact small-tree checks and eight deterministic uniform-query simulations per source size. At314queries, scalar Ext8 payload components (paired leaves,48bytehashes,quadratics/roots/terminal; excludes config/framing/upstream) span123,656–127,160bytes forD1024,871,752–894,976 forD131072, and1,037,448–1,065,648 forD262144. D32 nearly saturates its tiny trees (~5.2KB) and must not support realistic size claims. These are geometry simulations, not measured proofs or universal lower bounds. Results agree in scale with the separately reported small-source codec. The current rate-four,314query scalar pipeline remains over300KB at realistic degrees even with shared paths. Evidence `results/ext8-multiproof-geometry.json`; protocol-level authentication/query reduction remains necessary.


### Independently verified Ext8 shared-opening codec

Root reviewed canonical multiproof extraction/expansion and new binary framing, matched PCS/arithmetic dependencies, and independently reproduced exact-roundtrip/fresh-process checks and all36negativecases. D32:5,200binarybytes(5,517withcanonicalexternalconfig); D1024:127,256binarybytes(127,733withconfig). All314 sampled checks retained, including repeated indices; terminal tree regenerated from authenticated constant disclosure. Root is included and checked against mandatory external root. Full proof reconstruction and original verifier remain mandatory. Source context remains scoped to point/claim/config and cannot yet serve the source-before-GKR-point integration. Tiny-source results do not imply sub300KB at realistic degrees. Evidence `results/ext8-codec-integration.json`.


### Matched sender/adapter execution and rate tradeoff

Root reviewed and integrated13matched-message lemmas; full auditPASS3,480theorems. Exact23field equality yields sameopcode, selectednaturaladdress/storevalue, clock/offset/result, then actualload/storeexec with finitecollision alternative. Four canonical16bitlimbs avoid64bitfieldalias. Localmessagepairing is explicit; arbitrarylowerstack, CODE/gas/pages/instance/globalbus and boundary obligations remain. Evidence `results/memory-attached-integration.json`.

Root evaluated larger domains under existing conditional replay inequality, T=floor((2N+D)/3)+1 and E=N-B. Blowups4,8,16,32,64,128 need314,262,241,232,227,225queries respectively at isolated130bitbudget/Ext8. Independent frontier simulations atD131072/262144 show longer Merkle paths offset query savings: rate4 remains smallest among tested choices. Alternate rates are hypothetical, not implemented or fullsecuritycertified. Evidence `results/ext8-rate-tradeoff.json`.


### Fixed-slot soundness and reusable-source Ext8 integration

Root reviewed/integrated11fixedconjunctionlemmas; fullauditPASS3,491theorems. Canonical coverage fixes all live inputs except512e/o slots; all-zero residual semantics separate from randomizedaggregate escape. Runtime256rows/32sourcepairs/12,144inputs match formalshape. Same-vector wrongfixedoperand escapes at at most14*|S|^13 ofS^14points. Source-DAG execution and cryptographic/FSbinding remain open. Evidence `results/fixed-conjunction-integration.json`.

Root reviewed V2diff: namespace/domain/layout determine reusable sourcecontext, with point/claim/querybudget/statement bound separately into fullopeningtranscript+mandatoryexpectedroot. Independent root replay passed two distinctnonbasepoints perD32/D1024 sharingexactroot, independentlycomputedclaims, fourfreshprocessverifications and46negatives. D1024 binaries124,480/124,488bytes; pluscanonicalexternalconfig124,985/124,993bytes. This removes sourcecontextdependence on openingpoint; stillscalarPCS, notpacked/GKR/fullNEAR orPQ128certified. Evidence `results/ext8-reusable-root/report.json`.


### Ext8 zero-equality-weight adversarial regression

Root added `test_ext8_zero_weight.py` against reusable V2PCS+codec. Scriptedfoldchallenge0 withpoint1, andchallenge1 withpoint0, forceexactzero equalityweight. Honestprove/verify+codecexactroundtrippass. Adversarialterminal+1 is freshlycommitted, transcript/queries regenerated, completeconstantterminalroot authenticates and everyMerklepath independentlychecks. Zero terminalresidual also passes, but full verifier rejects specifically at foldconsistency. This validates reliance on queriedfoldrelations rather than division by a potentiallyzero weight. Sampling is deliberately scripted test coverage, not a hashuniformity/FS/QROM claim. Evidence `results/ext8-zero-weight.json`.


### Explicit quantum resource accounting

Root independently retrieved authorpaper viaNSF(566,838bytePDF), checked Corollary4 onprintedpp31–32 (ePrint revision numbering differs), and reran exactresourceledger. ClassicalFRI/BCSbound isQ*epsilonRBR+3(Q²+1)/2^kappa; quantumcorollary givesTheta(Q*epsilonFS) withqueryoverhead. SymbolicconstantC mustbeinstantiated and protocolhypotheses proved before applying toourverifier. NominalC=1, adversaryQ=2^64 andtargetadvantage2^-128 allocate258bits toeachinteractivefield/queryterm; currentExt8extractioncannotmeetthatbudget. This doesnotdemonstrate anattack or ruleout128bitworkfactor: resourcebound+advantagetarget differfromconstant-successworkfactor. Rootcorrected fieldbudgetlabel toquarterbudget. Evidence `results/qrom-resource-ledger.json`, withPDFhash/source. NoPQ128certification.


### Concrete source batching program integration

Root reviewed/integrated9sourceprogramlemmas; fullauditPASS3,500publictheorems. Structural node/edge routes plus acyclicexecution imply concrete leftassociated beta-times-leaf accumulation, optional projection and target subtraction;16queries yield32residuals with1792globaloffset. Independent checker rebuiltall24,369nodes,112branches/3440lanes/10352slots and compared192outputs over6vectors;13malformedlayoutsreject. Root regenerated dependency fromoriginalproofs/trustedstatements and matched capturedbytes exactly(SHA2561673834045f5fd9d8592840dc7f7c9d7028d556193bc1fb0aa5c479be2ab39ea). Capturedinstance certificates remain executable ratherthan kernel proofs; native header/hash authentication, PCSbinding/QROM andfullNEAR remainopen. Evidence `results/source-program-integration.json`.


### Ext8 coordinate packing algebra

Root implemented fourlemmas foractualcertifiedFp8: reconstructionfromeightbasecoordinates, weightedcontributions, columnMLElinearity andgeneric row/group/padding functional. UnlikeExt4instance, finaltheorem supportsarbitrary rowbits/groupbits/highpaddingbits. No inverse or nonzerochallengepremise. FullauditPASS3,504publictheorems. This prepares largerfieldrecursivepacking; executablepackedPCS/GKRmigration andcryptographiccomposition remainopen. Evidence `results/ext8-packing-integration.json`.


### Refreshed main alignment

Fetchedorigin/main f025caf629bd1caa5a919a442545c07de2f55cb2; researchbase9116a4da95f2d17cfddecc1618ccc0daaa9ba37d. Onlychangedpathisdocs/HANDOVER.md; nosource/specdrift. Rechecked requestedA7B/phase2logs andD3requirements. `make pin-check`PASS. UpstreamD0a live rejection iswitnessvalidationconformance ontrueclaim (applied_receipts_hash), notcertificateunsoundness; require completewitnessvalidation in eventualcandidate. SignedcurrentR5 andlongtermrecursion permission remain distinct. Neither upstreamD1link gaps norresearchPQ/fullNEAR gaps are closedbycomponentaudits. Evidence `results/main-alignment-refresh.json`.


### Rate-shift prerequisite integration

Root independently validated degree32/domain128 to degree8/domain64 diagnostic: all64 new-domain evaluations,32 prior coset folds,10 adversarial cases and fresh-process verification passed. Three fixed-candidate mixing lemmas integrated; full audit PASS3507. Four queries only; candidate extraction, rate-shift soundness and QROM composition remain open. Evidence `results/rate-shift-integration.json` and `results/ext8-rate-shift-root`.


### Complete stack input and exact shared lane emitter

Root reviewed and integrated15 lemmas; full audit PASS3522. Actual source constraints determine complete mixed input arrays and canonical numeric slots, with exact load/store consumed operands and preserved prefixes. Exact shared seven-node lane builder proves execution equals the concrete accumulator for arbitrary operands. Whole next-row transitions and complete shared query compiler remain pending. Evidence `results/stack-shared-integration.json`.


### Rate-shift vector identity and prechallenge candidate lists

Root implemented six weight-accumulator lemmas, reviewed/integrated five candidate-list lemmas, and completed full audit PASS3533. Monomial coordinates equal x^i; shape-preserving zip updates and sequential powers realize exactly the scalar functional used by the mixing bound, including gamma0. Candidate-list union bound permits an accepting candidate to vary with gamma inside a prechallenge family. A normalized unique-decoding list is empty or singleton without an existence premise; D8/N64 permits radius28 and yields at most5 bad mixing challenges for one OOD plus four sampled constraints. The scalable continuation still must imply a close constrained candidate; fixed-oracle binding, prior-domain rate-shift transfer and QROM errors are separate open obligations. Evidence `results/rate-shift-list-weights-integration.json` and `results/rate-shift-candidate-list.json`.


### Coupled security and size feasibility screen

Root coupled the existing binary PCS frontier model to conditional security-resource budgets and replayed32 baseline size cases exactly. Five profiles,14 powers-of-two dimensions and8 seeds were evaluated. At degree131072 the existing314-query Ext8 model costs871752–894976 bytes before GKR/composition. The nominal C=1 constant-success query-workfactor scenario (Q=2^128, advantage<=1/2) allocates each interactive constituent1/8 and hash1/4; arithmetic choices are degree10,625queries,49-byte digest, giving1550730–1566211 estimated bytes. Exact independent Fraction checks validate allocations and minimal integer choices. Larger field/hash widths and reduction applicability are NOT implemented or certified. This does not imply an attack or a universal lower bound. Screening decision: stop treating binary-fold serialization optimization as the primary route to300000 bytes at these dimensions; prioritize rate-shift extraction/transfer feasibility. Degree-to-Petagas mapping, native recursive verification closure and full NEAR remain open. Evidence `results/compression-feasibility.json`; reproduce with `python3 airbender/direct-wasm/assess_compression_feasibility.py` (includes independent Fraction validation).


### General weights remove a continuation mismatch

Root identified that accumulated rate-shift functionals generally lack the single tensor factor required by the old weighted extraction interface. Added and audited seven lemmas: exact zip-fold functional, general bilinear quadratic and endpoint identity, shared-curve extraction, adaptive unique-regime extraction and explicit bad-challenge count. Full audit PASS3540. Existing weighted triple-intersection/RS reconstruction proof supplies the same strict separation and error max(domain.length,2), now for arbitrary even/odd weight vectors. Runtime checked40 quadratics and120 folded evaluations including0/1. Equality weights[2,-4,-3,6] plus monomial injection at3 become[3,-1,6,33], with determinant105, explicitly disproving general tensor factorization. Full continuation induction, rate-shift prior-domain transfer and cryptographic binding/QROM remain open. Evidence `results/general-weighted-extraction-integration.json` and `results/general-weighted-runtime.json`.


### General-weight continuation chain

Root integrated eight lemmas with full audit PASS3548. Exact arbitrary even/odd functional interleaving and root-power domain transport extend the extraction bound to the indexed verifier relation. Child candidate implies fold success; extracted pair constructs a concrete degree-bounded parent preserving weighted agreement and endpoint claim. Composing these gives the deterministic all-round bound: outside extraction-bad transitions, absence of an initial candidate implies fewer thanT passing global query seeds. This removes the equality-tensor restriction through the deterministic chain. The general-weight adaptive history union bound, actual root binding and rate-shift domain/OOD transfer remain open. Evidence `results/general-chain-integration.json`.


### Adaptive general-weight continuation bound

Root integrated five lemmas, full audit PASS3553. General transcript snapshots now include arbitrary even/odd weights; actual transcript cap/mass bounds supply each stage error max(childDomain,2). Adaptive challenge and independent query composition proves the accepted-pair count, including malformed/aborting branches rejected by prefix/terminal checks. For nonempty domains the normalized ideal bound is E/|sample|+((T-1)/N0)^q. Prefix causality and no-initial-candidate reduction remain explicit premises, not verifier checks. D8/N64 continuation requires T46 (at most18 mismatches), which lies inside the previously proved radius28 unique list. Three halving stages give E56. Actual prefix instantiation, candidate normalization/list composition, root binding, rate-shift domain/OOD transfer and QROM remain open. Evidence `results/general-adaptive-integration.json`.


### Continuation candidate to prechallenge list

Root integrated five lemmas, full audit PASS3558. Explicit D-coefficient normalization pads short candidates, preserving coefficients/evaluations under the degree bound; existing canonicalPolynomial only truncates and was insufficient for list uniqueness. Actual indexed initial candidate mass implies plain root-domain agreement under explicit received-oracle binding. Its accumulated functional is preserved and converted to the mixing functional, yielding membership in the fixed prechallenge unique list when N<=T+radius and2radius+D<=N. D8/N64/T46/radius28 satisfies both. This closes the candidate interface, not candidate existence outside its probabilistic bound. Joint continuation/mixing experiment, executable causality, rate-shift transfer, root binding andQROM remain open. Evidence `results/continuation-list-integration.json`.


### Joint mixing and continuation experiment

Root proved the combined accepted-event count allowing the entire continuation strategy to depend on gamma while keeping the received oracle/candidate list fixed before gamma. Full audit PASS3559. For nonempty sample spaces the bound normalizes to m/|mixSample|+E/|foldSample|+((T-1)/N)^q. The actual indexed candidate bridge discharges continuation initial-candidate absence outside mixing bad events, conditional on the explicit noCorrect semantic premise. That premise must follow from prior-domain/OOD/source-query transfer outside its own bad event; it has not been proved. Exact Fraction check61/P^8+(45/64)^256<=2^-130 passes for the isolated D8/N64 example; this omits transfer, binding, QROM and upstream errors. Four source queries differ from256 continuation queries; no executable profile or size certification added. Evidence `results/joint-continuation-integration.json`.


### Source-query transfer into noCorrect

Root integrated three lemmas, full audit PASS3562. Complement of wrong-constraint predicate gives every old-functional/OOD/query equation. For any family fixed before source queries, candidates satisfying old claim but fewer thanT seed agreements pass allq independent queries in at most family.length*(T-1)^q tuples. Applying the fixed unique list bounds failure of the previous joint theorem noCorrect premise; OOD is retained but ignored in this upper bound. Need still derive insufficient agreement from prior-domain candidate absence across skipped folds. Conditional arithmetic forN128/D32 gives strict threshold97; with weight4 per32cosets insufficient agreement means at most24, yielding(3/4)^q. Four queries give81/256, not a security profile or measured attack; isolated130bit tail needs314queries. Evidence `results/rate-query-transfer-integration.json`.


### Skipped folds via exact virtual oracles

Root integrated four lemmas; full audit PASS3566. Virtual oracles are recursively determined by source and drawn affine challenges, with consistency true by construction. Candidate absence propagates across any number of folds outside extraction-bad events without intermediate commitments or terminal disclosure. Uniform seed weight becomes exactly2^stage; candidate absence therefore yields the unweighted agreement bound required by source-query transfer. N128/D32/T97 atstage2 gives weight4 and fewer than25 matching cosets. Production inverse-DFT quartet transform matched two sequential pair decodes in640 comparisons over arbitrary source words, all32cosets and0/1/full-extension challenges. Authentication mocked explicitly; parity is executable evidence, not kernel Python refinement. Need instantiate the full virtual prefix strategy/adaptive budget, then combine source queries with mixing and continuation; root binding andQROM remain open. Evidence `results/virtual-fold-integration.json` and `results/virtual-rate-shift-runtime.json`.


### Derived virtual prefix causality and adaptive budget

Root integrated five lemmas, full audit PASS3571. VirtualPrefixTranscript computes arbitrary weights and exact source folds from prior challenge coordinates; sent quadratic reads only history.take stage. Source, weights and complete snapshot causality are proved, including the query measure. Direct adaptive bad-path budget needs no separate causality/extraction premise and permits arbitrary prefix-dependent quadratic messages. Counted good paths imply the actual completed transcript is outside all corresponding local bad transitions. N128 with two skipped folds has extraction numerator64+32=96. Full shape/endpoint-check integration, continuation prefix instantiation and outer query/mixing composition remain before an ideal complete rate-shift statement; source binding andQROM are separate. Evidence `results/virtual-prefix-integration.json`.


### Checked virtual strategy discharges transfer premises

Root integrated four lemmas, full audit PASS3575. Initial weights length equal degree0 and the halving degree schedule derive every subsequent weight length, equal even/odd lengths and exact interleaving. Literal Boolean endpoint checks supply parent claim equations; next functional and claim updates are definitional. Original candidate absence and counted good virtual path now imply folded candidate absence using the actual strategy rather than assumed layout/claim relations. Direct checked_no_close theorem exposes the agreement bound for any folded-degree candidate satisfying its current functional. Full query/mixing/continuation experiment composition and executable continuation remain, along with root binding/QROM/fullNEAR. Evidence `results/checked-virtual-transfer-integration.json`.


### Checked source-stage composition

Root integrated three lemmas, full audit PASS3578. Unique-list membership gives an actual normalized degree bound. Checked virtual-fold transfer now discharges source-query noClose for every list member satisfying the current functional. Joint prior-challenge/source-query experiment counts rejected endpoint paths correctly and allows the next oracle/domain/OOD data to depend on the prior challenge prefix, but not future queries. Normalized bound is E_virtual/|F|+((minimum-1)/Nfolded)^q, with original source no-candidate as the semantic reduction premise. No caller-supplied noClose or prefix causality remains. This bounds failure of noCorrect on the selected prequery list; combine with list completeness and the mixing/continuation theorem for whole rate-shift acceptance. Commitment/QROM/fullNEAR remain open. Evidence `results/checked-source-stage-integration.json`.

## Research checkpoint and publication cadence

User requested committing and pushing as work progresses. This checkpoint preserves
the research sources, Lean audit harness, proof fixtures, and validation reports.
Regenerable `results/**/*-cache/` prover caches and repository-wide build caches
are excluded; retained proof artifacts are research evidence, not a full NEAR
proof or a 128-bit post-quantum security certification. Latest completed full
`python3 check.py` audit passed 3,578 theorem/boundary checks. Future checkpoints
should follow verified milestones and be pushed to `research/direct-wasm-whir`.

## Checked full ideal rate-shift composition

`CheckedRateShiftComposition.lean` joins the checked source-stage and mixing/
continuation theorems into an acceptance-count bound. Next oracle and OOD data
precede source queries; the continuation can adapt to the prior transcript,
source queries and mixing challenge. NoCorrect is derived, folded weight shape
is derived, and rejected prefix endpoint checks remain in the event.

For nonempty sample spaces the bound has five terms: virtual extraction, source
sampling, mixing, continuation extraction, and final sampling. The exact count
theorem avoids division and remains valid for empty sample spaces. Full audit
passes 3,579 theorem/boundary checks with the allowed axiom closure.

`check_rate_shift_budget.py` independently normalizes the finite count bound
and checks exact rational arithmetic for D32/N128 -> D8/N64. Source queries 314
and continuation queries 256 jointly meet the ideal interactive 2^-128 bound;
with those respective other counts fixed, minima are 310 and 253. These are
not simultaneously optimized counts. Four diagnostic source queries do not
certify that bound. These results are conditional ideal protocol calculations,
not a quantum security claim or a measured succinct proof. The executable
diagnostic still discloses terminal coefficients rather than implementing this
continuation. Next work should connect a scalable executable continuation and
price its complete authenticated data, then address the commitment/QROM bridge.

## Executable arbitrary-weight rate-shift continuation

Added a separate versioned reference `pq384_ext8_rate_shift_continuation.py`.
It authenticates the rate-4 scalar source, performs two virtual folds, commits
a paired-leaf rate-8 next oracle before OOD/source queries, accumulates the
actual arbitrary weight vector, and proves its continuation down to one
coefficient. Each continuation checks quadratic endpoints, folds both weights
and coefficients, authenticates queried transitions, and reconstructs the
complete constant terminal oracle. Initial root, statement and both query
budgets are transcript-bound. The prior diagnostic remains unchanged.

`test_rate_shift_continuation.py` passed four fresh-process verification cases
and 15 negative checks covering endpoint equations, authentication, field
shapes/counts, terminal value and external context substitution. Exact rational
checks instantiate the joint ideal bound for each degree (no inherited small
degree query assumption). D32/s314/c256 and D1024/s314/c264 are below 2^-128
under the theorem's assumptions; low-query diagnostics are not.

Complete uncompressed JSON envelope sizes, including configuration and root:
D32/s314/c256 = 1,162,716 bytes; D1024/s314/c264 = 3,855,695 bytes. These sizes
include repeated Merkle paths and all source and continuation openings; no
original witness is required by the verifier. They cover only this PCS task,
not the recursive GKR/NEAR statement. Python-to-Lean refinement, commitments
and quantum Fiat-Shamir remain open. Next: a canonical multiproof codec with
unchanged sampled queries, then realistic degree/cost measurements.

## Lossless rate-shift multiproof codec and matched baseline

Added `pq384_ext8_rate_shift_codec.py` with version `NRS8MP01`. Decoder counts
and indices come exclusively from the supplied configuration and transcript.
Source quartet leaves share one canonical multiproof; each nonterminal
continuation oracle has one multiproof; terminal openings are reconstructed
from the constant oracle. No sampled checks are dropped. Prefix/continuation
metadata replay is shared with the reference verifier, whose previous four
fresh-process cases and 15 rejection checks still pass after refactoring.

Codec validation: exact equality with all four original expanded proofs,
canonical re-encoding, four fresh-process verifications without expanded
proof input, and 31 malformed/context substitution rejections. D1024/s314/c264
uses 126,680 proof bytes, 127,192 bytes including canonical external config,
or 127,475 bytes including the actual external JSON file. D32/s314/c256 uses
4,888 proof bytes / 5,240 bytes with canonical external config.

A matched-source comparison is less encouraging than the JSON reduction:
on the same D1024 root, point, claim, statement and source query count, the
existing no-rate-shift codec is 124,344 proof bytes; this rate-shift proof is
2,336 bytes larger. At D32 it saves 312 bytes (5,200 -> 4,888). These are
single-fixture measurements, not statistical superiority results. The new
codec establishes a complete authenticated PCS transport but does not yet
show rate-shift savings at useful scale. It does not include recursive GKR
or a full NEAR state transition and does not establish QROM security.

Next substantive design decision: measure multiple skipped-fold/rate schedules
and larger degrees under explicit joint budgets, rather than assuming this
single two-fold rate shift will meet the full end-to-end target.

## Calibrated single-shift schedule screening

`screen_rate_shift_schedules.py` evaluates 30 schedules at each of degrees
1,024, 8,192, 131,072 and 1,048,576, four simulated seeds each. Skipped folds
are {1,2,3,4,6,8}; new encoding rates are {2,4,8,16,32}. Query budgets use
exact rational arithmetic from the joint ideal acceptance bound, with both
sampling tails at most 2^-130 and the full sum at most 2^-128. The geometry
exactly matches all four actual codec fixture sizes before extrapolation.

Best schedules in this grid:
- D1,024: skip8/rate2, 17,992 bytes (opens all original source leaves).
- D8,192: skip8/rate2, 182,776–227,832 bytes.
- D131,072: skip2/rate4, 842,184–849,080 bytes versus baseline 871,760–883,928.
- D1,048,576: skip2/rate4, 1,388,584–1,400,008 bytes versus baseline
  1,417,384–1,434,632.

None of the tested single-shift schedules reaches 300,000 bytes at the two
larger degrees, even before external config, GKR, recursion or NEAR data.
These are calibrated geometry simulations, not measured larger proofs or
protocol lower bounds. Only skip2/rate8 through D1,024 is implemented. Raw
scalar coefficient disclosure itself costs just 4D bytes plus context, with
linear-size verifier reconstruction; small-degree byte wins must not be
mistaken for succinct scaling. The screen reports source leaf saturation.

Decision: further single-shift variants are not the primary implementation
priority for the full target. Screen repeated rate shifts under an explicitly
identified composition obligation, and compare stronger extraction/query
bounds, before choosing the next protocol implementation. No quantum
Fiat-Shamir reduction or new post-quantum certification is inferred.

## Repeated-rate-shift feasibility screen

`screen_repeated_rate_shifts.py` searches repeated shifts over rates 2/4/8/16/32
and 1–8 skipped folds with exact expected Merkle frontier/leaf costs. The
expectation formula is independently checked by exhaustive query enumeration
in 12 small cases, including duplicate draws; 654 additional coset-replication
checks validate the structured opening geometry. All intermediate sources
are correctly priced as paired Ext8 leaves (64 bytes), not scalar leaves.

Two terminal policies are compared: arbitrary coefficient disclosure and
disclosure capped at degree64. The latter avoids selecting a large witness
dump as the apparently best succinct-verifier protocol. With the cap:
- D131,072: selected repeated schedule estimates 743,000–754,776 bytes over
  eight seeds, versus 842,184–849,080 for the prior single-shift screen.
- D1,048,576: 1,259,752–1,273,320 bytes.
Neither reaches 300,000 bytes before configuration, GKR or NEAR costs.

With unrestricted disclosure, D131,072 instead selects sending all scalar
coefficients (524,344 bytes including version/root); D1,048,576 selects a
repeated schedule ending at 4,096 disclosed coefficients (~1.20MB). Such
choices require source-size verifier reconstruction. They are explicit
baselines, not claims of succinct verification.

The repeated composition is NOT proved or implemented: the current Lean
theorem ends in a plain fold continuation. Its extension needs an inductive
no-candidate invariant through each rate shift and adaptive transcript. The
script checks only the conditional additive arithmetic budget (134 bits per
tail, <=20 stages); it does not silently treat this as a formal theorem.
No commitment/QROM security or impossibility claim follows from this grid.

Decision: repeated scheduling gives modest savings but is not enough with
current query bounds. Prioritize reviewing stronger extraction/proximity
bounds and their provable assumptions before implementing another large
variant. This is evidence to change the research direction, not completion.

## Stronger agreement route and checked constraint reduction

Pinned the November2025 primary paper at
https://www.math.toronto.edu/swastik/rs-proximity-gaps-2025.pdf
(SHA256 in `results/johnson-curve-bridge-review.json`); inspected Corollary4.4
and Theorem4.6, including the rendered error formula. The latter offers a
stronger analytic starting point than our current three-candidate extraction.
The Basefold PDF remains HTTP403. A September2026 prime-field capacity
preprint was identified but is not audited or adopted for our Ext8 setting.

Our new `GeneralListCurveExtraction.lean` isolates the protocol-specific
constraint step without treating the analytic theorem as an axiom. Given a
fixed prechallenge complete family of jointly agreeing curves and an explicit
exceptional-set transfer, success without a valid parent outcome is bounded
by `exceptional_count + 2*family.length`. This follows from two roots per
nonzero residual quadratic. A second checked lemma derives coefficient
identity from agreement on at least D distinct points, matching the required
support-preserving interface. Full audit: 3,581 theorem/boundary checks PASS.

This is a conditional reduction, not a proved Johnson-regime extractor. The
MCA transfer and complete finite family/cardinality still need proof. The
next formal target is the finite Johnson list bound and support-preserving
transfer; then list/OOD/mixing penalties must replace the unique-list ledger.
No runtime query profile or claimed security level changes in this checkpoint.

## Checked finite Johnson list-size bound

Added `FiniteRSJohnsonList.lean`: three public theorems prove a conservative
Johnson-regime finite-family bound. With N distinct evaluation points, degree
below D, agreement at least T, and L coefficient-distinct candidates,
`L*T*T <= N*N + L*N*(D-1)`. When the gap is nonnegative this yields
`L*(T*T-N*(D-1)) <= N*N`. A strictly positive gap gives a numerical list cap.
The proof derives the incidence second-moment inequality over natural numbers
and combines it with the existing polynomial-root bound; no decoder or MCA
axiom is introduced. Full audit: 3,584 checks PASS.

Independent finite-code check enumerated all 3,125 received words for the
25 affine polynomials over F5, including a duplicate-candidate counterexample
to demonstrate why coefficient distinctness is necessary. At rate1/4 and
agreement9/16 the large-domain bound gives L<=15, hence at most225 pairs
and at most450 quadratic constraint roots across those pairs. An isolated
list-union sampling term needs162 queries for2^-130 at those parameters.
These components are NOT a replacement total security budget.

Remaining analytic/composition work: construct the complete normalized
prechallenge lists and prove support-preserving correlated agreement (the
main unproved transfer). Only then connect the list penalties throughout
rate shifts and the full transcript/QROM ledger. Runtime profiles unchanged.

## Complete candidate lists and slice-first gate

`FiniteRSJohnsonCandidates.lean` constructs a coefficient-distinct normalized
list, proves soundness/completeness and applies the Johnson gap bound to it.
The list depends only on the alphabet, fixed domain/received oracle and degree/
agreement thresholds. It has no challenge argument. Completeness assumes a
finite alphabet covering the field; its exponential enumeration is a
mathematical construction, not a proposed prover algorithm. Full audit3,588
checks PASS. Support-preserving MCA remains the major unproved transfer.

User asked whether we are on track to prove a slice with soundness feasibility
first. Candid assessment: executable PCS and semantic components exist, but
no integrated Wasm slice yet meets soundness and size requirements together.
Theorem growth alone has not passed that gate. Recorded explicit requirements
in `results/slice-feasibility-gate.json`: accepted proof implies actual bounded
Wasm execution; same data is committed across semantics/AIR/GKR/PCS; complete
quantified quantum soundness ledger; total byte measurement and scaling;
coherent cross-layer adversarial validation. All unclosed requirements are
marked incomplete, not assumed.

Prioritize this integrated feasibility gate after the current candidate-list
checkpoint, before further instruction families. A first bounded no-host
slice is a milestone toward the unchanged full NEAR1Pgas goal, not a narrowed
definition of completion.

### Slice-first feasibility review: literal semantics correction

Reviewed the newer PreparedLiteralEntry and PreparedExecBoundary sources. The gate previously cited the older supplied-certificate path: actual callEntry is now derived from literal HoldsP plus executable CODE/entry checks, actual function lookup and fuel. Cryptographic acceptance to that HoldsP premise remains the central integration/soundness obligation. Gate remains NOT_PASSED.

Recorded existing 193-instruction diagnostic: 121982 proof bytes, 19564 compact public bytes, 223788 statement JSON bytes. Proof plus current statement JSON is 345770 bytes; compact proof/public subtotal 141546 excludes other configuration inputs. Q8/Ext4 is not certified 128-bit PQ. Existing fixture reports were inspected, not rerun. Validated JSON, evidence paths and arithmetic; no code or theorem changes.

### Literal slice verifier frontend: actual preparation and fixed AIR

Added PreparedSliceCheck.lean and verify_prepared_slice.py. The caller supplies intended Wasm bytes/method/prepaid gas; the frontend reconstructs literal AIR and invokes the actual preparedLiteralRunCallCheck against the same public vector before binary verification. Preparation runs, function execution does not. Source roots remain prover commitments checked by the transcript. The existing prepared_literal_public_run_call theorem already binds literal HoldsP to actual runCall and published status, gas and stack; the cryptographic acceptance-to-HoldsP reduction is still open.

Validation: test_prepared_slice.py passes a fresh verifier process on the retained 193-instruction proof, and 14 cross-layer rejection tests (valid alternate Wasm, method, gas, CODE, AIR, output, root and framing). Retained request and report make the test reproducible without /tmp fixtures. All transported inputs: 121982 proof + 223788 statement JSON + 919 request JSON = 346689 bytes. Q8/Ext4 diagnostic only; no new secure proof or full NEAR claim. No new theorem declarations; the Lean executable was compiled/run through lake during these checks.

### Joint bus soundness component and actual slice budget

Added BusJointChallengeBound.lean: combines existing generic fingerprint and grand-product theorems into one joint alpha/gamma bad-pair count. Fixed unequal expanded message multisets are essential; support width controls alpha collisions, expanded natural multiplicities control gamma collisions. Generic field and distinct finite samples; no Fiat-Shamir or commitment-extraction assumption is hidden. Full check.py audit passed 3589 theorems (/tmp/root-slice-bus-joint-audit.log).

check_slice_bus_budget.py reads the retained literal statement and computes conservative budgets from actual rows, interaction widths/multiplicity bits and public records: 1475 support records, padded width28, alpha41300, gamma8589934531, total numerator8589975831. Ideal uniform Ext4 yields90.63 bits for this component; Ext8 yields214.26. These are sufficient upper-error budgets, not attacks or maximal achievable security. Source extraction, concrete tagged-padding/auxiliary adapters, local/PCS errors, sampler distribution and QROM remain open. Do not treat this component bound as end-to-end soundness.

### Variable-length bus-tag adapter

Added BusTaggedChallengeBound.lean with three audited theorems over an arbitrary field: nonzero trailing-tag padding injectivity; the exact fp(message ++ [tag]) = fp(message) + alpha^length * tag encoding; and the joint challenge bound directly for variable-width unpadded message lists. This removes fixed-width padding from the component bound contract while retaining explicit fixed-message, nonzero-tag and unequal-multiset premises. Natural busCount-to-expanded-message correspondence and committed-source extraction are still open for the executable frontend.

Full check.py audit passed3592 theorems (/tmp/root-slice-tagged-audit.log). check_slice_bus_encoding.py passed1560 checks across195 retained public records, widths25/27, four challenges including0/1, and both Ext4/Ext8 implementations. Tests cover the public encoding, not source-trace extraction or whole-protocol soundness. No security or proof-size improvement claimed in this checkpoint.

### Exact natural bus counts for arbitrary public field vectors

Added BusTraceMultiset.lean with expanded per-row/table natural traffic plus public messages, an exact count theorem, and balance iff permutation. All three new public theorems audited; check.py passed3595 (/tmp/root-slice-trace-multiset-audit.log). This works directly with Trace F and List F public inputs. The existing Udr transcript pubOf maps individual claim bytes to field elements and cannot be silently used to represent this slice’s large field-valued public limbs.

The exact count-to-multiset step is now closed independently of transcript decoding. Still required: injective bounded-tag/base-field embedding into extension messages, common committed source extraction, actual auxiliary/global-product correspondence, and complete local/PCS/QROM soundness. No executable security profile, size, or full NEAR coverage change.

### Natural trace imbalance to concrete Ext8 fingerprint bound

Added BusTraceChallengeBound.lean: injective payload embedding and bounded tags preserve raw bus/message identities; a locally injective mapping preserves unequal multisets; the concrete natural imbalance theorem composes with the tagged joint bound. Certified Fp8.ofBase and natural bus+1 tags satisfy the premises for bus<P-1, and bus_trace_fp8_joint_bound discharges those encoding assumptions. This field is the certified BabyBear x^8-11 extension.

Full check.py audit passed3599 public theorems (/tmp/root-slice-trace-challenge-audit.log). Fixed source trace/public vector, support coverage and shape, and distinct challenge samples remain explicit. Formal actual-slice support/mass budgets, source extraction, actual auxiliary/global products, local/PCS soundness and QROM are still required. No change to the executable Ext4 profile or proof size.

### Constructed bus support and exact support-size formula

Added BusTraceSupport.lean: support contains one message per row/interaction plus all public records; proved coverage of both multiplicity-expanded sides, exact support length, and descriptor/public shape propagation. bus_trace_supported_fp8_bound composes this construction into the actual-trace Ext8 bound, removing supplied coverage and candidate-size premises. Full check.py audit passed3603 (/tmp/root-bus-support-audit.log).

Remaining numerical discharge is concrete literal descriptor/public widths and expanded natural multiplicity mass. Authenticated common trace, auxiliary/global product semantics and the rest of protocol/QROM soundness remain open. No executable profile or proof-size change.

### Descriptor-derived natural multiplicity budget

Added BusTraceMass.lean: proved multNat≤2^bitcount-1, per-side expanded length bounds from actual row heights/descriptors, and bus_trace_budget_fp8_bound with constructed support and bounded expanded lengths. Full check.py audit passed3606 (/tmp/root-bus-mass-audit.log). PreparedSliceBusBudget.lean evaluates the actual literal AIR; integrated Python comparison matches support1475, send mass1024, receive mass8589934531 and total numerator8589975831. Budget does not use trace cell values or honest multiplicities.

Remaining: concrete literal tag/width proof, common authenticated source trace, actual auxiliary/global products and complete protocol/QROM soundness. No executable security or proof-size change.

### Literal bus bound reaches actual runCall output semantics

Added PreparedLiteralBusBound.lean: literal source descriptors and public records prove tag/width limits for arbitrary public vectors; specialized the constructed-support/mass Ext8 bound. Added PreparedLiteralBusSoundness.lean: wrong actual runCall/public output, executable eligibility and fuel, local table validity, and public fit imply the bus joint error bound. Exact bus balance would construct HoldsP and contradict the existing actual-runCall/public-output theorem. Full check.py audit passed3610 (/tmp/root-literal-bus-soundness-audit.log), standard axioms only.

The theorem explicitly assumes one fixed locally valid trace. Cryptographic source extraction, local/PCS checks to TableLocal, auxiliary/global products to natural products, and transcript/commitment/QROM reductions remain required. This is a semantic bus-error component, not end-to-end soundness. No proof size or executable parameter change.

### Initial local-constraint batching error

Added AirResidualBatchSoundness.lean: exact compiler power-accumulator/Horner identity and joint ideal power-batching plus row-MLE zero count for a fixed nonzero residual matrix. The normalized bound is (L-1+rowLog)/fieldSize. Full audit passed3612 (/tmp/root-local-initial-audit.log). check_slice_local_budget.py evaluates the actual constraint/auxiliary residual lists on deliberately invalid literal rows: EXEC738 residuals gives numerator745; CODE553 gives560. These counts include automatic multiplicity and auxiliary constraints.

This closes the initial random-batching count component, not cryptographic local soundness. Concrete all-row residual/equality-weight adapter, adaptive sumcheck, terminal PCS authentication, common source/auxiliary extraction and QROM remain open. No executable parameter or proof-size change.

### Equality-weighted initial sumcheck target

Added AirEqualityWeightedTarget.lean: equality-weighted Boolean sums reproduce row MLEs, Boolean-only evaluator correspondence suffices, and the initial mixing/row-MLE count transfers to the actual evaluator’s weighted sum under that explicit correspondence. No false claim that nonlinear constraints commute with interpolation. Full audit passed3616 (/tmp/root-weighted-target-audit.log). check_slice_weighted_target.py passed18 checks on both literal tables with synthetic invalid8-row traces, cyclic next rows, source/auxiliary residuals, and zero/one/nontrivial extension challenges.

The concrete evaluator’s Boolean-row correspondence remains an explicit formal premise; runtime parity does not discharge it. Adaptive sumcheck, authenticated terminal/source bindings and complete QROM/security remain open. No proof size or executable security parameter change.

### Source AIR Boolean-row correspondence

Added AirBooleanRowEnvironment.lean. The formal input environment interpolates current columns, cyclically permuted next columns, and first/last/transition row flags, while fixing public inputs. Every Expr.evalWith agrees with actual Expr.eval on Boolean rows. Ordered source batching, equality-weighted target and initial zero count now compose without a supplied source Boolean-correspondence premise. Full check.py audit passed3620 (/tmp/root-air-boolean-audit.log).

Scope is source expressions in the formal MLE environment, not yet the entire executable weighted evaluator: auxiliary residuals, concrete selector-product/base-extension adapters, adaptive sumcheck, authenticated source/PCS inputs and QROM remain. No executable security parameters or proof size changed.

### Concrete selector products and base-to-Ext8 source semantics

Added AirSelectorProducts.lean: first=product(1-x), last=product(x), transition=1-last equal row-flag MLEs at all points, including dimension0/off-cube. Added AirExtensionLift.lean: certified Fp8.ofBase preserves actual Expr.eval for the lifted trace/public vector, and product-selector Boolean evaluation agrees with original BabyBear semantics. Full check.py audit passed3627 (/tmp/root-air-selector-lift-audit.log), standard axioms only.

Auxiliary bus residual correspondence, combined target, adaptive sumcheck, authenticated inputs and complete QROM remain open. The Python verifier still runs its diagnostic Ext4 profile; no secure parameter or size claim changes.

### Combined source and auxiliary Boolean-row target

Added AirCombinedResidualRows.lean: BusProgramFormula (extension literals/current/next/selectors/arithmetic) agrees between product-selector MLE and direct row environments on Boolean rows. Combined residual list preserves source then auxiliary order; composed its weighted initial zero bound. Exposed the reusable Boolean-row MLE value lemma previously private. Full audit passed3631 (/tmp/root-combined-residual-audit.log).

This covers the formal formula model. Concrete auxiliary layout-to-formula-list certification and coordinate reconstruction remain required, as do adaptive sumcheck, terminal/source/PCS authentication and QROM. No executable security or size change.

### Common source/auxiliary coordinate trace

Added AirAuxCoordinateTrace.lean: reconstruct one Ext8 semantic trace from source columns followed by eight base coordinates per auxiliary value. Current/cyclic-next interpolation commutes with reconstruction; coordinate input environment equals the formula environment at all points. Source expressions with colBound within sourceWidth preserve original BabyBear Expr.eval. Full audit passed3635 (/tmp/root-aux-coordinate-audit.log).

This establishes algebraic common-trace correspondence, not PCS authentication. Concrete auxiliary layout/formula-list certification, adaptive sumcheck, accepted-opening extraction and QROM remain. The current executable slice uses Ext4; formal Ext8 progress does not change its security parameters or size.

### Auxiliary chain layout checkpoint

Derived ordered auxiliary square/product formulas and contiguous column allocation in Lean; zero residuals imply chain equations. Full audit passes (3638 registered results, allowed axioms only). Exported Lean formulas match the executable evaluator in nine cases / 150 residual comparisons, including the 24-link CODE chain. This closes the chain layout adapter only: full interaction/fingerprint/boundary layout, accepted-proof extraction, and complete quantum soundness remain open. Slice feasibility gate stays NOT_PASSED.

### Per-interaction layout to final product

Added deterministic per-interaction chain/factor construction and boundary residuals. Lean proves the generated factor equals busBitFactor from vanishing chain residuals, derives the exact chain length, and composes all-row generated residuals into the final running product. Environment selector and next-row bindings remain explicit; empty multiplicities, nonboolean arithmetic factors, and zero fingerprints require no division. Boolean multiplicity validity remains a separate source constraint.

Validation: full check.py passed with 3642 registered results and allowed axioms only. Lean-exported formulas match the executable Ext4 auxiliary evaluator in 48 cases / 744 residual comparisons, covering 0/1/2/25 bits, first/last/arbitrary extension selectors, distinct next accumulator values, nonboolean bits, and a zero fingerprint. This is parity evidence, not formal Python/parser refinement or executable Ext8 certification.

Next: table-wide chain offsets and send/receive boundary order, then source-expression/fingerprint lowering. Common committed-trace extraction, complete adaptive/PCS/transcript soundness, 128-bit quantum security, secure sub300k sizing and full 1 Pgas scope remain open. Slice feasibility gate stays NOT_PASSED.

### Table-wide auxiliary layout and product composition

Constructed source-order chain allocation and stable send-then-receive boundary ordering, with accumulator columns starting after all chains. Lean proves source-list preservation, total chain length, grouping permutation, consecutive accumulator/final pairs, and inclusion of every bound interaction's residuals in the table residual list. These compose into final-product correctness for every bound interaction, conditional on zero table residuals and explicit selector/next-row environment bindings. Finals are indexed by a total function; parser/list-length agreement remains an implementation boundary.

Validation: full check.py passed with 3648 registered results and allowed axioms only. Exported Lean table formulas match the executable Ext4 evaluator in 72 cases / 2280 residual comparisons over six profiles, including empty tables/multiplicities, mixed directions, long chains, arbitrary extension selectors and distinct next values. Synthetic powers use alpha=0: this validates table layout/order, not general fingerprint/source-expression lowering or actual slice specialization.

Next: general source-expression and fingerprint lowering, then instantiate the table construction for the actual slice. Committed-trace extraction and complete adaptive/PCS/transcript/quantum soundness remain open; neither secure sub300k nor full 1 Pgas execution is established. Slice gate remains NOT_PASSED.

### Source AST and tagged fingerprint to table product

Added total source Expr lowering to auxiliary formulas, preserving arbitrary environment evaluation and actual cyclic trace-row semantics. Tagged Horner formulas evaluate to fp of the source message with the trailing bus+1 tag, matching the bus challenge-bound encoding. Generated table products now have an existential source-interaction witness derived from allocation/grouping membership; their factors are expressed in source message/multiplicity semantics rather than supplied abstract powers.

Validation: full check.py passed (3654 registered results; allowed axioms only). Lean lowered actual preparedLiteralAir(193) EXEC/CODE descriptors and exported the complete auxiliary residual lists. Python comparisons passed in 54 cases / 1701 residual comparisons, covering all 9 EXEC and 54 CODE residuals, alpha=0/1/7, arbitrary Ext4 current/next/auxiliary values and selectors. This finite comparison does not prove Python/parser refinement, sample arbitrary extension challenges, or certify executable Ext8.

Next: connect source bit constraints to natural multiplicity expansion, then compose all interaction finals with global send/receive/public products. Committed-trace extraction, adaptive local/PCS soundness and quantum transcript reductions remain open. Slice gate remains NOT_PASSED; no secure sub300k or full 1 Pgas claim.

### Natural multiplicity factor composition

Connected auxiliary arithmetic factors to Interaction.multNat, preserving natural exponents rather than reducing counts modulo the field. Lean derives bit Booleanity from the actual Table.allConstraints list and proves each generated factor equals both the corresponding fingerprint power and a product over exactly that many replicated tagged messages. The all-row table theorem derives each bound final's product with natural multiplicities and discharges selector/cyclic-next bindings from the actual trace row environment.

Validation: full check.py passed (3660 registered results; allowed axioms only). This is a formal composition change; no executable/proof-size changes or new runtime benchmark are claimed. Explicit premises remain that all source and generated auxiliary residuals vanish on the same trace and that the binding belongs to the constructed table layout.

Next: compose direction-specific finals and public factors into the exact busTraceMessages product. Accepted-proof-to-residual extraction, full adaptive/PCS/transcript quantum soundness, secure sub300k total sizing and full 1 Pgas scope remain open. Slice gate remains NOT_PASSED.

### Expanded traffic to global side products

Proved exact row, table and all-table product identities for naturally expanded bus traffic, allowing an arbitrary payload embedding and tag function. Row-major traffic is transposed into per-interaction row products without dividing by any factor. Public traffic then gives exactly the source-plus-public message product and trailing-tag encoding already used by the joint challenge bound. The existing concrete Ext8 budget now bounds equality of these semantic global side products.

Validation: full check.py passed (3665 registered results; allowed axioms only). This is a formal algebraic/bound transfer; no runtime, proof-size, or security-parameter improvement is claimed. The bound still requires a fixed trace/public vector, bounded shapes, natural imbalance and distinct ideal challenge samples.

Next: fold the constructed bound-final list into the direction-specific semantic products. Per-binding natural-product correctness is already proved, but the aggregate list fold is not claimed here. Common committed-trace extraction and full adaptive/PCS/transcript quantum soundness remain open, as do secure sub300k sizing and full 1 Pgas scope. Slice gate stays NOT_PASSED.

### Bound-final list fold to the global bus product

Proved that the constructed binding list retains every source interaction with multiplicity through allocation and stable direction grouping. Direction-selected bound finals equal semantic formula products; with source/auxiliary residual validity, they equal natural-multiplicity source products. Recursive all-table composition and public factors give the exact expanded global bus-message product. No separate certificate equating aggregate claimed finals to semantic products is assumed.

Validation: full check.py passed (3669 registered results; allowed axioms only). This is a formal composition checkpoint without runtime or proof-size changes. Its explicit boundary is same-field source/auxiliary/public arithmetic; the global public theorem requires PubVal K. It does not silently instantiate an unproved Ext8 public adapter.

Next: concrete BabyBear source/public and natural-multiplicity transport into the reconstructed Ext8 trace, then accepted-proof-to-common-trace/residual extraction. Complete adaptive/PCS/transcript quantum soundness, secure sub300k sizing and full 1 Pgas scope remain open. Slice gate stays NOT_PASSED.

### Concrete BabyBear source to reconstructed Ext8 bus products

Proved exact source-message embedding and natural multiplicity preservation under source-column bounds for airAuxCoordinateTrace. Natural counts are preserved even for nonboolean source values. Original BabyBear source residual validity lifts to Ext8, and generated auxiliary residual validity then identifies constructed table finals with products of the original BabyBear message traffic. All-table composition and public factors (formed directly from the original base public vector) equal the semantic Ext8 side product already used by the ideal challenge bound. No PubVal Ext8 instance or unproved public adapter is introduced.

Validation: full check.py passed (3675 registered results; allowed axioms only). Formal transport only: the executable remains Ext4 and no size/performance/security certification is claimed. Explicit premises are column bounds, source/auxiliary residual validity and a supplied common coordinate trace.

Next: allow challenge-dependent auxiliary coordinates/finals while holding source columns fixed; then connect accepted local/PCS checks to the common trace/residual premises. Complete quantum transcript soundness, secure sub300k sizing and full 1 Pgas scope remain open. Slice gate stays NOT_PASSED.

### Adaptive auxiliary acceptance and literal wrong-output bus bound

Added a source-preserving auxiliary attachment: heights and source columns are fixed, while arbitrary remaining coordinate cells and indexed finals may be chosen after each alpha/gamma pair. Proved bounded source evaluations/messages/natural multiplicities remain unchanged, and generated residual validity plus claimed side-product equality implies the fixed-source bus equation. Existential auxiliary/final choices are inside the challenge event, so the ideal Ext8 budget applies to adaptive witnesses, not just fixed honest auxiliaries.

Composed this event with the literal slice's wrong actual runCall output theorem. Source TableLocal, public fit, executable preparation eligibility and sufficient fuel remain explicit. No cryptographic extraction, Fiat-Shamir or quantum compiler theorem is inferred from this composition.

Validation: full check.py passed (3681 registered results; allowed axioms only). No executable, proof-size or security-parameter changes. Next: derive the common fixed source and source/auxiliary residual premises from accepted local/PCS proofs with correct transcript timing. Adaptive sumcheck/PCS extraction, quantified quantum reduction, executable Ext8 migration, secure sub300k sizing and full 1 Pgas scope remain open. Slice gate stays NOT_PASSED.

### Degree-generic adaptive local sumcheck

Inspected verify_table_reduction: source/auxiliary zerocheck rounds enforce table_degree+2 coefficients, endpoint sums, and an exact claim update before a terminal weighted-evaluator equality. Existing adaptive weighted theorem was quadratic PCS-specific. Added the degree-generic adaptive checked-message bound, false-claim persistence, and specialization to the actual Boolean suffix-sum truth function. Endpoint consistency is derived by splitting the Boolean cube. Integer counting theorem covers zero rounds/empty samples and needs no degree premises on malformed/aborting branches.

Validation: full check.py passed (3687 registered results; allowed axioms only). Inspected retained actual degrees: EXEC table_degree6/round_degree7 with8 rounds; CODE4/5 with8 rounds. Conditional sumcheck numerators56/40 follow, but actual combined source/auxiliary honest-polynomial degree and representation remain uninstantiated. Terminal equality is still an authenticated-honest-value premise, not a proved PCS conclusion.

Next: construct those combined evaluator round polynomials and discharge degree/representation, then compose terminal current/next/PCS authentication. Initial batching, adaptive bus and quantum transcript components still require full composition. No secure sub300k, 128-bit quantum or full 1 Pgas completion claim. Slice gate stays NOT_PASSED.

### Combined source/auxiliary polynomial lowering and honest round degree

Added auxiliary formula degree and polynomial lowering, with evaluation/degree preservation for arbitrary extension constants and current/next/selectors. Source-then-auxiliary power batching and affine equality-weighted suffix summation now have combined evaluation/degree theorems. The adaptive sumcheck theorem consumes the derived honest degree, leaving concrete affine slice construction and suffix-sum representation explicit.

Validation: full check.py passed (3694 registered results; allowed axioms only). Computed actual preparedLiteralAir(193) source and generated auxiliary AST degrees for alpha0/1/7, compared with the executable verifier caps: EXEC729 source residuals degree6 plus9 auxiliary degree4 yields weighted round degree7; CODE499 source degree3 plus54 auxiliary degree4 yields round degree5. Both match coefficient limits8/6 and conditional eight-round numerators56/40. These are component bounds, not protocol security claims.

Next: construct affine coordinate slices from the common trace MLE and equality kernel and prove suffix-sum representation; then terminal current/next/PCS authentication. Quantum reduction, executable Ext8 migration, secure sub300k sizing and full 1 Pgas scope remain open. Slice gate stays NOT_PASSED.

### Concrete trace-coordinate honest sumcheck rounds

Constructed affine coordinate polynomials from the actual trace MLE at coordinate endpoints, allowing arbitrary nonboolean history/suffix values. Proved they evaluate to current and cyclic-next MLEs, constant public inputs and actual product selectors; constructed the affine equality-kernel coordinate polynomial as well. Boolean suffix enumeration now builds honest combined source/auxiliary round polynomials and proves exact remaining-sum representation. The concrete adaptive sumcheck bound therefore no longer takes detached affine environment, honest-degree or representation certificates.

Validation: full check.py passed (3706 registered results; allowed axioms only). No executable changes or performance claims. Remaining theorem premises: fixed trace/formula lists/mixing/equality point, AST degree bounds, false initial weighted sum, and terminal equality to the actual trace evaluator under distinct ideal challenge samples.

Next: compose initial residual-batching/row-MLE error with adaptive rounds, then prove terminal current/next/PCS authentication and common-trace extraction. Full quantum transcript reduction, executable Ext8 migration, secure sub300k sizing and full 1 Pgas scope remain open. Slice gate stays NOT_PASSED.

### Composed local invalid-trace bound

Composed initial residual power batching/equality-point error with adaptive concrete-trace sumcheck in one integer challenge-count theorem. Strategies can depend on initial mixing/tau and all prior round challenges. A fixed invalid combined trace with zero initial claim and terminal equality to its actual weighted evaluator has conditional ideal acceptance probability at most (residualCount-1+rowLog+roundDegree*rowLog)/fieldSize. The exact count includes every initial and round challenge; no division is used in Lean.

Validation: full check.py passed (3707 registered results; allowed axioms only). Reproducible retained-fixture budget report gives EXEC738 residuals:745 initial+56 adaptive=801; CODE553:560+40=600. These are local component numerators only. No new runtime proof, executable Ext8, secure-size or quantum-security claim.

Next: terminal current/next/PCS authentication and common-trace extraction, then global bus/multi-table/transcript composition. Fixed combined trace before local challenges and honest terminal equality remain explicit premises. Full 1 Pgas scope, quantified quantum soundness and secure sub300k total-input sizing remain open. Slice gate stays NOT_PASSED.

### Ordinary shift kernel and quadratic reduction polynomial

Inspected pq384_shift start_claim/kernel/verify. Current and next values share a power-batching challenge after the vector is committed; next claims use the alpha^width offset. Existing borrow proofs covered DP/bit indexing, while the optimized dual-weight theorem concerned upper-zeta weights. Added the ordinary borrow-DP-to-cyclic-predecessor-row-MLE identity needed here, valid at arbitrary field points. Constructed an affine polynomial for the actual current equality plus shifted kernel, then a quadratic polynomial for its product with batched current-column MLEs, with exact evaluation.

Validation: full check.py passed (3714 registered results; allowed axioms only). Formal algebraic progress only; no executable, proof-size or security-level change. Dimension equalities and the common source trace remain explicit. Next: initial Boolean-sum/current-next-claim identity, vector batching plus adaptive shift count, and authenticated final original-column PCS openings. End-to-end quantum soundness, secure sub300k sizing and full 1 Pgas scope remain open. Slice gate stays NOT_PASSED.

### Initial cyclic-next reduction claim and vector batching

Connected the ordinary shift kernel's Boolean sum to actual cyclic-next MLEs using the existing natural-index predecessor reindexing theorem. Proved row-MLE Boolean dot products, column-batching/interpolation commutation and the exact current-then-next concatenation identity with alpha^width offset. The actual initial shift sum is now the honest batched claim vector, and a fixed incorrect vector matches it for at most2*width-1 distinct column-batching challenges.

Validation: full check.py passed (3721 registered results; allowed axioms only). Formal composition only, with no runtime/proof-size/security-parameter change. The claim vector must be fixed before the batching challenge and have exactly twice the source-column width. Next: compose adaptive quadratic shift rounds, authenticate final original-column PCS openings, and combine with local AIR/global bus bounds. Quantum transcript soundness, secure sub300k sizing and full 1 Pgas scope remain open. Slice gate stays NOT_PASSED.

### Full algebraic adaptive shift reduction bound

Constructed honest quadratic shift rounds from actual trace slices and Boolean suffix enumeration, proving degree and exact remaining-sum representation. Composed adaptive rounds with fixed-vector batching: an incorrect current/next vector accepted with honest terminal source evaluations has ideal error at most (2*width-1+2*rowLog)/fieldSize. Strategies may depend on alpha and prior challenges. Promoted existing Boolean-suffix/count-composition lemmas to audited reusable interfaces rather than duplicating them.

Validation: full check.py passed (3729 registered results; allowed axioms only). Reproducible retained-fixture budget: Ext4 coordinate widths617/398 give numerators1249/811; projected Ext8 widths629/598 give1273/1211. Ext8 figures are arithmetic projections, not an executable migration or security certification.

Next: authenticate final original-column MLEs through PCS and establish common-source extraction/transcript timing, then compose local AIR/global bus/shift bounds. Terminal equality remains explicit. Full quantum transcript soundness, secure sub300k sizing and full 1 Pgas scope remain open. Slice gate stays NOT_PASSED.


### Computed packed source binding

Proved `mobius_tensor_row_mle`, `packed_computed_tensor`, and
`packed_computed_opening_bad_count`. The mutable source transform now discharges
the algebraic sourceBinding premise of packed vector authentication, including
zero padding, at arbitrary field points. The wrong-lane count remains conditional
on `PackedPCSExact`; this is not a cryptographic extraction theorem. The next
critical task is replacing that contract with a quantified authentication bound
on one committed trace. The slice gate remains NOT_PASSED.

Validation: full `check.py` passed with 3732 registered results and the existing
axiom allowlist. No new size or security measurement is claimed.


### Fallible PCS packing composition

`PackedOpeningFailureBudget.lean` decomposes wrong-vector acceptance into a
packing collision or an accepted scalar value inconsistent with the computed
source tensor. Its joint-experiment count is at most p*Q^(p-1)*R plus the
PCS failure count, allowing opening strategies to adapt to packing coordinates.
No independence between failures or exact PCS contract is assumed. The PCS
failure term is not yet bounded. Inspection of `checked_interactive_unique_fold_soundness`
confirms its initial premise is no candidate; this cannot directly establish
fixed-source incorrect-opening soundness without candidate coherence and common
committed-source extraction. This checkpoint establishes the interface for that
reduction, not the reduction itself. Slice gate remains NOT_PASSED.

Validation: full `check.py` passed, 3734 registered results; existing axiom
allowlist enforced. No new performance, size, or quantum-security claim.


### Fixed representative folding and unique-basin cost

`WeightedPCSRepresentativeSoundness.lean` derives no initial candidate from a
wrong equality functional of a fixed degree-bounded representative within R
mismatches of the source oracle, provided R+(N-T)+D<=N. This composes with the
prefix-prover adaptive count bound. Common representative existence, terminal
authentication, and cryptographic/quantum transcript reductions remain open.

Exact integer screening of A/Q+((T-1)/N)^q at N=4D, minimal admissible
T=3D+1, and projected BabyBear^8 requires 309 queries for 128 ideal bits and
463 for 192 at D=1024,131072,1048576. The fold term alone prevents this bound
from certifying 256 ideal bits. These are costs of the sufficient theorem, not
security upper bounds or attacks. The Q8 diagnostic cannot inherit these targets.
No byte-cost estimate is made here. The query cost motivates prioritizing a
stronger list-decoding/proximity reduction before a secure size claim.

Validation: full `check.py` passed with 3736 registered results and enforced
axiom allowlist. Independent Python Fraction arithmetic confirmed that each
reported query count meets its target and one fewer does not.


### Weighted Johnson list bound

Proved weighted finite agreement counting by replication and specialized it to
RS polynomial families and joint even/odd polynomial pairs. For total surviving
mass M, point cap B, strict degree D, agreement T and family length L, the bound
is L*(T*T-M*B*(D-1))<=M*M when the gap is nonnegative. A positive gap is required
to constrain L. Joint pairs need no product-of-two-list penalty. These bounds
apply to fixed finite coefficientwise distinct families, not extracted candidates.

This discharges the weighted list-size ingredient for a suitable family in
`GeneralListCurveExtraction`; constructing that family with complete correlated
transfer remains open. No improved parameters, bytes, or quantum security claimed.

Validation: full `check.py` passed with 3740 registered results and the existing
axiom allowlist. The slice feasibility gate remains NOT_PASSED.


### Constructed weighted curve candidate family

`WeightedCurveCandidates.lean` constructs the prechallenge family by enumerating
normalized degree-bounded polynomials and filtering Cartesian pairs by joint
weighted agreement with the two source words. Proved soundness, completeness
when the finite alphabet covers the field, coefficientwise distinction, and the
weighted Johnson gap bound for the constructed family. Normalization retains
coefficients of every degree-bounded candidate through the existing normalization
theorems. This is a mathematical witness, not a practical decoder.

The remaining correlated-agreement theorem must map successful postchallenge
folded candidates into this family outside a quantitatively bounded exceptional
set. Completeness here covers already jointly agreeing pairs and does not assume
or imply that transfer. No security/size parameter improvement is claimed.

Validation: full `check.py` passed with 3744 registered results and enforced
axiom allowlist. Slice feasibility gate remains NOT_PASSED.


### Concentration target correction

Rechecked the author-uploaded Basefold revision (Section4 Propositions1/2 and
Section4.2 Theorem4): https://www.researchgate.net/publication/387601318_Basefold_in_the_List_Decoding_Regime
The route concentrates selected candidates on one affine polynomial curve, using
Guruswami-Sudan interpolation/factorization. Universal candidate transfer is a
stronger optional interface, not a prerequisite to follow this route.

`GeneralCurveConcentrationReduction.lean` proves that more than max(|domain|,2)
constrained successes on one curve yield joint weighted agreement and the
quadratic formal identity. It then derives the bad-count bound conditional on
quantitative concentration. This avoids requiring a universal list transfer.
Concentration is still an explicit unproved premise, not a new axiom. The
mathematical work remaining is substantial; list enumeration/counting does not
substitute for rational-function interpolation/factorization or another valid
concentration proof. No protocol parameters or size claims changed.

Validation: full `check.py` passed with 3746 registered results and enforced
axiom allowlist. Feasibility gate remains NOT_PASSED.


### Small-field concentration validation

Added exact finite enumeration of all normalized source pairs, every degree<2
polynomial and all challenges over F5,F7,F11,F17. Two profiles: uniform weights
with T=3 and weights[1,1,1,2] with T=4, on four points. Total202376 normalized
source pairs. Maximum false-success challenge counts are respectively4 and3
in each field. Arbitrary-word normalization by subtracting separate affine
interpolants preserves agreement supports; that reduction is explanatory math,
not a newly proved Lean generalization.

`SmallFieldCurveCounterexample.lean` independently checks the explicit F5
example e=[0,0,0,1],o=[0,0,1,2]: successful challenges[0,1,2,4], no jointly
agreeing pair at T=3, positive Johnson gap5. It exhausts all25 canonical
affine polynomials and all625 pairs via kernel `decide`. This is a counterexample
to zero-exception transfer from the gap alone, not a cryptographic attack and
not a contradiction of a concentration theorem with a nonzero error allowance.
The zero functional/zero sent polynomial satisfies the quadratic constraint.
The regression prevents mistaking list cardinality for candidate coherence.

Validation: full `check.py` passed with3747 registered results and enforced axiom
allowlist. All eight finite enumerations completed. Feasibility gate remains open.


### Constructive support interpolation

`CurveSupportInterpolation.lean` derives coefficientwise and evaluation equality
between each degree<D candidate and the affine combination of source Lagrange
interpolants on D fixed distinct agreement points. The candidate may depend on
the challenge; the points and source words are fixed. This feeds the checked
single-curve result to bound supported constrained successes by max(N,2) under
no compatible parent. There is no supplied concentration or transfer hypothesis.

This is a local proof component, not global list-decoding soundness. A union over
all supports can be exponential, so support control or polynomial-cost algebraic
concentration is still necessary. Neither the security parameters nor the
measured proof size changes at this checkpoint.

Validation: full `check.py` passed with 3749 registered results and enforced
axiom allowlist. Slice feasibility gate remains NOT_PASSED.


### Slice query-count geometry

Added `report_slice_query_geometry.py`. It freshly verifies the retained binary
with the shared verifier, exactly re-encodes its JSON proof, derives each table
reduction and PCS transcript, and reconciles all Q8 branch sizes with the actual
codec. It then counts longer query prefixes without generating proof openings.
The process-local query-count override is restored after each calculation; no
production protocol or domain identifier changes.

Q8 reproduces121982 proof bytes and346689 current transported bytes. At128,239,
309 queries the retained Ext4 layout projects492238,705390,817054 proof bytes.
At309 total current transport is1041761 bytes, with462016 leaf bytes and299520
shared-path bytes. Four branch costs are306870 EXEC-source,48566 EXEC-auxiliary,
204390 CODE-source,205638 CODE-auxiliary; other wire data is51590 bytes.
The309-query count comes from the conditional unique-decoding ideal-interactive
screen, not a post-quantum security choice. Other counts are sensitivity probes.

These are counterfactual sizes for retained commitments and the diagnostic
transcript, not authenticated high-query proofs. Ext8 and a new profile change
commitments and indices. Nevertheless, the measured geometry changes the next
engineering priority: packing/joint-opening or recursive compression must reduce
opened field data, not only Merkle paths. Simply improving the concentration
bound and increasing queries on this layout does not demonstrate sub300000 bytes.

Validation: Q8 fresh shared verification, exact whole-proof re-encoding and each
branch byte reconciliation passed. An independent occupied-parent arithmetic
calculation matched codec Merkle boundary sizes for every stage/query case.
Python compilation and diff checks passed; no Lean changes require a new audit.


### Packing-only expected-size screen

Added `report_packing_expectation.py`, which evaluates uniform-query expected
unique leaves and Merkle boundary nodes and optimizes each source/auxiliary
branch independently over power-of-two packing1..1024 within the degree and
64-lane limits. Expected stage sums do not require independence across stages.
Twelve exhaustive small-tree/query-count cases verify both expectation formulas
against actual codec boundaries. Ext4 non-PCS bytes reconcile to51590.

At309 queries, retained Ext4 expectation820634 bytes improves only to816299
with packings[16,1,8,8]. Projected Ext8 best is1103809 bytes with[16,1,4,8];
its non-PCS vectors/framing already cost123302 bytes. Retained Ext8 CODE auxiliary
packing4 would have100 lanes, above the64-lane limit, and is labeled ineligible.
At128 queries optimized expectations are495517 Ext4 and683223 Ext8.

These are expectations, not generated proofs or worst-case/security guarantees.
No statement/request cost is included; Ext8 is a coordinate-width/field-byte
projection. The result disfavors packing-only engineering: investigate joint
source/auxiliary PCS folding/commitments or recursion while retaining all binding
and adaptive-transcript obligations. Query counts are sensitivity inputs, not
secure parameter selections.

Validation: exhaustive expectation checks, baseline framing reconciliation,
Python compilation and diff checks passed. No Lean sources changed.


### Optimistic shared-fold/source-opening floor

Added a layout screen that deliberately removes every PCS round, terminal and
folded-oracle byte, then optimizes source packing. At309 queries, the four-tree
source-only expected floor is321599 Ext4 or349123 projected Ext8 bytes. Thus
sharing only the folding tail cannot reach300000 under this retained geometry.
These are expectations over uniform queries, not per-proof lower bounds or
impossibility statements about arbitrary protocols.

An optimistic alternative combines equal-height tables within each commitment
phase: source before bus challenges, auxiliary after. At projected Ext8/q309,
two source trees cost222888 expected bytes. Current local/framing data adds
123302, giving346190 before all omitted PCS work and public transport. Old
root/framing costs are intentionally retained, so this is a sensitivity subtotal,
not an exact hypothetical new format. No cross-phase root merging is allowed.

Next engineering comparison must include local claim-vector compression as
well as common folding/commitments, or use recursion. Common-point reductions,
source/auxiliary transcript timing, and candidate coherence remain necessary;
this screen does not supply a new prover or security theorem.

Validation: table heights/coordinate widths checked against the actual fixture;
input statement/report hashes recorded; exhaustive small-tree expectation checks
rerun; Python compilation and diff checks passed. No Lean changes.


### Fresh literal193 GKR compression integration

Ran the existing GKR/weighted-PCS prover on the same actual literal193 rows and
spec as the direct slice. Source roots and the entire serialized statement match
the baseline exactly. Auxiliary roots/finals were regenerated from the new GKR
profile's bus challenges; no old auxiliaries were reused. Proving GKR+weighted
PCS took14.23s and independent JSON verification1.08s on this run.

Compact binary52921 bytes versus direct121982. Including identical current
statement223788 and request919 gives277628 bytes. This is a Q8/Ext4 diagnostic
result, not the requested secure sub300000 result. The codec comparison report's
unchanged transcript/roundtrip statements refer to compact encoding of this new
GKR proof, not equality between the GKR and direct-profile transcripts.

Added `verify_prepared_gkr_slice.py`: shares the existing literal request/Lean
preparation and locally reconstructed AIR checks, then invokes mandatory compact
GKR/weighted PCS verification. Codec choice is fixed by the entrypoint, never
selected by proof data. The original frontend retains its default codec.
The full acceptance-to-literal-HoldsP and GKR common-source soundness composition
remain unproved. No full NEAR state or quantum-security claim follows.

Reproduction used `run_pq384_gkr_bus.py` with the baseline statement's spec,
source rows split from `/tmp/near-prepared-code-table/long-193-rows.json`,
`/tmp/near-pq384-target/release/rs_commit`, `/tmp/libnear_folded_v2.so`, and
`/tmp/libpq384_fft.so`; reference directory `airbender/generic-air`. Fresh prover
report and JSON/binary/statement/request artifacts retained under
`results/pq384-literal193-gkr`. Compact codec tested with
`test_pq384_compact_gkr_bus_codec.py`; frontend tested with
`test_prepared_slice.py --fixture results/pq384-literal193-gkr --gkr`.

Validation: GKR frontend fresh process plus15 cross-layer rejection cases passed;
original frontend fresh process plus14 baseline cases passed. Compact codec had
80 primitive roundtrips,3 primitive rejections, exact proof roundtrip,2 proof
rejections and independent-process verification. Python compilation/diff checks
passed. No Lean theorem changes; gate remains NOT_PASSED.


### Actual compact GKR leaf/query scaling

Added `report_gkr_query_scaling.py`. It verifies and re-encodes the retained
Q8 proof, replays GKR-derived weights, rebuilds the combined source polynomial
from authenticated cache identities, then reconstructs all12 folded trees and
checks each root against the proof. Larger query prefixes read actual source
leaves with authenticated paths and reconstructed folded leaves. Exact zero-tag
bit lengths and shared-path counts determine payload bytes. Fixed opening
header1294 bytes is independently reconciled from rounds/roots/terminal layout.

Proof sizes: Q8=52921, Q128=283053, Q239=432188, Q309=504163, Q463=640745.
Only Q8 is an actual verified profile. Other rows retain the Q8 transcript and
count authenticated-tree payloads; they do not certify a new high-query proof.
At309, source payload329974, fold payload155344, fixed18845. Outer GKR/local
data is17551; current statement/request adds224707, total728870.

This corrects the interpretation of earlier source-only screens: their full-word
leaf model is not a universal lower bound for this sparse zero-tagged witness.
Actual compact source data is measured here, and still exceeds300000 at309.
Local-vector compression has materially reduced its contribution; next focus
is source openings/shared chain or recursion, alongside common-source soundness.
No Ext8, full-NEAR, or quantum-security conclusion follows.

Validation: fresh compact decode/re-encode, all12 reconstructed commitment roots,
canonical leaf word counts, exact zero-tag bit counts, and independently derived
fixed opening header passed. Script rerun reproduced results; Python compilation
and diff checks passed. No Lean sources changed.


### Fresh joint-packing experiment

`screen_joint_packing.py` accounts for source trees plus one chain at the maximum
source degree. Exhaustive eligible power-of-two combinations select
[16,1,16,16] instead of[16,1,4,4], preserving max degree4096. Full-word expectation
is only a ranking heuristic; actual zero-tag payloads were measured next.

Generated a new GKR/weighted-PCS literal193 proof with source_packings[16,16]
and aux_packings[1,16], fresh commitments/challenges/auxiliaries. AIR,public,
rows,request and terminal degree match the previous fixture; roots/transcript
are not assumed unchanged. Proof52445 bytes, total current transport277154.
Artifact retained in `results/pq384-literal193-gkr-packed`. Existing prover and
codec runners used with `/tmp/near-literal193-gkr-packed-spec.json`; same native
libraries and source rows as the prior checkpoint.

Actual compact authenticated-tree replay: Q128272290,Q239392955,Q309457064,
Q463572709 bytes. At309, saving47099 bytes (about9.3%), source payload285515,
fold payload152704, fixed18845. Only Q8 is a generated verified profile; higher
counts remain counterfactual sizes without secure parameter certification.
This is a measurable improvement but not a solution to the secure size target.

Validation: independent JSON verifier, exact compact codec roundtrip/fresh process,
80 bitcodec roundtrips and primitive/proof negatives, new literal frontend with
15 cross-layer rejections, all12 reconstructed fold roots and exact query-size
accounting passed. No Lean changes or new soundness claims.


### Complete canonical GKR slice transport

Added `prepared_gkr_envelope.py`. Carries canonical public u32 values, two-table
shapes/packings, source commitments, exact Wasm bytes, UTF8 method, uint64 prepaid
gas, and framed compact proof. Reconstructs literal AIR locally from public CODE
length; no AIR JSON is transmitted or trusted. Decoded statement/request/proof
are exactly equal to the retained originals. Verification pins the caller's
expected request before invoking the same preparation and compact GKR verifier.

Actual envelope72486 bytes = proof52445 + transport20041, versus prior277154.
Including a separate expected-request JSON file gives73405 bytes, explicitly
counting that redundant caller input too. Security remains Q8/Ext4 diagnostic.
At309-query replay, unchanged overhead would yield477105 bytes, or478024 with
external request, so this does not resolve high-query secure size feasibility.

The parser checks framing before allocation/reconstruction, canonical field
encodings, strict UTF8, no trailing bytes, and profile identity. Shape/security
validation remains in the existing verifier. Oversized malformed lengths fail
against remaining input length; the u64 gas envelope is an explicit wire range.
No new Lean codec refinement or acceptance-to-HoldsP claim is made.

Validation: exact three-object roundtrip, fresh-process verifier,14 rejection
cases (caller mismatch, framing, fields, shape, roots, UTF8, published output,
proof integrity) and Python compilation/diff checks passed. Existing proof
artifact unchanged; envelope and report retained. Feasibility gate stays open.


### Computed-source GKR table interpretation

`PackedComputedGKRTable.lean` joins the modeled mutable Mobius transform with
the inverse table decoder used by recovered GKR candidate semantics. On every
bounded row/column, decoding computed coefficients returns the original packed
source cell, including partial-lane padding. A second theorem transfers this
identity to any polynomial with the same bounded coefficients. A third derives
the exact GKR current/next slot functional for the computed polynomial without
assuming its coefficient transform.

These are algebraic interpretation/refinement identities, not PCS extraction.
Accepted openings must still establish a common source binding or appropriate
common representative; mere polynomial proximity is not enough for equality.
Whole compiled GKR/AIR/PCS/bus soundness and quantum compilation remain open.

Validation: full `check.py` passed with 3752 registered results and enforced
axiom allowlist. No byte measurements or security parameters changed.


### Shared representative functional uniqueness

`FunctionalBatchRepresentative.lean` now derives functional-family equivalence
from two shared representatives of the same fixed source oracles, assuming
radiusLeft + radiusRight + degreeBound <= distinct domain size. It applies
scalar Reed–Solomon uniqueness to every obligation and point, then uses the
existing Boolean-coordinate functional interpretation to identify all requested
functional values. Unequal radii are supported. Individual lane proximity and
lane-selector geometry are not required for this functional conclusion.

This discharges the equivalence premise of the existing functional consistency
interface. It does not establish existence of a common representative, permit
separate per-point witness choices, identify entire tables, or establish AIR
satisfaction. The unique-decoding separation is retained; no list-decoding,
query-count, byte-size or quantum-security improvement is asserted.

Validation: full `check.py` passed with 3754 registered results and the enforced
axiom allowlist. Slice feasibility remains NOT_PASSED. Next critical obligation
is common representative existence with commitment/challenge chronology, followed
by composed acceptance-to-execution soundness.


### Far-source acceptance joined to adaptive weighted folding

`JointSourceAcceptance.lean` connects `joint_beta_candidate_far_count` to
`weighted_prefix_no_candidate_count`. If no fixed joint source representative
exists, actual weighted replay acceptance is bounded by the sum of the outer
tensor-extraction term, the adaptive folding term, and the query tail. The
initial candidate's indexed-domain agreement is transported to the same joint
beta source; no honest source polynomial or representative-existence premise
is introduced. The entire inner strategy, opening point and initial claim may
depend on the outer coordinates. Inner messages remain prefix-adaptive.

For nonempty sample and domain, normalizing the proved integer count gives
outerRounds*max(N,2)/Q + sum_i max(sizes(i+1),2)/Q + ((T-1)/N)^queries.
The strict regime 2*N+D<3*T remains required. Root geometry, source contraction
identity, independent ideal sampling and authenticated terminal oracles remain
explicit. This is an abstract far-case acceptance theorem, not a compiled
verifier or quantum soundness certificate. It does not lower query parameters.

The next composition duties are the actual heterogeneous compiler/transcript
instantiation and the near-case common trace supporting AIR, GKR, bus and the
published execution. Full NEAR 1 Pgas semantics, quantum security and secure
sub300000-byte feasibility are unchanged and incomplete.

Validation: full `check.py` passed with 3755 registered results and the enforced
axiom allowlist. Slice gate remains NOT_PASSED; byte artifacts are unchanged.


### Constant terminal reconstruction to indexed authentication

`WeightedTerminalAuthentication.lean` connects the existing typed reconstructed
RS terminal checker to the exact pointwise constant-oracle premise required
by weighted folding soundness. It models natural-domain pair leaves as
oracle(i), oracle(i+half), rather than adjacent positions. Equality to the
reconstructed constant tree implies every index below 2*half is that constant.
Accepted reconstruction therefore yields either this authentication or an
explicit distinct-tree/equal-root event. No degree premise on an arbitrary
committed oracle is introduced.

The executable weighted verifier uses degree1/domain4/lane1, so half=2.
It reconstructs all leaves and checks the terminal residual. Its compact codec
also reconstructs the last root/openings. The new theorem covers typed tree
semantics; canonical field/byte serialization and SHA-384 tree binding still
require refinement and a quantitative cryptographic reduction. Full near-case
trace composition, quantum security and the full NEAR target remain open.

Validation: full `check.py` passed with 3758 registered results and the enforced
axiom allowlist. Existing independent terminal tests passed for shapes
(1,4,1), (4,16,3), (16,64,2), using direct power-sum evaluations, Rust SHA384
roots and independent convolution residuals with rejection mutations. The
retained integration report records their counts. No proof sizes changed.


### Full byte-tree binding reduced to supported hash collisions

`sha384_source_tree_collision` in `SHA384MerkleSource.lean` constructs a
collision witness from two distinct, fully specified byte trees with equal
roots. It finds a differing leaf, constructs both accepted source paths and
applies framed-path collision extraction. The result identifies two unequal
byte messages with equal hashes inside those concrete path-query lists.
No global root injectivity or collision-resistance premise is assumed.

The theorem requires a common positive power-of-two tree size, a fixed context,
and explicit u64 bounds. Each selected path has depth+2 queries; this is the
support of the resulting witness, not the adversary's total hash-query budget.
For the current two-leaf terminal, depth is one. Applying this reduction to
the typed terminal theorem still requires canonical pair serialization to
preserve inequality. Unknown-root extraction and quantitative quantum hash
security are separate obligations. Whole-slice and full NEAR feasibility
remain incomplete, with no change to proof bytes or security parameters.

Validation: full `check.py` passed with 3759 registered results and the enforced
axiom allowlist. Slice gate remains NOT_PASSED.


### Canonical field-word serialization and tree binding

`CanonicalFieldWordBytes.lean` models `field_words` as concatenated four-byte
little-endian encodings of canonical natural coordinates below2013265921.
It proves encoded length, prefix parser roundtrip, and injectivity without an
assumed common input length. Coordinate-tree serialization consequently
preserves inequality. The final theorem composes this with constructed byte-tree
binding: different canonical coordinate trees sharing a root yield a concrete
unequal-input/equal-hash collision on constructed path-query supports.

This covers the exact canonical coordinate stream interface. Connecting an
abstract extension-field pair to that stream still needs the fixed coordinate
representation and layout refinement. No arbitrary-root extraction, quantum
collision bound or Fiat-Shamir theorem is implied. Full near-case semantics,
full NEAR1Pgas scope and secure sub300000-byte feasibility remain incomplete.

Validation: full `check.py` passed with 3764 registered results and enforced
axiom allowlist. No proof byte artifacts or security parameters changed.


### Certified Ext4 scalar-pair bytes

`Ext4PairBytes.lean` instantiates canonical word serialization for the certified
Fp4 tower. Flat coordinates are a.a,b.a,a.b,b.b, matching the existing
DiagnosticExt4Embedding and Python coefficient order. Pair leaves concatenate
the first and second scalar's four coordinates. Their encoding has exactly32
bytes, all coordinates are canonical by Fp.toNat_lt, and both word and byte
encodings are injective.

The pair-tree theorem composes the full reduction: distinct typed Fp4 pair
trees with equal serialized Merkle roots yield concrete unequal hash messages
with equal outputs in constructed path-query supports. This removes the
pair-coordinate injectivity assumption for the diagnostic terminal format.
The next step is instantiating the full terminal/folding contract with this
root function and actual transcript context. Earlier-oracle extraction,
near-case composition and quantum error bounds remain separate. Ext4 remains
diagnostic; no Ext8 implementation, full NEAR or secure-size claim is made.

Validation: full `check.py` passed with 3770 registered results and enforced
axiom allowlist. Proof artifacts and measured sizes are unchanged.


### Concrete terminal reconstruction authentication

`Ext4TerminalBinding.lean` composes the degree-one reconstructed RS check,
natural-domain scalar-pair interpretation, canonical Ext4 byte serialization
and framed Merkle collision extraction. An accepted check now yields either
pointwise constant-oracle authentication or a concrete unequal-input/equal-hash
collision on constructed terminal path-query supports. A second theorem
supplies the folding terminal premise when that specific collision is absent.
No abstract typed-tree injectivity, coordinate canonicality, serialization
injectivity or prior terminal-oracle degree premise is left to the caller.

The source trees and context are supplied to this theorem; it does not extract
an oracle from an arbitrary root. Compiled transcript/acceptance plumbing and
quantitative quantum hash/Fiat-Shamir reductions remain open. The field is the
diagnostic Fp4 profile, not an implemented secure Ext8 profile. Common-source
near-case semantics, full NEAR1Pgas and secure sub300000-byte feasibility
remain incomplete.

Validation: full `check.py` passed with 3772 registered results and enforced
axiom allowlist. No proof bytes or security parameters changed.


### Near functional acceptance through adaptive folding

Inspection found that `ChosenGKRSourceRecovery` already derives the sparse
lane image from projected sources and natural-domain geometry. The new work
therefore closes the downstream candidate-to-acceptance gap instead of adding
a duplicate sparsity lemma.

`NearFunctionalFoldAcceptance.lean` composes the close-family weighted
sumcheck theorem with adaptive weighted folding. For a wrong functional of
one shared representative, checked sumcheck-plus-folding acceptance has the
integer-scaled bound corresponding to 2*n/Q + foldSum/Q + ((T-1)/N)^queries.
The initial folding candidate's agreement is transported to the exact weighted
virtual source. Each folding strategy may depend on the full preceding
sumcheck path and remains prefix-adaptive in its own challenges. A general
finite product-count lemma is now shared with the far-case composition.

Representative/source identity, decoding separation, folding geometry,
terminal authentication and independent ideal sampling are explicit. Full
compiled GKR/AIR/bus/execution composition, quantum reductions, secure size
and full NEAR1Pgas feasibility remain open. No measured bytes changed.

Validation: full `check.py` passed with 3774 registered results and enforced
axiom allowlist. Slice feasibility remains NOT_PASSED.


### Retained literal193 geometry certificate

Replayed the retained packed193-instruction GKR proof through the existing
heterogeneous metadata audit:76 lanes,2072 live slot values,76 beta values,
three partial lanes and13 rejected metadata mutations. Independent live-slot
enumeration accepted the same76 selectors and rejected four geometry mutations.
The captured layout has16 row coordinates,inputLog13,commonLog12 and4096
private slots. Branch degrees are4096,256,4096,4096; their common-domain
projection exponents are1,16,1,1.

`Literal193GKRGeometry.lean` is reproducibly generated from the retained metadata
and kernel-checks lane WellFormed and CanonicalLaneSelectors for these exact
table records. It reuses existing GKRMetadataValidity and GKRSlotCertificate
proofs. The metadata hash is embedded in the module, while the captured proof
and statement hashes are retained in the audit report.

This instantiates numerical geometry for the measured fixture. Compiler-export
correspondence and beta equality are checked by executable parity, not a
universal Lean compiler refinement. The observed input dimension is not a
proof that circuit dimensions remain fixed over every transcript. Source
projection identities, full near/far composition, quantum security and the
full NEAR1Pgas secure-size target remain open.

Validation: full `check.py` passed with3776 registered results and enforced
axiom allowlist. No proof bytes or security parameters changed.


### Literal193 compiler challenge-layout sweep

Added a reproducible compiler-only sweep using the retained packed193 proof's
public inputs. It covers the captured case, a controlled rho=1 baseline, and
zero/one substitutions for rowpoint, mixing, tau and terminal claim. The nine
synthetic cases are not claimed to be accepted transcripts. All10 retain the
same private blocks and8192 input slots; arithmetic layer counts vary from5
to35. Constant folding therefore changes the arithmetic circuit, while this
finite sweep does not exhibit a change to the input dimension used by joint
source contraction.

For every case, the existing experimental fixed-input helper preserves the
output on a deterministic nonzero private vector both at8192 and at16384
input slots. The larger cap exercises zero-slot relocation. An undersized4096
cap is rejected in all10 cases. The retained proof profile remains unchanged;
this is evidence for integrating a trusted fixed input envelope, not a universal
challenge-independent bound or formal compiler proof. A production integration
must bind the trusted cap before challenges and establish overflow behavior.

Validation: all10 compiler cases,20 layout-output comparisons and10 undersized
cap rejections passed; Python compilation and diff checks passed. No Lean
sources changed, so the previous full formal audit remains applicable. Quantum
security, end-to-end soundness and full NEAR secure size remain open.


### Fixed-input envelope semantics

`GKRFixedInputEnvelope.lean` proves the transformation used by the experimental
fixed-input helper. For positive oldSize<=newSize, a zero reserved final input,
and bounded first-layer operands, replacing oldSize-1 references with
newSize-1 preserves each operand value. Consequently every first-layer output
and every subsequent circuit output is identical for arbitrary field inputs.
Only first-layer references change; later layers address gate outputs. The
input vector is extended with zeros, leaving all old positions intact.

The10-case literal compiler sweep now checks these exact zero-slot and operand
bounds and still passes20 output comparisons and10 undersized-cap rejections.
This is circuit-value preservation, not proof or transcript equivalence.
Trusted cap binding must precede challenges in an integrated profile; a changed
layout requires fresh proofs. Cap sufficiency/completeness, compiler refinement,
full protocol composition, quantum security and full NEAR secure size remain
open.

Validation: full `check.py` passed with3780 registered results and enforced
axiom allowlist; compiler sweep, Python compilation and diff checks passed.


### Fresh trusted fixed-input GKR-bus profile

The GKR-bus prover/verifier now accept an optional caller-supplied input_log.
Omitting it preserves the old profile and statement digest. Supplying it selects
`near-pq384-gkr-fixed-input-bus-v1`, binds the u64 cap in the statement digest
before bus challenges, and uses the fixed-input layer transformation. The cap
is not selected from proof fields. CLI verification requires the external
--input-log configuration; invalid caps and envelope overflow reject.

Generated a fresh literal193 proof with cap13 (8192 input slots), the same
source commitments and fresh profile-specific auxiliaries. Independent process
verification passed. Measured GKR+weighted PCS time was14.17s and independent
verification1.06s in this run; these exclude source/aux and table work and are
not general performance claims. Proof, statement, prover and negative-test
reports are retained under results/pq384-literal193-gkr-fixed13.

Validation:11 changed-cap/profile/message cases rejected, original statement
digest unchanged, old prepared compact frontend plus15 rejections passed,
Python compilation and full check.py passed (3780 registered results). The new
profile currently has JSON verification only; compact codec and prepared-request
frontend integration remain open. No compact-size or secure-profile claim is
made. Formal transcript refinement, cap sufficiency, common-trace composition,
quantum security and full NEAR1Pgas feasibility remain incomplete.


### Compact fixed-input prepared slice and complete envelope

Extended the compact GKR codec and prepared literal frontend with explicit
caller input_log configuration. The fixed profile has distinct compact magic;
decoding replays its cap-bound statement and fixed layout. The complete literal
envelope also has distinct magic and carries one cap byte, which must equal the
caller's configured cap. No proof-selected cap or profile dispatch is introduced.
Old defaults and original wire formats retain their behavior.

The retained fresh cap13 proof exactly roundtrips and verifies against the
requested Wasm/method/prepaid gas in a fresh process. Compact proof47846 bytes;
complete envelope67888 bytes = proof +20042 transport bytes. Including a separate
expected-request JSON gives68807 bytes. These are Q8/Ext4 diagnostic measurements.
The earlier proof used a different transcript/auxiliary witness, so this size
difference cannot be attributed solely to the fixed envelope.

Validation:14 cap/profile/framing/request/output negatives rejected; original
complete-envelope regression and its14 negatives passed. Python compilation,
diff checks and full check.py passed (3780 registered results). Actual
acceptance-to-execution composition, quantum hash/Fiat-Shamir reduction, secure
parameters and full NEAR1Pgas sub300000-byte feasibility remain open.


### Literal execution scaling to 769 instructions

Added optional `--pairs N` fixture generation while preserving the original
seven default cases. Generated actual Lean preparation/execution for 769
straight-line literal instructions; independent AIR inspection passed and
rejected altered public CODE fees, published exit and nonterminal final row.
The larger trace uses 1024 rows per table and a trusted input cap of14.

A fresh Q8/Ext4 proof passed independent verification, exact compact/wire
roundtrips, prepared-request verification and14 rejection checks. Retained
proof:63206 bytes; complete envelope:141712 bytes; envelope plus separate
expected-request JSON:144934 bytes. The193-instruction cap13 baseline is
47846 proof bytes and67888 envelope bytes. Caps and transcripts differ, so
this is not an isolated execution-length performance comparison.

Public CODE transport is now a measured scaling obstacle:264+100*n bytes
for n distinct literal instructions, exceeding300000 at n=2998 before proof
or Wasm bytes. Full-state scaling therefore needs authenticated code
commitments. These fixtures do not model1Pgas or certify secure parameters.

Validation: original seven fixture cases preserved, Python compilation,
independent AIR mutations, fresh compact verifier and14 negatives passed;
full check.py passed3780 registered results. The feasibility gate remains
NOT_PASSED. Corrected two stale gate descriptions: fixed-input transcript
binding is implemented, while formal transcript refinement and universal cap
sufficiency remain open.

Next composition boundary identified in current source: chosen_gkr_terminal_near_count
bounds a residual-candidate event for the single chosen source representative;
near_functional_fold_acceptance_count bounds checked sumcheck/folding acceptance
for a shared representative. Connecting chosen recovered GKR input to actual
fold acceptance, retaining source projection, chronology and terminal
authentication assumptions, is the next formal step. This inspection does
not itself discharge that composition or quantum Fiat-Shamir security.


### Chosen GKR input to checked folding acceptance

Added chosen_gkr_terminal_acceptance_count. The theorem uses the single
prechallenge chosen joint source representative, derives its sparse lane
coefficients from actual source projection, and constructs the shared
representative for heterogeneous opening weights. Sequential known-constant
subtraction converts a wrong full recovered GKR input claim into a wrong
coefficient-table functional of that same tuple. The existing adaptive
sumcheck/folding theorem then bounds checked acceptance rather than merely
a close residual-candidate event.

The normalized ideal bound is2*n/Q + sum_i(max(sizes(i+1),2))/Q +
((T-1)/N)^queries, with n=commonLog, N=4*2^n and initial degree2^n. The
formal statement is an integer-scaled count. This retains representative
existence, canonical geometry, source-oracle identity, terminal authentication,
independent ideal challenges and the strict unique-decoding regime as
explicit premises. It does not authenticate a commitment, refine executable
transcripts, compose all AIR/GKR/bus events, or certify quantum security.

Validation: module check and full check.py passed3781 registered results;
axiom closure remains propext/Classical.choice/Quot.sound. Registered the
module in imports, axiom audit and scope inventory; retained the integration
report and updated the still-NOT_PASSED slice gate. Full NEAR1Pgas and secure
sub300000-byte compression remain the objective.


### Near/far heterogeneous opening oracle identity

Proved heterogeneous_lifted_joint_coefficients and
heterogeneous_lifted_joint_oracle: the near-case lifted heterogeneous weight
MLEs equal the far-case joint beta coefficients at the same row/GKR/gamma/PCS
coordinates. The low PCS coordinates skipped by smaller lanes follow from
the repeated-weight MLE theorem. The resulting virtual source identity holds
for arbitrary received source functions, without honesty or proximity.

This removes an algebraic mismatch between the two acceptance formulations.
It does not yet merge their sample spaces: the far theorem samples the full
joint vector, while the near theorem fixes earlier row/GKR coordinates and
samples the PCS suffix. A chronological composition must additionally justify
conditional uniformity and fixed source/aux metadata in the actual protocol.
No representative existence, hash binding or quantum security claim follows
from the oracle equality alone.

Validation: both module proofs and full check.py passed3783 registered
results with the existing axiom allowlist. Imports, audit, scope inventory,
integration report and the still-NOT_PASSED feasibility gate are updated.


### Executable challenge chronology audit

Added audit_gkr_challenge_order.py, which instruments Transcript.commit/draw
during fresh verification of retained fixed-cap proofs and restores all
wrapped functions afterward. It checks source commitment before bus draws,
auxiliary commitments/finals before row draws, and all selected table mixing,
tau and row coordinates against the actual verifier output. The final GKR
draw suffix is checked against both returned query points and gamma.

Both193/cap13 and769/cap14 artifacts pass. Their joint opening dimensions are
55=16+27+12 and63=20+29+14 respectively (row + final GKR + PCS). Both have
quadratic commitments before reduction/fold challenges, fold roots after their
challenges, and query draws after terminal disclosure. Event records and proof
hashes are retained in literal193-challenge-order.json and
literal769-challenge-order.json. Python compilation and diff checks passed.
No Lean source changed; the preceding3783-result audit is unchanged.

This is finite implementation evidence, not a randomness theorem. SHA-384
draws are deterministic. To combine near/far bounds, the formal model must
account for intervening adaptive messages and other challenges while treating
the selected joint coordinates as independent ideal verifier coins. It must
also establish source/aux metadata is fixed before them, and handle sampler
abort/rejection semantics. Quantum Fiat-Shamir compilation and universal
compiler/transcript refinement remain open; the feasibility gate stays
NOT_PASSED.


### Near acceptance over the joint earlier-history/PCS experiment

Added ChronologicalChallengeCount: uniform_tuples_append proves exact ordered
sample-list equality for prefix/suffix concatenation, and
chronological_suffix_count lifts uniformly bounded conditional suffix events
to the full vector. Event/strategy dependence on the complete earlier history
is allowed; no independence between the strategy and that history is assumed.

Added near_history_fold_acceptance_count. One fixed shared source tuple
represents every history-dependent weight table. The initial claim, sumcheck
strategy and folding prover may all depend on the earlier vector. Wrongness
is part of the counted event rather than required at every earlier history.
The conclusion bounds actual checked sumcheck/folding acceptance on the joint
coordinate vector. Its integer budget multiplies the prior near bound by
Q^earlier, matching the sample-count factor and adding no normalized error.

The result still assumes ideal independent draws, a shared representative,
virtual source identity, fold geometry and terminal authentication. It does
not identify SHA-384 outputs with ideal coins or handle all adaptive protocol
scheduling. Next: instantiate the history-dependent full GKR wrong-input event
and combine far/near cases before global AIR/bus/execution composition.

Validation: all three new results pass the module checks and full check.py
(3786 registered results), with the existing axiom allowlist. Imports, scope
inventory, integration report and NOT_PASSED feasibility gate are updated.


### Full chosen GKR failure over joint history and PCS coordinates

Proved chosen_gkr_history_acceptance_count. The counted event now contains
a wrong full recovered GKR input claim AND checked sumcheck/folding acceptance
on the joint earlier-history/PCS coordinate vector. Rowpoints, GKR weights,
constants, terminal claims and subsequent proof strategies may depend on the
earlier history. The source representative is chosen once, without a history
argument; sparse lane recovery and shared functional representation are
derived for that same tuple.

Exact sequential constant subtraction derives the wrong PCS functional from
the full GKR failure event, so no separate discrepancy certificate is assumed.
The prior near-history theorem supplies the acceptance bound with no extra
normalized error term. Representative existence, received-oracle identities,
terminal authentication and ideal independent challenges remain premises.

Next is the actual coordinate-block instantiation and joint far/near failure
event. Protocol metadata stability, commitment extraction, global
GKR/AIR/bus/execution composition, quantum compilation, and secure full
NEAR1Pgas sub300000-byte feasibility remain open.

Validation: module and full check.py passed3787 registered results; axioms
remain within propext/Classical.choice/Quot.sound. Imports, audit, scope report,
integration evidence and NOT_PASSED slice gate updated.


### Concrete history coordinates and far-case acceptance

Added GKRHistoryCoordinates: history length is rowCoordinates+2*inputLog+1.
For valid lane metadata, row/left/right/gamma blocks read only that history.
The actual lifted weight-table coefficients at a PCS suffix equal the joint
beta coefficients at history++suffix. The virtual oracle identity is also
proved directly on take/drop of a correctly sized full joint vector.

A total fixed-length PCS extraction resolves the far theorem's requirement
that every strategy input produce commonLog opening coordinates. It equals
ordinary drop on valid full joint samples, with zero-default lookup for short
inputs. Added gkr_history_far_acceptance_count using this extraction and the
concrete heterogeneous coefficient family. Affinity and opening-point length
are now derived in this specialization.

These results establish concrete coordinate compatibility between the near
and far experiments. The final case split/event merger is still outstanding,
as are compiler metadata stability, source-oracle commitment binding, terminal
authentication, global GKR/AIR/bus/execution composition and quantum security.
No secure full NEAR1Pgas size claim is made.

Validation: six new results pass module checks and full check.py (3793
registered results), with the existing axiom allowlist. Imports, audit, scope
inventory, integration report and NOT_PASSED gate updated.


### Merged near/far GKR failure acceptance

Proved gkr_joint_failure_acceptance_count. On one joint history/PCS/folding/
query experiment it bounds accepted sumcheck+folding AND either absence of a
common prechallenge representative or a wrong full recovered GKR input for
the chosen representative. Representative existence is no longer a premise.

The source family fixes whether the near or far branch applies before any
coordinates are sampled, so the bound is max(nearBudget,farBudget), not their
sum. The near branch uses chosen_gkr_history_acceptance_count; the far branch
uses gkr_history_far_acceptance_count. Concrete take/drop oracle identity and
fixed-length PCS extraction connect both to the same strategy and sample
space. Sequential constant subtraction remains bound to the full GKR claim.

General and concrete far theorems now require source identity and terminal
authentication only on sampled outer vectors. This weakens unnecessarily
universal shape obligations without changing their conclusions. Exposed and
audited uniform_tuple_member_length; added concrete history accessors.

Remaining assumptions include fixed valid source/layout geometry, initial
virtual-oracle identity, terminal authentication, ideal independent sampling
and strict unique decoding. This is not computational extraction from roots,
full executable refinement, upstream/global GKR/AIR/bus/Wasm composition or
quantum security. Next is upstream failure propagation into this merged event
and discharge of concrete commitment/oracle premises.

Validation: full check.py passes3795 registered results with the existing
axiom allowlist; diff checks pass. Integration report, imports, audit, scope
and the still-NOT_PASSED feasibility gate updated. Full secure NEAR1Pgas
sub300000-byte compression remains unestablished.


### GKR terminal failure with subsequent PCS randomness

Reused the existing GKRTerminalFailure verifier-path split instead of
duplicating its abstraction. Added gkr_terminal_mismatch_last to expose the
last layer's combined functional with its complete preceding history;
gkr_terminal_recovered_mismatch identifies that event with the full recovered
input mismatch when the circuit input equals decoded private slots plus
known constants. The same-assignment equality remains explicit.

Added gkr_continuation_terminal_error_budget. A false-root accepted path with
arbitrary subsequent PCS randomness is bounded by the GKR repair term times
continuation mass plus accepted terminal mismatches counted on that exact
joint experiment. Acceptance and opening failures may depend on the full
GKR path; no independence between those events is assumed.

Next: construct the fixed circuit evaluation from the chosen tuple and map
the full layered path/ancillary randomness to the selected joint coordinates
used by the merged PCS theorem. Simply conditioning on all earlier or
intervening challenges would not discharge that mapping. Global AIR/bus/Wasm
composition, concrete commitment binding and quantum compilation remain open.

Validation: three new results pass module checks and full check.py (3798
registered results), retaining the axiom allowlist. Imports, audit, scope,
integration report and NOT_PASSED feasibility gate updated. No secure
full-NEAR1Pgas or sub300000-byte completion claim is made.


### Constructed circuit values from recovered input

Added GKRRecoveredCircuit using the existing gkrFiniteCircuit evaluator.
Finite-circuit append composition supplies an output-to-input value sequence
by evaluating prefixes from a single input assignment. Reverse depth0 is the
complete output and depth=layer count is the original input. Each actual
in-range gate agrees with the fixed-wiring layer evaluation required by GKR.

The input is constructed from recovered private slots plus known constants.
gkr_evaluated_recovered_terminal_mismatch now derives the final recovered
input mismatch without a separate assignment-equality premise. Path/circuit
depth alignment is explicit. The GKR output-reduction strategy starts with
reverse depth1 because its values are inputs to the output layer.

This is finite circuit semantics, not executable AIR compiler refinement.
Padded cube shapes, verifier-strategy binding to evaluated values, commitment
authentication, full-path/selected-coordinate sampling alignment and global
AIR/bus/Wasm/PQ soundness remain open.

Validation: five new results pass module checks and full check.py (3803
registered results), with the existing axiom allowlist. Imports, audit, scope,
integration report and the NOT_PASSED feasibility gate updated.


### Evaluated strategy binding and terminal alignment

Added GKREvaluatedStrategy. gkrBindCircuitValues replaces only the analysis
assignment; raw messages, adaptive strategies and gate data are unchanged.
gkr_bind_values_preserves_checks proves that verifier message checks do not
read that assignment. A structural finite-circuit path relation retains raw
checks, padded cube/gate shape, next-query wiring and transmitted-claim
linkage, while removing independently supplied layer values/equations.

The evaluated path implies the existing gkrCircuitVerifierPath: per-layer
values and adjacent evaluations follow from finite execution. Its shape
theorem derives the exact remaining layer/block count. The recovered terminal
mismatch adapter therefore no longer takes separate shape, depth or
assignment-equality premises. A false-root continuation budget is instantiated
for this evaluated strategy, leaving accepted terminal failures explicit.

Executable parser/compiler refinement must still establish the structural
checks and AIR output semantics. Full layered challenge sampling must still
be mapped to the selected joint PCS experiment before substituting its merged
near/far bound. Commitment authentication, global AIR/bus/Wasm soundness and
quantum compilation remain open.

Validation: five new results pass module checks and full check.py (3808
registered results), with the existing axiom allowlist. Imports, audit, scope,
integration evidence and NOT_PASSED gate updated.


### Fixed-profile layer routes and finite evaluator semantics

Extended the existing terminal DAG route checker with caller-supplied fixed
input caps. The profile must match that configuration; fixed captures undergo
full proof verification before route extraction. Legacy replay calls remain
supported. Added out-of-range/negative operands and non-power-of-two layer
mutations to the prior nine route negatives.

Both193/cap13 and769/cap14 pass full proof verification, route validation,
JSON roundtrip and12 negatives. Each has35 layers,7708 computed gates,6753
relays and7338 padding gates. The legacy193 route regression also passes all
12 negatives. Missing cap and changed cap12/cap14 reject the cap13 artifact.
Retained complete circuit/layout/route bundles and reports for both fixed
profiles. These are Python-validated captures, not concrete kernel proofs.

Added TerminalFiniteLayerCertificate. Existing DAG route semantics now
compose through finite gate lists, with explicit stored-gate and live-position
bounds. Acyclic DAG equations and initial placement yield root preservation
under the same gkrFiniteCircuit evaluator used by recovered GKR values.
The universal theorem assumes structural certificates; no emitter or parser
refinement is claimed by the captured Python checks.

Validation: three new results pass full check.py (3811 registered results)
with the existing axiom allowlist; Python compilation and diff checks pass.
Gate remains NOT_PASSED; compiler/transcript/global execution/PQ composition
and secure full NEAR1Pgas sub300000-byte feasibility remain incomplete.


### Lean finite route checker

Added TerminalStoredRouteCheck with finite live-node, position and gate lists.
The executable Boolean checker inspects source/position/storage bounds, zero
gates, and computed or relay routes against prior live placement. Its proved
soundness yields TerminalLayerRoute and finite storage bounds, then recursively
TerminalFiniteRouteChain. terminal_stored_certified_root composes checker
acceptance directly with finite acyclic DAG root preservation.

A kernel-evaluated regression theorem accepts a valid add route and rejects
six malformed cases: missing previous node, wrong zero gate, wrong computed
operation, invalid source node, invalid stored position and truncated positions.
The retained full fixed-profile captures are not yet encoded or checked as
instances of this Lean format. Initial placement, DAG acyclicity and root
liveness remain explicit root-theorem premises. Padding powers and operand
bounds for unused gates are separate executable shape invariants.

Validation: module and full check.py passed3815 registered results with the
existing axiom allowlist. Imports, audit, scope, integration report and
NOT_PASSED feasibility gate updated. No full capture, executable refinement,
global execution or quantum-security completion is claimed.


### Full retained route captures executed by Lean

Added CheckStoredRoutes.lean to parse the retained JSON bundles into the
proved finite checker format. It preserves canonical flat Ext4 constants in
the certified Fp4 tower order, validates node/gate arity and opcodes, rejects
noncanonical/out-of-range placement keys, and checks final root placement
before executing terminalStoredChainCheck.

Both fixed193 and fixed769 captures pass:10509 nodes,35 layers,21834 gates
each. Measured end-to-end Lean invocations took approximately1.55s each in
this run, including parsing and elaboration. Five full-size mutations per
capture reject: wrong zero gate, missing final root, invalid source node,
out-of-range live position, unknown opcode. The harness rejects compilation
errors as test evidence; all ten were runtime rejections. Input and adapter
hashes, sizes and outcomes are retained in lean-stored-route-captures.json.

This is native execution of a generically proved checker, not kernel-reduced
proof terms for the concrete JSON instances. Parser refinement, concrete
initial placement/acyclicity certificates, executable compiler correspondence
and cryptographic/global/PQ soundness remain open. No formal module changed;
the previous3815-result axiom audit remains the latest formal audit.

Validation: full capture and mutation harness passed; Python compilation,
scope inventory and diff checks passed. The slice gate remains NOT_PASSED.

### Combined stored bundle checker derives root preservation

TerminalStoredBundleCheck now checks DAG acyclicity, initial input and constant
placement, reserved zero, the finite route chain and final root placement in
one Boolean predicate. Its kernel-proved acceptance theorem preserves the
sequential source DAG root for every private input without separately assuming
acyclicity or initial placement. A kernel-evaluated small regression covers a
valid bundle and four boundary failures.

CheckStoredRoutes parses canonical layout constants and private capacity into
this combined checker. Both retained captures pass (10509 nodes, 35 layers,
21834 gates each); all 18 full-size malformed variants reject. Added cases
exercise cyclic dependency, misplaced input, changed constant and nonzero
reserved slot. Native capture execution is not a kernel proof term for JSON;
parser refinement and concrete kernel certificates remain open.

Validation: full check.py passed 3819 registered results with the existing
axiom allowlist; Python compilation passed. The integration report and slice
gate record the new evidence while retaining NOT_PASSED. Source program/AIR
compiler correspondence, global sampling composition, cryptographic binding
and quantum security remain unfinished. No secure size claim is added.

### Executable arithmetic witnesses and checked program composition

TerminalArithmeticCheck checks all ten existing arithmetic route constructors:
direct operation, constant folding, zero/one shortcuts and subtraction of an
operand from itself. The soundness theorem derives TerminalArithmeticRoute
from acceptance. The finite wrapper checks all operand/result indices so a
missing node cannot manufacture evidence through the default zero value.

The source-program composition theorem now uses the combined finite bundle
checker and a source acyclicity check. It concludes finite circuit output equals
independent TerminalProgramRun execution, under the explicit reconstruction
route including leaf bindings. This does not yet derive the reconstruction
route from the Python certificate: recursive signed expansion, balancing and
leaf-binding checks are the next compiler-certificate gap.

Kernel-evaluated Rat regressions cover 14 valid cases (all witness constructors
and all three constant-fold operations), reject 14 wrong-result substitutions,
and reject missing nodes, forged constant operands and a mismatched opcode.
The regression uses decide +kernel, not native_decide. Full check.py passed
3823 registered results with the existing axiom allowlist. No new full-capture
arithmetic check or concrete JSON kernel certificate is claimed. Integration
and gate evidence updated; the gate remains NOT_PASSED and full execution,
cryptographic composition, quantum security and secure size remain open.

### Checked signed expansion trees

TerminalExpansionCheck introduces recursive finite collect certificates with
explicit register identity and sign. Acceptance derives the existing
TerminalSignedExpansion relation, bounds the root and every retained leaf,
and preserves the executed DAG's signed root value under checked acyclicity.
The checker permits stopping at retained internal registers, while only add
and sub nodes may expand. Subtraction flips the right subtree sign.

Kernel regressions accept nested subtraction with exact ordered leaves,
retained internal registers and negative-root subtraction; they reject wrong
signs, swapped dependencies, multiplication expansion and absent leaf/branch
registers. Full check.py passed 3827 registered results under the existing
axiom allowlist. Imports, axiom audit, scope inventory and integration/gate
evidence are updated; the slice gate remains NOT_PASSED.

This establishes generic checker soundness, not parser refinement or concrete
kernel certificates for retained JSON. Balanced reduction and recursive
reconstruction/input binding still need executable checked certificates before
TerminalRebuildRoute can be removed as an explicit composition premise. Global
soundness, quantum security and secure proof size remain open.

### Checked balanced reduction certificates

TerminalBalanceCheck adds executable certificates for sign-aware pair joins,
whole passes and recursive balanced reduction. Soundness derives the existing
TerminalJoinRoute, TerminalPassRoute and TerminalBalanceRoute relations. With
checked DAG acyclicity the result equals the independently executed signed
sum of initial terms. Finite arithmetic witnesses check pair operands/results;
singleton carries and final empty/positive nodes also require finite bounds.

Stage output must exactly match the next stage's input. Passes must contain
at least two terms; empty and negative final terms require the correct zero
node and arithmetic route. Kernel regressions cover all four sign pairs,
two-stage reduction with an odd carry, exact initial terms/final result,
empty/positive/negative terminals, and rejection of wrong signs, subtraction
order, stage mismatch, nonreducing passes, nonzero anchor and missing nodes.

Full check.py passed 3832 registered results under the existing axiom allowlist.
Integration/gate and scope evidence are updated. The gate remains NOT_PASSED.
Recursive reconstruction/input binding must still compose these checkers to
derive TerminalRebuildRoute; concrete JSON parsing/kernel certificates and
global execution, cryptographic/PQ soundness and secure size remain open.

### Reconstruction checker composed to finite program execution

TerminalRebuildCheck checks finite records in dependency order, maintaining a
list of already established source/target mappings. Constant and input leaves
check exact values; binary records reference prior mappings and checked
arithmetic witnesses. Expanded records compose the signed expansion and balance
checkers, bind their exact ordered mapped terms, and require all retained leaves
to have prior mappings. Source and target record indices are bounded.

The final root must occur in the checked mapping context. Starting from an
empty context derives TerminalRebuildRoute with no assumed routes. The new
program theorem combines checked source acyclicity, reconstruction and finite
bundle acceptance to conclude finite circuit output equals independent source
program execution, without a separate reconstruction-route premise.

Input binding remains assignment-specific: checking a source constant against
inputs(slot) does not prove universal symbolic correspondence or extraction
from commitments. Retained JSON records still need translation and execution;
parser/compiler refinement and concrete kernel instances remain open.

Kernel regressions accept a full constant/input/binary/expanded chain and reject
wrong input values, unavailable dependencies, wrong final root, truncated
mapping, missing expansion leaf, forged constant, out-of-range default nodes
and an empty record list. Full check.py passed 3836 registered results with the
existing axiom allowlist. Integration, gate and scope evidence updated; gate
remains NOT_PASSED. Global execution and cryptographic/PQ soundness and secure
size remain open.

### Native reconstruction checks on retained fixed193 programs

CheckRebuildRecords parses retained source instructions, constants, selectors,
register records, signed expansion trees and balance stages into typed Lean
certificates. It infers arithmetic witnesses only by the proved finite checker,
orders records by source index, checks source/target acyclicity and executes
terminalRebuildRecordsCheck for each source program from an empty context.

The fixed193 capture contains two programs and 9152 records. Both programs pass
on deterministic diagnostic input assignments with seeds 0 and 7; complete
Lean invocations took about 2.1 seconds each. Six full-capture mutations reject:
wrong program root, flipped expansion sign, missing root record, changed input
target, changed selector and unknown opcode. The harness distinguishes runtime
rejection from compilation failure and also executes CheckStoredRoutes on the
same target bundle. Hashes, outcomes and timings are retained.

capture_fixed_rebuild.py reproduces the reconstruction artifact after full
fixed-profile proof verification and requires the replayed circuit to equal
the retained bundle. The capture helper accepts the two compiler calls made
by fixed-profile verification/replay only when their arguments agree; legacy
profiles retain the single-call requirement. The artifact report binds proof,
statement, bundle and reconstruction hashes.

Scope: native per-program checking on diagnostic assignments, not committed
input extraction or concrete kernel proof terms. Final equality-weight/claim/
rho batching across programs is still outside this Lean adapter. Parser/emitter
refinement, source AIR compilation, global cryptographic/PQ soundness and secure
size remain open. Full check.py again passed 3836 results with the existing
axiom allowlist; Python compilation and diff checks passed. Gate NOT_PASSED.

### Final batching checks and exact residual identity

TerminalBatchCheck binds each reconstructed program root to multiplication by
its expected equality weight, subtraction of its expected claim and scaling
by the current rho power. The recursive checker advances powers by rho.
Soundness derives the exact terminalResidualValue equation. Checked final
balance and the optional forced add-zero gate preserve this value at the
emitted DAG root. Default lookups cannot supply required constant witnesses:
finite arithmetic bounds connect their lookups to actual stored nodes.

Kernel regressions cover rho progression, expected weight/claim changes,
wrong arithmetic result, missing power node and direct/forced final roots.
This is an algebraic identity, not a probabilistic assertion that zero batch
implies every residual is zero. Expected values remain caller-supplied.

The fixed capture manifest now retains rho, equality weights and claims from
verified transcript replay. CheckRebuildRecords binds the two source-program
roots to these values, checks final balance terms and the exact circuit root.
Both diagnostic assignments pass all 9152 reconstruction records and final
batching. Fourteen mutations reject, including changed batch powers, weights,
claims, missing outputs, wrong final root and independently modified expected
rho/weight/claim. Stored-bundle validation passes in the same harness.

Full check.py passed 3841 results under the existing axiom allowlist; native
harness, Python compilation and diff checks passed. Integration/gate updated;
gate remains NOT_PASSED. Verified Python replay is not Lean transcript/parser
refinement. Committed assignment extraction, global soundness composition,
quantum security, full NEAR capacity and secure proof size remain open.

### One checked finite compiler contract

TerminalCompiledCheck packages each explicit source program, environment,
reconstruction records and batch entry. Its combined checker verifies source
and target acyclicity, reconstruction, batching, final balance/root and the
finite stored bundle. The main theorem derives finite GKR output equals the
rho-weighted residual of independently executed source programs from one
Boolean acceptance. No route, intermediate value equality or node equation
is a separate premise of that theorem.

The native adapter now preserves parsed source programs and records, constructs
these packages, parses the actual finite layout and invokes the same combined
checker. Both diagnostic assignments pass the retained two-program/9152-record
capture; all 14 malformed cases still reject. Kernel regressions also exercise
the complete finite interface and reject input/reconstruction/claim/output/
balance/program mismatches.

Full check.py passed 3845 registered results with the existing axiom allowlist;
native harness, Python compilation and diff checks passed. The gate remains
NOT_PASSED. This closes the generic structural compiler composition boundary,
not the external identification of explicit programs/environments with AIR
compilation and recovered committed data. Transcript/parser refinement,
concrete kernel capture certificates, global sampling composition, quantum
security, full NEAR capacity and secure proof size remain open.

### Recovered assignment connected to compiled execution

RecoveredCompiledCheck closes the representation difference between the
protocol's scattered recovered private values plus constants and the compiler's
capacity-split initial vector. Current/next lane support bounds imply that all
recovered private slots fall below capacity, including masked partial lanes.
Constants at or above capacity then establish exact function equality.

The compiled residual theorem is instantiated on gkrRecoveredCircuitInput and
on depth zero of gkrReverseCircuitValues. No input-vector equality is assumed.
The result remains conditional on the decoded tuple, metadata geometry and
combined compiler checker acceptance for that recovered assignment.

Support separation does not establish unique ownership or commitment
extraction. Kernel regressions preserve additive duplicate keys and missing
slots and show that constants inside the private region, or private slots
outside it, break the split. Existing canonical ownership is a separate theorem
for interpreting individual recovered columns.

Full check.py passed 3851 results with the existing axiom allowlist; diff checks
passed. Integration/gate/scope evidence updated; gate remains NOT_PASSED. No new
capture execution is claimed. Actual recovered-assignment checker acceptance,
AIR compilation/environment identification, global sampling/computational
soundness, quantum security and secure full-NEAR size remain open.

### Executable AIR expression/register checks

AIRExpressionCheck recursively checks each AIR Expr against actual source
instructions. It covers all constructors, exact operands and zero padding,
finite registers, column width and a real zero anchor for negation. Public
reads preserve the source semantics of default zero outside the public list.
Acceptance derives AIRProgramRoute and hence actual acyclic program execution
equals Expr evaluation. When the checked expression is a compiled table's
source root, this composes with reconstruction to its emitted DAG root.

Kernel regressions include nested current/next arithmetic, natural/public
constants, default public values and all selectors; they reject changed public
values, insufficient width, current/next mismatch, missing registers, nonzero
negation anchor and nonzero padding. Full check.py passed 3855 results with the
existing axiom allowlist; integration/gate/scope evidence and diff checks pass.

This is generic checker soundness, not new execution on retained AST captures.
Ordered weighted residual accumulation and auxiliary bus formulas still need
checked connections; a weighted table is not inferred to be a single AIR Expr.
Expected AIR capture binding, recovered environments, parser/transcript and
global/PQ soundness and secure full-NEAR size remain open. Gate NOT_PASSED.

### Checked ordered AIR residual accumulation

AIRAccumulatorCheck verifies finite residual/coefficient/product/result steps
against the exact source multiply/add instructions. Mixing powers advance in
order; all step registers are bounded. The full program check binds initial
zero, expected residual order, final add-zero copy and the last instruction.
Acceptance derives AIRAccumulatorRoute and the executed weighted-register sum.

When each residual has an accepted AIR expression route, the composed theorem
replaces register values with AST evaluations. It also composes with the
checked compiled table to its emitted DAG root. Auxiliary bus residual meaning
is still separate and is not asserted by the all-Expr corollary.

Kernel regressions accept ordered two-residual and empty sequences and reject
changed mixing, swapped order, wrong final output/coefficient, absent residual
and missing steps. Full check.py passed 3861 results under the existing axiom
allowlist; integration/gate/scope and diff checks pass. Gate NOT_PASSED.

No retained AIR capture execution was added here. Expected-AIR capture binding,
auxiliary bus formulas, recovered environments, parser/transcript refinement,
global cryptographic/PQ soundness and secure full-NEAR size remain open.

### Retained AIR/accumulator capture checked in Lean

The fixed-profile capture generator now re-emits source programs from verified
replay, requires exact retained instruction equality, and records expected AIR
expression routes, source-constraint prefix, mixing values and full accumulator
steps. The replay manifest includes the AIR artifact hash. CheckRebuildRecords
parses the expected ASTs and executes airExpressionCheck and
 airWeightedProgramCheck before its combined reconstruction/batching/layout
check. Column flags, AST shape, accumulator continuity and counts are checked.

Fixed193 has 2 programs, 1386 expression roots, 1228 source constraints and
1291 accumulator residuals. Both diagnostic assignments pass (about4.6s per
complete Lean invocation). All20 malformed cases reject, including6 new cases
for unknown AST, missing expression register, altered mixing/coefficient,
wrong final copy and missing AIR table. The full audit remains PASS3861.
Python compilation and diff checks pass; gate remains NOT_PASSED.

The63 auxiliary residuals are structurally covered by accumulation but their
bus-formula meaning remains separate. Native execution and verified Python
replay are not formal parser/compiler refinement or concrete kernel capture
certificates. Recovered inputs/environments, global cryptographic/PQ soundness
and secure full-NEAR size remain open. Diagnostic certificates are research
artifacts, not a newly measured proof envelope.

### Checked auxiliary formulas and mixed AIR/bus residuals

BusFormulaCheck adds a finite recursive checker for arbitrary field-valued
literals, current/next coordinates, selectors and add/sub/mul formulas.
Acceptance derives BusProgramFormulaRoute and independently executed formula
values. A mixed AIR/bus residual list composes with the ordered accumulator and
checked reconstruction, yielding the exact mixed sum at the emitted table root.
Exact instruction padding, register bounds and column bounds are checked.

The fixed replay generator now uses the existing auxiliary formula generator,
checks exact auxiliary width/count/order and retains all expected formula
register routes. The native adapter checks every supplied formula and requires
the combined source-constraint/formula register list to equal the complete
accumulator list. Expected-formula generation remains a Python refinement
boundary; supplied formula evaluation is not a global bus-validity theorem.

Validation: both diagnostic assignments pass all63 auxiliary formulas
(24 squares,24 multiplicity links,5 each first/transition/last) and all1291
residuals. Native invocations took about5.6s each. All24 malformed cases reject,
including wrong bus operation, absent register/formula and reordered formulas.
Full check.py passed3867 results under the existing axiom allowlist. Python
compilation and diff checks pass; integration and gate evidence updated.

The gate remains NOT_PASSED. Expected-formula generation, recovered input
identification, concrete kernel/parser/transcript refinement and global
execution/PQ soundness and secure full-NEAR size remain open.

### Symbolic reconstruction independent of private assignments

TerminalSymbolicRebuild keeps source current/next reads as input-slot nodes.
Its finite record checker binds input identities directly, rather than testing
whether values happen to match for one assignment. Constant, binary and signed
expanded records reuse the existing arithmetic/expansion/balance checks.
Acceptance from an empty mapping context yields source/target DAG root equality
for every private input assignment under checked acyclicity.

A symbolic placement maps current/next columns to base/nextOffset slots and
retains fixed selectors. The instruction and sequential-run lowering theorems
connect this DAG to actual TerminalProgramRun execution for every assignment.
Composition with an accepted finite stored bundle gives program equality at
that bundle's output. For the retained multi-program circuit, per-program
symbolic root equalities are the new evidence; a universal combined batched
interface still needs to substitute them into the complete compiler theorem.

Kernel regressions distinguish slot identity from equal sample values, reject
input-to-constant substitution and missing records, and accept an actual input
multiplication route. Full check.py passed3874 results with the existing axiom
allowlist. The native adapter now invokes the symbolic checker for each program.

Native validation passed both programs/9152 records through the symbolic path;
both diagnostic combined executions and all24 malformed cases also passed.
Integration/gate/scope evidence updated; diff checks passed. The gate remains
NOT_PASSED. Native JSON acceptance is not a concrete kernel capture proof.
Full universal batching/recovered-input composition, expected AIR/bus generation,
metadata ownership, parser/transcript/commitment refinement, global/PQ security
and secure full-NEAR size remain open.

### Universal symbolic compiler and recovered-input composition

SymbolicCompiledCheck packages fixed source placement, source program,
reconstruction records and batch entry. Its predicate has no private input
argument: one acceptance checks symbolic reconstruction, batching and the
finite physical layout. The resulting theorem quantifies over every private
assignment and equates finite GKR output with the residual of independently
executed source programs under their constructed environments.

A second theorem instantiates this universal result at the scattered decoded
private tuple and uses support separation to match gkrRecoveredCircuitInput.
It no longer assumes compiler-checker acceptance specific to that recovered
assignment. Decoded tuple existence/extraction, metadata ownership and the
expected AIR/transcript/formula bindings remain separate obligations.

The native adapter constructs the symbolic table packages and invokes the
combined input-independent checker. Its former per-program symbolic calls are
subsumed by this combined check. Kernel regressions exercise accepted layout,
wrong base placement, missing reconstruction, wrong output slot and distinct
positive/negative input outputs. Full audit passed3878 results with the existing
axiom allowlist.

Native validation passed the combined symbolic checker on the retained two
programs/9152 records. Both diagnostic runs and all24 malformed cases pass.
Integration/gate/scope evidence and diff checks pass; gate remains NOT_PASSED.
Universal expected AIR/bus value substitution, formula-generation/metadata
refinement, commitment extraction and global/PQ soundness and secure full-NEAR
size remain open. Native JSON execution is not a concrete kernel capture proof.

### Universal formula-to-finite-circuit contract

SymbolicFormulaCheck proves acyclicity checks depend only on binary register
dependencies, so symbolic program acceptance supplies acyclicity for every
value-specialized environment. Checked mixed AIR/bus formulas and ordered
accumulation then replace program outputs with formula sums for every input.

The combined predicate includes the input-independent compiler certificate and
all per-table formula/accumulator checks. Its main theorem equates finite GKR
output with the explicit batched mixed-formula residual for every private
assignment. A recovered-input corollary uses the same predicate and support
separation, with no assignment-specific acceptance or program-value premise.

The adapter now preserves parsed formula/accumulator packages and invokes the
combined formula-level checker. Kernel regressions cover one complete nonzero
input path plus changed current/next formula, missing residual, wrong final
copy, changed base and differing positive/negative inputs. Full audit passed
3883 results with the existing axiom allowlist; adapter elaboration passed.

Native validation passed the combined formula compiler predicate for both
retained diagnostic assignments; all24 malformed cases reject. Integration,
gate, scope and diff checks pass. Gate NOT_PASSED. This is equality with the
supplied checked formulas, not proof of constraint satisfaction or formal
identification of formula generation with the intended AIR/bus specification.
Decoded-column environments, transcript binding, global sampling/computational
soundness, quantum security and secure full-NEAR size remain open.

### Canonical decoded columns supply the symbolic environment

RecoveredSymbolicEnvironment uses the existing canonical lane ownership proof
to identify every live source/auxiliary column with a polynomial in the fixed
tuple. Checked base and next-offset placement connects these owners to actual
symbolic program current/next reads. Source and auxiliary packed div/mod
coordinates are handled separately, including the final partial lane.

The environment theorem chooses one entire decoded column table before all
rowpoint/current-next choices. Every live column retains tuple provenance and
both reads equal its MLE/next-MLE at the corresponding lane point. No vector
agreement is assumed; canonical enumeration and all-support nonoverlap remain
explicit. This constructs an assignment, not proof of AIR satisfaction or
commitment extraction.

Kernel regressions cover source/auxiliary offsets, partial source packing,
current/next addresses and rejection of wrong base/next offset. Full check.py
passed3886 results with the existing axiom allowlist. No new native capture
execution was required. Integration/gate/scope and diff checks pass; gate
NOT_PASSED. Formula evaluation transport, complete verifier metadata premises,
specification/transcript binding, global/PQ security and secure full-NEAR size
remain open.

### Checked formulas transport to fixed decoded columns

FormulaEnvironmentTransport proves that bounded current/next agreement and
selector agreement preserve checked AIR and bus evaluation and their ordered
weighted mixture. Combining this with canonical ownership chooses one decoded
column table before all later rowpoints, programs, public values, mixing powers
and checked residual lists. The symbolic recovered-input mixture therefore
has the same value on those decoded-column MLE/next-MLE reads.

Kernel regressions allow differing unused columns, reject out-of-width reads,
and demonstrate sensitivity to current/next swaps and selector changes. Full
check.py passed 3893 registered results with the existing axiom allowlist.
No native adapter/prover changed; no new native capture run was needed.

This is evaluation transport, not AIR satisfaction or commitment extraction.
Canonical enumeration, support disjointness, placement and width bounds remain
explicit. Selector/specification binding remains open. Next connect all table
transports to symbolic_formula_recovered_value, then the global verifier and
execution contract. Gate remains NOT_PASSED; secure parameters, quantum
soundness and full-NEAR sub300000-byte feasibility are unresolved.

### Complete circuit evaluated on a fixed decoded table family

DecodedFormulaCircuit composes environment transport across all formula tables
with symbolic_formula_recovered_value. One decoded table family, chosen from
the fixed polynomial tuple before rowpoints, preserves every live column's
provenance. The full finite GKR output is exactly the terminal residual of the
decoded AIR/bus mixtures, retaining table order, weights and claims.

Full check.py passed 3895 registered results with the existing axiom allowlist.
This is generic formal composition; no native prover/adapter changed. The
compiled circuit and supplied selector values are fixed in this theorem;
challenge-dependent selector generation is not silently certified. Metadata
membership, placement/width, slot geometry and canonical disjoint ownership
remain explicit premises. The executable adapter currently reads selector
values from the reconstruction certificate, so intended selector binding is
still a concrete verifier integration obligation.

Next bind metadata, formulas and selectors to protocol construction and compose
with chronological failure bounds and execution semantics. This closes the
planned all-table recovered-circuit identity, not accepted-proof soundness.
Gate remains NOT_PASSED; full-NEAR capacity, secure parameters, quantum security
and secure sub300000-byte feasibility remain unresolved.

### Selector products bind decoded columns to one row environment

Inspected the native selector construction and certificate checker. Python
computes product(1-r), product(r), and 1-product(r), and checks captured values
against the terminal point. The Lean adapter currently parses those supplied
values without deriving them from a terminal point.

DecodedSelectorBinding introduces an executable point-length/product check and
uses existing selector MLE proofs to derive boundary flag semantics. In-range
lane-coordinate alignment then connects decoded-column environments to a
common-point row environment, including cyclic next rows. Checked AIR/bus
mixtures preserve their values. Padded point coordinates and unused columns
need not agree. This does not silently assume selectors are Boolean at arbitrary
field points.

Kernel regressions cover the empty point, off-Boolean [2,3], both Boolean corners,
and rejection of wrong transition/length. Full check.py passed 3899 registered
results with the existing axiom allowlist. No native adapter/prover changed.
The new selector checker is not yet invoked by the executable adapter; transcript
point binding and lane alignment remain explicit integration work. Formula
specification, execution, global/PQ soundness and secure full-NEAR size remain
open. Gate NOT_PASSED.

### Native selector checks consume replayed terminal points

The fixed-profile capture now retains expected terminal points and statement
row logs after full proof verification and matching circuit replay. The Lean
adapter requires exact table coverage and invokes symbolicSelectorCheck before
reconstruction. It checks point length and first/last/transition products using
the same Fp4 embedding as the circuit. Circuit, reconstruction and AIR artifacts
remain unchanged; only the replay manifest gains terminal point data.

Validation passed: full check.py (3899 registered results), stored bundle check,
two native diagnostic assignments, and 28 runtime rejection cases. Changed
selector, changed/truncated point and wrong row log fail the new selector check;
missing terminal table fails coverage. Results retain hashes and reasons.

The manifest is still supplied data to Lean; its transcript derivation and the
Python replay are not formally refined. Selector products do not uniquely bind
a point (for example coordinate permutations preserve them). Lane alignment,
intended formula generation, global execution/soundness, quantum security and
secure full-NEAR size remain open. Gate remains NOT_PASSED.

### Chronological history derives common table rowpoints

HistoryDecodedEnvironment eliminates the separate lane-alignment premise when
using gkrHistoryRowpoints: source/auxiliary lanes inherit rowOffset and rowLog
from table metadata regardless of packing/group. Total table point extraction
has exactly rowLog entries; checked metadata and complete chronological history
length prove these are actual history entries, not zero-padding.

Selector-checked decoded environments and mixtures therefore agree with the
common-point row environment. An all-table theorem transports decoded formula
outputs to historyRowFormulaOutputs with unchanged order, weights and claims.
This output identity can be substituted directly into the recovered circuit
identity. It does not authenticate history or prove its transcript derivation.

Kernel regressions cover nonzero offsets, partial source/auxiliary lanes, short
history padding, changed offsets and out-of-dimension zero. Full check.py passed
3906 registered results with the existing axiom allowlist. No native code
changed. Executable history/metadata refinement, intended formula generation,
execution and global/PQ soundness remain open; gate NOT_PASSED. Secure full-NEAR
capacity and sub300000-byte feasibility are not established.

### Decoded compiler mixtures reach AIR trace semantics and zerocheck bounds

DecodedTraceSemantics constructs a total AIR trace table from decoded columns,
without assuming valid rows. The decoded common-point environment equals the
AIR row MLE environment and the auxiliary bus environment. The compiler's
power accumulator equals ordered lanePowerBatch independently of register labels.
With an explicit source-then-auxiliary formula ordering, the mixture equals
combined point residuals and, at Boolean points, actual trace-row residuals.
Nonlinear expressions are evaluated after column interpolation; no invalid
commutation of constraints with MLE is used.

The initial zerocheck count now applies directly to the decoded compiler
accumulator: a nonzero row residual yields the existing finite-sample bound.
Columns and formulas are fixed before batching samples, sample values are
distinct, and the offending row and residual-family bounds remain explicit.
This is ideal initial-check soundness, not global acceptance or Fiat-Shamir.

Full check.py passed 3913 registered results with the existing axiom allowlist.
No native code changed. Supplied source/auxiliary lists still require intended
specification binding; decoded execution validity, global chronological
GKR/PCS composition, commitment extraction, quantum security and secure
full-NEAR size remain open. Gate NOT_PASSED.

### Adaptive decoded-local soundness and explicit terminal failure

DecodedLocalSoundness identifies the compiler-accumulator terminal event with
the existing AIR trace local event on complete challenge paths. The initial
batching plus adaptive sumcheck bound now applies to an invalid decoded row:
for q>0, r rounds and L residuals, honest-terminal acceptance is at most
(L-1+r+(d+1)*r)/q. Lean proves the scaled integer count; strategies may depend
on initial mixing/tau and previous round challenges. Fixed decoded columns,
formula ordering, degrees, distinct samples and initial zero claims are explicit.

A separate event-split theorem bounds arbitrary acceptance passing sumcheck
checks by honest-terminal local acceptance plus accepted terminal mismatch on
the same experiment. No independence is assumed, and terminal correctness is
not silently included in verifier acceptance. The mismatch event must next be
connected to the chronological GKR/PCS failure analysis.

Full check.py passed 3916 registered results with the existing axiom allowlist.
No native code changed. Intended formulas, executable transcript refinement,
commitment extraction, quantum security and secure full-NEAR size remain open.
Gate NOT_PASSED.

### Terminal mismatch batching cancellation is explicit

TerminalBatchFailure identifies terminalResidualValue with the difference of
ordered output/claim power batches. For a fixed wrong table claim, cancellation
occurs at at most tableCount-1 distinct rho values. The result transfers through
per-rho circuit identities even when the compiled DAG changes with rho; only
the semantic output/claim list must be fixed before rho.

A continuation theorem adds this cancellation budget to a conditional downstream
nonzero-circuit-output acceptance budget. Strategies may depend on rho and no
independence between acceptance and failures is assumed. This is the interface
needed between local terminal mismatch and GKR/PCS; the downstream budget is
still an explicit premise, not a claimed completed composition.

Kernel examples show opposite mismatches cancelling at rho=1 and a later-only
mismatch disappearing at rho=0. Full check.py passed 3921 registered results
with the existing axiom allowlist. No native code changed. Actual chronological
experiment matching, intended formulas, commitment extraction, quantum security
and secure full-NEAR size remain open. Gate NOT_PASSED.

### Batch cancellation composes with evaluated GKR repair

BatchedEvaluatedGKR derives the first wrong-claim predicate from a nonzero
finite circuit output, actual computed layer values, a Boolean root query and
zero transmitted claim. It instantiates the downstream GKR repair term in the
batching continuation bound. The remaining term is accepted terminal mismatch
on the exact fixed-envelope GKR-path/continuation experiment. Circuits, inputs
and strategies may depend on rho; semantic output/claim pairs remain fixed
before rho. No independence of acceptance and mismatch is assumed.

The merged PCS theorem cannot yet supply the remaining pcsBudget without
matching chronological coordinates and event predicates. Root/path checks and
per-rho compiler identities also need executable verifier instantiation. This
checkpoint removes an abstract downstream GKR budget, not the PCS premise.

Full check.py passed 3923 registered results with the existing axiom allowlist.
No native code changed. Transcript/specification binding, commitment extraction,
quantum security and secure full-NEAR size remain open. Gate NOT_PASSED.

### Final GKR block exactly enumerates the PCS joint coordinate space

Review found a composition constraint: merged far-case PCS soundness averages
over rowpoints as well as final GKR and PCS coordinates. It must not be inserted
as a conditional bound after fixing rowpoints. GKRBlockCoordinates proves exact
sampling identities to preserve this required averaging.

Flattening a GKR block as left++right++[gamma] gives uniform tuples of length
2m+1 exactly, including order and multiplicities. Challenge paths split across
round-list append. Adding rowpoints and the PCS opening point gives precisely
the heterogeneous joint outer space; arbitrary event counts with later
continuations agree after coordinate assembly.

Kernel tests cover axis order, zero axes and duplicate samples. Full check.py
passed 3929 registered results with the existing axiom allowlist. No native
code changed. Earlier GKR block rearrangement, concrete accessor/mismatch
identities and merged PCS assumptions remain to be connected. These ideal
sample identities do not establish Fiat-Shamir sampling. Global/PQ soundness
and secure full-NEAR size remain open; gate NOT_PASSED.

### Evaluated terminal mismatch matches joint-history coordinates

GKRJointTerminalEvent proves left/right/gamma accessor identities for assembled
row-prefix plus final GKR block. Axes agree even outside their dimensions, where
both are zero. Valid lane rowpoints are invariant under suffix append, so final
GKR challenges do not alter source row coordinates. Exact lengths prove the
merged PCS take/drop split recovers history and opening suffix.

Using evaluated structural path checks, terminal mismatch now equals the
joint-history recovered-input functional mismatch. The recovered tuple and
constants remain explicit; this does not establish commitment extraction or
identify the source tuple with the chosen PCS representative automatically.
Earlier GKR block rearrangement and prover-message mapping remain necessary
before applying the merged bound while preserving rowpoint averaging.

Kernel regressions cover distinct axis/gamma values, padding and incorrect row
prefix offsets. Full check.py passed 3934 registered results with the existing
axiom allowlist. No native code changed. Global/PQ soundness and secure full-NEAR
size remain open; gate NOT_PASSED.

### Earlier GKR sequences lift joint PCS counts without fixing rowpoints

GKREarlierJointCount proves a finite-count exchange retaining all event and
continuation dependencies. The rows-first GKR/PCS experiment becomes a sum over
earlier GKR sequences of exactly the merged PCS joint-coordinate experiment.
Rows, final left/right/gamma and opening coordinates remain sampled together.
A uniform bound for each earlier sequence lifts with the exact earlier-path
multiplicity, without an independence assumption or reordering protocol messages.

This resolves the counting-order obstacle, not the concrete prover-family
mapping. The sent/claim/folding strategy families and accepted event still need
instantiation for each fixed earlier sequence, with all source/authentication
premises preserved. It remains invalid to use the far-case theorem after fixing
rowpoint values.

Full check.py passed 3937 registered results with the existing axiom allowlist.
No native code changed. Global/PQ soundness, secure parameters and full-NEAR
sub300000-byte feasibility remain open; gate NOT_PASSED.

### Construct history-indexed terminal claims from GKR messages

GKRHistoryStrategy decodes the row prefix and final GKR block from joint history
and proves the inverse on exact-length samples. Generic downstream families can
be reindexed without losing their dependencies. The terminalClaim needed by
the merged PCS theorem is now explicitly constructed from a/b messages for the
fixed earlier sequence. Evaluated mismatch uses this constructed function,
rather than a caller-supplied equality to an unrelated terminal claim.

Kernel examples cover distinct row/axis/gamma values and malformed truncated
history, whose right axis is empty and gamma defaults to zero. The inverse
lemmas require lengths and do not validate malformed histories. Full check.py
passed 3942 registered results with the existing axiom allowlist. No native code
changed. Reindexed sent/claim/folding checks, source representative identity and
authentication premises still need merged-theorem instantiation. Global/PQ
soundness and secure full-NEAR size remain open; gate NOT_PASSED.

### Reindexed PCS families preserve the accepted mismatch event

GKRHistoryPCSFamily packages concrete row/block-indexed sent polynomials, claims,
constants and folding provers, then constructs their history-indexed versions.
Valid assemblies preserve every family, weighted sumcheck checks, full weighted
folding replay acceptance, and the initial constant-subtracted claim equation.
The initial equation uses actual final GKR a/b messages and recovered axes.

The combined evaluated-terminal-mismatch AND concrete PCS-acceptance event is
now equivalent to the history-indexed event used by the joint PCS interface.
This does not yet invoke the numerical merged bound: chosen representative
identification, source-oracle equations, geometry and terminal authentication
still require instantiation. The no-representative branch remains essential.

Full check.py passed 3946 registered results with the existing axiom allowlist.
No native code changed. Executable refinement, global/PQ soundness and secure
full-NEAR size remain open; gate NOT_PASSED.

### Concrete GKR/PCS sampling now invokes the merged near/far bound

GKRConcretePCSCount proves exact event-count transport from concrete rowpoints,
final block, PCS point, fold path and query samples to joint history. It invokes
gkr_joint_failure_acceptance_count with the constructed terminal claim and
reindexed message/prover families. The resulting concrete accepted failure
count retains absence of a joint representative OR recovered-input mismatch
and the max(nearBudget,farBudget) bound. The chosen representative is used
directly; representative existence is not smuggled in as an assumption.

All original ideal-oracle hypotheses remain explicit: source/projection and
weighted oracle identities, canonical geometry, initial constant subtraction,
RS/folding geometry, unique-decoding regime and authenticated terminal oracle.
This is a numerical theorem instantiation, not a proof those hypotheses hold
for the native verifier. Earlier-sequence lifting and global local/GKR error
composition must preserve the joint averaging over rowpoints.

Full check.py passed 3948 registered results with the existing axiom allowlist.
No native code changed. Computational/QROM soundness, secure parameters and
full-NEAR size remain open; gate NOT_PASSED.

### Parameter feasibility checked against the merged PCS bound

Added report_joint_pcs_parameters.py reading the retained fixed193 statement and
replay manifest with statement hash validation. The normalized merged bound is
(A+max(2*C,jointDimension*max(N,2)))/fieldSize+((T-1)/N)^queries.
For rowCoordinates16,inputLog13,C12,N16384,T12289 the challenge coefficient is
917500. The far-case term is included; the older unique-basin screen alone did
not account for it. Exact normalization matches literal theorem-count formulas
on 324 small cases and all feasible actual-geometry parameter boundaries.

Ext4 cannot certify even 128 ideal bits under this bound at any query count.
Ext8 projects to 309 queries for128 ideal bits and463 for192, but cannot certify
256. Ext12 arithmetic projects to617 queries for256. These are sufficient-bound
screens, not attacks or impossibility claims. Ext8/12 projections do not create
implemented fields or new proof profiles; 128 ideal bits is not 128 PQ bits.

JointPCSParameterArithmetic kernel-checks the coefficient, challenge-only
obstructions and adjacent query boundaries. Full check.py passed3950 registered
results with the existing axiom allowlist. No generic normalization theorem or
secure-byte claim is made. Global composition, QROM loss and high-query/extension
size remain unresolved. Gate NOT_PASSED. This reinforces that closing soundness
alone will not make the present Q8/Ext4 diagnostic profile a secure solution.

### Merged parameter normalization is now proved generically

JointPCSNormalization closes the preceding arithmetic-normalization gap.
Literal near/far count formulas factor by S^(H+2C); their maximum has coefficient
A+max(2C,(H+C)*max(N,2)). For S>0 and H+C>0 the original scaled-budget target is
equivalent to the normalized integer test. No approximate logs or division by
zero are used. The maximum is preserved rather than replaced by a union bound.

For retained193 geometry the theorem identifies the original budget target
with literal193MergedBoundMeets for every extension degree, bit target and query
count. Previous kernel query-boundary checks therefore apply to the original
budget arithmetic, not only to a separately asserted normalization. This still
does not establish native field construction, source/authentication hypotheses,
ideal sampling, global composition or QROM security.

Full check.py passed 3955 registered results with the existing axiom allowlist.
No native code changed. Larger-field implementation, secure query/proof bytes
and full-NEAR quantum soundness remain open; gate NOT_PASSED.

### Batch/GKR composition keeps PCS errors averaged

AveragedTerminalFailure provides the composition form needed by the merged
far-case bound. Conditional acceptance keeps variable terminal-error counts;
batching adds its cancellation term without demanding a uniform conditional
PCS budget. The evaluated GKR theorem supplies its actual repair term and leaves
the sum of accepted terminal mismatches over rho explicit. A rowpoint summation
lemma preserves that total, allowing joint averaging before the PCS estimate.

The earlier per-rho pcsBudget theorem remains valid under its stronger premises,
but this new theorem does not require that premise and is the appropriate route
for the joint far-case analysis. It does not yet assemble the selected local
mismatch and no-representative events into a single global bound.

Full check.py passed 3959 registered results with the existing axiom allowlist.
No native code changed. Executable source/authentication assumptions, global/PQ
soundness and secure full-NEAR size remain open; gate NOT_PASSED.

### Invalid local traces compose with averaged downstream errors

DecodedLocalContinuation materializes the mixing/tau/path experiment and proves
its good-terminal count equals decodedLocalAcceptedCount. Full acceptance
implying local checks splits into the already-proved local event and downstream
repair on wrong terminal claims. Failed local checks contribute no acceptance.
The invalid-trace theorem supplies the local term; downstream errors remain one
joint total over all local prefixes, without a per-rowpoint PCS bound.

This is the local-to-downstream composition interface. Its conditional repair
and joint-error premises still need substitution of the concrete terminal
output, averaged batching/GKR and merged PCS theorems. No-representative failure
and executable source/authentication/specification refinement remain open.

Full check.py passed 3962 registered results with the existing axiom allowlist.
No native code changed. Global/PQ security and secure full-NEAR size remain open;
gate NOT_PASSED.

### Decoded family now precedes compiler and batching choices

While connecting local mismatch to terminal batching, identified a quantifier
issue: the previous circuit theorem fixed compiled tables before selecting its
decoded witness. Applying that existential separately for each rho does not
establish one assignment fixed before rho. No prior theorem was invalid, but
this stronger order is required for the planned batching composition.

PrechallengeDecodedTables uses a metadata-only placement with zero selectors
to select decoded columns, then proves the same columns work for every later
metadata-consistent placement. The entire metadata-indexed family precedes all
compiler tables, selectors, rowpoints and batch challenges, retaining polynomial
provenance. Any later checked formula/output list evaluates on that same family.
This can be substituted into the universal recovered circuit identity without
reselecting decoded data for each rho.

Full check.py passed 3966 registered results with the existing axiom allowlist.
No native code changed. Local-mismatch-to-fixed-output binding, global counts,
no-representative integration, computational/QROM security and secure full-NEAR
size remain open; gate NOT_PASSED.

### Local terminal mismatch reaches fixed semantic batching outputs

TerminalSemanticOutputs erases compiler register and reconstruction witnesses
while retaining the ordered formulas, public values, metadata, mixing, weights
and claims. The preselected decoded family transports checked compiler outputs
through chronological rowpoints and selector checks into this semantic list.
A wrong local weighted claim yields an indexed unequal output/claim pair; with
the list fixed before rho, a later rho-dependent circuit can cancel it at at
most tableCount-1 distinct sampled challenges.

The semantic-list binding and local point/mixing/formula/weight/claim identities
remain explicit premises. This does not prove that the native transcript or
formula generator satisfies them. Concrete global counts, no-representative
integration, executable specification binding and QROM security remain open.

Full check.py passed 3972 registered results with the existing axiom allowlist.
No native code changed. No new secure byte measurement; gate NOT_PASSED.

### Checked recovered circuit binds the fixed semantic batch

SemanticCircuitBinding packages the existing compiler witnesses without
changing their checker, and composes symbolic_formula_recovered_value with
preselected_semantic_outputs. The actual finite circuit on recovered source
inputs equals semantic residual batching. Its cancellation theorem allows
compiler witnesses, constants and circuit structure to vary with rho while
requiring a fixed semantic list. Circuit evaluation equality is now derived
from the checker and geometry rather than supplied as an assumption.

Source environment agreement is supplied by the prechallenge decoded-family
theorem for a canonical disjoint source tuple. Native transcript/specification
binding, global averaged counts and no-representative integration remain open.
Full check.py passed 3974 registered results with the existing axiom allowlist.
No native code or measured proof size changed; gate remains NOT_PASSED.

### Local, batching and evaluated GKR counts composed

LocalBatchedGKR substitutes the concrete evaluated GKR repair theorem into
the local-prefix continuation split through terminal batching cancellation.
The result has a local accepted-count term, explicit batching/GKR repair terms,
and one residual accepted GKR terminal-mismatch sum over local prefixes and
rho. A second theorem identifies that sum with the chronological joint event
count, including duplicate sample multiplicities. No conditional PCS bound
after fixing rowpoints is introduced.

Wrong-terminal-to-output mismatch and checked-circuit identities are explicit
interfaces supplied by the preceding semantic modules. Concrete transcript
binding, joint PCS substitution, no-representative integration and the final
invalid-trace bound still need assembly.

Full check.py passed 3976 registered results with the existing axiom allowlist.
Native code and byte measurements unchanged; global/PQ soundness and secure
full-NEAR size remain open, and gate remains NOT_PASSED.

### Concrete accepted GKR failure receives merged PCS budget

GKRConcreteErrorInclusion proves lengths from concrete sample membership,
then embeds accepted evaluated-GKR mismatch or absent representative into the
concrete PCS failure event. The numerical theorem invokes the existing merged
near/far bound directly. It retains the absent-representative branch rather
than assuming a decoded source exists. Whole-function recovered-input binding
and acceptance-implies-GKR/PCS checks remain explicit.

The earlier GKR block sequence is fixed for this fiber, while rowpoints remain
jointly sampled. Summation over earlier paths and local-prefix/rho experiments
still needs connection. All original ideal source, unique-regime and terminal
authentication premises remain; native refinement and QROM security are open.

Full check.py passed 3979 registered results with the existing axiom allowlist.
No native code or proof-size measurement changed. Gate remains NOT_PASSED.

### Full GKR path and PCS experiment counts aligned

GKRFullPCSExperiment defines the chronological rows/full-GKR-path/PCS
continuation experiment. Splitting the final GKR block and exchanging finite
sums identifies its event count with the sum of concrete PCS counts over
earlier paths. A per-earlier-path budget lifts with exactly the earlier path
space's multiplicity. The event still receives the original complete path;
no message dependency or rowpoint averaging is removed.

The row-averaged evaluatedGKRExperiment used by the local/batching work is
proved equal to that full experiment and receives the lifted budget. The
multi-table local-prefix coordinate connection and concrete native bindings
remain open, as does final no-representative/invalid-trace assembly.

Full check.py passed 3983 registered results with the existing axiom allowlist.
No native code or byte measurements changed; gate remains NOT_PASSED.

### Two-table local challenges regroup into joint row coordinates

TwoTableLocalCoordinates preserves both complete local prefixes while
regrouping the sequential two-table challenge experiment into initial
mixing/weighting draws and one concatenated uniform rowpoint vector. The
event reconstructs each table path by take/drop. The proof exchanges finite
sums only; later messages retain dependence on every earlier challenge.
A joint rowpoint budget lifts across both initial sample spaces with their
exact multiplicities, without fixing either table rowpoint.

This covers the current two-table literal slice, not arbitrary table counts.
Substituting the GKR/PCS event and proving native metadata/input bindings
still remain, followed by invalid-trace/no-representative assembly.
Full check.py passed 3986 registered results with the existing axiom allowlist.
Native code and byte measurements unchanged; gate remains NOT_PASSED.

### Table history partition and whole recovered input binding

TableHistoryBinding proves that metadata offsets select the actual table
rowpoint segment inside a history with arbitrary suffix. Adjacent two-table
metadata therefore matches the take/drop coordinate partition. For bounded
live source lanes, appending GKR/PCS coordinates leaves the entire recovered
input function unchanged. Concrete PCS sample membership supplies the row
length, so the earlier whole-function input-binding obligation follows when
the PCS constants match the earlier circuit constants.

This replaces an input-function equality premise with explicit lane geometry
and constant-list binding. Native derivation of metadata/constants/formulas
and global invalid-execution count assembly remain open.
Full check.py passed 3990 registered results with the existing axiom allowlist.
Native code and proof sizes unchanged; gate remains NOT_PASSED.

### Two-table batching/GKR/PCS sampling budget composed

TwoTablePCSExperiment combines the prior count identities into one theorem
for sequential local prefixes followed by batching rho, the full evaluated
GKR path and PCS continuation. A concrete PCS budget for each initial-pair,
rho and earlier-path choice lifts with exactly their sampling multiplicities.
All row coordinates remain jointly averaged throughout. The event retains
both complete local prefixes and every continuation value.

The per-choice budget is still an explicit interface to the concrete accepted
GKR failure theorem. Instantiating the full accepted-error event and native
bindings, then assembling invalid-trace/no-representative acceptance, remains.
Full check.py passed 3991 registered results with the existing axiom allowlist.
No native code or proof-size changes; gate remains NOT_PASSED.

### Native local terminal replay binding

The Lean reconstruction adapter now compares compiled mixing and claim values
to the supplied terminal replay record and recomputes the equality-kernel
weight from its tau and rowpoint. Both vectors must have the table row-log
length. Previously weights and claims were checked against supplied batch
values without this independent kernel recomputation in Lean.

LocalTerminalBindingCheck is executable, and its theorem exposes precisely
the checked equalities. Capture generation retains tau, mixing and claim from
the full verified proof replay. This strengthens consistency with a supplied
manifest; it does not authenticate that manifest, formally refine the parser
or prove native transcript derivation or expected AIR generation.

Full check.py passed 3992 registered results with the existing axiom allowlist.
Fresh full-proof replay regenerated the manifest; circuit/AIR artifacts stayed
unchanged. Native suite passed two diagnostic assignments and 32 runtime
rejections, including changed replay mixing, claim, tau and truncated tau.
No secure proof-size claim; gate remains NOT_PASSED.

### Executable terminal binding feeds semantic mismatch and batching

CheckedTerminalSemantics uses the exact localTerminalBindingCheck called by
the native adapter to derive mixing, equality-kernel weight and sent-claim
equalities. A selected compiler table and ordered semantic-list projection
supply semantic membership and residual-formula identity. A wrong local
terminal therefore produces the indexed output mismatch and the existing
tableCount-1 cancellation bound without separately assuming those scalar
equalities.

History-point binding, fixed semantic-list projection, decoded-family source
ownership and checked circuit identity remain separate established interfaces.
Native transcript authentication and binding the residual list to the intended
specification remain open; this does not establish global/PQ soundness.
Full check.py passed 3995 registered results with the existing axiom allowlist.
Native code unchanged since the prior 32-rejection suite; gate NOT_PASSED.

### Invalid later-table bound preserves earlier transcript adaptivity

AdaptiveTableContinuation lifts the actual invalid decoded-trace local bound
after arbitrary earlier transcripts. Sent polynomials and claim strategies
may depend on the entire earlier value, covering the second table's dependence
on the first table protocol. Downstream errors remain one joint total; no
per-earlier-transcript or per-rowpoint PCS estimate is introduced. A count
identity aligns that error sum with the chronological experiment.

Bad-table selection from invalid slice semantics, concrete batching/GKR/PCS
substitution, native bindings and no-representative branch assembly remain.
Full check.py passed 3997 registered results with the existing axiom allowlist.
Native code and proof sizes unchanged; global/PQ soundness remains open and
gate remains NOT_PASSED.

### Wrong execution supplies a residual or bus witness; base-field gap explicit

TableLocalResidualWitness defines the inspected native source residual order:
table constraints followed by interaction multiplicity bit polynomials. Zero
residuals and valid row geometry imply TableLocal. Local failure yields a
fixed nonzero source residual and an indexed combined source/auxiliary
coefficient. The prepared Wasm extraction theorem then gives a contrapositive:
wrong published runCall output implies a local residual or bus imbalance.

Critical boundary: this extraction uses Trace Fp, whereas PCS recovery produces
a generic extension-field decoded trace. The existing forward airExt8Trace
lift does not prove descent of arbitrary recovered source cells. Descent from
base-valued source oracles, or a separate extension-field extraction theorem,
is still required. This gap is explicitly recorded in the feasibility gate.

Full check.py passed 4001 registered results with the existing axiom allowlist.
Native formula generation remains unrefined; no security or size claim changed.
Gate remains NOT_PASSED.

### Base-field polynomial descent and recovered-cell preservation

BaseFieldPolynomialDescent proves a projection argument: a zero-preserving
additive projection commuting with domain scalar multiplication commutes with
polynomial evaluation. If a degree-<D polynomial agrees with projection-fixed
oracle values at at least D distinct points, the polynomial and its projected
coefficient polynomial agree on enough points to force coefficient equality.
This is instantiated with the Fp8 base-coordinate projection, which is Fp-linear
but is not treated as a ring homomorphism on arbitrary extension values.

Base-valued coefficients survive projected-coefficient recovery and inverse
Mobius reconstruction, so recovered source cells descend too. This resolves
the algebraic route conditionally, not the whole execution boundary: the actual
adversarial source oracle must be base-valued on the full domain, and chosen
joint representatives must supply the scalar agreement premise. Honest capture
values and sampled checks alone do not establish those hypotheses.

Full check.py passed 4009 registered results with the existing axiom allowlist.
No native or proof-size change; global/PQ soundness remains open. Gate NOT_PASSED.

### Joint representative descent for typed source oracles

JointSourceBaseDescent uses the actual joint representative lane radius and
agreement partition to supply D scalar agreements for every polynomial in
the same fixed tuple. Typed Fp-valued source functions embedded into Fp8
discharge full-domain base-valuedness; reconstructed source cells are therefore
base-valued. Powers of an embedded base-field root satisfy the domain premise.

Read-only native inspection found that weighted_joint source branches already
use check_opening(first=True): canonical scalar words are embedded with base()
before extension weighting, while folded leaves use a different format. This
is evidence for the typed source model, not formal full-domain authentication.
The inspected native path is Ext4; these descent theorems instantiate Fp8 and
do not implement a new Ext8 profile. Unknown Merkle preimage extraction and
typed-oracle/native refinement remain open, as does matching base-trace assembly.

Full check.py passed 4012 registered results with the existing axiom allowlist.
No native code or proof-size change; gate NOT_PASSED.

### Constructed base trace preserves source AIR and execution witnesses

DecodedBaseTrace projects recovered cells to one base-field trace with the
same row geometry. Base-valuedness is required only within live source
columns. Bounded expressions evaluate identically after embedding, including
current and cyclic-next reads. Zero source residuals therefore imply actual
TableLocal on this constructed trace, and nonzero residuals transport back
to the recovered extension trace. The prepared wrong-output theorem now yields
an extension-trace source residual or a bus imbalance on the constructed
base trace. Auxiliary cells outside source width remain unrestricted.

Joint-source descent can supply source base-valuedness once authenticated
typed-oracle binding is established. Auxiliary/bus alignment and the final
concrete acceptance theorem still need composition; native/QROM security and
secure full-NEAR size remain open.
Full check.py passed 4017 registered results with the existing axiom allowlist.
No native or measured-size changes; gate NOT_PASSED.

### Decoded coordinates connect to adaptive bus soundness

DecodedAdaptiveBus proves that a decoded coordinate trace with fixed source
cells and logs projects to an allowed auxiliary attachment on that source.
Validity of reconstructed auxiliary residuals and claimed final-product
equality therefore imply the existing adaptive bus acceptance event. The
resulting ideal bus bound permits a different decoded auxiliary witness and
final products for every alpha/gamma pair.

Source cells must still be fixed before those challenges; consistency of
source representatives across later auxiliary commitments remains open.
Auxiliary residual validity is explicit on reconstructed coordinates, not
inferred from PCS agreement. Actual generated-formula refinement, global
acceptance composition, authentication and QROM security remain open.
Full check.py passed 4020 registered results with the existing axiom allowlist.
No native/size changes; gate NOT_PASSED.

### Source lane consistency across auxiliary choices

SourceAcrossAuxiliary proves coefficientwise equality preserves every
recovered column row. Two joint tuples sharing a selected source oracle
therefore recover the same source lane under unique-decoding separation,
even if their other oracles, including auxiliary commitments, differ. A
noncomputable selection theorem chooses one decoded column family valid for
all eligible auxiliary choices under the same fixed source proximity bounds.
No candidate is required for every choice; absent-representative cases remain
separate. This is ideal-model choice, not extraction from unknown hashes.

Assembling fixed lanes into the base source trace and substituting them into
the adaptive bus bound remain, together with native authentication, formula
refinement, global counts and QROM security.
Full check.py passed 4023 registered results with the existing axiom allowlist.
No native/size changes; gate NOT_PASSED.

### One base source trace for all eligible auxiliary choices

FixedDecodedSourceTrace assembles scalar source uniqueness, base descent and
cell provenance into a single base-field trace shared by every eligible
decoded auxiliary choice. Fixed row logs and live source-column equality are
derived; auxiliary cells are unrestricted. No eligible choice is required to
exist, and absent-representative choices remain a separate failure branch.
The trace can be used directly by the decoded adaptive-bus family theorem.

Instantiation of scalar proximity and provenance from concrete metadata and
joint tuples remains, as do auxiliary residual/native authentication bindings
and global/PQ soundness. Selection remains ideal-model classical choice.
Full check.py passed 4025 registered results with the existing axiom allowlist.
No native/size changes; gate NOT_PASSED.

### Fixed source trace instantiated from joint representatives

FixedJointSourceTrace derives candidate degree bounds and per-lane scalar
proximity directly from JointBetaRepresentative and its lane-radius theorem.
Bounded lane indices connect those candidates to decoded-cell provenance.
The existing uniqueness/descent construction then yields one base source
trace across all eligible auxiliary choices, rather than assuming independent
scalar closeness premises. Source-oracle equality, row logs and cell provenance
remain explicit, and absent-representative choices remain outside eligibility.

Concrete metadata indexing/authentication and auxiliary formula refinement
still need substitution before global acceptance soundness.
Full check.py passed 4026 registered results with the existing axiom allowlist.
No native/size changes; global/PQ security remains open, gate NOT_PASSED.

### Metadata-fixed source indices and indexed decoded provenance

IndexedDecodedProvenance derives a unique live source-lane index from
canonical metadata coverage and all-support disjointness. This choice
precedes the polynomial tuple. Existential zipped lane/polynomial membership
then identifies the polynomial at that fixed index, converting preselected
decoded-family provenance into the exact indexed cell equality used by
fixed_joint_representative_source_trace. Empty-support lanes are not assumed
globally unique.

The index-family assembly, native metadata authentication and auxiliary
formula/global soundness connections remain open.
Full check.py passed 4030 registered results with the existing axiom allowlist.
No native/size changes; QROM security remains open, gate NOT_PASSED.

### Metadata index family composed with fixed source trace

`metadata_source_index_family` now chooses all live source-column indices from
metadata before polynomial tuples or auxiliary strategies are supplied.
`metadata_joint_fixed_source_trace` uses that family and existential decoded
provenance to instantiate `fixed_joint_representative_source_trace`. The caller
no longer supplies indices or an indexed provenance equality. Empty source
widths impose no membership requirement; live lanes retain unique indices.

Validation: full `check.py` PASS (4032 registered results); existing axiom
allowlist. Native captures were not rerun for this formal-only composition.
This does not establish authenticated typed source oracles, representative
existence from actual verifier acceptance, native auxiliary formula refinement,
QROM soundness or secure sub-300 KB size. The slice gate stays NOT_PASSED.
Next: instantiate the slice table enumeration and combine this common source
with bus/local/GKR failure accounting in one acceptance theorem.

### Prepared decoded bus continuation branch

`prepared_decoded_bus_continuation_bound` connects the wrong actual prepared
Wasm output theorem to decoded bus witnesses over the whole chronological
bus-pair × continuation experiment. Under local validity of one fixed source,
accepted count is at most the existing bus error budget times sample length
and continuation length, plus the count of accepted downstream failures.
Witnesses/finals may depend on the entire transcript. The error event is
retained explicitly; no per-rowpoint PCS estimate is assumed.

This is the locally valid source branch only. Source binding and reconstructed
bus residual validity must be supplied outside the retained error event. The
next composition must handle an invalid fixed source and bound the downstream
failure event using the local/GKR/PCS results. Native authentication, QROM,
secure size and full NEAR scope remain open; gate remains NOT_PASSED.

Validation: full `check.py` PASS (4034 registered results), existing axiom
allowlist; native captures not rerun for this formal-only change.

### Earlier-dependent decoded auxiliary tables

Inspection found that `decoded_invalid_table_after_earlier_budget` held the
whole decoded table fixed, which was too restrictive for bus-challenge-dependent
auxiliary columns. Added `decoded_adaptive_table_after_earlier_budget`: decoded
cells, auxiliary formulas and residual entries may depend on the earlier
transcript, with uniform auxiliary length/degree. It applies the actual local
bound in each fiber and retains one joint PCS error budget, without assuming
small per-fiber PCS error. Nonzero row/lane remains an explicit premise.

`fixed_source_decoded_expression` and `fixed_source_decoded_nonzero` establish
that arbitrary decoded auxiliary changes preserve bounded source-expression
values and nonzero witnesses when live source cells and logs are fixed.
Next: select the combined residual index, instantiate the adaptive local bound,
and join it to the bus branch and actual GKR/PCS error accounting. These are
formal interface connections, not native or QROM certification.

Validation: full `check.py` PASS (4037 registered results), existing axiom
allowlist; native captures not rerun for this formal-only change. Gate remains
NOT_PASSED; secure sub-300 KB and full 1 Pgas scope remain open.

### Fixed invalid source instantiates adaptive local budget

`FixedSourceLocalBudget.lean` proves exact selected-table expression semantics,
selects a nonzero row/source-residual index from failed base `TableLocal`, and
transports that same index across all earlier-dependent decoded auxiliary
attachments. `fixed_source_invalid_local_budget` invokes the actual adaptive
local bound with this derived witness. Appended auxiliary residuals cannot
change the source index. Cyclic next rows and selectors are preserved.

The caller no longer supplies a nonzero combined row/lane premise. It still
supplies source binding, residual order/degrees, local checks, terminal-repair
and joint PCS error budgets. Next: select the invalid table in the full slice,
align its sample space and substitute actual GKR/PCS budgets, then combine
with the locally valid bus branch. Native/QROM and secure-size gates remain
open, as does the full 1 Pgas objective.

Validation: full `check.py` PASS (4040 registered results), existing axiom
allowlist. Native captures not rerun for this formal-only composition.

### Second-table invalid source / joint PCS experiment composition

`second_table_fixed_source_pcs_budget` invokes the fixed-source local theorem
with the full first-table prefix as earlier randomness and actual
`twoTablePCSContinuations` as downstream randomness. Its total error sum is
derived using `earlier_local_error_count` and `two_table_gkr_pcs_joint_budget`.
Both rowpoint vectors remain jointly sampled, with exact initial challenge,
batching and earlier GKR path multiplicities. No fixed-rowpoint PCS estimate
is introduced.

The concrete PCS event bound and wrong-terminal repair still require
instantiation; they are not cryptographic conclusions of this wrapper.
Earlier bus challenges are fixed outside this theorem. Next: corresponding
first-table branch (second local protocol is part of its continuation), then
actual repair/event substitution, table selection and bus averaging.

Validation: full `check.py` PASS (4041 registered results), existing axiom
allowlist. Native captures not rerun for formal-only composition. Full NEAR,
QROM and secure sub-300 KB gates remain open.

### First-table invalid source / joint PCS experiment composition

`firstTablePCSContinuations` retains the complete second local protocol before
batching/GKR/PCS randomness. `first_table_fixed_source_pcs_budget` derives its
nonzero residual from fixed-source `TableLocal` failure, invokes the actual
local continuation bound, and discharges the total error sum with the joint
two-table PCS lift. Both invalid-table branches now use the same chronological
two-table experiment; no conditional fixed-rowpoint PCS bound is introduced.

Wrong-terminal repair and the concrete PCS event bound remain explicit. Next:
instantiate repair from checked semantics/evaluated GKR and the event bound
from `concrete_gkr_accepted_failure_budget`, including absent representatives;
then select the invalid table and combine/average with the bus branch.
Earlier bus challenges remain fixed outside this theorem. No native/QROM or
secure-size certification is implied.

Validation: full `check.py` PASS (4042 registered results), existing axiom
allowlist. Native captures not rerun for formal-only composition. The full
1 Pgas objective and secure sub-300 KB feasibility remain open.

### Evaluated GKR terminal repair over two-table continuations

`two_table_terminal_repair` invokes batching cancellation and evaluated GKR
soundness for each future local prefix, then sums them while retaining one
accepted-terminal-error event count. It uses actual `twoTablePCSContinuations`
and an explicit equality aligning GKR rounds. Repair is the future-prefix
count times the concrete batching/GKR terms; there is no per-rowpoint PCS
budget. The event may additionally include absent representatives.

The semantic output vector must be fixed before rho, with a mismatch and
finite-circuit binding. Accepted GKR checks and error-event inclusion remain
explicit. Next: specialize the future family to second-local prefixes or a
singleton, substitute this repair into the table branches, and instantiate
semantic binding plus the concrete PCS failure theorem. Native/QROM, secure
size and full 1 Pgas execution remain open.

Validation: full `check.py` PASS (4043 registered results), existing axiom
allowlist; native captures not rerun for this formal-only composition.

### Second-table evaluated GKR repair substituted

`second_table_evaluated_gkr_pcs_budget` invokes the prior second-table
fixed-source/PCS bound and discharges terminal repair via the singleton
specialization of `two_table_terminal_repair`. No free repair amount or
wrong-terminal numerical inequality remains. The conclusion contains the
actual batching/GKR terms and joint PCS sample multiplicities.

Semantic mismatch, whole circuit binding, accepted GKR checks, event inclusion
and the concrete PCS event bound remain explicit. Next: corresponding
first-table substitution, checked semantic bindings and actual concrete PCS
budget, then table selection/bus averaging. Native/QROM, secure size and the
full 1 Pgas objective remain open.

Validation: full `check.py` PASS (4044 registered results), existing axiom
allowlist; native captures not rerun for this formal-only composition.

### First-table evaluated GKR repair substituted

`first_table_evaluated_gkr_pcs_budget` instantiates the first-table local/PCS
bound with the actual repair theorem over all second-table local prefixes.
Both invalid-table branches now derive the numerical repair term rather than
assuming it. The first branch pays the exact second-prefix multiplicity;
accepted terminal errors remain jointly counted over both rowpoint vectors.

Semantic output mismatch/binding, root geometry, accepted verifier checks and
concrete joint PCS error bound remain explicit. Next: checked semantic
instantiation and concrete PCS event/budget, followed by table-selection/bus
composition and earlier bus averaging. No native/QROM or secure-size claim.
Full 1 Pgas remains the objective.

Validation: full `check.py` PASS (4045 registered results), existing axiom
allowlist; native captures not rerun for this formal-only composition.

### Checked terminal/compiler semantics feed GKR repair

`checked_terminal_gkr_repair` composes `checked_local_terminal_mismatch`,
`checked_semantic_circuit_value` and the actual evaluated-GKR repair theorem.
The caller supplies executable checker results rather than an assumed output
mismatch or finite-circuit evaluation equality. Compiler witnesses may vary
with rho while their semantic projection stays fixed. The circuit inputs are
the actual recovered-input function and layers are the witness's stored gates.

Decoded-environment agreement, metadata/history/formula binding, checked
geometry and placement, root geometry/accepted GKR checks and error inclusion
remain explicit. Next: instantiate this across both local-table families,
substitute the concrete PCS event bound, and join/average the source-local and
bus branches. Native/QROM, secure-size and full 1 Pgas requirements remain open.

Validation: full `check.py` PASS (4046 registered results), existing axiom
allowlist; native captures not rerun for this formal-only composition.

### Actual merged PCS bound over the complete two-table experiment

`two_table_concrete_pcs_failure_budget` invokes the actual
`concrete_gkr_accepted_failure_budget` in each initial-challenge/batching/earlier
GKR context, then the two-table joint lift. It derives max(nearBudget,farBudget)
with exact outer multiplicities, including accepted absence of a joint source
representative. No numeric PCS fiber budget is supplied. Source oracles remain
fixed across the contexts; both rowpoint vectors are still jointly sampled.

Ideal source projection/geometry, root/fold conditions, initial weighted
oracle equality, terminal authentication, whole recovered-input binding,
accepted verifier checks and event inclusion remain explicit. Next: substitute
this same-event bound in table branches, handle absent representatives and
join table selection/bus averaging. Native commitment/QROM refinement, secure
size and full 1 Pgas remain open.

Validation: full `check.py` PASS (4047 registered results), existing axiom
allowlist; native captures not rerun for this formal-only composition.

### Fixed-source local/bus branch composition

`prepared_fixed_source_branch_budget` selects the branch from one fixed base
source before challenges. If all source tables are locally valid it invokes
the actual prepared wrong-output bus continuation theorem. Otherwise it selects
one failed table from the actual two-table AIR. The resulting bound is the
maximum of the two local budgets and the scaled bus budget, plus a shared
accepted-downstream-failure budget once. It does not union-bound both table
branches or duplicate the PCS error.

The local and joint-error premises explicitly cover the full bus-pair ×
continuation experiment; no fixed-bus bound is silently substituted. Next:
average existing local/GKR/PCS results across earlier bus choices, supply the
same-event witnesses and fixed source, then native/QROM refinement. Secure
size and full 1 Pgas scope remain open. This is conditional composition, not
an end-to-end verifier-acceptance theorem.

Validation: full `check.py` PASS (4048 registered results), existing axiom
allowlist; native captures not rerun for this formal-only composition.

### Audit correction: locally valid source can have invalid bus auxiliaries

Before bus averaging, inspection identified a missing event inclusion:
source `TableLocal` does not imply valid reconstructed bus auxiliary
residuals. The existing branch theorem is correct conditionally, but its
accepted-outside-failure witness premise cannot be discharged by PCS checks
alone. Local/GKR acceptance errors for invalid auxiliaries must also be
included and budgeted. The shared failure must not be mislabeled PCS-only.

Added `decoded_adaptive_witness_after_earlier_budget`, allowing the violated
row/index to vary with earlier bus transcripts. Added
`decoded_adaptive_invalid_rows_budget`, which derives those indices from
failure of complete combined-residual validity. Selection precedes the
selected table's local randomness; the downstream PCS error remains a joint
sum. This supports the missing invalid-auxiliary branch without falsely
assuming one source-residual witness exists in that branch.

Next: bind reconstructed bus auxiliary residuals to the generated combined
formula list, select the invalid table before local challenges, and include
its local/GKR budget in the bus-witness failure event before averaging. No
previous conditional theorem is claimed to prove this premise. Full 1 Pgas,
QROM and secure-size feasibility remain open.

Validation: full `check.py` PASS (4050 registered results), existing axiom
allowlist; native captures not rerun for this formal-only change.

### Generated bus auxiliary failure witness

`BusResidualFailureWitness.lean` reconstructs the recursive Ext8 bus residual
predicate from source checks and all generated `busTableResiduals` equalities.
Its contrapositive selects an actual table, row and generated auxiliary
formula with nonzero value. `auxiliary_nonzero_combined_index` places that
violation in the exact combined source-plus-auxiliary local residual list.
Offsets and table membership are retained, rather than assumed bad indices.

The evaluated trace here is `airAuxCoordinateTrace raw sourceWidth`. It is
not automatically the decoded PCS coordinate trace. Next: prove coordinate
formula reconstruction/refinement before feeding this violation to the local
bound, include local/GKR failures in bus witness failure, and average the
same full event. Native generator refinement, QROM, secure size and full
1 Pgas execution remain open.

Validation: full `check.py` PASS (4053 registered results), existing axiom
allowlist; native captures not rerun for this formal-only change.

### Ext8 coordinate formula lowering

`BusCoordinateFormulaLowering.lean` defines `lowerBusCoordinates`, retaining
source indices and replacing each logical auxiliary read with an eight-term
certified-basis linear combination. It proves value preservation for arbitrary
environments and exact reconstructed row semantics, including cyclic next
rows/selectors. The lowering does not increase `busFormulaDegree`.

`decoded_bus_coordinate_lowering` transports this equality to decoded PCS
coordinates under explicit base-valued coordinate cells. This requires more
than source-only descent; live auxiliary coordinate typing must be supplied
from the typed joint representative or the premise narrowed by formula bounds.
The native generator has not yet been proved to emit this AST. Next: live
coordinate typing/native formula refinement, violation transport, and complete
local/GKR/PCS/bus event composition. QROM, secure size and full 1 Pgas remain open.

Validation: full `check.py` PASS (4062 registered results), existing axiom
allowlist; native captures not rerun for this formal-only change.

### Bounded coordinate typing and auxiliary violation transport

`BoundedBusCoordinateTyping.lean` adds formula read bounds and proves base
projection/value transport using only those columns of the selected table,
including next-row references. `typed_joint_bus_coordinate_lowering` invokes
typed joint representative descent to discharge base typing for source and
auxiliary coordinate lanes with recovered-column provenance.
`lowered_auxiliary_failure_index` transfers a reconstructed auxiliary failure
to a nonzero combined residual on the decoded PCS trace, for the exact
coordinate-lowered formula list. Unreferenced cells need no typing premise.

Remaining: actual generated-formula read bounds/coordinate provenance,
native generator equivalence and authenticated typed oracles; then adaptive
invalid-auxiliary acceptance and complete event averaging. QROM, secure size
and full 1 Pgas scope remain open.

Validation: full `check.py` PASS (4066 registered results), existing axiom
allowlist; native captures not rerun for this formal-only change.

### Coordinate coverage and precompiler metadata typing

`BusCoordinateCoverage.lean` derives physical read coverage
`sourceWidth+8*auxCount` from the logical formula bound. Zipped polynomial
provenance yields typed joint base descent without distinct-lane/index
assumptions. `metadata_typed_coordinate_formula` composes that with the exact
precompiler decoded-column provenance interface, removing an independently
supplied per-coordinate typing premise.

Read-only native inspection confirms `check_bus_program_formulas.py:28` and
`heterogeneous_bus_whir.py:102` use four-coordinate Ext4 reconstruction, not
Ext8. Native accumulation is left-associated coordinate*basis; formal lowering
is right-associated basis*coordinate. Algebraic equivalence/native generator
refinement has not been inferred from a superficial structural resemblance.
Next: native-style accumulation equivalence, generated logical-formula bounds
and an actual Ext8 profile/generator path, alongside event composition. Full
1 Pgas, QROM and secure-size feasibility remain open.

Validation: full `check.py` PASS (4071 registered results), existing axiom
allowlist; native captures not rerun for formal-only changes.

### Native-style Ext8 accumulation semantics

`NativeStyleCoordinateAccumulation.lean` models zero-initialized left-fold
coordinate*basis accumulation and proves equality with the existing
right-associated basis*coordinate lowering for arbitrary environments.
The equality extends to complete formulas; degree and physical read bounds
are preserved. This resolves the association/operand-order difference without
assuming syntactic AST equality or honest-only evaluations.

This remains an Ext8 candidate AST model. The inspected native slice path is
Ext4; existing standalone Ext8 arithmetic/PCS prototypes do not by themselves
supply a full native Ext8 slice generator/profile. Next: generated logical
formula refinement and actual native Ext8 validation, alongside auxiliary
failure/event composition. QROM, secure size and full 1 Pgas remain open.

Validation: full `check.py` PASS (4077 registered results), existing axiom
allowlist; native captures not rerun for this formal-only change.

### Executable Ext8 auxiliary formula candidate

Parameterized `check_bus_program_formulas.expected`/source-expression lowering
with explicit arithmetic and derived coordinate degree; default Ext4 behavior
is retained. `validate_formula` supports an explicit coordinate degree while
retaining its default four-word ABI. Ext8 tests use the existing certified-layout
arithmetic adapter and an independent direct row evaluator with tuple-slice
reconstruction, rather than evaluating a second copy of the generated AST.

Validation: 24 Ext8 cases covering 0/1/2/4 multiplicity bits, zero/random bus
challenges, arbitrary selectors and coordinate values; 192 residual value
comparisons and 576 rejected opcode/literal/column mutations. 40 exact default
Ext4 formula/layout comparisons against commit `59c3833bd`'s generator passed
(using deterministic synthetic arithmetic inputs). Full `check.py` PASS
(4077 registered formal results); no Lean theorem changed.

This is executable formula generation/register validation, not a full Ext8
native GKR/prover capture or a universal Python-to-Lean refinement theorem.
Next: generated-formula/certificate binding to Lean, full Ext8 slice profile
integration and remaining event composition. QROM, secure sub-300 KB and full
1 Pgas execution remain open.

### Executable Lean checking of Ext8 formula certificates

Added `CheckExt8BusFormulas.lean`, using canonical eight-coordinate constants,
eleven-word instruction parsing, existing `busFormulaCheck` and
`terminalAcyclicCheck`, plus independent comparisons of formula evaluation and
`terminalProgramRun` against captured expected values. Python exports eight
representative zero/random cases (64 residual programs) from the Ext8 generator
and its independent evaluator. The retained capture is 188987 bytes; this is
a diagnostic certificate fixture, not a compressed state-transition proof.

Validation: all eight cases/64 residuals accepted; ten runtime rejections for
bad roots/opcodes, truncated instructions/selectors, noncanonical constants or
coordinates, altered expected values, cyclic root and empty fixture/residual
lists. The Python generator suite still passes 24 cases/192 value comparisons
and 576 mutations. The Lean runner and tests are registered in scope inventory.

The existing proved formula-check semantics applies to accepted routes and
acyclic programs, but supplied formula lists are still not authenticated as
the universal intended bus specification. Next: bind generated formulas to
Lean's bus specification (including challenge-dependent constants), then
full Ext8 slice integration and acceptance-event composition. Native commitment
and QROM soundness, secure size and full 1 Pgas remain open.

Full `check.py` PASS (4077 registered formal results), existing axiom allowlist.

### Ext8 certificate formulas bound to the formal bus specification

`GeneratedExt8BusSpecCheck.lean` compares the complete ordered formula list to
`busTableResiduals` followed by native-style Ext8 lowering. Its soundness theorem
transports accepted formula values to the formal reconstructed environment
for all environments. `CheckExt8BusFormulas` now parses source interactions,
public values, challenges and finals; reconstructs this specification; checks
final count and physical width; and rejects any formula-list disagreement
before checking routes. The Ext8 Python candidate emits the exact formal
Horner message AST. Default Ext4 generation remains unchanged.

All 8 cases/64 residuals pass; 16 runtime rejection cases include a coherent
wrong formula+program+expected-value substitution, changed live bus ID,
challenge/final, omission and reorder. A test changing an empty-multiplicity
interaction's bus ID was correctly inert; it was corrected to target a live
interaction. Forty exact default Ext4 comparisons pass. Full `check.py` PASS
(4078 registered results), existing axiom allowlist.

The certificate is now bound to the supplied formal bus specification, not
merely to itself. Supplied statement/table/challenge authentication and full
Ext8 prover integration are still separate. Next: integrate checks with
slice/compiler artifacts and finish auxiliary/local/GKR/PCS/bus composition.
QROM, secure size and full 1 Pgas remain open.

### Checked formula lists connected to bus validity

`CheckedBusResidualTransport.lean` connects the executable specification
checker to the failure analysis. `checked_bus_decoded_row_values` transports
actual checked formula-list values to reconstructed bus residuals under bounded
coordinate typing. `checked_bus_failure_combined_index` derives a nonzero
combined local residual from a formal bus violation in that checked list.
`checked_bus_rows_zero` and `checked_bus_tables_residuals_zero` prove the reverse
zero-validity implication, producing the exact recursive predicate consumed by
the fixed-source bus acceptance theorem.

Source constraints/interaction bounds, table widths, coordinate typing and
consistent public/challenge/final inputs remain explicit. Next: discharge the
bus witness premise outside the full local/GKR/PCS failure event, compose
adaptive auxiliary-invalid budgets and average bus randomness, then integrate
authenticated Ext8 slice inputs. QROM, secure size and full 1 Pgas remain open.

Validation: full `check.py` PASS (4082 registered results), existing axiom
allowlist; native captures not rerun for this formal-only composition.

### Checked bus failure selects a decoded local witness

`CheckedBusFailureSelection.lean` derives the table/row/lane witness from
failed reconstructed bus validity, using the actual checked formula lists.
The row is below the selected table height and the residual count is positive.
A separate restriction lemma preserves the whole combined residual vector,
including cyclic next-row reads and boundary selectors.

Source checks, matching widths, exact specification checks and bounded base
coordinate typing remain premises. Witness existence does not itself prove
chronology: the subsequent adaptive application must fix its trace/formula
inputs before local challenges. Next: use this selection across earlier bus
transcripts and compose the invalid-auxiliary local/GKR/PCS budget. The slice
gate remains NOT_PASSED; native Ext8 integration, QROM, secure size and full
1 Pgas are still open.

Validation: full `check.py` PASS (4084 registered results), existing axiom
allowlist. Native captures were not rerun for this formal-only change.

### Checked auxiliary failures enter the adaptive local bound

`checked_auxiliary_after_earlier_budget` connects invalid generated bus
residuals to `decoded_adaptive_invalid_rows_budget` through exact formula
checks and bounded coordinate typing. No row/lane witness or decoded-row
invalidity premise is supplied by the caller. Trace/formula data and violated
rows may vary with earlier history; the selected table and its geometry are
fixed on the supplied history family. Terminal repair and aggregate downstream
error bounds remain explicit.

Composition findings: split earlier histories by selected invalid table before
combining bounds. Auxiliary validity can vary with bus challenges, so the
fixed-source branch maximum cannot simply be reused between auxiliary-invalid
and bus-bad histories. Use disjoint counts, charging shared PCS failures once.
Also derive earlier-only auxiliary representatives from authenticated
commitments: the new theorem requires that chronology, it does not prove it.
These are the next integration obligations, alongside substituting actual
checked GKR repair and concrete PCS bounds.

Validation: full `check.py` PASS (4085 registered results), existing axiom
allowlist. No native captures rerun for this formal-only change. The gate stays
NOT_PASSED; full native Ext8 slice, QROM, secure size and full 1 Pgas remain open.

### Disjoint history branches composed with prepared-Wasm bus soundness

`HistoryBranchBudget.lean` proves exact three-way count identities for
acceptance and shared downstream failures. An earlier-only `Option Bool`
selector identifies valid auxiliaries or either invalid table. The budget
composition pays the shared failure count once across these disjoint branches.

`prepared_history_branch_budget` applies the actual prepared-Wasm bus theorem
to the valid-auxiliary branch and adds the two restricted invalid-table bounds.
The resulting source-valid bound is bus budget + local0 + local1 + joint PCS
budget, not an unjustified maximum over bus-dependent branches. The existing
fixed-source branch theorem is unchanged and remains conditional as documented.

Remaining premises are substantial: derive the selector from earlier committed
auxiliary traces; establish decoded witnesses on its valid branch; instantiate
both restricted local budgets with the checked auxiliary/local/GKR/PCS chain;
normalize their chronological experiments; then combine source-invalid cases.
This theorem does not derive authenticated commitment chronology or native
verifier acceptance. Ext8 execution, QROM, secure size and full 1 Pgas remain
open, and the slice gate remains NOT_PASSED.

Validation: full `check.py` PASS (4088 registered results), existing axiom
allowlist; native captures not rerun for formal-only composition.

### Earlier fixed auxiliary coordinates and residual transport

`HistoryFixedCoordinates.lean` applies joint representative uniqueness to all
covered physical coordinates, separately for each earlier history. Typed ideal
oracles can vary with the earlier history but are fixed across later local,
GKR and PCS continuations. All eligible later decoded witnesses agree with one
base trace; empty eligible fibers are supported by the existing construction.

`fixed_coordinate_bus_formula` preserves bounded bus formula evaluation,
including next-row wraparound, selectors and Ext8 constants.
`fixed_coordinate_combined_residuals` preserves the full ordered local vector.
Thus representative choices after local challenges cannot alter residual
validity under these ideal-oracle premises. Formula lists/public/challenge/final
inputs must also be bound earlier; this theorem does not establish that binding.

Next: define the two-table selector on these fixed residual vectors and connect
its branches to the checked auxiliary and prepared history budgets. Native
commitment extraction and coordinate provenance remain separate obligations;
no claim of end-to-end chronology, QROM or secure size. Full 1 Pgas stays open.

Validation: full `check.py` PASS (4091 registered results), existing axiom
allowlist. Native captures not rerun for this formal-only composition.

### Two-table auxiliary selector with decoded branch meaning

`TwoTableAuxiliaryBranch.lean` defines an analytical selector on the earlier
fixed trace's actual auxiliary formula lists. It prefers invalid table 0,
otherwise invalid table 1, and returns none iff both tables vanish on every
live row. This is a noncomputable proof construction, not an executable prover.

A selected branch transports to a nonzero combined local residual, with a
bounded row and positive residual count, in every decoded continuation sharing
the covered fixed coordinates. The none branch, exact formula specification
checks and source checks imply the recursive reconstructed bus-validity
predicate for exactly two tables. This supplies the semantic meaning previously
left abstract in the disjoint branch composition.

Next: instantiate prepared history budgets with this selector and substitute
the selected-table local/GKR/PCS bounds in the common chronological experiment.
Earlier binding of formulas/finals and authenticated fixed typed coordinate
oracles remains necessary. Native Ext8 integration, global acceptance, QROM,
secure size and full 1 Pgas remain open; gate remains NOT_PASSED.

Validation: full `check.py` PASS (4095 registered results), existing axiom
allowlist. No native captures rerun for formal-only composition.

### Concrete checked selector enters prepared acceptance budget

`prepared_checked_history_budget` instantiates the history partition with
`twoTableAuxiliaryBranch` on earlier fixed traces and formula lists. Accepted
witnesses supply source/coordinate binding and equal claimed final products;
bus residual validity is derived on the none branch from exact formula checks.
`table_local_all_constraints_zero` derives explicit and multiplicity-bit source
residual validity directly from TableLocal, removing a redundant premise.

The result preserves bus + local0 + local1 + joint failure scaling and counts
the shared downstream failure once. The actual restricted local budgets and
PCS budget still need substitution, and the accepted decoded bindings/final
equality still need native-verifier derivation. Source-invalid cases remain
separate. This is conditional composition, not full acceptance certification.

Next: instantiate selected-table local/GKR/PCS bounds on these precise branch
experiments. Native Ext8 execution, QROM, secure envelope size and full 1 Pgas
remain open; slice gate remains NOT_PASSED.

Validation: full `check.py` PASS (4097 registered results), existing axiom
allowlist. Native captures not rerun for this formal-only change.

### Selected auxiliary local bound with evaluated GKR repair

`selected_auxiliary_local_error_count` uses the actual auxiliary selector to
derive local invalidity and invokes adaptive local soundness. Its downstream
term is the exact accepted shared-failure count over the chronological
experiment, avoiding an independent PCS budget per branch or history.

`selected_auxiliary_gkr_error_count` substitutes the actual batching/evaluated
GKR repair theorem for the last-local-table case. Semantic output mismatch,
circuit binding, verifier checks and shared-error inclusion remain explicit;
there is no assumed numeric repair term. The first-table case still needs the
second local protocol included as future randomness.

Next: extend over later local prefixes, normalize both branch experiments to
the prepared continuation, then apply concrete joint PCS once. Native bindings,
checked terminal semantic instantiation, full Ext8, QROM, secure size and full
1 Pgas remain open. The slice gate remains NOT_PASSED.

Validation: full `check.py` PASS (4099 registered results), existing axiom
allowlist. Native captures not rerun for formal-only composition.

### First-table future GKR and common chronological counts

`selected_auxiliary_future_gkr_error_count` extends selected-table local/GKR
composition over arbitrary future prefixes. Instantiating these with second
local prefixes covers the first-table continuation; outputs and GKR strategy
may depend on those future prefixes, while the selected local trace/formulas
remain earlier-indexed. Actual evaluated-GKR repair is substituted and the
accepted shared-failure count remains exact.

`SelectedHistoryExperiment.lean` proves selector-filter count equality and
reindexes both first-table future nesting and second-table earlier nesting to
the common history/first/second/PCS experiment. These identities preserve list
multiplicities and apply to arbitrary events, including accepted failures.

Next: substitute both selected branch bounds into the concrete prepared history
theorem, then apply the concrete joint PCS budget once. Semantic GKR checks,
authenticated native bindings, full Ext8, QROM, secure size and full 1 Pgas
remain open. Slice gate remains NOT_PASSED.

Validation: full `check.py` PASS (4103 registered results), existing axiom
allowlist; native captures not rerun for formal-only changes.

### Filtered table bounds transfer to shared branch counts

`SelectedBranchTransfer.lean` combines the earlier selector filter and
chronological reindexing into direct equalities for each table's actual nested
experiment. `two_table_filtered_history_budget` consumes those differently
nested bounds, converts their accepted-failure counts to the shared branch
experiment, and applies the disjoint three-branch budget exactly once.

This is a count-composition result. It does not manufacture numerical bounds:
the bus, first/second local/GKR and joint PCS estimates remain inputs. Their
existing theorem outputs now have explicit transfer interfaces to the shared
experiment, including retained accepted errors, without inferring per-history
budgets from aggregate bounds.

Next: instantiate these interfaces with the actual prepared-Wasm and selected
local/GKR data, then concrete joint PCS. Checked terminal/native binding,
full Ext8, global acceptance, QROM, secure size and full 1 Pgas remain open.
Slice gate remains NOT_PASSED.

Validation: full `check.py` PASS (4106 registered results), existing axiom
allowlist; native captures not rerun for formal-only count composition.

### Both numerical selected local/GKR budgets derived in one composition

`SelectedGKREvidence.lean` packages the existing last-local and future-local
semantic hypotheses into Lean records. These contain geometry, binding,
verifier checks and mismatch/error-inclusion proofs; neither record contains
an acceptance inequality or numeric repair budget. Evidence-bound theorems
invoke the existing selected local/GKR soundness proofs and compute the local
budget from geometry.

`two_table_selected_gkr_composition` invokes both evidence-bound theorems on
their filtered, differently nested experiments and transfers the results to
the common history/first/second/PCS count. This removes the two independent
numerical local-budget premises from this composition. Valid-auxiliary bus
and shared accepted-failure estimates remain inputs, paid once as documented.

Next: instantiate bus with prepared-Wasm checked results and shared failure
with concrete PCS, and construct semantic evidence from checked terminal and
native artifacts. These records are mathematical proof data, not native
certificates. Full Ext8, global acceptance, QROM, secure size and full 1 Pgas
remain open; slice gate remains NOT_PASSED.

Validation: full `check.py` PASS (4109 registered results), existing axiom
allowlist. Native captures not rerun for formal-only composition.

### Prepared-Wasm bus and both selected local/GKR terms derived

`prepared_selected_gkr_budget` instantiates the checked prepared-Wasm theorem
with the full two-local/GKR/PCS continuation and computes both local budgets
from semantic evidence. Exact first/second branch-count transfers discharge
its invalid-branch inequality premises. The actual prepared-Wasm bus theorem
supplies the bus term. Only one shared accepted downstream-failure estimate
remains a numerical error premise.

This is the locally valid fixed-source branch. Source/coordinate binding,
checked formulas/finals, semantic local/GKR evidence and native authentication
remain explicit. The theorem does not yet discharge its shared error count
using concrete PCS or include fixed-source-invalid cases.

Next: lift `two_table_concrete_pcs_failure_budget` across earlier bus pairs,
where source oracles may vary with the pair but are fixed across local draws,
and supply the matching accepted-failure event inclusion. Full native Ext8,
global acceptance, QROM, secure size and full 1 Pgas remain open; slice gate
remains NOT_PASSED.

Validation: full `check.py` PASS (4110 registered results), existing axiom
allowlist. Native captures not rerun for formal-only composition.

### Source-valid prepared branch: all numerical terms derived

`ConcretePCSEvidence.lean` packages the existing concrete PCS hypotheses and
invokes `two_table_concrete_pcs_failure_budget`; it contains no numerical
failure inequality. `HistoryConcretePCS.lean` lifts that theorem over earlier
histories. Each history may choose its own source oracles and strategy, but
oracles are fixed across the subsequent local/PCS draws in its evidence.

`prepared_concrete_soundness_budget` substitutes that history-averaged PCS
bound into the prepared-Wasm composition. For the locally valid fixed-source
branch, the actual bus, both selected local/GKR and shared PCS numerical terms
are now derived. There is no independent numerical error-budget premise.

Substantial semantic premises remain: accepted decoded bindings/final equality,
exact checks, local/GKR evidence, fixed ideal PCS oracles/projection/geometry,
authentication, recovered-input binding and accepted-failure event inclusion.
These need compatible construction from actual verifier artifacts. This is
not an end-to-end native acceptance theorem or a Fiat-Shamir/QROM theorem.

Next: construct compatible evidence, include fixed-source-invalid cases and
evaluate the complete ideal bound at candidate parameters. Native Ext8, QROM,
secure size and full 1 Pgas remain open; gate remains NOT_PASSED.

Validation: full `check.py` PASS (4113 registered results), existing axiom
allowlist. Native captures not rerun for this formal-only composition.

### Composed source-valid parameter screen on retained geometry

`report_composed_slice_parameters.py` evaluates the derived source-valid bus,
local/GKR and concrete PCS count terms and independently normalizes them with
exact rational arithmetic. It checks retained statement/proof hashes against
the rebuild manifest, matches AIR/public/rows against the degree fixture, and
recomputes the bus budget against the retained Lean export. All 144 small
cardinality/count cases agree; each reported minimum query count checks the
preceding query count fails the target. No native proof was regenerated.

`SelectedBranchWeights.lean` proves disjoint selected-history counts total at
most the earlier sample length and bounds their weighted contribution by one
maximum. The separate bus contribution is still added. Full count-to-rational
normalization remains a Python arithmetic check, not a new Lean theorem.

Retained geometry yields bus 8,589,975,831; local+batching+GKR numerators 1,785
and 1,584; PCS 917,500. The total challenge coefficient is 8,590,895,116:
`coefficient / fieldSize + (3/4)^queries`. Under an Ext8 field-size projection,
128 ideal bits still needs 309 queries and 192 needs 463. The challenge-only
ceiling is approximately 214.25496 ideal bits; 215 cannot be certified by this
bound regardless of queries. Ext4 cannot certify 128. These are upper-bound
screens, not attack/lower-bound results or post-quantum claims.

Crucial limitation: the circuit/packing geometry is the retained Ext4 geometry.
A native Ext8 circuit can change it and must be measured/re-screened. The
source-invalid branch and theorem semantic/native premises also remain open.
No secure byte estimate, QROM compiler or full 1 Pgas conclusion follows.

Development implication: adding the composed terms does not increase the
128/192 ideal query candidates for this geometry. Secure-size investigation
still requires the native Ext8 geometry, openings and compression path; extra
queries cannot fix the field/challenge ceiling.

Validation: full `check.py` PASS (4115 registered results), existing axiom
allowlist; exact arithmetic screen and minimum-query boundaries pass. Slice
gate remains NOT_PASSED.

### Ext8 terminal compiler candidate and measured circuit geometry

The terminal DAG compiler now accepts explicit field arithmetic and a matching
instruction compiler; default Ext4 behavior retains its ABI and output. The
layer builder accepts explicit constant decoding. The separate
`pq384_ext8_terminal_compile.py` candidate builds 11-word instructions from the
existing Ext8 formula generator and uses shared constant folding, CSE and
balancing. It does not call the Ext4 native round kernel.

On the actual 193-instruction AIR with deterministic synthetic Ext8 terminals,
six unoptimized-program vs DAG vs layered-output comparisons pass, covering
zero/one/random batching and zero/random private inputs. Three complete Ext4
compiler outputs match the pinned pre-edit compiler at `04eaa8e31` exactly;
three malformed input/API cases reject. The retained Ext4 fixed13 binary proof
also passes the full prepared-slice frontend after these shared-code changes.

Measured candidate geometry: private capacity 4096 and minimum input log 13
remain unchanged; random batching has 78 layers versus 35 in the Ext4 baseline.
Its sum(4*m+1) is 2158 and raw GKR scalar payload is 104832 bytes at 32 bytes
per Ext8 element. This counts scalar payload only, not framing, PCS openings,
statement transport or a generated proof. Zero/one batching yield different
specialized shapes, explicitly recorded in the report.

Next: investigate the increased depth (the candidate retains the exact Horner
formula structure), prove/validate a shallower lowering, then integrate Ext8
GKR/transcript and native round/PCS execution. No authenticated Ext8 transcript,
universal Lean compiler refinement, secure size or QROM claim is made. Full
1 Pgas remains open and the slice gate stays NOT_PASSED.

Validation: differential/negative tests and retained Ext4 frontend PASS; full
`check.py` PASS (4115 registered results), existing axiom allowlist.

### Ext8 fingerprint expansion restores shallow terminal geometry

The candidate's long Horner dependency was removed by expanding fixed public
challenge powers into scalar-weighted message terms. The canonical generator
remains default; only the Ext8 terminal candidate opts into expansion. The
shared compiler can then balance additions using its existing DAG pass.

`ExpandedBusFingerprint.lean` proves the accumulator/weight identity for all
fields and environments, specializes it to the canonical tagged fingerprint,
and preserves local degree and column coverage bounds. Zero challenges need
no special assumptions. This is the algebraic rewrite proof; universal Python
AST/refinement and checked optimized-program binding remain outstanding.

On the same actual 193-instruction AIR and seeded Ext8 input cases, random
batching drops from 78 to 35 layers and raw GKR scalar payload from 104832 to
47744 bytes (57088 bytes less, about 54.5%). Minimum input log remains 13,
private capacity 4096, and sum(4*m+1) is 983. These are compiler geometry/scalar
counts, not a generated proof or complete transport size.

Validation: six canonical-Horner instruction vs optimized DAG/layer output
comparisons; three exact pinned Ext4 compiler comparisons; 192 expanded vs
canonical bus residual comparisons with independent row-semantic checks;
576 register mutations rejected. Canonical Lean specification capture still
passes 64 residuals and rejects 16 mutations. Full `check.py` PASS (4119
registered results), existing axiom allowlist.

Next: bind optimized generated programs to the proved rewrite, then integrate
Ext8 GKR/transcript and round/PCS execution. Full acceptance/QROM, secure size
and full 1 Pgas remain open; slice gate remains NOT_PASSED.

### Expanded fingerprint instruction checker

Added `ExpandedBusFingerprintCheck.lean`: the executable checker constructs the expanded fingerprint from supplied alpha/tag/message and checks its exact register route. The soundness theorem composes route execution with the universal expansion identity, proving canonical Horner semantics for every environment under acyclicity. Kernel regressions reject wrong tag, challenge, message, root and column width.

Validation: full `check.py` PASS, 4121 audited theorems/regressions, allowed axioms only. This is a component checker: actual optimized terminal-program integration, authenticated challenge/message binding, native Ext8 proving, complete envelope measurement, source-invalid composition and QROM remain open. The feasibility gate remains NOT_PASSED.

### Check actual expanded fingerprint compiler routes

Extended `CheckExt8BusFormulas.lean` with `--fingerprints`: derive messages/tags from supplied AIR, check each fingerprint route inside a complete emitted weighted program, and check program acyclicity. Added a deterministic compiler capture runner using the retained 193-instruction AIR and zero/unit/random Ext8 alpha. No compiler production behavior changed.

Validation: 15 fingerprint routes across six cases accepted; nine mutations rejected (alpha, bus, message, root, live constant, cycle, column width, omitted root, empty capture). Existing canonical residual checker regression: 64 residuals accepted and 16 mutations rejected. Reports include statement, capture and checker digests. This connects actual compiler output to the prior universal route theorem at the fingerprint component boundary; full residual semantic replacement, optimized DAG refinement, authenticated inputs and native Ext8 proof/envelope remain open. Gate remains NOT_PASSED.

### Expanded residual context/specification bridge

Added `BusFormulaReplacement.lean`: exact subexpression replacement preserves evaluation when the replacement does; tagged fingerprint expansion therefore preserves arbitrary surrounding residual operations. An executable ordered-list checker accepts unchanged formulas or a single interaction fingerprint expansion in each residual. Its soundness theorem composes with the existing generated Ext8 specification and decoded-coordinate environment. This bridges complete expanded residual values, beyond isolated fingerprints.

`CheckExt8BusFormulas.lean --expanded` derives canonical residuals and candidate fingerprint patterns from supplied AIR, then checks ordered expanded formulas, instruction routes, acyclicity and sample values. Synthetic capture validation: 64 expanded residuals accepted, 16 mutations rejected; Python independent semantics: 192 residual comparisons, 576 instruction mutations rejected. Canonical checker regression remains 64/16; actual compiler fingerprint route regression remains 15/9. Full Lean audit PASS: 4126 theorems/regressions, allowed axioms only.

Limitations: this is conditional specification/route checking, not universal Python compiler refinement or authenticated verifier evidence. Whole optimized terminal DAG, source-invalid soundness composition, native Ext8 slice proof, secure envelope bytes and QROM remain open. Feasibility gate stays NOT_PASSED.

### Ext8 terminal structural certificates

Extended the existing program-to-DAG certificate generator/checker with explicit field arithmetic, matching instruction compiler and selector/equality environment. Instruction width derives from coordinate degree; legacy defaults remain Ext4. DAG-to-layer checker accepts explicit coordinate degree. Validation now also requires table/finals/terminal/certificate counts to agree, preventing zip truncation.

On the retained 193-instruction AIR with synthetic Ext8 challenges, zero/unit/random batching each validates 9624 reconstructed register records, signed-sum expansion/balancing, terminal equality weights/claims, batching and all DAG-to-layer routes. JSON reconstruction-certificate roundtrip passes; eight mutations per case reject (24 total). Independent canonical-Horner/program/DAG/layer comparisons still pass. Geometry stays 34/35/35 layers and input log13. Report: `results/ext8-terminal-structural-compiler.json`.

Retained Ext4 full-bus certificate remains byte-identical; 62420 register records, 14 malformed certificates and 14 arithmetic shortcut rejection cases pass. These are Python structural checks corresponding to generic Lean route theorems, not Lean-kernel-checked Ext8 captures or universal compiler refinement. Native Ext8 GKR/PCS proof, authenticated transcript, complete secure envelope and QROM remain open. Feasibility gate remains NOT_PASSED.

### First native Ext8 round primitives

Added `native-folded/kernel_ext8.rs` and explicit `pq384_ext8_native.Kernel` adapter. Rust implements affine multilinear folding and quadratic product-sumcheck coefficients in flat Ext8 (X^8=11). Coefficients use canonical u32; multiplication accumulates in u128. The ABI checks shapes/canonicality, while the wrapper checks before allocating and supplies valid disjoint buffers. Library building is explicit, with no profile replacement.

`test_ext8_native.py` builds the library in a temporary directory and checks independent Python arithmetic: 64 basis products, 18 table/challenge cases (sizes0 through4096, zero/unit/random challenge), 36 round identities, four wrapper and four direct ABI rejections. Bad ABI inputs leave output unchanged. Report `results/ext8-native-primitives.json`: PASS. At4096 elements, wrapper-inclusive fold plus quadratic work measured ~11ms versus93–100ms reference on this machine; diagnostic component timing only.

This advances native execution but does not implement the full local/GKR prover, authenticated transcript or PCS integration, and does not prove Rust refinement. Secure envelope size, QROM security and full1Pgas remain open; gate NOT_PASSED.

### Native Ext8 GKR round coefficients

Extended the native kernel and explicit adapter with GKR gate-round quadratic coefficients on either input axis, supporting add/sub/mul and prior equality weights. The native routine computes coefficients directly from affine gate values and equality factors; the independent Python test evaluates the original gate expression at0,1,2. Native validation checks all gate bounds, folded indices, shapes and scalar canonicality before output writes.

Validation: nine complete synthetic two-axis layer reductions,54rounds,162independent polynomial evaluations, endpoint and final wiring identities all pass. Sizes2/8/32 and zero/unit/random challenges cover all gate operations. Five wrapper and three direct ABI malformed cases reject; output remains unchanged on native errors. Existing native fold/quadratic/basis regression still passes. Reports: `results/ext8-native-gkr-rounds.json`, `results/ext8-native-primitives.json`.

This implements the previously missing gate-round calculation but does not yet provide transcript-driven full Ext8 GKR or PCS integration, a Rust refinement theorem, secure full envelope, or quantum security. Gate remains NOT_PASSED; next execution step is full-circuit transcript integration using these native rounds.

### Transcript-driven native Ext8 terminal GKR diagnostic

Added a separate `near-pq384-ext8-terminal-gkr-diagnostic-v1` profile in `pq384_ext8_terminal_gkr.py`. It uses eight-coordinate challenges/serialization, binds the supplied circuit/statement/claim in the SHA384 transcript, validates layout shapes, and invokes the native gate-round/fold kernels. The verifier uses independent Python field arithmetic. Its return value is an explicit REQUIRED private-input linear opening obligation; this is not a standalone proof of the circuit input commitment.

`test_ext8_terminal_gkr.py --full` proves and verifies the actual193-instruction compiled terminal geometry with synthetic terminal challenges/finals and zero private inputs:35layers,474rounds,47744raw scalar bytes. Initial timings ~9.5s prove/~3.3s verify. Raw scalar size matches the earlier geometry projection; profile/framing/public statement/PCS overhead is excluded. A small mixed-operation circuit produces exactly the same proof/transcript and opening obligation with native and reference provers; JSON proof roundtrip and direct input dot-product obligation agree. Mutation checks cover coefficients, canonicality, scalar width, omitted rounds/layers, layer inputs, profile, statement, claim and public circuit; false prover output claims reject.

The compiled193 run is not a valid prepared-Wasm transition witness. Full local-protocol/trace integration, PCS discharge, implementation refinement, complete secure envelope and QROM remain open. Feasibility gate remains NOT_PASSED.

### Native Ext8 local folded-table kernel

Inspection confirmed the existing constraint prover still depends on Ext4-only `NativeTable`. Added `kernel_ext8_local.rs`, adapting its row/selector state to eight coordinates while reusing the already-tested Ext8 arithmetic/GKR kernel. Added explicit owned-state adapter `pq384_ext8_local_native.py`: base-coordinate rows, 11-word instructions, eight-coordinate tau/prefix, round-node evaluation, folding and terminal current/next extraction.

Independent validation uses direct full multilinear evaluation and a closed-form expression covering every opcode and first/last/transition selectors. 120 round-node comparisons and nine terminal-vector pairs pass at dimensions1/3/4 with zero/unit/random folding challenges. Cyclic next rows are independently rotated before MLE evaluation. Four malformed program cases (opcode, self-cycle, column, noncanonical constant) reject; extra folds and closed-state reads reject. Shared arithmetic/GKR regressions also pass. Report: `results/ext8-local-native.json`.

This supplies the missing Ext8 local execution kernel, not yet a valid state-transition witness or local transcript. Actual source/auxiliary construction and full local→terminal GKR→PCS integration remain next; no Rust refinement, secure envelope or QROM claim. Gate NOT_PASSED.

### Retained execution traces through Ext8 local and GKR reductions

Located the retained literal193 source files and matched both exact SHA256 values to the existing prepared-slice prover report. Stored deterministic gzip copies under `results/ext8-source193` so this test does not depend on temporary external files. Added Ext8 auxiliary construction, adapted from the existing group1 generator, and transcript-driven local sumcheck proving/verifying with scalar Lagrange interpolation and the native local kernel.

`test_ext8_execution_reduction.py` uses fresh eight-coordinate challenges, constructs auxiliary coordinates/finals, checks global bus product equality including public messages, produces both local proofs, reconstructs their terminal metadata independently, and feeds the actual folded current/next values into the compiled terminal GKR. Unlike the earlier synthetic GKR run, the circuit claim is required to be ZERO. The Python GKR verifier returns the same input obligation, which the test checks directly against the witness.

Measured on two256-row source tables:16local rounds,3584local scalar bytes;35GKR layers,47744GKR scalar bytes. Combined raw scalars51328bytes exclude all commitment/opening/envelope data. Initial timings ~0.65s local and~9.66s GKR, excluding auxiliary generation and independent verification. Local proof mutation is rejected; corrupted source-row rejection is also exercised.

Critical limit: source/auxiliary full-vector digest bindings in this diagnostic are NOT polynomial commitments. Mandatory PCS authentication/discharge remains open, as do complete envelope size, native/implementation refinement, full1Pgas and QROM. Feasibility gate remains NOT_PASSED.

### Ext8 coefficient opening target

Added Ext8 dual Mobius/current/cyclic-next weight functions and branch derivation from the compiler input blocks and verifier GKR weights. Branch descriptors deliberately omit roots until actual PCS commitment binding exists. Independent base-field Boolean Mobius conversion plus direct row evaluation validates27small coefficient claims and57lane-weight MLE evaluations.

Integrated the coefficient conversion check into the retained execution reduction. The sum across all four source/auxiliary branches equals the REQUIRED GKR private-input claim. Actual widths/packing/lanes: table0 source605/16/38, auxiliary24/1/24; table1 source198/16/13, auxiliary400/16/25. Local and GKR checks, direct witness opening, mutated-round and corrupted-source rejection continue to pass.

Size implication:100lanes ×2base scalars ×4bytes ×309queries =247200bytes for naive per-query source-leaf payloads alone. Adding51328raw local/GKR bytes gives298528bytes before PCS reductions/folds, authentication, framing or statement. This is an uncompressed projection, NOT a lower bound (query deduplication/multiproofs can reduce it), and309 is the prior conditional128-ideal-bit projection, not a quantum security certificate. Next PCS work must preserve opening-point-independent commitments and measure deduplicated full geometry. Existing reusable Ext8 scalar PCS supports only equality-weight openings through degree1024; existing weighted-joint PCS is Ext4 and needs Ext8 arithmetic/FFT/encoding adaptation. Gate NOT_PASSED.

### Native Ext8 FFT/LDE for PCS commitments

Added native natural-order eight-coordinate FFT/LDE4, sharing the Ext8 kernel library. Explicit flat-word and tuple adapters preserve coefficient order; domain is bounded to2^22. Native checks validate shape, buffer alignment/capacity, overlap and scalar canonicality before output writes. This covers the retained slice's degree4096/domain16384 transform requirement.

Validation:10FFT/LDE cases,27direct polynomial evaluations,4Merkle-root comparisons, base-source preservation,4wrapper and4direct ABI rejections. Optional native backend in the existing reusable scalar Ext8 PCS gives identical source root and complete diagnostic proof to the reference, independently verified in Python. Existing fold, GKR-round and local-kernel regressions remain passing. Report `results/ext8-native-fft.json`. Atdegree4096, wrapper-inclusive LDE4 measured~8.5ms versus~275ms reference; component timing only.

The reusable scalar PCS test is not the required weighted multi-branch slice opening. That integration, deduplicated full envelope measurement, Rust refinement and quantum security remain open. Feasibility gate NOT_PASSED.

### Weighted Ext8 PCS diagnostic integrated with retained execution

Added `pq384_ext8_weighted.py`: packed base-source commitments in opening-independent contexts, weighted multi-branch reduction across heterogeneous degrees, native Ext8 fold/LDE commitments, mandatory terminal root/claim check, and independent Python Merkle/fold verification. Query budget is an explicit verifier input bound into the transcript. Sources match the existing base-field packed layout; no opening point/weight is allowed to choose the source commitment context.

Tests: heterogeneous degrees at8and309queries pass;13mutations reject (reduction/fold coefficients, source leaf/path, terminal, lengths, canonicality, statement, parent, root, weights, claim, query budget). Source roots match independent reference FFT/Merkle construction. On retained literal193 execution, actual packed source roots match the earlier statement exactly. These roots precede alpha/gamma; newly built Ext8 auxiliary roots and finals precede local mixing. Local proofs and zero-claim terminal GKR feed the mandatory weighted PCS opening. The opening verifies at309queries; first timing ~9.84s PCS proving/~0.36s verification, excluding source commitments and local/GKR work.

Current opening is5033829JSONbytes with repeated Merkle paths. This is not a compact binary measurement and not the complete envelope. Capture support writes opening config/proof plus reduction data, and checks the opening in a fresh Python process. Working capture: `/tmp/nearproof-ext8-weighted-execution`; reproducible via `test_ext8_execution_reduction.py --pcs-queries 309 --capture-dir ...`.

Executable input-opening discharge is now present, but formal implementation/proximity/composition/QROM security is not.309queries is a configured diagnostic, not128-bit quantum certification. Next: compact codec and deduplicated multiproofs, measured complete envelope, then reconcile actual PCS geometry with the conditional bounds. Gate remains NOT_PASSED.

### Compact weighted Ext8 multiproof: measured size failure

Factored weighted transcript replay for codec metadata and added `pq384_ext8_weighted_codec.py`. Codec includes fixed-width Ext8 round scalars/roots and canonical deduplicated Merkle multiproofs. Counts/indices derive entirely from the verifier-supplied branches/query budget and transcript. The constant terminal tree is reconstructed rather than transmitted. Strict version, canonical scalars, length, authentication and trailing-byte checks are enforced; full PCS verification remains mandatory after decode.

Actual retained309-query opening:5033829JSONbytes →620632binarybytes. Exact decoded proof equality, fresh-process verification, and eight binary mutations pass. Small heterogeneous-degree8/309-query proofs also roundtrip and verify through the codec;13existing adversarial PCS cases still reject. Binary capture: `/tmp/nearproof-ext8-weighted-execution/proof.bin`; report `results/ext8-weighted-codec.json`.

Breakdown:231104source-leaf bytes +181584source-authentication bytes +97408fold-leaf bytes +107616fold-authentication bytes +2920metadata =620632. Add51328raw local/GKR scalar bytes =>671960before any full envelope overhead. The current profile therefore FAILS the300000-byte target even before assembling the envelope. This is measured failure of this layout/codec, not an impossibility bound for other schemes.

Strategic implication: further scalar serialization tuning cannot close the gap. Investigate commitment pooling where transcript chronology permits, rate/fold schedule changes with corresponding soundness bounds, and reductions of source lane payload. Pooling alone cannot remove the large source-leaf and fold costs; do not silently shorten hashes or lower query security. Actual128-bit PQ certification, formal implementation binding and full1Pgas remain open. Gate NOT_PASSED.

### Calibrated packing, pooling and rate screen

Added `screen_ext8_packing.py`. First replays/verifies the actual retained opening and reproduces its620632-byte codec size exactly. For each maximum degree, independently minimizes branch packing costs while requiring at least one branch attain that degree; four small exhaustive product searches check the optimizer. Candidate geometry uses deterministic simulated uniform queries, not claimed proof measurements.

Primary screen holds309queries,48-byte hashes,32-byte Ext8 scalars,LDE4 and binary folds fixed, trying packing powers1through1024 across16seeds. Separate commitments best openings:595080–615032bytes. Pooling only within transcript phases (both pre-bus sources together; both post-bus auxiliaries together) best:500200–516728bytes, with packing16/16 and51/27lanes. Adding local/GKR scalars still gives at least551528bytes in sampled candidates. Thus no screened packing/pooling layout reaches300KB.

Secondary pooled screen uses the EXISTING conditional PCS-only130-ideal-bit inequality from `estimate_ext8_rate_tradeoff.py`, not a new security assumption. Eight seeds, LDE factors4/8/16/32/64/128. Best sampled opening bytes respectively507640/540808/607752/695960/795928/910984, despite query counts314/262/241/232/227/225 at the winning geometry. Larger authentication domains outweigh the query reduction. Alternate rates require runtime and bound revalidation; these are projections, not measured proofs or lower bounds.

Decision: do not spend implementation effort expecting packing/pooling or larger fixed blowup alone to solve the target. Investigate protocol-level reduction of source-query burden, particularly the existing rate-shift/constraint-accumulation work, with explicit composition and chronology obligations before reducing source checks. Full scope and gate unchanged: NOT_PASSED.

### Formal source-query limit for current rate-shift interface

Inspected the existing contract and `RateShiftQueryTransfer`/continuation composition. The current theorem explicitly retains the noClose source-query term; the OOD constraint is not used to improve that bound. Added `RateShiftQuerySharpness.lean`: when a fixed candidate satisfies the old functional and the OOD answer is its own evaluation, correctness of all constituent constraints is equivalent to all source queries passing. Consequently the exact count is agreement^q for every OOD point; atT-1matches it equals the existing(T-1)^qbound.

This is an interface limitation, NOT an attack on the full protocol or an impossibility result for WHIR/rate shifting. It does not assert that every such agreement pattern satisfies additional earlier-oracle/folding premises. It shows that fewer queries cannot be justified solely by the current threshold and a truthful candidate OOD answer; a stronger quantitative prior-oracle/fold/candidate relation is necessary.

Validation: full Lean audit PASS4129theorems/regressions, allowed axioms only. Exact rational budget check:96matches/128seeds gives81/256at4queries; minimum309queries for this isolated term to reach2^-128. Existing4-query diagnostic remains algebraic/chronological only. Updated the rate-shift contract and feasibility gate with this distinction. Full security, compression and1Pgas goal remain open.

### WHIR source audit: stronger query bounds still need different geometry

Reviewed upstream https://github.com/worldfnd/whir at commit
`afec1fac27c1c8cc7331aa5668bc9800f104d92c` (2026-10-09), fetched into
`/tmp/nearproof-whir-review-20261016`. Current source differs from README's
older SoundnessType CLI: `src/protocols/params/regime.rs` exposes Unique,
Johnson, and Capacity. Do not infer implementation policy from that README.
The IACR PDF fetch returned HTTP403; this entry verifies source formulas,
not the underlying paper's theorem hypotheses.

Pinned source:
- `src/protocols/params/regime.rs`, SHA256
  `8b621e391eeb6f039d0f4aec14b717859111f126d07f2461ac1e8c8a5f24a70a`:
  unique agreement factor `(1+rho)/2`; Johnson `sqrt(rho)+eta`, canonical
  `eta=sqrt(rho)/20`. Capacity explicitly cites STIR Conjecture5.6 and is
  excluded from our screen. Johnson MCA code cites BCSS25 Theorem1.5;
  that theorem has not been imported or formally validated here.
- `src/protocols/irs_commit.rs`, SHA256
  `d8039161eba7c737c277bbf01452944a130ba1af219e3874eee513e4dec7a4fe`:
  `rbr_queries` computes `-q*log2(agreement factor)`.
- `src/protocols/params/code_switch.rs`, SHA256
  `731f461e450f0f06c74c0616c3909a9f2a2735a3952534b87eddbe7abb1df96d`:
  source-query, OOD list-separation, and combination errors are separate
  terms; its solver can add grinding. We take no grinding credit.

Our `GeneralWeightedExtraction.general_weighted_unique_extraction` calls
`weighted_three_candidate_curve` and requires `2*mass+B*(D-1)<3*T`.
`CheckedRateShiftComposition` consequently requires `2*N+D<3*T`.
This is a stricter extraction regime than upstream Unique; simply changing
query counts to use `(1+rho)/2` would be unjustified. The needed replacement
must extract a shared affine polynomial curve from adaptively chosen decoded
candidates at the weaker threshold, quantify exceptional fold challenges,
and preserve the coefficient-functional identity and chronological bindings.
Ordinary uniqueness of one nearby codeword does not establish that result.

Added `screen_whir_query_regimes.py` and
`results/whir-query-regime-screen.json`. Exact rational arithmetic checks
minimal q for the isolated128-bit query term at rho=1/4:
current3/4 ->309; upstream Unique5/8 ->189; Johnson21/40 ->138.
Eight simulated seeds per geometry, existing SHA384/Ext8 binary-fold codec,
256rows, all packing powers through1024, separate or pooled-by-phase tables.
Pooled subtotal ranges including51328local/GKR scalar bytes:
554056–566504 current;402136–415640 Unique;335592–340072 Johnson.
These are counterfactual geometry projections, not implemented proofs,
not WHIR proof-size predictions, and exclude envelope and all other error
terms. No parameter or feasibility gate changed. Exact q minimality assertions
pass; screen completes successfully. No Lean changes or new formal claims.

Decision: improving extraction alone does not reach300000bytes in the sampled
fixed binary-fold layouts. Next design work should jointly target stronger
extraction and actual code-switch/multi-fold geometry; use the existing
rate-shift diagnostic as a starting point and budget all source coset openings.
Avoid a large standalone Johnson formalization before its complete geometry
shows useful headroom. Full NEAR1Pgas and128-bit PQ remain unestablished.

### Weighted code-switch geometry: marginal classical candidate, PQ headroom unresolved

Added `screen_weighted_code_switch.py` and
`results/weighted-code-switch-screen.json`. This connects the previous scalar
repeated-shift geometry model to the actual slice's weighted source widths.
Two pooled commitment-phase sources have widths803/424,256rows, equal packing
16/32/64/128/256. Equal degrees deliberately avoid an unproved heterogeneous
multi-fold lifting shortcut. All base source lanes are transmitted; every
later paired leaf is64bytes. A k-fold source query opens2^(k-1) paired leaves
per source tree. The screen includes all replicated cosets and separate
SHA384 sibling frontiers. It does not pretend a multi-fold query costs one leaf.

Dynamic programming selects skipped folds1..8, continuation rates4/16/64,
and a final disclosure of at most64Ext8 coefficients. Fixed subtotal includes
51328local/GKR scalar bytes,96log2(D) weighted-reduction bytes and8framing
bytes. Each switch costs96k quadratic bytes,48root bytes,32OOD-value bytes,
plus all opened leaves and frontier hashes. Public envelope excluded. Exact
rational query counts at134/198/220bits are sensitivity budgets ONLY, not
claimed total classical or quantum security. No grinding credit.

At134isolated query bits per stage, optimal expected subtotal and16-seed range:
- Current extraction regime:531174bytes,523688–536296.
- Upstream Unique factor:389639bytes,379944–395448.
- Upstream Johnson factor:295908bytes,290344–298472.
Johnson schedule:packing32,D8192; (degree,rate,skipped,nextRate,queries) =
(8192,4,1,64,145), (4096,64,2,64,46), (1024,64,2,4,46),
(256,4,2,4,145); disclose64coefficients. Expected source-stage cost129171,
later stages48566/39741/23798, fixed52584, terminal2048bytes.
This is a concrete geometry candidate, not an executable weighted code-switch
proof. Worst sampled headroom is only1528bytes before the envelope.

Johnson198-bit sensitivity:377928–387272bytes;220-bit sensitivity:
407656–419048bytes. These larger query budgets are not QROM conversions and
may exceed available algebraic-security headroom once MCA/list errors are
included. Their purpose is to show that the marginal134-bit size result is
not robust to extra query-security requirements.

Validation: nine exhaustive small-domain expectation checks; replicated-coset
frontier identity checked on small domains/copy counts; every query count
passes exact rational minimality checks;16 actual sampled index sets per
selected schedule, using independent frontier counting. Python compilation
and diff checks pass. No Lean changes. No feasibility gate changed.

Next decision: use this explicit schedule as the candidate for a full
algebraic/list/OOD and quantum-security feasibility budget before investing
in a weighted repeated-shift prover. A real result requires weaker-threshold
adaptive extraction, repeated weighted continuation composition, source
commitment binding and QROM analysis. The current formal regime still misses
the target substantially. Full NEAR1Pgas remains open.

### Code-switch algebra ledger: distinguish ordinary from mutual agreement

Retrieved and read the primary paper at
https://www.math.toronto.edu/swastik/rs-proximity-gaps-2025.pdf
(November11,2025; PDF SHA256
`4added3e55b83c15fcc8a698fb57e137f5bd83e79ea25ce79382817c1ad26a46`).
Verified printed page29 visually as well as text extraction. Ordinary
Theorem1.5 and mutual/list-correlated Theorem4.6 use different multiplicities:
the former has ceil(sqrt(rho)/(2eta)); the latter ceil(sqrt(rho)/eta), both
at least3. The latter also includes positive lower-order terms omitted by
upstream's leading-only m10 formula. Paper rho uses maximum degree divided
by domain size, rather than polynomial dimension. These distinctions matter
when budgeting our candidate, whose needs include adaptive candidate lists.
This is not a finding of an upstream exploit: its complete proof/other
references have not been audited.

Added `report_code_switch_algebra.py` and
`results/code-switch-algebra-ledger.json`, tied to the schedule report hash.
Uses exact rational intervals enclosing sqrt((degree-1)/domain), proves the
ceiling integer is identical at both endpoints, and upper-encloses the full
Theorem4.6 expression for M1. Independent100-digit Decimal evaluation checks
the integer and formula enclosure; relative overestimate below1e-15. Counts
include each hypothetical binary virtual fold, target-list OOD pair
separation, conservative mixing count including full cosets, quadratic
sumcheck/list terms and the sum of all source-query tails. All comparisons
against bit targets use rational arithmetic; decimal bits are presentation.

This is explicitly a PARTIAL CONDITIONAL ledger. Theorems have NOT been
ported to Lean or connected to our weighted protocol. Weighted source
extraction, coefficient-functional preservation, repeated-step composition,
local/GKR/bus, initial weighted reduction, commitment and FS/QROM terms
remain excluded/open. It is not a complete classical or quantum certificate.
No claim that simply adding these numbers proves the actual protocol.

For the selected Johnson schedules:
-134query bits per stage: query sum132.778bits; Ext8 partial132.778bits.
-198query bits per stage: query sum196.488bits; Ext8 partial196.090bits.
-220query bits per stage: query sum219.056bits; Ext8 partial198.143bits.
The modeled algebra-only ceiling is198.143bits, chiefly the high-rate
continuation MCA terms. Full-expression counts are roughly22–28times the
upstream leading-only expression on these folds. Ext12 arithmetic raises
the algebra-only ceiling to321.770bits, but that is only field sensitivity;
Ext12 requires different implementation and proof-byte accounting.

Decision: the near300k candidate is not ruled out at a classical128-bit
partial-budget level, but there is no PQ conclusion. A QROM reduction with
explicit adversary resources is now a decisive prerequisite to selecting
Ext8 versus a larger extension and a viable query budget. Do not treat
192/214/220 classical bits as automatic128-bit quantum security. Preserve
NOT_PASSED and full NEAR1Pgas scope. No Lean change this turn.

### QROM applicability and work-factor screen for the candidate schedule

Previous turn was progress (full-expression MCA ledger). Rechecked existing
`qrom_resource_ledger.py` before extending it; that older report targeted
advantage2^-128 for specified adversary query budgets. Added a distinct
constant-success resource screen in `report_code_switch_qrom.py` and
`results/code-switch-qrom-workfactor.json`.

Primary source inspected: Block/Garreta/Tiwari/Zajac, On Soundness Notions
for Interactive Oracle Proofs, author-hosted
https://www.pratyush.site/publication/soundnessnotions/soundnessNotions.pdf
SHA256 `e95696372fd879e8ac3c0a2d2612cfa3d168bc50d8b68fcceb19b745a3bd27a1`.
Corollary1.6 and its proof via CMS19Theorem8.6 give the BCS route with error
O(t²epsilon+t³/2^lambda). Resource t includes verifier/reduction overhead.
This needs appropriate special or round-by-round soundness. In particular,
all false statements start in a doomed state, every fixed doomed prefix
has bounded escape probability for every next prover message, and doomed
terminal states reject. Total accepting-path counts alone do not establish
this. The corollary distinguishes soundness from knowledge soundness.
Exact constants and correspondence to our custom transcript remain open.

Screen uses the EXISTING conditional formula
C*(Q²epsilon+3*(Q³+Q)/2^h), nominal C1/256, with the partial schedule ledger
hypothetically substituted for RBR epsilon. This substitution is explicitly
unproved. Under C1/SHA384, the maximum INTEGER log2Q where this expression is
at most1/2 is65/97/98 for per-stage query budgets134/198/220 respectively.
Under C256 it is61/93/94. These are limits of a conditional bound, NOT actual
attack costs or upper bounds on protocol security.

For target Q=2^128 and success at most1/2, allocate1/4to the Q²term and1/4to
hashing, then split epsilon between algebra and source-query tails. Holding
algebra counts frozen, the nominal C1 calculation requires extension degree
at least10, digest at least388bits, and stage queries281/90/90/281. C256
requires degree11,digest396bits,queries290/92/92/290. These are arithmetic
sensitivities, not certified field constructions or complete parameters.
Changed queries also change algebra counts; the full ledger must be rerun.
A byte-aligned or standard hash choice would round digest width upward.
No automatic SHA384 upgrade and no full-proof size claim is made.

Validation: exact rational threshold/minimality checks and script compilation.
No Lean changes. Decision: stop treating the marginal Ext8/134-bit geometric
candidate as a plausible128-bit PQ configuration without a better reduction.
Next protocol work should formalize per-prefix doomed-state transitions and
rescreen larger-field/hash configurations, or establish a demonstrably tighter
QROM route. Full NEAR1Pgas, recursion, implementation binding and300k target
remain open; feasibility gate unchanged.

### Formal per-prefix weighted-fold escape bound

Previous turn was progress (QROM work-factor screen and compiler obligations).
Added `NearCompression/WeightedFoldDoomed.lean` to begin discharging the
pointwise prefix obligation with actual extraction, not a numerical premise.

`WeightedFoldPrefix` stores the fixed source-even/source-odd functions,
domain, agreement weights/threshold, arbitrary coefficient weights and current
claim. Its `Doomed` predicate says no sufficiently agreeing polynomial pair
realizes that claim; importantly it does not refer to the next prover message.
`weightedFoldEscape` includes doomedness, quadratic degree, endpoint check,
and existence of a valid folded candidate AFTER the challenge. Malformed
polynomial messages cannot escape because the verifier rejects them.

`weighted_fold_prefix_escape_bound` proves for every valid fixed prefix and
EVERY fixed next polynomial that at most max(domain.length,2) distinct
challenges escape. It invokes actual general weighted extraction, then derives
a contradiction to initial doomedness from the extracted polynomial identity
and the endpoint check. It does not fix the decoded candidate before sampling.

`weighted_fold_adaptive_escape_budget` allows arbitrary prefix states and
prover messages depending on the complete prior challenge history. It derives
the per-history bounds and applies the existing finite-tree adaptive union
bound: escape-leaves*sample.length <= rounds*limit*sample.length^rounds.
No independence between different prover messages or different histories is
assumed; only the next uniform challenge experiment is modeled.

Scope: existing strict regime2*mass+B*(D-1)<3*threshold, not Johnson. This is
an escape-event component, not a whole-verifier RBR theorem. Actual successive
state compatibility, false-statement initialization, terminal rejection,
commitment extraction and BCS/QROM correspondence remain open. In particular,
arbitrary states(history) does not by itself say the implementation transitions
between these states. No proof-size or security gate changed.

Validation: full Lean audit PASS4131theorems/regressions; allowed axioms only.
Registered module/import/axiom checks and scope source hash; diff checks pass.
Full NEAR1Pgas and128-bit PQ under300k remain unproved.

### Checked fold transition to per-prefix escape counting

Previous turn progressed with the abstract weighted-prefix escape theorem.
Added `NearCompression/CheckedFoldEscape.lean` to connect this style of
per-prefix argument to the existing indexed, consistency-gated fold semantics.

`GeneralFoldStepChecks` contains only local size/degree halving, arbitrary
coefficient-weight interleaving/folding, endpoint/current-next claim checks,
and root-domain algebra. It requires no future-round or terminal certificate.
`checkedFoldEscape` means these checks hold, the parent indexed candidate
is absent, and a child indexed candidate exists.

`checked_fold_escape_implies_bad` derives the exact general indexed
extraction bad event from that transition. The child-to-fold-success and
extracted-outcome-to-parent implications use the literal weight/claim
recurrences and gated agreement transport; neither implication is an assumed
candidate-preservation property.

`checked_fold_continuation_escape_bound` quantifies over any fixed prior
transcript and any challenge-dependent complete continuation. It only fixes
the extraction snapshot on sampled challenges and binds the current challenge
to the sampled value. The next oracle and all later data can be adaptive.
It proves at most max(nextDomainSize,2) sampled challenges escape, using the
existing proven global measure caps and strict-regime extraction. Invalid
local checks cannot contribute an escape event.

This advances an algebraic IOP transition, not the Python/Rust verifier or
Merkle binding. A full RBR proof still must relate successive prefix states,
show false NEAR statements initialize doomed, handle all other protocol
phases, establish terminal rejection and instantiate the quantum compiler.
Snapshot equality is an explicit chronology obligation. No Johnson-bound
upgrade, smaller proof, or whole-protocol security assertion is made.

Validation: full Lean audit PASS4133theorems/regressions, allowed axioms only;
module/import/scope registration and diff checks passed. Gate NOT_PASSED;
full1Pgas/128-bit PQ/300k objective remains open.

### Larger-field/hash code-switch size screen

Previous turn progressed with checked-transition Lean bounds. Returned to the
size/security design decision before extending more formal interfaces.
Parameterized the existing code-switch geometry helpers by extension degree
and hash-node width, preserving Ext8/SHA384 defaults. Regenerated the original
nine-case report BYTE-IDENTICALLY, including exhaustive geometry checks.
Added `screen_larger_field_code_switch.py` and its retained report.

The screen uses digest64bytes, extensions8/10/12, and isolated source-query
budgets262bits with nominal C1 or270bits with nominal C256. Source width803
stays base-field; auxiliary width53*extension scales with coordinate count.
Each extension scalar costs4*extension bytes and paired intermediate leaves
8*extension bytes. All source cosets, each source tree's separate frontier,
quadratics, next roots, OOD values and terminal coefficients are counted.
Local/GKR scalar COUNT1604 is frozen but its byte width scales; a larger-field
compiler may change the count. Public envelope excluded. Neither new field
arithmetic nor a secure repeated-shift prover is implemented.

Dynamic programming over the same packing/fold/rate grid,16sampled schedules:
-Ext8,C1:527640–540120bytes; partial quantum ledger fails.
-Ext8,C256:538376–550136bytes; partial quantum ledger fails.
-Ext10,C1:570072–583800bytes; partial quantum ledger passes.
-Ext10,C256:581792–594352bytes; partial quantum ledger fails.
-Ext12,C1:611672–624136bytes; partial quantum ledger passes.
-Ext12,C256:622920–636280bytes; partial quantum ledger passes.

Recomputed the conditional algebra/query ledger for each selected schedule
and its actual new query counts, fixing the earlier frozen-count limitation.
Q=2^128, success target1/2, full MCA expression, OOD/mixing/sumcheck modeled;
local/GKR/bus/initial-reduction errors still excluded. C is nominal, the RBR
and quantum compiler hypotheses remain unproved, so passing this PARTIAL
ledger is necessary evidence only for this chosen bound, never certification.
Failing the bound is not an attack. Extension10/12 means arithmetic size
sensitivity, not a certified irreducible extension construction.

Decision: larger arithmetic/hash parameters do not preserve the marginal
300k projection. Even the optimistic passing Ext10 case is about570k before
the envelope. A successful next architecture must remove substantial opening
payload (for example via a genuinely cheaper outer recursive verifier), or
justify a substantially tighter quantum reduction. More parameter tuning in
this finite grid is not supported as the main path. No universal lower bound
or impossibility result follows. Full NEAR1Pgas/PQ/300k gate unchanged.

Validation: old report exact regression, geometry/minimal-query checks,
new schedule ledger recomputation, script compilation and clean diff checks.
No Lean changes; prior4133-theorem audit remains the latest formal result.

### Measured recursive hash work for the retained Ext8 compact proof

Previous goal turn progressed with the larger-field screen, followed by a
user-requested status update. To assess architectural compression, measured
the actual retained compact Ext8 weighted opening verifier instead of
assuming that a recursive wrapper will be cheap.

Added `measure_ext8_recursive_hash_work.py` and
`results/ext8-recursive-hash-work.json`. The script first independently runs
the canonical decoder/full weighted verifier, then instruments the existing
hash_parts function without changing verification. SHA384 framing is checked
against the implementation at nine payload lengths including padding
boundaries. Identical inputs are deduplicated by EXACT framed bytes, not by
assuming collision resistance of an auxiliary counting hash. Every profile
capture is removed in finally. Input and gadget fixture hashes retained.

Retained q309/proof620632bytes:
62977hash invocations,177186SHA384compression blocks.
12762distinct framed inputs,39701blocks after identical-input sharing.
The current codec expands shared paths then the verifier rechecks them;
measurement includes those repeated checks. Deduplicating hash computations
would not eliminate any query consistency checks.

Using the existing formally evaluated128row x6944column compression gadget:
all calls imply22,679,808rows and586.691GiB dense u32trace storage;
shared calls imply5,081,728rows and131.456GiB dense u32trace storage.
These are exact layout products, NOT peak-RAM or runtime measurements, and
exclude auxiliaries, LDE/FFT, commitments and all non-hash verifier work.
The supplied local/GKR/statement obligations are external; this measures
only opening verification, not a complete recursive state-transition proof.
The inner q309 profile itself is diagnostic, not128-bit quantum certified.

Decision: recursive compression remains an architectural option, but the
current SHA384gadget is not an economical turnkey outer circuit. Next work
must measure/constrain shared Merkle verification and substantially improve
hash-gadget layout before a full recursive prover investment. The unique
count is a candidate for sharing, not a proven minimal SHA circuit: compression
prefixes may share further work, and equality/routing constraints have cost.
No whole-proof compression or quantum security claim follows; gate unchanged.

Validation: fresh ordinary verification, instrumented verification, exact
framing parity and retained gadget dimensions checked. No Lean changes.

### Ext8 verifier compression DAG and existing batched hash layout

Previous turn measured whole-input dedup against the baseline128x6944gadget.
Inspection found existing exact-state/block capture tooling and a more compact
5234column core/1668column endpoint layout. Reused them instead of inventing
another hash profile or claiming the old baseline was the best available.
Added `measure_ext8_compression_dag.py`; reports `ext8-compression-dag.json`
and `ext8-compression-dag-check.json`.

Captured the accepted compact Ext8/q309 verifier via the existing native
SHA384 state probe. Every final digest equals hashlib; keys are the full
512bit chaining state concatenated with the128byte block. Sharing solely
on block bytes would be invalid and is not done. Return values are checked
against captured digests, and every observed hash occurrence is accounted for.
Capture artifacts under `/tmp/nearproof-ext8-compression-dag` can be regenerated
from the retained proof/config using the script; their hashes are in reports.
Build probe reproducibly with `cc -O2 -shared -fPIC sha384_state_probe.c -o
<library> -lcrypto` (OpenSSL low-level API deprecation warnings are expected).

Counts reconcile with previous instrumentation:177186compression calls,
39701after whole-input dedup,27538distinct state/block records. Prefix reuse
removes another12163blocks. All12762distinct framed calls replay correctly;
20862distinct chain edges form an acyclic graph. Independent artifact checker
rejects eight mutations:input/block/output state, negative/out-of-range node,
digest, duplicate record, partial record.

Applying existing25block batched core/endpoint GEOMETRY gives1102batches,
2,256,896core rows,35248endpoint rows,11,871,387,328base-field cells or
44.224GiBtotal dense u32source data. Largest raw chunk source is43,090,432bytes
(~41.1MiB), existing source degree262144. This improves the previously quoted
131.456GiBwhole-input baseline projection but is not measured peak RAM or
runtime: routed DAG constraints, auxiliaries,LDE,trees,GKR and nonhash verifier
operations remain excluded. No newly generated recursive AIR/proof is claimed.

Decision: use exact DAG records and existing batched layout as the next
recursive benchmark input. Measure a representative constrained batch and
its routing before making any recursion throughput or compression promise.
The full inner local/GKR/frontend obligations are external to this capture;
q309 itself is diagnostic. Gate and full1Pgas/PQ300k objective unchanged.
No Lean changes this turn; script compilation and diff checks pass.

### Measured24-node constrained batch from the Ext8 verifier DAG

Previous turn progressed with the validated exact compression DAG. Selected
actual call indices148..159, global nodes1995..2018:24distinct compression
nodes and24ordered uses. Selection uses existing contiguous chunk limits;
it is one reproducible batch, not a representative statistical sample of
all27538nodes. These selected uses do not exercise repeated fanout.

Ran imported Lean witness exporter, independent canonical AIR evaluator,
natural bus balance checks, fixed the external ordered-use commitment, then
generated and freshly verified a full diagnostic compression-record proof.
Native libraries `/tmp/libnear_folded_v2.so`,`/tmp/libpq384_fft.so`, committer
`/tmp/near-pq384-target/release/rs_commit`; proof process pinned CPUs8-15,24-31,
RAYON_NUM_THREADS2. Existing run_sha384_node_chunk workflow, no verifier rule
or cryptographic parameter changes.

Measured stages (wall time; peak RSS):
-Lean exporter25.46s;2358164KiB (~2.25GiB).
-Independent checker17.28s;197032KiB.14601248canonical constraint evaluations,
 exact balance across five buses,21negative cases pass. Actual shapes
2048x5234,32x1666,32x191,32x179;10784384base-field cells.
-Full diagnostic proof pipeline379.03s;714136KiB (~697MiB). This includes
setup, prover, compact encoding and repeated independent verification.
Within runner:source commitments3.426s,auxiliary construction/commit18.283s,
local table proofs5.754s total,GKR+weighted PCS288.357s,independent verifier
12.394s. Runner328.702s; wrapper total379.005s.

Compact proof120477bytes including four source roots; empty public payload,
external ordered-use receipt731bytes; total121208bytes. Proof SHA256
`fb2a820479543697e7447a4a4a488414f3b525338f7a3364acf31300a5859521`.
Fresh-process compact verifier passed against the preexisting receipt.

Retained in `results/ext8-node-batch/`:binary proof, compressed full statement,
config,selection,checks,receipt,runner/wrapper reports,fresh-verifier output,
and benchmark manifest with hashes. Added archive_ext8_node_benchmark.py,
which refuses incomplete/nonzero timing runs. Source traces can be regenerated
using SHA384NodeChunkImportedFixture.lean with retained config. Exact original
commands and cwd are in /tmp/nearproof-ext8-node-{export,check,proof}.time.

Scope: workload comes from an Ext8 inner verifier, but THIS OUTER proof is the
existing Q8/Ext4 diagnostic. It proves a compression-record component with
external ordered-use commitment; full call padding/IV/digest provenance,
cross-chunk coverage,aggregation,complete recursive verifier semantics and
PQ/security parameters remain open. Do not extrapolate its121k envelope to
one proof of the full DAG or1Pgas. Full workload routing geometry now accounts
44.283GiBtotal dense source data at25nodes/chunk, not actual resident memory.

Decision: first measured prover optimization target is GKR/PCS, not local AIR
proof generation. It consumes288s versus5.75s for local tables in this batch.
A full recursive investment must reduce terminal circuit/prover cost and
compose chunks securely. Gate remains NOT_PASSED. No Lean changes; prior
4133-theorem audit remains latest. Artifact/compilation/diff checks pass.

### Native Ext4 GKR acceleration on the retained recursive hash batch

Added explicit prover-only kernel_gkr4.rs and pq384_gkr4_native.py, adapting
Ext8 coefficient-generation/folding to the existing Ext4 X^4=11 basis.
Both terminal and seed GKR support optional kernel=; Python reference remains
the default and independent verification uses Python. --gkr-library threads
through the diagnostic batch runner; backend/library digest recorded.
No statement, transcript, profile, verifier, or security parameters changed.

Validation: test_gkr4_native.py checks 54 rounds, 162 independently evaluated
quadratic values, nine complete two-axis layers, all gate operations,
zero/one/random challenges, six full terminal/seed transcript and obligation
parity cases, five wrapper and three ABI rejection cases. The actual retained
24-node SHA384 batch was rebuilt with native GKR and passed fresh verification.
Both proof JSON and compact binary match the retained Python proof EXACTLY;
binary SHA256 fb2a820479543697e7447a4a4a488414f3b525338f7a3364acf31300a5859521.
Statement, source hashes and external ordered-use receipt match too.

GKR+weighted PCS: 288.357s ->123.443s (2.336x). Full pipeline including repeated
verification: 379.005s ->214.379s (43.4% less time). Proof remains120477bytes,
121208bytes with receipt. Single run each, same fixture/CPU affinity and
RAYON_NUM_THREADS=2; not a throughput estimate for full DAG or1Pgas.
Reports: results/gkr4-native.json, results/gkr4-native-batch.json and
results/gkr4-native-batch/{report.json,chunk-report.json,pipeline.time,
fresh-verifier.log}. compare_gkr4_batch.py requires exact parity before
reporting timing; no duplicate binary needed because bytes match retained one.

Reproduce: rustc --edition=2024 --crate-type cdylib -O
 airbender/direct-wasm/native-folded/kernel_gkr4.rs -o /tmp/libnear_gkr4.so;
use the prior run_sha384_node_chunk.py command with a fresh output directory
and --gkr-library /tmp/libnear_gkr4.so. Exact command is in pipeline.time.
An initial integration attempt failed because only seed-GKR had the keyword;
terminal-GKR support and six-profile parity tests corrected it before the
successful fresh run. Failed attempt timings excluded.

This accelerates experiments on recursive compression components; it does
not advance the security bound or prove Rust refinement. No Lean changes;
4133-theorem audit remains latest. Full recursive composition, secure
parameters, <300k envelope and full NEAR scope remain open; gate NOT_PASSED.

### Actual adaptive prefix-to-prefix fold escape composition

Added CheckedHistoryEscape.lean. The previous CheckedFoldEscape result used
absence/presence of candidates inside one completed transcript. The new event
uses absence in strategy(history), presence in strategy(history++[challenge]),
and literal local fold checks in the latter. This distinguishes state binding
from an assumed semantic candidate-preservation statement.

indexed_candidate_snapshot_congr derives equality of the indexed candidate
predicate from fixed extraction snapshot plus fixed parent weights and claim.
The snapshot supplies the consistency measure, source oracle and root; no
whole future transcript equality is imposed. checked_history_escape_bound
then derives the per-prefix count <=max(nextDomainSize,2), including rejecting
invalid prechallenge branches. checked_history_adaptive_escape_budget composes
these conditional counts across a full adaptive history tree with uniform
limit L: failingLeaves*|sample| <=rounds*L*|sample|^rounds. The strategy and
next oracle are arbitrary; only sampled continuations require the bindings.

Explicit premises: distinct uniform ideal challenge sample, size/degree
halving, positive domains, 2!=0, the existing strict 2*N0+D0<3*T regime,
prechallenge snapshot/parent weights/claim binding and literal sampled
challenge values. No Johnson code-switch improvement or cryptographic
binding is silently inferred. The budget counts escape events, not verifier
acceptance. Initial doom, terminal/query rejection, executable transcript
causality, Merkle binding and QROM composition remain to be discharged.

Validation: full check.py passed4136 theorem/axiom and boundary checks,
/tmp/checked-history-escape-audit.log. Registered module, public axiom audits
and scope inventory; only allowed propext/Classical.choice/Quot.sound.
No prover/proof-size change; feasibility gate remains NOT_PASSED. Host coverage
remains65/75 with10real-gated names; capacity gap remains290x versus1Pgas.

### Adaptive history terminal/query boundary

Added CheckedHistoryTerminal.lean with four audited theorems. Local path checks
are defined on successive strategy(history++[challenge]) states. Starting from
no candidate, absence of checkedHistoryEscape preserves no-candidate status
through the actual adaptive path. This deterministic induction does not assume
candidate preservation; the preceding CheckedHistoryEscape supplies the
separate conditional escape bounds under snapshot/claim/weight bindings.

For a checked final coefficient disclosure, the actual terminal polynomial
would be a candidate if at least T global-chain query seeds passed. Terminal
doom therefore implies fewer than T passing seeds. Independent uniform q-query
sampling yields at most(T-1)^q accepting query tuples. The final theorem places
local and terminal checks INSIDE acceptance, so malformed branches contribute
zero even at q=0. It does not assume honest terminal values on rejected paths.

Critical scope: the terminalValues check is complete algebraic oracle equality;
it is not yet derived from executable Merkle authentication. Initial doom is
explicit. The query-tuple count is not a claim about each sequential query's
round-by-round doomed predicate or a QROM theorem. Combining this boundary with
the escape budget into the full protocol, commitment causality, initial
source-invalid branch and quantum transformation remain necessary. No proof
size/security improvement is claimed; the target remains full NEAR1Pgas with
quantum-resistant sub300k proof, and the feasibility gate remains NOT_PASSED.

Validation: full check.py PASS4140 actual-semantics bridge theorems and boundary
examples; only permitted axioms. Log /tmp/checked-history-terminal-audit.log.
Module/Audit/scope registrations updated; git diff --check passes.

### Combined checked-history interactive acceptance theorem

Added CheckedHistoryAcceptance.lean. checkedHistoryAccept contains all
successive-prefix local checks, actual final coefficient checks, and global
chain query checks. The acceptance theorem combines the escape analysis with
terminal doom/query counting, rather than leaving those as disconnected
lemmas. For nonempty challenge/query alphabets the normalized consequence is

  Pr[checked acceptance] <= sum_i max(sizes(i+1),2)/|sample|
                            + ((T-1)/N0)^q.

Lean proves the exact cross-multiplied finite-count inequality. Queries are
independent uniform draws after the final disclosure. Invalid local/terminal
branches are already excluded inside acceptance. A separate new theorem
charges each shrinking domain individually instead of rounds times a uniform
maximum. This sharpening is within the existing strict extraction regime;
it does not justify any Johnson/code-switch size projection.

Premises remain visible: no initial indexed candidate, distinct ideal challenge
alphabet, positive/halving domain geometry, degree halving, 2!=0,
2*N0+D0<3*T, fixed snapshots/parent weights/claims before each challenge, and
correct sampled challenge values. The local conditional bounds are derived,
not assumed. This proves algebraic interactive acceptance soundness for the
stated model, NOT committed implementation soundness or a QROM theorem.
The source-invalid initial reduction, cryptographic/executable state binding,
and round-by-round treatment of the actual Fiat-Shamir query schedule remain
necessary before quantum128 certification. Full NEAR1Pgas/sub300k goal remains
open; feasibility gate NOT_PASSED.

Full check.py PASS4142 theorem/axiom and boundary checks; log
/tmp/checked-history-acceptance-audit.log. Module/Audit/scope registrations
updated. No executable protocol, proof size or prover performance change.

### Source-far initialization composed with adaptive checked acceptance

CheckedHistorySource.lean now joins the existing joint-beta source-far bound
to the new successive-prefix acceptance model. indexed_initial_candidate_agreement
shows an initial indexed candidate implies an actual degree-bounded polynomial
with at least T source agreements: initial global-chain weights have cap1, so
consistency mass cannot manufacture source agreement.

checked_history_joint_far_acceptance_budget permits the complete inner strategy
to depend on all outer batching coordinates. Fixed multiaffine contractions
of fixed sources with no joint representative yield a bounded outer event
where an initial scalar candidate could exist. Outside it, the new lemma
DERIVES noInitial and invokes checked_history_interactive_acceptance_budget.
The conclusion is the literal checked-acceptance finite count with outer
batching error plus summed adaptive folding error plus terminal-query error.
It no longer takes absence of an initial indexed candidate as a premise.

Still explicit: no common joint representative (the far branch), fixed source
values/root before outer draws, multiaffine batching maps, distinct domains,
the strict extraction regime/interpolation, inner prechallenge snapshot and
claim/weight bindings, and ideal independent sampling. This does not identify
arbitrary source-invalid AIR traces with the far branch; the near branch can
have a representative and needs functional discrepancy. The existing
WeightedVirtualInitial provides the near-source no-initial lemma, but full
executable source classification, commitment authentication, transcript
causality, full NEAR and QROM remain open. No new security-bit or sub300k claim.

Validation: full check.py PASS4144 theorems/axiom closures and boundary checks,
/tmp/checked-history-source-audit.log; module/Audit/scope registrations updated.
No executable protocol or proof-size change. Feasibility gate NOT_PASSED.

### Executable Lean checker for real chunk hash-call links

Added SHA384ChunkCallCheck.lean: checkChunkCallWiring checks all eight state
words (512bits) at every link; checkChunkCall checks declared use ordinals,
128-byte block lengths, block words against ordered-use payloads, canonical
SHA512-family padding of supplied message bytes, standard SHA384 IV, and final
full state. check_chunk_call_wiring_iff and check_chunk_call_sound prove that
successful executable checks discharge the corresponding semantic premises.
sha384_chunks_checked_call_sound then composes this with actual chunk HoldsP
compression facts and the explicit ordered-use binding interface to obtain
the complete sha384ChainDigest. No compression fact is supplied by this checker.

CheckSHA384ChunkCalls.lean runs the exact proved checker. The Python fixture
builder selects actual calls148..159 and source03 ordered-use rows from the
retained Ext8 verifier node batch. All12calls/24steps pass. Eleven cases reject:
wrong IV, hidden output word, hidden input word, block word, operand byte,
padding length, omitted block, reordered uses, out-of-range use, wrong final
state, and short block. Hidden-word tests touch the last128bits discarded only
at final digest extraction, ensuring intermediate chaining uses the full state.

Artifacts: results/ext8-call-check/{cases.json.gz,report.json,lean.log}.
The gzip expands to the exact cases.json hash recorded in report.json. Replay:
  gzip -dc results/ext8-call-check/cases.json.gz > /tmp/chunk-call-cases.json
  lake env lean --run CheckSHA384ChunkCalls.lean /tmp/chunk-call-cases.json
Generator: airbender/direct-wasm/test_sha384_chunk_call_check.py with the prior
/tmp/nearproof-ext8-compression-dag and /tmp/nearproof-ext8-node-batch inputs.

Scope: an executable, proved semantic checker, not a new AIR or recursive
proof. Message bytes must still be bound to actual framed verifier operands;
this checker does not establish that provenance or unique chronological call
coverage. Ordered-use roots must still imply trace equality. Recursion must
arithmetize these checks and compose all chunks. The measured121208-byte
compression-component envelope and quantum-security status are unchanged.

Validation: full check.py PASS4147 theorem/axiom and boundary checks;
/tmp/sha384-chunk-call-check-audit.log. Module/Audit/scope registration updated.
Goal remains full NEAR1Pgas/quantum128/sub300k; feasibility gate NOT_PASSED.

### Same-root compression proof and full-call checker conjunction

Added verify_sha384_linked_calls.py. It independently reconstructs the packed
base-field use-table root in Python (lower Mobius, LDE4 FFT, exact lane-pair
leaves and SHA384 Merkle context) and requires equality with the externally
fixed use receipt AND the compression proof's source3 root. On the retained
batch this matches the original Rust-produced root exactly. The verifier then
checks externally supplied message bytes, expected digests and use ordinals:
all active use ordinals must occur once in exact order; final digest must match
the expected call result; the proved Lean checker must accept every call.
Finally the full compact compression proof decoder verifies local/GKR/PCS/bus
conditions. Caller configuration is not read from the proof as an assertion.

This joins the previous separate checker/proof runs using the SAME committed
use payload. It uses full use-table disclosure for a concrete integration
baseline; it does not create a succinct recursive linkage proof. Equal Merkle
roots give cryptographic binding only under the separately required hash
assumption. Neither this Python reconstruction nor the Q8 proof establishes
Lean HoldsP unconditionally. Message framing/operand provenance must still
come from the enclosing verifier, and calls cover only this selected batch.

Actual retained proof accepted in a fresh process for12calls/24active uses,
32padded rows x179columns. Fourteen negative cases reject: node ID, input,
block, hidden output, digest-field and padding-row changes, noncanonical
field, reordered use rows, missing/reordered calls, duplicate ordinal, wrong
expected digest, wrong same-length message, and corrupt compression-proof
magic. The last check ensures a valid call checker cannot bypass proof verify.

Retained results/ext8-linked-calls contains rows.json,calls.json,report.json,
fresh-verifier.log and statement.json.gz. Proof/receipt are the unchanged
results/ext8-node-batch artifacts. Total actual proof + disclosed-row JSON +
trusted-call JSON + receipt =149487bytes (static AIR/spec external). Raw u32
row data would be22912bytes; this is an accounting alternative, not an encoded
format used here. No sub300k secure-recursion claim: parameters remainQ8/Ext4.
Fresh verification was approximately13seconds. Regression reproduction:
python3 airbender/direct-wasm/test_sha384_linked_calls.py --output-directory
/tmp/nearproof-ext8-linked-calls (package cwd; all inputs retained in repo).
No Lean source changed; latest full audit remains4147. Python compilation and
git diff --check pass. Full1Pgas/PQ128 objective and feasibility gate stay open.

### Same-root GKR/PCS call-link proof removes use-row disclosure

sha384_call_pcs.py compiles the externally configured12calls into2880linear
field equalities:768input-state/chain limbs,1536canonical padded-block limbs,
576expected digest bytes. Each first block uses the standard IV; every later
block equates all32input limbs with the preceding32output limbs. Messages,
ordinals and digest expectations remain verifier inputs. Exact ordered ordinal
coverage is checked; framing bytes derive from caller context, not proof data.
Compression AIR supplies the byte/limb range and output-digest relationships.

After binding the trusted statement/calls/use root, a transcript challenge
batches the residuals. A verifier-derived14-layer arithmetic circuit checks
the resulting linear functional against its derived constant. Generic terminal
GKR reduces to two input MLE queries, then existing weighted PCS opens exactly
the SAME packed use root as the compression proof. Input slots are row-low,
column-high with zero column padding; direct row-MLE/obligation parity checked
before proving. The public verifier receives no rows or cache. A canonical
binary format carries fixed-shape GKR scalars plus the existing weighted PCS
codec; configuration derives all dimensions/weights and must verify.

Actual12call/24step experiment: call proof25134bytes, compression proof120477,
combined proofs145611; with trusted calls5858 and receipt731,total152200bytes,
static AIR/spec external. Disclosed row bytes0. New proof generation~2seconds.
This is2713bytes MORE than the149487byte disclosure baseline at this small
size; the progress is replacing full-source disclosure with a PCS interface,
not claiming a size win. Same proof binary reproduced on the second run:
53f90c09443952465d10da72a356754028d90234192292ba46b1cc3be429dba2.

Fresh process verified both proofs together without rows. Seven wire/config
negatives reject: truncated/trailing bytes,GKR coefficient,PCS authentication,
external digest,message,and call order. Five source mutations independently
violate both exact equations and the compiled output: IV,block,hidden chaining
output,hidden chaining input,final digest. Full canonical encode/decode parity
and original native-source root parity pass. Retained results/ext8-call-pcs
includes proof.bin,proof.json.gz,statement.json.gz,report,verifier log,manifest.

Reproduce from package cwd:
python3 airbender/direct-wasm/test_sha384_call_pcs.py --output-directory <fresh>
 --rs-binary /tmp/near-pq384-target/release/rs_commit
 --fft-library /tmp/libpq384_fft.so --gkr-library /tmp/libnear_gkr4.so
Standalone verifier: verify_sha384_call_pcs_bundle.py, requiring call proof,
compression proof, trusted statement/receipt/calls; no witness arguments.

Limits: Q8/Ext4 diagnostic remains. No Lean refinement of the new compiler or
root-to-AIR cryptographic implication is claimed. Next formal obligation is
linear-constraint compiler equivalence to the proved call checker under
canonical limbs and compression facts. Native transcript operand provenance,
full recursive verifier, aggregation and quantum128 parameters remain open.
No Lean changes this turn; latest4147audit remains applicable to existing
formal modules. Python compilation and git diff --check pass. Goal/gate open.

### Lean refinement foundations for the new call-link compiler

SHA384CallLinear.lean adds eight audited results. callWordLimb matches the
compiler's little-endian16-bit decomposition. Each limb survives Fp embedding
exactly, and four limbs decode a bounded64-bit constant exactly. Constant
residual lists recover arbitrary bounded expected word lists. The specific
SHA384 IV follows from its32constant residuals, without assuming the decoded
initial state.

callStateLinkResiduals uses the actual use-row column offsets3and99 and all32
limbs. Zero residuals imply equality of all eight decoded words. Concatenating
these residuals for every adjacent use establishes the existing chunkCallWiring
predicate for the entire ordered sequence. The final state is the last output
state by the same fold definition; no truncated digest is used in any link.
The row-low/column-high slot injection theorem proves r+rows*c cannot alias
s+rows*d when both row indices are bounded. This supports the8192-slot packing
used in the actual call-link GKR proof.

These are deterministic semantic refinement pieces. They do not yet prove
Python generator correspondence or randomized residual-batching soundness,
connect canonical framed bytes to every generated block constraint, or complete
the final digest/PCS/compiler join. The generic constant-word theorem can
supply block-word equality once that framing/coverage connection is made.
No claim that all new Python/GKR behavior is now formally verified.

Validation: full check.py PASS4155 theorem/axiom and boundary checks, only
permitted axioms; /tmp/sha384-call-linear-audit.log. Registered module and all
eight public theorem audits. No executable/proof format changes this turn;
retained152200-byte diagnostic bundle unchanged. Full NEAR/PQ128 goal and
feasibility gate remain open.

### Exact Lean/Python descriptor correspondence for retained call proof

Added SHA384CallEquations.lean with the compiler's left-slot/optional-right/
constant descriptor and row-low/column-high private input interpretation.
Four audited theorems show slot decoding, exact evaluation of constant and
state-copy descriptors into the previously proved residual lists, and recovery
of expected digest bytes from zero digest descriptors. The per-call generator
uses standard IV, all32state-copy limbs, all64block limbs and48digest bytes in
the same order as the Python compiler.

ExportSHA384CallEquations.lean independently pads actual message bytes using
NearSpecV3.SHA512.pad, decodes block words with the Lean words function, and
exports canonical descriptors. test_sha384_call_equation_parity.py checks that
input messages/ordinals/digests correspond to the retained caller configuration
before comparing every descriptor against sha384_call_pcs.equations.
All2880descriptors match exactly:384copy +2496constant (384IV +1536block +576
finaldigest), with identical slot indices, sequence and constant values.
All emitted source slots are inside32x179 and constants below65536.

Retained results/ext8-call-equation-parity/{equations.json.gz,report.json,
lean.log}; uncompressed descriptor SHA256
 a7dfacd2c1faf4a69aca31cf79d32c253f1d1f9dd1e268ff9076e1f3154933c0.
Reproduce from package cwd after lake build NearCompression.SHA384CallEquations:
python3 airbender/direct-wasm/test_sha384_call_equation_parity.py
 --output-directory /tmp/nearproof-call-equation-parity

Scope: general Lean descriptor evaluation facts plus exact regression parity
on the real12call batch. This is not a universal refinement theorem for Python,
and does not yet prove scattered coefficient accumulation/batching, generic
GKR circuit compilation, complete framed-operand provenance or QROM soundness.
The152200-byte same-root diagnostic proof bundle is unchanged. Full1Pgas/PQ128
objective and NOT_PASSED feasibility gate remain open.

Full check.py PASS4159 theorem/axiom and boundary checks;
/tmp/sha384-call-equations-audit.log. New module/Audit/scope entries registered.
Python compilation and git diff --check pass.

### Exact coefficient batching identity and ideal cancellation bound

CallLinearBatch.lean proves the algebraic step between unbatched descriptors
and the GKR compiler's coefficient functional. Generic field equations are
left-minus-optional-right-minus-constant (copies use constant0). Compilation
scatters +weight/-weight into slots and accumulates weight*constant in the
claim. call_scatter_dot and call_linear_compilation prove the resulting dot
product minus claim equals the weighted residual sum. Repeated slots are
allowed and summed exactly; no unique-slot or nonzero-weight premise is used.

call_compiled_score_mle identifies equality-weight batching with the residual
table MLE. call_compiled_batch_zero_count applies finite-grid counting directly
to that compiled functional: a fixed nonzero residual in2^dpositions is hidden
on at most d*|sample|^(d-1) challenge vectors from a distinct sample. Thus the
ideal uniform bound is d/|sample|, conditional on fixed residuals and bounded
slots. The retained2880-equation batch occupies d=12 coordinates; zero padded
positions are represented algebraically by self-copy equations with constant0.
This is not an end-to-end soundness or Fiat-Shamir/QROM result.

Remaining refinement: connect actual Nat/Fp descriptor constants to the chosen
extension representation, prove Python's mutable array accumulation implements
the mathematical scatter, identify exact padding behavior, and join the GKR
circuit compiler/PCS and commitment semantics. The theorem quantifies over an
abstract field; it does not certify the diagnostic Ext4 profile at128PQ bits.
No proof or protocol change;152200-byte retained bundle unchanged.

Validation: full check.py PASS4164 theorem/axiom and boundary checks,
/tmp/call-linear-batch-audit.log. Five public theorem audits and module/scope
entries registered; git diff --check clean. Full NEAR1Pgas/PQ128/sub300k goal
and NOT_PASSED feasibility gate remain open.


### Sequential call coefficient compiler refinement

CallArrayCompilation.lean now proves the sequential Array.modify accumulator
implements mathematical scatter and constant accumulation. Five public results
cover size preservation, reads after each update, the full loop, initialization
from zero, and the resulting weighted residual functional. Same-slot addition
and subtraction read the updated array and cancel correctly. The final
functional theorem requires bounded descriptor slots; the array loop itself
has defined out-of-range no-op behavior and does not establish input bounds.

The executable Python compiler now exposes its existing coefficient loop as
compile_coefficients, used directly by compile_layout. ReplayCallArray.lean
executes the proved Lean loop over Fp for all four coordinates of actual Ext4
weights. This coordinatewise comparison is applicable because the loop only
adds/subtracts weights and multiplies them by base-field constants. It is a
concrete parity check, not a universal refinement theorem for Python or Ext4.
The retained 2880 equations produce exactly matching 8192 coefficients and
claim in all four coordinates. An additional case covers aliasing, repeated
slots, and zero/unit weights. Existing call proof verification passes and its
binary encoding is unchanged (SHA256
53f90c09443952465d10da72a356754028d90234192292ba46b1cc3be429dba2).

Validation: full check.py PASS4169; /tmp/call-array-audit.log. Replay command:
python3 airbender/direct-wasm/test_call_array_parity.py --output-directory
/tmp/nearproof-call-array-parity (from research/near-compression, after the Lean
build). Retained results/call-array-parity/report.json records source hashes.

Remaining work includes general descriptor-to-extension correspondence, exact
zero-padding refinement, GKR circuit lowering, commitment/PCS composition and
Fiat-Shamir/QROM analysis. The 152200-byte diagnostic bundle is unchanged;
full NEAR 1Pgas / PQ128 / sub300k feasibility remains NOT_PASSED.


### Unpadded array compiler to padded residual soundness

CallPadding.lean closes the mathematical zero-padding interface. Missing
positions use a self-copy equation (left=right=0, constant=0), whose residual
is zero for every private vector. call_short_batch_mle proves the weighted sum
over the actual equation count equals the MLE of the full power-of-two padded
residual table. call_short_array_mle composes this with the sequential array
compiler theorem; call_short_array_zero_count derives the finite challenge-grid
cancellation bound directly for that array functional. No disjointness or
nonzero-challenge premise is introduced. Bounds on actual slots and on equation
count, plus a fixed nonzero residual before sampling, remain explicit premises.

The concrete regression now compares 2880 real equations with 4096 equations
including neutral padding. Both Python and the proved Lean array program yield
identical 8192 coefficient vectors and claims in all four base-field
coordinates; both replay outputs have SHA256
c148a8c5cf4a3e545c819e55c35db8dbbc564971444e798b66dd2fc383d5d1f7.
Retained call proof verification and exact binary re-encoding still pass.
Full check.py PASS4174; /tmp/call-padding-audit.log. Parity command is unchanged,
with output /tmp/nearproof-call-padding-parity; retained report is updated.

This proves abstract equality-weight truncation and neutral padding, not the
universal correspondence of Python eqs/transcript sampling to the Lean field
model. Descriptor lifting, GKR lowering, PCS/commitment composition, QROM and
full NEAR feasibility remain open. No security or size gate is newly passed.

### Source call descriptors through extension batching

CallDescriptorLift.lean proves the missing semantic transport from source
CallLinearEquation.eval to CallBatchEquation.residual. The two formats differ:
source copy descriptors ignore the constant field, while batch equations always
subtract it. CallLinearEquation.Valid records the necessary zero-constant
invariant for copies. Every descriptor emitted by callBlockEquations and
callEquations satisfies it, without bounds or assumptions about private values.

The general lift theorem requires preservation of zero and subtraction.
Instantiation with the existing Fp8.ofBase model identifies every generated
extension residual with the embedding of its source Fp residual; injectivity
preserves nonzero residuals. call_descriptor_array_zero_count composes this with
the previous unpadded array theorem. Its failure premise is now an actual source
descriptor evaluated over Fp, not an assumed unrelated extension residual.
The count bound remains d*|sample|^(d-1) for a distinct ideal challenge sample,
with fixed descriptors/private values, bounded real slots and at most 2^d real
equations. Generated descriptor validity discharges the zero-copy premise.

Validation: full check.py PASS4180; /tmp/call-lift-audit.log. Six public theorem
axiom audits added; no new axioms beyond propext/Classical.choice/Quot.sound.
No executable protocol or retained proof bytes changed. This uses the formal
Ext8 model; the retained small hash-call proof still uses diagnostic Ext4 and
is not granted Ext8 or PQ128 security by this theorem. GKR circuit lowering,
commitment/PCS composition, transcript/QROM analysis, full recursive operand
provenance and full NEAR 1Pgas feasibility remain open.


### Sparse call DAG functional and empty-support correction

CallCircuitRoute.lean reuses the existing TerminalDAGRun evaluator and
TerminalBalanceRoute addition-tree semantics. Its structural certificate binds
all nonzero coefficient slots to input-times-constant leaves, the balanced sum,
and the final claim subtraction. Exact support prevents omitted nonzero terms.
call_circuit_functional derives the root's dot-minus-claim value from acyclic
execution and this structural route; call_circuit_residual_sum composes the
result with the sequential array compiler. Neither theorem assumes root-value
equality. Structural route construction for arbitrary emitted Python circuits
is still an explicit obligation, not silently discharged by the theorem.

The executable compiler now exposes compile_dag for regression inspection.
Inspection found a real empty-support bug: terms[0] crashed if all coefficients
cancelled. It now emits a constant-zero sum node before subtracting the claim.
This handles both an identically zero functional and a constant nonzero
functional with zero coefficient support. Existing retained proof bytes are
unchanged and still verify.

The parity test checks actual DAG acyclicity, exact sparse support and leaf
constants, root subtraction, and agreement of independent DAG execution,
layered GKR evaluation and direct dot-minus-claim on three input vectors for
each of five scenarios: retained, padded, aliases, zero support and constant
failure. Deliberately changing the root subtraction to addition is rejected.
These Python checks are concrete evidence, not kernel-checked certificates.

Validation: full check.py PASS4182, /tmp/call-circuit-audit.log. Extended parity
PASS, /tmp/call-circuit-parity-v2.log; retained results/call-array-parity report
includes source hashes. Next formal work is certificate extraction/checking
and composition with existing layer-route semantics. General layering
refinement, full recursion, PQ128/QROM and full NEAR1Pgas/sub300k remain open.


### Proved call circuit checker and actual certificate replay

CallCircuitCheck.lean reuses the existing proved TerminalBalanceCheck instead
of introducing a second addition-tree checker. callCircuitCheck recomputes
exact nonzero support from caller-supplied coefficients, checks finite input /
constant / product node bindings, final claim subtraction and all DAG
acyclicity, then checks the supplied balance certificate. Acceptance constructs
the CallCircuitRoute required by the previous theorem. The resulting root
functional theorem holds for all private inputs, not just regression vectors.
call_layered_checked_functional additionally composes it with the existing
terminalStoredBundleCheck theorem; actual layer-certificate replay is still
pending for this call compiler.

CheckCallCircuit.lean parses the existing diagnostic Ext4 scalar representation
using the repository's Fp4 model. Extracted actual addition stages, product and
constant-node maps feed the proved checker. Five fixtures pass: the retained
2880-equation batch, its 4096-equation padded equivalent, aliases, zero support,
and zero support with a nonzero claim. Four mutated retained certificates
reject (root operation, coefficient constant, product operation, support map).
The fixture is retained as results/call-array-parity/circuits.json.gz alongside
the checker log, source hashes and uncompressed fixture hash. This runtime
execution uses a checker whose acceptance theorem is kernel-checked; it is not
a kernel evaluation of the full large fixture.

Validation: full check.py PASS4185, /tmp/call-checked-audit.log. Extended parity
and certificate replay PASS, /tmp/call-checked-parity.log. Existing proof still
verifies and has identical binary encoding. Expected coefficients in the
fixture are supplied by the executable compiler (their concrete array parity
was checked); arbitrary Python compiler correspondence and transcript sampling
are not inferred from this replay. No PQ128 claim, full-recursion completion,
or full NEAR1Pgas/sub300k feasibility gate is newly established.


### Actual call GKR layer certificates checked

The actual call DAG fixtures are regenerated by compile_dag, required to equal
the earlier checked nodes/root, and lowered by pq384_terminal_gkr.layer_circuit.
The existing certificate extractor records initial storage and every layer's
node placement. All five bundles pass CheckStoredRoutes.lean, whose executable
terminalStoredBundleCheck has a proved acceptance theorem. This checks the
actual initial private/constant positions, computed gates, relays, zero slots,
and final output placement. The retained and padded circuits each have 17985
DAG nodes, 14 layers and 8210 gates (6528 computed, 16 relayed, 1652 padding,
plus reserved zero gates). Each large checker replay took about 1.8 seconds.

Nine retained-layout mutations reject: cyclic node, misplaced private input,
changed constant, nonzero reserved zero slot, wrong zero gate, missing final
root, invalid source node, out-of-range placement and unknown opcode. The
parser rejects some malformed cases before the structural checker; the test
explicitly excludes Lean elaboration failures from rejection evidence.

call_layered_checked_residual_sum composes sequential array accumulation with
both accepted structural checkers, deriving the weighted residual sum at the
actual layered output. This is deterministic compiler preservation, not GKR
transcript soundness or the polynomial commitment opening argument. It requires
bounded equation slots and checks against the intended coefficients/claim.

Validation: full check.py PASS4186, /tmp/call-layer-audit.log. New script
python3 airbender/direct-wasm/test_call_layer_certificates.py --output-directory
/tmp/nearproof-call-layer-certificates passes five captures and nine negatives.
Compressed exact captures, logs, counts, timings and source hashes are retained
in results/call-layer-certificates. No executable protocol/proof bytes changed.
Runtime checker acceptance is not a kernel reduction of these large JSON
instances. Parser refinement, arbitrary compiler generation, transcript/PCS/
QROM composition, full recursive operands and NEAR1Pgas/PQ128/sub300k remain
open; the feasibility gate remains NOT_PASSED.

### Checked call root enters the GKR terminal-error budget

CallGKRRoot.lean derives the GKR initial wrong-claim predicate from the actual
checked call circuit and a nonzero weighted residual sum. It uses the computed
reverse circuit valuation, the exact Boolean output-slot query and initial zero
claim. These verifier interfaces and output bounds remain explicit. The result
no longer asks callers to assume an abstract unrelated wrong GKR root.
call_gkr_terminal_budget specializes the existing evaluated continuation bound:
accepted paths are charged to sum(4*m+1)/|sample| plus accepted incorrect
terminal input functionals on the same joint experiment. The opening-error
term is not dropped, nor is independence from acceptance assumed.

measure_call_gkr_budget.py reads the retained layout rather than estimating
rounds. Its output-to-input predecessor logs are
[2,2,3,4,4,5,6,7,8,9,10,11,12,14], giving GKR numerator402. The2880-equation
batch has12coordinates, giving a conditional component union numerator414.
For the diagnostic field size2013265921^4 the displayed component bound is
414/|F| = approximately2^-114.934. This upper bound alone cannot certify128-bit
classical soundness, let alone128-bit quantum security. It is not an attack
probability lower bound or a total-protocol error estimate. The report keeps
PCS/commitment error explicit and states the missing whole-transcript outer
batching/GKR composition and Fiat-Shamir/QROM obligations.

Validation: full check.py PASS4188, /tmp/call-gkr-audit.log; two public theorem
audits added. Parameter report retained at
results/call-layer-certificates/ideal-gkr-budget.json with exact source hashes.
No proof bytes or executable verifier changed. Next work is the actual GKR
message-path refinement and source-opening binding, followed by full soundness
composition; the diagnostic small proof is still not the secure target profile.
Full recursion, full NEAR1Pgas/PQ128/sub300k and NOT_PASSED gate remain open.

### Actual GKR message arithmetic replay through proved checks

GKRMessageCheck.lean adds a computable axis check for coefficient length≤3,
endpoint equality and evaluation at each supplied challenge. Its acceptance
theorem yields weightedSumcheckChecks for the SAME history-indexed message and
claim functions. The layer checker includes both axis lengths, the left/right
claim connection and gkrLayerWiring equality; its acceptance theorem yields the
existing GKRLayerStrategy.checked predicate and both length equalities.

CheckGKRMessages.lean replays finite transcript tapes in the existing diagnostic
Fp4 model. test_call_gkr_messages.py extracts actual challenge draws, weighted
gates, quadratic messages and terminal inputs from the retained call proof.
All14layers /194sumcheck rounds pass the Lean checker. Six modified paths reject:
wrong initial claim, coefficient, excessive degree, challenge, terminal input
and axis length. The independently extracted terminal obligation equals the
actual Python verifier's returned obligation exactly.

Scope boundary: the replay's tape functions certify one finite path. This does
not reconstruct a causal adversarial strategy across all sampled paths, prove
Fiat-Shamir challenge derivation, or formally establish every cross-layer query
binding. The full evaluated-path assumption in CallGKRRoot is therefore not yet
universally discharged. PCS opening/binding and QROM obligations remain open;
no PQ128 or full-recursion conclusion follows from arithmetic parity.

Validation: full check.py PASS4190, /tmp/gkr-message-audit.log. Replay PASS14,
negative checks6, /tmp/call-gkr-messages.log. Compressed fixture, uncompressed
hash, source hashes and Lean log are retained in results/call-gkr-messages.
No executable proof/verifier was modified. Full NEAR1Pgas/PQ128/sub300k goal
and NOT_PASSED feasibility gate remain unchanged.

### Checked cross-layer GKR path

GKRPathMessageCheck.lean extends the finite message checker with actual
next-layer weighted wiring, a+gamma*b claim linkage and circuit-depth/shape
checks. Acceptance implies gkrEvaluatedVerifierPath for the same supplied
history-indexed strategies. Composition with gkr_evaluated_path_linked gives
gkrCircuitVerifierPath for the computed finite-circuit assignment, removing
independent adjacent-layer evaluation assumptions from this checked interface.

CheckGKRPath.lean builds replay strategies from the retained arithmetic records
and executes the path checker against the actual retained layer wiring. The
capture layout is first required to equal fresh compile_layout output. The
full14-layer path passes; seven mutations reject: gamma, next claim, next
weighted-gate order, circuit layer wiring, missing layer, extra layer and empty
path. The gamma mutation is especially useful: gamma does not enter the local
layer check but must bind the following weighted queries and claim.

Validation: full check.py PASS4192, /tmp/gkr-path-audit.log. Runtime path replay
PASS1 / reject7, /tmp/call-gkr-path.log. Compressed exact path cases, fixture
hash, source hashes and Lean log are retained in results/call-gkr-path.
No executable prover/verifier or proof bytes changed.

Remaining boundaries: replay strategies certify this finite path, not causal
Fiat-Shamir/adversarial strategy behavior over all challenge paths. Initial
root-query binding is supplied separately by CallGKRRoot. Commitment opening
composition, hash/QROM reductions, complete recursive operand provenance and
full NEAR1Pgas/PQ128/sub300k feasibility remain open. The new checked relation
must not be confused with a complete proof of the Python verifier or protocol.

### Checked initial GKR root query and zero claim

GKRRootMessageCheck.lean checks that the final layer exists, its width is the
power of two described by the supplied Boolean bits, the selected output slot
is bounded and equals the decoded Boolean index, the initial weighted gates
are exactly the corresponding single root query, and the initial claim is0.
call_root_message_wrong composes these checks with the checked call compiler,
so CallGKRRoot's root-query/zero-claim/output-shape assumptions are discharged
by an executable check rather than independently supplied equalities.

CheckGKRPath.lean now checks this starting relation together with the full
cross-layer path. The root slot and bits are derived from the retained layout,
which is compared with fresh compile_layout output before replay. The actual
14-layer path passes. Eleven negatives reject: the prior seven plus changed
output slot, wrong Boolean root bit, nonzero initial claim, and wrong initial
root weight. Retained paths fixture/report/log updated in results/call-gkr-path.

Validation: full check.py PASS4194, /tmp/gkr-root-message-audit.log. Combined
root/path replay PASS1/reject11, /tmp/call-gkr-root-path.log. No prover/verifier
or retained proof bytes changed. The selected slot's provenance is supplied
by the existing checked compiler layout; this is still runtime execution of
proved checkers rather than kernel evaluation of the full JSON capture.
Transcript causality/Fiat-Shamir, source-opening binding, PCS/QROM composition,
full recursive operands and full NEAR1Pgas/PQ128/sub300k feasibility remain
open. Next focus is terminal functional to committed source rows.

### Terminal call functional to source-table opening

CallSourceOpening.lean proves the exact row-low/column-high MLE decomposition
for the zero-padded call input. The column weights retain all high GKR input
coordinates, including coordinates beyond the256-column private capacity when
public constants enlarge the total input space. Six results cover the source
functional, its two-query combination, private/public input splitting, zero
values beyond the private capacity, the specialized source input split, and
an iff between wrong full-input and wrong constant-subtracted source openings.
This is algebraic obligation preservation; cryptographic binding is separate.

ReplayCallSource.lean evaluates these identities in the existing diagnostic
Fp4 model against the retained32x179source table and both actual terminal
queries. All358column weights match sha384_call_pcs.branches; all next-row and
packing-padding weights are zero; both branches use the same intended use-root.
The source total and full-input-minus-constant total equal the verifier's
private claim. Actual input log14 splits into5row and9column coordinates.
Truncating the column weight to8coordinates changes all358weights, confirming
that the extra high-coordinate factor cannot be omitted by an adapter.

Validation: full check.py PASS4200, /tmp/call-source-audit.log. Runtime replay
PASS2queries, /tmp/call-source-opening.log. Exact compressed input/output,
source hashes and logs retained in results/call-source-opening. Source rows
are regression inputs only; the verifier remains a no-row proof verifier.
No executable protocol or proof bytes changed. Generic Python branch/compiler
refinement, Merkle/PCS soundness, transcript/QROM composition, full recursive
operand provenance and full NEAR1Pgas/PQ128/sub300k remain open.

### Canonical source openings: fixed-tree equality or hash collision

CallMerkleOpening.lean composes existing SHA384 fixed-source Merkle binding
with canonical u32 field-word serialization injectivity. An accepted claimed
word leaf either equals the fixed source leaf or yields distinct equal-hash
messages in the two actual finite path-query supports. The second theorem
transports this result to the interleaved antipodal pair consumed by weighted
PCS, for arbitrary weights (including adaptive or zero weights). No challenge
inversion, global hash injectivity, or low-degree inference from a root is used.

The independent row-to-LDE reconstruction helper now exposes its byte leaves
without changing root construction. The actual retained root is reconstructed
from256leaves. All16source branch openings across8query indices match those
canonical field words and their weighted antipodal pairs. The existing Lean
SHA384 path verifier accepts all16actual paths and rejects5mutations (leaf,
root, context, sibling and index). This is a regression using disclosed source
rows as reference data; no rows are added to the actual proof verifier.

Validation: full check.py PASS4202, /tmp/call-merkle-audit.log. Opening replay
PASS16/reject5, /tmp/call-merkle-opening.log. Compressed exact fixtures/results,
source hashes and logs retained in results/call-merkle-opening. The root remains
155656d5033f2996c935d8845c1addf3ee97d2d2e56f056c37ed9bda508ad89a6af28a6c756bc9f37d66915ddf5d1acc.

Boundary review: the existing representative theorem explicitly requires a
fixed close polynomial; Merkle binding does not establish one. The current
results only identify correct queried values relative to a fixed constructed
source, or an explicit collision. Adversarial oracle proximity/adaptive folding
and source recovery, plus hash probability/QROM composition, remain required.
Full NEAR1Pgas/PQ128/sub300k and NOT_PASSED gate remain open.

### Adaptive near-source composition and retained PCS error budget

CheckedHistoryNear.lean supplies the near-source counterpart to the existing
CheckedHistorySource far theorem. A wrong functional of a fixed jointly-close
polynomial tuple gives initial indexed-candidate absence through
weighted_virtual_no_initial, then the checked adaptive-history theorem bounds
acceptance. Later oracles may be adaptive; the explicit prechallenge snapshot,
weight and claim bindings remain required. The close tuple and its separation
from other candidates are hypotheses, not consequences of a Merkle root.

measure_call_pcs_budget.py instantiates the conditional terms from retained
proof geometry: degree128, domain512, seven folds and eight queries. The strict
extraction regime requires T≥385, so its best query term is (384/512)^8 =
6561/65536 ≈0.100112915 (only3.3203negative-log2 bits). The adaptive fold
numerator is508 over the challenge-field size; the separate source-far outer
numerator is3584. The isolated query term requires309queries for128bits,
478for198bits, and531for220bits. The latter are component-budget examples,
not claimed quantum-security conversions. Ext4 field terms independently
prevent this bound from certifying128bits, even with increased queries.

These are upper bounds under explicit ideal hypotheses, not attack-probability
lower bounds. The report excludes functional reduction, hash/extraction,
Fiat-Shamir/QROM, full recursion and NEAR errors. It makes no complete proof
size projection. The existing152200-byte batch remains a diagnostic size only.
A secure profile requires larger-field analysis and a stronger query/recursion
strategy; merely adding proofs of diagnostic correctness cannot establish it.

Validation: full check.py PASS4203, /tmp/checked-near-audit.log. Exact rational
query arithmetic and minimal query counts checked by the measurement script;
results/call-layer-certificates/ideal-pcs-budget.json records assumptions and
source hashes. No executable protocol or proof bytes changed. Full goal and
NOT_PASSED feasibility gate remain open.


### Actual Ext8 call proofs at309 and531 queries

sha384_call_ext8_pcs.py wires the existing Ext8 GKR/native kernel, weighted PCS
and canonical multiproof codec into the same2880-equation call workload. It
reuses the existing descriptor generator; its profile/magic are separate and
the trusted query count enters the initial transcript binding as well as PCS.
Source commitment root remains identical. No row data is disclosed to the
fresh verifier. Existing Ext4 call/proof behavior is unchanged.

Both profiles generated, encoded, decoded and verified in fresh processes,
alongside the existing compression proof. Eight negative tests reject
(truncation, trailing bytes, GKR coefficient, PCS authentication, changed
external digest/message/order, mismatched query budget), and five source
mutations fail equation/circuit checks. The309-query call proof is168896bytes;
with the existing120477-byte compression proof,5858-byte calls and731-byte
receipt, total295962bytes. The531-query call proof is205360bytes, mixed total
332426bytes. Prover/codec timings and exact binary hashes are in the retained
reports. This is a mixed-strength bundle: the compression proof is STILL
Q8/Ext4. Neither measurement establishes full PQ128 security or recursion.

Exact codec accounting identifies duplicated authentication for the same root,
context, leaf width, domain and query indices across the two terminal branches.
Removing one copy would save65832bytes at309queries and84000at531queries,
projecting mixed totals230130and248426bytes. Those are projections, not encoded
or verified smaller proofs. The next concrete optimization is canonical shared
source authentication; distinct branch weights must remain independently bound.

Validation: test_sha384_call_ext8_pcs.py with /tmp/libnear_call_ext8.so passes
at both budgets; logs /tmp/call-ext8-q309.log and /tmp/call-ext8-q531.log. Native
library built from the existing kernel_ext8.rs. Artifacts retained under
results/call-ext8-q309 and results/call-ext8-q531; exact comparison with source
hashes in results/call-ext8-profiles.json. No Lean change; last full audit4203
remains applicable. Full NEAR1Pgas/PQ128/sub300k gate stays NOT_PASSED.

### Shared Ext8 source authentication and complete call decode verification

Implemented optional NP8WMP02 transport in pq384_ext8_weighted_codec.py.
Source multiproofs share bytes only for exact equality of verifier-derived
root, context, domain half, leaf width and ordered query indices. No wire
references or counts select aliases. Encoding verifies the full proof and
requires identical compressed witnesses for aliases; decoding reconstructs
both branches. Each branch retains its own transcript-bound weights and point.
NP8WMP01 remains supported and default encoding retains identical old bytes.

Found and fixed a verification omission in sha384_call_ext8_pcs.decode:
codec.decode authenticates openings and replays the transcript, but does not
check query fold consistency. The call decoder now explicitly invokes
pcs.verify after decoding. Earlier fresh-process logs therefore established
less than complete call verification; both retained old proofs now pass the
complete decoder, as do both new shared proofs. The older Ext4 codec already
invokes its full verifier and does not have this omission. Regression fault
injection tests the parser-to-verifier boundary; it is not a cryptographic
forgery or proof of exploitability.

Actual measurements (bytes):
- 309 queries: call168896 ->103064; saved65832; mixed bundle230130.
- 531 queries: call205360 ->121360; saved84000; mixed bundle248426.
These replace the previous projections with encoded, freshly verified results.
The accompanying compression proof STILL uses Q8/Ext4. Neither bundle proves
PQ128, full recursion or full NEAR1Pgas. The feasibility gate stays NOT_PASSED.

Validation: test_call_ext8_shared_codec.py PASS for both budgets, old-byte
parity, canonical roundtrip, eight rejection cases per budget, five geometry
key separation checks and fresh-process conjunction verification without rows.
Artifacts: results/call-ext8-shared-q309 and results/call-ext8-shared-q531.
Heterogeneous-source test_ext8_weighted.py PASS at8/309queries: shared encoding
retains every distinct source; existing13negative cases and independent FFT
root comparison pass. Reports/source hashes retained in
results/ext8-weighted-shared.json and results/ext8-shared-codec-sources.json.
Logs /tmp/call-ext8-shared.log and /tmp/ext8-weighted-shared.log. No Lean changes;
last full audit remains4203. Codec implementation refinement remains open.

### Complete Ext8 execution verifier from external spec and source roots

verify_ext8_execution.py connects the existing Ext8 bus/local/GKR/weighted PCS
components in one verifier. It requires external spec/roots, checks reduction
shape and global bus products, binds auxiliary commitments/finals before local
challenges, replays local proofs, constructs the terminal circuit, verifies
zero-root GKR, derives source/auxiliary opening branches and the private claim,
and invokes full binary PCS verification. It never consumes the prover's
opening.json as authority. Optional --compression-receipt checks the existing
canonical SHA384 node-chunk contract, enabling reuse for the upcoming all-Ext8
compression pipeline. That compression pipeline has NOT yet been measured.

The previous retained capture verified PCS against externally supplied opening
parameters. The new test derives those parameters through the full reduction
and independently compares them with the capture. It passes on the retained
prepared193 execution at309queries, including fresh-process replay without
source rows and11negative cases: bus final, auxiliary root, local round, GKR
input, table/final counts, extra prover claim, external root/spec, opening
authentication and query budget. Captured reduction, opening parameters, binary,
report and test log are retained under results/ext8-complete-verifier.
The prepared execution runner now invokes this complete verifier after capture
and writes complete-verifier.log, in addition to the earlier PCS-only check.
That runner modification is not a new full proving run; the verifier itself
was exercised on the retained actual full capture.

Validation: test_ext8_execution_verifier.py PASS, log
/tmp/ext8-execution-verifier.log. No Lean changes; no new formal implementation
refinement or QROM/security claim. Opening remains620632bytes; prior671960-byte
subtotal still exceeds300000 before envelope. Full NEAR/PQ128 feasibility gate
remains NOT_PASSED. Next: use this verifier with fresh Ext8 auxiliary/local/GKR
compression proofs, rather than carrying forward the Q8/Ext4 compression part.

### Complete Ext8 binary envelope and first all-Ext8 compression run

ext8_execution_codec.py encodes source/auxiliary roots, bus finals, local
sumchecks, terminal GKR and the weighted PCS opening. Counts are derived from
the trusted spec and reconstructed terminal circuit. Decoder checks canonical
Ext8 scalars and source roots, then performs complete reduction/PCS verification.
A checked-prefix helper avoids compiling the terminal circuit twice at decode.
verify_sha384_call_ext8_bundle.py now accepts explicit --compression-format
ext8 (default remains ext4), checks the canonical compression receipt, then
verifies the Ext8 envelope and same-root call proof at the trusted query count.
The Ext8 conjunction path has not yet been exercised on a compression proof.

Prepared193 envelope measurement:672320bytes, including620632-byte opening and
51688bytes of commitments, finals, local/GKR scalars and framing. Static AIR/spec
and external receipts remain excluded. Canonical roundtrip, fresh CLI verifier
and9negative cases pass. This is the actual full binary envelope replacing the
previous671960-byte subtotal estimate; it still exceeds300000bytes. Artifacts
and source hashes are in results/ext8-complete-verifier/envelope*; test log
/tmp/ext8-execution-envelope.log. No Lean changes or new security certificate.

Generalized test_ext8_execution_reduction.py to accept --statement,
--source-directory and optional --compression-receipt, preserving the default
prepared fixture. External source hashes are recorded; authoritative binding
is equality of reconstructed packed source commitments to the external roots.
Started the actual24-node SHA384 workload (2048x5234,32x1666,32x191,32x179) with
Ext8 local/GKR/PCS and309queries under an8GiB cgroup cap. All four roots match,
Ext8 auxiliaries and four local tables finish, and GKR proving finishes. Full
PCS/verification/size result is still pending at this checkpoint.

Live run: exec session24454, Python PID1725108, log
/tmp/ext8-compression-q309.log, intended capture /tmp/ext8-compression-q309,
report /tmp/ext8-compression-q309-report.json. External inputs are
/tmp/nearproof-ext8-node-native-v2/statement.json and
/tmp/nearproof-ext8-node-batch (source files and expected-use.json).
An initial invocation from repo root exited2 before starting Python; the active
run uses research/near-compression as cwd. Do not restart the active run without
checking its handle/process and terminal result. This checkpoint does NOT claim
an all-Ext8 compression proof, PQ128 or a passed full-NEAR feasibility gate.

### Native Ext8 tensor weights; compression run reaches PCS

Added near_ext8_tensor_weights to the existing Rust kernel and an optional
Kernel.lane_weights adapter. The kernel evaluates the exact column-major
current/next tensor a[c]*r[i]+b[c]*s[i]; Python still constructs the independently
specified upper-zeta and row-weight inputs. ABI rejects invalid capacity,
zero dimensions, null pointers, overflow and noncanonical scalar buffers.
Existing libraries without the symbol retain the reference path. Weighted PCS
uses the optional adapter; its verifier and transcript are unchanged.

Validation:12small randomized cases and a complete2048x128 lane (262144Ext8
values) match the Python reference exactly. Representative single-pass timing:
reference4.81568s, native0.150686s,31.96x for tensor materialization only. Three
malformed ABI cases and three Python input checks reject. The heterogeneous
weighted PCS test passes at8/309queries, with exact proof equality between
native and reference weight paths at8queries, existing13negative cases,
shared/unshared codec checks and independent source-root comparison. This is
not an end-to-end speedup or formal Rust refinement theorem. Reports and source
hashes: results/ext8-native-tensor; logs /tmp/ext8-native-weights.log and
/tmp/ext8-native-weighted-pcs.log. No Lean changes.

The original all-Ext8 compression run (session24454/PID1725108) is still running
with its originally loaded reference tensor code; it was not restarted to use
this optimization. At541elapsed seconds it logged Starting weighted PCS after
GKR verification and independent coefficient-target parity. Full proof result
and size remain pending. The prepared measurement utility
measure_ext8_compression_envelope.py requires a terminal PASS prover report,
checks the canonical compression receipt, builds the complete envelope,
verifies a same-root all-Ext8 call/compression conjunction in a fresh process,
and accounts for the full PCS geometry and external receipt/call bytes.
It is syntax-checked but awaits the actual compression output for execution.
Full NEAR/PQ128/sub300k feasibility remains open.

### Combined Ext8 PCS budget: two query terms must be counted

measure_ext8_bundle_budget.py instantiates the existing conditional ideal
source-far/fold bound for both the compression geometry (degree262144,
domain1048576,18folds) and call geometry (degree128,domain512,7folds), using
Ext8 field cardinality. It sums the field numerators and BOTH query terms with
exact Fraction arithmetic, then checks minimal equal query counts at selected
component targets. No independence between the two proof events is required
for their union bound; each component's theorem premises remain explicit.

At309queries per proof, the conditional two-PCS bound has127.2466negative-log2
bits, so this bound alone does not certify128bits even in its ideal model.
At531queries it has219.2722bits. Minimal equal query counts for this restricted
PCS budget are311for128bits,480for198bits and533for220bits. Functional reduction,
local/GKR/bus errors, source-case coverage/extraction, hashes and Fiat-Shamir/QROM
remain excluded. These numbers are neither attacks nor quantum-security
conversions, and are not a complete parameter prescription. This corrects any
interpretation of309queries as sufficient for a complete two-proof128-bit
bundle. The original309-query run remains useful for measured proof geometry.

Validation: exact rational threshold/minimality checks PASS; artifact
results/ext8-bundle-conditional-budget.json with source hashes, log
/tmp/ext8-bundle-budget.log. No Lean changes; existing conditional theorem
hypotheses have not been discharged for the full protocol. The original
compression process remains active in session24454/PID1725108, in weighted PCS
at696elapsed seconds with about4.9GiB resident memory. No result yet.

### Actual all-Ext8 SHA384 compression/call bundle:1,863,197bytes

The original session24454/PID1725108 completed successfully; no process remains
from that run. All four packed source roots match the externally fixed node
statement. Ext8 auxiliaries balance; four local sumchecks and58-layer GKR prove
zero, the independent coefficient-functional check agrees, and weighted PCS
passes both in-process and complete fresh-process verification. Mutated local
round and corrupted source trace checks reject. Measured local proving23.970s,
GKR156.115s, PCS332.411s; these exclude other preparation/reference checks and
are not total wall time. This run used the original reference tensor path.
Its8GiB cgroup cap was raised to12GiB while active after checking available host
memory and no OOM events; the run was never restarted.

measure_ext8_compression_envelope.py now executes successfully. Actual sizes:
- Complete compression envelope:1,753,544bytes.
- Of that, weighted PCS opening:1,636,192bytes; reduction/framing:117,352bytes.
- Same-root shared Ext8 call proof:103,064bytes.
- Calls5,858bytes plus mandatory receipt731bytes.
- Combined:1,863,197bytes (6.21times the300000-byte target).
Static trusted AIR/spec remain external. Both components use Ext8 at309queries;
this is no longer the earlier mixed Q8/Ext4 compression experiment. Fresh
conjunction verification passes without disclosed rows. The binary codec test
also passes canonical roundtrip, independent fresh CLI verification and9
rejection cases. The two independently generated envelope binaries match.

PCS accounting: source leaves501496, source authentication237648, fold
leaves212096, fold authentication680592, header4360bytes. Opened values alone
sum713592bytes. Serialization-only removal of authentication cannot bring this
configuration below300000bytes; this is a configuration measurement, not an
impossibility result for redesigned protocols. Query/source-opening reduction
and a better folding/authentication schedule are necessary design priorities.

Artifacts, source hashes, complete proof, compressed statement/reduction/prover
report, fresh verification logs and codec rejection report are retained under
results/ext8-compression-q309, with manifest.json. Working capture remains
/tmp/ext8-compression-q309; test logs /tmp/ext8-compression-envelope.log and
/tmp/ext8-compression-codec-test.log. All three relevant exec sessions24454,
76560and75826 are terminal PASS. Updated slice-feasibility-gate.json with the
actual failed size target and prepared complete-envelope size672320bytes.
The gate remains NOT_PASSED. Existing two-PCS budget at309queries already fails
to certify128ideal bits before excluded errors. No PQ128, QROM, full recursive
verifier, full NEAR1Pgas, or formal implementation-refinement claim is added.
No Lean changes; last full Lean audit remains4203.

### Joint rate/grouped-fold screen calibrated to all-Ext8 compression

Reviewed the existing WHIR audit before choosing more work. The pinned primary
implementation remains worldfnd/whir afec1fac27c1c8cc7331aa5668bc9800f104d92c:
https://github.com/worldfnd/whir/blob/afec1fac27c1c8cc7331aa5668bc9800f104d92c/src/protocols/params/regime.rs
Its Unique/Johnson formulas are counterfactual inputs, not soundness theorems
for our implementation. Capacity/grinding remain excluded. The primary paper
https://eprint.iacr.org/2024/1586.pdf again returned403. No unseen theorem or
correction is assumed proved. The existing rate-shift sharpness result and
prior query-only screen already explain why a query-count substitution is
insufficient; this work extends geometry rather than repeating that audit.

screen_ext8_grouped_geometry.py calibrates the actual compression opening
1636192bytes and shared call opening83536bytes exactly, hence the1863197-byte
combined baseline. It retains source widths/packings and143469bytes of other
reduction/call/receipt overhead. It screens blowups4/16/64/256, groups of1..4
binary folds, and current/Unique/Johnson agreement factors. Query counts use
exact rational minimality for TWO query terms at hypothetical128/220-bit
component budgets. Dynamic programming optimizes all allowed group schedules
for each sampled geometry, across four deterministic query samples per case.
All quadratic messages remain; only intermediate roots/openings are grouped.

Crucially, grouped queries account for the entire folded coset, not one pair.
An initial model retained old paired-leaf Merkle trees; the main screen instead
permits NEW coset-packed commitment leaves. This is a protocol/root-layout
change. Heterogeneous source x^(D/d) embeddings reduce distinct queried values;
at least paired source leaves are retained. Soundness for missing intermediate
roots, new layouts, alternative rates and stronger extraction remains unproved.
This is not an estimate of the full upstream WHIR protocol: code switching,
OOD traffic and its error terms are not included.

Best sampled fixed-source results still FAIL300000bytes:
-128-bit query-only union target: Johnson/blowup256/q33,526197–530277bytes.
-220-bit query-only union target: Johnson/blowup256/q57,765541–773733bytes.
These budgets omit field, functional, list/extraction, hash and QROM errors;
220 is not a claimed quantum-security conversion. Source packing/pooling and
code switching were not optimized, and this is not a universal lower bound.
The geometry does not justify a large standalone formalization of grouping or
Johnson extraction as the next step. Source commitment layout/opening reduction
must be included before a candidate has useful end-to-end size headroom.

Validation: exact measured-byte calibration and36independent exhaustive cases
PASS. The independent test enumerates all scalar coset positions, computes
Merkle boundaries level by level, and exhaustively searches fold compositions
through7bits for paired and coset-packed layouts, heterogeneous sources,
repeated queries and shared roots. Artifacts: results/ext8-grouped-geometry.json
and results/ext8-grouped-geometry-validation.json; log
/tmp/ext8-grouped-geometry.log. No executable security profile or Lean theorem
changed; full NEAR/PQ128/sub300k gate remains NOT_PASSED.

### Joint source packing and phase pooling with shared-root constraints

Added screen_ext8_joint_packing.py. The optimizer jointly chooses per-source
power-of-two packing (through the next power covering width), global maximum
degree, groups of1..4folds and the call schedule, subject to base-field domains
at most2^27. It enforces that some source actually attains the selected maximum
degree. For the external use table, compression and call proofs MUST use the
same packing, blowup and coset leaf size; independent minima that would require
different roots are rejected. This is a constrained geometry search, not a
new prover/security profile. Existing runtime lane/degree caps are not imposed
on all candidates. Grouped geometry gained an optional fixed-first-group
argument so independently checked costs can replay selected schedules.

Separate-source search: best sampled totals at hypothetical query-only union
targets128/220bits are502157–506277 and723197–727365bytes respectively. Both
use the unproved-for-us Johnson formula at blowup256 (q33/q57). Eight brute-force
small packing cases match the optimizer, and96selected full-size geometries
match the independent previously calibrated estimator, including shared-root
layout and domain checks.

Phase pooling keeps the externally bound use table separate. Other prechallenge
source tables pool into2048x7091; postchallenge auxiliaries pool into2048x296;
uses remain32x179. Shorter tables require a repeated-row embedding and per-table
functional/column ownership binding. Those implementation/formal obligations
are not discharged here. Source roots remain separated across the bus challenge;
no future auxiliary commitment is moved before its challenge. Modeled cell
count grows10842240 ->15134304; only240root bytes are removed from fixed
upstream overhead. The same constrained optimizer gives423005–426253bytes at
the128-bit query-only target and597605–600861 at220bits. Best source packings
are[128,32,4] and[128,32,8], max degree262144. Eight independent brute-force
cases and96full-size replays pass for this pooled scenario too.

These are NOT measured proof bytes, total soundness budgets or quantum-security
conversions. Query factors, changed Merkle layouts, pooling/embedding, extraction,
Fiat-Shamir/QROM and additional errors remain unproved/unimplemented. Neither
separate nor pooled search reaches300000bytes. Do not start a large standalone
pooling/Johnson formalization based on these results: the next useful model
must include actual code switching with stage-specific query counts, and its
OOD/constraint traffic, rather than one fixed rate/query budget throughout.

Artifacts: results/ext8-joint-packing-{geometry,validation,manifest}.json and
results/ext8-pooled-packing-{geometry,validation}.json. Scripts run successfully;
logs /tmp/ext8-joint-packing.log and /tmp/ext8-pooled-packing.log. Existing36
independent coset/schedule tests still pass. No Lean changes; full NEAR/PQ128/
sub300k feasibility remains NOT_PASSED.

### Code-switch ledger includes stage queries, OOD and field errors

Inspected pinned WHIR implementation afec1fac27c1c8cc7331aa5668bc9800f104d92c,
src/protocols/{code_switch.rs,params/{regime,sumcheck,code_switch,layout}.rs}.
Primary source:
https://github.com/worldfnd/whir/tree/afec1fac27c1c8cc7331aa5668bc9800f104d92c/src/protocols
The source commits a target after sumcheck, samples OOD points/answers, opens
the prior IRS, then draws constraint-mixing coefficients. Source query, OOD
list-separation and mixing errors are separate; sumcheck also charges proximity
gaps and polynomial identities. No grinding/capacity-conjecture credit used.

Added screen_ext8_code_switch.py. It REPRICES the existing joint/pooled packing
and group schedules (not a new global optimization) with stage rates stepping
B_next=B*2^(k-1), either unbounded or capped256. Queries are recomputed at each
stage. Both proofs share a per-error allocation sized for2*sum(k)+3*stages;
every stage charges k MCA/identity terms plus query/OOD/mixing. Each switch
includes96*kquadratic bytes,48root bytes and32bytes per OOD answer, plus
coset-packed source/intermediate Merkle openings. Initial functional reduction,
terminal scalars and fixed upstream costs remain charged. OOD sample count is
at least one and is increased until its source-formula bound fits.

Critical finding: canonical Johnson MCA error from the pinned code is
(21^5/48)*message_length*B^(5/2)/|Fp8|. It cannot be omitted when selecting a
high-rate-inverse profile. Exact squared comparisons avoid irrational rounding;
the printed additive ledger uses a conservative rounded-up square root. List
size is10B, identity error2L/F, and mixing error(t_ood+q*2^k)*L_target/F.
These are SOURCE-FORMULA transcriptions, not newly proved bounds for our PCS.
The script requires the exact pinned Git HEAD and clean formula files.

Results across256sampled runs:
-128-bit illustrative component target: best conditional-ledger-passing case
 is pooled Johnson/stepping startingB256,433469bytes.
-220-bit illustrative component target: NO tested Johnson candidate passes the
 MCA field allocation. Best passing Unique/capped256 case startsB4 and costs
 1413653bytes. This does not imply a general impossibility for Ext8 or PQ128;
 220is not a derived quantum target and schedules were not reoptimized.
Neither tested family supplies a sub300000-byte candidate or certified security.
Earlier query-only Johnson220-bit projections must not be selected as parameters.
Theorem mapping, common-candidate/extraction obligations, initial batching,
local/GKR/bus errors and Fiat-Shamir/QROM remain outside this conditional ledger.

Validation:30independent source-log/formula cases (including odd-rate logarithms)
and256exact per-stage additive ledgers PASS; OOD/query minimality, known Unique
case and Johnson field-budget rejection checked. Artifacts: readable decision
summary results/ext8-code-switch-ledger.json; full ledger in matching.json.gz;
validation and manifest JSON alongside. The test accepts the full.gz archive;
rerunning the screen writes a full JSON to the requested output path. Log
/tmp/ext8-code-switch-ledger.log. No Lean change or accepted runtime profile
change; full NEAR/PQ128/sub300k gate remains NOT_PASSED.


### 2026-10-16: affine terminal rewrite and weighted expansion lemmas

The actual Ext8 compression terminal circuit contains long constant-multiply
Horner chains. Experimental rebalance_terminal_linear.py distributes public
constant weights through add/sub, retains shared/nonlinear boundaries, combines
weights and balances emitted sums by depth. Existing accepted compiler/verifier
remain unchanged. Replay from committed ext8-compression-q309/reduction.json.gz
reconstructs the terminal circuit via reduction_prefix.

Measured layout: 58 -> 20 layers; 323178 -> 149506 gates; 1124 -> 384
sumcheck rounds. Calculated GKR scalar payload 111616 -> 38144 bytes, saving
73472 bytes. Arithmetic node count increases 84338 -> 89475. Zero, one and
seeded random Ext8 differential vectors pass; the structural layer certificate
passes. These are not a universal semantic equivalence proof or a newly
measured complete proof. Last verified combined envelope remains 1863197 B.

TerminalWeightedExpansion.lean proves weighted collector expansion, transport
under retained-register equality, and its specialization to an executed acyclic
DAG. All three compile; full axiom audit PASS at 4206 theorems/examples. The
initial attempted file creation used the wrong relative path; repaired before
this validation. Remaining refinement obligations include coefficient merging,
constant accumulation, arbitrary heap reassociation, emitted-node simplification
and recursive mapping. Thus these lemmas do not certify the whole Python pass.

Retained result and manifest: results/ext8-terminal-linear-rebalance*.json.
Replay command is in the manifest. Next: finish semantic rewrite validation,
then generate and independently verify the optimized GKR/PCS proof and measure
the complete envelope. Full NEAR 1 Pgas, PQ128 and sub300000 B remain unproved;
slice-feasibility gate stays NOT_PASSED.


### 2026-10-16: exact symbolic rewrite check and aggregation algebra

Added check_terminal_linear_equivalence.py, an independent exact symbolic
normalizer. It expands affine arithmetic, combines coefficients in Ext8, and
interns nonlinear products by normalized operand expressions. Source and target
must normalize to the identical root expression; no random identity testing is
used for this check. On the actual terminal DAG, PASS with 133099 forms,
26272 atoms and maximum 10877 terms per form, in 1.19 seconds. This implies
all-input equality under the checker/field implementation; the Python checker
and its arithmetic refinement are not Lean verified. It does not certify input
block metadata, security, or the full state transition.

Validation: 100 generated rewrite pairs pass symbolic normalization and 300
independent concrete evaluations. 100 changed-root variants and 9 malformed or
changed circuits are rejected. Replay from the committed reduction reproduces
the 20-layer, 38144-byte calculated GKR scalar payload. Results and hashes are
updated in ext8-terminal-linear-rebalance*.json; negative/generated test counts
are retained in ext8-terminal-linear-equivalence-tests.json.

TerminalWeightedAggregation.lean proves reference association-list insertion,
coefficient aggregation, zero-weight deletion, and permutation preserve weighted
value. Combined with the expansion lemmas these cover more of the algebra,
but do not establish Python dictionary/heap/compiler refinement. Full axiom
audit PASS at 4210 theorems/examples. Accepted compiler/verifier unchanged;
next step is an explicitly selected optimized experimental profile and actual
GKR/PCS generation plus independent verification. Last verified complete size
remains 1863197 bytes; full NEAR/PQ128/sub300000 B gate remains NOT_PASSED.


### 2026-10-16: explicit affine profile and heap composition

Added externally selected terminal profile affine-v1. Both prover and verifier
rebuild the baseline terminal DAG, apply the affine rewrite, require unchanged
private-input metadata and run exact symbolic equivalence validation. Baseline
remains the default. Binary envelope NPEX8002 is accepted only when the caller
selects affine-v1; baseline keeps NPEX8001. GKR additionally binds the rebuilt
layout in its transcript. Profile selection propagates through the complete
verifier, envelope codec, same-root conjunction and measurement commands.

Small GKR roundtrips pass for both layouts; cross-layout proofs, unknown profile,
changed root and changed metadata are rejected. A retained baseline envelope
with its header relabelled as affine-v1 is rejected at the GKR endpoint. Reports:
results/ext8-terminal-profiles-tests.json and ext8-baseline-relabel-test.json.

TerminalHeapBalance.lean proves arbitrary frontier reordering and pairwise
merge routes preserve the sum, weighted-leaf arithmetic routes yield their
claimed value, and expansion/aggregation/zero removal/permutation/heap merging
compose into root equality. Concrete route extraction, constant accumulation,
and full Python/refinement obligations remain. Full axiom audit PASS:4213.

At this checkpoint the full q309 affine run is LIVE in session43126,
PID1884997, log /tmp/ext8-affine-q309.log, capture /tmp/ext8-affine-q309,
report /tmp/ext8-affine-q309-report.json. All local tables and GKR generation
have completed; input-obligation/PCS/completion checks remain. A baseline codec
regression runs in session55840/PID1884998 with log
/tmp/ext8-baseline-profile-codec.log. Do not restart either while live.
No new complete-proof size or security claim is made at this checkpoint.

Baseline profile regression subsequently completed PASS (session55840 terminal):
full canonical roundtrip/re-encode, fresh verifier, 10 negative cases, and exact
byte equality to retained results/ext8-compression-q309/compression.bin. Report
results/ext8-baseline-profile-codec.json. The additional relabelled-header case
was tested separately and retained above. Affine run43126 remains live.


### 2026-10-16: complete affine Ext8 slice and faster independent contraction

Full affine run43126 is TERMINAL PASS. Fresh complete local/GKR/PCS verification,
canonical envelope roundtrip/re-encode, fresh same-root call/compression
conjunction and 11 malformed/tampered/profile cases pass. Measurement60544 and
codec74789 are also TERMINAL PASS. Do not restart these runs.

Retained results/ext8-affine-q309/ contains envelope, compressed statement and
reduction, prover/codec/measurement reports and verification logs plus manifest.
Actual byte accounting (baseline -> affine):
- GKR scalars:111616 ->38144; 58 ->20 layers.
- Compression reduction/framing:117352 ->43880.
- PCS opening:1636192 ->1644656 (changed transcript/query paths).
- Compression envelope:1753544 ->1688536.
- Same-root call proof103064, receipt731, calls5858 unchanged.
- Combined:1863197 ->1798189, saving65008 bytes (3.489%).
Static AIR/spec excluded as before. Result remains5.994x300000; no full NEAR,
recursive verifier, PQ128/QROM or complete proximity-soundness claim. q309 is a
comparison profile, not a certified128-bit setting. Slice feasibility gate
remains NOT_PASSED. PCS now dominates the residual size.

Measured local proving24.630s, GKR81.866s, PCS137.838s and PCS verification0.949s.
The earlier baseline was GKR156.115s and PCS332.411s; this run also includes the
previous native tensor-weight optimization, so do not attribute every timing
change to terminal balancing or treat these single runs as controlled benchmarks.
The prover source at launch is equivalent to fc7c85f07 and used the slow tensor
coefficient check; later contraction integration was not used for this proof.

During the run, added an independent separable coefficient-claim implementation.
It retains Python Mobius conversion and contracts base-field coefficients with
two row-weight vectors before multiplying by column weights, avoiding the large
Ext8 weight tensor. 36 small cases agree with both the old tensor method and
direct cyclic-row evaluation. Actual2048x128 lane:5.476s ->0.471s (11.64x
microbenchmark only). All8 actual source/auxiliary branches sum to the independently
verified GKR input claim; contraction19.030s, full standalone validation84.186s.
Report results/ext8-coefficient-contract-execution.json; session7420 terminalPASS.

SeparableCoefficientClaim.lean proves the algebraic row-contraction identity;
full axiom audit4214 PASS. Python integer/Ext8 refinement remains outside the
lemma. Future prover diagnostics default to --coefficient-check contract;
--coefficient-check tensor retains the independent slower reference. This only
changes the witness-side check, not verifier acceptance or proof bytes. The
new path was exercised on all actual branches; no redundant full proof rerun
was needed for replacing that check. All work remains directed at full1Pgas,
hash-only PQ128 succinct state transitions, which are not yet achieved.


### 2026-10-16: lossless derived-fold transport

PCS dominated the measured affine bundle. Added NP8WMP03 transport that omits
fold-leaf scalars fixed by preceding authenticated source/fold pairs, the public
fold challenge, and transcript-derived query indices. A queried leaf can have
one or both coordinates derived; repeated derived coordinates must agree.
Source aliasing is retained. Reconstructed complete leaves pass the unchanged
Merkle multiproof check; decode is followed by the original full PCS verifier.
No roots, transcript messages, samples or query counts were changed. Existing
transport versions/default encoding remain supported; prover option
--derived-fold-transport selects the new representation.

Actual q309 compression opening:1644656 ->1528144 bytes, removing3641 Ext8
scalars (116512 B). Decoded PCS JSON proof is exactly identical to the prior
proof, including all queries and Merkle paths; canonical re-encode passes.
Source value bytes513400, source path bytes237744, remaining fold values96992,
fold path bytes675648, header4360. These figures explain why transport alone
cannot deliver the final300000-byte requirement with this proof geometry.

Small tests cover terminal-only degree2 and heterogeneous degrees2/8, duplicate
source roots with different weights, query budgets1/8/80, duplicate samples,
and both-coordinate derivation.15 invalid transport/context cases are rejected,
including conflicting derived coordinates and noncanonical retained scalars.
The complete envelope independently passes canonical roundtrip/re-encode,
fresh external-statement verification and11 tampering/profile cases. Fresh
same-root call/compression conjunction also passes. All sessions24631,35362,
81216 and Lean audit77064 are terminal PASS.

Complete compression envelope1572024 bytes. With unchanged103064-byte call
proof,731-byte receipt and5858-byte calls, combined1681677 bytes. Savings versus
the previous1798189-byte affine bundle:116512 (6.48%); versus pre-affine1863197:
181520 (9.74%). Still5.606x300000. Retained artifacts, reports, logs and source
hashes:results/ext8-affine-derived-q309/. The archived prover report is from
the original proof generation; this experiment transcodes that exact proof.

DerivedFoldTransport.lean proves the fold expression matches affine RS pair
decoding, reconstruction of a selected scalar, reconstruction along a consistent
query chain, and preservation of predicates on that chain. Full axiom audit4218
PASS. These are algebraic/per-query completeness lemmas, not a refinement of
Python bytes, shared-leaf placement, Merkle extraction or quantum soundness.
The original q309 security limitations remain; slice-feasibility gate stays
NOT_PASSED. Full NEAR1Pgas/hash-only PQ128 correctness remains the objective.
Next structural work must address source-value and authentication-path cost,
with an explicit soundness budget for any changed folding/commitment protocol.


### 2026-10-16: pooled-bank logical row projection foundation

Started concrete source/auxiliary pooling rather than another parameter screen.
An important failure case is now retained: logical rows[10,20] in physical
rows[10,20,99,77], next-row weight at logical row1, must return10. Extending the
row point with zero and using the physical cyclic shift returns99. Pooling
must preserve each logical table's own wrap boundary.

ext8_pooled_weights.py instead masks the logical row equality weights and their
logical cyclic predecessor permutation before applying the full physical-row
upper-zeta transform. Column weights scatter into fixed bank intervals, and
multiple terms add. Unused physical cells may be arbitrary; no repeated-row or
zero-padding premise is needed for these projected functionals. This resolves
the functional obstacle behind the older screen's repeated-row placeholder,
but does not yet implement the source-bank commitment/protocol mapping.

Proposed bank layout from the actual trusted spec:
- pre-bus source bank:2048x7091, tables0/1/2 in fixed column intervals;
- post-bus auxiliary bank:2048x296, all coordinate columns;
- separate use source:32x179, preserving its existing source geometry.
The phase_layout function records these groups; transcript-phase enforcement
and external source-root mapping are still integration work.

Validation:9 coefficient-vs-direct functional cases,39 dense-vs-compact beta
cases,9 arbitrary-unused-cell invariance cases,5 malformed-term rejections and
the explicit wrong-cyclic-shift counterexample PASS. The actual table0/table1
seam at global columns5120..5247 was also tested:114 columns from2048 rows,
14 columns from32 rows, with random unused physical cells. Coefficient/direct
identity and dense/compact beta identity PASS (2.351s and9.831s respectively).
Source hashes and retained opening descriptor hash are recorded. Test61167
and final audit35913 are terminal PASS.

PooledRowFunctional.lean proves masked physical coefficient dots equal logical
row dots, current-row evaluation, logical cyclic-next evaluation, their linear
combination, and arbitrary bounded cell scattering through the full coefficient
transform. The latter composes existing dual-Mobius and scatter lemmas and
allows repeated cells to add. Full axiom audit4223 PASS. The compact beta
factorization and Python/mutable transform refinement are not yet proved by
this module; compact beta has numerical parity checks, including the real seam.

Artifacts:results/ext8-pooled-weights*.json and ext8-pooled-seam.json. Accepted
verifier/PCS unchanged; last measured combined bundle remains1681677 bytes.
No pooled proof-size, PQ128 or full NEAR1Pgas claim. Next: combine a bank's
logical weight terms BEFORE allocating coefficient/weight states (do not send
three aliases of the7091-column bank through the current state allocator),
introduce an externally derived pooled weight-family profile and implement its
commitment mapping. Preserve logical next-wrap and source/auxiliary chronology.
Full NEAR1Pgas/hash-only PQ128 correctness and sub300000 B remain open;
slice-feasibility gate stays NOT_PASSED.


### 2026-10-16: pooled PCS weight family and compact mask algebra

Integrated the externally supplied pooled weight descriptor into weighted PCS.
A branch is either the legacy row_point/lanes descriptor or a physical bank
with terms. Exact schema validation is required. Any pooled descriptor selects
the distinct near-pq384-ext8-pooled-weighted-diagnostic-v1 transcript domain;
proofs cannot choose this family. All three binary transports derive the profile
and lane count from the trusted descriptors. The existing execution verifier
still derives legacy descriptors: full execution-bank mapping is NOT integrated.

Native tensor_weights now accepts explicit row and column factors, allowing
logical row masks. A pooled lane sums its logical terms BEFORE allocating its
sumcheck state; all-zero terms are skipped. Small tests observe4 pooled weight
vectors for4 bank lanes with4 logical terms, rather than16 duplicated vectors.
Mixed pooled/legacy source degrees, aliased legacy roots, overlapping terms,
native/reference weights, q8/q309 proofs and all3 transports PASS.16 malformed
shape/transcript/profile cases are rejected. Legacy weighted tests and actual
retained derived-codec roundtrip/byte parity PASS; native tensor regression
including262144 elements and old-library fallback PASS.

Actual seam proof:2048x128, degree262144, one committed lane, combining114
columns from a2048-row logical table and14 from a32-row logical table. q309
pooled PCS generation, reference verification, binary roundtrip and fresh JSON
and binary verification PASS. Commitment2.515s, PCS proving13.105s, fullrun20.135s.
Component transport926272 bytes. This is NOT the full7091-column source bank,
not the auxiliary pool, and not a new complete execution size measurement.
The last verified complete slice bundle remains1681677 bytes. Retained fixture,
proof, reports, logs and hashes:results/ext8-pooled-pcs/. Source rows are not
required by the archived functional-statement/binary verification interface.
All test sessions55288,86306,64557 and audit1064 are terminal PASS.

PooledWeightMLE.lean proves upper-zeta preserves the logical prefix mask, the
mask's multilinear extension has the exact high-row-bit product(1-u), and the
same compact factor applies to the actual masked dual transform. These apply
to both logical current and cyclic-next row weights and close the previously
unproved ROW part of the compact beta formula. Full axiom audit4226 PASS.
Python/Rust refinement, full packing composition, execution binding and
proximity/QROM/PQ128 soundness remain separate obligations.

Next integration: derive three physical bank descriptors from the logical
spec/GKR private weights: source0/1/2 at2048x7091; all auxiliary coordinates at
2048x296; use source at32x179. Candidate packings128/32/4 fit current degree/lane
caps. Keep source banks before bus challenges and auxiliary bank after them.
A dedicated externally selected commitment profile must enforce logical-root
aliases and derive term offsets/heights, rather than accept prover metadata.
The logical spec can remain unchanged, preserving the existing use-root call
binding if its contract checks permit it; verify this before claiming call-proof
reuse. Sum terms into one state per bank lane as implemented here. Full-pool
memory/commitment overhead still needs measurement. No gate is passed by this
component work: full NEAR1Pgas, hash-only PQ128 correctness and sub300000 B
remain open; slice-feasibility stays NOT_PASSED.

## 2026-10-16 — Full execution integration of phase-pooled commitments

Added externally selected `phase-pooled-v1` alongside unchanged `separate`.
The verifier derives three banks from the logical AIR: source0/1/2 at
2048×7091, packing128; all auxiliaries at2048×296, packing32; use source3
at32×179, packing4. It enforces source0=source1=source2 and equality of all
auxiliary roots. Offsets, logical heights, lane padding and coverage are
checked; none is selected by the proof. Source commitments precede bus
challenges; the auxiliary commitment follows bus challenges and precedes
local challenges. A distinct statement domain and envelope versions bind the
external profile. Reusing logical spec and use root preserves the call PCS:
the retained call proof was decoded and verified against the new statement.

Actual full fixture run (24 SHA384 nodes,12 linked calls, q309, affine-v1,
derived-fold transport) passed fresh local/GKR/PCS verification and a separate
fresh same-root call/compression conjunction. Combined bytes are **1431885**,
versus1681677 previously: **249792 B /14.85% smaller**;23.15% below the earlier
1863197 B baseline. Compression envelope1322232; opening1278352;
reduction/framing43880; call103064; receipt731; calls5858. This is still
**4.773×300000**, not a successful size gate. Static AIR/spec remain external.

Physical PCS lanes fall279→111. Source values513400→227592 B, source paths
237744→264768 B; fold values96992→97824 B, fold paths675648→683808 B;
header4360 B. The transcript changes, so fold-path variation is not a
transport regression. Fold paths alone exceed the entire300000 B target.
Next size work should therefore target the folding/code-switch protocol,
with an explicit composable soundness ledger, rather than just more pooling.

Measured local24.613 s, GKR81.430 s, independent logical coefficient check
18.675 s, PCSprove184.306 s, PCSverify1.305 s. Earlier PCSprove137.838 s is
not a controlled timing baseline; no overall performance improvement is
claimed. Expanded physical source rows increase prover work despite fewer
opening lanes. The full run stayed inside the12 GiB process cap; no precise
peak-memory benchmark was recorded.

Evidence: `research/near-compression/results/ext8-phase-pooled-q309/`.
Mapping regression checks8 logical descriptors→3 physical banks, canonical
ordering, domain separation, fixed use descriptor, and15 negative cases.
Legacy complete envelope remains byte-identical (SHA256ff42a773…258bbe2).
The Lean audit passes4226 checks, including previously proved pooled row
projection/compact mask identities. This commit adds execution wiring, not a
new complete Lean implementation-refinement theorem. Full NEAR1Pgas,
recursive verifier coverage, proximity/extraction/QROM and PQ128 remain
unproved; q309 is still only the diagnostic profile. Slice-feasibility stays
NOT_PASSED. No signed challenge, oracle or main D1 relation was modified.

Replay mapping from retained inputs (package working directory):
```
python3 airbender/direct-wasm/test_ext8_commitment_profiles.py \
 --statement results/ext8-phase-pooled-q309/statement.json.gz \
 --opening results/ext8-phase-pooled-q309/mapping-input.json.gz \
 --output /tmp/ext8-mapping-replay.json
```
Full source preparation and prover commands, file hashes, and verifier replay
are retained in the manifest. Source row fixtures remain external, with the
same four hashes checked against the prior retained prover report.

Final envelope regression passed roundtrip and12 malformed/profile cases,
including relabeling pooled→separate and affine→baseline. The independently
measured compression envelope matches the codec-tested bytes exactly:
SHA256 `fe7871c889ccfb2835d2d9f3b5268cdfba862852810eee978ec3ad5e7374d4b7`.
All preparation, prover, audit, legacy regression, new codec and measurement
processes completed successfully; no background prover remains from this run.

## 2026-10-16 — Executable code-switch functional algebra and nine Lean lemmas

The phase-pooling measurement identifies fold paths (683808 B) as a remaining
size blocker. Existing code-switch files are conditional geometry/error
ledgers; they are not an implemented switch protocol. Added
`ext8_code_switch_functional.py` as an algebra reference for the next protocol
step, deliberately without accepting it as a PCS profile.

`fold_coset` reads natural-order evaluations f(x*root^j), pairs antipodes,
decodes even/odd coefficients, and applies each affine folding challenge.
It validates the primitive2^k-th root, nonzero anchor, exact coset size and
canonical Ext8 values. `inject` updates coefficient weights by adding
mixer*point^i and updates the scalar claim by mixer*answer. These are monomial
evaluation powers, not Boolean equality weights. Multiple source-query and
extension-field OOD constraints use the same operation.

The independent test covers22 configurations (degrees2..128,1..4 folds),
compares queried-coset evaluation to both full-domain oracle folding and
folded-coefficient evaluation, and re-encodes the resulting polynomial at
16× blowup after starting at4×. It checks22 arbitrary wrong-answer/claim
residual identities,7 malformed input cases, and two explicit counterexamples:
adjacent leaf folding gives the wrong result; a wrong old claim and wrong
answer can cancel at one particular mixer. This last example prevents
mistaking honest preservation for malicious-prover soundness.

`CodeSwitchFunctional.lean` proves coefficient preservation, the one-injection
dot identity, arbitrary-depth residual identity, honest preservation, and
uniqueness of the cancelling mixer for one fixed wrong answer.
`GroupedCosetFold.lean` proves coefficient-fold evaluation, pair decoding,
and the four-value/two-fold identity at [x,x*i,-x,-x*i], assuming i²=-1 and
nonzero divisors. Exact even-shape premises are explicit. Python supports
arbitrary fold depth; the new Lean coset theorem covers two folds and is not
a full arbitrary-depth loop refinement. Nine audited lemmas added; full audit
**4235 PASS**. Results and hashes: `results/ext8-code-switch-functional/`.

Next executable protocol contract:
1. Fix the source commitment and weighted claim before the stage's sumcheck.
2. Commit each quadratic before drawing its challenge; evaluate virtual folds
   without publishing intermediate roots.
3. Commit the new encoding before drawing an OOD point; bind its answer.
4. Draw source coset queries, authenticate their source values, and compute
   their folded values with the grouped evaluator. Bind all supplied answers
   before drawing constraint mixers.
5. Inject the query/OOD constraints into the continuing coefficient functional.
   The next stage must actually prove this updated functional against the new
   commitment; accepting the injection arithmetic alone is unsound.

Still required: precise query/FS schedule, new-root extraction/common-candidate
proof, multi-constraint mixing bound, grouped authentication, arbitrary-depth
formal refinement, complete stage composition and QROM/security accounting.
The old code-switch byte ledgers cannot be promoted to measured proof sizes.
No new complete bundle was generated here; last verified slice remains1431885 B.
Full NEAR1Pgas/PQ128 and sub300000 B remain open; feasibility stays NOT_PASSED.

## 2026-10-16 — Authenticated scalar code-switch chain prototype

Added `ext8_code_switch_stage.py`, a separate experimental scalar Ext8 profile.
It creates natural-order coset Merkle leaves under SHA384 contexts binding the
namespace, coefficient degree, blowup and leaf fold depth. It binds the
external weighted claim, source root and complete future schedule; commits
quadratics before folding challenges; commits the child encoding before its
random extension-field evaluation point; binds the answer before source query
sampling; authenticates cosets and binds responses before drawing mixers.
The OOD point is sampled over the extension field without conditioning on
being outside the base domain. No excluded-point argument is claimed.

`verify_stage` returns a **continuing obligation**, not final acceptance.
The next stage receives the updated weights and scalar claim derived by the
verifier. `verify_chain` closes at a fully disclosed terminal polynomial:
its exact coefficient shape, reconstructed root and residual are all checked.
A wrong terminal claim is rejected even when the terminal root matches.
Parameters are externally supplied; proofs cannot select weights or schedules.
The reference caps degree4096, domain65536, fold depths1..4 and queries128;
terminal degree is at least2. These are prototype limits, not a NEAR profile.

Four cases at degree8/32/128/256 passed, including two- and three-stage chains
and blowup changes4→8→16 and4→16→16. A fresh verifier accepted the retained
case using only the external statement, stage proofs and terminal coefficients;
it was not given initial source coefficients. Twenty-four negative tests
cover both stages, reordering, authentication, OOD/terminal changes, shapes,
noncanonical fields, externally changed configuration/schedule/weights/claim,
and bypass of the continuing functional. Retained largest-case JSON22130 B
is a small diagnostic encoding size; it is NOT comparable with the full slice.
The tests use8 queries/stage and imply no security target.

`CodeSwitchStage.lean` adds3 lemmas: injection preserves coefficients;
honest fold+injection stage preserves the functional and exact terminal shape;
arbitrary honest stage lists compose without resetting the functional.
It composes the earlier repeated affine sumcheck and injection lemmas.
Honesty of queried/OOD evaluations remains an explicit premise; this does not
refine the Python transcript/parser or infer honesty from Merkle authentication.
Full audit **4238 PASS**, permitted axioms only. Evidence and replay commands
are in `research/near-compression/results/ext8-code-switch-stage/manifest.json`.

Next: adapt the initial multi-source weighted opening to this scalar tail.
The current execution slice has several differently sized packed sources;
its combined polynomial is virtual and has no independent initial commitment.
Do not introduce a free scalar root and silently forget those source roots.
The adapter must authenticate the original branches, derive their combined
folded query values using the existing private weights/degree embedding, then
inject those constraints into the first committed scalar child. Grouped leaf
layout requires either rebuilding sources or initially retaining one-bit pair
queries. After that: compact transport/actual slice measurement, malicious
candidate extraction, complete code-switch error budget and QROM composition.
No full slice rerun or new complete size claim here: last verified combined
slice1431885 B; full NEAR1Pgas/PQ128 and sub300000 B remain open. Feasibility
stays NOT_PASSED.

## 2026-10-16 — Original packed commitments feed code-switch tail

Added `ext8_weighted_code_switch.py`. It reuses the original weighted PCS
public-parameter validation, input sumcheck, beta evaluation, packed source
contexts and authenticated pair reader. A distinct adapter domain binds its
externally chosen complete schedule. The first committed scalar is the child
of a one-bit fold; there is no independently trusted combined-source root.

After input reduction, the prover combines lane coefficients at sparse
indices i*(D/d), with verifier-derived beta weights. It commits the folded
child before the OOD draw and authenticates original source pairs at each
query. For d<D it selects the correct full-domain side and duplicates it;
for d=D it retains both sides. The verifier sums these branch pairs, derives
the folded query value, injects query/OOD constraints, and passes the updated
functional into the scalar code-switch stages. Tail terminal root and claim
are both checked. Source commitments and their original pair layouts remain
unchanged in this adapter; queries cannot replace them with a free scalar root.

Four positive cases (queries8/31; separate or mixed pooled/legacy weights)
pass at source degrees64/8/16. An independent direct-polynomial evaluation
matches the authenticated combined pair at **256 exhaustive positions**.
The retained proof passes a fresh process without initial source rows or
prover caches. Twenty-two negatives cover input sumcheck, first child/round,
source roots/leaves/paths/order/count, unknown scalar root metadata, tail,
terminal, canonical scalars, and externally changed weights/claim/schedule.
These small-fixture query counts and JSON sizes are not a security or full
slice measurement. Runtime numbers are test timings, not capacity benchmarks.

`WeightedCodeSwitchQuery.lean` adds4 lemmas: affine pair-fold linearity,
linearity over branch sums, the existing heterogeneous authenticated-source
projection feeding the switch query, and the folded polynomial evaluation
when a combined polynomial representation is separately established.
The arbitrary-oracle projection lemma does not require honest polynomials;
the polynomial conclusion explicitly does. These are algebraic composition
lemmas, not a proof that hash authentication establishes low degree.
Full audit **4242 PASS**; evidence/replay in
`research/near-compression/results/ext8-weighted-code-switch/manifest.json`.

The adapter currently inherits the small scalar-stage geometry/query caps.
Next full-slice work must replace reference large-domain FFT/functional
injection with parity-checked native paths, define compact multiproof transport,
and then integrate an externally selected execution opening profile. Do not
silently change the existing verified execution codec. Source-side first-fold
queries can retain one-bit pair leaves while later scalar commitments use
larger cosets. The first source stage still needs its own soundness budget;
raising later rates cannot retroactively improve its agreement threshold.
Full malicious-candidate extraction, stage error composition and QROM remain
open. Latest verified complete slice stays1431885 B; no gate changed and full
NEAR1Pgas/PQ128/sub300000 B remain the objective.

## 2026-10-16 — Native code-switch functional update and large-domain parity

Added `near_ext8_inject` to the existing Rust kernel, with a checked Python
adapter and reference fallback for libraries lacking the new symbol. It
updates the weight vector and claim for all injected evaluation constraints.
The recurrence carries mixer*point^i, reducing the general multiplication
count; base-field query points use scalar multiplication of8 coordinates.
The ABI checks degree/constraint capacity, scalar canonicality, alignment and
output overlap before writing. Inputs remain caller-owned buffers with declared
sizes, as with the existing ABI. Direct tests cover rejection without writes.

Code-switch stages now optionally use native FFT, quadratic/fold and injection
operations, including verification of the updated functional. The packed-root
adapter uses these paths on its prover side. Verifier CLIs accept an explicit
`--native-library`; the proof does not select its implementation. The native
FFT accepts a zero-extended input for arbitrary supported blowups, retaining
exact reference roots/leaves. No hash, transcript or proof layout changed.

Evidence in `research/near-compression/results/ext8-native-injection/`:
* 15 small native/reference/fallback cases,11 malformed wrapper/ABI cases.
* Full-vector equality at131072 coefficients and310 constraints against an
 independent reference combining repeated-point constraints. There are4
 distinct points (one extension point and3 base points), so this is an exact
 arithmetic stress case, not a random-query prover benchmark.
* Every output of a1048576-point native FFT matches an independently evaluated
 sparse polynomial; tree/root/leaf equality checked at2×/8×/16× blowups.
* Complete small scalar-chain native/reference proof equality; retained packed
 adapter and scalar-stage proof bytes unchanged. Both retained proofs pass
 fresh native verifiers; original weighted PCS regression also passes.
* Boundary tests execute262144-weight and4096-constraint injections, reject
 larger capacities, and validate maximum geometry without allocating a4M
 tree. Stage caps are now degree262144, domain2^22, queries4095 (plus1 OOD
 constraint fits the4096 injection cap). This is capacity, not security tuning.

Two Lean lemmas prove the rolling recurrence equals the previously proved
monomial-power update and preserves its dot identity. Full audit **4244 PASS**.
Rust ABI/FFT/transcript implementation refinement remains separate; algebraic
Lean identities plus parity testing are not a full native correctness proof.

Next: compact code-switch proof transport, then a full source-root-bound
execution measurement using a separately selected opening profile. The old
complete execution profile remains unchanged. Do not infer sub300000 B or
PQ128 from faster arithmetic. Last fully verified combined slice1431885 B;
full NEAR1Pgas, source extraction/proximity, adaptive error/QROM composition
and the feasibility gate remain open/NOT_PASSED.

## 2026-10-16 — Compact sequential code-switch multiproof transport

Added `ext8_weighted_code_switch_codec.py`, magic `NP8WCS01`, as a separate
experimental transport. External source descriptors and schedule determine
all scalar counts, leaf widths, domain sizes and terminal length. Queries
are replayed from the transcript; no query indices/counts are transmitted.
Original packed base-field pairs and later Ext8 coset leaves use canonical
multiproofs. Identical root/context/geometry/query lists share bytes even
when logical branches have different functional weights; every branch still
participates in verification.

Decoding authenticates each stage's responses, reconstructs the original
ordered per-query leaves and paths, binds those exact responses, derives the
mixers, and carries the updated functional into the next stage. It checks
sumcheck endpoints and the terminal root/residual; it is not merely a parser
or Merkle checker. Truncation, trailing data and noncanonical scalars fail.
The32 MiB wire cap is separate from the existing field/domain capacities.

During initial replay testing, encoding failed the second tail's endpoint:
the first tail's query draw had been replayed on a preview transcript while
its mixing step used the unadvanced transcript. Corrected this so each scalar
stage advances its actual transcript through child root, OOD answer and query
draws before mixing, matching the original verifier. The first packed adapter
still uses a preview solely to derive read dimensions, then its existing
`initial_obligation` replays those events on the actual transcript. Exact
roundtrip across both tail stages now tests this sequencing.

Retained small diagnostic:113161 B JSON→12464 B binary; all original proof
fields reconstruct exactly. A separate shared-source case is3560 B and uses
one shared group. Native/reference wire/proof equality, a fresh process, and
27 malformed-byte/config cases pass. Results and replay commands are in
`research/near-compression/results/ext8-weighted-code-switch-codec/`.
No Lean definitions changed; last audit remains4244. Existing algebra and
multiproof results do not constitute a Lean refinement of this new decoder.

Next: an externally selected full execution envelope using this codec,
followed by actual root-bound slice proving and combined call/compression
measurement. Retain the current execution profile unchanged. Code-switch
error/extraction/QROM obligations remain open; do not treat31-query small
fixtures as PQ128. Last verified complete slice remains1431885 B. Full NEAR
1Pgas correctness/PQ128/sub300000 B and the feasibility gate are still open.

## 2026-10-16 — Full retained execution slice with code-switch opening

Added a separate full envelope `ext8_switch_execution_codec.py`, magic
`NPEX8CS1`, fixed to pooled commitments and affine terminal reduction. The
external switch schedule is bound by the opening protocol. Existing execution
codecs and their accepted profiles were left unchanged. New prover reconstructs
the original packed sources and Ext8 auxiliary vectors from the four hashed
fixtures, checks every root/final against the retained reduction, and derives
opening parameters by independently verifying that local/GKR reduction.
It then reproves the opening with the original-root adapter and scalar tail.
This reuses the local/GKR proof; it does not claim a new trace execution.

Actual full SHA384 node/call slice, unchanged24 nodes/12 calls:
*  Initial source stage is one fold at rate4 with309 queries.
*  Scalar source degrees131072,16384,2048,256,32,4 use rates8,16,32,64,128,256
  and fold depths3,3,3,3,3,1; each stage uses309 queries plus one OOD answer.
*  Terminal degree2 is fully disclosed and checked against its rate256 root.
*  Full opening1191112 B, reduction/framing43880 B, compression envelope1234992 B.
*  Unchanged call proof103064 B, receipt731 B, calls5858 B: **1344645 B combined**.
  This is **87240 B /6.09% smaller** than1431885 B and still **4.482×300000**.

Fresh execution verification, exact codec/envelope roundtrip and a fresh
same-root call/compression conjunction passed. The schedule is a deliberately
uniform-query diagnostic baseline, not an accepted128-bit/PQ128 profile.
Security cannot be compared merely by holding query counts equal across
protocols. No extracted-candidate/proximity/QROM theorem is inferred.

Measured new opening prover195.085 s, source/aux regeneration87.944 s,
encode+opening decode23.740 s. Total445.052 s includes repeated verification
and envelope/fresh-process checks; local/GKR proving was reused, so this is
not an end-to-end prover-time comparison. The process completed inside its
12 GiB cap; precise peak memory was not recorded.

Byte diagnosis: original-source values228672 B and paths264624 B, totaling
* *493296 B**. Scalar coset values384320 B and paths309504 B; opening
header/terminal3992 B. Relative to prior pooling, scalar paths shrink from
683808 B, but coset values grow from97824 B. This modest net reduction is a
real measurement, not the earlier counterfactual code-switch estimate.
The measured original-source openings alone exceed300000 B; this source
layout/query configuration cannot meet the target by tail compression alone.
This is a transport/configuration observation, not a universal proof-size
lower bound.

Evidence: `research/near-compression/results/ext8-switch-execution-q309/`.
Full Lean audit4244 PASS; repository `make pin-check` passed. No Lean theorem
or native/byte-decoder refinement was added in this integration chunk.
Full NEAR1Pgas, complete relation coverage, source extraction, adaptive
code-switch error/QROM composition and PQ128 remain open; feasibility stays
NOT_PASSED. Next work should optimize source geometry/rate and stage query
budgets against explicit proven assumptions, not silently reduce queries to
make size pass. The full-state-transition objective remains unchanged.

Final envelope tests passed12 malformed/profile cases, including relabeling
legacy→switch and switch→legacy. Verified compression SHA256 is recorded
in `codec-report.json`; manifest contains replay/build/prover commands and
artifact/source hashes. All prover, audit, conjunction and codec-test
processes completed successfully; no background proof remains from this run.

## 2026-10-16 — Sharp independent-constraint mixing count and implementation bridge

Added `IndependentConstraintMixing.lean` with6 public audited lemmas.
The implemented switch samples an independent Ext8 mixer for each OOD/query
constraint; it does not use the earlier rate-shift power-batching protocol.
For fixed residual coefficients with at least one nonzero entry, the exact
Cartesian experiment satisfies count≤|sample|^(m−1), for any old residual
offset. The proof handles a nonzero coefficient at any position: sum interchange
isolates it, distinctness bounds its roots by1, and zero prefixes recurse.
Samples are independent with replacement across coordinates, while the field
alphabet itself is duplicate-free. Integer counting also handles empty alphabets.

The template-binding and residual lemmas connect this linear sum to the actual
`switchInjectAll` update, including an incorrect prior functional claim. A
fixed false candidate satisfies the same bound; if all evaluation constraints
are true but the prior claim is wrong, acceptance is impossible. A fixed
prechallenge family of L candidates admits selection after the mixer tuple
but bounds bad acceptance by L*|sample|^(m−1). For nonempty constraints, the
scaled theorem is count*|sample|≤L*|sample|^m, i.e. L/|sample| for a nonempty
uniform alphabet. This replaces a constraint-count factor in this particular
mixing argument; it is not an automatically applicable WHIR theorem.

Exhaustive validation:96 toy-prime cases,4768 independently computed injection
identities, later-position nonzero coefficients, fixed-family unions, and
explicit counterexamples for missing premises. Over F7, choosing the candidate
c=r/(1+r) after seeing r satisfies a false mixed claim for6/7 mixers; this
invalidates a1/F fixed-candidate argument without prechallenge list control.
A repeated alphabet [0,0,0] also violates the distinct-sample root bound.
Neither example is presented as an attack on the committed protocol.

Conditional arithmetic for the actual7-stage schedule uses Ext8 field size
2013265921^8. Assuming one candidate/stage gives mixing-only7/F; assuming caps
10*targetRate gives7600/F. Both are below2^-220 for this term alone, but the
candidate caps are explicitly unproved here.220 is an illustrative threshold,
not a quantum-security conversion. This ledger excludes OOD separation,
source/child proximity and extraction, local/GKR/bus errors, adaptive stage
composition, hash assumptions and Fiat–Shamir/QROM losses. No query counts,
accepted profiles or feasibility status changed.

Full audit **4250 PASS**, allowed axioms only. Evidence and replay:
`research/near-compression/results/independent-constraint-mixing/`.
Next proof obligation is a complete, bounded candidate family determined by
the committed child oracle before all mixers, with the SAME candidate supplying
the carried functional and every query/OOD evaluation. Existing unique-basin
and older power-mixing lemmas cannot simply be relabeled as that theorem.
Latest verified diagnostic bundle remains1344645 B; full NEAR1Pgas/PQ128 and
sub300000 B remain open, with slice feasibility NOT_PASSED.

## 2026-10-16 — Complete Johnson family connected to independent mixing

Added IndependentMixingCandidates.lean with three audited public theorems.
The earlier FiniteRSJohnsonCandidates construction already enumerates a complete
normalized candidate family for a fixed received oracle, provided the coefficient
alphabet covers the field. Its list bound is L*(T²-N*(D-1))≤N². The new bridge
maps this family to the actual coefficient/weight pairs consumed by switchInjectAll
and bounds the existential bad-mixing event over ALL degree-bounded candidates
with agreement at least T. The same polynomial supplies the old functional and
all evaluation constraints. Selection within this family may depend on mixers.
Exact weight length preserves all normalized coefficients; the shape lemma
explicitly prevents zip truncation when applying the arithmetic interpretation.

For m>0 independent mixers from a distinct alphabet S, the composed result is
badCount*|S|*(T²-N*(D-1))≤N²*|S|^m. This is useful only for positive Johnson gap
and nonempty S. The complete family depends on the received oracle/domain and
threshold, not mixers. It is a mathematical enumeration, not a proposed runtime
list-decoding algorithm. No oracle extraction from a Merkle root is proved.

The seven diagnostic target geometries admit explicit thresholds
388822,68733,12149,2145,375,60,25 with fixed-oracle candidate caps
79,159,319,634,1229,1985,2319 respectively. These are integer consequences of
the proved Johnson bound, replacing an assumed 10*rate list cap ONLY under
the stated agreement premise. Protocol acceptance has not been shown to imply
that premise. These numbers are not an all-stage error ledger or a PQ128 claim.

Validation:79 exhaustive/structured small-field received-oracle cases and1111
mixer tuples, including empty and multiple-candidate lists, independent injection
checks, and explicit incomplete-alphabet/zero-gap premise checks. Full audit
4253 PASS, allowed axioms only. Evidence:results/independent-mixing-candidates/.
No query profile, serialization, or prover was changed. Latest verified bundle
remains1344645 B and feasibility stays NOT_PASSED. Next: connect continuation
acceptance to agreement and the SAME candidate for the carried injected
functional, then account for failure of that reduction; commitment extraction
and adaptive/QROM composition remain separate obligations.

## 2026-10-16 — Candidate-independent verifier state and continuation bridge

Added IndependentMixingContinuation.lean, four audited public theorems.
switchVerifierState computes the new weights and claim from old weights,
claim, templates and mixers without using any polynomial coefficients.
switch_inject_verifier_independent proves this independence for arbitrary
constraint sequences. switch_continuation_functional identifies its scalar
functional with SwitchMixedAccept for the SAME normalized degree-bounded
polynomial, with exact weight shape preventing zip truncation. The proof uses
coefficient preservation and scalar-functional normalization, not an assumed
identification between the old power accumulator and independent mixers.

switch_indexed_continuation_candidate connects the existing indexedChainCandidate
relation to one polynomial with both ordinary agreement against a fixed received
oracle and the injected functional. Global consistency mass is bounded by raw
agreement. Initial oracle, degree, weights and claim bindings are explicit.
It does NOT derive indexedChainCandidate from concrete switch-chain acceptance.
switch_continuation_candidate_count then applies the complete Johnson family
bound when every agreeing polynomial violates an original constraint. This
no-correct-candidate/rate-transfer premise remains explicit and unproved for
the implemented protocol.

Composition finding: general_checked_interactive_fold_soundness requires
2*N+D<3*T. Every lower Johnson threshold from the prior report fails this
premise. In the first geometry its minimum threshold is742742, versus388822
in the Johnson report. The isolated ideal classical query term (T-1)/N to
power q requires258 versus90 queries for2^-128. Across the seven geometries,
the high-agreement counts are258,237,228,224,221,220,220; the lower-threshold
counts are90,67,53,44,38,32,29. Neither is an accepted code-switch or PQ128
schedule, and terminal-stage counts are mathematical screening only. Other
errors, composition, extraction and QROM are excluded. This exposes why the
available binary-fold theorem cannot justify the desired small query schedule;
the actual rate-changing continuation needs its own applicable reduction.

Full Lean audit4257 PASS, allowed axioms only. Exact-integer regime screening
and audit evidence:results/independent-mixing-continuation/. No runtime protocol,
query count or proof bytes changed. Latest measured bundle1344645 B; feasibility
NOT_PASSED. Next critical work is a rate-changing continuation/agreement
reduction with an explicit error bound in a useful regime, plus source transfer;
adding list-size lemmas alone will not close that gap.

## 2026-10-16 — Joint source queries and independent mixing

Added IndependentSwitchQueries.lean with three audited theorems. Templates are
one fixed OOD answer followed by q sampled source equations, exactly matching
the independent-mixer shape. The unmixed lemma returns the old claim, OOD
equation, and ALL source equations for the same coefficient vector. A fixed
family query theorem bounds existence of a completely correct candidate by
L*(T-1)^q, assuming each family member with the old functional has source
agreement strictly below T. The joint theorem then counts actual injection
acceptance in the query-then-mixer experiment, allowing selection after both
draws within the fixed prequery family. Its bound is
L*(T-1)^q*|F|^(q+1) + N^q*L*|F|^q, or after normalization
L*((T-1)/N)^q + L/|F| for nonempty sampling spaces. The Lean statement also
covers empty lists and q=0 by integer counting. The OOD equation is retained
but no extra OOD improvement is claimed. Candidate-family construction is
available from the preceding Johnson bridge; this theorem is generic in that
family and does not itself establish its size.

The source no-close premise is still essential: deriving it from a prior
state is the missing rate-transfer step. The child candidate family and folded
source must be fixed before queries, and all templates before independent
mixers. This is not the old power-mixing protocol. It neither proves concrete
continuation extraction nor recursively composes the changing-rate chain.

Validation:1215 F3 cases covering empty/singleton/two-candidate families,
q=0,1,2 and all27 received words;110565 joint query/mixer experiments. An
omitted-noClose counterexample accepts27 outcomes where the unjustified bound
would allow9. Full audit4260 PASS, allowed axioms only. Evidence and replay:
results/independent-switch-queries/.

Inspected GeneralListCurveExtraction.lean as a possible route past the
high-agreement restriction. Its general_list_curve_extraction_bad_count is
conditional on a fixed jointly agreeing curve family AND exceptional-set
transfer; it proves the extra two-roots-per-curve functional penalty only.
It does not discharge correlated agreement, so it cannot be used as an
unconditional replacement for the high-agreement extraction theorem. Next
research should attack that correlated-agreement/exceptional-set transfer,
not add another assumed-family wrapper. Query profile and measured bundle
remain unchanged at1344645 B; full NEAR/PQ128/sub300000 B remain open and
feasibility NOT_PASSED.

## 2026-10-16 — Exact-support MCA interface and weighted-transfer counterexample

Reviewed BCSS25 Theorem4.6 against the actual weighted extraction requirement.
Primary source:https://www.math.toronto.edu/swastik/rs-proximity-gaps-2025.pdf,
November11,2025 version, SHA256
4added3e55b83c15fcc8a698fb57e137f5bd83e79ea25ce79382817c1ad26a46.
Theorem4.6 excludes challenges with a large support on which the mixed word is
an RS restriction but the source tuple is not. This exact-support statement,
not ordinary existence of a jointly close tuple on another support, is the
needed interface. Our affine mixture uses u0=sourceEven and
u1=sourceOdd-sourceEven, so (1-r)*even+r*odd=u0+r*u1 without dividing by r.
The published proof uses the Section3 interpolation/factorization pipeline;
the all-useful-factors extension is needed for the list statement. It is not
a short consequence of the finite Johnson list-size lemma. Its field-function
and factor/Hensel arguments remain unformalized here. The separate Habock
2025/2110 abstract was accessible, but its PDF returned403; no claim of having
read that PDF is made.

Added SupportPreservingAgreement.lean. AffineSupportException explicitly
quantifies over a sublist support of the distinct domain and a mixed candidate,
then says no source pair can interpolate that same support. No numerical
bound on this event is asserted or introduced as an axiom. The proved
support_preserving_weighted_lift takes the full agreement support of a candidate.
If weights are bounded by B and mass≥T with B*(minimum-1)<T, that support has
at least minimum points. Outside the exact-support event both source words
interpolate on it, preserving all its mass. With D≤minimum, polynomial root
uniqueness also yields the SAME affine candidate coefficient identity. This
removes a potential weighted-support mismatch; the exceptional-set cardinality
bound, finite joint family and extraction composition still need proof.

Concrete counterexample to replacing this with ordinary unweighted agreement:
over F3, constant code, even=(0,0,1), odd=(0,0,2), r=2, weights=(1,1,10).
The mixture is identically zero and has mass12. The joint pair(0,0) agrees on
two points, but its mass is2; even the best joint constant pair has mass10.
Thus existence of a two-point jointly agreeing pair cannot transfer the full
weighted mass. This r belongs to the exact-support exceptional event; it is
not a counterexample to the published theorem or a protocol attack.

Validation:all729 pairs of F3 words, plus64 deterministic F5 pairs with
linear candidates;1611 weighted lifts checked outside each computed exception
set. Small-field exception counts are not an asymptotic security bound.
Full Lean audit4261 PASS, allowed axioms only. Artifacts and replay:
results/support-preserving-agreement/. No query/profile/proof-size change:
1344645 B measured bundle; feasibility NOT_PASSED. Full NEAR1Pgas/PQ128 and
sub300000 B remain open. The next substantial formal target is the MCA
interpolation/exceptions argument itself, beginning with its polynomial
multiplicity and interpolation infrastructure, not another assumed-family
composition wrapper.

## 2026-10-16 — Characteristic-independent synthetic multiplicity foundations

Added SyntheticMultiplicity.lean with seven audited public theorems, starting
the polynomial machinery required by the MCA interpolation proof. No MCA
exception-count or candidate-family premise is introduced in this module.
Synthetic jets are successive remainders after division by X-a. The module
proves a coefficient identity for division, formal zero from zero quotient and
remainder, Taylor evaluation after translation, identification of Taylor
coefficients with these jets, equivalence of vanishing jets and repeated-root
certificates, and the single-point multiplicity bound for a nonzero polynomial.
A sequential root certificate of length at least D forces a degree-<D
polynomial to be formally zero, even when nodes repeat. It checks a root on
the successive quotient at EVERY step; repeated evaluation of the original
polynomial is not accepted as a multiplicity certificate. Formal zero is
coefficientwise, not inferred from being the zero function on a finite field.

These constructions require no factorial inverses and work in all field
characteristics. Validation independently computes translated coefficients
with binomial coefficients:4330 Taylor cases,20738 evaluation identities,
933 root certificates across F2,F3,F5. Regressions include X^p, whose ordinary
positive-order derivatives vanish in characteristic p although its p-th
synthetic jet is1, and X checked twice at0, which fails after the first
synthetic division. Full audit4268 PASS, allowed axioms only. Evidence and
replay:results/synthetic-multiplicity/.

This is a foundation, not the full multiplicity root bound used by GS:
independently specified jets at MULTIPLE distinct centers have not yet been
shown equivalent to a sequential certificate. Needed next are quotient/jet
compatibility across centers and a summed multi-point multiplicity bound,
then bivariate substitution and interpolation existence. The numerical MCA
exception bound, factor/Hensel steps, concrete switch-chain extraction, QROM,
full NEAR1Pgas and sub300000 B remain open. No runtime/query/proof-size change;
latest measured bundle1344645 B and feasibility NOT_PASSED.

## 2026-10-16 — Multi-point multiplicity bound from independent jets

Added MultipointMultiplicity.lean with six audited public theorems. The central
result is unconditional: for a nonzero formal polynomial of degree<D, the sum
of prescribed vanishing-jet counts at distinct centers is<D. It accepts
independently specified jets at every center, not a prearranged division
certificate. Empty center lists and zero multiplicities are allowed.

The proof develops the missing compatibility explicitly: quotient coefficients
are evaluations of coefficient tails; two synthetic divisions commute as
actual coefficient lists; jets of a quotient satisfy the translated linear
factor recurrence. Dividing at a root preserves every prescribed jet at a
different center. Repeated removal therefore converts all independent jet
conditions into the sequential certificate proved in the prior module, and
its length yields the total multiplicity bound. No infinite-field assumption,
ordinary derivatives or factorial division is used. Formal coefficient
identity is retained throughout, rather than inferred from agreement of
finite-field functions.

Validation over F2,F3,F5 covers5126 polynomial encodings,107995 quotient
commutations,4748 preserved zero jets and5106 multi-point certificates in
reverse center order. Independent jet computation uses the binomial formula.
Regressions show why centers must be distinct (duplicating a root would count
it twice) and why division must remove an actual root (dividing X at1 yields
quotient1 and destroys its root at0). Full audit4274 PASS, allowed axioms only.
Evidence and replay:results/multipoint-multiplicity/.

This supplies the univariate root-counting foundation needed after GS
substitution. Next: formal bivariate translation/substitution showing that
vanishing mixed jets of total order<m at (a,p(a)) give m univariate jets of
Q(X,p(X)) at a, then the degree/interpolation existence argument. The MCA
exceptional-set cardinality and factor/Hensel argument remain unproved.
No runtime/query/profile/proof-size change; latest verified diagnostic bundle
1344645 B, feasibility NOT_PASSED. Full NEAR1Pgas/PQ128/sub300000 B remain open.

## 2026-10-16 — Centered bivariate substitution multiplicity

Added BivariateMultiplicity.lean with four audited public theorems. PolynomialOrder
is a formal lower-degree bound: every coefficient below m is zero. Multiplication
adds these lower bounds, proved directly for coefficient-list multiplication.
Synthetic jets at0 equal formal coefficients. Bivariate polynomials are rows
Q_j(X), ordered by powers of Y, and substitution uses polynomial Horner arithmetic.
BivariateOrder requires every mixed coefficient with i+j<m to vanish.
For any curve with zero constant coefficient, substituting it for Y preserves
this total-order lower bound and therefore gives m vanishing synthetic jets
at0. This is unconditional polynomial algebra, with no family, extraction or
MCA exception-count assumption and no finite-field function identification.

Validation:1000 centered substitutions over F2,F3,F5,F7 compared with direct
monomial expansion. A further1000 binomial-translation computations check
arbitrary-center identities numerically. Those computations are explicitly
NOT a Lean translation theorem: translation and substitution compatibility
at an arbitrary point(a,b) remains to be proved before applying the earlier
multi-center bound to Q(X,p(X)). Negative cases show Q=Y loses its order when
substituting a curve with nonzero constant, and pure-axis constraints miss
the XY coefficient (which becomes X² under Y=X). Full audit4278 PASS,
allowed axioms only. Evidence:results/bivariate-multiplicity/.

Next algebraic target is formal translation/substitution compatibility at
arbitrary centers, followed by weighted-degree control and interpolation
existence. MCA factor/Hensel and exception-count arguments, actual protocol
extraction and QROM remain open. No runtime/query/proof-size change: latest
verified diagnostic bundle1344645 B, feasibility NOT_PASSED; full NEAR1Pgas,
PQ128 and sub300000 B remain open.

## 2026-10-16 — Arbitrary-center translation and GS root-forcing bridge

Added BivariateTranslation.lean with five audited public theorems. Translation
uses synthetic Taylor coefficients in X and explicit polynomial-row Horner
arithmetic for Y. Proved its evaluation identity and that EVERY translated
coefficient equals the corresponding synthetic jet, including indices beyond
the stored coefficient list. The arbitrary-center substitution result uses
Q(X+a,Y+p(a)) and p(X+a)-p(a), whose constant coefficient is zero, to apply
the centered multiplicity theorem.

Coefficient equality is recovered via the existing polynomial root bound,
with an EXPLICIT separation condition: both translated/substituted polynomials
have degree<D and there are at least D distinct evaluation points. This domain
is an algebraic witness, not a verifier query sample. No arbitrary equality of
finite-field functions is used as formal coefficient equality. The final
bivariate_multiplicity_forces_zero theorem takes a concrete sufficient size
(maximum of both coefficient-list lengths at each center), so its internal
translation degree bounds follow from lengths. It then combines all centers
with the multi-point multiplicity theorem: if total prescribed multiplicity
reaches the substitution degree bound, Q(X,p(X)) is formally zero.

This closes the arbitrary-center interface left computational-only in the
previous turn, subject to the stated field/domain-size condition. It does
NOT prove this condition for the actual Ext8 MCA construction, supply the
substitution's weighted-degree bound, or construct an interpolant. Those
remain explicit tasks; the theorem introduces no MCA or extraction axiom.

Validation:500 translation/substitution cases compare synthetic/Horner
translation with binomial expansion over F2,F3,F5,F17,F31. Another200 graph
square examples verify mixed multiplicity at three centers, total multiplicity,
and the exact size guard. The X³-X/F3 regression demonstrates why equality
on too few field elements cannot prove coefficient equality. Full audit4283
PASS, allowed axioms only. Evidence:results/bivariate-translation/.

Next: bound substitution degree from bivariate weighted degree, then prove
interpolation existence/nonzeroness. MCA factor/Hensel and exceptional-count
arguments, actual protocol extraction, QROM, full NEAR1Pgas and sub300000 B
remain open. No query/profile/proof-size change: latest verified diagnostic
bundle1344645 B, feasibility NOT_PASSED.

## 2026-10-16 — Weighted substitution degree and concrete GS witnesses

Added BivariateWeightedDegree.lean with three audited public theorems.
BivariateWeightedDegree requires every coefficient X^i Y^j with i+k*j≥D
to vanish. Substitution of any curve of degree≤k then has degree<D. The proof
handles k=0, D=0, zero rows, arbitrary trailing-zero encodings, and rows beyond
the weighted budget. An equivalent row formulation uses degree<D-k*j with
truncated subtraction; exhausted budgets require formally zero rows. The
weighted-degree root-forcing theorem now derives the substitution degree,
removing that separate premise from the prior multiplicity theorem. The
explicit distinct-point size guard for translation remains unchanged.

Built a small finite-field homogeneous interpolation solver and independent
witness checks. Six fixtures over F17/F31 use eight distinct points, curve
degree≤2, multiplicity2, weighted-degree bound12:42 monomials and24 Hasse
constraints. Gaussian elimination produces a nonzero coefficient vector;
direct translated coefficients independently check every constraint. All
104112 possible degree≤2 curves across the six fixtures were enumerated.
Each fixture has one qualifying candidate (at least six agreements), and
its substituted polynomial is formally zero. The explicit distinct-sample
size guard is also checked at every agreeing center. The fixtures include
two errors in each received word, so interpolation is not restricted to an
honest polynomial word. All coefficient rows and inputs are retained in the
report for review/replay. This solver is NOT the main proving system and its
general existence/correctness has not been formalized in Lean.

Additional144 weighted-degree cases cover F2,F3,F5,F17 and k=0..3,D=0..8.
A degree-2 curve substituted into Y² demonstrates failure of an incorrectly
claimed weight1 curve bound. Full Lean audit4286 PASS, allowed axioms only.
Evidence:results/bivariate-weighted-degree/.

Next is a general nonzero-kernel theorem for fewer homogeneous equations
than unknowns, followed by the interpolation monomial/constraint count and
constraint-to-mixed-jet bridge. MCA useful-factor/Hensel and exception-count
arguments remain beyond that. No runtime/query/proof-size change; latest
verified diagnostic bundle1344645 B, feasibility NOT_PASSED. Full NEAR1Pgas,
PQ128 and sub300000 B remain open.

## 2026-10-16 — General nonzero homogeneous-kernel existence

Added HomogeneousKernel.lean with two audited public theorems. kernelDot
expresses a homogeneous row over an explicit list of unknown identifiers.
homogeneous_nonzero_kernel proves, over EVERY field, that fewer equations
than distinct unknown identifiers admit a solution nonzero on at least one
of those identifiers. No finite-field enumeration, rank bound, assumed
Gaussian solver, interpolation theorem or new axiom is used.

The induction handles a zero leading row by dropping it. Otherwise it selects
a nonzero pivot, removes that unknown, eliminates its coefficient from all
remaining rows, invokes induction, then reconstructs the pivot value. An exact
row-elimination identity and permutation invariance connect the reduced
solution back to every original equation. Nonzeroness is inherited from a
remaining unknown, so an arbitrary value outside the declared variable set
cannot satisfy the conclusion vacuously. Distinctness and the strict dimension
inequality are essential premises.

Validation enumerates4904 small matrices over F2/F3, including1705 matrices
with rank below their row count, zero rows and empty systems. Every generated
solver witness is independently checked against the original matrix. A
square identity tests the strict inequality boundary; duplicate identifier0
with coefficients[1,1] over F3 shows why nominal list length cannot replace
the number of distinct unknowns. These checks validate witnesses, not a formal
refinement proof of the Python solver. Full Lean audit4288 PASS, allowed axioms
only. Evidence:results/homogeneous-kernel/.

This proves the linear-algebra existence step needed for GS interpolation.
Still needed: construct the admissible distinct monomial list, count it against
the mixed-jet constraints, map a kernel vector injectively to polynomial rows,
and prove each matrix equation equals the appropriate translated coefficient.
Only then will general GS interpolation existence be established. MCA
factor/Hensel and exception-count arguments, actual protocol extraction, QROM,
full NEAR1Pgas and sub300000 B remain open. No runtime/query/proof-size change;
latest verified diagnostic bundle1344645 B, feasibility NOT_PASSED.

## 2026-10-16 — Distinct GS monomials, exact dimensions and nonzero row encoding

Added GSMonomialSpace.lean with eleven audited public theorems. gsMonomials
constructs all(i,j) with j<height and i+k*j<D. Membership, distinctness and
exact count sum_{j<height}(D-k*j) are proved with natural truncated subtraction.
An explicit height cap makes the definition finite even for k=0. gsEncode
builds dense polynomial rows from the indexed coefficient vector; every
admissible coefficient is recovered exactly, every inadmissible coefficient
is zero, and a vector nonzero on this monomial set gives a formally nonzero
polynomial. Its weighted-degree bound is proved, not assumed.

gs_linear_interpolant combines this encoding with homogeneous_nonzero_kernel:
any collection of fewer coefficient-linear equations than admissible monomials
has nonzero polynomial rows satisfying every equation and the weighted-degree
bound. The equations are still generic. This is NOT yet a theorem that those
rows have prescribed mixed jets; the coefficient-linear matrix-to-translation
identity must be proved next.

gsJetOrders enumerates every(r,s) with r+s<m exactly once, and its twice-length
is m*(m+1). gsConstraints replicates these orders at each given point, with
exact twice-count N*m*(m+1). All statements include zero budgets, empty lists
and exhausted rows without hidden positivity assumptions.

Validation covers1323 monomial spaces,3969 coefficient encodings over F2/F3/F5,
401 nonzero kernel-to-polynomial witnesses and130 constraint-count cases.
An out-of-support nonzero vector does not falsely certify a nonzero encoded
polynomial. Full audit4299 PASS, allowed axioms only. Evidence and replay:
results/gs-monomial-space/.

Next: prove each interpolation matrix row equals the translated mixed
coefficient of the encoded polynomial (not merely a binomial-formula test),
then instantiate the general existence theorem with these constraints. The
large-parameter dimension inequality, MCA factor/Hensel and exceptional-set
bounds, actual protocol extraction and QROM still need work. No runtime/query/
proof-size change: latest verified diagnostic bundle1344645 B, feasibility
NOT_PASSED. Full NEAR1Pgas/PQ128/sub300000 B remain open.

## 2026-10-16 — Formal jet linearity and concrete coefficient-matrix identity

Added SyntheticJetLinear.lean and JetCoefficientMatrix.lean with eight audited
public theorems. Synthetic jets respect coefficient equality, addition, scalar
multiplication and finite polynomial sums; polynomial translation is therefore
coefficient-linear even when stored lengths differ. The proofs use coefficient
tails and exact synthetic quotient identities. They need no sufficiently-large
field/domain assumption and never identify formal polynomials from their
finite-field functions.

A canonical formal monomial X^n has the proved Kronecker coefficient vector.
The finite monomial expansion reconstructs every polynomial coefficientwise.
Applying jet linearity proves the actual matrix formula: the r-th synthetic
jet at a equals the coefficient vector dotted with the r-th jets of these
monomials. A direct range-indexed vector theorem matches canonical interpolation
row encoding. Matrix correctness is now derived in one variable rather than
supplied as a linear-functional premise. No binomial-coefficient identity is
needed by the Lean theorem; that formula is used independently in tests.

Validation:139710 concrete jet-matrix rows over F2/F3/F5,20748 zero-padding
checks and800 linear combinations including empty encodings, higher jet orders
and small characteristic. Full audit4307 PASS, allowed axioms only. Evidence
and replay:results/jet-coefficient-matrix/.

Next: apply the coefficient-matrix identity in X and Y, prove that the resulting
nested jets are exactly coefficients of bivariateTranslate, and flatten the
result onto gsMonomials. This will connect actual mixed jets to the general
linear-interpolant existence theorem. General mixed-jet interpolation, MCA
factor/Hensel and exceptional-set bounds, actual protocol extraction and QROM
remain open. No runtime/query/proof-size change; latest verified diagnostic
bundle1344645 B, feasibility NOT_PASSED. Full NEAR1Pgas/PQ128/sub300000 B remain
open.

## 2026-10-16 — General GS mixed-jet interpolation existence proved

Added MixedJetTranslation.lean and GSInterpolation.lean, seven audited public
theorems. The coefficients of row-Horner translation in Y equal successive
synthetic jets of the corresponding coefficient polynomial. Combining this
with X translation proves that every actual mixed coefficient of Q(X+a,Y+b)
is exactly the nested X/Y synthetic jet. This identity works over every field,
with no distinct evaluation sample or field-size guard. Total-order vanishing
is therefore equivalent to ALL nested mixed jets below that order vanishing.

The actual gsMixedRow entries are products of univariate monomial jets.
Applying the univariate coefficient-matrix theorem in each variable and
flattening the nested sums over gsMonomials proves matrix correctness for
every encoded coefficient vector. No matrix/jet linearity premise is assumed.
The homogeneous-kernel theorem now yields gs_interpolant_exists: under the
exact dimension inequality, a formally nonzero bivariate polynomial exists,
has weighted degree<D, and satisfies every mixed-jet constraint at every
specified point. gs_interpolant_exists_counted uses the denominator-free
inequality N*m*(m+1)<2*sum_{j<height}(D-k*j). Repeated points are permitted
(the equation count may overestimate independent constraints); no distinct
point premise is needed for existence.

Validation checks8000 mixed matrix entries against direct translation,
and retains18 independently checked nonzero interpolation witnesses over
F2/F3/F5/F17/F31. Cases include k=0, m=0, repeated points, small characteristic
and rectangular weighted spaces. The witness solver remains an executable
check, not a formally refined implementation. Full audit4314 PASS, allowed
axioms only. Evidence:results/gs-interpolation/.

This completes the ordinary bivariate mixed-jet interpolation-existence
component, not MCA. The earlier substitution/root-forcing theorem still has
its explicit algebraic separation guard. For the published improved MCA
bound, further work is needed on interpolation along u0+Z*u1 with controlled
Z degree (a trivariate coefficient budget), followed by useful-factor/Hensel
and exceptional-set arguments. Instantiating ordinary interpolation over an
abstract extension field alone would NOT supply that Z-degree bound. These
are the next research targets; no assumed-family theorem closes them.
No runtime/query/profile/proof-size change: latest diagnostic bundle1344645 B,
feasibility NOT_PASSED. Full NEAR1Pgas/PQ128/sub300000 B remain open.

## 2026-10-16 — Controlled Z-degree of jets along affine source lines

Added JetCenterPolynomial.lean with eleven audited public theorems. A recursive
formal polynomial represents each synthetic jet as a function of its center;
its evaluation equals that jet, and its degree is below coefficientLength-r.
The construction uses the proved Horner jet recurrence, not factorial division
or an assumed binomial formula. Affine polynomial composition preserves semantic
degree bounds, including constant/zero curves and trailing-zero encodings.
Thus the s-th jet of Y^j along u+vZ has degree≤j-s (or is formally zero for s>j).

trivariateJetTerm represents the mixed(X,Y) jet of X^i Y^j Z^h along(x,u+vZ)
as a formal Z polynomial. Its evaluation matches the concrete gsMixedRow
factor times the Z monomial. The coupled budget j+h<Zcap proves degree<Zcap-s.
Finite linear combinations preserve this bound; each Z coefficient is proved
to be the exact kernelDot of the trivariate coefficient vector against its
term-coefficient row. Consequently, checking precisely Zcap-s coefficient
equations makes the entire jet polynomial formally zero. No sampled-Z
identity or large-field guard is used for these results.

Validation:4433 center/affine-line cases over F2/F3/F5/F17, including derivative
orders exceeding degree and characteristic. Three retained trivariate witnesses
(F3/F5/F17) use70 admissible monomials and42 coefficient equations, and each fixture has three source triples(x,u,v),
multiplicity2, X weight1, X budget6, Y height5 and coupled Y/Z budget5. Witnesses
are checked coefficientwise and independently by specializing Q at every field
Z, then applying the existing bivariate translation. These concrete fixtures
do not constitute the general trivariate existence or specialization theorem.
Full audit4325 PASS, allowed axioms only. Evidence:results/jet-center-polynomial/.

Next: construct/count the distinct trivariate monomial and coefficient-constraint
sets, apply the nonzero-kernel theorem, and formally identify the zero jet
polynomials with mixed jets of specialized Q. This addresses the controlled-Z
interpolation requirement; MCA useful-factor/Hensel and exceptional-count
arguments remain beyond it. No runtime/query/proof-size change: latest verified
diagnostic bundle1344645 B, feasibility NOT_PASSED. Full NEAR1Pgas/PQ128 and
sub300000 B remain open.

## 2026-10-16 — General controlled-Z trivariate interpolation existence

Added TrivariateInterpolation.lean with five audited public theorems. The
explicit monomial list consists of(i,j,h) satisfying j<height, i+k*j<DX and
j+h<DZ; membership, distinctness and count
sum_{j<height}(DX-k*j)*(DZ-j) are proved, with truncated natural subtraction.
The explicit coefficient-constraint set has count
N*sum_{s<m}(m-s)*(DZ-s). It includes every r+s<m and every Z coefficient
index t<DZ-s, including cases where a budget is exhausted.

gs_trivariate_interpolant_exists applies the general nonzero-kernel theorem
to these actual coefficient rows. Under the exact dimension inequality, a
vector nonzero on the declared distinct monomial set exists, and every required
mixed jet along every source line is a formally zero polynomial in Z. Thus
controlled-Z interpolation existence is proved for the sparse coefficient
representation; it is not merely ordinary interpolation over an abstract
extension field or checking a few Z samples. The remaining specialization
bridge must identify this representation with bivariate polynomial rows at
fixed Z. Nonzeroness is on the sparse monomial set, not a claim that every
specialization is nonzero.

Validation:2016 support/count cases,486 constraint-count cases and three
independent small-field witnesses (F3/F5/F17), each with70 variables and42
coefficient equations. An exact-integer dimension-only screen at seven
representative geometries uses multiplicity20 and conservative integer ceilings
of the prior interpolation shape; every variable count exceeds its equation
count. The first geometry has246995886747 variables versus245450670080
equations. These enormous matrices are mathematical existence objects, NOT
a suggested runtime prover algorithm. The screen does not map all protocol
folds, prove a security ledger, or change parameters. Full audit4330 PASS,
allowed axioms only. Evidence:results/trivariate-interpolation/.

Next: formal sparse-to-bivariate specialization and its mixed-jet identity,
then progress on factor/useful-curve extraction and exceptional-set counting.
The main MCA bound, actual protocol extraction and QROM remain open. No runtime/
query/profile/proof-size change: latest verified diagnostic bundle1344645 B,
feasibility NOT_PASSED. Full NEAR1Pgas/PQ128/sub300000 B remain open.

## 2026-10-16 — Dense specialization and total-annihilation bound

Added TrivariateSpecialization.lean with four audited public theorems. The
dense bivariate specialization preserves the weighted X/Y degree budget;
its actual translated mixed coefficient equals evaluation of the sparse
source-line jet polynomial. Consequently the formal interpolation constraints
hold at every Z, without a field-size or sampled-evaluation premise. Finite
sum reordering explicitly connects the two coefficient enumerations.

A nonzero sparse coefficient vector can yield an identically zero bivariate
specialization at at most DZ-1 distinct sampled Z values. The proof selects
one nonzero coefficient polynomial and applies the formal polynomial root
bound. This counts total annihilation only: it does NOT establish the full
MCA exceptional set, useful factors, Hensel lifting, or verifier extraction.

Validation: 200 nonzero vectors over F2/F3/F5/F17, 12150 mixed-coefficient
identities, and all specializations of three previously retained interpolation
witnesses. Boundary checks include Q=Z, the nonzero formal polynomial Z^3-Z
over F3, and failures without distinct samples or a nonzero vector. Replaying
the test reproduced the retained report exactly. Full audit: 4334 PASS,
allowed axioms only. Evidence: results/trivariate-specialization/, including
the prior witness report hash and compressed audit.

Next: nonzero specialized interpolant root forcing and useful-factor/curve
extraction, followed by the complete MCA exceptional-count argument. No runtime
or security parameter change: diagnostic bundle 1344645 B; feasibility
NOT_PASSED. Full NEAR 1 Petagas, PQ128 and sub300000 B remain open.

## 2026-10-16 — Specialized candidate root forcing

Added TrivariateRootForcing.lean with two audited public theorems.
gs_specialization_root_forcing connects the actual source-line identities
to a candidate curve: agreement on distinct source abscissae with total
multiplicity at least DX forces Q(X,curve(X),z) to be formally zero. The
weighted substitution degree and mixed constraints are derived from the
trivariate representation, not assumed as independent candidate properties.
The theorem retains the existing explicit distinct evaluation-domain
separation premise for translation/substitution compatibility. It does not
claim this premise follows from the production field parameters.

gs_interpolation_specialization_certificate chooses ONE sparse vector from
the dimension inequality and packages its nonzeroness, formal source-line
identities, degree and mixed constraints at every Z, and the total-annihilation
count on every distinct sample. It does not choose unrelated interpolants
after observing a challenge. The DZ-1 bound still counts only identically
zero specializations, not all MCA exceptions.

Validation: independently constructed 70-variable, 56-equation witnesses over
F17 and F19 (rank53), with four source lines, one corrupted source ordinate,
and multiplicity2. Exhaustive enumeration checks 11772 candidate/Z pairs.
All36 sufficiently agreeing candidates yield zero formal substitutions.
All36 cases check the actual translation separation premise (maximum list
length6), and neither witness has a zero specialization. Boundary examples
show failure without enough total multiplicity or without distinct abscissae.
Full audit4336 PASS, allowed axioms only. Evidence: results/trivariate-root-forcing/.

Next: useful-factor extraction and the complete exceptional-set bound;
root forcing alone does not recover a common source candidate. Full protocol
extraction, adaptive/QROM composition, recursion and full NEAR1Pgas remain
open. No runtime or parameter change: diagnostic bundle1344645 B, feasibility
NOT_PASSED; no PQ128 or sub300000 B claim.

## 2026-10-16 — Formal division by a curve factor

Added BivariateCurveDivision.lean with five audited public theorems. An
explicit synthetic quotient for division by Y-curve(X) has rows.length-1
stored Y rows. The exact coefficient identity is
Q=(Y-curve(X))*quotient+Q(X,curve(X)); the factor product is represented by
its explicit coefficient formula. Formal substitution zero is equivalent
to that factor identity. This is coefficient algebra, with no sampled
evaluation, field-size, or separation premise. Arbitrary zero padding,
empty and constant polynomials are included.

If Q is nonzero and the curve is a root, the quotient is nonzero. If Q has
weighted degree<D and curve has degree≤k, the quotient has weighted degree
<D-k (truncated natural subtraction). The latter follows from tail weighted
bounds and the already proved substitution bound. These results connect
root forcing to an actual formal linear factor with decreasing degree,
not merely agreement as a finite-field function.

Independent validation uses reverse Horner synthetic division, rather than
the Lean tail-substitution definition. 1600 cases over F2/F3/F5/F17 include
1062 formal-root cases, of which574 have nonzero input. Tests check full
coefficient reconstruction, factor equivalence, quotient length, nonzeroness
and weighted degree. Four X^p-X examples reject the invalid inference from
zero polynomial function to a formal curve root. Full audit4341 PASS, allowed
axioms only. Evidence: results/bivariate-curve-division/.

Next algebraic obligation: show removing one curve factor preserves other
distinct formal curve roots, enabling repeated extraction and a root-count
bound. Useful-factor/Hensel and the complete MCA exceptional-set argument
remain open. No runtime or cryptographic parameter change: diagnostic bundle
1344645 B, feasibility NOT_PASSED. Full NEAR1Pgas/PQ128/sub300000 B remain open.

## 2026-10-16 — Formal polynomial zero-product cancellation

Added PolynomialIntegralDomain.lean with three audited public theorems.
For polynomials of orders at least m and n, coefficient m+n of the product
is exactly the product of coefficients m and n. This is proved directly
from schoolbook multiplication and the lower-order product bound. A private
first-nonzero-coefficient construction then establishes that two nonzero
formal polynomials have nonzero product. Consequently a product is formally
zero iff at least one factor is formally zero. All characteristics and zero
padding are supported, without any evaluation-domain or field-size premise.

This supplies cancellation needed to preserve other distinct curve roots
after removing one factor. It does not yet prove that preservation: the
formal substitution-through-factor identity remains necessary. In particular,
pointwise equality over a finite field is not used to infer that identity.

Validation: 26661 polynomial pairs, with exhaustive lists of length≤3 over
F2/F3/F5 plus500 randomized, zero-prefixed pairs over F17. Tests checked52267
permitted order-coefficient identities. Four X^p-X examples retain nonzero
formal products despite vanishing as functions. A Z/6Z counterexample shows
why the domain hypothesis matters. Full audit4344 PASS, allowed axioms only.
Evidence: results/polynomial-integral-domain/.

Next: formal substitution compatibility for the curve-factor identity, then
other-root preservation and repeated extraction/counting. Useful-factor/Hensel,
full MCA exceptions and protocol/QROM composition remain open. No runtime or
parameter change: diagnostic bundle1344645 B, feasibility NOT_PASSED. Full
NEAR1Pgas/PQ128/sub300000 B remain open.

## 2026-10-16 — Distinct curve-root preservation and root count

Added PolynomialCoefficientAlgebra.lean (six public theorems) and
CurveRootPreservation.lean (three). Coefficientwise multiplication respects
coefficient equality and satisfies left/right distributivity, associativity,
commutativity and left subtraction. All proofs work directly with schoolbook
coefficient lists and tolerate arbitrary trailing zero padding.

The formal divided-difference identity is
Q(X,g)-Q(X,f)=(g-f)*quotient_f(X,g). Combining it with zero-product cancellation
proves that removing the factor Y-f preserves any other coefficient-distinct
curve root g. Distinctness is NOT merely structural list inequality. Induction
on a pairwise coefficient-distinct list then repeatedly removes factors,
preserving nonzeroness and reducing the number of stored Y rows, to prove
number_of_curve_roots≤rows.length-1 for nonzero Q. This is a stored Y-degree
bound and remains valid with padding. These results have no field-size,
evaluation-domain, or curve-degree assumption. The earlier agreement-to-root
forcing step still retains its explicit translation separation premise.

Validation:600 coefficient-algebra cases,600 arbitrary divided-difference
cases and100 fixtures whose affine candidate roots were exhaustively
enumerated over F2/F3/F5/F17. Checked372 ordered pairs of distinct roots through
factor removal. Four examples distinguish formal curves with identical finite
field evaluations. Counterexamples reject counting duplicate roots and
treating zero-padding differences as distinct roots. Full audit4353 PASS,
allowed axioms only. Evidence: results/curve-root-preservation/.

Next: connect the root-count bound to specialized interpolants outside total
annihilation, then the useful-factor/Hensel and complete MCA exceptional-set
argument. Root counting alone does not recover a common source candidate or
bound the full exception set. No runtime/security-parameter change: diagnostic
bundle1344645 B, feasibility NOT_PASSED. Full NEAR1Pgas/PQ128/sub300000 B remain open.

## 2026-10-16 — Remove translation separation guard; count specialized candidates

Added FormalTranslation.lean and FormalRootForcing.lean, eight audited public
theorems. Formal translation is multiplicative; translating X commutes with
substitution of the translated curve; Y translation commutes with adding the
constant to the substituted curve. Together these prove the centered
translation/substitution identity coefficientwise in every field. No finite
evaluation domain, polynomial list-length separation, or field-size assumption
is used. This supersedes the separation-guarded route without changing its
existing API or silently dropping one of its premises.

formal_substitution_at_center transfers mixed multiplicity to univariate
synthetic jets. formal_weighted_multiplicity_zero then uses the existing
distinct-center multiplicity bound and weighted degree. The specialization
root-forcing theorem now needs only the source-line identities, curve degree,
distinct agreement support and sufficient total multiplicity. Finally,
formal_specialization_candidate_count applies repeated curve-root extraction
to show that every pairwise coefficient-distinct eligible candidate list at
a NONZERO specialization has length≤height-1. Supports may differ by candidate.
This is not a common-source-candidate theorem or a full MCA exception bound.

Validation:400 formal translation cases (289 exceed field-size separation),
plus independent trivariate witnesses over F2/F3/F5. Their candidate sets were
exhaustively enumerated:10 eligible candidates across10 nonzero specializations
all satisfy root forcing and the count. Their28 agreement-point checks exceed
the previous coefficient-list-length separation bound. Thus the new test
exercises cases outside the old theorem's applicability, not just large-field
examples. Full audit4361 PASS, allowed axioms only. Evidence:
results/formal-root-forcing/.

Next: useful-factor/Hensel selection and the complete MCA exceptional-set
argument. Total annihilation remains bounded separately by DZ-1, but that is
not the full exception set. Protocol extraction/adaptive/QROM composition and
recursion remain open. No runtime or security-parameter change: diagnostic
bundle1344645 B, feasibility NOT_PASSED. Full NEAR1Pgas/PQ128/sub300000 B remain open.

## 2026-10-16 — Finite smooth Hensel lifting

Revisited the primary MCA source, sections3.2/4.3:
https://www.math.toronto.edu/swastik/rs-proximity-gaps-2025.pdf
SHA256 4added3e55b83c15fcc8a698fb57e137f5bd83e79ea25ce79382817c1ad26a46.
Its useful-factor argument requires lifting over a rational-function field
and finite extension, plus exactness and separate inseparable-factor handling;
per-specialization list counts do not substitute for this step.

Added HenselCoefficientStep.lean with seven audited public theorems. The
operational slope is the constant coefficient of the formal curve quotient
evaluated at the current approximation. Order-n curve perturbations preserve
all lower residual coefficients, and for n>0 change residual coefficient n
by perturbation_coefficient*slope. A nonzero slope therefore gives the unique
correction -residual_n/slope. The slope depends only on the constant term.

curveHenselLift constructs successive coefficients. hensel_finite_lift proves
that after n corrections it retains the chosen constant, has degree<n+1 and
residual order≥n+1. hensel_lift_unique_modulo proves uniqueness modulo X^n
for any two approximate roots with the same constant and nonzero local slope,
without degree bounds on the approximations. All statements are generic over
a field and all characteristics. They do not construct the rational-function
field/finite extension, choose a smooth starting point, handle inseparable
factors, or prove bounded-degree termination/exactness of the lift.

Validation:600 initial roots over F2/F3/F5/F17, of which441 are smooth and159
singular. The smooth cases exercised3087 lifting steps,24430 exhaustive
next-coefficient choices and3087 higher-coefficient preservation checks.
Independent derivative evaluation at the initial point matches the quotient
slope. Singular examples Y^2-X and Y^2 over F2 demonstrate nonexistence and
nonuniqueness respectively; Y-X-Y^2 demonstrates that finite approximation
need not be an exact polynomial root. Full audit4368 PASS, allowed axioms only.
Evidence: results/hensel-coefficient-step/.

Next: connect finite lifts to specialization and bounded-degree exactness,
then useful-factor selection and the complete MCA exceptional-set count.
No runtime or cryptographic parameter change: diagnostic bundle1344645 B,
feasibility NOT_PASSED. Full NEAR1Pgas/PQ128/sub300000 B remain open.

## 2026-10-16 — Bounded-degree Hensel reconstruction and exactness certificates

Added HenselBoundedReconstruction.lean with four audited public theorems.
Any exact root f of degree≤n with nonzero local slope is coefficientwise
equal to the n-step lift from f(0). Consequently, through a fixed smooth
initial root, exact residual checking after k corrections is sound AND
complete for degree≤k polynomial roots. This proves a reconstruction method
without assuming that every smooth branch terminates within that degree.

A second exactness certificate uses a weighted substitution bound: if Q has
weighted degree<D, lift precision n+1≥D, and all lift coefficients above k
vanish, its residual is formally zero. When also k≤n, that high-coefficient
condition is equivalent to existence of a degree≤k exact root through the
smooth initial value. Smoothness, sufficient precision and the coefficient
condition remain explicit; finite precision alone is not called exactness.

Validation:220 fixtures over F2/F3/F5/F17,10280 exhaustive polynomial candidates.
All172 smooth exact roots were reconstructed;48 smooth initial branches had
no exact root within the requested degree and were rejected. The220 higher-
precision coefficient certificates agreed with exhaustive existence checks.
The same fixtures contain71 singular roots, explicitly outside the theorem's
scope. Counterexamples show failure with insufficient precision or with the
high-coefficient condition omitted. Full audit4372 PASS, allowed axioms only.
Evidence: results/hensel-bounded-reconstruction/.

Next: denominator-aware specialization of these lifts and the useful-factor
argument needed to force bounded-degree exactness across many challenges.
Singular/inseparable branches and the complete MCA exceptional-set count
remain open; a smooth-branch decoder is not a full protocol extractor.
No runtime or security-parameter change: diagnostic bundle1344645 B,
feasibility NOT_PASSED. Full NEAR1Pgas/PQ128/sub300000 B remain open.

## 2026-10-16 — Guarded rational specialization; denominator-growth diagnostic

Added RationalSpecialization.lean with six audited public theorems. Arithmetic
expressions over polynomial leaves carry explicit addition, multiplication,
negation and inversion, an unnormalized numerator/denominator pair, and a
guard polynomial. The guard is nonzero at a challenge iff every syntactic
inversion is valid there. On that domain the denominator is nonzero and both
the cross-multiplied and fraction evaluation identities hold. This avoids
pretending evaluation at Z=z is a total map on a rational-function field.

Regularity explicitly requires every inverted numerator to be formally
nonzero. It implies the guard is formally nonzero, NOT that any particular
challenge is safe. Proved recursive numerator/denominator/guard degree
budgets yield an excluded-distinct-challenge bound by guard degree. These
are expression-domain poles only, not the full MCA exceptional set. The
representation is not a quotient-field or algebraic-extension implementation.

Validation:600 random expressions over F2/F3/F5/F17,497 regular. Tests cover
cancelled-output poles (Z/Z and inverse(inverse(Z))), four regular expressions
undefined at every base-field challenge, and an inverse-zero nonregular
counterexample. Symbolic coefficients of Y^2+(Z+1)Y-X through degree5 match
138 specialized finite-lift coefficients away from Z=-1. This Hensel-to-circuit
correspondence is tested here, not yet Lean-proved. Full audit4378 PASS, allowed
axioms only. Evidence: results/rational-specialization/.

The diagnostic exposes a quantitative problem: raw guard-degree budgets for
the five Hensel coefficients are1,3,9,27,81, but every coefficient has exactly
one excluded challenge. Repeated syntactic factors grossly overcount the
same pole. Next: prove common-denominator-power representation/specialization
and count the pole set once; do not insert this loose budget into a claimed
MCA or PQ128 ledger. Useful factors, algebraic extensions, inseparable cases
and the complete exceptional-set argument remain open.

No runtime or cryptographic parameter change: diagnostic bundle1344645 B,
feasibility NOT_PASSED. Full NEAR1Pgas/PQ128/sub300000 B remain open.

## 2026-10-16 — Common denominator removes repeated-pole overcounting

Added CommonDenominator.lean with seven audited public theorems. The expression
interface permits polynomial leaves, addition/multiplication/negation and one
designated reciprocal1/S. It expands to the previously guarded rational
expression semantics, and every expansion is safe where S does not vanish.
Normalization produces numerator/S^e, aligns sums at the maximum exponent,
and has a proved cross-multiplied evaluation identity on that domain. Actual
normalized numerator degrees and exponents satisfy explicit recursive budgets.
No assertion of coefficient equality is inferred from finite-field functions.

For ANY finite family using this interface, excluded distinct challenges are
bounded by degree(S), independently of family size, repeated inversions or
denominator exponents. Nonzero S and its degree bound are explicit. A further
theorem proves that sufficiently many distinct SAFE zero specializations force
the normalized numerator polynomial to be formally zero. This is a component
needed to force high Hensel coefficients to vanish across challenges.

Validation:600 expressions in20 shared-denominator families over F2/F3/F5/F17,
including109 formal-zero certificates. Boundary tests reject using an unsafe
point's totalized inverse-zero value as a root and reject duplicate samples.
For Y^2+(Z+1)Y-X, the same five coefficients that had raw guard budgets
1,3,9,27,81 now have denominator exponents1,3,5,7,9, numerator-degree budgets
0,2,4,6,8, and ONE shared pole bound1, matching the actual excluded set.
All138 safe specialized coefficients still match the independent finite lift.
Full audit4385 PASS, allowed axioms only. Evidence: results/common-denominator/.

This resolves repeated-pole overcounting for the explicit interface. The
generic Lean correspondence between Hensel lifting and these expressions is
still open (the specific recurrence is tested), as are algebraic extensions,
useful-factor selection, inseparable cases and complete MCA exception counting.
No runtime/security-parameter change: diagnostic bundle1344645 B, feasibility
NOT_PASSED. Full NEAR1Pgas/PQ128/sub300000 B remain open.

## 2026-10-16 — Generic symbolic Hensel specialization

Added SymbolicHensel.lean with six audited public theorems. Symbolic X-polynomial
coefficient lists use common-denominator expressions; padded addition,
schoolbook multiplication, bivariate substitution and coefficient perturbation
specialize exactly to the existing Poly operations. The generic symbolic lift
uses the designated reciprocal1/S at every correction. Induction using slope
stability proves it specializes to curveHenselLift at every challenge where
the initial value is a root, S equals the actual initial slope, and S is nonzero.
The slope equality is an explicit semantic premise, not inferred from S≠0.

symbolic_hensel_high_coefficient_zero connects this lift to bounded-degree
reconstruction: if enough distinct safe challenges have degree≤k exact roots
with the prescribed initial value, every specified coefficient above k has
a formally zero normalized numerator, provided its numerator-degree bound
and lift precision are adequate. The theorem does NOT supply the common
initial branch, useful factors, or those quantitative budgets.

Validation:120 expression-polynomial arithmetic fixtures and12 generic
Hensel fixtures over F2/F3/F5/F17, using factored bivariate polynomials with
Z-dependent quadratic root curves. All284 safe specialized coefficients
match independent numeric lifts and the known root. Three F17 fixtures have
16 safe challenges against numerator-degree budget6 (strict cutoff7), so
the high-coefficient zero criterion is exercised with enough points. Other
small-field examples are not claimed to meet that criterion. An incorrect
but nonzero slope denominator demonstrably gives a different lift; zero
slope is excluded. Full audit4391 PASS, allowed axioms only. Evidence:
results/symbolic-hensel/.

The previous generic Hensel-to-expression correspondence gap is now closed
under the stated semantic premises. Next: derive the initial-value/slope
interface from actual trivariate data and advance the common-branch/useful-
factor argument, including algebraic extensions and singular/inseparable
cases. Full MCA/protocol/QROM composition remains open. No runtime or security-
parameter change: diagnostic bundle1344645 B, feasibility NOT_PASSED.
Full NEAR1Pgas/PQ128/sub300000 B remain open.

## 2026-10-16 — Derive initial residual and slope from trivariate coefficients

Added TrivariateInitialBranch.lean with five audited public theorems. Dense
Q(X,Y,Z) uses Y rows, X coefficient lists, and polynomial-in-Z entries. The
initial residual is Q(0,a(Z),Z); the initial slope is constructed by formal
Y-division at a(Z) and substitution into that quotient. Their specializations
are proved to be exactly the numeric initial-root equation and Hensel slope.
The symbolic lift therefore specializes correctly when the supplied initial
branch is a FORMAL polynomial root and the computed slope is nonzero at z.
There is no separately trusted numeric slope input in this composition.

If a has degree≤w and Q(0,Y,Z) has weighted degree<D, the constructed slope
has degree<D-w. For a formally nonzero slope, its zero challenges on any
distinct sample are bounded by D-w-1. This pole budget follows from the
actual weighted input and the quotient-degree theorem. Formal nonzero slope
remains an explicit requirement. The existence of the initial branch is NOT
proved here; general useful factors may require an algebraic extension, not
a polynomial branch a(Z) over the original field.

Validation:2700 initial residual/slope evaluation checks over F2/F3/F5/F17,
400 weighted slope-degree cases and202 nonzero-slope pole counts. Twelve
constructed initial branches give71 matched symbolic/numeric lift
specializations using the slope computed from input data. An independent
formal Y-derivative calculation matches the quotient-based slope. Boundary
examples reject inferring smoothness from a formal initial root, and reject
inferring a formal initial branch from one sampled root. Full audit4396 PASS,
allowed axioms only. Evidence: results/trivariate-initial-branch/.

Next: the general common-branch/useful-factor construction, algebraic
extensions, and singular/inseparable factor treatment needed for the full
MCA exceptional-set argument. The polynomial-branch interface does not close
those obligations. No runtime or cryptographic parameter change: diagnostic
bundle1344645 B, feasibility NOT_PASSED. Full NEAR1Pgas/PQ128/sub300000 B remain open.

## 2026-10-16 — Characteristic screen narrows the factorization route

Rechecked the authoritative dimension-only interpolation screen: Y-heights
58,83,116,165,236,379,464, hence maximum stored Y-degree463. The existing Fp8
IsCharP instance proves characteristic2013265921 (not field cardinality).
These shapes are far below the characteristic; they are still NOT accepted
protocol/security parameters. This suggests prioritizing the separable-factor
route rather than implementing arbitrary-characteristic inseparable reduction
first, subject to proving the missing factorization/degree obligations.

Added SmallCharacteristicDerivative.lean with five audited public theorems.
The formal Y-derivative has coefficient(j+1)*Q_{i,j+1}. In any field of
characteristic p, for rows.length≤p, its being zero is equivalent to Q being
constant in Y. A Y-dependent polynomial therefore has nonzero derivative.
A concrete corollary uses the existing Fp8 characteristic instance, and the
seven recorded heights are kernel-checked below that characteristic.

This is NOT a theorem that Q is squarefree, irreducible, or smooth at every
root. For irreducible nonconstant factors, this degree observation can rule
out the zero-derivative obstruction once factor degree and irreducibility
are connected; that composition is not yet proved. Generic same-characteristic
field instances are supported, but algebraic/rational-function field instances
are not constructed by this module.

Validation:3870 exhaustive bivariate polynomials and400 randomized coefficient
cases over F2/F3/F5/F17. Boundary examples Y^p show why the degree condition
matters. Repeated-factor examples (Y-1)^2 over F3/F5/F17 have nonzero formal
derivative but zero slope at the repeated root, preventing a false smoothness
inference. The recorded geometry screen was replayed from its retained report.
Full audit4401 PASS, allowed axioms only. Evidence:
results/small-characteristic-derivative/.

Next: factorization, irreducibility/separability certificates and construction
of the common algebraic initial branch. Full MCA/protocol/QROM composition
remains open. No runtime or cryptographic parameter change: diagnostic bundle
1344645 B, feasibility NOT_PASSED. Full NEAR1Pgas/PQ128/sub300000 B remain open.

## 2026-10-16 — Checked Bezout certificates supply initial-root smoothness

Added BezoutSmoothness.lean with six audited public theorems. The actual
Horner derivative has coefficient(i+1)*p_{i+1}, lowers a degree bound by one,
and evaluates to the first synthetic jet (quotient evaluated at its center).
The operational curveHenselSlope at an initial constant is proved equal to
the derivative of the actual initial Y-polynomial formed from X-constant
coefficients. No finite-field evaluation uniqueness is used.

A coefficientwise certificate A*p+B*q=C(c) with c≠0 proves that p and q have
no common root. Taking q=p' and p equal to the initial Y-polynomial supplies
nonzero Hensel slope for every initial root. This is a checked certificate
interface; it does not assume nonzero formal derivative alone implies
smoothness, and does not yet prove general Bezout certificate existence,
irreducible factorization, or algebraic-root/extension existence.

Validation:600 extended-Euclidean identities over F2/F3/F5/F17,473 with
nonzero constant gcd and127 rejected noncoprime cases. Checked4050
derivative/synthetic-quotient evaluations,320 certified initial roots and
finite lifts, and rejection of473 mutated certificates. The cleared identity
-Q+(Y/2)Q'=Z for Q=Y^2-Z certifies22 smooth specialized roots when Z≠0; at Z=0
it has zero right-hand side and a singular root. A separate zero-certificate
counterexample prevents dropping c≠0. Full audit4407 PASS, allowed axioms only.
Evidence: results/bezout-smoothness/, with concrete witness coefficients.

Next: existence/construction of the Bezout and factorization certificates,
parameter-polynomial specialization budgets, and the common algebraic initial
branch. Full MCA/protocol/QROM composition remains open. No runtime or
cryptographic parameter change: diagnostic bundle1344645 B, feasibility
NOT_PASSED. Full NEAR1Pgas/PQ128/sub300000 B remain open.

## 2026-10-16 — General polynomial division foundation for certificate existence

Added PolynomialDivision.lean with three audited public theorems. Multiplying
by X^n is proved to shift formal coefficients exactly. Long division then
constructs a quotient of degree<n and remainder of degree<d for an input of
degree<n+d and divisor of degree exactly d. Each step cancels the actual top
coefficient and strictly decreases the degree bound; reconstruction is
coefficientwise, with no finite evaluation-domain assumption. Constant
divisors, zero dividends and arbitrary trailing zero padding are covered.

A private leading-position construction removes the need to supply the actual
divisor degree: every nonzero formal divisor admits division with a remainder
strictly below its leading degree. These are general existence proofs whose
witness construction is inside the proof; no production prover algorithm or
complete Euclidean/Bezout construction is claimed by this milestone.

Validation:1200 degree-recursive divisions compared with an independent
long-division implementation over F2/F3/F5/F17, including240 constant divisors,
317 zero dividends and1115 padded cases. Checked57600 monomial-shift
coefficients. Zero divisors and falsely declared leading positions are
rejected. Full audit4410 PASS, allowed axioms only. Evidence:
results/polynomial-division/.

Next: use degree-decreasing division to prove Euclidean/Bezout certificate
existence, then connect irreducibility and the derivative degree bound to
separability. Algebraic branch/factor construction and the complete MCA
exceptional-set argument remain open. No runtime or cryptographic parameter
change: diagnostic bundle1344645 B, feasibility NOT_PASSED.
Full NEAR1Pgas/PQ128/sub300000 B remain open.

## 2026-10-16 — Euclidean/Bezout existence and irreducible derivative certificates

Added PolynomialBezoutExistence.lean and IrreducibleDerivativeBezout.lean,
five audited public theorems. Strong induction on the first nonzero input's
degree constructs a nonzero common divisor, bounded degree, formal Bezout
coefficients, and divisibility witnesses for both inputs. Every common divisor
divides the Bezout combination, giving the greatest-divisor property. If all
common divisors are nonzero constants, normalization gives a unit certificate.
The construction uses the proved general division theorem, not a solver oracle.

PolynomialIrreducible explicitly means nonzero, nonconstant and no formal
factorization into two nonconstant polynomials. For an irreducible polynomial
of positive degree below the characteristic, the derivative is nonzero and
has smaller degree. Applying the Euclidean result to derivative and polynomial
forces their constructed common divisor to be constant: the alternative from
irreducibility would contradict the polynomial's leading coefficient. Thus a
unit Bezout certificate against the derivative EXISTS, rather than being
assumed. Existing roots are smooth. The root corollary does not assert root
existence or yet transport the certificate to a newly constructed extension.

Validation:600 Euclidean witnesses over F2/F3/F5/F17, including133 zero second
inputs, compared with independent extended Euclid;420 normalize to unit
certificates. Exhaustive trial factorization screens475 monic polynomials in
selected degree ranges below characteristic and verifies all216 irreducible
derivative certificates. A reducible repeated-root example prevents dropping
irreducibility, and zero first input is rejected. Full audit4415 PASS, allowed
axioms only. Evidence: results/polynomial-bezout-existence/, including explicit
nonlinear irreducible witnesses and their certificates.

Next: irreducible factorization, algebraic field/root construction, and
coefficient/certificate transport to those extensions. Complete MCA exception
counting and protocol/QROM composition remain open. No runtime or security-
parameter change: diagnostic bundle1344645 B, feasibility NOT_PASSED.
Full NEAR1Pgas/PQ128/sub300000 B remain open.

## 2026-10-16 — Certificate transport to extension-field roots

Added PolynomialFieldTransport.lean with six audited public theorems. An
explicit unital coefficient homomorphism preserves coefficients, polynomial
addition and multiplication, and formal differentiation. Unit Bezout
certificates transport coefficientwise. Combining this with the existing
low-degree irreducible derivative certificate proves smoothness at roots in
any target field equipped with the coefficient homomorphism. Irreducibility
of the mapped polynomial is not assumed: it can split in the extension.
Root existence and generic extension construction remain separate obligations.

Validation: concrete quadratic extensions F9/F25/F49, including exhaustive
checks of multiplication associativity/distributivity and nonzero inverses.
83 base coefficient homomorphism pairs and 83 extension certificate evaluations
pass; six smooth roots exist outside their respective base fields, where the
three selected quadratics have no roots. Corrupt zero certificates fail.
Full audit4421 PASS, allowed axioms only. Evidence:
results/polynomial-field-transport/.

Next: irreducible factorization and generic algebraic field/root construction,
then the useful-branch and complete MCA exceptional-set bounds. This closes
certificate transport, not extension existence or protocol/QROM composition.
Runtime and security parameters unchanged: diagnostic1344645 B,
feasibility NOT_PASSED. Full NEAR1Pgas/PQ128/sub300000 B remain open.

## 2026-10-16 — Irreducible factorization and inherited separability budgets

Added PolynomialFactorization.lean with six audited public theorems. The
leading coefficient of a bounded-degree product is proved to be the product
of the leading coefficients. A decomposition of a nonzero input into two
nonconstant factors therefore strictly decreases both degrees. Strong
induction constructs a finite tree whose leaves are nonzero scalars or
irreducible polynomials and whose product is coefficientwise equal to the
input. Every nonconstant input has an actual irreducible divisor extracted
from this tree. Classical existence is claimed, not an efficient algorithm.

A divisor of a nonzero polynomial inherits its degree bound. Consequently,
every irreducible factor of an input of degree below the characteristic has
a unit Bezout certificate against its derivative. This applies even when
the original input has repeated factors; it does not falsely assert that
the original polynomial itself is squarefree. The earlier field-transport
result can carry these factor certificates to roots in extension fields.

Validation: exhaustive3397 nonzero polynomials of degree at most4 over
F2/F3/F5, each with trailing-zero padding, reconstruct exactly from valid
factor trees. Checked7321 irreducible leaves,3390 nonconstant inputs with
extracted divisors,6758 below-characteristic factor derivative certificates,
and597 repeated-factor inputs. Zero input is rejected. Full audit4427 PASS,
allowed axioms only. Evidence: results/polynomial-factorization/.

Next: construct the algebraic field/root extension from an irreducible
modulus, then connect useful branches and complete MCA exceptional-set
bounds. Generic factorization existence is now supplied, but rational-function
field construction, extension existence, full MCA and protocol/QROM composition
remain open. Diagnostic1344645 B unchanged; feasibility NOT_PASSED.
Full NEAR1Pgas/PQ128/sub300000 B remain open.

## 2026-10-16 — Inverses and normal representatives modulo irreducibles

Added IrreducibleResidueInverse.lean with six audited public theorems.
A nonzero polynomial below an irreducible modulus's degree has a constructed
unit Bezout certificate with the modulus. General division extends this to
any representative not divisible by the modulus. Reducing the Bezout
coefficient supplies an inverse representative of degree below the modulus,
with the product formally congruent to one. These results need no bound on
the characteristic; that restriction is only for derivative separability.

Defined residue equality as formal divisibility of the difference. Every
polynomial has a reduced representative, and two reduced representatives
in the same class are coefficientwise equal, regardless of trailing zeros.
Nonzero base-field constants cannot vanish modulo an irreducible polynomial.
This establishes key algebraic obligations for a root extension but does not
yet construct the quotient equivalence, operations, field instance or root.

Validation:34 small irreducible moduli over F2/F3/F5;517 nonzero residue
inverses checked against exhaustive multiplication tables,1653 representative
checks,12629 uniqueness pairs and93 nonzero constants. Certificates also
transport to unreduced representatives. Three reducible Y^2 moduli exhibit
nonzero nilpotents without inverses, preventing omission of irreducibility.
Full audit4433 PASS, allowed axioms only. Evidence:
results/irreducible-residue-inverse/.

Next: quotient congruence and well-defined arithmetic, then the field instance
and root evaluation. Rational-function field construction, useful branches,
full MCA exception bounds and protocol/QROM composition remain open.
Diagnostic1344645 B unchanged; feasibility NOT_PASSED.
Full NEAR1Pgas/PQ128/sub300000 B remain open.

## 2026-10-16 — Actual residue quotient and representative-independent arithmetic

Added PolynomialResidueQuotient.lean with fourteen audited public theorems.
Formal coefficient equality implies residue congruence; congruence is
reflexive, symmetric and transitive and respects addition, negation and
multiplication. These proofs define an actual Setoid/Quotient and lift the
three arithmetic operations with their representative-independence proofs.
Quotient equality is exactly divisibility of the representative difference;
being the zero class is exactly divisibility by the modulus.

Lifted multiplication associativity, commutativity and distributivity to the
quotient. For an irreducible modulus, every nonzero quotient element has an
inverse quotient element, and zero and one are distinct. This goes beyond
representative-level witnesses but does not yet install a complete Lean Field
instance or construct the embedded coefficient map and root evaluation.

Validation:48 nonzero monic moduli over F2/F3/F5,16578 representative-
independence pairs and398164 associativity/distributivity triples. Checked295
nonzero inverses under irreducible moduli and122 nonunit elements under
reducible moduli. Full audit4447 PASS, allowed axioms only. Evidence:
results/polynomial-residue-quotient/.

Next: complete the additive/identity laws and Field instance, embed the base
field, and prove the class of X is a root of the mapped modulus. Rational-
function construction, useful branches, full MCA exceptions and protocol/QROM
composition remain open. Diagnostic1344645 B unchanged; feasibility NOT_PASSED.
Full NEAR1Pgas/PQ128/sub300000 B remain open.

## 2026-10-16 — Constructed field extension and actual polynomial roots

Added PolynomialResidueField.lean with six audited public theorems. Completed
all commutative-ring laws, casts, scalar operations and powers for the residue
quotient. For an irreducible modulus, classical selection of the already
proved inverse witnesses yields a complete Lean.Grind.Field structure with
zero inverse zero. The field-existence audit entry covers the construction
and every field axiom; no field structure or root-existence oracle is assumed.
This is a noncomputable existence construction, not a production field backend.

Constructed the canonical unital coefficient map and proved it injective.
Horner evaluation of any transported polynomial at the class of X equals
its residue class. Thus the mapped irreducible modulus has an actual root.
The earlier transported derivative certificate proves this root smooth when
the modulus degree is positive and below the characteristic. Combining the
proved irreducible-divisor existence theorem with this construction also
supplies a root extension for every nonzero nonconstant polynomial.

Validation:34 constructed small-field quotients,317711 additive associativity
triples,8265 cast/scalar checks,34 modulus roots,23 below-characteristic smooth
roots,1020 variable-evaluation identities and1020 composite-root checks,
including repeated-modulus products. Base-field constants remain distinct.
Full audit4453 PASS, allowed axioms only. Evidence:
results/polynomial-residue-field/.

Next: construct the rational-function coefficient field and connect the
algebraic root extension to the useful Hensel branches and specialization
exception bounds. Generic algebraic root-extension existence is now supplied;
full MCA exceptions and protocol/QROM composition remain open.
Diagnostic1344645 B unchanged; feasibility NOT_PASSED.
Full NEAR1Pgas/PQ128/sub300000 B remain open.

## 2026-10-16 — Formal polynomial fractions and rational-function quotient

Added PolynomialFractions.lean with seventeen audited public theorems.
The polynomial residue ring at modulus zero is proved to identify exactly
coefficient-equal polynomials and is an integral domain with cancellation.
Polynomial fractions carry formally nonzero denominators. Cross multiplication
is proved to be an equivalence relation, including transitivity by cancellation
of the middle denominator. Addition, multiplication, negation and reciprocal
respect the relation and descend to an actual rational-function quotient.

The denominator-one polynomial embedding is injective. Zero is characterized
by a zero numerator, reciprocal maps zero to zero, and every nonzero rational
function multiplies by its reciprocal to one. No evaluation-domain or sampled
identity premise appears. A complete rational-function Field instance remains
to be installed, and no total specialization map at poles is claimed.

Validation:600 fraction cases checked against independent gcd normalization,
including46 zero numerators, plus3208 common safe specializations. Four
nonzero denominators Z^p-Z vanish everywhere in their base fields but remain
valid formal denominators; four Z/Z examples preserve the distinction between
rational equality and a representative's evaluation domain. Formally zero
denominators are rejected. Full audit4470 PASS, allowed axioms only. Evidence:
results/polynomial-fractions/.

Next: complete the rational-function Field instance and connect specialization
to pole bounds, then use the algebraic extension and Hensel construction for
useful branches. Full MCA exceptions and protocol/QROM composition remain open.
Diagnostic1344645 B unchanged; feasibility NOT_PASSED.
Full NEAR1Pgas/PQ128/sub300000 B remain open.

## 2026-10-16 — Rational-function field and transcendental indeterminate

Added PolynomialRationalField.lean with eight audited public theorems.
Completed all ring laws, casts, scalar operations and natural powers for the
formal fraction quotient; the proved reciprocal laws yield a complete
Lean.Grind.Field instance. The field-existence audit entry covers every field
axiom. No ambient rational-function field is assumed.

The polynomial embedding preserves addition/multiplication and identifies
exactly coefficient-equal polynomials. Constructed an injective unital base-
field coefficient map and an IsCharP instance inheriting the base
characteristic. Horner evaluation of a transported polynomial at the rational
indeterminate returns its embedded formal polynomial. Therefore no nonzero
formal base polynomial vanishes at that indeterminate: transcendence is
proved, including over finite fields with nonzero vanishing functions.
The constructed coefficient field can now instantiate the generic algebraic
root-extension and degree-bounded smoothness constructions.

Validation:400 field-law cases against independent gcd normalization,
112 characteristic/cast checks,400 indeterminate-evaluation checks and four
Z^p-Z negatives distinguishing formal polynomials from base-field functions.
Full audit4478 PASS, allowed axioms only. Evidence:
results/polynomial-rational-field/.

Next: safe specialization of formal rational functions, linkage to guarded
expressions and pole bounds, then useful algebraic branches and complete MCA
exceptions. Protocol/QROM composition remains open. Diagnostic1344645 B
unchanged; feasibility NOT_PASSED. Full NEAR1Pgas/PQ128/sub300000 B remain open.

## 2026-10-16 — Partial specialization of constructed rational functions

Added RationalFunctionSpecialization.lean with eleven audited public theorems.
Evaluation descends to the formal polynomial quotient and preserves addition
and multiplication. Equivalent fractions have the same value whenever both
denominators evaluate nonzero. Defined partial rational-function specialization
by existence of a safe representative, and proved uniqueness, addition and
multiplication preservation, plus reciprocal specialization when the value
is nonzero. No total field evaluation at poles is claimed.

Formal regularity ensures the earlier expression fraction has a nonzero
formal denominator, so it now constructs an actual rational-function element.
Its guarded evaluator specializes that element on the original syntactic
safe domain. Equal formal expression functions therefore evaluate equally
where both expressions are safe. Their totalized evaluator disagreement count
is bounded by the sum of their guard-degree budgets on distinct samples.
This is a syntactic-pole bound, not the complete MCA exceptional-set bound.

Validation:484 regular expressions,3254 guarded-function bridge checks,
2805 safe identities,2818 safe arithmetic checks and2348 safe reciprocals.
All289 evaluator disagreements occur at excluded poles and satisfy the guard
bound. Cancellation and reciprocal-at-zero negatives distinguish intrinsic
rational values from unsafe representative evaluation. Full audit4489 PASS,
allowed axioms only. Evidence: results/rational-function-specialization/.

Next: connect algebraic root branches and Hensel construction to specialization,
including the additional algebraic exceptional points. Full MCA and protocol/
QROM composition remain open. Diagnostic1344645 B unchanged; feasibility
NOT_PASSED. Full NEAR1Pgas/PQ128/sub300000 B remain open.

## 2026-10-16 — Specialized algebraic-root smoothness feeds Hensel lifting

Added AlgebraicRootSpecialization.lean with six audited public theorems.
Defined position-preserving coefficient specialization for polynomials in Y
with rational-function coefficients. Horner evaluation and derivative
evaluation preserve this partial relation. A unit rational Bezout certificate
therefore supplies nonzero derivative at every specialized root whenever
its polynomial and two certificate polynomials specialize safely.

The existing irreducible low-degree theorem now supplies the certificate
and its specialization guarantee together over the constructed rational
field. Composed the resulting nonzero derivative with the actual initial-Y
polynomial and operational Hensel slope, yielding finite lifts at every
precision without a separate smoothness oracle. No polynomial convergence,
bounded-degree exact branch or general branch-specialization theorem is claimed.

Validation:233 parameterized quadratic certificates Q=Y^2+b(Z)Y+c(Z), with
A=-4/(b^2-4c), B=(2Y+b)/(b^2-4c). Verified699 formal coefficient identities,
24144 safe certificate evaluations,1822 specialized smooth roots and5466
finite Hensel lifts. All191 singular roots occur at the191 excluded
discriminant points; the fixture-specific root count satisfies its actual
discriminant degree bound. Full audit4495 PASS, allowed axioms only. Evidence:
results/algebraic-root-specialization/.

Next: general coefficient/certificate denominator degree bounds and preservation
of the relevant algebraic branch under specialization. Full MCA exceptions and
protocol/QROM composition remain open. Diagnostic1344645 B unchanged;
feasibility NOT_PASSED. Full NEAR1Pgas/PQ128/sub300000 B remain open.

## 2026-10-16 — Constructed coefficient guards and singular-specialization counts

Added RationalCoefficientGuards.lean with nine audited public theorems.
Every coefficient of the actual rational-function quotient has a polynomial
numerator/nonzero denominator presentation, and every polynomial has a finite
list of such presentations preserving coefficient positions. The product of
all denominators is formally nonzero and has degree at most the sum of the
individual presentation degree bounds. Outside its roots, all coefficient
specialization witnesses are constructed automatically.

A combined guard for a polynomial and both Bezout coefficient polynomials
therefore guarantees smooth specialized roots. Singular-root specialization
points are contained in the guard roots and bounded by its degree budget on
distinct samples. Irreducibility below the characteristic now yields the
certificate, finite presentations, nonzero guard and singular-point bound
without assuming per-point coefficient specialization. The bound remains
presentation-dependent; it is NOT a bound from the original interpolation
dimensions or the complete MCA exceptional-set theorem.

Validation:320 coefficient families,4952 safe coefficient evaluations and179
quadratic certificate presentations with deliberately introduced cancellable
denominator factors and padding. All192 singular points lie inside the shared
guard;764 roots outside it are smooth. Full audit4504 PASS, allowed axioms
only. Evidence: results/rational-coefficient-guards/.

Next: bound certificate denominator degrees from source polynomial degrees,
and preserve useful algebraic branches under specialization. Full MCA and
protocol/QROM composition remain open. Diagnostic1344645 B unchanged;
feasibility NOT_PASSED. Full NEAR1Pgas/PQ128/sub300000 B remain open.

## 2026-10-16 — Bounded Bezout multipliers and finite coefficient checking

Added BoundedBezout.lean with four audited public theorems. Given any unit
certificate A*p+B*q=1, deg(p)<=m with m>0, and deg(q)=n, divide A by q and
adjust B to construct U,V with deg(U)<n and deg(V)<m. The constant q case is
handled explicitly. The bound on V follows from the formal leading-product
coefficient and the reconstructed identity, not a claimed algorithm invariant.

For degree-d irreducibles below the characteristic this supplies derivative
certificate multipliers of degree<d-1 and<d, including d=1. With these bounds,
checking the first2d-1 coefficients suffices for the full formal certificate.
The generic m+n finite-check theorem also handles constant q and padding.
These bound the algebraic-variable unknowns/equations; no parameter-variable
denominator-degree bound or formal matrix invertibility is claimed yet.

Validation:600 coprime inputs over F2/F3/F5/F17, all certificates deliberately
inflated by arbitrary polynomial syzygies and then reduced. All match an
independent finite coefficient-matrix solve, totaling3758 equations;120 cases
have constant q. A high-degree hidden coefficient demonstrates why the finite
check requires multiplier degree bounds. Full audit4508 PASS, allowed axioms
only. Evidence: results/bounded-bezout/.

Next: coefficient-system invertibility and a source-degree denominator bound,
then useful algebraic branch specialization. Full MCA and protocol/QROM
composition remain open. Diagnostic1344645 B unchanged; feasibility NOT_PASSED.
Full NEAR1Pgas/PQ128/sub300000 B remain open.

## 2026-10-16 — Bounded Bezout coefficient-map invertibility

Added BezoutSystemInvertibility.lean with four audited public theorems.
A unit Bezout certificate proves Euclid's divisibility lemma. Consequently,
a bounded syzygy U*p+V*q=0 with deg(U)<deg(q) must have both U and V zero.
Differences of solutions give uniqueness up to formal coefficient equality.

For every target of degree<m+n, divide A*target by q and adjust B*target to
construct U,V with deg(U)<n and deg(V)<m, satisfying U*p+V*q=target. The
leading-product argument proves the second bound. Together these prove the
bounded coefficient map is bijective, including constant-polynomial and
zero-target cases. These are algebraic polynomial-space results, not yet a
matrix determinant construction or parameter-variable denominator bound.

Validation:400 arbitrary-target systems compared with independent Gaussian
elimination, including151 cases with a constant polynomial and29 zero targets.
Exhaustively enumerated98 small coefficient maps (2184 vectors), checking
unique zero preimage and complete image. Three noncoprime examples exhibit
nonzero bounded kernels. Full audit4512 PASS, allowed axioms only. Evidence:
results/bezout-system-invertibility/.

Next: degree-controlled matrix inverse/denominator construction, then useful
algebraic branch specialization. Full MCA and protocol/QROM composition remain
open. Diagnostic1344645 B unchanged; feasibility NOT_PASSED.
Full NEAR1Pgas/PQ128/sub300000 B remain open.

## 2026-10-16 — Source-degree bound for polynomial Bezout determinants

Added PolynomialDeterminantDegree.lean with six audited public theorems.
Defined matching scalar and polynomial Laplace expansions using ordered
row/column minors, with empty determinant one. Proved parameter degree<=N*D
for N-row minors whose entries have degree<=D, and that polynomial evaluation
commutes with this determinant construction. Conditional on formal nonzeroness,
at most N*D distinct sample points make the specialized determinant vanish.

Defined the bounded Bezout coefficient matrix and its derivative specialization.
Multiplying source coefficients by derivative indices preserves parameter
degree in every characteristic. The degree-d derivative matrix has size2d-1,
and its polynomial determinant has degree<=(2d-1)*D. Nonzeroness from the
previous coefficient-map bijectivity theorem, and the determinant's inverse/
shared-denominator interpretation, remain separate unproved obligations.

Validation:240 polynomial matrices checked against independent permutation
expansion,1620 specialized numeric Gaussian determinants and220 nonzero
root-count bounds.100 derivative Bezout matrices satisfy the source-degree
bound,99 with nonzero determinants. A constant singular matrix demonstrates
why the exceptional-point count needs nonzeroness. Full audit4518 PASS,
allowed axioms only. Evidence: results/polynomial-determinant-degree/.

Next: determinant nonzeroness and inverse-certificate identity, then connect
the bounded denominator to algebraic branch specialization. Full MCA and
protocol/QROM composition remain open. Diagnostic1344645 B unchanged;
feasibility NOT_PASSED. Full NEAR1Pgas/PQ128/sub300000 B remain open.

## 2026-10-16 — Determinant row linearity and rational-field transport

Added DeterminantRowLinearity.lean with five audited public theorems.
The Laplace minor depends only on its selected rows. For distinct row labels,
replacing any selected row by a linear combination gives the same linear
combination of determinants; a zero selected row gives zero determinant.
These are general field results preserving the original column order/signs.

Proved that embedding the explicit polynomial determinant into the constructed
rational-function field gives exactly the scalar determinant of the embedded
matrix. Formal polynomial nonzeroness is therefore equivalent to determinant
nonzeroness in that field, without a finite evaluation-domain assumption.
This prepares the connection to the previously proved coefficient-map
invertibility but does not yet establish determinant alternation, nonzeroness
from invertibility, or an adjugate/shared-denominator identity.

Validation:400 row-linearity cases and400 zero-row cases over F2/F3/F5/F17,
plus100 polynomial-to-rational determinant transports (79 nonzero). An empty
minor example confirms selected-row membership cannot simply be omitted.
Full audit4523 PASS, allowed axioms only. Evidence:
results/determinant-row-linearity/.

Next: determinant alternation and connection to inverse maps, then the
shared-denominator certificate. Full MCA and protocol/QROM composition remain
open. Diagnostic1344645 B unchanged; feasibility NOT_PASSED.
Full NEAR1Pgas/PQ128/sub300000 B remain open.

## 2026-10-16 — Determinant alternation in every characteristic

Added DeterminantCofactorFold.lean with nine audited public theorems.
A signed column-selection fold is proved exactly equal to the existing indexed
Laplace expansion. Its linearity, paired-selection sign reversal and direct
cancellation of symmetric paired contributions are proved recursively.
The cancellation proof never divides by two.

Derived sign reversal on exchanging the first two determinant rows and on
adjacent row exchanges at arbitrary positions. Equal first rows give zero;
this extends to two equal rows separated by any prefix/middle/suffix. These
results include characteristic two, where determinant=-determinant alone
would not establish zero. No new determinant unrelated to the existing
polynomial degree construction is substituted.

Validation:320 indexed-fold identities,320 double-selection swaps,320 symmetric
cancellations,320 arbitrary adjacent-row swaps and320 separated-equal-row
zeros, including80 characteristic-two row cases. Explicit F2 example rejects
the invalid divide-by-two inference. Full audit4532 PASS, allowed axioms only.
Evidence: results/determinant-cofactor-fold/.

Next: determinant nonzeroness from inverse maps and the shared-denominator
certificate identity. Full MCA and protocol/QROM composition remain open.
Diagnostic1344645 B unchanged; feasibility NOT_PASSED.
Full NEAR1Pgas/PQ128/sub300000 B remain open.

## 2026-10-16 — Cramer row identities and conditional shared denominator

Added DeterminantRowReplacement.lean with six audited public theorems.
Two selected rows with equal entries force zero; replacing one selected row
by another is a direct instance. Finite row-combination expansion follows
from determinant row linearity. All off-diagonal terms vanish by the proved
alternation, giving the Cramer row identity: replacement by a combination of
selected rows multiplies the determinant by that row's coefficient.

For a solved row system and nonzero determinant, every solution entry is
its row-replacement determinant divided by the common matrix determinant.
Also proved that a nontrivial row dependence forces determinant zero. These
results do not yet prove the converse or determinant nonzeroness from the
previous inverse-map theorem. The row-form system still needs connection to
the chosen Bezout coefficient-matrix orientation.

Validation:1473 Cramer identities,1377 copied-row zeros,322 nonsingular and158
singular matrices over F2/F3/F5/F17.992 shared-denominator entries agree with
independent transposed-system elimination; four explicit dependencies force
zero determinant. Full audit4538 PASS, allowed axioms only. Evidence:
results/determinant-row-replacement/.

Next: discharge determinant nonzeroness from invertibility and connect the
Cramer formula to the Bezout matrix and source-degree bounds. Full MCA and
protocol/QROM composition remain open. Diagnostic1344645 B unchanged;
feasibility NOT_PASSED. Full NEAR1Pgas/PQ128/sub300000 B remain open.

## 2026-10-16 — Determinant nonzeroness from a row inverse

Added DeterminantRowPermutations.lean and DeterminantRowSpan.lean with nine
audited public theorems. Every row permutation scales all minors by one
nonzero factor; repeated row labels give zero. An equally long selection
from a singular distinct row family also has zero determinant, by splitting
between repeated selections and permutations. Row reindexing is linked
exactly to row selection in the existing determinant.

A vector-list form is proved equal to that determinant and used to expand
finite combinations in every row. Consequently any equally large family of
linear combinations of a singular row family remains singular. The ordered
identity minor has determinant one. A row inverse producing identity thus
forces the original determinant nonzero, with no assumed determinant
multiplicativity or nonsingularity oracle. This closes the generic implication;
the concrete Bezout encoding/orientation still must provide that inverse.

Validation:400 row permutations,329 singular row-combination families,
5648 singular row selections and289 constructed row inverses (2226 entries),
including71 empty identity cases and characteristic two. Full audit4547 PASS,
allowed axioms only. Evidence: results/determinant-row-span/.

Next: connect bounded polynomial solutions to the explicit Bezout matrix
and compose nonzeroness, Cramer identity and source-degree denominator bounds.
Full MCA and protocol/QROM composition remain open. Diagnostic1344645 B
unchanged; feasibility NOT_PASSED. Full NEAR1Pgas/PQ128/sub300000 B remain open.

## 2026-10-16 — Explicit Bezout matrix inverse and common determinant

Added BezoutCoefficientMatrix.lean with five audited public theorems.
Finite coefficient convolution identifies the explicit matrix action with
U*p+V*q, including trailing-zero representations. Solving each monomial
target constructs a row inverse for the transposed coefficient matrix; its
identity holds at every output coefficient, including beyond the square block.
The proved row-inverse criterion now establishes this determinant nonzero
from a unit Bezout certificate. Every bounded solution coefficient satisfies
the Cramer formula with that same determinant denominator.

Validation:320 coprime systems,10611 coefficient actions,923 monomial targets,
4396 Cramer entries checked against Euclidean reduction and independent
elimination. Includes24 empty matrices,159 constant cases,168 loose bounds
on p's degree and four noncoprime singular counterexamples. Full audit4552
PASS, allowed axioms only. Evidence: results/bezout-coefficient-matrix/.

Next: transport the explicit matrix over rational functions to polynomial
entries and compose nonzeroness with source-degree denominator bounds.
Full MCA and protocol/QROM composition remain open. Diagnostic1344645 B
unchanged; feasibility NOT_PASSED. Full NEAR1Pgas/PQ128/sub300000 B remain open.

## 2026-10-16 — Source-degree common Bezout denominator

Added BezoutPolynomialDenominator.lean with six audited public theorems.
Formal coefficient presentations identify the polynomial-entry transposed
matrix with the rational-function coefficient matrix. A unit certificate now
proves the explicit shared polynomial determinant nonzero. For source
coefficient degrees at most D, its degree is at most (n+m)*D, hence at most
(n+m)*D distinct specialization points annihilate it. No elimination pivot
or presentation-dependent denominator budget enters this bound.

Cramer replacement determinants give polynomial numerators over this same
denominator for every bounded solution coefficient. Numerators also have
degree at most (n+m)*D when target entries have degree at most D, including
constant targets. Derivative-certificate instantiation and safe coefficient
specialization still require composition; this does not finish useful-branch
extraction or the protocol soundness argument.

Validation:333 nonzero polynomial systems,1815 exact coefficient identities,
2085 safe specializations,257 exceptional points,27 singular systems and28
empty systems. Four nonzero formal denominators vanishing at every base-field
point guard against assuming existence of a safe specialization. Full audit4558
PASS, allowed axioms only. Evidence: results/bezout-polynomial-denominator/.

Next: compose the degree-controlled denominator with the derivative Bezout
certificate and specialization/Hensel interfaces. Full MCA and protocol/QROM
composition remain open. Diagnostic1344645 B unchanged; feasibility NOT_PASSED.
Full NEAR1Pgas/PQ128/sub300000 B remain open.

## 2026-10-16 — Derivative certificate with source-degree denominator

Added DerivativeBezoutDenominator.lean with five audited public theorems.
Formal derivative coefficient entries transport to the rational-function
field. For an irreducible source of Y-degree d with 0<d<characteristic,
the row-oriented derivative determinant is nonzero without an assumed unit
certificate. Its parameter degree is at most (2d-1)*D when source coefficient
degrees are at most D; the same bound controls distinct denominator roots.

The bounded derivative Bezout certificate exists, and every one of its
2d-1 coefficient coordinates has an explicit polynomial Cramer numerator
over that same determinant. This supplies the certificate interface needed
for safe specialization; the general specialization/Hensel composition is
not yet proved from this denominator condition alone.

Validation:240 Eisenstein families Y^d+(Z-z0)*C(Y),1278 exact certificate
coefficient identities,1303 safe smooth roots and192 denominator exception
points. Four Y^p-Z cases demonstrate failure of derivative separability when
the degree reaches the characteristic. Full audit4563 PASS, allowed axioms
only. Evidence: results/derivative-bezout-denominator/.

Next: specialize the bounded certificate coefficients using their shared
denominator and compose root smoothness/Hensel lifting. Full MCA and
protocol/QROM composition remain open. Diagnostic1344645 B unchanged;
feasibility NOT_PASSED. Full NEAR1Pgas/PQ128/sub300000 B remain open.

## 2026-10-16 — Shared denominator protects specialization and Hensel lifts

Added SharedDenominatorSpecialization.lean with seven audited public theorems.
Polynomial expressions specialize everywhere; a nonvanishing denominator
protects every quotient numerator. Coordinatewise partial specialization
constructs a polynomial preserving coefficient-list length and zero padding.
The bounded derivative certificate's Cramer formulas therefore yield safe
specializations of both multipliers whenever the single derivative
shared denominator is nonzero. Coordinates beyond the degree bounds are
handled as zero, without multiplying extra coefficient guards.

Composing with the existing certificate theorem proves smoothness of every
root of a specialized source, and supplies the actual finite Hensel lift:
correct initial coefficient, degree at most the requested precision, and
residual vanishing to precision+1. For any family specializing the source,
singular specialization points have the source-degree bound (2d-1)*D.
The source-specialization relation is still an explicit interface premise;
useful-branch extraction, algebraic extension specialization and global MCA
coverage are not established by these local theorems.

Validation:240 Eisenstein families,1260 exact certificate coefficient
identities,1314 safe smooth roots,3942 finite Hensel lifts and196 singular
specialization points, all inside the denominator zero set. Four inseparable
characteristic-degree counterexamples retained. Full audit4570 PASS, allowed
axioms only. Evidence: results/shared-denominator-specialization/.

Next: connect the source family/extension-field branch interfaces to this
bounded exceptional set, then establish useful-branch forcing and coverage.
Full MCA and protocol/QROM composition remain open. Diagnostic1344645 B
unchanged; feasibility NOT_PASSED. Full NEAR1Pgas/PQ128/sub300000 B remain open.

## 2026-10-16 — Explicit polynomial parameter families and dense source lifting

Added PolynomialParameterFamily.lean with five audited public theorems.
A list of polynomial parameter coefficients embeds into the rational-function
field with exact coefficient extraction, including out-of-range indices and
trailing zeros. Its direct evaluation automatically satisfies the partial
specialization interface at every point. The singular-point bound (2d-1)*D
therefore applies to explicit bivariate source data without a separate
coefficient-specialization oracle.

For dense Q(X,Y,Z), the X=0 polynomial obtained after specializing Z equals
specialization of the explicit initial coefficient rows. This discharges the
source-specialization premise of the finite Hensel theorem. The resulting
lifting theorem assumes that the initial polynomial is irreducible; it does
not infer this from irreducibility of Q. General initial-factor selection,
other-factor collisions and useful-branch coverage remain open.

Validation:200 dense source families,10833 coefficient-specialization checks,
3750 finite Hensel lifts,100 singular specialization points and212 empty
source rows. Full audit4575 PASS, allowed axioms only. Evidence:
results/polynomial-parameter-family/.

Next: extend the branch interface to selected initial irreducible factors
and account for other-factor collisions before useful-branch forcing.
Full MCA and protocol/QROM composition remain open. Diagnostic1344645 B
unchanged; feasibility NOT_PASSED. Full NEAR1Pgas/PQ128/sub300000 B remain open.

## 2026-10-16 — Selected-factor smoothness and lifting the full source

Added SelectedFactorSmoothness.lean with six audited public theorems.
The derivative product rule at a point follows from multiplicative formal
translation, including small characteristic and degree beyond field size.
At a root of h, the product h*g is smooth iff h is smooth there and g does
not vanish. A repeated selected factor is singular at its roots. The result
transfers through coefficientwise equality, so padding does not change it.

A unit Bezout certificate between h and g supplies noncollision. The actual
source's finite Hensel lift now follows from a selected smooth initial factor
and a nonvanishing complement; irreducibility of the entire initial polynomial
is unnecessary. Selected-factor existence, source-degree collision guards
and coverage remain separate obligations; noncollision is not inferred from
mere distinctness of formal factors.

Validation:2700 derivative-product evaluations,374 selected-root criteria,
103 colliding roots,374 repeated-factor singular roots,233 unit-certificate
noncollisions and573 actual-source finite lifts. Explicit collisions of two
individually smooth factors included in all four characteristics. Full audit4581
PASS, allowed axioms only. Evidence: results/selected-factor-smoothness/.

Next: specialize a coprime factor/complement certificate with a shared
degree-controlled denominator and bound collision points. Then connect
factor selection, useful-branch forcing and coverage. Full MCA and
protocol/QROM composition remain open. Diagnostic1344645 B unchanged;
feasibility NOT_PASSED. Full NEAR1Pgas/PQ128/sub300000 B remain open.

## 2026-10-16 — Source-degree factor-collision guard

Added FactorCollisionGuard.lean with five audited public theorems.
An arbitrary unit Bezout certificate between polynomial parameter families
reduces to bounded multipliers; their Cramer coordinates specialize wherever
the common determinant does not vanish. Partial specialization of the unit
identity excludes common roots. For explicit source lists of Y-degree bounds
m,n and coefficient parameter degree at most D, collision parameter points
are bounded by (m+n)*D. A positive selected-factor degree is required; constant
complements are supported. A unit certificate remains an explicit premise.

The derivative and collision guards now compose with selected-factor
smoothness to lift the full source from a selected irreducible initial factor.
This requires a coefficientwise specialized factorization and the coprime
certificate. It does not yet derive factor selection/certificates from the
full general source or establish useful-branch forcing and coverage.

Validation:245 coprime parameter pairs,658 exact certificate coefficient
identities,158 collision parameter points,1520 protected selected roots,
2832 guarded full-source lifts and77 constant complements.15 zero determinants
rejected. Four explicit distinct-factor collisions show why formal distinctness
alone is insufficient. Full audit4586 PASS, allowed axioms only. Evidence:
results/factor-collision-guard/.

Next: derive selected-factor/complement coprimality from squarefreeness,
connect factor selection and specialization, and prove useful-branch coverage.
Full MCA and protocol/QROM composition remain open. Diagnostic1344645 B
unchanged; feasibility NOT_PASSED. Full NEAR1Pgas/PQ128/sub300000 B remain open.

## 2026-10-16 — Source separability supplies factor certificates

Added SquarefreeFactorCertificates.lean with six audited public theorems.
The formal derivative product rule is recovered by evaluating the existing
pointwise product rule at a transcendental rational indeterminate, then using
formal embedding injectivity. No inference from finite base-field evaluation
is used. Derivatives also preserve coefficient equality and padding.

Given P=h*g and S*P+T*P'=1, explicit multipliers U=S*g+T*g', V=T*h'
satisfy U*h+V*g=1. Replacing V by T*g supplies U*h+(T*g)*h'=1.
Thus source separability supplies both factor/complement coprimality and
selected-factor separability. Root conditions and the source-degree collision
count are composed with these constructed certificates. A derivative unit
certificate for P and a coefficientwise factorization remain premises;
separability of arbitrary initial specialization is not assumed automatic.

Validation:720 formal derivative product identities,401 constructed certificate
pairs,296 protected selected roots and319 rejected nonsquarefree products.
Four repeated-factor negatives and four finite-field vanishing-polynomial
counterexamples retained. Full audit4592 PASS, allowed axioms only. Evidence:
results/squarefree-factor-certificates/.

Next: derive suitable separable initial data and select factors with controlled
parameter degree, then connect useful-branch forcing and coverage. Full MCA
and protocol/QROM composition remain open. Diagnostic1344645 B unchanged;
feasibility NOT_PASSED. Full NEAR1Pgas/PQ128/sub300000 B remain open.

## 2026-10-16 — Constructed separable factor, root field and Hensel lift

Added SeparableFactorSelection.lean with six audited public theorems.
Coefficient identities transport through field maps. For a nonzero nonconstant
source with a derivative unit certificate, the existing factorization theorem
now selects an actual irreducible factor and complement, both inheriting the
source's algebraic-variable degree bound. Explicit inherited certificates prove
selected-factor separability and complementary coprimality.

The constructed quotient field contains a root of this factor. The same root
annihilates the full source, has nonzero full-source derivative, and does not
annihilate the complement. Initial-polynomial extraction commutes with field
extension, yielding finite Hensel lifts at every precision in the constructed
field. No base-field polynomial initial branch is assumed. These statements
are over a generic field, hence also apply to the rational-function field;
they do not yet control parameter degrees of rational coefficient
representatives or specialize the constructed algebraic extension.

Validation:34 selected quotient fields,24 nonbase-field roots,210 smooth
full-source roots and1050 extension-field Hensel steps. Full audit4598 PASS,
allowed axioms only. Evidence: results/separable-factor-selection/.

Next: parameter-degree control and safe specialization of algebraic extensions,
then useful-branch forcing and coverage. Source separability at a suitable
initial slice still requires proof. Full MCA and protocol/QROM composition
remain open. Diagnostic1344645 B unchanged; feasibility NOT_PASSED.
Full NEAR1Pgas/PQ128/sub300000 B remain open.

## 2026-10-16 — Safe long division for extension specialization

Added RegularPolynomialDivision.lean with five audited public theorems.
Coefficient regularity at a parameter point is preserved under polynomial
addition, subtraction and multiplication. Long division produces regular
quotient and remainder coefficients when the divisor's specialized leading
coefficient is nonzero. The proof follows the actual degree-reducing
corrections and uses partial reciprocal specialization only at that leading
value. Constant divisors, zero input and trailing zeros are supported.

For an exactly divisible regular input, reduced-residue uniqueness forces
the regular remainder to zero, yielding a regular quotient even if the
original divisibility witness had a pole-bearing representation. This
removes the hidden-quotient-pole obstacle to representative-independent
algebraic-extension specialization. The latter composition remains next;
no total evaluation homomorphism on the rational-function field is claimed.

Validation:220 regular rational-function divisions,112 exact divisions,
360 safe output coefficients and73 constant divisors, checked against
independent numeric division after specialization. Four examples with a
vanishing specialized leading coefficient force quotient poles. Full audit4603
PASS, allowed axioms only. Evidence: results/regular-polynomial-division/.

Next: prove equivalent regular residue representatives have the same value
at a specialized modulus root, then compose extension operations and lifting.
Parameter-degree control/useful-branch coverage and protocol/QROM composition
remain open. Diagnostic1344645 B unchanged; feasibility NOT_PASSED.
Full NEAR1Pgas/PQ128/sub300000 B remain open.

## 2026-10-16 — Well-defined partial algebraic residue specialization

Added AlgebraicResidueSpecialization.lean with six audited public theorems.
Coefficient-list specialization implies coefficient regularity at all indices.
For equivalent regular representatives, the preceding exact-quotient theorem
constructs a regular witness for their difference modulo the modulus. Evaluating
that identity at a specialized modulus root proves their values equal, provided
the specialized leading coefficient remains nonzero.

AlgebraicResidueValueAt is an existential relation on actual residue classes,
witnessed by a regular representative and its specialized polynomial. Value
uniqueness now descends to the quotient; addition and multiplication preserve
the partial domain and values. No total evaluation homomorphism is introduced.
Inversion requires more than nonzeroness at the chosen root: for h=Y^2-Z,
Y-1 is nonzero at z=1,a=-1 but its coefficientwise inverse has a pole at Z=1,
as the conjugate root a=1 annihilates Y-1. A sufficient certificate/norm guard
must be used for the Hensel slope inverse.

Validation:193 equivalent-representative pairs,134 specialized-root value
equalities,268 quotient add/mul values,4 leading-degree-drop counterexamples
and3 inverse-domain counterexamples. Full audit4609 PASS, allowed axioms only.
Evidence: results/algebraic-residue-specialization/.

Next: guarded derivative inversion and composition of algebraic-extension
Hensel specialization. Parameter-degree control/useful-branch coverage and
protocol/QROM composition remain open. Diagnostic1344645 B unchanged;
feasibility NOT_PASSED. Full NEAR1Pgas/PQ128/sub300000 B remain open.

## 2026-10-16 — Guarded actual algebraic derivative inverse

Added AlgebraicGuardedInverse.lean with three audited public theorems.
For A*h+B*p=1 with irreducible h, the actual quotient-field inverse of the
class of p equals the class of B. Safe specialization of h,A,B and the
evaluation of p at a specialized modulus root proves both nonzero numeric
value and partial specialization of the actual inverse to its reciprocal.
This uses an inverse representative supplied by the certificate, not an
invalid assertion that nonzero value at one root protects every inverse.

The source-degree derivative determinant supplies the safe bounded certificate,
so its guard now protects the actual inverse of the modulus derivative in the
constructed algebraic field. Full extension-field Hensel specialization still
needs composition of coefficient operations, source evaluation and the
operational slope with this interface.

Validation:240 irreducible parameter families and polynomial quotient inverse
checks,1355 guarded root inverse values agreeing with independent numeric
Euclid,167 excluded denominator points. Full audit4612 PASS, allowed axioms
only. Evidence: results/algebraic-guarded-inverse/.

Next: compose algebraic and numeric Hensel recurrence specialization, including
the actual full-source slope where it differs from the modulus derivative.
Parameter-degree control/useful-branch coverage and protocol/QROM composition
remain open. Diagnostic1344645 B unchanged; feasibility NOT_PASSED.
Full NEAR1Pgas/PQ128/sub300000 B remain open.

## 2026-10-16 — Partial specialization through the Hensel recurrence

Added PartialHenselSpecialization.lean with seven audited public theorems.
A partial arithmetic relation preserving zero,one,minus one,addition and
multiplication lifts to polynomial products and bivariate substitution.
The actual Hensel recurrence preserves its initial coefficient unconditionally;
the operational slope thus equals the initial slope at every step. One related
initial slope inverse supplies coefficientwise specialization of all finite
lifts, without an unconditional inverse-preservation axiom.

The relation is instantiated with AlgebraicResidueValueAt using the proved
quotient arithmetic and base-constant witnesses. Consequently actual algebraic
Hensel lift coefficients specialize to the numeric lift, given related source
rows, the initial root and its guarded initial slope inverse. The concrete
source/selected-factor interfaces and full-source slope still need to supply
these premises in the general branch construction.

Validation:36 rational-algebraic source systems,1080 algebraic/numeric lift
pairs and3240 coefficient specialization comparisons;27 derivative guard
points excluded. Includes characteristic two via Y^2+Y-Z. Full audit4619 PASS,
allowed axioms only. Evidence: results/partial-hensel-specialization/.

Next: discharge the concrete source, algebraic root and full-source slope
interfaces, then parameter-degree/useful-branch forcing and coverage. Full
MCA and protocol/QROM composition remain open. Diagnostic1344645 B unchanged;
feasibility NOT_PASSED. Full NEAR1Pgas/PQ128/sub300000 B remain open.

## 2026-10-16 — Dense algebraic source and full-source slope specialization

Added DenseAlgebraicHensel.lean with six audited public theorems.
Regular rational constants and the residue indeterminate have explicit
algebraic specialization witnesses. Dense trivariate source coefficients now
supply the related-input-row premise automatically, including empty rows and
padding. Initial extraction commutes with rational embedding. The operational
algebraic slope is exactly the residue class of the derivative of the full
initial source polynomial, rather than necessarily the modulus derivative.

A safely specialized unit certificate between the modulus and that full-source
derivative therefore supplies the actual inverse needed by the recurrence.
The resulting dense-source theorem specializes every finite algebraic lift
coefficient to the numeric lift. The extension modulus may be a proper factor
of the initial polynomial. Safe certificate and specialized modulus root
remain premises; general branch guard extraction/degree control remain open.

Validation:36 proper-factor source systems with initial source
(Y^2+bY-Z)*(Y-c),750 algebraic/numeric lift pairs and2250 coefficient
comparisons;60 derivative/collision guard points excluded. The test was fixed
for a variable-shadowing error before its passing run. Full audit4625 PASS,
allowed axioms only. Evidence: results/dense-algebraic-hensel/.

Next: derive full-source modular certificate guards and bounds from selected
branch data, then useful-branch forcing and coverage. Full MCA and protocol/QROM
composition remain open. Diagnostic1344645 B unchanged; feasibility NOT_PASSED.
Full NEAR1Pgas/PQ128/sub300000 B remain open.

## 2026-10-16 — One source-degree guard for the full algebraic lifting slope

Added SelectedSourceSlopeGuard.lean with six audited public theorems.
From P=h*g and S*P+T*P'=1, the explicit identity (S*g)*h+T*P'=1
supplies the modular full-source slope certificate. SelectedSourceSlopeData
records concrete dense source and polynomial parameter factor rows, the
factorization and source certificate, a positive factor degree bound m, and
exact derivative degree n. These remain explicit input obligations.

The corresponding Bezout determinant is nonzero and has parameter degree at
most (m+n)*D when both source and selected-factor coefficient degrees are at
most D. Its nonvanishing constructs safe bounded certificate multipliers,
then discharges the dense algebraic Hensel specialization theorem at every
precision. One exceptional set therefore protects all lift coefficients;
there is no precision-dependent product of coefficient denominators.

Validation:36 source systems,132 exact modular certificate coefficients,
760 algebraic/numeric lift pairs and2280 coefficient comparisons;59 guard
points excluded. Nine characteristic-induced derivative degree drops use the
actual derivative degree. A test-loop variable collision was corrected before
the passing run. Full audit4631 PASS, allowed axioms only. Evidence:
results/selected-source-slope-guard/.

Next: derive polynomial parameter factor representations and degree bounds
from general source data, then useful-branch forcing and coverage. The record
does not assert those obligations automatically. Full MCA and protocol/QROM
composition remain open. Diagnostic1344645 B unchanged; feasibility NOT_PASSED.
Full NEAR1Pgas/PQ128/sub300000 B remain open.

## 2026-10-16 — Clear rational factor coefficients to polynomial parameter rows

Added RationalFactorClearing.lean with eight audited public theorems.
A presented coefficient times its denominator equals its formal numerator.
Recursive common-denominator clearing constructs polynomial parameter rows,
exactly equal after embedding to the original rational polynomial scaled by
a formally nonzero polynomial. Every rational-function polynomial has such
a representation. The algebraic-variable degree bounds and generic roots
are preserved, and nonzero scalar multiplication preserves irreducibility,
so clearing produces a valid irreducible modulus when the original is one.

This is a representation theorem, not a source-parameter-degree theorem.
Redundant denominator presentations can introduce arbitrary common content;
primitive normalization/Gauss-type descent is still needed before claiming
factor parameter degrees bounded by the original source. Safe specialization
may exclude newly introduced scalar zeros until that content is removed.

Validation:400 rational polynomial families,1253 exact cleared coefficient
identities,27507 safe root/evaluation comparisons and2223 nonzero-scalar
irreducibility checks. Twelve fixed-source examples demonstrate unbounded
clearing content. Full audit4639 PASS, allowed axioms only. Evidence:
results/rational-factor-clearing/.

Next: primitive content normalization and descent of rational factorization
to polynomial parameter data with source-controlled degree bounds. Full MCA,
useful-branch coverage and protocol/QROM composition remain open.
Diagnostic1344645 B unchanged; feasibility NOT_PASSED.
Full NEAR1Pgas/PQ128/sub300000 B remain open.

## 2026-10-16 — Primitive normalization of polynomial parameter rows

Added PolynomialContentNormalization.lean with seven audited public theorems.
Constructed nonzero greatest common content for any nonzero coefficient family,
quotient rows and exact reconstruction. Proved the normalized rows primitive,
transported reconstruction to the rational-function polynomial, and proved
that normalization preserves generic irreducibility.

Validation: 400 families, 2204 exact row reconstructions, 8000 universal common
divisor checks, 1605 primitive divisor checks, 30249 safe scaled evaluations,
and 16 redundant-denominator examples with content removed. Full audit
4646 PASS, allowed axioms only. Evidence: results/polynomial-content-normalization/.

Next: primitive-product/Gauss descent and source-controlled factor parameter
degrees, followed by useful-branch forcing and coverage. These are still open;
the normalization theorem alone does not establish the full MCA bound.
Diagnostic 1344645 B unchanged; feasibility NOT_PASSED.
Full NEAR 1Pgas, PQ128 composition, recursion and sub300000 B remain open.

## 2026-10-16 — Gauss primitive-product lemma over polynomial parameter rows

Added PrimitivePolynomialProduct.lean with four audited public theorems.
Explicit dense addition/multiplication of K[Z][Y] rows transports exactly to
K(Z)[Y] and to polynomial residue rings. A primitive row family stays nonzero
modulo every irreducible parameter polynomial. Reducing a hypothetical common
nonconstant divisor of the product to an irreducible divisor, then using the
constructed residue field and formal polynomial integral-domain theorem,
proves that the product of two primitive families is primitive. The argument
covers zero/padded rows, characteristic two and the zero candidate divisor.
No unique-factorization instance or sampled evaluation identity is assumed.

Validation: 400 random and 3217 exhaustive primitive products; 17700 residue
reductions; 2700 parameter-specialization checks. Negative regressions include
800 nonprimitive factors, four reducible residue moduli with zero divisors,
and four nonzero formal polynomials vanishing on the entire base field.
Full audit 4650 PASS, allowed axioms only. Evidence:
results/primitive-polynomial-product/.

Next: rational scalar descent for primitive factors and source-controlled
parameter-degree inheritance. The primitive-product lemma is one step in
Gauss descent, not the completed source-factor degree theorem. Useful-branch
forcing/coverage, full MCA and protocol/QROM composition remain open.
Diagnostic 1344645 B unchanged; feasibility NOT_PASSED.
Full NEAR 1Pgas, PQ128 composition, recursion and sub300000 B remain open.

## 2026-10-16 — Rational scalar and selected-factor Gauss descent

Added PrimitiveScalarDescent.lean with eight audited public theorems.
A finite polynomial row-span construction derives a nonzero common divisor
as a polynomial linear combination. Primitiveness turns this into a unit
combination. If a rational scalar sends every primitive row into K[Z], the
unit combination forces the scalar itself to have a polynomial representative.
This is a constructed proof, not a coprimality or integrality oracle.

Combined denominator clearing and content normalization to represent any
nonzero K(Z)[Y] polynomial as a nonzero rational scalar times a primitive
polynomial family. For a rational factorization of polynomial source data,
the primitive-product lemma and scalar descent produce a primitive polynomial
left factor and polynomial complement. The selected irreducible factor stays
irreducible over K(Z); the source identity is proved at every formal parameter
coefficient, including unequal lengths and padding. No source-controlled
parameter-degree bound is yet claimed.

Validation: 400 constructed unit combinations; 3200 scalar integrality checks
including 1407 nonpolynomial scalar rejections; 160 rational factorizations
reconstructing 466 source coefficients. Four nonprimitive and four zero-family
counterexamples exercise necessary premises. Full audit 4658 PASS, allowed
axioms only. Evidence: results/primitive-scalar-descent/.

Next formal obligation: source-controlled factor parameter-degree inheritance,
then useful-branch forcing and coverage. User requested an independent agent
process review; its preliminary finding recommends rechecking the concrete
size/security viability gate before extending the algebraic critical path.
Diagnostic 1344645 B unchanged; feasibility NOT_PASSED. Full NEAR 1Pgas,
PQ128 composition, recursion and sub300000 B remain open.

## 2026-10-16 — Reconcile feasibility and measure the complete fixture verifier

Following the independent process review, deferred further standalone MCA
algebra until a named full-byte/security candidate makes its remaining
obligations decisive. The previous scalar-descent checkpoint remains valid.
No theorem count is treated as compression or full-NEAR progress.

Added report_current_feasibility.py and results/current-feasibility.json.
The generator checks all 24 pins in the latest switch capture manifest,
reconciles actual retained file lengths with the codec component ledger,
and recomputes each larger-field schedule's conditional quantum ledger.
Fresh native-assisted full bundle verification passes. The six-case larger
field screen replays byte-identically; zero candidates meet both its partial
quantum bound and projected size target. This finite screen is not a universal
lower bound and omits costs explicitly retained in its scope. Ext10/C1 remains
570072–583800 bytes before excluded envelope costs.

Actual current bundle:1344645 B. Source values/authentication:493296 B.
Continuation values/authentication:693824 B. Eliminating all opening
authentication for free still leaves770517 B. Keeping all other components,
a replacement of the entire opening must cost at most146466 B for strict
sub300000 total; replacing the compression envelope allows190346 B. These
are accounting budgets, not secure deletion/substitution constructions.
The historical slice gate now points to current evidence while retaining
its older1863197-byte record as history. Six mutated evidence/ledger cases
are rejected; the strict299999-byte boundary is checked. No Lean changes.

Added measure_switch_verifier_work.py, covering the actual current contract,
call-link decoder, and compression envelope including local/GKR and PCS.
Measured104839 framed SHA384 calls /419568 compression blocks; identical
framed-input deduplication leaves40726 calls /242409 blocks. At the existing
128x6944 hash gadget this is802.65 GiB of dense u32 trace accounting after
sharing, NOT measured RAM/runtime/proof size. Sharing still needs authenticated
routing/equality constraints. The old PCS-only census is not substituted
for this complete-fixture workload.

Largest unique block tags include transcript/commit44326, Merkle nodes43072,
code-switch stage initialization37479, terminal GKR layouts31080, and Merkle
leaves11957. Code inspection confirms stage initialization hashes the full
derived weight vector, and authenticated response commits hash JSON openings.
No such binding has been removed. An optimized transcript would require a
new version, regenerated proofs, and exact derivation/provenance checks.

Next experiment: a bounded complete small recursive-verifier slice with
explicit public binding and no full-trace disclosure, recording full outer
bytes across workloads. First inspect deterministic transcript inputs and
hash-gadget routing so avoidable serialization is not mistaken for necessary
recursion cost. Existing recursive-pcs-root still discloses a full trace for
root linkage and is not a compression success. Evidence:
results/current-feasibility/ and results/switch-full-verifier-hash-work.json.
Full NEAR1Pgas/PQ128/recursive correctness/sub300000 B remain open; feasibility
NOT_PASSED. Source-controlled parameter degrees and full MCA remain open too.

## 2026-10-17 — Public-only private Merkle call routing for recursion

Corrected the current feasibility report's recursion baseline: the newer
recursive-single-root-root prototype already removed trace disclosure using
fixed-operand equalities under the single PCS root. It still requires original
inner proofs and native transcript/GKR/SHA384/Merkle checks. The older
recursive-pcs-root full-trace requirement is now explicitly historical.
This avoids repeating a solved root-linking task.

Implemented merkle_recursive_call_routes.py. The public root, actual source
context, leaf count, index, and claimed leaf determine the complete verifier
call-routing equations. There is no externally trusted expected call list.
Siblings remain private 16-bit message limbs in the same SHA384 use table.
The compiler binds exact primitive framing, canonical SHA384 padding, standard
IV, all512 chaining bits, digest bytes packed into later message limbs, and
final public root. Source contexts of197bytes give the required even alignment
for digest/sibling byte pairs; the current profile explicitly rejects even
context lengths and odd leaf lengths. Depths1..4 fit the25-block chunk bound.
This is a bounded Merkle-verifier consumer, not a complete PCS/NEAR verifier.

Validation:360 actual paths (all positions, depths1..4, public leaf sizes
0/2/8/64, context lengths1/197/255),555456 routing equations and the same
number of flat-vector comparisons;822 input/mutation rejections. Forty-eight
explicit stale-state counterexamples pass routing alone, demonstrating why
compression AIR acceptance cannot be omitted. All route data is regenerated
from the public statement; a proof-selected equation list is not accepted by
the check_routing entry point.

Generated the10-block, actual-source-context instance with the existing
Lean SHA384NodeChunkImportedFixture exporter. Every use row matches native
SHA384 states exactly and satisfies the routing equations. A changed private
sibling message byte with old states is rejected by Lean's actual compression
check. This is executable Lean witness parity, not a new kernel theorem about
the Python compiler. Canonical source AIR/spec and replay configuration are
retained; large source tables remain regenerable in /tmp with pinned hashes.

Next concrete implementation: same-use-root GKR/PCS proof of the weighted
linear route equations together with the actual compression/use AIR proof,
under a distinct public-statement-bound profile. The verifier must receive
neither original sibling path nor expected hash messages nor full trace.
Measure full proof bytes before attempting larger depths or claiming recursion
break-even. A formal route-compiler theorem and cryptographic composition are
still required. No existing transcript/profile has been relabeled or weakened.

Evidence:results/merkle-recursive-call-routing/. No Lean source changes; prior
full audit4658 remains the last full audit. Full NEAR1Pgas/PQ128/sub300000 B
remain open; latest full fixture1344645 B unchanged; feasibility NOT_PASSED.

## 2026-10-17 — Complete bounded private Merkle diagnostic proof

Added private_merkle_proof.py with distinct bundle/routing profiles. The
public Merkle root/context/count/index/leaf and all four proof-carried source
commitments bind the routing transcript before its random equation weights.
The verifier regenerates all984 equations from public data, compiles their
weighted linear sum into GKR, and authenticates the input obligation through
PCS on the compression proof's exact use-table root. SHA384 compression,
full state, messages, padding and all natural bus/use relations are handled
by the existing four-table compression AIR proof. Neither expected calls,
original path siblings, nor a full use trace is an external verifier input.
The source commitments are witness commitments carried in the proof; the
public Merkle root is a distinct, constrained application input.

Generated fresh Ext8/q8 compression proof for the10-block actual-context
fixture. Local table proofs, zero-claim GKR and weighted opening verify.
Generated a27456-byte routing proof (5.70s prove/encode/check) on the same
use root. Concrete generated13-layer circuit matches independently weighted
equations on honest, zero and arbitrary extension-field vectors, including
negative coefficients represented modulo the base prime. This is finite
compiler parity, not the missing universal compiler theorem.

Combined proof149968 B =122496compression +27456routing +16framing.
Public statement625 B; complete dynamic proof/public total150593 B.
Configured static canonical AIR/spec1143101 B excluded and reported.
Original private path48 B: this instance expands rather than compresses.
It is a complete executable bounded Merkle-verifier diagnostic, not a
complete recursive PCS verifier, zero-knowledge construction, PQ128 result,
or a full NEAR state-transition proof. PCS openings can leak witness data.

Fresh-process verification passes in27.99s. Ten negative cases reject:
changed public root/index/leaf, truncated/trailing/altered routing bytes,
substituted use root/query count, missing routing component, and changed
compression root. An isolated verifier audit admits only proof/spec/public
data-file reads and disables bytecode writes before importing verifier code.
The native/Lean compression witness and routing-boundary tests from the
previous checkpoint remain prerequisites, not replacements for either proof
component. No original inner Merkle verification is called by this API.

Evidence:results/private-merkle-proof-q8/. Existing full fixture remains
1344645 B at diagnosticq309; no secure parameters changed. Full audit4658
is unchanged (no Lean source changes). Feasibility NOT_PASSED.

Next: measure how complete proof size scales with larger paths/batches and
shared hash work, then decide whether this architecture can reach a useful
compression break-even. Full PCS transcript/arithmetic/canonical decoding
constraints, a universal routing-compiler theorem, interactive/QROM security
composition and the full NEAR1Pgas capacity/semantics gates remain open.
Do not interpret150593 B atq8 as progress through the PQ128/300000 B gate.

## 2026-10-17 — Bounded Merkle architecture fails optimistic break-even

Process-reflection follow-up independently checked that the feedback loop now
connects current byte evidence to experiments. Its concrete recommendation:
stop larger-path proof generation in the current bounded profile before
spending more prover time, and replace the dashboard's stale generic next step.

Added screen_bounded_merkle_break_even.py and its deterministic pinned report.
The current separate-root codec needs at least416 B:16outer framing,
8compression magic +8*48source/aux roots, and8routing magic. This excludes
all GKR/PCS messages and public data, so is optimistic. Actual197-byte context
costs4SHA384 compression blocks per internal node. Supported depths1..4 cost
10/14/18/22blocks, hiding48/96/144/192B of siblings. None can break even.

For hypothetical perfectly shared batches under the same25-block budget,
each computed parent on a union of paths has at least one computed child;
therefore at most one external sibling per computed parent. Even omitting
leaf/root work permits at most6parents and288B of deduplicated frontier.
Exhaustively checked all65808nonempty leaf subsets of depth1..4 trees;
61fit the full block budget and the largest frontier is192B. Batching is
not implemented by this experiment. Assumptions: public queried leaves,
connected tree paths, unchanged framing/context/codec and one bounded chunk.
This is an executable finite accounting screen with a stated counting
argument, not a Lean theorem, security proof, or universal recursion bound.

Updated current-feasibility decision to stop this losing sweep. A scalable
replacement must cover more than authentication alone: even free removal
of all574128authentication bytes leaves770517B in the larger fixture.
Replacing its entire opening allows146466B; replacing the entire compression
envelope allows190346B, under the strict300000B total target. These are
accounting budgets, not achievable or secure constructions. Next evaluate
a scalable complete verifier consumer and versioned canonical transcript
with all derivation/binding obligations explicit before more formal expansion.

Validation: deterministic replay matches; current feasibility reconciliation
rejects7inconsistent-evidence cases including tampered byte floor; manifest
pins refreshed and checked. No Lean changes; last full audit4658 unchanged.
Full NEAR1Pgas/PQ128/sub300000B remains NOT_PASSED; larger fixture1344645B
unchanged. This supersedes the preceding proposal to benchmark larger paths
within the existing bounded profile. Goal remains active.

## 2026-10-17 — Lossless response transcript shadow screen

Inspected actual code-switch source response commitments, stage weight seeds,
and GKR layout hashing. Added a shadow-only response encoding candidate with
explicit version, list lengths, field-word tags and canonical48-byte digests.
It preserves all original response values, nested branch ordering, path
ordering and lengths; it does not drop authenticated fields or paths.
No existing verifier/prover transcript is changed. The candidate is a research
codec, not a deployed untrusted-input API or universally verified codec.

Fresh full retained-fixture verification passes, with exactly the prior
104839hash calls /419568blocks /40726unique calls /242409unique blocks.
All7source-response commitments round-trip through binary encoding exactly.
Those commitments cost42840blocks originally versus21157in the candidate.
Frozen-execution unique total becomes220726blocks:21683saved, only8.9448%.
Other transcript calls retain original seeds and data; changing the actual
protocol changes future challenges. These are shadow byte/block counts, not
new proof bytes, prover timing, secure parameters or new-protocol verification.

Decision: defer standalone protocol migration for this modest total gain.
Keep the encoding as an option for a complete scalable verifier architecture.
Next account for provenance of derived weight vectors and GKR layouts;
replacing them by input bindings requires precise deterministic derivation
and transcript-order obligations, plus fresh protocol/QROM analysis. Existing
opening/authentication-only replacement budgets remain insufficient.

Evidence:results/response-transcript-screen.json and its pinned source hash;
current-feasibility report incorporates the screen. Four independent encoding
examples and17malformed/noncanonical cases pass; feasibility reconciliation
now rejects8inconsistent-evidence cases. No Lean changes; last full audit4658.
Full NEAR1Pgas/PQ128/sub300000B remains NOT_PASSED; full fixture1344645B
unchanged. This measurement is not a new quantum-secure construction.

## 2026-10-17 — Derived transcript binding boundary checked

Added check_derived_transcript_bindings.py. Rebuilt baseline and affine-v1
terminal layouts from the retained full-fixture reduction under the same
phase-pooled source commitment profile. They share the exact pre-GKR seed,
but have different layouts. Existing GKR begin correctly distinguishes them
by hashing the layout. A candidate input-only descriptor must bind the
terminal profile and compiler identity; dropping the layout hash with no
replacement loses this distinction. This is not an attack on the current
verifier. Profiles are externally selected, not proof-selected.

A second executable counterexample supplies two distinct weight vectors to
standalone stage.start with identical config/parent/claim. They define
different linear functionals; existing start hashes distinguish them.
Deleting vector binding globally would collapse their descriptors. The
integrated weighted adapter can instead be a consumer of a future closed
interface: derive initial weights from its reduction challenges, authenticate
and commit responses before mixers, derive updated functionals internally,
and pass only verified state into subsequent stages. Standalone GKR/stage
APIs must retain explicit external circuit/weight binding.

The report specifies derivation contracts for terminal layouts, call routing,
initial weighted reduction, and subsequent stages. Formal proof would need
exact descriptor-to-layout/functional determinism, then composed acceptance
and new Fiat-Shamir/QROM analysis; equal descriptors alone prove no soundness.
No protocol was changed and no universal/Lean theorem is claimed.

Optimistic cost screen grants removal of ALL68559unique blocks in layout and
stage tags (even unrelated scalar/init work), plus21683binary-response savings.
Still152167unique SHA384blocks remain, or503.85GiB under current128x6944
u32dense-gadget accounting. This is frozen-execution arithmetic, not measured
RAM, runtime, outer proof size, or a recursion impossibility bound. It does
not establish a viable candidate. Full outer-codec geometry and cheaper
hash constraints still need a feasibility screen before protocol migration.

Validation: both omission counterexamples and current binding distinctions
pass; current evidence reconciliation rejects9inconsistent cases;18manifest
pins checked. No Lean changes; last full audit4658. Larger measured fixture
remains1344645B; full NEAR1Pgas/PQ128/sub300000B NOT_PASSED.

## 2026-10-17 — Complete nibble-lookup SHA384 compression prototype

Revisited pinned Airbender source6ec4ea725d654c5e4fd3a122d571ca37804f9abd,
cs/src/delegation/blake2_round_with_extended_control/mod.rs. It materializes
Xor/Xor3/Xor4/Xor7/Xor9 tables and constrains split/reassembled words through
lookups. This is source evidence for lookup-based implementation, not a claim
that its Blake2 hash parameters or proof security transfer to SHA384/NEAR.
No RISC-V translation or hash substitution is introduced.

Added sha384_nibble_circuit.py: a fixed complete SHA384 compression graph,
including64message-expansion steps,80rounds and all8feed-forward words.
Inputs are all512state bits and1024message bits as384nibbles. Nonaligned
rotations/shifts use two-nibble splice relations; XOR3/choose/majority use
four-bit truth tables. Addition uses exact base16carry equations with bounds
for2/4/5summands. Carry magnitudes are tiny relative to Fp, preventing modular
wrap when composed with enforced range checks. Constants derive from the
pinned NearSpecV3.SHA512 source. Graph is trusted configuration, not supplied
by an untrusted proof; the checker consumes a witness and expected full state.

Witness has31632scalar cells,18688lookup requests,6272addition equations,
13056fixed table rows and31632explicit nibble-range obligations. These are
NOT AIR cells/proof bytes: wiring, static table authentication, multiplicities,
range/lookup arguments, padding, auxiliaries and PCS costs remain excluded.
Current core uses418720unpadded cells per block; no ratio of these unlike
quantities is claimed as a prover or proof-size speedup. In particular Ext8
lookup auxiliaries may consume much of the apparent wire-count saving.

Validation:11messages spanning SHA padding boundaries and multiblock inputs,
28compression blocks, all8output words match independent OpenSSL states;
probe also checks final SHA384 digest against hashlib. All13056lookup table
rows independently checked by bit-level definitions. Every internal wire has
one defining gate;122targeted/scattered/boundary cell mutations reject.
Initially stopped an unnecessarily quadratic all-cell/full-graph mutation
sweep; replaced with coverage of every operation/carry bound and boundaries.
No full-sweep success is claimed. Evidence:results/sha384-nibble-circuit.json.

Next: compile a row layout with actual lookup/range and routing constraints,
accounting for fixed tables and extension-field auxiliaries before selecting
this architecture for formalization. The intended Lean consumer would compose
lookup membership, bounded carries, rotations, schedule and full compression
semantics; current work is executable parity only, not that theorem.
No existing verifier/proof profile changed. Current evidence checks and pin
checks pass; no Lean changes (last audit4658). Full1Pgas/PQ128/sub300000B
NOT_PASSED; larger measured proof remains1344645B.

## 2026-10-17 — Nibble phase rows and existing-bus overhead screen

Annotated the unchanged compression graph with64schedule rows,80round rows,
and one feed-forward row. Materialized independent row copies and checked
all local operations plus full-word routing, expected output and exact fanout.
There are992cross-row word reads,248distinct routed words,maximum fanout5.
Six independently altered row copies reject. Replayed all prior compression
parity/lookup/mutation tests after the graph metadata change; all pass.

Lookup membership constrains22545wire ranges (one overlaps a constant),
6272carry outputs have bounded carry constraints, and constants are fixed.
Only2800additional nibble range obligations remain. Explicitly counted them;
blindly adding a range lookup for every wire would obscure the actual costs.
Projection uses existing pq384_ext8_auxiliary.layout, not an assumed cheap
lookup protocol: one Ext8accumulator for each single-multiplicity interaction;
2*(bits-1)extra extension columns for multiplicity powering. Fixed lookup
and range tables include boolean multiplicity-bit source columns and padded
rows; all logical source/aux tables include power-of-two padding. Cross-row
buses route16nibbles per word. Boundary costs and8endpoint output sends are
charged. Static programs, word-address enforcement and fixed table contents
are trusted in this checker, so their AIR enforcement remains EXCLUDED.

Result: ordinary1/4/16/25-block cases remain more expensive than existing
core+endpoint cell geometry once fixed tables and Ext8auxiliaries are counted.
At64blocks, projected candidate29733680cells versus43181696existing
core+endpoint cells (~0.689ratio). This is not proof-size or runtime saving.
The projected64-block candidate source/aux widths fit the existing64lane /
262144degree caps with appropriate packings; larger256/1024/4096cases fail
those caps. Old64-block core geometry itself exceeds its current packing
capacity: this comparison is cell accounting, not two executable provers.

Decision: structured64-block candidate merits fixed-program/lookup enforcement
work; small bounded chunks do not amortize the lookup table. Do not claim
viability until full AIR, commitment geometry, local/GKR/PCS bytes and security
parameters are included. Endpoint/call provenance and full recursive verifier
semantics are not solved by a cheaper compression gadget.

Evidence:results/sha384-nibble-row-plan.json. Current report consumes it;
10inconsistent-evidence checks and23manifest pins pass. No Lean changes;
last full audit4658. Full1Pgas/PQ128/sub300000B remains NOT_PASSED.

## 2026-10-17 — Fixed nibble lookup tables constrained by canonical AIR

Added sha384_nibble_lookup_air.py. Six fixed relation tables enumerate all
4-bit XOR3/choose/majority and two-input splice tuples. A seventh fixed table
enumerates range0..15. Boolean index columns, first/last index constraints,
and a nonwrapping increment constrain the complete enumeration. Lookup output
values are polynomial expressions of index bits, not witness-selected output
columns. Multiplicity bits are separately constrained Boolean and connect to
the existing natural bus semantics. Canonical np-air-v1 spec retained compressed.

Split tables have4096rows for ternary functions,256for splices,16for range.
This also avoids the existing local-profile8192row cap that a monolithic
16384row lookup table would exceed. At the64-block capacity,21multiplicity bits
cover the conservative total request bound. Source+Ext8 auxiliary widths are
33+328,29+328,25+328respectively. Actual source/aux degree upper bounds are
6(XOR3/majority),5(choose),4(splices/range), below the existing degree16cap.

Canonical interpreter checks928800source constraints and balances18688lookup
plus2800range requests from the complete nibble graph fixture. All13072fixed
rows checked against independent relation definitions. Nine negative cases
reject: index-bit/nonboolean-index changes, nonboolean/extra multiplicity,
wrong request result, hidden request, out-of-range range request, truncated
enumeration and reordered enumeration. This is a full-witness AIR test,
not a succinct proof or a universal Lean/compiler/soundness certificate.
Request tables remain external to the not-yet-implemented phase-row AIR.

Updated cost screen to use actual fixed-table constructors. 64-block projection
is28644752source+aux cells vs43181696old core+endpoint geometry (~0.6634ratio).
16blocks now project a small5%advantage;25blocks still lose due to padding.
Fixed table geometry is included; phase program/address enforcement, proof
transport and recursive semantics remain excluded. Minimum PCS degree128
is now included when choosing packing; row-cap checks are explicit. Larger
256/1024cases fail row/degree limits;4096is rejected even before layout because
its conservative multiplicity bound needs27bits, above the schema's25-bit cap.
No supported profile limit was loosened to make this candidate fit.

Evidence:results/sha384-nibble-lookup-air.json and.spec.json.gz; updated
results/sha384-nibble-row-plan.json. An initial artifact export path bug was
fixed and the full test rerun successfully. Current feasibility reconciliation
rejects11inconsistent cases;27manifest pins and oracle pin checks pass.
Next: connect phase-row lookup sends and word routing to these fixed tables
with actual constrained row programs, then measure the composed proof.
No Lean changes; last full audit4658. Full1Pgas/PQ128/sub300000B NOT_PASSED.

## 2026-10-17 — Composed nibble SHA384 phase/lookup AIR

Added sha384_nibble_phase_air.py. Actual canonical polynomial constraints now
connect schedule64-row, round80-row and endpoint1-row programs to the seven
fixed lookup/range tables. One-hot phase selectors are Boolean, sum to active,
start at phase0 and transition cyclically with a constrained block counter.
Active-prefix/stop constraints enforce the last phase and exact block count;
inactive data cells are zero. Compiler-selected word IDs, constants and fanout
bits are fixed expressions of phase selectors, not prover-chosen metadata.
Word-bus messages include block index,word ID and all16nibbles. Bounded carry
polynomials and nibble lookups constrain the exact local arithmetic.

Diagnostic public segments supply repeated initial state/message words and
consume all8final feed-forward words. They are explicit public compression
boundaries, NOT a compact recursive interface. Two-block129-byte-message
fixture checks all state words against the independent SHA384 probe.
Canonical full-witness interpreter passes933860source constraints and all
natural bus balances. Eight negative cases reject, including an otherwise
valid one-hot selector at the wrong phase, copied word, carry, block ID,
endpoint output, multiplicity, and public final state corruption.

Initial round auxiliary width2072just exceeded the packing threshold for
64blocks. Moved boundary-word range checks to the endpoint table, which already
imports the same words via the exact word bus. All2800range obligations remain;
round width is now498source+1560aux; schedule274+1224; endpoint515+1728.
This avoids redundant per-phase range interaction slots without dropping checks.
Actual compiled64-block source+aux geometry totals27854288cells. Maximum table
degree6, row/degree/lane limits all fit. Old core+endpoint accounting43181696
cells gives~35.5%less in this geometry, NOT a measured proof-size/time saving.
64-block witness has NOT been run; report records that flag as false.

Evidence:results/sha384-nibble-phase-air.json and.spec.json.gz. Current ledger
consumes actual compiled geometry;12inconsistent evidence checks and31manifest
pins pass. No Lean changes; last full audit4658. This compiler and natural-bus
checker do not provide a universal Lean theorem, a cryptographic bus/PCS/QROM
certificate or a recursive verifier. Next check64-block execution and actual
proof transport, then replace verbose public boundaries with private same-root
call binding. Full NEAR1Pgas/PQ128/sub300000B remains NOT_PASSED.

## 2026-10-17 — Full64-block witness and committed private boundary

Generated64actual SHA384compression blocks (8175-byte deterministic message),
checked full512-bit states with the independent probe, and passed8769184
canonical AIR source constraints plus natural bus balance. Generation7.80s,
full canonical check22.80s, source commitments17.48s on reserved benchmark CPUs.
Retained complete compressed source witnesses and statement with raw-file hashes
under results/sha384-nibble64, approximately1.66MB including preparation evidence.

Diagnostic public boundary105992field elements is423968bytes under fixed-u32
encoding, but256707JSON bytes. The former is NOT an encoding-independent lower
bound; an earlier commentary saying public data alone exceeds300KB was corrected.
Neither representation is a claim about an optimized public encoding.

Added sha384_nibble_boundary_air.py, replacing the public word sends/receives
with an additional514-column committed source table. It contains block index,
active flag, full input state/message/output words; prefix/index/stop constraints
enforce the exact block sequence.24input-word sends use compiler-fixed fanouts,
and8output-word receives link the table to the existing phase AIR. All boundary
nibbles are linked to constrained computation words. No application root or
recursive call list is bound yet: the new boundary root must be consumed by
same-root call routing, not treated as a proof of a named hash by itself.

Private64-block version passes8802336canonical constraints and natural balance
in22.53s, with zero public field elements. Total source+aux cells27939408;
boundary table root fc52a781c41cefe14fbd90a313758e8837710fb120e53944da16911a8b491a1268684695a51ab577548a88f6c655c25a.
Two-block boundary regression rejects inactive row, wrong ID, initial-state,
message and result changes. No zero-knowledge claim: source PCS can leak values.

Started existing Ext8 prover at diagnosticq8, affine-v1, separate commitments,
using /tmp/sha384-nibble64-private. Source roots checked; auxiliary generation
was live at this checkpoint. No completed proof or proof-size result is claimed.
Tool session93870 / Python PID2943677 identifies this specific live run; inspect
that process and its prover.log before restarting. Command is retained in
results/sha384-nibble64/manifest.json. Static evidence status explicitly says
FULL_64_BLOCK_WITNESS_CHECKED_PROOF_NOT_YET_CAPTURED.

Current evidence reconciliation rejects13inconsistent cases;37manifest pins
and oracle pins pass. No Lean changes (last audit4658). Full1Pgas/PQ128/sub300000B
remains NOT_PASSED. Next finish the current prover run, encode/freshly verify its
complete result, and measure bytes before adding private recursive-call linkage.

## 2026-10-17 — Base-field auxiliary generation parity; baseline prover continues

Revalidated live prover session93870/PID2943677 rather than restarting it.
Reference auxiliary generation/commitment completed; all11local tables proved.
No completed GKR/PCS result was present at this checkpoint. Original prover,
source commitments and verifier code remain unchanged.

Added pq384_ext8_auxiliary_base.py, a separate prover-side generator. It compiles
source expressions into a shared base-field DAG, caches powers of the Ext8
fingerprint challenge and scales those powers by base values. Extension-valued
accumulator and multiplicity-power operations retain the original arithmetic.
This optimization applies only to generation on canonical base traces, NOT to
verifier evaluation at arbitrary extension points. Nonboolean multiplicity
values are not silently coerced; source constraints still enforce Booleanity.

Exact differential comparison passes16cases /814800base coordinates, including
empty messages/multiplicities, zero factors, next-row/public/selector terms,
nonboolean multiplicities, two rows from every retained source table, and512
round rows. Larger case:13.7439s reference versus2.0161s optimized (~6.82x).
Compilation overhead made the tiny preliminary two-row aggregate slower;
therefore no claim of universal speedup is made. Evidence pins all source
inputs. Full64-block vector/commitment parity has not yet been checked and
this generator is NOT substituted into the running baseline proof.

Existing Lean BusExt8SourceTransport.bus_ext8_coordinate_message and the
underlying air_aux_coordinate_source_eval establish the semantic base-to-Ext8
source-expression transport under column bounds. Reuse those facts; they do
not prove the Python DAG compiler, cached evaluation or complete generator
refinement. No new Lean modules/audit count are claimed.

Added finish_sha384_nibble_proof.py for the pending encode/fresh-verify step.
It requires a completed matching prover report, includes source/aux roots in
the binary envelope, and freshly verifies from proof plus trusted static spec.
The boundary root is returned for a future recursive-call consumer. Only syntax
was checked at this checkpoint; positive codec execution awaits the live prover.
Run after completion: python3 airbender/direct-wasm/finish_sha384_nibble_proof.py
--capture /tmp/sha384-nibble64-private --queries 8.

Current reconciliation and41manifest pins pass. No Lean changes; last full
audit4658. Full1Pgas/PQ128/sub300000B NOT_PASSED. Continue polling the existing
prover and finish its concrete envelope before drawing proof-size conclusions.

## 2026-10-17 — Reference OOM, packed PCS retry, process review

Reference session93870 exited137. The user systemd journal confirms oom-kill
at01:02:02 under its12GiB cap, after all11local tables, GKR and the47.835s
coefficient check; the last stage logged was weighted PCS. Retained the original
log and journal in results/sha384-nibble64/reference-oom*.log. The original
runner only captured reduction data after PCS, so those completed stages were
lost. No complete64-block proof or byte measurement is available yet.

Added opt-in pq384_ext8_packed_prover.py: packed uint32 coordinates retain
32payload bytes per Ext8 scalar through input reduction and native folds.
Protocol, transcript, verifier and reference prover remain unchanged. Three
heterogeneous small complete proofs match reference objects AND encoded bytes
(3120,7560,1880bytes), verify, and reject noncanonical native input. These are
parity fixtures, not secure-size or full-scale memory measurements.

run_ext8_checkpointed_prover.py substitutes the previously tested base-source
auxiliary generator and packed PCS. Before PCS it independently derives the
opening obligation from local/GKR, checks exact parameters, and saves reduction,
opening and status. It does not yet implement PCS-only recovery or persist
source caches. Active retry: session73727, PID2987258, same12GiB cap, capture
/tmp/sha384-nibble64-private. All11local tables finished; GKR running at this
checkpoint. Revalidate this exact process before any restart. Existing finisher
remains the next step after a completed report.

Fresh user-requested process review recommends: (1) finish this measured proof
before expanding architecture; (2) implement independent PCS restart from the
checkpoint with root-checked cache reconstruction and small byte-parity replay;
(3) predict simultaneous buffer memory before scaling; (4) keep the decision
surface current; (5) freeze semantic interfaces before parallel Lean work.
Updated stale top-level next_experiment to the actual64-block retry. Reconciliation
now rejects14inconsistent artifacts; packed evidence and OOM logs are pinned.

New implementation hypothesis: keep base coefficients as uint32 until their
first active PCS fold, with specialized base-by-Ext8 quadratic/first-fold
kernels. Predict peak saving before implementation; require exact full-proof
parity. New compiler specialization candidate: static per-relation multiplicity
bounds may shorten auxiliary power chains; use proved request-count bounds,
never honest observed maxima, and reject if packing erases savings. Re-evaluate
existing auxGroup only by exact nibble degree/layout accounting. LogUp is an
existing idea, not a discovery; defer until a complete replacement ledger wins.

Proposed semantic composition target: canonical constraints plus exact natural
bus balance imply each active boundary output equals full SHA384 compression of
its state and message. Separate fixed lookup/range semantics, bounded word
operations, phase/word routing and boundary extraction, and SHA composition.
Cryptographic extraction of these premises remains separate and unproved.
No new Lean audit claimed; last4658. Full1Pgas/PQ128/sub300000B NOT_PASSED.

## 2026-10-17 — Independently resumable PCS and retained reduction

The same retry session73727/PID2987258 completed GKR and its48.282s coefficient
check, independently rederived opening parameters, and saved its pre-PCS
checkpoint. Packed PCS remains live at this checkpoint; no full proof claimed.
Retained compressed reduction/opening/status under results/sha384-nibble64/checkpoint
with a separate hash manifest. These are intermediate evidence, not a proof.

resume_ext8_checkpoint.py verifies checkpoint hashes and independently derives
local/GKR opening parameters from the external statement. It regenerates one
table's auxiliaries at a time, checks every source/aux root and final, and proves
only PCS. It does not repeat local/GKR proving. A fresh verifier process derives
its own descriptors from the external statement and verifies the resumed output.
The output is a PCS capture/resume report, not a fabricated original prover report.

Tiny four-row, one-table AIR test passes: uninterrupted adapter and separate
recovery from compressed checkpoint give identical1768-byte opening proofs.
Five negatives reject wrong query count, external root, checkpoint opening hash,
source root and auxiliary root. This also exercises the adapter end-to-end.
No full-scale recovery has been launched alongside the still-live full prover.

Recovery command (when needed, after confirming current process terminal):
python3 airbender/direct-wasm/resume_ext8_checkpoint.py
--checkpoint results/sha384-nibble64/checkpoint
--statement results/sha384-nibble64/statement.json.gz
--source-directory results/sha384-nibble64
--native-library /tmp/merkle-route-ext8.so
--output-dir /tmp/sha384-nibble64-resumed --queries 8
Use the same bounded heavy execution wrapper. Native library must include local
and tensor symbols. The retained source JSON files are compressed; recovery
supports those and uncompressed source files.

Exact opening geometry:22branches,834lanes,28178816scalars per vector. Packed
coefficient+weight array payload1803444224bytes; keeping initial coefficients
as base uint32 would hypothetically save789006848bytes before fold temporaries.
This excludes caches/trees/Python/native temporary memory and is not a peak-RAM
prediction. Current live cgroup memory.peak6273830912bytes observed at elapsed
6m56s; this is an interim measurement, not final peak. FullNEAR/PQ128/sub300000B
remain NOT_PASSED. Next finish this PCS and measure its complete envelope.

## 2026-10-17 — Complete64-block envelope265040B, fresh verification passed

Packed retry session73727 exited0 under the same12GiB cap. Journal records
01:07:01–01:15:43 (8m42s); no final peak-RAM measurement retained beyond the
previous interim cgroup observation. Local proving52.017s, GKR60.268s,
coefficient obligation48.282s. The weighted-pcs reported166.697s includes the
adapter's independent checkpoint verification before the actual packed prover.
No full reference-generator equivalence claim: original run OOMed without its
reduction capture. Small differential tests remain the optimization evidence.

Finisher session53270 exited0. Complete affine-v1 envelope265040bytes:
186344opening +78696other proof bytes, zero public field elements. It carries
all source/aux roots, finals, local/GKR messages and PCS. Fresh process verifies
using only wire plus trusted static specification (387100uncompressed bytes,
excluded as fixed verifier data), returning the expected boundary root. Wrong
version, truncation, trailing bytes and altered source root all rejected. Fresh
verification22.786s. SHA25622a622b664d83f83ca63d4cf97afe7c1fdcbfaf1c38dd65255a6c1ffc9a9327b.
Retained binary, compressed JSON capture, reports and logs in
results/sha384-nibble64; manifest pins the exact adapter/verifier implementation.

Interpretation: this is a complete q8 diagnostic compression relation, NOT a
PQ128 proof, recursive-call binding, compiler theorem, or fullNEAR proof. Its
265040bytes already exceeds both existing whole-opening replacement allowance
146466bytes and whole-compression allowance190346bytes. It is below the299999
whole-bundle allowance by34959bytes, but does not verify the bundle's full
computation. Therefore do not claim usable recursive compression or multiply
this chunk result into an unmeasured full-verifier proof. Next screen exact
full-verifier coverage and private same-root call routing with the actual byte
budget before launching a larger proof. Full1Pgas/PQ128/sub300000B NOT_PASSED.

Static multiplicity specialization screen now retained. Compiler graph counts
per block: xor3=4608, choose=1280, majority=1280, splice1=3328, splice2=4864,
splice3=3328, range=2800. At64blocks, fixed receive multiplicity widths can be
bounded by19/17/17/18/19/18/18bits respectively instead of common21bits, conditional
on exact graph routing/natural balance. This is a static request upper bound,
not an honest-witness maximum. Exact geometry preserves731952source+aux cells
and61lanes of potential savings (732032padded base coefficients). No revised
AIR/proof or universal Lean theorem produced. Keep this bounded optimization
behind the full-verifier coverage decision rather than launching another proof
without a candidate byte/security ledger.

## 2026-10-17 — Full-verifier coverage rejects independent chunk transport

screen_nibble_full_verifier.py derives a query-independent framing lower bound
for THIS fixed64-slot codec:1064header/root bytes +18912finals +21728local
rounds =41704bytes, excluding all GKR/PCS and routing. The recorded unchanged
whole-input-deduplicated verifier workload242409SHAcompression blocks would
need3788independent envelopes, hence157974752mandatory bytes. Even the prior
optimistic152167-block transcript scenario needs2378envelopes and99172112bytes.
This rejects concatenating this format, not joint proofs or recursive aggregation,
new block/state sharing, transcript designs or other AIR/codec architectures.
No measured265040-byte proof-size extrapolation is used as a universal bound.

Coverage ledger explicitly separates the implemented compression relation from
missing hash framing/IV/chaining/digest handling, same-root verifier call routing,
Fiat-Shamir chronology, Merkle and PCS equations, local/GKR algebra, protocol
soundness/PQ128, and fullNEAR semantics/capacity. One measured q8 hash-only proof
already exceeds whole-opening replacement allowance by118574bytes and whole-
compression allowance by74694bytes. Whole-bundle headroom34959bytes does not
establish feasibility because the proof does not cover that verifier.

Decision: no further independent hash-batch transport or larger SHA-only proof
as a substitute for closed-verifier recursion. Next candidate needs global
amortization plus explicit hash-call binding AND arithmetic, with a complete
byte/security ledger before full-scale proving. Added an executed-operation
profiler for the same complete retained verifier to measure the missing arithmetic
side; it distinguishes Python Ext8 function calls from native vector calls and
lengths. Its full run is pending at this checkpoint (session69594/PID3024571).
Do not treat nested composite-call counts as disjoint gates or claim native
scalar operations were counted. Full1Pgas/PQ128/sub300000B remains NOT_PASSED.

## 2026-10-17 — Arithmetic workload and structured functional candidate

Profiler session69594 exited0 in69.998s. Contract, call-link and full compression
verifier all passed. Counted3685574Python Ext8 multiplications:306360call-link
and3379214compression. Native work is separate:17affine folds across524284input
values;7injections across149798weight elements and2170evaluation points. Counts
exclude native scalar operations and built-in base arithmetic; composite calls
include nested operations and must not be summed as disjoint circuit gates.
Hash calls104839exactly match the earlier full verifier census. Retained input
and source pins in results/closed-verifier-arithmetic.json.

Named candidate for closed-verifier arithmetic: represent a functional as one
scaled tensor-equality term plus a list of geometric terms m*z^i. Injection
appends terms. Folding removes the low tensor coordinate and updates each
geometric term to m*(1-r+r*z)*(z^2)^i. This avoids constructing every coefficient
merely to carry a functional forward. Existing stages hash the entire expanded
vector, so the current protocol still requires expansion; no transcript/profile
change or speedup claim is made. Any descriptor-only transcript must bind the
closed derivation history, not caller-selected replacement weights (see prior
derived-transcript counterexamples).

ext8_structured_functional.py and its test pass18alternating injection/fold
sequences (1098Ext8value comparisons), zero/one/random fold challenges,
zero/duplicate evaluation points, and zero mixers. This is small executable
parity, not full-stage shadow validation. Next shadow the retained full verifier
state transitions and count structured work before proposing a protocol change.

NearCompression/StructuredFunctional.lean proves four universal POINTWISE field
identities: geometric fold, tensor low-bit fold, fold linearity, and agreement
with the existing oneFoldScale convention. These support this specific measured
arithmetic candidate; they do not prove Python/list refinement or transcript
soundness. Reuses CodeSwitchFunctional and OneFoldScalarComposition. Root module
build passes and full Audit.lean now4662theorems; no sorryAx. Exact audit and
build logs retained under results/structured-functional. Original goal still
NOT_PASSED: no full closed-verifier proof, PQ128 certificate, or fullNEAR1Pgas.

## 2026-10-17 — Full verifier structured-state equivalence

check_structured_verifier_states.py completed session83039/PID3039481 with
exit0 in57.324s. Replayed original retained contract, call-link and compression
verifier; all accepted. Every coefficient of initial262144-entry functional,
all17fold outputs and all7injection outputs matches the structured shadow:
674084Ext8coefficient comparisons. Each injected claim independently matches
claim+sum(mixer*answer). Full expansion reuses the tested native injection kernel
with transformed geometric points/mixers; three positions per state also use
independent Python at(), and earlier small tests compare full Python expansion.
This is executable full-state parity, not universal implementation refinement.

Actual dense injections process46437380coefficient/point terms. Structured
folds update15810geometric terms. These are different work units, not a measured
speedup ratio: native injection specializes base-field points, and the shadow
materializes all states for checking. Initial structured scalar payload608bytes
versus8388608dense payload; after first injection20416versus4194304. Dense wins
by degree1024 (32768versus59872); final state64versus138944. Thus a future closed
verifier should use a hybrid, not retain geometric terms to the terminal blindly.
Neither payload count is proof size or total Python/Rust memory.

Next binding contract to design BEFORE a transcript migration:
- Closed entry binds external statement/spec/source roots, commitment/terminal
  profiles, code-switch schedule and the exact functional-derivation version.
- Initial equality point is derived only from checked input-reduction challenges.
- Each fold consumes the previously checked state and transcript challenge.
- Each injection derives points/answers from authenticated openings and child
  commitment, then draws mixers only after binding those responses.
- A continuation may omit expanded weights only when it derives the identical
  functional from this bound history. Caller-supplied structured terms are not
  an authorized replacement for that derivation. Standalone stage.start keeps
  its explicit vector binding.
- Hybrid materialization must preserve pointwise weights and terminal dot claim.
This is an interface plan, not a proved hash-chain/QROM reduction or changed
protocol. Current ext8_code_switch_stage.start still hashes expanded weights;
no hash omission or verifier-speed claim follows from this parity result.

Dashboard now records full state parity,18inconsistent-evidence negatives.
No Lean changes this turn; last full audit4662. Full1Pgas/PQ128/sub300000B
NOT_PASSED. Next quantify a closed derived-state transcript and remaining full
verifier costs before producing a new larger proof.

## 2026-10-17 — Separate closed derived-functional transcript experiment

Added ext8_closed_derived_switch.py with explicit experimental adapter/stage
profiles. It clones helper function namespaces without global monkeypatching;
original standalone stage.start still binds its full external weight vector.
The only public proving/verifying entry points run the complete packed-root
adapter, deriving initial weights from input-reduction challenges and every
continuation from checked previous stages. New stage seeds bind versioned
profile, fixed derivation identifier, complete config/history parent and claim,
omitting the derived expanded vector. Root/schedule/namespace and initial
statement/branches remain bound. This is a changed experimental Fiat-Shamir
protocol, NOT a backwards-compatible transport or a security-certified omission.

One heterogeneous small q8 proof completes and verifies in a fresh process.
17negative cases pass, including old/new profile rejection after relabeling,
external statement/parent/source-weight/root/claim changes, schedule/query changes,
mutated reduction/root/OOD/tail/terminal, and an injected caller-selected weights
field. Original baseline proof still verifies and its stage.start function is
unchanged. New proof is27432JSON bytes; no compact/full-execution size claim.

Measured this small fixture's stage-start hashing:20SHAblocks baseline versus12
closed. Overall blocks1635versus1628, but exact-input-deduplicated blocks1268
versus1296. Changed challenges change query/path overlap; report that increase,
not a misleading total savings claim. This is an interface/algebra experiment,
not a full-scale benefit, whole acceptance theorem, adaptive-QROM analysis or
PQ128 claim. Dense arithmetic is still used in both prover and verifier.

Next implement the already-tested structured/hybrid functional inside this
closed verifier, with terminal-dot and every injection/fold checked. The full
hash/arithmetic/security ledger must have headroom before another large proving
run. No Lean changes this turn; last audit4662. Dashboard rejects19inconsistent
evidence cases; full1Pgas/PQ128/sub300000B remains NOT_PASSED.

## 2026-10-17 — Hybrid verifier integrated without transcript changes

Added ext8_closed_hybrid_verify.py, a representation-only verifier fork of the
separate closed-derived experiment. Initial equality weights and large
continuations stay structured; when structured scalar payload reaches dense
payload, the implementation materializes once and continues dense. Injection
updates claims exactly; terminal verification still checks the disclosed
polynomial's committed root and coefficient/weight dot product. Public entry
accepts proof/statement/branches/claim/config, never a caller-selected weight state.
Original standalone stage and dense closed verifier remain unchanged.

A newly generated degree1024/q31 closed-profile proof passes dense, native hybrid
and fresh pure-Python hybrid verification. Ordered framed hash PREIMAGES match
exactly across dense/hybrid executions, in addition to equal3029hash calls,
7752blocks and6308unique blocks. This is stronger than merely comparing totals;
no new transcript or proof bytes are needed for this arithmetic change. This
fixture materializes atdegree128with64geometric terms, then exercises dense
folding and injection. It does not imply the same crossover for other profiles.

Six negative mutations rejected by both verifiers:terminal,OOD,tail,source leaf,
external claim and injected weight field. Separate256-entry transition sequence
checks765Ext8coefficients and all injected claims across zero/one/random folds
and zero/base/extension evaluation points. A structural regression confirms the
authenticated initial/tail obligation functions differ from their originals only
in preserving the internal weight object instead of converting it to JSON lists.

This is executable bounded equivalence, not universal Python refinement, whole
protocol soundness, fullNEAR or PQ128. Existing four Lean pointwise identities
support the structured updates; no additional Lean theorem count claimed (4662).
Next validate the full retained shape and account for remaining hash/arithmetic
cost before a large new-profile proof. Dashboard20negative evidence checks pass.
Original1Pgas/PQ128/sub300000B goal remains NOT_PASSED.

## 2026-10-17 — Full hybrid decoder replay and remaining-work decision

check_full_hybrid_verifier.py now replays the complete retained q309contract,
call-link and binary compression decoder with baseline vector-hash binding
preserved. Every104839ordered framed hash preimage matches literally between
dense and hybrid runs; all17folds and7injections execute on hybrid state, with
materialization atdegree1024/930terms. Full run session86889 exited0. Timings
50.257s dense/48.306s hybrid include asymmetric instrumentation and mandatory
vector expansions; they are NOT a production speedup result.

Harness development caught two isolation/coverage errors before any success
claim: cloning after a temporary verifier substitution could recursively call
the wrapper (that run was terminated); replacing top-level verify did not affect
binary decode's inline verification (event-count assertion failed). Corrected
by cloning the decoder's adapter namespace and supplying the hybrid backend at
the actual inline fold/injection calls. A retained small binary proof exercised
this exact path before the final full replay. No baseline verifier code changed.

account_closed_hybrid_work.py derives the closed-profile shape costs from that
replay. Original dense injections46437380coefficient/point terms; hybrid planned
materialization952320terms plus91140dense tail injection terms and3720geometric
fold-term updates. These are loop units, not comparable timing/field-operation
ratios: native injection specializes base points. Counts exclude the temporary
expansions required to preserve baseline hashes in the compatibility replay.

Six old stage-start bindings take37479SHA384blocks; versioned derived bindings
would take36on the same geometry/configuration lengths. Holding all OTHER
recorded hash work fixed gives204966blocks, NOT a measured new-transcript total
or a global lower bound. New challenges and sharing change (as the tiny-profile
experiment already demonstrated). This optimization is useful but still leaves
large hash work: do not launch a large new proof solely on this improvement.
Next assess the remaining hash architecture and joint-verifier geometry/security
ledger. FullNEAR1Pgas, PQ128, and sub300000B secure proof remain NOT_PASSED.

Dashboard reconciliation rejects21inconsistent-evidence cases. No Lean changes;
last full audit4662. Full replay and cost screen source/input pins retained.

### 2026-10-17: algebraic hash range and geometry screen

Primary-source review retained exact Plonky3 commit
f98331687e47106a64ab82a77e2e1d0d66c9161b and Airbender commit
6ec4ea725d654c5e4fd3a122d571ca37804f9abd source snapshots with raw/compressed
SHA256 pins in results/hash-architecture-review/sources.json. Plonky3's
[round selector](https://github.com/Plonky3/Plonky3/blob/f98331687e47106a64ab82a77e2e1d0d66c9161b/poseidon2/src/round_numbers.rs)
targets M=128; this is not evidence of PQ128 collision resistance.
[BHT](https://arxiv.org/abs/quant-ph/9705002) motivates the unrestricted
quantum-query output-range screen: an ideal n-bit digest has generic collision
query scale 2^(n/3). This is a necessary screen under that model, not a lower
bound for concrete Poseidon2 or this proof protocol.

For BabyBear p=2013265921, exact integer arithmetic gives p^12 < 2^384 <= p^13.
Twelve field elements serialize to 48 bytes but have only 370.88 bits of range;
13 elements serialize canonically to 52 bytes and have 401.79 bits of range.
Eight elements give only about 82.42 bits of generic quantum collision query
scale. All candidates remain explicitly uncertified.

Hypothetical capacity13/output13 sponge wrappers around pinned upstream widths
16/24/32 require respectively 14/4/2 permutations for a pair of digests with
two framing words and one delimiter. Upstream rounds give 7896/3408/2288 x^7
multiplications respectively, excluding linear layers, routing, encoding and
proof costs. Width32 is only a cost-screen candidate. Capacity13 is a shape
hypothesis, not a security theorem; upstream round margins are not a quantum
algebraic cryptanalysis result. Retain the SHA384 baseline.

[Quantum sponge indifferentiability](https://arxiv.org/html/2504.16887v1)
concerns an ideal binary public permutation; it does not automatically certify
a concrete prime-field sponge/duplex, PCS binding/collapsing or adaptive
Fiat-Shamir. [Poseidon2 abstract](https://eprint.iacr.org/2023/323) reviewed;
PDF retrieval returned403, so no claim of full-paper review. The
[Plonky3 recursion hashing documentation](https://plonky3.github.io/Plonky3-recursion/architecture_and_internals/hashing.html)
separates Merkle compression and transcript roles; both require exact native/
circuit compatibility. Application-mandated NEAR hashes remain a separate cost.

Screen replay passes and current-feasibility reconciliation rejects23
inconsistent-evidence cases, including false PQ128 certification and accepting
12 elements as meeting the 384-bit range criterion. No Lean changes, and no
new cryptographic theorem. Next gate: a named end-to-end candidate linking
hash geometry, full recursive-verifier coverage, outer bytes and explicit
security assumptions before a larger proving experiment. Full NEAR1Pgas,
PQ128 and secure sub300000B proof remain NOT_PASSED.

### 2026-10-17: witness-free joint SHA geometry gate

Implemented model_joint_nibble_geometry.py, following the independent process
review. It first reconciles the retained 64-block envelope from its actual
transcript-derived query indices and trusted table geometry: header/roots1064,
finals18912, local21728, GKR36992, opening header4360, leaves61696 and sibling
hashes120288 =265040B. Every nonopening byte equals the independently retained
reduction messages; the wire SHA256 also matches the verified capture. This is
accounting replay, not a fresh cryptographic verification or a new proof.

The named projection is ONE joint envelope with22separate source/auxiliary trees
and the current rate4 weighted codec. Power-of-two packings are optimized over
this finite shape using exact uniform-query expected leaf/frontier counts.
Conditional on a maximum degree, branch choices separate; the model enumerates
all maximum degrees. Small exhaustive checks independently enumerate9packing
cases and4368joint query sequences;3invalid geometries are rejected.

The actual implementation caps branch degree at2^18 and lanes at64. The
counterfactual explicitly lifts those caps while retaining BabyBear's rate4
subgroup degree limit2^25. In the full workload the round table alone needs
2^25rows, forcing packing1 in that table. No enlarged prover profile or witness
is implemented. Baseline widths/finals are frozen optimistically: increased
multiplicity bounds, GKR, hash-call routing/framing/chaining, verifier arithmetic
and public binding are all priced at zero. Thus these are intentionally
incomplete architecture estimates, not secure proof-size measurements.

At q8 the measured full-verifier workload242409SHAblocks gives expected471152B
and16simulated totals464744–474864B. The closed-binding counterfactual204966blocks
and prior optimistic-erasure152167blocks both give expected405072B and simulated
398664–408784B, because both map to the same padded table geometry. The current
full fixture allows190346B for its compression replacement or299999B for the
whole bundle. Even these incomplete q8 projections miss both allowances.
At q309 the same shapes project roughly10.17–12.71MB. Neither query count is a
PQ128 certificate; simulations are not worst-case bounds or an impossibility
result for other joint layouts, pooling, code switching, or algebraic hashes.

Decision: do not scale this separate-tree SHA profile. A changed joint layout
must supply its own costs and assumptions; algebraic S-box counts alone do not
provide outer proof bytes. No new Lean lemmas were needed for this cost decision.
Full NEAR1Pgas, PQ128, recursive acceptance soundness and secure sub300000B proof
remain NOT_PASSED. Current dashboard now points to the changed-layout gate.

### 2026-10-17: phase-pooled joint SHA screen

Extended the witness-free joint model with model_pooled_nibble_geometry.py.
For each allowed maximum degree, subset dynamic programming enumerates all
partitions of the11logical source tables and separately all partitions of the11
auxiliary tables. Each bank concatenates columns, pads to its tallest member,
and searches power-of-two packings. No source/auxiliary merge is permitted:
the commitments occur on different sides of bus challenges. Existing
ext8_pooled_weights supplies the logical masking/rotation design precedent;
the existing executable phase-pooled-v1 only supports its four-table profile,
so this11-table search is explicitly counterfactual, not a new working profile.
Logical root slots remain in the existing envelope accounting.

Independent small enumeration checks12cases and1074partition/packing choices
against the optimizer, verifies exact logical-slot coverage and column offsets,
and rejects a cross-phase merge. No witness or larger prover job was launched.
All zero-cost omissions and uncertified q8/q309 sensitivity assumptions from
the previous joint screen remain in force.

For242409blocks, six selected banks reduce expected q8 bytes471152->393856;
16simulated totals are389152–396448B. For the204966/152167block counterfactuals,
four banks reduce405072->310725B, with simulated306656–312992B. Even these
incomplete projections exceed the299999B whole-bundle allowance and190346B
compression replacement allowance. At q309 the projected totals remain about
7.93–10.97MB. This finite-family expected/sampled result is not a universal
lower bound for pooling, alternative commitments or recursive protocols.

Selected packed base coefficient buffers contain95,797,903,360 or61,270,392,832
field coordinates: respectively383,191,613,440B or245,081,571,328B at4B each.
These are shape accounting, not measured memory and not total peak RAM; they
exclude extension expansion, evaluation vectors, witnesses, trees and scratch.
Streaming/recomputation could change residency. The cost is another reason not
to launch this unimplemented enlarged SHA profile.

Decision: pooling changes costs materially but does not rescue this candidate.
Next obtain a concrete algebraic-hash AIR layout and connect it to a full
verifier cost model, keeping quantum permutation/sponge/FS assumptions explicit.
Do not infer outer bytes from S-box count or switch protocol hashes based on
this geometry. Current-feasibility reconciliation rejects27inconsistent cases.
No Lean or security theorem changed; full goal remains NOT_PASSED.

### 2026-10-17: concrete algebraic permutation AIR and verifier-length replay

Implemented poseidon2_permutation_air.py for the pinned Plonky3 width32
BabyBear permutation: initial external linear layer,4initial full rounds,
30internal rounds,4final full rounds, and all round constants. The
[external layer source](https://github.com/Plonky3/Plonky3/blob/f98331687e47106a64ab82a77e2e1d0d66c9161b/poseidon2/src/external.rs)
and [Monty31 layer source](https://github.com/Plonky3/Plonky3/blob/f98331687e47106a64ab82a77e2e1d0d66c9161b/monty-31/src/poseidon2.rs)
are retained as pinned unmodified compressed snapshots. Constants come from
the already pinned BabyBear source. These upstream M128 rounds are NOT a
PQ128 security certificate; no hash in the proof protocol has been replaced.

The concrete canonical np-air-v2 relation has2106columns and2074degree2
constraints in ONE row per permutation. Inputs occupy32columns; each round
allocates its32output coordinates. Each x^7 uses three intermediate columns
x^2,x^3,x^6; its final multiplication appears inside linear-output equations.
Every noninput column has one acyclic defining equation. Inputs and outputs
share the same row, avoiding a new internal routing bus. This does not supply
external call binding, sponge constraints or a universal Lean compiler theorem.

Built a separate Rust oracle calling default_babybear_poseidon2_32 directly
at commit f98331687e47106a64ab82a77e2e1d0d66c9161b, with Cargo.lock retained.
All44inputs match: zero, one, p-1,32basis states,8seeded random states and the
upstream known-answer vector. Canonical AIR evaluation checks64padded rows,
132736constraints. All2074intermediate/output coordinates are individually
corrupted and rejected by their defining canonical equation;32input mutations
are also rejected. These2106negative controls and causal-column checks are
finite implementation evidence, not a formal correctness or soundness proof.

measure_algebraic_hash_workload.py replays the complete original retained
contract/call-link/compression verifier unchanged and records exact framed
input lengths. The four old census counts match:104839calls,419568SHAblocks,
40726unique inputs,242409unique SHAblocks. For a hypothetical width32/rate19/
capacity13 wrapper,3bytes per field element plus byte01 delimiter and zero
padding gives57bytes per rate block. The old unique inputs would require
503684permutations, padded to524288rows, or1060758504logical source cells.
This is a specified byte-wrapper shape, not one permutation per SHA block.
The wrapper is unimplemented;52byte digests, new domains/challenges and sharing
would alter the actual new protocol workload. NEAR application hashes are
not substituted. Exact-input sharing still requires a proved routing relation.

A permutation-only weighted-codec projection gives109907.61B at q8 and
2417356.08B at q309, including source root and local degree2 sumcheck but
excluding GKR, sponge chaining/encoding, call binding, verifier arithmetic and
auxiliary integration. Existing degree/lane caps are lifted in this model;
selected lanes264/132 and degrees2^22/2^23 exceed current implementation limits.
The current adapter also requires positive auxiliary width, so this zero-bus
layout is not an executable whole-proof profile. Packed base coefficient
payload4429185024B is arithmetic accounting, not observed peak RAM.

Decision: the concrete hash relation substantially changes cost, but the q309
outer schedule still misses size even with major components omitted. Next
screen a changed outer PCS schedule plus complete conditional security/byte
ledger before full sponge-verifier implementation or a large proof run.
Current dashboard rejects29inconsistent-evidence cases. No Lean changes;
full NEAR1Pgas, secure sub300000B, PQ128 and recursive acceptance remain open.


## 2026-10-17 — Outer PCS screen and published-design cross-check

The permutation-only layout now has a conditional outer PCS screen in
`research/near-compression/airbender/direct-wasm/screen_algebraic_outer_pcs.py`.
Results are in `results/poseidon2-permutation-layout/outer-pcs-screen.json`.
This is a model, not a generated recursive proof or a security certificate.
It enforces BabyBear source/destination domains at most 2^27, screens rates
4/16/64 and folds 1..8, extensions 8/10/12, and nominal QROM constants 1/256.
64-byte digests and conditional minimum hash-term-budget digests (49/50 bytes)
are compared. Complete expected modeled sizes are 1,181,595–1,491,861 bytes;
there are zero joint size/partial-ledger survivors. Even relaxed schedules
which independently grant each query term the entire error budget exceed
1.15 MB. GKR, sponge binding, routing, auxiliary integration and full NEAR
remain excluded, so these are optimistic costs.

Important scope correction: only the 64-byte digest cases have relaxed
source-plus-fixed prefixes over 300,000 bytes (301,198–312,051). Shorter digests
bring those prefixes below target (264,889–277,234); their complete schedules
still fail. This is not a universal no-go theorem. Passing a partial ledger
with Ext12 is not PQ128. Upstream Poseidon2 M128 parameters are not a PQ128
certificate. The independent test passed six exhaustive schedule cases,
34,942 costs, invalid-domain checks and exact rational budget decisions.
The relaxed-query test caught and corrected an off-by-one security-bit bound.
The existing current-feasibility dashboard does not yet consume this screen.

Published-design cross-check (primary sources consulted 2026-10-17):

- Airbender Prime announcement: https://www.zksync.io/blog/introducing-airbender-prime
  describes GKR, WHIR, BLAKE2s and planned Keccak-256 L1 commitments. Its
  single-GPU speed results do not establish our PQ128 plus <300,000-byte target.
  GitHub API HEAD resolved to 6ec4ea725d654c5e4fd3a122d571ca37804f9abd;
  docs/philosophy_and_logic.md at that revision still describes DEEP STARK/FRI.
  Consequently we must distinguish Prime's announcement from the older source
  we have inspected. A reproducible Prime release/parameter mapping remains open.
- SP1 Hypercube: https://docs.succinct.xyz/docs/sp1/security/security-model
  explicitly retains elliptic-curve discrete-log assumptions for global memory,
  before optional BN254 Groth16/PLONK wrapping. Thus compressed STARK does not
  imply an entirely hash-based system. Its Jagged PCS is relevant for us:
  https://docs.succinct.xyz/docs/sp1/hypercube/jagged
  At source 02fa30185ecd658174b211d56128b14867ab8e81, inspected
  slop/crates/jagged/src/verifier.rs: shape and prefix-sum checks, binding table
  dimensions to original commitments, and reduction toward a dense PCS.
- OpenVM 2.0 Beta reports <300 kB and 100-bit provable post-quantum security:
  https://blog.openvm.dev/2.0-beta . This is a published claim, not locally
  reproduced and not PQ128. SWIRL stacks heterogeneous tables before WHIR and
  uses LogUp-GKR: https://openvm.dev/swirl.pdf . At source
  e74f9b1ee868c42776faf821b8b9f2e8829a7f68 inspected security-model.mdx and
  docs/crates/recursion/modules/whir/README.md. Dedicated AIRs cover folding,
  query openings, sumcheck and final evaluations; buses bind Merkle roots and
  challenges. Security docs disclose Poseidon2 ideal-permutation assumptions,
  per-round grinding and distinct app/recursive/root schedules. PQ128 requires
  redoing the quantum loss accounting, not merely setting security_bits=128.
  Its Halo2/KZG EVM wrapper is excluded from our hash-only comparison.
- RISC Zero distinguishes recursive STARK succinct receipts from Groth16:
  https://dev.risczero.com/proof-system/ . Retain as a recursion baseline;
  do not compare a tiny Groth16 receipt with our hash-only requirement.
- S-two's dedicated circuit recursion replaces general Cairo verifier execution:
  https://starkware.co/blog/minutes-to-seconds-efficiency-gains-with-recursive-circuit-proving/
  Supports the direction of a specialized verifier circuit; this page does not
  establish our exact size/security target.
- Binius64 is a distinct, untested candidate for bitwise/hash-heavy computation:
  https://github.com/binius-zk/binius64 . Its word-oriented binary-field design
  merits a bounded comparison before concluding SHA recursion itself is
  unworkable. Our negative SHA results concern our prime-field layouts.
- Jolt now documents Dory (elliptic curve) and Akita (lattice) backends:
  https://jolt.a16zcrypto.com/usage/quickstart.html . Dory is excluded by our
  requirement; Akita is not hash-only and is an alternative research track,
  not a locally tested or dismissed hash-based candidate.

Priority update: benchmark SWIRL-style stacking and a dedicated native-field
recursive verifier against our current outer PCS geometry; study SP1 Jagged
PCS without importing its curve-based memory assumption. Keep algebraic hash
co-design as a candidate, with explicit PQ assumptions. Keep Binius64 as the
alternative for preserving bitwise hashes. Do not spend another large Lean
campaign on a rejected layout. First establish a complete byte/security budget,
then prove the interfaces connecting semantics, AIR, transcript, PCS and recursion.
No full NEAR proof, PQ128 certificate or secure sub-300,000-byte proof is claimed.


## 2026-10-17 — Pin SWIRL calculator and distinguish RBR from PQ security

Previous goal turn classified progress: committed geometry screen and published
comparison changed candidate priority. Current worktree was clean at e80af3461.
Pinned openvm-org/stark-backend v2.0.0 to
16d60de724c21dcadfde7d8315a1db507e5832d7. Four compressed source snapshots and
raw SHA-256 pins live in research/near-compression/results/swirl-security-review.
Inspected calculator.rs, soundness/mod.rs, SDK config and production soundness tests.

SDK explicitly targets 100 bits of round-by-round (RBR) security using BabyBear^4.
Calculator takes the minimum over component bounds and adds biased grinding
costs at selected stages. It is not itself a complete end-to-end quantum-security
calculator. This qualifies the prior comparison: the release's claimed 100-bit
post-quantum security is a published claim; the inspected calculator alone does
not establish that claim under our concrete adversary-budget convention.
No attack or defect in SWIRL is inferred from this distinction.

Version mismatch matters: the previously inspected OpenVM docs table lists
k_whir=3, while this pinned backend defaults DEFAULT_K_WHIR=4. Do not combine
those schedules and reported proof sizes into a synthetic benchmark.

The new screen_swirl_field_budget.py verifies all four source pins and replays
only two ungrounded error terms: degree-three GKR and stacking 2*columns/|E|,
with optimistic PCS list size one. At the published test column bounds (2,000
recursion; 30,000 app), degree-four extension cannot make these terms <=2^-128.
Degree five clears these individual RBR128 budgets. Under our hypothetical
C Q^2 epsilon budget with C=1, Q=2^128 and allowance 1/4 per term, minimum tested
extension degree is nine for all three cases. This is necessary term-budget
arithmetic, NOT a sufficient security parameter set, field implementation,
attack, proof-size result or theorem that this QROM transform applies to SWIRL.
Exact Fraction comparisons are checked independently against integer inequalities.

Next action: obtain a matching complete backend/configuration release, reproduce
its production calculator and serialized STARK baseline, then include all
algebraic, hash, grinding and recursive-composition terms under one security
convention. Before proposing implementation, assess larger challenge-field and
hash costs against the narrow root stacking geometry. Keep the full 1 Petagas
NEAR goal active; no completion or PQ128 claim.


## 2026-10-17 — Executable pinned SWIRL baseline

Previous goal turn was progress (pinned calculator and exact field screen).
Revalidated clean worktree at c06c06f63. Cloned stark-backend v2.0.0 into
/tmp/nearproof-swirl-backend, verified revision
16d60de724c21dcadfde7d8315a1db507e5832d7, read its AGENTS.md, and ran only
individual-crate commands. Rust toolchain 1.90.0. All six production soundness
integration tests pass. Re-ran the all-configs test alone to obtain uninterleaved
output. This is reproduction of upstream RBR accounting, not a PQ128 theorem.

Actual pinned query schedules: app [193,88,81,81], leaf [118,84,81], internal
[68,30,20], root [61,30,20], hook [193,42,24]. k_whir=4 throughout. Root has
l_skip=2, n_stack=18, w_stack=18, blowup16, list-decoding m=1 and 15-bit
fold/mu/query grinding. This differs from the previously reviewed documentation
configuration; do not transfer size measurements or security claims between them.

Ran the upstream CPU Keccak example with unchanged workload and protocol
parameters: 1,024 seeded Keccak-f1600 permutations, 2,633 columns, 3,182
constraints, no interactions, app_params_with_100_bits_security(21), four Rayon
threads. Instrumentation only encodes the proof, reports bytes, decodes, checks
round-trip equality and verifies the decoded proof. Actual proof: 859,137 bytes.
A second run added component accounting and produced the same total:

- GKR: 24 bytes (this workload has no lookup interactions).
- Batch constraints: 85,992 bytes.
- Stacking: 1,728 bytes.
- WHIR: 771,336 bytes (89.78%).
- Remaining framing/metadata: 57 bytes.

Both processes exited zero. The second timed cargo invocation took 15.48s and
maximum RSS 2,398,432 KiB; elapsed time includes compilation and must not be
reported as prover-only latency. Instrumented example passed crate/example
Clippy with -D warnings and was formatted with rustfmt.

Results, exact generated Cargo.lock, instrumented example source, compressed
proof and raw-hash-pinned logs are in
research/near-compression/results/swirl-security-review/baseline/report.json.
The proof is an application-level Keccak permutation proof, not OpenVM's final
recursive root, an Ethereum block, or NEAR. Therefore its size does not refute
OpenVM's published sub-300kB root claim. The reference now has executable
provenance; reproducing the dedicated recursive verifier/root remains next.

Strategic implication: stacking protocol messages themselves are small, while
PCS openings dominate this wide application relation. Move to the actual
recursive-verifier layout before adjusting the hash or quoting a final size.
Full NEAR1Pgas, end-to-end PQ128, recursive acceptance and <300000B remain open.


## 2026-10-17 — Execute dedicated SWIRL recursive-verifier proof

Previous turn classified progress: actual serialized application proof reproduced.
Revalidated clean worktree at71c4f2941. Cloned OpenVM at
 e74f9b1ee868c42776faf821b8b9f2e8829a7f68 and read AGENTS.md. Its Cargo.lock
pins stark-backend d667af5929d0ea9e5194adf639d6bddeb8c10f9a (v2.0.1), which is
DIFFERENT from the preceding standalone v2.0.0 baseline. Used --locked and
Rust1.91.1 throughout; did not silently override its backend dependency.

Found recursion/src/tests.rs::run_test only generates child proofs and debug
checks parent AIR constraints. Extended that local helper to retain the debug
check, generate a parent proof, verify it with its generated VK, and encode
both proofs. First compile failed because AirProvingContext is not Clone;
resolved by regenerating contexts after the debug check. No debug checks
were disabled. Only the selected tests were run.

Actual workload: nine Fibonacci AIRs, each height256, one child proof,
VerifierSubCircuit MAX_NUM_PROOFS=2. This is the dedicated verifier circuit,
not a general-purpose VM executing a verifier. Results:

| Configuration | Child bytes | Parent bytes | Verification |
| --- | ---: | ---: | --- |
| upstream small test params (WHIR target5) |11934|109441|pass|
| app_params_with_100_bits_security(12), leaf_params_with_100_bits_security() |87838|383529|pass|

The second test took15.00s including its complete test body; timed cargo
invocation30.87s includes compilation. Maximum RSS4126432KiB includes compiler
and test process. These are not isolated prover throughput figures. Nightly
rustfmt applied to instrumentation; targeted crate lib/tests Clippy -D warnings
passed. Seven compressed evidence snapshots are raw-SHA256 pinned, with an
exact reproduction patch and lockfile, under results/swirl-security-review/recursion.

Scope: these tests establish executable parent-proof generation/verification,
not the final narrow root, stabilized recursive VK chain, VM public-value
binding, end-to-end PQ128, or NEAR. A single leaf recursion layer exceeds our
300000B target in this measured case. Do not read the 109441B five-bit smoke
proof as a secure compression result.

Source review also found OpenVM's certified-verifier crate. Its README says
its Lean source-of-truth ws-fv is private, pinned at
b94bf5a2a38535d22a2e5a6633b7e6d8351b8a84; this repository vendors generated C,
not the proof-module closure. Therefore it may be a differential executable
reference, but we cannot audit or reuse its Lean proof dependencies from this
checkout. The root STARK uses a BN254-field Poseidon2 commitment; using that
field for hashing is not itself an elliptic-curve discrete-log assumption.
Its optional Halo2/KZG wrapping remains a separate excluded curve-based stage.

Next: extend the executed verifier path through internal/root configurations,
collect actual trace layout and serialized-component costs, and keep NEAR
public-value/state binding explicit. Full1Petagas NEAR, PQ128 and sound
sub300000B remain unachieved; no Lean acceptance theorem is claimed.


## 2026-10-17 — Measured three-layer generic verifier chain below300kB

Previous goal turn classified progress: executed real parent proof. Revalidated
clean authoritative worktree at0926a03f3 and the existing pinned OpenVM clone.
Extended the experiment with a new nearproof_recursive_chain test. It proves
nine height256 Fibonacci AIRs under app_params_with_100_bits_security(12), then
proves the resulting verifier under leaf, internal and root parameter
constructors. Every stage retains debug AIR checking, generates an actual proof
and verifies it with the generated VK. MAX_NUM_PROOFS=2 throughout.

IMPORTANT: final stage is labeled root_geometry_babybear_hash. It uses the
root schedule/stacking geometry on the generic VerifierSubCircuit with
BabyBear Poseidon2. It is not OpenVM's full VM RootProver (which also binds user
public values and uses a different commitment hash), and not a stabilized
recursive VK chain. The experiment has no NEAR state-transition semantics and
no PQ128 certificate. No curve-based wrapper was used.

| Stage | Serialized bytes | Common cells | Cached cells |
| --- | ---: | ---: | ---: |
| leaf |383529|6489279|3072|
| internal |398697|25261532|393216|
| root geometry / BabyBear hash |242809|14447856|393216|

Final byte decomposition: GKR11448, constraints45980, stacking948, WHIR183884,
framing/other549 =242809 exactly. This provides a concrete sub300000B generic
recursive-verifier proof using upstream100-bit-target constructors; it does not
upgrade the scope/security of our objective. Actual remaining budget is57191B
to reach300000, or57190B for strict less-than.

Trace census changes optimization priority. In the internal verifier,
FinalPolyQueryEvalAir uses11796480cells (46.70%), Poseidon2 uses9863168cells
(39.04%). The terminal polynomial is evaluated through nested per-query Horner
loops (source pinned). Root geometry reduces that polynomial-evaluation table
to737280cells, but hashing remains9863168cells. Thus terminal degree, query
schedule and hash cost must be optimized jointly; cheaper hashing alone does
not remove the internal layer's dominant work.

One compile error required explicitly selecting BabyBearPoseidon2Config for
circuit.airs() in the trace logger; no protocol changes. Final targeted test
passed in57.89s, cargo wall73.30s including compilation; maximum process RSS
4067580KiB includes build. Nightly formatting and targeted lib/tests Clippy
-D warnings passed. All three proof binaries, trace/component logs, exact
instrumented source/patch and lockfile are retained with rawSHA256 pins in
results/swirl-security-review/chain. Independent capture reconciled every
trace-cell total, component-byte sum and serialized proof length.

Next gate: count actual extension-field elements and digest payloads in the
242809B proof, then price the stronger field/hash parameters under our
conditional quantum budget. Also account for VM/NEAR public binding and
recursive key stabilization before treating this as a deployable architecture.
Full1Petagas NEAR, PQ128, Lean acceptance soundness remain open.


## 2026-10-17 — Exact wire census and frozen PQ parameter sensitivity

Previous turn classified progress (three real parent proofs and measured root
geometry242809B). Revalidated clean authoritative worktree atf14c40ca2.
Decoded all three saved proofs with the pinned backend, checked EOF and exact
byte-for-byte re-encoding. No proof regeneration was needed. Added typed
field/digest counts and unique digest counting to the local Rust experiment;
nightly formatting and targeted Clippy passed.

Root geometry census:
-4708extension elements at16B =75328B.
-14657base elements at4B =58628B.
-3374digest occurrences at32B =107968B.
-885B framing. Total242809B, reconciled exactly.
-Extension counts: GKR715, constraints2853, stacking58, WHIR1082.
-2606distinct digests; repeated occurrences768.

screen_swirl_wire_cost.py verifies source/log hashes and recomputes 72
fixed-slot profiles (three stages, six extension degrees, four digest widths).
A hypothetical dictionary stores each unique digest once plus a four-byte
count and a two-byte reference for every occurrence. No dictionary codec was
implemented; all table entries except baseline are projections.

| Root extension | Digest bytes | Ordinary | Dictionary | Free dictionary references |
| --- | ---: | ---: | ---: | ---: |
|4|32|242809|224985|218233|
|4|52|310289|277105|270353|
|9|32|336969|319145|312393|
|9|52|404449|371265|364513|

Degree9 corresponds only to the earlier conditional term-budget screen, NOT a
complete PQ128 parameter set or implemented field. Digest52 is a hypothetical
larger-hash profile, NOT a certified Poseidon instantiation. These counts freeze
queries, circuit layout, hash repetition and framing. A real parameter upgrade
changes the recursive verifier workload too. Thus this is neither a feasibility
certificate nor a universal lower bound for redesigned PCS/frontier multiproofs.
Even granting free dictionary references does not bring degree9 below300000B
in this family. The earlier242809B result therefore does not establish spare
capacity for PQ128 by simple field/hash widening.

Next architectural target: constraint messages contain2853/4708extension
values. Investigate a proved reduction of per-column evaluation disclosure,
while jointly modeling its added rounds, PCS openings and recursion circuit.
These claims cannot simply be omitted. Also retain terminal-polynomial work
and actual frontier multiproofs in the comparison. Need a new full size and
quantum ledger before more large Lean development. Evidence and exact source
patch saved under results/swirl-security-review/census; full NEAR1Petagas,
PQ128 and Lean recursive-acceptance soundness remain open.


## 2026-10-17 — Column-reduction interface and Lean obstruction proof

Previous turn classified progress: typed wire census established fixed-layout
parameter widening fails. Revalidated clean branch atb0ba4983d. Traced pinned
SWIRL verifier consumers: batch_constraints.rs observes the column openings
into the transcript and evaluates nonlinear symbolic constraints/interactions;
stacked_reduction.rs then samples fresh lambda and forms its weighted opening
claim for the committed trace. Therefore omitting the openings alters both
constraint evaluation and Fiat-Shamir chronology. A single linear summary is
not a drop-in replacement for their nonlinear use.

Added NearCompression/SwirlColumnClaimBoundary.lean and imported it from the
library root. Two Lean theorems establish the deterministic obstruction:
for nonzero r, inputs(0,0) and(r,-1) have the same x+r*y but distinct x*y;
there is no function of that single summary that recovers every product.
This is NOT an attack on fresh random batching with inputs fixed before the
challenge. It identifies an interface requirement: a replacement must prove
nonlinear evaluation and PCS linkage for the same committed input, and must
account for new transcript ordering. Existing GKRLayerTransition/common-input
lemmas are available building blocks, not a completed SWIRL composition proof.

Targeted lake build succeeded; both theorem axiom closures contain only
propext, Classical.choice and Quot.sound (no sorryAx). This is a targeted audit,
not a claim that the entire existing Lean library was re-audited this turn.

Refined the saved-proof census: root constraint proof contains2694column
opening elements out of2853total extension elements. Leaf has2684, internal
2694. At hypothetical degree9 (36B/element), replacing all root column claims
removes96984B. Starting from the earlier frozen dictionary projection371265B,
free removal leaves274281B; strict <300000 permits25718B for the ENTIRE
replacement, including new field messages/commitments/openings/recursion costs.
Without dictionary sharing, free removal still leaves307465B. These are cost
counterfactuals, not valid proofs after deletion. Query strengthening and the
actual changed verifier workload are still uncharged, so this does not establish
feasibility. Keep a whole-protocol budget ahead of implementing the reduction.

The census test decoded/re-encoded existing proofs, passed and passed targeted
Clippy; source/log snapshots and budget report live under
results/swirl-security-review/column-boundary. No long proving run was repeated.
Next: evaluate a concrete GKR/shared-input reduction plus stronger PCS query
schedule against this small remaining allowance; reject before implementation
if the combined budget fails. Full NEAR1Petagas, PQ128 and Lean recursive
acceptance remain open.


## 2026-10-17 — Joint query/column-removal gate rejects zero-credit geometry

Previous goal turn classified progress: Lean interface obstruction and exact
column-removal budget. Revalidated clean worktree ate05b6bb5b. Decoded saved
proofs to measure query payload shape without reproving. Root: queries61/30/20,
240base elements per initial query,16extension elements per continuation query.
After removing2694column claims and existing query payloads, fixed values are
17base and1214extension elements plus885framing bytes.

Pinned backend m=1 list-decoding agreement is1.5/sqrt(rate). Replayed the
calculator's biased field-to-index sampling mass using exact Fraction arithmetic.
Rates16/128/1024 and query domains2^20/2^19/2^18 follow the pinned root schedule.
Irrational sqrt128 is enclosed by integer-square-checked rational bounds at
40decimal digits; both interval endpoints certify the same minimal integer
query count. No floating-point threshold decides a query count.

Under our uninstantiated conditional C*Q^2*epsilon ledger, Q=2^128,C=1:

| Error allocation | Hypothetical grinding credit | Queries | Free-auth/free-column-reduction bytes at degree9 |
| --- | ---: | --- | ---: |
| whole1/2budget separately for each term |0|182,89,59|304625|
| query1/4budget split equally among3terms |0|184,90,59|307121|
| whole1/2budget separately for each term |15|172,84,55|289841|
| query1/4budget split equally among3terms |15|173,84,56|291377|

Even the relaxed zero-credit allocation exceeds300000B with ALL authentication
bytes and ALL column-replacement costs zero. Therefore do not implement an
expensive GKR column reduction against this unchanged opening geometry under
that accounting. The15-bit-credit rows have not failed this very weak payload
gate; they have almost no room for omitted components. The credit is a
hypothetical sensitivity parameter, not a proven quantum grinding benefit.

This is failure of a conditional bound/cost screen, not an attack or proof that
PQ128 is impossible. No applicable QROM compiler is instantiated, other error
terms remain omitted, and changing geometry can change the conclusion. In
particular, taller stacking with fewer opened columns deserves a modeled
comparison before another full proof: initial values dominate much of this
expanded schedule. Any such comparison must include terminal polynomial
length, Merkle frontier, revised query bounds and recursive trace costs.

screen_swirl_query_payload.py screens32profiles (C1/256,credit0/15,two budget
allocations,extensions5/9/10/12). Degree5 entries are cost sensitivity only,
not PQ128 candidates. Source/shape logs are hash-pinned in
results/swirl-security-review/query-payload. Typed decode/re-encode test passed,
exact minimal-query checks passed; no new proof or new Lean soundness theorem
is claimed. Full NEAR1Petagas/PQ128/Lean acceptance remains open.


## 2026-10-17 — Broad stacking/frontier screen and workload threshold

Previous turn classified progress: conditional query payload rejected unchanged
geometry with free column reduction. Revalidated clean branch at9081cef4b.
Implemented witness-free screen_swirl_stacking_geometry.py. It reproduces the
242809B raw-path baseline EXACTLY from measured field counts, widths, three
query stages and Merkle depths before exploring any changed layout.

Search: heights2^15..2^25, every blowup2^b with b>=2 and height*blowup<=2^27,
folds1..8 and maximum terminal degree logs1..12, excluding negative final-degree
logs.5790configurations per profile,46320total across extension9/12,digest52/64,
and cached-trace-opened/public variants. Geometry includes source widths from
measured14447856common cells and393216cached cells; terminal polynomial,
sumcheck/stacking message lengths, roots, query values, and expected binary
Merkle frontier hashes. Column-reduction argument is FREE throughout.

Queries use the earlier exact interval method with conditional C=1,Q=2^128,
zero grinding credit and the entire1/2budget granted independently to EACH
query term (optimistically ignoring their sum and every other soundness term).
The model freezes verifier trace work despite larger fields/hashes. It is not
an executable new protocol, PQ128 certificate or universal size lower bound.

At extension9/digest52, best expected full frontier cost396024.72B. Granting
all cached-source verification/openings/authentication free gives326824.40B.
Both prefer stacked logheight19,logblowup8,fold3,final logdegree10,queries76/59/48.
That LDE reaches the BabyBear2^27limit. Thus taller stacking alone is not the
winner; high blowup and a different fold tradeoff also matter. All eight
profiles have zero expected-size survivors. Public-cache best costs for other
profiles: extension9/digest64=362695.95B,extension12/digest52=360940.40B,
extension12/digest64=396811.95B.

Frontier expectation independently matched exhaustive enumeration of682
with-replacement query sequences on small trees. Sixteen seeded full-size
frontier samples for the two extension9/digest52 winners:393709–398129B with
cache opened,325405–328317B with cache free. These are geometry simulations,
not generated proofs; expected size is not a deterministic lower bound.

For a concrete next research threshold, keeping the best free-cache geometry
and fixed non-column messages, reducing common trace cells by2x/4x/8x projects
292272.40/274996.40/267592.40B. No such workload reduction is implemented. These
figures still omit the column-replacement argument and complete security/NEAR
costs; even2x leaves little useful headroom. Fourfold reduction is a more useful
hypothesis to test, especially jointly reducing hash calls and terminal-
polynomial evaluation rather than optimizing one in isolation.

The saved report pins its measured input report. No large proof run was spent
on a failed candidate. Next: identify a specific verifier specialization or
transcript change that reduces the measured common trace, then recalculate
its full authenticated statement and soundness budget. Full NEAR1Petagas,
PQ128 and Lean recursive acceptance remain open.


## 2026-10-17 — Measured hash deduplication and root padding threshold

Previous comparison turn classified no progress: it restated research and
refreshed published sources without changing the implementation decision.
Revalidated clean branch at ed3141514 and inspected current OpenVM source.
CPU TranscriptModule::dedup_poseidon_inputs ALREADY sorts identical full
Poseidon inputs across permutation and compression requests, preserving separate
lookup multiplicities. Poseidon2Air consumes both multiplicities. GPU source
also invokes deduplication; this experiment measures CPU only. Therefore adding
hash deduplication is not a new source of savings over our measured baseline.

Instrumented the existing pinned generic Fibonacci recursive chain to count
requests before deduplication, distinct states and padded rows. Assertions check
that both lookup multiplicity sums equal their original request counts.

| Stage | Permute requests | Compress requests | Distinct | Padded rows |
| --- | ---: | ---: | ---: | ---: |
| leaf |3354|4825|5656|8192|
| internal |6225|16429|19685|32768|
| root geometry, BabyBear hash |11025|7054|16842|32768|

All three recursive proofs generated and verified. Sizes match prior baseline:
383529,398697,242809 bytes. Targeted clippy with -D warnings passed. Artifacts,
source snapshots, lockfile, raw SHA256 pins and full instrumentation patch:
research/near-compression/results/swirl-security-review/hash-census/.

Root dedup already removes1237requests. Its16842distinct states exceed the
16384row threshold by only458 (2.72%). Removing458distinct computations would
halve the301column hash table, saving4931584cells and reducing common cells
from14447856to9516272 (34.13%), IF other tables stay unchanged. This is a
counterfactual threshold, not an implemented optimization or new proof size.
It is substantially less than the earlier fourfold-workload hypothesis and
cannot independently establish the PQ128 budget. Even perfect unpadded storage
of the existing16842states would save4793726cells, not fourfold overall work.

Next: attribute the distinct root states to transcript, initial row hashing,
continuation leaf hashing, Merkle paths and external inputs. Seek458removable
DISTINCT calls with an authenticated statement-preserving transformation;
transport compression or shared-path hashing alone cannot be credited twice.
Any fixed-VK specialization must retain verification-key binding, and any
transcript change needs fresh causal/soundness analysis. No new Lean theorem,
PQ128 certificate, full VM root chain or full NEAR1Petagas proof is claimed.


## 2026-10-17 — Hash source attribution and a table-partition candidate

Previous goal turn classified progress: measured deduplication and root padding
threshold, committed5befaf797. Revalidated clean worktree and reran the pinned
chain with per-source full-input set membership. Diagnostic instrumentation
asserts one child and checks that initial preflight permutations precede
transcript permutations. This patch is a fixture probe, not an upstream-ready
change. All three recursive proofs verified at unchanged serialized sizes;
targeted clippy -D warnings passed.

Root distinct inputs by exclusive source: initial-row hashing8704, Merkle
paths5070, transcript2321, continuation leaves800, external0. Raw Merkle
requests6254; all other categories have no repeated inputs in this run.
No distinct state crosses categories. Total16895versus previous16842: the
458-removal threshold was fixture-instance-specific; this run needs511.
No cause of the run-to-run proof variation is established here. Do not use
these counts as a worst-case bound or infer hashes can be omitted because
input values happen to be public or repeated in another execution.

Source inspection: recursion Poseidon2Air uses row_slice(0), and its pinned
p3-poseidon2-air0.4.3 dependency also evaluates current-row permutation
constraints. Separate permutation/compression lookup multiplicities carry
cross-table usage. This suggests a concrete next experiment: partition the
same hash rows between two copies of that AIR, keeping the same buses and
preserving every multiplicity, instead of deleting required computations.
For this run16384+512rows fit16895states with one padding row. Relative to
32768rows this saves4777472common cells before additional AIR overhead.
This partition is NOT implemented or proved sound yet. Keygen, AIR ordering,
trace-shape binding, added column claims/commitments and recursive verifier
cost must all be measured; smaller trace area does not guarantee smaller proof.

Initial opened-row hashing is now the largest measured source, exceeding
half the distinct states. Future caching/specialization proposals must prove
that the authenticated evaluation at each challenge-selected query is retained;
knowing a verification key does not by itself justify deleting those hashes.
First test the table-partition candidate, then compare complete bytes against
the original proof and update the stronger-security model if it wins.

Artifacts:research/near-compression/results/swirl-security-review/hash-sources/
contains report, successful run/clippy logs, source snapshots, dependency
lockfile, raw hashes and instrumentation patch. Existing padding-census evidence
is preserved as a separate run. No full NEAR1Petagas proof, PQ128 certificate,
new Lean theorem or end-to-end recursion correctness is claimed.


## 2026-10-17 — Executable hash-table partition reduces root proof bytes

Previous goal turn classified progress: source attribution and a concrete
partition candidate. Revalidated clean branch at f402fd50e. Implemented an
opt-in NEARPROOF_SPLIT_HASH fixture transformation on the last recursive
circuit only. Locate its Poseidon2AIR; keep the original row values, divide
its live prefix between16384and512rows, append the same AIR with the same
buses, and keygen the resulting AIR list. Existing valid padding rows fill
the second table. Assertions require no cached/public data on this AIR and
zero permutation/compression multiplicities in all discarded padding rows.
No transcript hash or authentication computation is removed.

The initial attempt failed because the helper matched a bare AIR name while
the runtime name includes generic type parameters. Fixed the helper before
rerunning; this was not a constraint failure. Successful run had16862live hash
rows. Both debug constraint checking and actual proof verification passed.
Targeted clippy --lib --tests -- -D warnings passed after the fix.

| Metric | Prior baseline | Split root |
| --- | ---: | ---: |
| Common cells |14447856|9670384|
| Cached cells |393216|393216|
| Total proof bytes |242809|231997|
| GKR bytes |11448|11448|
| Constraint bytes |45980|50836|
| Stacking bytes |948|884|
| WHIR bytes |183884|168268|
| Other bytes |549|561|

Net savings10812bytes (4.45%) and4777472common cells (33.07%). The added
constraint-opening cost offsets a substantial portion of the WHIR savings.
These are compared with prior baseline runs, not a paired identical-transcript
experiment; baseline sizes have repeated across runs, while distinct hash
counts vary. Retain that limitation. Leaf/internal proofs again verified with
383529/398697bytes. The new final proof and raw source/lock/log pins are saved
under research/near-compression/results/swirl-security-review/hash-split/.

This is an implemented, verified padding optimization for a generic recursive
Fibonacci fixture, not a full VM root or a NEAR proof. Parameters remain upstream
RBR100; the under300k result is NOT PQ128. No Lean partition theorem is claimed.
Next: decode the split proof's new field/hash counts and rerun the stronger
query/field/digest budget with its additional AIR claims; only retain the split
for that target if the complete modeled ledger improves. Before production
integration, prove local-row/lookup-multiset preservation and account for the
changed verification key and downstream recursion. Full NEAR1Petagas, PQ128
and end-to-end Lean correctness remain open.


## 2026-10-17 — Split-layout stronger-security budget still misses target

Previous goal turn classified progress: implemented/verified hash AIR partition.
Revalidated clean worktree at bdc617d8f. Extended typed wire census to decode
and byte-identically reencode the saved split proof without reproving. Exact
counts:5007extension,10753base,3374digest occurrences,905framing bytes. Of the
3156constraint extension values,2995are column claims (baseline2694); fixed
constraint count rises159to161. Initial query has176base values vs240;
queries remain61/30/20,continuation16extension values per query. Unique digest
count2598is instance-specific. Decode/reencode and targeted clippy passed.

Parameterized the existing geometry cost function for column-claim count,
fixed constraint messages and framing. Defaults preserve the old screen:
reran it, with no report changes, including682exhaustive frontier checks.
The new comparison independently reproduces BOTH measured wire sizes exactly
(242809and231997), then screens5790geometries per scenario,46320total.

Same conditional ledger:extension9,digest52,C=1,Q=2^128,zero grinding credit,
each query error independently granted the entire half-budget. These are
uninstantiated sensitivity parameters, not a QROM or PQ128 certificate. Work
is frozen despite different fields/hashes/queries. Expected frontier cost is
not a deterministic lower bound.

| Assumed work retained | Baseline best expected bytes | Split best expected bytes |
| --- | ---: | ---: |
| columns and cached work |493008.72|471034.81|
| columns retained, cached work free |423808.40|408076.20|
| column replacement free, cached work retained |396024.72|363214.81|
| column replacement AND cached work free |326824.40|300256.20|

Zero sub300000expected-size survivors in all eight scenarios. Split winners
use logheight18,logblowup9,fold3,final logdegree9,queries66/53/44, at the2^27
LDE cap. Baseline winners remain19/8/3/10,queries76/59/48. The split helps in
all modeled scenarios but does NOT independently meet the target. The300256
row omits the entire column-replacement argument and cached evaluation/binding;
it is not meaningful production headroom. Keeping both costs yields471035.

Decision: retain the actual hash-partition improvement, but do not start a
large Lean campaign around a standalone split-only compression candidate.
Next viable work must reduce authenticated initial opening/cached evaluation
cost and column-claim cost together, or change the PCS/recursive-verifier
architecture; merely shaving the256-byte optimistic excess is insufficient.
The eventual partition integration still needs local-row and lookup-multiset
preservation formalized. No security assumption is strengthened by this screen,
and no universal impossibility/attack is inferred. Full NEAR1Petagas/PQ128/
end-to-end Lean correctness remain open.

Artifacts and source pins:research/near-compression/results/swirl-security-review/
split-geometry/. Reproducer:airbender/direct-wasm/screen_swirl_split_geometry.py.


## 2026-10-17 — No-cache DAG binding is real work, not free preprocessing

Previous goal turn classified progress: split-layout stronger-security screen.
Revalidated clean branch at bcf109db0. Inspected upstream has_cached=false:
it adds DagCommitSubAir to SymbolicExpressionAir, hashing the constraint DAG
in a row-to-row onion chain with the digest exposed as public values. The
production RootProver selects this mode; StaticVerifierCircuit explicitly pins
the digest to internal_recursive_dag_onion_commit. Merely verifying a generic
proof with arbitrary public values is insufficient to pin the intended DAG.
This is not a newly discovered upstream binding defect.

Implemented opt-in NEARPROOF_DAG_COMMIT and NEARPROOF_TRACE_ONLY in the pinned
single-child chain fixture, retaining the previous hash-table split. Generated
and verified leaf/internal proofs, then generated and debug-checked the final
no-cache trace. Command:NEARPROOF_DAG_COMMIT=1 NEARPROOF_TRACE_ONLY=1
NEARPROOF_SPLIT_HASH=1 RAYON_NUM_THREADS=4 cargo test --locked --profile fast
-p openvm-recursion-circuit tests::nearproof_recursive_chain -- --exact --nocapture.
Final proof was deliberately NOT generated. Existing log stage label remains
root_split_hash; environment/options distinguish this no-cache experiment.

SymbolicExpressionAir height32768, common width24->328. Common cells rise
9670384->19631856 (+9961472), cached cells393216->0. Distinct standalone hash
rows16874still fit16384+512; embedded DAG hashing accounts for the new work
and is not captured by the standalone hash census. Debug checks and targeted
clippy passed. This does not measure full production RootProver (hash field,
continuations and statement still differ).

A5790-geometry sensitivity screen substitutes these measured common cells,
one source tree and free column replacement into the earlier conditional
extension9/digest52 ledger. It freezes the prior fixed messages and omits new
public-value overhead: best expected frontier351596.40bytes. This is only a
favorable workload comparison, not a final proof size or rigorous lower bound.
Reproducer:airbender/direct-wasm/check_swirl_dag_screen.py. No PQ128 inference.

Decision: do not treat has_cached=false as realizing the free-cache optimization.
Its concrete replacement is more expensive in trace area and still fails the
favorable size screen. Next architecture to examine is specialized evaluation
of a fixed constraint DAG with the circuit shape bound by keygen, avoiding
both a generic cached-DAG opening and rehashing the DAG every proof. Such a
change must preserve actual constraint/interaction evaluation and PCS links;
constant-folding alone is not evidence that the nonlinear verification work
can be removed. Compare its full input claims and circuit costs before another
large proof/Lean campaign. Full NEAR1Petagas/PQ128/Lean completion remains open.

Evidence:research/near-compression/results/swirl-security-review/dag-trace/
contains source snapshots for DAG AIR, production root and static digest pin,
trace/clippy logs, patch, lockfile and raw hashes. No final proof artifact or
new Lean soundness theorem is claimed.


## 2026-10-17 — Fixed-DAG arithmetic census and backend boundary

Previous goal turn classified progress: measured authenticated no-cache DAG
cost and inspected its production digest binding. Revalidated clean worktree
at a1d094c7b. Inspected openvm-static-verifier: it fixes the VK, all nonzero
trace heights and AIR permutation, then eval_symbolic_nodes_assigned compiles
symbolic nodes directly into arithmetic. Its implementation backend is
Halo2/KZG. We may reuse the specialization design, not claim its proof backend
satisfies our hash-only requirement. Merely using BN254 field arithmetic is
not the issue; the KZG commitment assumption is the excluded component.

Added a cheap keygen-only census for the child VK consumed by the generic
root: Fibonacci fixture -> leaf verifier keygen -> internal verifier keygen.
No recursive proofs needed for this count. Runtime0.12s after compilation.
Checks every arithmetic operand refers to an earlier node and total counts
sum exactly, per AIR and across all39AIRs. Results:
15516nodes =3773add +2110sub +192neg +5626dynamic mul +930base-constant mul
+512constant +2303variable +34first-row +2last-row +34transition. No
constant-times-constant multiplication nodes remain. Source confirms upstream
SymbolicDagBuilder already folds constants, simplifies identities and performs
structural deduplication; do not claim these as new optimization opportunities.

This counts the DAG used for constraint AND interaction expressions. It is not
a full arithmetic-verifier size: variable selection/evaluation, selectors,
constraint batching, interaction reduction, transcript and PCS work are extra.
2303variable nodes are not a count of unique PCS opening claims. The root input
claims must remain tied to the same earlier committed trace; hardcoding the
DAG only removes structural authentication, not that obligation.

Next concrete design: export/compile this fixed DAG to a native-field GKR
circuit, validate node/output evaluation parity and make its input-opening
interface explicit. Compare complete GKR plus input-link costs with the
existing symbolic-expression AIR and cached/DAG authentication. Do not port
the Halo2 wrapper or infer speed/security from node counts. Existing Lean
common-input/GKR lemmas are potential components, not a soundness theorem for
this compiler. A broad formalization remains gated on that cost/interface test.

Census and clippy --lib --tests -- -D warnings passed after correcting the
probe's VK field paths. Evidence/source pins/patch are saved under
research/near-compression/results/swirl-security-review/fixed-dag/. Full
NEAR1Petagas, PQ128, sub300000secure bytes and end-to-end Lean correctness
remain unachieved.


## 2026-10-17 — Fixed-DAG export/lowering parity and naive GKR depth failure

Previous goal turn classified progress: fixed-DAG census. Revalidated clean
branch at6d083ea17. Extended upstream probe to export all39AIR DAGs as JSONL:
explicit variable kind/part/rotation/index, canonical constants, operation
indices, constraint outputs, interaction message/count indices, bus ids and
count weights. Native SymbolicEvaluator::eval_nodes produces reference values
for three synthetic base-field assignments per AIR. These are evaluation tests,
not actual accepted proof witnesses or independent random extension challenges.

Added compile_swirl_fixed_dag.py: lowers negation to subtraction, preserves
variable coordinates as explicit input slots, retains all constraint and
interaction outputs, and feeds a balanced diagnostic checksum into our
existing layered GKR layout builder. Fixed checksum coefficients are ONLY a
cost/parity device; they are NOT sound random output batching. Every15516source
node matches native values for all3assignments (46548node comparisons). Every
layered output matches direct evaluation in117AIR/case pairs. Altered reference
values and a self-referential arithmetic edge are rejected. Upstream export
test and clippy passed. No extension-field or Lean compiler proof is claimed.

Measured lowering:2373input slots,3871distinct semantic output nodes,
27282lowered nodes (27275live),137070padded gates,937layers across39separate
circuits. Deepest circuit is AIR14 with229layers; AIR16has74layers. Depth is
not captured by the earlier arithmetic-node census and is a material cost.
Existing GKR message layout requires6*log2(previous_width)+2extension elements
per layer:36452elements total, or1312272bytes at hypothetical extensiondegree9,
BEFORE framing, output batching, input PCS links and other verifier work.
This is a layout-derived payload count, not a generated GKR proof. It rejects
this naive separate-circuit lowering under that message format, not all GKR.

Next: inspect long dependency chains and test depth-reducing algebraic
reassociation plus shared/batched layering before expensive proving. Any
rewriting must preserve every constraint/interaction output and bind the same
input coordinates; later random output aggregation must have explicit timing
and error accounting. The compiler export itself does not eliminate column
opening costs or provide cryptographic soundness. Full NEAR1Petagas/PQ128/
secure sub300000bytes/end-to-end Lean correctness remain open.

Artifacts:research/near-compression/results/swirl-security-review/dag-export/
contains compressed full DAG/reference export, compiler report, source/log
pins and upstream patch. Reproducer:airbender/direct-wasm/compile_swirl_fixed_dag.py.


## 2026-10-17 — Reassociation plus combined layering passes component-size gate

Previous goal turn classified progress: exported fixed DAG/native parity and
rejected naive separate GKR layout. Revalidated clean branch at d7cb128ae.
Implemented bounded linear reassociation over BabyBear: flatten add/sub and
base-constant multiplication into modular coefficient maps, discard zero
coefficients, hash-cons emitted operations, and combine terms by increasing
subtree depth. Forms larger than512terms fall back to the original operation.
Dynamic multiplications remain nonlinear atoms. Original node outputs remain
addressable for parity; unused generated nodes are pruned by existing layout.

Combined all39AIR DAGs with explicit AIR namespaces on variable and selector
inputs; operation and semantic output indices are offset, interaction bus/count
metadata retained. Assert combined input count equals the sum of separate
counts2373, so equal synthetic values cannot accidentally merge independently
bound coordinates. Output checksum still uses FIXED DIAGNOSTIC coefficients;
it is not a sound batching protocol or the native verifier acceptance predicate.

| Layout | Padded gates | Total layers | GKR extension elements | Degree9 field bytes |
| --- | ---: | ---: | ---: | ---: |
| separate, original |137070|937|36452|1312272|
| separate, rebalanced |54514|489|17598|633528|
| combined, original |146218|232|11810|425160|
| combined, rebalanced |62890|23|1198|43128|

Message count uses the existing GKR format: each layer6*log2(previous width)+2
extension values. No proof generated, framing/input openings/PCS links excluded.
Reassociation reduces deepest separate circuit229to21layers; combined has23.
This passes a component payload gate that failed badly for naive lowering,
not the complete secure300000-byte target. Input commitments and output batching
may change the circuit and size. Degree9 is still a sensitivity parameter.

Every exported node matches three native base-field assignments, and layered
checksum outputs match. Rewrites additionally compare every requested original
node/root at all-zero, all-one, all-minus-one and independent seeded random
slot assignments. Tests include selectors/AIR namespaces independently rather
than relying only on equal synthetic selector values. Existing malformed-edge
and altered-reference rejection checks still pass; unchanged default compiler
report reproduces. No extension-field/Lean compiler soundness theorem yet.

Next: execute GKR prove/verify for the combined rebalanced graph and validate
the returned input functional obligation against the same original coordinates.
Then replace diagnostic output checksum with a sound reduction matching actual
constraint/interaction consumers and establish challenge chronology. Those
interfaces, and arithmetic rewrite correctness, are the relevant Lean targets.
Do not call the43128-byte component an end-to-end proof. Full NEAR1Petagas,
PQ128, secure sub300000bytes and end-to-end Lean correctness remain open.

Reproducer:airbender/direct-wasm/measure_swirl_rebalanced_gkr.py.
Evidence/source hashes:results/swirl-security-review/dag-rebalance/.


## 2026-10-17 — Executed rebalanced DAG GKR with explicit input obligation

Previous goal turn classified progress: depth rewrite/combined layout passed
component-size gate. Revalidated clean worktree at4026f8a9b. Exposed optional
compiler artifacts and added prove_swirl_fixed_dag.py. Uses independent seeded
Ext4 coordinates, evaluates original exported DAG and its diagnostic checksum,
then checks the layered circuit returns the same checksum. Real native Ext4
GKR prover and Python verifier executed on the combined23-layer graph.

Proof has1198extension elements exactly as predicted,19168bytes of canonical
Ext4 field payload. Prover10.05s; verifier2.50s on this host, not a production
benchmark. The earlier43128bytes is degree9 sensitivity only; no Ext9 proof,
field instantiation or PQ128 claim. Framing, circuit/input metadata, PCS input
proof and all other verifier work are excluded from field-payload counts.

Prover and verifier return the same input functional obligation. Its dot
product matches the original padded input vector. Changing a nonzero-weight
input fails that explicitly checked obligation. Altered proof round, output
claim, statement and layer count reject. Fresh process reconstructs the trusted
layout from the exported DAG, compares stored layout/coordinate mapping,
verifies saved proof, and checks the full-witness obligation again. Layout is
not accepted solely from proof-supplied metadata. Source export, payload,
proof/layout/inputs/claim/obligation, logs and hashes are retained.

Scope limits: fixed diagnostic output coefficients are NOT sound random
batching, the output is not native verifier acceptance, and checking a full
input vector is NOT authenticated PCS linking. An input linear functional
alone does not bind all coordinates. This experiment establishes an executable
GKR component, not a secure recursive compression proof. Original source
compiler reports and layout estimates reproduce after the optional API change.
No Lean theorem or full NEAR/PQ128 result is claimed.

Next must jointly price the actual output-reduction interface and the PCS link:
previous free-column cost screens charged ZERO for this replacement; they must
now pay its messages and account for changes in the recursively verified
circuit. Then instantiate challenge chronology and common-input obligations
before compiler/GKR Lean composition. The small component alone does not
close the full300000-byte gap or NEAR1Petagas semantics/capacity obligations.

Evidence:research/near-compression/results/swirl-security-review/dag-gkr/.
Reproduce:airbender/direct-wasm/prove_swirl_fixed_dag.py; replay with
--verify-saved. Full goal remains active and unachieved.


## 2026-10-17 — Native output-consumer weights and dynamic GKR coefficient inputs

Previous goal turn classified progress: executed GKR component and full-witness
input-obligation check. Revalidated clean branch at46ce467fc. Inspected pinned
backend verifier/batch_constraints.rs: terminal evaluated_claim combines
2*Tinteraction outputs followed byTconstraint outputs with mu powers. Constraint
terms use lambda powers and eq_ns; interaction numerators use eq3b,norm_factor,
eq_sharp; denominators use beta_logup powers,eq3b,eq_sharp and bus_index+1.
Lambda and mu are sampled earlier, not after a new diagnostic output checksum.

Implemented terminal_weights: derives sparse node coefficients plus a constant
bus-identifier offset for this exact scalar formula, given controls and trace
order. Independent procedural transcription of the native consumers matches
for arbitrary Ext4 node values across six scenarios (forward/reverse AIR order,
random/zero/one scalar challenges). Four nonzero-offset cases reject dropping
the bus constant. Four malformed cases reject wrong trace-control shape,
interaction shape, node index and bus range. This is algebraic interface
validation, not replay against controls captured from a real native proof.

Extended compiler with optional public_weights input slots. Keeps AIR variable
coordinates distinct, adds3871output-coefficient slots to2373DAG inputs and
retains23layers. Result:66214padded gates,1264GKR extension messages,45504bytes
at hypotheticaldegree9 (versus1198/43128for fixed checksum). Same native-node,
layer-output and independent-slot reassociation checks pass. Default saved GKR
proof still verifies in a fresh process after the compiler option change.
No dynamic-weight GKR proof generated this turn.

Crucial boundary: the additional slots are physically ordinary GKR inputs;
they are NOT automatically public/constrained just because the option is named
public_weights. The verifier must compute their values from bound parameters,
trace order and actual transcript, and subtract their exact contribution from
the final input functional obligation. The remaining obligation must link to
the SAME earlier committed trace evaluations, including rotations and cached
parts. Neither constant offset nor arbitrary prover-supplied coefficient slots
may be dropped. No claim that exposing all coefficients costs zero verifier
work, or that the original transcript remains valid after omitting columns.

Next: execute the weighted component with verifier-supplied controls, split
known coefficient inputs out of its obligation, and map remaining coordinates
to the PCS opening interface. Before cryptographic/Lean composition, derive
real controls, challenge chronology and the native evaluated_claim equality.
Full NEAR1Petagas, PQ128, secure sub300000bytes and end-to-end Lean remain open.

Reproducer:test_swirl_consumer_weights.py. Artifacts, pinned native source and
new layout:results/swirl-security-review/consumer-weights/.


## 2026-10-17 — Weighted GKR execution and formal known-input subtraction

Previous goal turn classified progress: exact native-consumer coefficient
formula and dynamic-weight layout. Revalidated clean worktree at8b05a32d2.
Added prove_swirl_weighted_dag.py. Derives output coefficients/constant offset
from synthetic fixture-owned controls, independently evaluates original Ext4
DAG nodes, and proves the weighted output equals native-form scalar minus the
bus offset. GKR layout23layers,1264extension elements,20224Ext4 field bytes.
Native round kernel/Python verifier agree. Fresh-process replay reconstructs
fixture/layout and verifies saved proof and residual obligation.

Known inputs are3871output coefficients plus70selector inputs =3941slots.
Remaining2303variable coordinates are typed as PCS inputs with AIR namespace,
main/preprocessed kind, partition, rotation and column index retained. No Public
or Challenge variable nodes occur in this particular DAG fixture. Split code
accepts known values from the caller, not proof metadata, subtracts their
weighted contribution, and emits the remaining coordinate weights/claim.
It validates canonical contiguous slot assignment and input length. The
unused private-capacity tail is explicitly a zero-padding range; fixture
validation rejects nonzero padding rather than silently discarding it.

The complete residual is checked against the original full input witness.
Changed known value changes the residual, missing known input rejects, altered
GKR input claim rejects, and nonzero padding rejects (four checks). This is
NOT a PCS opening proof. Controls/selectors are synthetic and statement-bound
before GKR in this fixture; they are NOT extracted from a native proof transcript.
Actual native evaluated_claim acceptance, trace order, selectors and challenge
chronology still require integration. Proof/obligations/logs/source pins saved
under results/swirl-security-review/weighted-dag-gkr/.

Added NearCompression.SwirlKnownInputSplit, imported by package root. Two Lean
theorems establish exact partition of a weighted list into known/PCS terms and
the equivalence between the complete claim and residual=claim-known_sum.
Targeted lake build passes; #print axioms lists only propext,Classical.choice,
Quot.sound, no sorryAx. This proves the subtraction algebra, not correctness of
the Python coordinate classifier, compiler, GKR security or commitment binding.
Full historical theorem audit was not rerun; do not update its count from this.

Next: extract real native terminal controls and evaluation coordinates, then
match the residual functional to an actual PCS opening relation with fixed
trace/AIR provenance. Price that complete link and recursive workload before
claiming a compression win. Ext4/20224bytes remain diagnostic; no degree9
implementation, PQ128 certificate, full NEAR1Petagas proof or end-to-end Lean
correctness is claimed. Full goal remains active.


## 2026-10-17 — Replay terminal consumer against accepted native proof controls

Previous goal turn classified progress: weighted GKR and Lean known-input
partition. Revalidated clean branch at692dcd62a. Added opt-in instrumentation
to pinned backend verifier/batch_constraints.rs. Only after native terminal
sumcheck equality succeeds, append lambda/beta/mu, trace/AIR order, per-trace
node evaluations/selectors, equality weights, lift normalization, evaluated
claim and accepted sumcheck claim. Native verification logic is unchanged.

Initial attempt reused Cargo's compiled git dependency despite edited checkout;
no capture was produced. Waited for that run to complete, cleaned only the
fast-profile openvm-stark-backend package, rebuilt and reran the chain. Capture
is from the successful rebuilt run. All three proofs verified at previous
383529/398697/242809byte sizes. Targeted backend clippy -D warnings passed.
Source patch/snapshot plus matching internal proof and lockfile are saved.

Three captures have15066,15516,15504nodes. Only capture1matches the exported
fixed internal-verifier DAG shape; checker explicitly matches per-AIR lengths
and identity set rather than treating all39-AIR verifiers as identical. Real
trace order starts36,0,14,5,15,... and is used for mu-power positions. Checked
13213non-variable nodes against exported operations/constants and captured
selectors. Recomputed coefficient+offset scalar AND independent procedural
consumer scalar match native evaluated_claim and accepted sumcheck claim:
[941997310,1041078624,1976683812,467589941] in the native Ext4 basis.
Changing mu or omitting the nonzero bus offset changes the scalar as expected.

This removes synthetic controls from the consumer identity test. Variable
values are still read from native evaluator nodes, not independently extracted
from proof column openings; that coordinate/rotation provenance is next.
The native proof still sends all column openings before later transcript
challenges. No old transcript is asserted valid after removing those messages.
No GKR has replaced native terminal verification or PCS here, and no PQ128,
full NEAR1Petagas or new end-to-end Lean theorem is claimed.

Next: replay weighted GKR on this accepted control capture and map every
residual variable coordinate to the actual disclosed opening (common/cached
partition, rotation, AIR permutation). This establishes the data interface before
attempting authenticated opening replacement or a new transcript schedule.
Reproducer:airbender/direct-wasm/check_swirl_native_controls.py.
Evidence:results/swirl-security-review/native-controls/. Full goal stays active.


## 2026-10-17 — Native openings mapped through weighted GKR residual

Previous goal turn classified progress: real native terminal control replay.
Revalidated clean branch at f33978554. Extended keygen-only upstream fixture
with optional saved-proof opening export. Decode/reencode saved internal proof
byte-identically, regenerate its internal verification key, and verify the
proof. Derive trace order independently from trace heights/air-id tie breaking;
export per-trace need_rot, preprocessed/cache structure and ordered openings.
A Rust extension-field basis type inference error in the probe was corrected;
export test and targeted clippy pass. No new upstream recursive proof run needed.

New prove_swirl_native_dag.py maps every source variable coordinate to that
export: common opening part0, cached parts after optional preprocessed part,
main DAG common part last, and interleaved current/rotated claims when need_rot.
All2303variable values equal their native captured node evaluations, including
757rotated coordinates and12cached-column coordinates. Actual trace permutation
matches the capture. Selector values and consumer coefficients come from that
accepted native control capture. No synthetic inputs remain in this fixture.

Ran native-kernel GKR prove/Python verify on the combined weighted circuit.
Native trace order slightly changes layering versus AIR-id order:1258extension
elements,20128Ext4field bytes (previous synthetic ordering1264/20224). All3941
known inputs are subtracted, leaving2303PCS coordinates plus explicit zero
padding. Full-witness residual check and four existing negative checks pass.
Fresh process rebuilds fixture/layout from captures, verifies saved proof and
checks residual; default synthetic fixture's saved proof replay still passes.
Prover about10.17s on this host, not a production benchmark.

This completes a concrete DATA interface between the original accepted proof,
its terminal scalar, weighted GKR and the remaining coordinate functional.
It does NOT replace native verification: the original proof and column openings
remain required. The diagnostic GKR statement hashes the entire native capture,
including node values; that binding is deliberately not claimed to compress
those values. Deriving controls after removing disclosed openings requires a
new justified transcript schedule. A PCS proof of the residual functional and
its same-trace/rotation binding remain unimplemented. Ext4 is not PQ128; field
payload is not total proof size. No new Lean theorem/full NEAR1Petagas claim.

Next: derive the residual's functional on actual committed trace polynomials
using the original evaluation point, lift and rotation conventions, then price
and prove an authenticated opening of it. Existing known-input subtraction
lemmas cover only algebra; compiler and cryptographic composition remain open.
Artifacts:results/swirl-security-review/native-dag-gkr/; reproducible with
prove_swirl_native_dag.py and --verify-saved. Full goal remains active.


## 2026-10-17 — Arbitrary-pair stacking kernel and actual residual grouping

Previous goal turn classified progress: native openings mapped through GKR.
Revalidated clean worktree at60f3bd135. Inspected pinned stacked_reduction.rs,
StackedLayout and poly_common. Native opening reduction batches current/rotated
claims with(lambda^(2j),lambda^(2j+1)); the kernel is linear in those two
coefficients. A GKR residual supplies arbitrary pairs instead. This requires
changing both initial claim and terminal coefficients, not merely changing
lambda or discarding openings in the existing verifier.

Implemented source_weight for arbitrary pairs, including high-cube placement,
negative-n short-trace indicator, r0 power transport and the native forward
rotation kernel. Independent dense Lagrange/Boolean interpolation checks cover
240identities across120fixtures,48short-trace cases;72fixtures distinguish
backward rotation from required forward rotation. Each fixture checks both the
weighted trace functional and off-domain kernel interpolation. Toy sources are
placed at aligned offsets in individual stacked columns; heterogeneous shared
column packing and full native-layout instantiation remain to be tested.

Added native Rust oracle using pinned poly_common kernels. All30off-domain
comparisons match, including BabyBear root-of-unity convention and short-trace
lift. Oracle test and targeted clippy -D warnings pass. Saved native outputs,
source snapshots, patch and hashes permit replay without recompilation.

Grouped the ACTUAL native-data GKR residual's2303coordinates into1548column
pairs,757with nonzero rotated weights. Current/cached partition extraction is
rechecked against saved proof openings; grouped scalar equals residual
[293547415,1139398467,1412829188,92166400]. No assertion that all pairs are
powers of one challenge. Source and target slot conventions are explicit.

This is kernel/data-interface evidence, not a generated stacking sumcheck or
PCS proof. It does not establish adaptive challenge soundness, commitment
binding, actual r-point extraction, Lean kernel correctness, PQ128 or full
NEAR1Petagas. Existing source point and full authenticated layout still must be
bound. No proof-size saving inferred from240checks or pair counts.

Next: instantiate weighted sumcheck with the actual committed stacking layout,
prove its terminal opening relation and preserve chronology after GKR, then
price the extra argument against the full stronger-security ledger. Full goal
remains active. Reproducers:test_swirl_weighted_stack_kernel.py and
group_swirl_pcs_pairs.py; evidence:results/swirl-security-review/weighted-stack-kernel/.

## 2026-10-17 — Native stacking layout and Ext4 mixed-packing interface

Previous comparison turn classified no implementation progress: it rechecked
published options but did not change the selected next experiment. Revalidated
worktree at3651d9b8f and the completed native export process via its successful
test log and generated outputs; no duplicate prover run launched.

Extended accepted-control capture with actual r and l_skip. Regenerated VK,
verified saved internal proof, and exported layouts from verify_proof_shape.
Removing the two new fields yields EXACTLY the previous accepted capture1.
Source/patch snapshots, input hashes, logs and proof hash are saved under
results/swirl-security-review/native-stack-layout/. Recursion and backend
clippy -D warnings pass.

Mapped all1548 residual column pairs through actual common/cached partitions
into two commitments of widths49and1, height2^19, l_skip2. Layout has1549source
slices. Checked unique source coordinates, alignment, bounds, nonoverlap and
captured trace heights. There are44mapped short-trace pairs. Accumulated Ext4
terminal coefficients at a deterministic synthetic evaluation point; original
source evaluation point r is native. Ext4 kernel agrees with30saved native
base-field oracle cases.

Added independent Ext4 dense Lagrange/Boolean interpolation checks with three
heterogeneous source heights sharing ONE destination column. Twelve fixtures
check both the original weighted functional and off-domain interpolation of
the accumulated kernel:24identities,12short sources,12wrong-direction rotation
differences. This closes a test gap in the prior separate-column/base-field
fixtures, not a formal kernel theorem.

No weighted sumcheck generated yet. The terminal point u is synthetic, source
matrices are not reconstructed and no final PCS opening equality is claimed.
Original proof/openings remain required. No proof-size saving, PQ128, new Lean
composition theorem or full NEAR1Petagas result follows from this mapping.
Next reconstruct or regenerate matching committed source matrices and prove
the arbitrary-pair weighted sumcheck, then authenticate its terminal opening
and justify the changed challenge chronology. Full goal remains active.

## 2026-10-17 — Preserve a native proof with its exact committed witness

Previous goal turn classified progress: native layout/point mapping and Ext4
mixed-packing checks committed at78b920267. Revalidated clean worktree.
Attempted internal trace regeneration from saved leaf proof and regenerated
keys. Leaf and original internal proofs verify; cached commitment matches,
but recomputed COMMON commitment does not match original internal proof.
Saved failing log. Cause remains unresolved; no original-witness recovery
claim and no original artifact replaced. Source trace order matches backend
height-descending/AIR-id ordering; this alone does not resolve the mismatch.

Generated a FRESH internal proof from the exact regenerated contexts, verified
it, and asserted its common commitment equals independently recomputed root.
Cached trace commitment was also independently recomputed. Exported40raw
row-major matrices, canonical little-endian base-field elements, manifest and
matching fresh proof/control capture/openings/layout. This bundle is distinct
from earlier native-dag-gkr and requires fresh residual weights.

Independent native probe evaluates all2694disclosed current/rotated openings
from exported raw matrices at the accepted native point. It handles short
trace r0 transport and forward cyclic next-row rotation; every value matches.
Probe runs in0.27s after compilation; fixture generation+proof25.65s, not a
production benchmark. Both targeted tests and clippy -D warnings pass.

Preserved witness archive32155960bytes with per-file SHA256; archive replay
checks all42files. Archive size is witness storage, NOT proof size. Sources,
patches, successful/failing logs, leaf proof and provenance are saved under
results/swirl-security-review/committed-witness/. Original artifacts retained.

Next generate the weighted GKR residual for THIS new capture, then feed its
arbitrary current/rotated coefficients into stacking sumcheck using these
matching committed matrices. Old residual cannot be silently reused. No new
weighted sumcheck/PCS authentication, PQ128, Lean composition or full NEAR
1Petagas proof has been achieved. Full goal remains active.

## 2026-10-17 — Native arbitrary-weight stacking sumcheck executed

Previous goal turn classified progress: matched committed witness saved at
d99d444c2. Revalidated clean worktree. Parameterized native GKR fixture and
pair grouping to preserve old artifacts while using the fresh committed-witness
capture. New GKR proof1258EF/20128Ext4field bytes; fresh-process replay and
old native fixture replay pass. New residual is
[822778656,238050685,651066353,73744785],2303coordinates/1548column pairs,
757nonzero rotated weights. Explicitly do not reuse the old residual.

Encoded weights in actual commitment/layout sorted-column order, with zero
weights for the one unreferenced source column:1549pairs total. Added a
DIAGNOSTIC native CPU prover setter replacing both current and rotated
lambda-power coefficients. Default upstream constructor/protocol unchanged.
Probe loads the saved40source matrices, recomputes common/cached commitments
and matches fresh proof roots before running sumcheck. Full native code and
patches are saved. Compile fixes: private module export, polynomial accessor,
explicit transcript configuration and unused-result annotations.

Standalone diagnostic transcript binds commitments, dimensions, source point,
residual claim and all weights before any sumcheck round. Native receiver
independently replays the challenges. Generated degree6initial polynomial and
17quadratic rounds:41EF, plus50terminal stacked-column evaluations. Every
terminal evaluation independently recomputed by full matrix dot product against
hyperprism evaluation weights. Native test passes in11.63s including commitment
reconstruction; this is not a production proving benchmark. Clippy passes.

Independent Python verifier checks initial domain sum, all round reductions
and final arbitrary-weight kernel equation at captured challenges using actual
layout/short-trace conventions. Four mutations (initial coefficient, round
value, challenge, terminal opening) reject. Checks canonical Ext4 encoding and
expected dimensions. Total91EF=1456Ext4field payload bytes; this excludes
serialization/context and is NOT a PCS proof or complete compressed proof.
Evidence:results/swirl-security-review/weighted-native-sumcheck/ and
witness-dag-gkr/. Prepare and checker scripts preserve explicit source hashes.

This supplies the previously missing executable weighted SUMCHECK bridge.
Its final50evaluations are checked with full witness, not authenticated by a
new WHIR proof. The GKR controls still come from a native transcript containing
all old disclosed openings; the diagnostic capture-bound GKR statement is not
compression. Next connect a new PCS opening at the actual sumcheck point,
then justify a causal combined transcript and price all costs at stronger
security. No PQ128, new Lean composition theorem or full NEAR1Petagas claim.
Full goal remains active.

## 2026-10-17 — WHIR authenticates weighted sumcheck terminal evaluations

Previous goal turn classified progress: executable native weighted sumcheck at
9a05e9aea. Revalidated clean worktree. Extended diagnostic native probe to
absorb all50stacked openings after sumcheck, expand prism point u0 to binary
powers, and invoke the unchanged native CPU WHIR prover on the exact committed
matrices. Separate receiver replays the same transcript. Pinned proof-shape
checker runs with regenerated matching VK before native WHIR verification.
Encode/decode/reencode is exact. Changed opening, commitment, point and final
polynomial each reject in WHIR (four checks).

Measured encoded WHIR337932bytes and encoded weighted stacking1476bytes.
Sumcheck JSON is byte-value identical to the previous accepted diagnostic.
Full probe17.28s including matrix commitment regeneration and full dot checks;
not a production benchmark. No original fixture or transcript overwritten.

Added fresh-process replay from SAVED stacking/WHIR binaries, residual weights
and the original native proof. It reconstructs keys, validates original proof,
checks new proof shapes, samples every sumcheck challenge itself, verifies
initial/round/final arbitrary-weight equations with native kernels and actual
layout, then verifies WHIR. It reads NO source matrices. Replay passed0.24s;
clippy -D warnings passed. Sources/patches/binaries/logs/hash pins saved under
results/swirl-security-review/weighted-whir/.

This replaces full-witness terminal checking with a real PCS opening argument
for the diagnostic weighted reduction. However original native proof and its
full-opening transcript still supply the GKR control context. It is NOT a
compressed replacement protocol or a combined end-to-end Fiat-Shamir proof.
GKR field payload20128 + stacking1476 + WHIR337932 =359536bytes even before
other metadata/context. This subtotal mixes actual encoded components with
GKR field-only payload and is explicitly not a complete proof encoding.
Internal fixture WHIR size is unchanged from its original337932bytes. Hence
this geometry fails300000 even before PQ128. It does not establish a lower
bound for the smaller root-split geometry or a redesigned PCS.

Next resolve combined transcript chronology and evaluate the authenticated
replacement on root geometry, with full byte/security accounting. Lean
known-input algebra remains useful but no new cryptographic composition theorem
is claimed. Full NEAR1Petagas, PQ128 and secure sub300000remain unachieved.
Full goal stays active.

## 2026-10-17 — Opening-free prefix controls and public-statement GKR

Previous goal turn classified progress: weighted WHIR authentication at
b4f74c8cc. Revalidated clean worktree. Source chronology audit corrects an
over-broad dependency concern: native lambda,beta,mu,r and terminal cur_sum
are ALL fixed before column openings are observed. Removing openings changes
later stacking/WHIR challenges, not these earlier controls. Thus a retained
native prefix can feed a new terminal GKR without that apparent cycle.

Refactored pinned native verifier into shared verify_zerocheck_and_logup_prefix
plus existing terminal evaluation. New typed BatchConstraintPrefixMessage has
only numerator/denominator terms and sumcheck messages; NO column-opening field.
Returns controls/point/equality factors and terminal scalar. Public selectors
computed through native evaluator with empty column inputs. Caller must still
validate prefix shapes and preamble; the diagnostic test validates original
proof first. This is not a standalone compressed-prefix wire decoder.

Test compares baseline with removed and changed column openings. Controls AND
complete prefix transcript log match exactly in both cases. Altered retained
numerator claim rejects. All exported controls/selectors equal the original
accepted capture after removing witness nodes and redundant evaluated_claim.
Full native verification remains passing after refactor; saved weighted-WHIR
replay regression and clippy pass. Native prefix test0.34s after compilation.

Generated a NEW1258EF/20128Ext4field-byte GKR proof whose statement hashes only
public prefix controls and the opening-free prefix transcript log hash. It no
longer hashes captured witness node values. Existing fixture supplies prover
witness inputs; fresh replay passes. Changed prefix digest and old capture-bound
GKR proof reject (two binding checks). Log uses pinned Debug representation as
a diagnostic checkpoint, not a stable production codec or QROM construction.

Added separate verify_swirl_prefix_dag.py: derives all3941known slots from
public controls and fixed DAG, verifies GKR, and emits the same2303-coordinate
residual without reading column openings, captured witness nodes or source
matrices. This closes the public-data interface gap in the old replay runner.
It trusts verified native prefix controls; it does not independently replay
native Poseidon or authenticate the residual PCS obligation.

New statement changes GKR challenges/residual weights, so prior weighted-WHIR
artifact cannot be reused. Next regenerate weighted stacking+WHIR for this
residual and bind their diagnostic statement to the verified GKR transcript,
then implement prefix-only shape/wire validation and assess root geometry.
Evidence:opening-free-prefix/ and prefix-dag-gkr/ under swirl-security-review.
No new Lean theorem, complete compressed protocol, PQ128 or full NEAR1Petagas
claim. Full goal remains active.

## 2026-10-17 — Public GKR drives an authenticated continuation

Previous goal turn classified progress: opening-free prefix/GKR at44785ef02.
Revalidated clean worktree. Public GKR verifier now returns its derived residual
and statement/proof. New preparation derives all1549native pairs (1548used,
one zero-filled) from that verified residual and fixed public trace/layout
metadata, without reading opening values or source matrices.

Added explicit SHA384 digest of canonical domain-separated public GKR statement
and complete GKR proof to native stacking transcript seed. Native prover and
replayer absorb domain tag, length and all48digest bytes as field elements
before the first stacking message/challenge. Digest is computed by verifier
preparation, not accepted from proof metadata. This is diagnostic composition
of existing hash transcripts, not a proved Fiat-Shamir/QROM transformation.

Generated fresh weighted sumcheck+WHIR for the NEW public-statement GKR residual.
Full probe passes16.84s; 50full-matrix evaluations agree. Encoded sizes remain
337932WHIR and1476stacking. Four native WHIR tampering checks reject. Saved
native replay passes0.22s without source matrices. Changing one binding digest
byte rejects at terminal sumcheck equality; saved expected-failure log. Clippy
passes. Original weighted/native artifacts remain unchanged in repository.

Added replay_swirl_prefix_continuation.py orchestrator. It re-verifies retained
native proof and recomputes opening-free prefix, compares complete prefix log
and controls, verifies public GKR, derives weights AND digest, and then replays
native weighted sumcheck/WHIR. Successful complete diagnostic replay reads no
source matrices. Public trace metadata is fixed exported key/proof data; a
standalone parser must derive/validate it instead of trusting a fixture file.

This closes the previous NEW-residual PCS gap at the executable component level.
Still retains original native proof for prefix/shape validation; no independent
compressed-prefix codec or complete proof-size claim. Next remove that retained
full-proof dependency using typed prefix-only decoding/shape validation, then
measure on root geometry and formalize composition interfaces. Internal WHIR
alone already exceeds300000, so this interface success is not size feasibility.
No PQ128, new Lean security theorem or full NEAR1Petagas proof. Goal stays active.
Evidence:results/swirl-security-review/prefix-continuation/.

## 2026-10-17 — Prefix-only codec removes original-proof replay dependency

Previous goal turn classified progress: public GKR/WHIR continuation at50a603d3b.
Revalidated clean worktree. Added native diagnostic NPREF001 codec containing
common commitment, key-directed trace presence/heights/cached roots/public
values, native LogUp GKR, and constraint-sumcheck prefix messages. No source
column openings, old stacking proof or old WHIR proof are encoded.15567bytes.
Lengths come from trusted VK plus bounded decoded heights, not attacker-supplied
vector lengths. Decoder rejects trailing bytes and noncanonical field values.
This profile explicitly rejects preprocessed AIRs; scope is current fixture.

Decoder validates presence, nonempty traces, height limits and linear height
constraints before deriving LogUp and sumcheck dimensions. Creates explicit
zero COLUMN SHAPE PLACEHOLDERS only to reuse native proof-shape checker with
new stacking/WHIR tail; placeholders are never accepted as actual openings and
full native verification is deliberately not called on that adapter. Actual
terminal relation is checked by public GKR and authenticated weighted PCS.
Roundtrip passes; seven codec negatives plus separate invalid presence-tag and
excessive-height probes reject (nine total). Clippy passes.

Native prefix replay now derives public trace shapes and stacking layouts from
VK and decoded prefix. Driver compares these to Python handoff metadata,
recomputes public controls/full prefix log, verifies GKR, derives residual and
binding, and verifies weighted stacking+WHIR. Temporarily moved original native
proof out of its expected path: entire replay passes without recreating it;
file restored afterward. No source matrices read. Original dependency is now
removed for this diagnostic replay. Historical artifacts/logs preserved.

Sources/new-file patch,15567byte prefix, metadata, positive/negative logs and
hash pins saved in results/swirl-security-review/prefix-codec/. Reproducer:
replay_swirl_prefix_continuation.py. New runtime logs go to prefix-codec rather
than mutating prior prefix-continuation evidence.

Still not a complete framed binary bundle: GKR remains a separate JSON artifact
and fixed public circuit/profile data are external verifier inputs. Component
subtotal15567prefix+20128GKRfieldpayload+1476stacking+337932WHIR=375103bytes,
before any new framing. Internal geometry fails300000 even at diagnostic
settings. Next finalize compact GKR/bundle encoding, assess root geometry,
and formalize parser/composition boundaries. No PQ128, Lean codec/security
composition or full NEAR1Petagas correctness is claimed. Goal stays active.

## 2026-10-17 — Complete framed diagnostic bundle:375127bytes

Previous goal turn classified progress: prefix-only replay at2cf351e40.
Revalidated clean worktree. Implemented fixed-layout GKR binary codec: canonical
four-u32 extension elements, layer/round dimensions derived from trusted public
layout, no proof-controlled lengths. Exact20128bytes, decode/reencode matches
saved proof values. NPBND001 envelope carries four nonempty length-delimited
sections with exact consumption and a64MiB diagnostic transport cap.

Complete serialized bundle:15567prefix +20128GKR +1476weighted stacking
+337932WHIR +24framing =375127bytes. Compared with original398697byte native
internal fixture,23570bytes smaller. This is an actual binary measurement,
not the earlier field-only subtotal or a PQ128 claim. WHIR still dominates.

Bundle verifier extracts native sections, re-derives controls/full prefix log,
trace metadata and stacking layouts using native key-directed decoding; derives
GKR circuit from those controls and fixed DAG; decodes and verifies GKR FROM
THE BUNDLE; computes residual/binding from that verified proof; then verifies
native weighted sumcheck+WHIR. Parameterized public-context and handoff runners
so supplied decoded inputs are used instead of reading saved GKR/controls.
Legacy default handoff regression still passes.

Positive replay passes while original native proof AND saved GKR JSON are
unavailable (temporarily moved, restored in finally). Fresh-process saved-bundle
replay passes. Thirteen negative checks reject: six envelope/version/length
mutations, three GKR length/canonical-field mutations, and one same-shape payload
mutation in each of four sections. Final positive replay restores valid runtime
inputs after mutation tests. Fixed VK/DAG/profile remain verifier configuration.

Evidence:results/swirl-security-review/bundle-codec/proof.bin,logs,reports,pins.
Reproduce:swirl_bundle.py and swirl_bundle.py --verify-saved. No native source
changes this turn. Native verifier remains diagnostic test harness, prefix
profile excludes preprocessed AIRs, and no Lean codec/compiler/composition or
QROM theorem is claimed. This internal geometry fails300000 already at Ext4/
upstream diagnostic settings. Next prioritize root geometry and complete
stronger-security accounting, not more transport micro-optimization. Full
NEAR1Petagas, PQ128 and secure sub300000remain unachieved; goal stays active.

## 2026-10-17 — Matched split-root witness and public terminal GKR

Previous goal turn classified progress: framed internal bundle at5e1ef183f.
Revalidated clean worktree. Generated root-geometry proof over the preserved
internal child, with existing hash-table partition:16874live rows,16384+512
heights. Native debug/prove/verify passes; root231997bytes. Independently
recomputed common/cached commitments match the exact exported41matrices,
10063600base cells. Root prefix encodes/roundtrips at14292bytes.

Preserved root proof, DAG18196nodes, openings, layouts, accepted capture and
witness archive. Last two native captures (root verification and export replay)
match exactly. Raw source-matrix opening probe independently checks2995current/
rotated claims at native point; all pass. Archive23453666bytes,43file hashes
rechecked. Witness storage is NOT proof size. Native root run46.13s including
debug, commitment recomputation and exports; not a production benchmark.

Generalized fixture DAG input and witness-probe directory without changing
internal defaults. Initial capture-bound root GKR1288EF/20608field bytes passes
(component-only diagnostic). Then generated root opening-free prefix controls
using a keygen-only root-split key helper. Public controls/selectors exactly
match captured root; native prefix trace metadata/layouts match native export.
Root public-statement GKR also1288EF/20608bytes; independent public-only replay
passes with4257known slots and2603PCS coordinates. No witness openings read by
that replay. Internal public GKR and native prefix regressions plus clippy pass.

Root commitment layout is height2^20 with widths10+1, versus internal2^19 with
49+1. This is the concrete root geometry for next authenticated continuation;
do not reuse internal weights, keys, query schedules or WHIR proof. Root prefix
probe still uses full native proof to derive controls; prefix-only root replay
and root weighted WHIR integration remain next. No complete new root bundle
size inferred from component sums.

Evidence:root-split-witness/,root-split-dag-gkr/,root-split-public-gkr/ under
swirl-security-review. This is generic cached-VK recursive root geometry, not
production RootProver/full NEAR1Petagas. Upstream diagnostic security is not
PQ128; no new Lean correctness/composition theorem claimed. Goal stays active.

## 2026-10-17 — Complete root bundle and charged-GKR security screen

Previous comparison turn rechecked published sources and current artifacts;
no new protocol implementation was completed during that comparison. Resumed
pending root continuation work from authoritative logs and saved outputs.
Native root-specific arbitrary-weight stacking and WHIR generation passed:
884 stacking bytes,168268 WHIR bytes,18 rounds,11 matrix openings checked,
four WHIR negatives. Generalized root key/source/witness selection while
preserving internal defaults. Native clippy passed.

Complete root bundle is14292prefix+20608GKR+884stacking+168268WHIR+24framing
=204076bytes. Prefix-only key-directed replay, public GKR, residual derivation,
weighted sumcheck and WHIR all pass. Thirteen codec/payload negatives reject
while both original native proofs and saved root GKR JSON are unavailable.
Fresh-process saved-bundle replay passes; internal375127-byte bundle regression
also passes. Source snapshots/full native patch (including untracked prefix
module), logs and hash pins retained in root-split-continuation/ and
root-bundle-codec/. This is generic cached-VK root geometry at upstream Ext4
diagnostic settings, not production RootProver, PQ128 or full NEAR.

Added screen_swirl_root_bundle.py. It reproduces204076 baseline bytes with the
measured1288EF GKR replacement charged, removing2995old column claims. The296B
framing residual is calibrated to the measured bundle, NOT an independent
new typed census. Screens5790geometries each with cached work retained/free.
Conditional extension9/digest52,C1,Q2^128,zero grinding credit; each query term
independently receives half budget, other security losses omitted. Frozen
trace/GKR workload despite changed parameters is explicitly optimistic.

Best expected frontier sizes:408973.81bytes with cache retained;346015.20with
cached evaluation/binding granted free. Zero sub300000survivors. Both winners
use height18,logblowup9,fold3,terminal9,queries66/53/44. Expected frontier sizes
are not deterministic lower bounds; extension/hash and QROM compiler remain
uninstantiated. These results reject this frozen-workload sensitivity profile,
not all hash-based PQ128 designs. Complete diagnostic bundle is useful progress,
but next work must reduce authenticated verifier workload or change the PCS
architecture rather than treating diagnostic size as secure feasibility.

No new Lean codec/compiler/composition theorem. Full NEAR1Petagas/PQ128/secure
sub300000bytes/end-to-end correctness remain unachieved; goal stays active.

## 2026-10-17 — Root workload attribution changes optimization priority

Previous goal turn made progress: validated/pushed complete204076B root bundle
and charged-GKR sensitivity screen atb0bc06163. Revalidated clean worktree.
Added screen_swirl_root_workload.py joining actual41-matrix manifest to pinned
native AIR names (AIR39duplicates hash AIR14), checking widths and exact totals.
Common9670384cells: hash5085696(52.59%), initial openings1458176(15.08%),
symbolic evaluation786432(8.13%), final query evaluation737280(7.62%).
Cached393216cells remain separately authenticated.

Each counterfactual reoptimizes5790geometries under the previous conditional
extension9/digest52 query ledger, charging1288EF GKR and keeping fixed messages.
Free removed work has NO replacement proof/constraints charged; this is an
optimistic prioritization experiment, not an implemented protocol.

| Counterfactual | Best expected bytes |
| --- | ---: |
| Measured work |408973.81|
| Half hash work free |389641.81|
| All hash work free |368161.81|
| Initial openings and final query evaluation free |391789.81|
| Symbolic evaluation and cached work free |339571.20|
| Hash, symbolic evaluation and cached work all free |298759.20|
| All common cells /4, cache retained |338151.08|
| All common cells /8, cache retained |306975.08|
| All common cells /16, cache retained |282333.82|
| All common cells /2, cache free |307351.20|
| All common cells /4, cache free |279660.84|

Even eliminating all hash cost does not pass with the second cached source
retained. Simultaneously erasing hash/symbolic/cache work gives only1240.80B
headroom before omitted replacement costs. Thus standalone hash-AIR tuning is
not the next architectural priority. A fixed-key verifier with materially
smaller opening/evaluation work and no separately authenticated cached source
is a more relevant candidate; /4common with freecache has20339.16B headroom,
still before replacement costs, full security composition and real NEAR work.
These are conditional expected sizes, not lower bounds or security claims.

Source inspection reconfirms important recursion boundary: native
nearproof_root_split_witness decodes ORIGINAL internal native proof and invokes
VerifierSubCircuit::generate_proving_ctxs_base on it. The new external terminal
GKR replacement reduces root proof column claims, but DOES NOT remove that
inner symbolic-expression/cached trace. No circuit currently proves acceptance
of our compressed bundle. Next implementation must explicitly compile that
verifier, including public prefix/GKR/weighted PCS/transcript binding; do not
infer its trace size or recursive closure from the existing root fixture.
Preserve fixed-key binding and all public state links when specializing.

Evidence:root-workload-screen/report.json with source pins and all14scenarios.
No new Lean theorem; fullNEAR1Petagas/PQ128/secure sub300000B goal remains active.

## 2026-10-17 — Compile compressed-bundle GKR arithmetic and prove two identities

Previous goal turn progressed via measured workload attribution atd6e541ff7.
Revalidated clean worktree. Added compile_swirl_gkr_verifier.py: fixed-layout
Ext4 DAG with explicit proof coefficients, layer input claims, external initial
claim,437transcript challenge inputs and4257known input values. No honest proof
values are frozen into circuit constants. Endpoint/wiring tests are437output
residuals; output also includes the known-subtracted PCS claim and2603weights.
Constants and circuit wiring come from the verifier-owned layout.

Actual root public proof is replayed by an isolated clone of existing verifier
to capture authenticated challenge order (no global monkeypatch). Compiled DAG
matches all equality checks, every2603PCS weight and final residual. Four
mutations (initial claim, coefficient, layer input, challenge) produce a nonzero
check. A changed known input correctly leaves GKR checks unchanged but changes
the PCS residual, documenting its separate authentication obligation.

Initial sequential arithmetic:820866nodes, maxdepth13789. Grouped wiring
factors op(a,b) outside each operation-specific sum. Balanced sum compilation
reduces maxdepth to34 with820866nodes, including627955extension multiplications.
All parity/negative checks rerun successfully after balancing. Independent
reachability/acyclicity check finds782476reachable nodes; unused emitted nodes
are not a necessary cost. Counts are Ext4 operations, not base-field AIRcells,
proof bytes or a proven speedup. Both source versions/reports preserved.

Added SwirlGkrVerifierArithmetic.lean and package import. Two compiled theorems:
operation-grouped wiring preserves weighted gate evaluation; emitted quadratic
endpoint residual is equivalent to the endpoint sumcheck equality. Targeted
lake build passes; axiom reports contain only propext,Classical.choice,Quot.sound.
These are reusable algebraic identities, NOT a Python compiler refinement,
Fiat-Shamir/QROM theorem or full GKR/recursive soundness proof.

Transcript hash/challenge derivation, public-prefix validation, known input
coefficient derivation and weighted stacking/WHIR are still external. This is
an executable circuit component, not a generated recursive proof. Its substantial
arithmetic count means fixed layout alone must not be assumed to deliver the
required4xworkload reduction. Next reduce/evaluate the fixed wiring polynomial
cost and connect authenticated transcript/PCS interfaces before large proving.
Evidence:compiled-gkr-verifier/ circuit, reports, logs and pins. Full NEAR1Pgas,
PQ128, secure sub300000bytes and end-to-end Lean correctness remain open.

## 2026-10-17 — Shared Boolean wiring evaluation reduces GKR verifier arithmetic

Previous goal turn progressed with fixed GKR arithmetic circuit and two Lean
identities at8439488fe. Revalidated clean worktree. Added swirl_wiring_bdd.py:
trusted fixed wiring is a Boolean predicate over output,left,right indices.
Build shared reduced decision nodes; evaluate each via Shannon interpolation
at GKR points. Operation-specific wiring sums remain factored from op(a,b).
Equal subtrees share arithmetic; equal children skip their variable. Zero high
branches use (1-r)*low. No proof-selected wiring or challenges are introduced.

Measured14fixed variable orders. Grouping all input bits first is costly;
interleaving output/left/right bits high-to-low gives the lowest reachable
multiplication count among these candidates. Independent direct-wiring parity
passes168cases across four shapes, all14orders, zero/one/random Ext4 inputs.
The zero-bit/one-gate case is included. Full root compiled circuit matches all
437equality checks,2603PCSweights and finalresidual; four proof/claim/challenge
mutations reject and changed knowninput changes only the residual obligation.

Comparison uses reachable nodes, not unused emitted nodes:
- Previous balanced direct wiring:782476nodes,598514Ext4multiplications.
- Selected shared wiring:540713nodes,382848Ext4multiplications.
- Reductions30.90%nodes and36.03%multiplications; maxdepth34->105.
Emitted579107nodes include unused intermediate entries. Counts are NOT base-
field AIRcells, measured speedup or proofbytes. Default compiler mode is
preserved: its entire serialized node/check/output/input graph exactly matches
the previously saved circuit. Keep both modes pending recursive proof costs.

Added two Lean lemmas: Shannon interpolation identity and equal-child variable
elimination. Targeted lake build and axiom checks pass (only propext,
Classical.choice,Quot.sound). These do NOT prove decision-graph construction
matches the original wiring or establish complete compiler refinement. That
remaining correspondence needs structural induction plus precise coordinate
ordering and unique Boolean support; runtime parity is current evidence only.

New sources:swirl_wiring_bdd.py,check_swirl_wiring_bdd.py,
screen_swirl_wiring_orders.py; optional wiring_kind in existing compiler.
Artifacts:bdd-gkr-verifier/ graph,14ordercensuses,parity,comparison,Leanlogs,pins.
Transcript/prefix/known-input derivation/PCS remain external. No recursive proof,
PQ128, secure sub300000B, full NEAR1Petagas or end-to-end Lean claim.

## 2026-10-17 — Ordered decision evaluation theorem and exact root wiring support

Previous goal turn progressed with shared wiring compiler at4bf903484.
Revalidated clean worktree. Added SwirlDecisionGraph.lean: indexed ordered
decision views have constant leaves, binary branches and explicit variable
skips. Defined Boolean evaluation, field Horner evaluation and dense Boolean
multilinear extension in the declared coordinate order.

Three theorems compile: constant Boolean-table extension is constant; every
ordered decision view evaluates to the multilinear extension of its own Boolean
function; separately established Boolean support correspondence transfers to
all field points. This is structural induction over branches/skip/terminals,
not merely an identity at one node or a test on Boolean inputs. Targeted lake
build passes, package import added; axioms only propext,Classical.choice,Quot.sound.
The tuple/function eta normalization needed explicit application of existing
Shannon identities instead of grind treating higher-order forms syntactically.

Added independent check_swirl_bdd_support.py. It validates variable permutation,
terminals, acyclic child indices and strictly ordered variables. Counts accepted
Boolean assignments using powers of two for skipped variables. Checks every
expected unique gate coordinate is accepted and count equals support size;
finite containment plus equal cardinality rules out extra accepted coordinates.
This checks the entire Boolean support without enumerating the huge cube.

All69operation/layer graphs match81062gate coordinates for selected root
wiring order.358negatives reject: empty/full substitution, removed/extra support,
same-cardinality replacement, self-referential node, repeated variable order.
The same-cardinality mutation exercises membership checks beyond the count.
Checker emits graph hashes per layer/operation; source/log pins preserved.

Remaining formal boundary is explicit: Python builder/checker and graph-to-
ordered-view unfolding are not yet refined in Lean. The field theorem assumes
that unfolding/support connection, rather than silently asserting the emitted
Python artifact is certified. No new proof-size or security claim. Prior
540713reachable-node arithmetic circuit and original bundle remain unchanged.
Transcript/prefix/PCS interfaces, recursive closure, PQ128 and full NEAR1Petagas
remain open. Evidence:bdd-support/; goal stays active.

## 2026-10-17 — Exact GKR transcript census and immutable fixed-key preparation

Previous goal turn progressed on structural decision theorem/support checker
atad0b4fb76. Revalidated clean worktree. Added measure_swirl_gkr_transcript.py:
cloned verifier/transcript functions capture exact framed SHA384 preimages
without global monkeypatching. Independently reconstructed bytes hash identically
to existing hash_parts. Replayed root public GKR obligation equals uninstrumented
verifier. Preserved all2188preimages/digests and437challenge records.

14341SHA384compression blocks total inside g.verify:9968hash its fixed-layout
JSON,4373are dynamic. All2188preimages are distinct.437draw requests consume
437squeeze blocks and reject114words in this particular proof. Every draw has
request/squeeze/ratchet/draw-result hashes; each costs2compression blocks.
437proof commits also each cost2blocks. Rejection counts are instance-specific,
not a universal fixed circuit schedule or a security guarantee.

Additional raw SHA384 bindings in existing public driver:
- native prefix Debug log189402bytes ->1480blocks;
- statement-description JSON35160bytes ->275blocks;
- continuation-binding JSON93025bytes ->727blocks.
All three digest values independently match saved statement/binding artifacts.
Thus6855dynamic SHA384blocks remain after fixed-layout precomputation, BEFORE
native prefix and WHIR Poseidon hashing or arithmetic circuit costs. Do not
infer full recursive size from prior540713arithmetic-node count. Existing
Debug/JSON encodings are diagnostic boundaries requiring explicit treatment.

Added swirl_fixed_gkr_verifier.prepare: computes existing layout digest once,
deep-freezes layout mappings/sequences, returns verifier with no caller layout
or digest argument. This is trusted key preparation, not a new transcript.
Prepared replay matches every dynamic preimage byte-for-byte (original event
list excluding only fixed-layout hash), and returns same PCS obligation.
Mutating caller's original layout after preparation cannot affect frozen key;
changed claim rejects. Preparation is an available dedicated entry point;
existing bundle driver remains unchanged, so no bundle-speedup claim is made.

The dynamic cost is material even after removing all fixed hashing. Next
address typed recursive transcript/binding representation and hash circuit
cost jointly with arithmetic; any replacement of Debug/JSON bytes or hash
schedule is a versioned protocol change requiring fresh GKR/PCS proofs, not a
lossless transport optimization. Current proof remains204076B at diagnostic
settings. No new Lean/hash-security/composition theorem, PQ128 or full NEAR
claim. Evidence:gkr-transcript-census/; full goal remains active.

## 2026-10-17 — Binary transcript v2 complete root bundle

Previous goal turn progressed via exact transcript census/fixed-key preparation
at0b6ba9dfd. Revalidated clean worktree. Introduced separate NPBND002 diagnostic
bundle. Native prefix remains canonical NPREF001; terminal GKR statement is
framed SHA384(tag=nearproof-binary-prefix-gkr-v2,prefixbytes). Continuation digest
is framed SHA384(tag=nearproof-binary-gkr-to-whir-v2,statementdigest,GKRbinary).
No Debug log or decimal JSON is hashed by v2; later removed the unused Debug-log
read from its public context and verifier path. Existing v1 behavior retained.

Security interface: native prefix is decoded/shape-checked and its sumcheck
prefix verified under fixed native VK before derived controls/known weights
are used. GKR begin still binds fixed layout and output claim. New binary
statement binds exact prefix; known values must remain deterministically
derived by trusted native prefix replay, never caller-provided replacement
controls. This is a changed Fiat-Shamir transcript, not lossless v1 transport.
No QROM or full security theorem is inferred from these bindings.

Fresh root GKR proves/verifies1288EF,20608bytes. Generated new root weighted
sumcheck/WHIR using its new residual and binding:884stacking,168268WHIRbytes,
18rounds,11matrixopenings checked, native run25.71s including recommit/checks
(not benchmark), four WHIR negatives reject. Source native code unchanged.
Complete v2 bundle:14292prefix+20608GKR+884stacking+168268WHIR+24framing
=204076bytes. Full verification passes while original root/internal proofs and
saved v2 GKRJSON are temporarily unavailable. Fifteen negatives reject: prior
13codec/payload checks plus both relabelled cross-version directions. Fresh
process replay passes; both v1 root204076 and internal375127 regressions pass.

Exact v2 hash census replays public GKR from binary bundle (no saved GKRJSON
needed):prefixbinding14362framed bytes/113SHA384blocks, continuationbinding
20735bytes/163blocks. Dynamic GKR remains4373blocks; total4649vs6855v1,
saving2206blocks (32.18%).437draws use437squeezes and reject103words for this
instance. Fixed-layout hash may be precomputed as before. Native prefix/WHIR
hashes are excluded; no total-recursive cost, proving speed or PQ128 claim.
Proof bytes unchanged. Census first attempted reading GKRJSON during the
intentional missing-file test; corrected it to decode the already-written
bundle, then replay passed without that dependency.

Reproduce:prove_swirl_binary_root.py; then native test
NEARPROOF_ROOT_SPLIT=1 NEARPROOF_WITNESS_DIR=/tmp/nearproof-root-split-witness
NEARPROOF_SOURCE_PROOF=/tmp/nearproof-root-split-witness/native.proof
NEARPROOF_GKR_BINDING=/tmp/nearproof-prefix-gkr-binding.bin
NEARPROOF_WEIGHTED_WHIR=1 RAYON_NUM_THREADS=4 cargo test --locked --profile fast
-p openvm-recursion-circuit tests::nearproof_weighted_native_sumcheck -- --exact
--nocapture. Preserve its stacking/WHIR outputs in binary-root-gkr/; run
swirl_binary_root_bundle.py, --verify-saved, measure_swirl_binary_transcript.py.

Evidence:binary-root-gkr/,binary-root-bundle/. New public_context/prepare options
are opt-in; v1 defaults preserved. No new Lean codec/transcript/composition
proof, circuit proving bundle acceptance, PQ128 or full NEAR1Petagas. The next
remaining hash cost is mostly the per-round transcript itself, not JSON;
any schedule/hash redesign needs separate analysis and new proofs. Goal active.
Final fresh replay after removal of the unused Debug-log read also passed;
log preserved as binary-root-bundle/fresh-no-debug.log.gz.

## 2026-10-17 — Routed hash graph supplies actual arithmetic challenge inputs

Previous goal turn progressed with binary transcript v2 atf3a97d96b. Revalidated
clean worktree. Added swirl_gkr_hash_graph.py: explicit typed input/literal/prior-
hash references for init, proof commit, request, squeeze, ratchet and draw-result.
Fixed layout digest is trusted key material. Proof rows/inputs are canonically
encoded; endpoint/gamma challenge names match the optimized arithmetic circuit.
Sampler loops over digest words in little-endian order, rejects words>=2P,
stops at the fourth accepted word, and retains bounded multiblock/exhaustion
behavior. Serialized graph metadata is NOT a source of trusted challenges;
derive returns its recomputed challenges after route/digest checks.

Independent operational replay produces2187hash nodes/4373SHA384blocks and
437challenges identical to existing g.verify. All103rejected words accounted
for. Saved optimized circuit is evaluated with fresh v2 proof/known inputs and
these derived challenges:437equalities,2603PCSweights and residual all match.
Six graph negatives reject wrong digest, parent, domain tag, payload route,
truncation and extra node. SHA384 is recomputed by host in this checker; this
is a concrete transcript-to-arithmetic bridge, NOT a recursive hash proof.

Reused existing SHA384TranscriptDraw.lean rather than duplicating rejection
semantics. Generated ActualScans.lean with437digest-to-word equality theorems
and437scan value/rejection/done theorems for the actual squeezed digests.
All874concrete kernel checks pass. Initial decide on the well-founded scan
function did not reduce; using its defining equations via simp then arithmetic
reduction passed. Digest examples use decide, scan examples use simp; no
native_decide or sorry. Sampled axiom print: digest has none, scan uses
propext/Quot.sound. Target dependency build also passes.

These are concrete fixture theorems, not874new general protocol lemmas.
No SHA384 compression truth is assumed to follow from decoding a digest. Hash
AIR, byte/range/scan constraints and graph routing still need integration into
the recursive circuit; prefix/statement binding and weighted native PCS remain
external interfaces. Existing generic operational scan range/length/preimage
lemmas remain available for that refinement. No compiler, QROM, PQ128 or full
NEAR1Petagas claim; full goal stays active.

Evidence:gkr-hash-graph/ graph,ActualScans.lean,parity/Leanlogs,reports,pins.
Reproduce check_swirl_gkr_hash_graph.py then lake env lean on ActualScans.lean.

## 2026-10-17 — Existing SHA384 AIR fails workload gate; first Binius64 hash proof

Previous goal turn progressed with routed transcript/arithmetic and actual Lean
scan checks atb0112c35e. Revalidated clean worktree. Reconstructed measured
64-block nibble AIR source+aux cells from physical branches:27939408, including
private boundary. Formula exactly reproduces that count. Applied frozen widths
to the4649dynamic v2hash blocks, preserving schedule64/round80/endpoint1 and
boundary1rows per compression. No full trace generated.

Conditional5790geometry screen per scenario (same extension9/digest52,C1,Q2^128,
zero grinding credit, independent half-budget query terms):
- Unpadded source only, all aux/fixed/routing free:271524845cells,737156.09bytes.
- Unpadded source+aux, fixed/routing free:1227731165cells,1170366.35bytes.
- Frozen padded tables:1898353936cells,1406206.35bytes.
All other verifier trace/cached work omitted; prior fixed messages retained as
accounting template. No survivors. Widths/multiplicity/domain validity at this
scale unestablished, expected frontier not a deterministic bound. This rejects
straight integration of the CURRENT nibble AIR under the conditional model,
not every SHA384 circuit. Avoided an expensive doomed large proving run.

Pinned fresh Binius64 checkout4428e759dd27956bd5b9ae5025d67eb8ccc1accf. Inspected
word-oriented SHA512 compression gadget and CLI; no CodeGraph/AGENTS present.
Added diagnostic SHA384 adapter using standard SHA384 IV, existing SHA512
padding/compression, first6outputwords. Existing SHA512 fixed helper delegates
to same parameterized-state implementation. Added nearproof_sha384 example
using independent sha2::Sha384 for expected digest. Local changes saved as
patch/source snapshots, not pushed upstream. Upstream omits Cargo.lock; generated
and preserved lock, then release build --locked passed (Rust1.98.1,nativeCPU,
4buildworkers;53.62s compile time, not proving benchmark).

Reconstructed exact187-byte first GKR commit preimage from routed graph;
hashlib SHA384 matches saved digest539a7926...e9e93477. Two-block circuit:
5520gates,2276committed64-bit words,1831AND,451ZEROconstraints. Generated proof
payload61648B; CLIserializedfile61684B. Public inout30words/240B external to
proof file; fixed circuit/constants also external. Fresh process verifies.
Changedmessage rejects in verifier; changedproof rejects Merkle authentication.
Changeddigest is rejected EARLIER by witness circuit assertion, not counted as
an independent proof-verifier negative. Padding0/111/112/127/128 and unchanged
SHA512187-byte regression all prove/verify. CLI randommessage utility disallows
empty inputs; empty-file fixture directly exercises zero-length circuit instead.

Pinned verifier sets SECURITY_BITS=96; FRI query function explicitly excludes
folding and other protocol losses. Default Merkle suiteSHA256. Therefore NOT
PQ128 or even a full96-bit security audit. Word counts and oldBabyBear cells
are different units, and no matched speedup or complete-state proof comparison
is claimed. This establishes a concrete alternative hash gadget, not a full
backend migration, transcript routing circuit or Lean refinement. Next test a
larger connected hash workload and quantify full parameter/security obligations
before adopting it. No new Lean theorem or goal completion.

Evidence:sha384-recursion-screen/ and binius-sha384/ reports/proof/message/logs,
lockfile,upstream/sourcepins,patch. Reproduce screen_swirl_sha384_work.py;
apply saved patch to pinned Binius64,restore lock,build -p binius-examples with
RUSTFLAGS='-C target-cpu=native',then run check_binius_sha384.py.

## 2026-10-17 — Connected Binius hash graph and concrete scaling limit

Previous goal turn produced evidence changing the next action: the full graph
failed at setup. Revalidated source and terminal logs; did not restart a live
process. This turn tested a supported intermediate workload and preserved the
source patch, runner, proofs, logs, lockfile and pinned source snapshots.

Added a fixed-graph example to the pinned Binius64 checkout (same4428e759 pin).
Every hash-parent reference uses the parent's computed digest wires, with
framing lengths/tags/literals fixed in the verifier key. Input bytes are public
word wires. Squeeze digests and final seed are public outputs. Host sha2 is the
independent output oracle; Python reconstructs every frame and checks its saved
digest and compression-block count before export. No unconstrained intermediate
digest inputs. Graph shape is NOT an untrusted runtime proof parameter.

Measured results at unchanged diagnostic settings:
- 8draws:42hashes,83compressionblocks;182720Bpayload/182756Bserialized;
  117public words/936B external. Fresh verification passes.
- 64draws:322hashes,643compressionblocks;280480Bpayload/280516Bserialized;
  833public words/6664B external. Fresh verification passes. Changedpublicinput
  rejects in proof verification; changedproof rejects Merkle authentication.
- Full437draws:2187hashes,4373blocks,5650public words/45200B external.
  Setup panics: wiring needs67bits, maximum63. NO full proof or size result.
  Observed process exit101,12.20s wall,5741388KiB peakRSS; diagnostic resource
  observations, not a comparative throughput benchmark.

Source explains the failure: shift/wiring.rs packs operand bits,18shift bits,
word index and constraint index into u64; SparseBitVector independently requires
log_len<64. Removing the assertion alone would truncate/alias addresses.
The implementation needs a wider/split sparse address representation or a
smaller circuit layout. Fragmenting into independent proofs would additionally
require authenticated links and another compression layer; do not assume the
component sizes amortize. No backend address modification made in this turn.

Scope remains restricted: pinned SECURITY_BITS=96 covers query parameterization,
not a complete security proof; default SHA256 suite, no PQ128 claim. The CLI
fresh verifier derives public reference outputs and evaluates a witness; this
is a diagnostic harness, not a production public-statement verifier API. Fixed
observed squeeze schedule does not constrain arbitrary rejection-sampling
control flow. Field sampling, GKR arithmetic, native prefix and PCS verification,
full NEAR state transition and Lean circuit refinement are not covered.

Decision: connected hash proving is real, but 64draws already consume most of
300000B before stronger security and other verifier work. Keep Binius as an
alternative, not evidence that the final target fits. Next investigate whether
wider sparse addresses are a small semantics-preserving backend repair and
measure the complete graph before deciding on integration. In parallel design
terms, the leading integrated route remains specialized GKR/WHIR recursion;
no new broad Lean campaign is justified by these component results alone.

Reproduction: apply binius-hash-graph/binius.patch to pinned checkout, restore
archived Cargo.lock, build release binius-examples with nativeCPU and four build
workers, then run check_binius_hash_graph.py. --reuse-tmp imports original proof
runs but always reruns fresh verification and negative checks. Full run is
expected to fail setup on the pinned implementation. make pin-check passes.
Evidence in results/swirl-security-review/binius-hash-graph/. No goal completion.

## 2026-10-17 — Wider Binius wiring executes full fixed transcript; size gate fails

Previous goal turn made progress: connected graph proofs and the concrete
63-bit backend limit were committed/pushed at9abcd1e25. Revalidated clean
research worktree and pinned external checkout before this experiment.

Changed only sparse-address storage/packing from u64 to u128 in Binius math
SparseBitVector and verifier shift WiringInfo; bounds now require log_len<128.
Chunk extraction still uses at most16bits per tensor, with the wide shift before
conversion to usize. Pair cancellation, operand order and field arithmetic are
unchanged. No cryptographic parameter changed. Preserved patch as an incremental
patch on top of binius-hash-graph/binius.patch, not an upstream modification.

Tests:12sparse tests pass, including independent per-bit-indicator evaluation
at64/67/96/127variables and cancellation/distinctness of high addresses.
Four wiring tests pass, including explicit67-bit address preservation and
existing contracted-tensor parity. Replaced the old64-bit expected-panic test
because that input is now supported. An initial mechanical edit accidentally
changed RNG seed method names; corrected before successful tests/build. Existing
64draw proof generated with u64 verifies under the widened backend. These are
implementation checks, not a Lean refinement or universal equivalence theorem.

Full fixed graph now proves and verifies:437draws,2187hashcalls,
4373SHA384compressionblocks,4583333hiddenwords,3715437ANDconstraints.
Payload399696B; serializedproof399732B; public inout5650words/45200B external.
Observed prove command (including circuit build and verification)16.88s wall,
6588292KiB peakRSS; four Rayonthreads, nativeCPU release. Not a matched backend
benchmark. Fresh process verification and changedinput/changedproof rejection
are recorded by check_binius_wide_graph.py (report produced only after all pass).

Decision: this resolves the implementation blocker and rejects this unchanged
full fixed-hash-graph layout as the final sub300000B proof: the component alone
is99732B over target, before remaining verifier components or PQ128 parameters.
It does not rule out Binius with a different transcript/layout or an additional
compression layer. Avoid widening the experiment to the full recursive verifier
without a concrete size-reducing design. The leading integrated GKR/WHIR route
still needs transcript/hash co-design and complete quantum soundness accounting.

Limitations unchanged: SECURITY_BITS=96 is only diagnostic query parameterization;
SHA256 default Merkle suite. Fixed squeeze schedule, no sampler/arithmetic/
prefix/PCS verifier, no full NEAR1Pgas or Lean circuit refinement. Full graph
means the GKR hash graph only, not a full verifier. Archived report/sourcepatch/
sourcepins/proofs/logs under binius-wide-graph. Reproduction script defaults to
new proof generation; --reuse-tmp imports original proof and reruns verification
and negatives. make pin-check passes. Goal remains unachieved.

## 2026-10-17 — Rate sweep corrects default-only size conclusion

Previous goal turn progressed atb3077bc1e: widened address representation and
full fixed hash graph proof. Revalidated worktree and inspected upstream code
rate selection before further integration. The prior rejection applies to the
unchanged rate1/2 profile, not to the graph at every code rate.

Proved identical437draw/2187hash/4373compressionblock graph with unchanged
SECURITY_BITS=96, SHA256 suite and u128-address patch:
- log_inverse_rate1:232queries,399696Bpayload/399732Bserialized.
- log_inverse_rate2:142queries,290704Bpayload/290740Bserialized.
- log_inverse_rate3:269008Bpayload/269044Bserialized.
Public inout45200B remains external: rate3 totals314244B with those bytes.
This does not include verifier-key transport or any missing verifier relation.
Code-rate tuning materially improves proof size without lowering the configured
query-security target. calculate_n_test_queries uses ceil(96/-log2((1+rate)/2));
this is explicitly query-phase-only accounting, not full96-bit or PQ128 security.

Added opt-in NEARPROOF_SIZE_CENSUS using upstream SizeTrackingChannel and an
IOP verifier run on zero placeholders, without accepting that synthetic run as
verification. Counters distinguish ordinary algebra messages, Merkle roots and
authentication, and opened/full-vector field values. Actual saved proofs are
then separately verified. For rate1,9648Balgebra+203680BMerkle+186368Bvalues
exactly reproduce399696Bpayload. For rate2,9648+155616+125440=290704B.
Thus current cost is dominated by the PCS, not the algebra messages. The runner
asserts census total equals actual serialized size minus36B for all three rates.
A synthetic size census is neither a proof nor a security calculation.

Reproduction: apply hash-graph patch, wide-address patch, then census.patch;
restore archived lockfile and release-build examples with nativeCPU/fourworkers.
check_binius_rate_sweep.py defaults to fresh generation, or --reuse-tmp imports
the observed runs and always fresh-verifies allthree and checks changed public
input and changedproof rejection for rate3. Report is written only on success.
Source snapshots, patches, proofs, exact logs and run resource observations are
under results/swirl-security-review/binius-rate-sweep. make pin-check passes.

Decision: retain rate-tuned Binius as a component candidate; do not infer it
meets the final target. Next investigate PCS scheduling and whether a single
combined verifier circuit can keep intermediate digest outputs private, while
charging the added arithmetic/sampler cost and stronger security requirements.
No full NEAR1Pgas, sampler/GKR/prefix/PCS verification circuit, PQ128 certificate,
or Lean implementation refinement has been established by this sweep.

## 2026-10-17 — Stronger query-budget screen fails fixed Binius graph size gate

Previous goal turn progressed at84cb84ac3 with measured rate tuning and exact
byte census. Revalidated clean research branch and pinned external sources.
Before adding sampler/arithmetic circuits, extended the diagnostic census to
30combinations: query-only budgets96/128/160/256/272bits, inverse-rate logs1..6.
Each candidate uses the same actual oracle specs and native optimized BaseFold
schedule selection; a synthetic IOP/PCS verifier run counts messages without
claiming synthetic acceptance. No new stronger-parameter proof generated.
Original saved rate3 proof independently verifies after the census.

All30query counts are independently checked with exact Fraction arithmetic:
((1+2^-r)/2)^q <=2^-b and the inequality fails at q-1. All three96-bit measured
profiles match every saved byte category and actual serialized size. The query
formula is the pinned upstream unique-decoding query-phase bound. It excludes
FRI folding and other protocols; these sensitivity points are NOT labels for
quantum security, and no QROM conversion is asserted.

Best serialized sizes over the six rates (all select rate1/8):
query budget96:116queries,269044B; with publicio314244B.
query budget128:155queries,341716B; with publicio386916B.
query budget160:193queries,411028B; with publicio456228B.
query budget256:309queries,612436B; with publicio657636B.
query budget272:328queries,643444B; with publicio688644B.
Algebra messages remain9648B. At128budget Merkle176768B and openedvalues155264B
sum with algebra to341680Bpayload, plus36BCLIenvelope. Fixed32-byte Merkle
digests and128-bit binary field are unchanged in every modeled row; no costs
of stronger hash/field instantiations or remaining verifier circuit are charged.

Decision: for this fixed graph and tested schedules, simply making public
intermediates private cannot meet the size gate at even128-bit QUERY budget:
proof bytes alone exceed300000 by41716. This is a conditional cost finding,
not an impossibility theorem for Binius or PQ128. Stop adding whole-verifier
circuitry to this profile until a smaller commitment/opening layout or smaller
circuit has a concrete budget. Rate tuning alone has been tested through1/64.
Next useful work is reducing the authenticated opening cost or transcript
workload, with complete security accounting kept separate from size sensitivity.

Reproduce screen_binius_query_budget.py after applying prior hashgraph,
wide-address,census patches and new parameter-screen.patch, then release-build.
Evidence in results/swirl-security-review/binius-query-screen includes all30rows,
exact-check runner, native log, incremental patch and source snapshots. make
pin-check passes. No Lean theorem changed, no full NEAR1Pgas proof/PQ128/end-to-end
correctness achieved; goal remains active.

## 2026-10-17 — Fused GKR transcript candidate reduces actual hash circuit

Previous goal turn progressed at9d0cb04c3 by rejecting the unchanged fixedgraph
under stronger query-only budgets. Revalidated clean branch and inspected
actual transcript routes: each usual commit/draw performs five hash calls.
No byte-preserving elimination was established. Instead implemented a NEW,
separately versioned GKR transcript candidate, nearproof-fused-terminal-gkr-v3.
Existing v2 bundle, transcript class and verifier remain untouched.

Candidate binds statement, fixed layout digest and claim in one initial hash.
Exactly one pending gkr-vector commit is allowed before a draw. A draw hash
frames profile, previous seed, commit label/payload, draw label, round index,
count, coefficient count and retry counter. The last squeeze digest becomes
the next seed. Uses existing rejection threshold and little-endian word scan;
no modulo-only fallback. Retries bind explicit counters; exhaustion rolls back
graph/input recording and preserves seed/pending message. Operational forced
retry, rollback, schedule and shape checks pass. These are not a Fiat-Shamir
security proof. Prior generic transcript security cannot simply be inherited.

Loaded an isolated copy of the existing GKR arithmetic module with new profile
and begin function, avoiding mutation of baseline module globals. Generated a
fresh native-kernel GKR proof for the same root layout/statement/claim. Verify
matches prover obligation; known-input subtraction/residual matches full witness.
Five negatives cover statement/coefficient/profile changes, old verifier and a
relabelled old proof. Native PCS continuation is NOT regenerated or claimed.
Candidate proof and routed graph saved under fused-gkr-candidate/.

Actual candidate graph:437draws,438hashcalls,1313SHA384compressionblocks versus
2187calls/4373blocks previously. Each typical combined frame costs3compression
blocks, so savings are not inferred from call count alone. Generated Binius
circuit with the existing trustedgraph harness and unchanged pinned patches:
1460229hiddenwords,1180068ANDconstraints. At inverse-rate log3 and diagnostic
96-bit QUERY setting, payload223488B, serialized223524B. Freshverify passes;
changedpublicinput rejects in verifier, changedproof rejects Merkle authentication.
Public inout5644words/45152B external (all squeeze outputs and final digest;
final is already a squeeze), combined diagnostic transport268676B. This remains
only a hash-graph component; not a full secure proof below300000B.

Repeated30case native byte census, with exact rational query sufficiency and
minimality checks. Generated payload matches its census. At128-bit QUERY budget,
best rate1/8 estimate283716B before publicio, or328868B with publicio. Hash/field
widths unchanged. No full/PQ128 soundness upgrade, no arbitrary sampler circuit,
GKR arithmetic circuit, native prefix/PCS verifier or full NEAR1Pgas proved.
No new Lean theorem or implementation refinement established in this turn.

Decision: retain the fused transcript as a candidate because both fresh GKR
and an actual smaller hash proof exist. Do not adopt it in production/v2 or call
it PQ128. Next establish its formal operational/framing interfaces and evaluate
a combined sampler/arithmetic circuit budget, keeping all opening obligations
and quantum Fiat-Shamir losses explicit. Candidate size margin is still narrow
at128query budget and not evidence that a complete verifier fits.

Reproduce prove_fused_gkr_candidate.py, check_fused_transcript_edges.py,
check_fused_binius_graph.py (latter --reuse-tmp imports observed proof but reruns
freshverify/negatives). Binius uses previous hashgraph/wide-address/census/query
screen patches and lockfile; no further upstream source change. Logs, proofs,
graphs and30row report under fused-gkr-candidate/ and fused-binius-graph/.
make pin-check passes. Full goal remains active and unachieved.

## 2026-10-17 — Formal fused-transcript operational and framing interface

Previous goal turn progressed at27b4b4e0b with a fresh separately versioned GKR
and smaller actual hash circuit. Revalidated clean research worktree. Added
NearCompression/FusedGKRTranscript.lean, importing existing SHA384 sampler and
framing decoder results rather than duplicating those foundations.

Generic kernel-checked results:
- Framing injectivity: equal canonical preimages imply equal seed, payload,
  round and retry counter. Explicit frame-fit and u64 counter bounds required;
  this is byte-encoding injectivity, NOT hash collision resistance.
- Bounded retry-loop specification: accepted result has exactly needed canonical
  field values, counter<blocks<=counter+fuel, a48-byte nextseed equal to the
  actual last consumed block. Retries use the SAME oldseed/payload; onlycounter
  changes, matching the new Python candidate rather than old ratchet semantics.
- Public draw specification specializes to4coefficients and a positive bounded
  blockcount, with the pendingpayload tied to the final hash preimage.
- Failure preserves entire modeled state (seed,round,pending), success advances
  round once and clears pending, doublecommit rejects, absentcommit cannotdraw.

Hash remains an arbitrary function parameter. No hash uniformity, collision
resistance, Fiat-Shamir/QROM, recursive soundness or SHA implementation theorem
is asserted. Model covers operational state, not Python's diagnostic graph
recording. Frame-fit bounds remain explicit premises. Initialization's layout/
statement binding and compiler implementation refinement remain separate work.

Generated concrete first/second/last frames from the actual candidate artifact
(indices0,1,436). Kernel checks exact byte framing, little-endian digest decoding
and full one-block scan result against Python. These are three concrete boundary
checks, not a universal Python/Rust equivalence proof. Literal byte constants
replace opaque UTF8 conversion in the Lean model to permit kernel reduction.
Scanner proofs use existing recursion equations, not native_decide.

Targeted lake build NearCompression.FusedGKRTranscript succeeds. Axiom output
for generic results and concrete frame/scan results contains only standard
propext/Classical.choice/Quot.sound as applicable; no sorryAx or native-decision
axiom. check_fused_lean_parity.py regenerates fixtures, compiles and checks output.
Evidence under results/swirl-security-review/fused-transcript-lean; make pin-check
passes. Next connect constrained hash output/scan relations to arithmetic
challenge inputs and budget their combined circuit, without treating these
operational lemmas as cryptographic security. No full NEAR1Pgas/PQ128/end-to-end
Lean correctness completion; goal remains active.

## 2026-10-17 — Constrain fused digest-to-challenge sampling in Binius

Previous goal turn progressed at360d23f45 with formal transcript interfaces.
Revalidated research tree and pinned external checkout. Added opt-in
--sample-challenges to the fixedgraph Binius example; default graph mode retains
its previous behavior and the old hash-only proof independently still verifies.

For each squeeze digest, derive12zero-extended little-endian u32 words from the
computed SHA384 wires. Unsigned comparisons enforce word<2P; conditional
subtraction implements moduloP on accepted words. A capped counter and selected
output slots retain the first4accepted words. Compare flags are MSB booleans;
select normalizes them before increment, avoiding undefined low bits. Assert
final count4. Challenge outputs are constrained public words, not unconstrained
witness digests. Only final seed remains a public digest. All437derived outputs
are independently compared with the fresh GKR graph values by the runner.

Scope is intentionally explicit: fixed one-block-per-draw schedule. Build rejects
multi-block draw metadata; circuit rejects digest inputs with fewer than4accepted
words. It does not yet implement variable retries or claim completeness for
all valid transcripts. The hashgraph remains verifier-key data. GKR arithmetic,
nativeprefix/PCS continuation and full NEAR relations are still absent.

Sampler gadget test passes140vectors: prime/threshold boundaries, insufficient
acceptedwords, wrongoutput, all9possible placements of four consecutive accepted
words,128deterministicrandomvectors. This is frontend circuit evaluation testing,
not a cryptographic proof-verifier negative. Wholegraph prove/freshverify passes;
changedpublicinput rejects in proofverification and changedproof rejects Merkle.

Measured1313hashblocks plus samplers:1563418hiddenwords,1251352ANDconstraints,
31464binary-multiplicationconstraints. At rate1/8 diagnostic96-querybudget,
payload230208B/serialized230244B, +6720B relative to hashonly. Publicio4776words/
38208B, diagnostic total268452B. Native30case queryscreen repeats with exact
rational query checks; best128-querybudget estimate290436B beforepublicio,
328644B including it. This is not a full128-bit/PQ128 parameterization; field,
hash and omitted soundness terms unchanged. Candidate has little size margin
for the still-missing arithmetic and stronger-security overhead.

Added SHA384ScanFilter.lean: generic operational scan values equal
filterMap(acceptWord).take(needed), and done iff at leastneeded words accepted.
Targeted build passes; axiom output onlypropext/Quot.sound, no sorry/nativeaxiom.
These connect the host reference to the existing formal scan model; they do NOT
prove the Rust comparator/select circuit implements that model. That refinement
and multi-block circuit completeness remain explicit obligations.

Artifacts under sampled-fused-graph include incremental sampler.patch, source
snapshot, proof, tests/logs,30case report and legacy regression. Reproduce after
prior Binius patches/lock using check_sampled_fused_graph.py. During harness
creation an inherited output path initially targeted the earlier evidence dir;
new artifacts were separated, original committed evidence restored, path fixed,
and verification/negatives rerun. Earlier evidence remains byte-identical.
make pin-check passes. No full NEAR1Pgas/PQ128/end-to-end proof achieved.

## 2026-10-17 — Canonical BabyBear word multiplication baseline

Previous goal turn progressed at7653dc054 by constraining sampled challenges.
Revalidated clean research tree and pinned Binius checkout. Next integration
obligation is the GKR verifier's prime-field/extension-field arithmetic inside
a binary-word circuit. Added an isolated canonical base-field multiplication
example, not a claim that the full arithmetic verifier is compiled.

Relation: a,b,q,r<P withP=2013265921, a*b=q*P+r. Both products use Binius's
full128-bit integer multiplication; highwords assertedzero. Addition checks
only the most-significant carry bit for overflow (carry wire also records
internal carries). Lowword product equals reconstructed quotientproduct+remainder.
The private quotient is supplied by host computation but fully constrained.
Public a,b,r are not baked into the key. Canonical q is sufficient for these
canonical a,b products; no unchecked integer/mod2^64 equality substitutes for
field reduction. Four range constraints prevent noncanonical representatives.

One product compiles to15gates,10privatewords,8ZERO/5AND/2IMULconstraints,
3publicinoutwords and3constants.64independent products reproduce exactlinear
counts:640privatewords,512ZERO,320AND,128IMUL;192publicwords/1536B external.
Actual rate1/8 diagnostic proof:185808Bpayload/185844Bserialized. Census exact:
algebra25584B,Merkle90784B,openedvalues69440B. Freshverification passes;
changedCANONICAL publicinput rejects in proofverifier, changedproof rejects
Merkle authentication. Initial bitflip negative crossedP and was correctly
rejected by witness rangecheck; replaced with decrement to exercise the actual
proofverifier and do not count that early failure as cryptographic evidence.

Gadget tests cover240assignments:36boundaryproducts and corresponding wrong
remainders/quotients, noncanonical representations, wraparound attempt, and128
random canonical products. Targeted tests pass. New WordModularProduct.lean
proves canonical integer quotient/remainder identity gives field product and
composes explicit highword/carry equations into that identity. Axiom output
onlypropext/Quot.sound, no sorry/nativeaxiom. This is a conditional mathematical
interface, NOT a Rust/frontend refinement proof.

Decision: use measured relation as a baseline for Ext4 lowering and shared
rangechecks. Do not extrapolate standalone proof bytes additively or treat
privateword cost as the full verifier's exact cost; shared operands/constants,
new internaloutputs and integer-multiplication protocol overhead change layout.
No extensionmultiplication, combinedhash/sampler/arithmetic proof, nativePCS
continuation, fullNEAR1Pgas, PQ128 or end-to-end formalcorrectness achieved.

Evidence under binius-babybear/: incrementalpatch,sourcepin,proof,negativeproof,
logs,statistics,report and Leanbuild. Apply after prior Binius patches, rebuild,
run check_binius_babybear.py (optional --reuse-tmp). make pin-check passes.

## 2026-10-17 — Fused Ext4 coefficient reductions halve private word count

Previous goal turn progressed at41bc27977 with constrained canonical BabyBear
multiplication and conditional Lean word equations. Revalidated clean research
tree and actual extension convention in check_whir_handoff.py: basis1,X,X²,X³,
X⁴=11. Added a matched Ext4 component; no whole-GKR lowering claimed.

Compute16canonical scalar products, weight6wrapped terms by11, accumulate each
output coefficient in exact128-bit words, and reduce each coefficient ONCE.
Four quotient witnesses have bounds[34,24,14,4]*P; all8input and4outputcoefficients
are canonical.128-bit addition checks upper overflow and uses only the low
addition's MSBcarry. Fullhigh/low quotientproduct+remainder matches the accumulator.
Maximumcoefficients exceed64bits, so a lowword-only implementation would be wrong.

Measured actual compiled circuit, same12publicwords for both approaches:
- Fused:178gates,120privatewords,72ZERO,64AND,26IMUL,0BMUL;4quotientwitnesses.
- Scalar-composed reference:394gates,255privatewords,157ZERO,111AND,44IMUL,
  12BMUL;22scalar reductions,44quotient/remainderwitnesses. Rangecheck sharing is
  whatever the same frontend actually performs, not an assumed multiplier.
Privatewords fall52.94%, IMUL40.91%. This is a component layout comparison,
not a measured fullverifier speedup or final proof-size improvement.

147valid pairs (allzero,allmax,mixed,16basisproducts,128random) agree with an
independent reduce-each-term polynomial reference. Eachpair has8wrongquotient/
wrongremainder cases, plus2noncanonical cases:1325assignments tested. Three
scalar-reference examples populate/evaluate successfully. Bothtargetedtests pass.
A16product fusedproof has190304Bpayload/190340Bserialized, plus1536Bpublicio.
Census exact:26368Balgebra,94496BMerkle,69440Bopenedvalues. Freshverify and
changedcanonicalinput/changedproof verification negatives pass. Statistics for
1and16products match linear constraint/privateword counts.

WordWideReduction.lean proves exact128-bit addition from explicit low/highcarry
equations and modular remainder soundness for a full128-bit numerator. Targeted
build/axioms pass (propext/Quot.sound only). These are conditional arithmetic
interfaces, not Rust frontend refinement, extensionpolynomial irreducibility,
or a complete Ext4 compiler proof. Diagnosticfield/security remain unchanged.

Next use these measured gates to budget/lower the actual fixed GKR arithmetic
DAG with shared inputs and challenge wiring. Standalone component bytes are
not additive; fully internal values and shared rangechecks affect layout. Still
no combinedGKR/hash/sampler/nativePCS proof, fullNEAR1Pgas, PQ128, or end-to-end
Lean correctness. Evidence binius-ext4/:patch/sourcepin/proof/tests/stats/logs/
report. check_binius_ext4.py reproduces, including the matchedreference test.
make pin-check passes; goal remains active.

## 2026-10-17 — Actual GKR DAG lowering exposes prime-field arithmetic cost

Previous goal turn progressed at56ad77b3c with measured fusedExt4. Revalidated
clean research branch. Replayed the existing optimized arithmetic DAG on the
FRESH fused-transcript GKR inputs:437equalities zero, residual and2603PCSweights
match the fresh proof's full-witness obligation. Inputs include actualclaim,
proofcoefficients,437derivedchallenges and knownvalues; no honest values are
converted into structural constants by the lowering.

Full reachable DAG540713nodes:599constants,5983inputs,82498adds,68785subs,
382848multiplications.382250multiplications have two dynamic operands;598have
aconstantoperand. This is structural classification, not a proof that no further
algebraic simplification exists. SHA256 of raw sourceDAG pinned in report.

Exported dependency-complete first32and128equality slices. Native example loads
fixednode/check graph as keydata and keeps named inputvalues public. Enforces
canonicalinputcoefficients, lowers add/sub to conditional reductions and mul to
fusedExt4 quotient constraints. Host topological evaluation only populates the
constrained witnesses. Every selected equality is assertedzero. It does NOT
include hash/sampler or residual/PCS verification. No fullverifier claim.

Measured sharing/padding:
- 32checks:642live nodes,252Ext4mults,124Ext4inputs;34630privatewords,
  496publicwords. Statistics only.
- 128checks:6774live nodes,4174Ext4mults,502Ext4inputs;527430privatewords,
  2008publicwords/16064B.796208gates,285730ZERO,268602AND,108524IMUL,
  8388BMULconstraints. Committedword padding crosses2^19 by3142words, so domain
  rounds to2^20. Do not optimize this slice-specific cliff as a fullgraph result.
- Actual128checkproof at rate1/8 diagnostic96-querytarget:
  281312Bpayload/281348Bserialized; algebra37536B,Merkle146880B,values96896B.
  Freshverification passes; mutatedproof rejects Merkle authentication.
  Changedchallenge rejects EARLIER at circuit witness assertions, explicitly not
  counted as an independent cryptographic verifier negative.

Repeated30case native query-budget screen and exactrational count checks.
Best128-querybudget is349764Bserialized beforepublicio (rate1/8), with unchanged
field/hashwidths and omittedsoundness terms. Native census equals actual96case.
Only4174/382848(~1.09%) of fullDAGmultiplications are in this slice;128/437checks
is not a representative fraction of total arithmetic work.

Decision: stop expanding this unchanged monolithic BabyBear-in-Binius lowering
before a fullcompilation/proving run. The smaller real slice already misses
300000B under the128-query-only screen. This is not a mathematical impossibility
or additive wholeproof bound; layoutchanges can alter costs. But it is sufficient
experimental evidence to require a different arithmetic/proof layout or large
workload reduction before investing in fullintegration. Direct prime-field
arithmetic with a hash-efficient recursion design remains the primary comparison;
Binius hash-gadget advantages alone do not remove this integration cost.

Evidence fused-gkr-arithmetic/:fullreplayreport,slices,nativesourcepatch/proof,
negatives,stats,30rowreport,logs. Reproduce export_fused_gkr_arithmetic.py then
check_binius_gkr_slice.py after applying savedpatch on previous Binius chain.
No new Lean/compiler refinement, PQ128certificate or fullNEAR1Pgas proof.
make pin-check passes. Fullgoal remains active and unachieved.
## 2026-10-17 — Source-pinned PCS adapter feasibility gate

Revalidated clean branch at d16c543a1. Previous comparison turn restated the
decision landscape and checked publications, but added no implementation
evidence; classified as no progress for the goal continuation audit.

Inspected actual Binius IOP channel, binary FRI fold and SWIRL WHIR verifier.
The channel admits arbitrary oracle linear relations and preserves commitment
round ordering, so it supplies a useful architectural seam. It does not make
the inspected PCS interchangeable. Binius folds additive binary-field domains;
the SWIRL verifier requires TwoAdicField, multiplicative power-of-two roots and
halving in binary_k_fold. In characteristic two, two is zero and x=-x, so the
unchanged multiplicative pair interpolation is unavailable. This rejects an
unchanged backend swap, not additive-domain WHIR or every binary PCS.

check_pcs_field_compatibility.py verifies exact upstream commits AND byte equality
for the three inspected files, archives sources with SHA256, and exhaustively
checks 4096 additive linear interpolation cases over GF(16). It checks that two
has no inverse and that there is no nonidentity square root of one in this
fixture. These finite checks are not a universal Lean theorem or protocol
security proof. The source operations establish the concrete implementation
incompatibility; no fresh cryptographic proof or size improvement is claimed.

Decision: do not start a supposed drop-in Binius/WHIR adapter. A real candidate
must supply binary encoding/folding/domain transitions/OOD reductions, preserve
oracle chronology and linear-relation semantics, and prove the resulting
proximity/composition bounds. It must also address the measured foreign-field
arithmetic cost. Primary next implementation direction stays native-field
recursive verifier workload reduction, with the complete 204076B diagnostic
root bundle as comparison, not independent Binius component-byte sums.

Artifacts: research/near-compression/results/swirl-security-review/
pcs-field-compatibility/. Audit passes; full NEAR1Pgas, PQ128, sub300000B at
that security and end-to-end Lean correctness remain open.

## 2026-10-17 — Shared equality products: proved identity and measured tradeoff

Previous goal turn made progress at84ebaf975 by source-gating an unchanged
Binius/WHIR adapter. Clean branch revalidated. Returned to the native-field
arithmetic verifier and inspected reachable costs: equality checks alone use
325519multiplications, residual45498 and PCScoordinates26333 (these sets overlap;
counts must not be added). Wiring/check evaluation remains the dominant target.

Implemented a separate candidate equality-table expansion: compute high=x*r
once, low=x-high, instead of independently multiplying x*(1-r). Prior baseline
and artifacts remain unchanged. Complete fixed-layout compilation and retained
proof replay pass all437checks, residual and2603PCScoordinates, including four
invalid-input checks and the known-value residual mutation. Complete baseline/
candidate output vectors also match for all-zero, all-one and seeded random
assignments to all5983inputs; inputs are not frozen to the honest witness.

Live census: multiplications382848->367934 (-14914,3.90%); subtractions68785->
98884 (+30099); adds82498 and inputs unchanged. Maximum emitted depth stays105.
This is NOT an unconditional improvement: multiplication must cost more than
30099/14914 (~2.018) subtractions in the chosen implementation for this simple
weighted operation metric to favor the candidate. Total live node count grows.
No recursive proof-size/runtime improvement has been measured, and no assumption
is made that generic GKR/AIR prices multiplication differently from subtraction.
Keep the candidate separate pending a real native-field circuit cost model.

SwirlSharedEquality.lean proves the child identity and full recursively expanded
ordered table equality for arbitrary field points and initial value lists.
Targeted lake build passes; axioms propext/Classical.choice/Quot.sound only.
This is an algorithmic identity, not Python interning/compiler refinement or
cryptographic soundness. Candidate does not change transcript or PCS obligations.

Reproduce check_swirl_shared_eq_products.py; artifacts in shared-eq-gkr-verifier/.
Next substantial workload reduction must address fixed wiring/check evaluation,
which dominates the measured full arithmetic, or use a circuit layout whose
actual cost makes these shared products valuable. FullNEAR1Pgas/PQ128/sub300000B
at that security and end-to-end correctness remain open.

## 2026-10-17 — Same-artifact execution/proof integration check

Previous turn answered the user's testing-level concern but made no code change;
classified no progress. Revalidated clean c575db2c5 and inspected actual slice
frontend, tests, Lean eligibility checker and native recursion test sources.
Stopped the contemplated BDD-order sweep: there is no measured parent-circuit
benefit that would justify it before the missing slice/recursion connection.

Added PreparedSliceOracle.lean: executes actual runCall using ONLY request bytes,
method, prepaid gas and explicit fuel. It receives no proof, statement, public
outputs or source trace and does not invoke the eligibility checker. The test
harness independently decodes published status/gas/i32 stack limbs and compares
them with that execution after fresh-process verification of the same retained
193-instruction proof. Both processes succeed and outputs agree.

Five altered public outputs (indices43,44,45,46,50) pass preparation and reject
specifically with ValueError: table zerocheck. The harness requires this exact
relation failure, not any exception or nonzero exit; archived stderr shows the
actual path. This improves on tests whose broad exception acceptance could
misclassify an earlier failure as cryptographic rejection. It is still proof
mutation testing, not adversarial witness generation or a soundness theorem.

Transport remains121982proof +223788statement +919request =346689bytes. This
retained proof is Q8/Ext4 diagnostic. No recursive parent currently consumes this
literal Wasm proof; generic SWIRL recursive fixtures do not close that gap.
Next integration work must implement that verifier relation in the parent or
prove the same literal AIR using the native child's backend before recursion,
with public program/output binding preserved. An oracle run alone must never
be substituted for the parent's constrained verification of the child.

Reproduce check_slice_execution_binding.py. Report and exact negative traces in
results/slice-execution-binding/. The Lean oracle compiles/runs through lake;
no new Lean theorem or acceptance-to-HoldsP proof. No fullNEAR1Pgas, PQ128 or
secure sub300000B claim. make pin-check passes.
