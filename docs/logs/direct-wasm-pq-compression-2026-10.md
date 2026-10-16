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
