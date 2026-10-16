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
