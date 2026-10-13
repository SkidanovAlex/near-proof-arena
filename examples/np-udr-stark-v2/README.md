# np-udr-stark-v2: Rust prover for the v3 succinct proof

The Rust prover for `np-udr-stark-v2` (`docs/zk-formal/FORMATS.md` §8):
v1's STARK (DESIGN.md §4) with **public segments** (bus messages read by the
verifier from the prepared statement) and **`auxGroup = g ∈ {1, 2, 3}`**
(`ZkFormal.V2.G.pg g`, V3-D0-DESIGN §5.3). The target AIR is the frozen
`ZkFormal.NearV3.Assembly.nearAirV3` (25 tables) at `g = 2`, verified by
`ZkFormal.Prover.Np.G.npVerifierP challengeSpecD0a nearAirV3 split prepV3b`
(`docs/zk-formal/STATUS-V3-ASSEMBLY.md`).

Validity, not zero knowledge (as v1).

## Provenance

`source/` and `conformance/` are forked from `examples/np-udr-stark-fast2`
(the admitted, live rank-4 v1 prover, commit `2cadc9fb`), then `cargo fmt`
was applied to the whole crate (fast2 was not rustfmt-clean). To review the
v2 changes against fast2, format a copy of fast2 first and diff the trees.
The v1 NEAR generators (`src/near/`, `bin/prove`, `bin/prepare`) are still the
v1 ones; they are kept so the v1 conformance suite keeps running, but they are
**not shipped**: the package's entry points are the v3 bins below.

## Entry points (v3 D0a package)

`build-recipe/build.sh` (judge: `bash build-recipe/build.sh` from the package root, offline,
fresh `$HOME`, `SOURCE_DATE_EPOCH=0`) installs (docs/CONTRACTS.md §4, argv as in
`runners/worker/src/stages/common.rs`):

| output | built from | contract |
|---|---|---|
| `out/prepare` | `src/bin/prepare_v3.rs` (std only) | `prepare --params P --out DIR`: `P` must be byte-equal to `NpUdrStarkV2.publicBin` (`formal/NpUdrStarkV2/PublicBin.lean`: `near-arena-params-v3`, `near/pv86/chunk-validation/v0`, pv 86, domain `D0a`, runtime config `b7dce203…062f`; 100 B, sha256 `ab13c199…957f`), else exit 2; writes `DIR/public.bin = P`. |
| `out/prove` | `src/bin/prove_v3.rs` | `prove --public DIR --request R --witness W --claim-out C --proof-out Q`: `C = R` (`near-arena-claim-v3`: request = claim); `Q = borshBytes (Hint.encode h) ++ π` — the `npudr v3prove` pipeline (`v3::prove::case_inputs`: `hintOf`, `prepD0`, all 25 tables natively; STARK at `auxGroup = 2` over (`DIR/public.bin`, prepared bytes); the Rust verifier re-checks `π` before anything is written). The AIR is `source/near-air-v3.json` (the `np-lean-export-v3` export of `nearAirV3`, sha256 `fa599b3b…b452`), compiled in. Exit 2 and no output on a claim outside RelD0a (`hintOf`/`prepD0` reject) or any failure. No constraint/bus pre-check (that is `npudr v3prove`'s diagnostic; the post-proof verify covers it). Memory budget: the prover default (`NPUDR_MEM_GB` unset = 11). |
| `out/verify` | `formal/` model closure + trusted `source/lean-vendor` | the judge's native-lean build of `NpUdrStarkV2.Model.verifier` replicated (`verify --public DIR --claim C --proof Q`; reads `DIR/public.bin`; exit 0 accept / 1 reject / 2 error). The judge uses its own build of the same model. |

Packaging steps (packager, from the repository checkout): `build-recipe/sync-lean.sh` (vendors
the certificate's import closure into `formal/ZkFormal`, `formal/ReexecV3D0` and the trusted
`source/lean-vendor`, pinned in `dependency-locks/{zk-formal,lean-vendor}.sha256`) and
`build-recipe/vendor.sh` (crates into `source/vendor`, digest in
`dependency-locks/vendor-digest.txt`; works offline from a warm cargo cache with
`CARGO_NET_OFFLINE=true`). The package is the git tree of this directory plus those generated
trees. Dry run (2026-10-13, lane v3-package): `docs/logs/v3-package-2026-10.md`.

**Known blocker (2026-10-13):** the Lean step of `build.sh` (and the judge's native-lean build)
stops at the model-import rule: `ZkFormal.Near.Render.Common` (in the 657-module closure of
`NpUdrStarkV2.Model`, via `NearAir → Candidates.SortEmpty → Render.Proof.*`) imports
`Std.Data.HashMap`; model modules may import only trusted modules, model modules and `Init`.
Needs a zk-formal fix (see the log). With that rule relaxed, the build, `prepare`, `prove` and
`out/verify` work end to end (4 D0a proofs accepted).

## Status

**End to end (2026-10-13, lane/v3-prover-prove): real v3 D0a proofs, accepted by the deployed Lean
verifier; the certificate is unconditional.**

* `npudr v3prove <case_dir> <out_dir> --air nearAirV3.json --pub public.bin` builds everything from
  `claim.bin` + `witness.bin` in Rust (hint, prepared statement, all 25 tables: `v3trie`, `v3sched`
  (lane v3-prover-schedqv), `v3rcptfam`, SHA collector), checks every table's constraints and the
  exact balance of **every bus** (51 buses incl. the public messages: BYTES, DIGEST, SIZE, VSLOT,
  KEYNIB, FINAL, VBYTES, MPOS, …), proves at `auxGroup = 2` and writes `proof.bin =
  borshBytes (Hint.encode h) ++ π`. `--check-only`: all 81 fixtures (64 public + 17 extra) pass.
* Proofs (8 CPUs, `taskset -c 8-15`, `NPUDR_MEM_GB=20`): `00-h10004-s3` 5,256,829 B / 749 s /
  12.2 GB RSS; `00-h10035-s3` (largest witness) 5,674,156 B / 736 s / 13.3 GB; `01-h10009-s1` (2
  scheduler blocks) 5,618,528 B / 710 s / 12.6 GB. All ≤ `maxProofBytes` 8 MiB (and the STARK part
  ≤ `v3MaxInner` 6,435,489 B). Time is dominated by the six fixed `2^22`-row tables (codec,
  scandist, proc, mem, cmp, rcpt: 588 columns at LDE `2^26`).
* `np-lean-verify-v3` (`conformance/VerifyV3.lean`) runs the deployed model
  `(npVerifierP challengeSpecD0a nearAirV3 split prepV3b).toVerifier.deployed` (`NpUdrStarkV2.Model.verifier`):
  **accepts** all three proofs (≈3 s each) and rejects 14/14 mutations per proof (STARK byte flips,
  truncation/extension/empty, hint `n`/body/length, public tape, claim bytes, another fixture's claim).
  `conformance/run-v2.d/prove.sh` (`PROVE_V3=1`; heavy, run alone).
* `formal/`: `NpUdrStarkV2.certificate` is main's unconditional `nearV3_admission_final`
  (`#print axioms`: `propext`, `Classical.choice`, `Quot.sound`). Log:
  `docs/logs/v3-prover-prove-2026-10.md`.

Older notes (per-part history) follow.

**Rust v3 prover (2026-10-12, synced to main c2bd648b, `nearV3_admission_final`):** all **25 generators** follow the honest renders of the current `nearAirV3` (`Render/CompleteV3.lean`): A7 tables `nodeA7`/`valA7`/`upsA7`/`sizeA7` (2/4/7/21), table 20 `SrcpDD` (dedup + A10 depth bits), table 17 `AccountEmpty`, table 23 `MerkleEmpty` (2^19), table 24 `SortEmpty` (cap 19), table 16 `RcptV3.tableQ` (2^22), table 9 with the A9 word counter, tables 8/10 at cap 22, scheduler tables 11–15 concatenated over all runs at 2^22 (`Proc.tableB`), SHA at `padLog22`. Every changed table has a Lean differential (`np-lean-render-v3-{a7,rcs,rcpt,sched}`, byte-identical; rcpt compares the planned prefix + 8 padding rows) and passes `npudr v3check`. The **public tape** uses 34-byte source rows `[dup, rep] ++ root` and is byte-identical to `Public.preparedBytes` on all 64 D0a fixtures. The **SHA job collector** (`collect.rs`) reproduces the Lean two-bin split `twoShaJobBins` (`[native ++ src₀, scheduler ++ receipt ++ src₁]`, gated RC digests, zero-length jobs) on all 64 fixtures (`np-lean-shabins-v3`). **Receipt side from claim + witness (2026-10-13, `src/v3/rcptfam.rs`):** `npudr v3rcptfam` builds the entries of tables 16 (rcpt view), 17, 18, 19, 20, 23, 24 and the receipt SHA family with no Lean dump; `npudr v3sha --native` builds the receipt family purely in Rust. `run-v2.d/rcptfam.sh` (`np-lean-rcptfam-v3`): identical on all 81 fixtures (64 public + 17 fixtures-extra; table-16 rows/view and bnd on the 78 with ≤ 4000 planned rows), collector bins identical, 283 PASS (see `docs/logs/v3-prover-rcptfam-2026-10.md`). Remaining before a real balanced proof: witness → entries dumpers for qv (22)/scheduler blocks/ups/A7 `sel`/`yN`, the sibling lane's `hintOf`/`prepClaim`/`prepBody`, and the memory cost of the fixed-2^22 tables.

**Trie side from claim + witness (2026-10-13, lane/v3-prover-trie):** `npudr v3trie <case>` (`src/v3/trie.rs` over `native.rs` (native execution: `applyNewChunk`/`applyMissingChunk` trie effects, bandwidth-scheduler `runCore` state, account replay, `traceUpsert` runs), `walks.rs`, `upsnat.rs` (honest ups instances), `forest.rs` (`TrieNative.nodes/vals/heads`, `uniqNative`)) derives the honest entries of tables 2 node (+A7 `rpl`), 3 head, 4 val (+A7 `rpl`), 5 walk, 6 uniq, 7 ups, 21 size (+`yN`) with no Lean dump. Ground truth `np-lean-trie-v3` (`conformance/TrieEntriesV3.lean`, the entry lists of `TrieSide.trie_side_exact`); fast Lean renders through `Conformance/FastTrie.lean` (executable twins with equality lemmas). `run-v2.d/trie.sh`: on all 81 fixtures (64 public + 17 extra) Rust entries == Lean entries, all 7 tables pass `v3check`, Rust renders == Lean renders, the 13 trie-internal buses balance against the public tape; 33 negatives rejected (116 PASS).

**Scheduler / ChaCha / qv side from claim + witness (2026-10-13, lane/v3-prover-schedqv):** `npudr v3sched <case> <dir>` (`src/v3/schedqv.rs`: `Gen.ActualRun.run` with `processEv` rounds and the run-wide ChaCha shuffle, `linkPass`/`allowances`/`a0Canon`, `distributeEv` grants, `priorValueId`, the qv read plan / queue providers) writes the honest entries of tables 8 chacha, 9 rng, 10 shuf (the runs' lane entries), 11–15 (one `SchedIn` block per scheduler call: main chunk, then each implicit step) and 22 qv (`{walks, records}`) as `<dir>/<table>.json`, the `v3prove` entries-dir layout. Ground truth `np-lean-sched-v3` (`conformance/SchedEntriesV3.lean`): the `PriorCore` block construction of `native_allocated_blocks_run` and `qvNativeWalks`/`qvNativeRecords`, plus renders of the native blocks through the proof's trace definitions (twins `codec_twin` … `qv_twin`, axioms ⊆ propext/Classical.choice/Quot.sound). `run-v2.d/schedqv.sh`: Rust == Lean entries on all 81 fixtures, `v3check` of the 9 tables, Rust renders == Lean native renders (full 2^22 sha256 on every multi-block / request case), 25 buses balanced against the public tape with the trie and receipt entries (40–52, 56–62, 21, 29, 63, 5, 6), the Lean `ActualRun.run` sampler == `npudr v3sched --rerun`, negatives (see `docs/logs/v3-prover-schedqv-2026-10.md`).

| piece | state |
|---|---|
| `auxGroup` | `Air.aux_group` (`Air::with_aux_group(g)`); `AuxLayout::new(t, g)`, `Table::{degree,aux_width,num_quot_chunks,num_finals}(g)` mirror `Table.auxCount/auxDegree/degree/quotCount g` and `chunksOf g` (`ZkFormal.Stark.Protocol`). |
| `np-air-v2` | `Air::from_json` reads v1 and v2 (`pubSegs`, `maxPub`), `Air::to_json` writes them byte-identically to `ZkFormal.V2.AirP.exportJson`. |
| reference verifier | `pub_fit`, `pub_msgs`, `pub_prod` (`PubSeg.count/startOffset/record/fits`, `pubFit`, `pubMsgs`, `pubProd`); bus equation `∏sends·Π_pub(true) = ∏recvs·Π_pub(false)` (`globalChecksP`), `pubFit` checked before any record is enumerated (as Lean's `okLens && pubFit && …`). The provers self-check with the same equation. |
| prover messages | unchanged from v1 (FORMATS §8.5): the v2 prover is v1's honest prover for `AP.toAir` at `pg g`. |
| `nearAirV3` | read from `np-lean-export-v3` (1,653,660 B, sha256 `fa599b3b…`, main c2bd648b), validated, per-table layout equal to Lean's at g = 1, 2, 3. |
| trace generation for `nearAirV3` (witness → 25 tables) | **partial**: aligned generators for 7 tables (bnd, akey, head, val, uniq, walk, **node**) in `src/v3/`, byte-identical to the Lean `Render/Padded*.lean` generators (`conformance/run-v2.sh` §3). node is the largest/most complex table. |
| witness → per-table entries (part 2c) | **partial**: `conformance/WitnessEntriesV3.lean` → `np-lean-entries-v3 <case> [<table>]` runs the proved D0a extraction (`checkD0a B0` + the reference `trace`) on a real fixture and dumps the honest entry lists for **node** (`initializeList 0 (forestNodes 0 0 0 ts)`), **val** (`seedValuesFrom 0 (forestBytes ts)`) and **head** (`traceHeads 0 0 pairs`); `src/v3/entries.rs` + `npudr v3entries` read them. `conformance/run-v2.sh` §4: `npudr v3check` accepts every constraint and `npudr v3render` is byte-identical to `np-lean-render-v3` on the real-fixture node/val/head entries. `walk`, `uniq`, `akey`, `bnd` need the query/receipt allocation layers (extension point, below). |
| `prepD0`/`Hint` codec in Rust (part 3) | **partial**: `src/v3/prep.rs` mirrors `PrepD0.lean`'s byte codecs — `Hint` (`u32 n ‖ borshBytes body`), `PrepHdr`/`SrcList`/`SchedPub`/`Prep` `encode()`, the `encList`/`encOpt`/`concatAll`/`borshBytes` helpers, and the refund body codec (`decode_body`/`body_of`, `pRefund`). `conformance/PrepV3.lean` (`np-lean-prep-v3`) runs the proved `checkD0a B0` + `hintOf` + `prepD0` on a real fixture and dumps `hint`/`prep`/`refunds_enc`/`prep_json`; `npudr prep-encode` re-encodes `prep_json` byte-identically to the Lean `Prep.encode`, and the `Hint`/body codecs round-trip (`run-v2.sh` §5, all 64 D0a fixtures). **Ported (2026-10-12):** `prepClaim`/`prepBody` (`src/v3/d0.rs`, incl. A8 and main's A12 `c.layout_wf`) and `hintOf` (`src/v3/hint.rs`: `decodeW`, `pReceipt`, `appliedReceipts`, `partialTrie`/`buildFor`, `PTrie.find/get/set`, `bufferedShards`/`mainKeys`, `applyReceipt`/`applySystemReceipt`, `refundsUpTo`; the `applyNewChunk` branch is argued equal to `refundsUpTo` via `find_upsert_other`, see the module docs). `npudr v3prepare <claim> <witness> <out>` = `hintOf` + `prepD0`; `run-v2.sh` §"prover preprocessing" checks it against `np-lean-prep-v3 --any`: hint + prep byte-identical on all 64 fixtures, and 120 mutated claim/hint/witness cases agree (every claim mutation `checkD0a B0` rejects is rejected). |
| package skeleton + certificate (part 4) | **superseded 2026-10-13: the certificate is now unconditional (above)**; historical: `candidate.toml`, `build-recipe/` (`build.sh`/`sync-lean.sh`/`vendor.sh`), `formal/` (`NpUdrStarkV2.{Model,PublicBin,Assembly,Certificate}.lean`), `bench/`, `dependency-locks/` mirror `examples/np-udr-stark`. `NpUdrStarkV2.Model.verifier` is the deployed model `(npVerifierP challengeSpecD0a nearAirV3 split prepV3b).toVerifier` (`split`/`join`/`prepV3b` = `ZkFormal.NearV3.Assembly`), closed, no `sorry`. `NpUdrStarkV2.certificate` is `ZkFormal.NearV3.Assembly.nearV3_admission_with_extract_b` specialised to `challengeParamsD0a`: it is **conditional** on the open obligations `ExtractV3Stmt` (the `link` package), the render completeness closure and `AlignedV3Stmt` (`docs/zk-formal/STATUS-V3-ASSEMBLY.md` §3). Until those land the candidate is **not ADMITTED**. `build.sh` builds the Rust bins (`out/prepare`/`out/prove`) and the native-lean `out/verify`; historical: the Rust bins were the inherited **v1** surfaces until 2026-10-13 (now the v3 `prepare_v3`/`prove_v3`, above). |

## Verification

* `cargo test --release` in `source/`: v1 suites unchanged plus `tests/v2.rs`
  (JSON round trip, layouts at g = 1/2/3, prove/verify at every g, proofs
  rejected under every other g, tampered claims, hostile counts/offsets
  rejected by `pubFit`, prover refuses an unbalanced claim).
* `conformance/run-v2.sh` §3 checks every aligned generator against `np-lean-render-v3` on the random samplers; §4 runs `np-lean-entries-v3` on real `public-d0a/d0` fixtures and checks that node/val/head entries from a real witness pass `npudr v3check` and render byte-identically to `np-lean-render-v3`.
* `conformance/run-v2.sh` §5 (part 3): `np-lean-prep-v3` on the `public-d0a/d0`
  fixtures (all 64 accept `checkD0a B0`) emits `hint`/`prep`/`refunds_enc`/
  `prep_json`; `npudr prep-encode` reproduces `Prep.encode` byte for byte and the
  `Hint`/refund-body codecs round-trip.
* `conformance/run-v2.sh` (166 checks + part 3, all pass on 2026-10-11): the deployed
  Lean `ZkFormal.V2.verifierP Fp Fp8 AP (pg g)` (`np-lean-verify-v2`) accepts the
  Rust v2 toy proofs at g = 1, 2, 3 and logs 4/6/10, rejects them under every
  other `auxGroup`, rejects 9 proof mutations and 5 claim mutations each, and the
  AIR re-exports byte-identically; `nearAirV3` layouts equal at g = 1, 2, 3.
* `conformance/run.sh` (inherited v1 suite; 205 checks, all pass on the fork).
* `formal/`: `cd formal && lake build NpUdrStarkV2.Certificate` (requires the repo
  `zk-formal` Lake package; build under `/data/illia/nearproof-deps/bin/heavy`).
  Builds the (unconditional, `nearV3_admission_final`) certificate; `#print axioms NpUdrStarkV2.certificate`
  reports `[propext, Classical.choice, Quot.sound]` (no `sorry`/`axiom`).
* `build-recipe/build.sh`: `SKIP_LEAN=1 bash build-recipe/build.sh` builds
  `out/prepare`/`out/prove` (Rust, the v3 bins `prepare_v3`/`prove_v3`); without `SKIP_LEAN=1` it also replicates the
  judge's native-lean build into `out/verify` (needs `source/lean-vendor` and
  `out/`+`formal/ZkFormal`+`formal/ReexecV3D0`, all produced by
  `build-recipe/sync-lean.sh`). `build-recipe/vendor.sh` needs network and is a
  packager step (not run here).
* `cargo clippy --all-targets -- -D warnings`: 109 findings on 2026-10-12: 50 inherited from
  fast2, 59 in the new `src/v3` generators (style lints; not yet cleaned).

`conformance/` needs a built `zk-formal/.lake` (it `require`s `../../../zk-formal`).
