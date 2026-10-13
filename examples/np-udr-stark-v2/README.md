# np-udr-stark-v2: Rust prover for the v3 succinct proof (work in progress)

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
v1 ones; they are kept so the v1 conformance suite keeps running.

## Status

**Rust v3 prover (2026-10-12, synced to main c2bd648b, `nearV3_admission_final`):** all **25 generators** follow the honest renders of the current `nearAirV3` (`Render/CompleteV3.lean`): A7 tables `nodeA7`/`valA7`/`upsA7`/`sizeA7` (2/4/7/21), table 20 `SrcpDD` (dedup + A10 depth bits), table 17 `AccountEmpty`, table 23 `MerkleEmpty` (2^19), table 24 `SortEmpty` (cap 19), table 16 `RcptV3.tableQ` (2^22), table 9 with the A9 word counter, tables 8/10 at cap 22, scheduler tables 11–15 concatenated over all runs at 2^22 (`Proc.tableB`), SHA at `padLog22`. Every changed table has a Lean differential (`np-lean-render-v3-{a7,rcs,rcpt,sched}`, byte-identical; rcpt compares the planned prefix + 8 padding rows) and passes `npudr v3check`. The **public tape** uses 34-byte source rows `[dup, rep] ++ root` and is byte-identical to `Public.preparedBytes` on all 64 D0a fixtures. The **SHA job collector** (`collect.rs`) reproduces the Lean two-bin split `twoShaJobBins` (`[native ++ src₀, scheduler ++ receipt ++ src₁]`, gated RC digests, zero-length jobs) on all 64 fixtures (`np-lean-shabins-v3`; the receipt family is Lean-supplied there until a real-witness rcpt dumper exists). Remaining before a real balanced proof: witness → entries dumpers for rcpt/scheduler blocks/ups/srcp `rep`/A7 `sel`/`yN`, the sibling lane's `hintOf`/`prepClaim`/`prepBody`, and the memory cost of the fixed-2^22 tables.

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
| package skeleton + conditional certificate (part 4) | **partial (NOT ADMITTED)**: `candidate.toml`, `build-recipe/` (`build.sh`/`sync-lean.sh`/`vendor.sh`), `formal/` (`NpUdrStarkV2.{Model,PublicBin,Assembly,Certificate}.lean`), `bench/`, `dependency-locks/` mirror `examples/np-udr-stark`. `NpUdrStarkV2.Model.verifier` is the deployed model `(npVerifierP challengeSpecD0a nearAirV3 split prepV3b).toVerifier` (`split`/`join`/`prepV3b` = `ZkFormal.NearV3.Assembly`), closed, no `sorry`. `NpUdrStarkV2.certificate` is `ZkFormal.NearV3.Assembly.nearV3_admission_with_extract_b` specialised to `challengeParamsD0a`: it is **conditional** on the open obligations `ExtractV3Stmt` (the `link` package), the render completeness closure and `AlignedV3Stmt` (`docs/zk-formal/STATUS-V3-ASSEMBLY.md` §3). Until those land the candidate is **not ADMITTED**. `build.sh` builds the Rust bins (`out/prepare`/`out/prove`) and the native-lean `out/verify`; the Rust bins are still the inherited **v1** surfaces — the v3 `prove` (nearAirV3 trace + STARK prove) is not written yet. |

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
  Builds the conditional certificate; `#print axioms NpUdrStarkV2.certificate`
  reports `[propext, Classical.choice, Quot.sound]` (no `sorry`/`axiom`).
* `build-recipe/build.sh`: `SKIP_LEAN=1 bash build-recipe/build.sh` builds
  `out/prepare`/`out/prove` (Rust); without `SKIP_LEAN=1` it also replicates the
  judge's native-lean build into `out/verify` (needs `source/lean-vendor` and
  `out/`+`formal/ZkFormal`+`formal/ReexecV3D0`, all produced by
  `build-recipe/sync-lean.sh`). `build-recipe/vendor.sh` needs network and is a
  packager step (not run here).
* `cargo clippy --all-targets -- -D warnings`: 109 findings on 2026-10-12: 50 inherited from
  fast2, 59 in the new `src/v3` generators (style lints; not yet cleaned).

`conformance/` needs a built `zk-formal/.lake` (it `require`s `../../../zk-formal`).
