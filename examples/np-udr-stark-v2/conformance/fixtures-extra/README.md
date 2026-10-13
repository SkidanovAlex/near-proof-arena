# Extra D0a fixtures (repeated source keys, empty values, bandwidth requests, upsert paths)

Accepted D0a statements (claim + witness) that exercise prover paths the 64 public D0a fixtures
(`oracle/fixtures/v3/public-d0a/d0`) never reach: those never repeat a source key, never read
an empty value, never make the bandwidth scheduler draw a ChaCha20 word, and upsert the
scheduler state only by an in-place leaf replace.  Lanes `v3-prover-fixtures` (sections a–d)
and `v3-prover-cover` (e, f), 2026-10-13.

## Provenance

Derived from the public D0a fixtures (nearcore chaingen, seed 4243) by structural surgery with
`gen_extra_d0a.py` (see its docstring); `generate.sh` is the exact command list and regenerates
`d0/` and `mutants/` deterministically:

    ./generate.sh            # rewrites ./d0 and ./mutants
    ./generate.sh /tmp/x     # or elsewhere

The generator restores every hash the relation checks (`chunk_headers_root`, block hash chain,
the endorsed chunk's `prev_block_hash`, the own slot's `prev_state_root` and its witness-entry key,
post-state roots of the main / implicit transitions, the endorsed chunk's `prev_state_root`) and
re-records implicit-transition `base_state` along 0x07/0x0f.  Post-state roots are obtained
point-wise from the independent Python reference checker (`oracle/tools/spec_check_v3.py`), which
must end with verdict `ok`.  Acceptance is decided by the proved Lean `checkD0a B0`
(`zk-formal` exe `nearspec-v3-check-d0a`).  nearcore cannot judge these cases (the mutated blocks
are not in its store); `meta.json` says so (`nearcore`), and records the base case, the
operations, the Python fix-ups and the sha256 of both files.

Nothing in the frozen `oracle/v3`, the signed challenges or the public fixtures is modified.

Operations of `gen_extra_d0a.py` (see `--help`): `--dup` (a), `--groups` / `--buffered` (b),
`--bw BLK:SLOT=TO/BITMAP,...` (e: a chunk header's `BandwidthRequests`, edited where the chunk is
new and in its copies in newer blocks; `BLK:*` = every slot new in block BLK, `TO=*` = every
layout shard id), `--state OP` (f: main pre-state surgery by `trie_edit.py` — canonical
`del:KEY`, `put:KEY=VAL|@SRCKEY`, `keep:PFX,...` (rebuild from the revealed keys with these
byte prefixes; `keep:` = empty), and the non-canonical `ext0:NIBBLES` (an empty-key extension
above a node); `memory_usage` is nearcore's, re-verified on every fully revealed node).  Since
lane v3-prover-cover `meta.json` also records the Python D0a verdict and `chacha_words` per
scheduler run (main, then implicit).

## Cases

`d0/` (all accepted: `expected_rel_d0a = true`):

| case | base | exercises |
|---|---|---|
| x-dup2-older | 00-h10007-s3 | key repeated 2x in an older source block (= `dupkey_v3.py`) |
| x-dup2-b2 | 01-h10004-s0 | 2x in B2 |
| x-dup3-b2 | 01-h10004-s0 | 3x in B2, non-adjacent slots |
| x-dup4-b2 | 01-h10004-s0 | 4x in B2 (every non-own slot) |
| x-dup2-cross | 01-h10010-s1 | 2x across source blocks (B2 slot copied into block 1) |
| x-dup2-cross-rev | 01-h10010-s1 | 2x across source blocks (block-1 slot copied into B2) |
| x-dup3x2-cross | 01-h10010-s1 | two repeated keys: 3x (B2 + 2 in block 1) and 2x |
| x-dup3-older | 01-h10010-s1 | 3x in an older source block |
| x-dup2-implicit | 00-h10025-s2 | 2x in B2 with an implicit block after it |
| x-empty1 | 00-h10011-s1 | one empty `BufferedReceiptGroupsQueueData` value, one non-empty |
| x-empty3 | 00-h10012-s0 | three empty groups-data values (equal value records) |
| x-empty-new | 00-h10004-s3 | new `BufferedReceiptIndices`, two empty groups-data values, no receipts |
| x-empty-mix | 01-h10008-s0 | new indices: empty / proven-absent / 2-byte groups data; 7 receipts |
| x-empty-implicit | 00-h10023-s2 | empty groups data with an implicit block |
| x-dup-empty-implicit | 00-h10025-s2 | dup in B2 + empty value + implicit block |
| x-dup3-empty | 01-h10024-s1 | 3x across blocks + empty value |
| x-dup-empty-new | 01-h10010-s1 | cross-block dup + three empty values (new indices) |
| x-bw-pair | 00-h10004-s3 | 3 one-increment requests, one shuffle: 1 ChaCha word |
| x-bw-16 | 00-h10004-s3 | 16 words: exactly one ChaCha20 block |
| x-bw-64 | 00-h10004-s3 | 64 words: exactly four blocks |
| x-bw-65 | 00-h10004-s3 | 65 words: one word into a fifth block |
| x-bw-all | 00-h10004-s3 | every new slot requests every shard, 40 bits: 156 words |
| x-bw-implicit | 00-h10024-s0 | B2 + implicit block, all requests, 5 receipts: 195 + 160 words |
| x-bw-implicit-only | 00-h10024-s0 | requests only in the implicit block: 0 + 158 words |
| x-bw-n5 | 01-h10009-s1 | n = 5, 25 + 20 requests (A8-maximal), implicit: 329 + 268 words |
| x-bw-noprior | 00-h10024-s0 | no prior scheduler state (ups BI) + all requests: 195 + 190 words |
| x-ups-bi | 00-h10024-s0 | 0x0f absent: `BI[NLF,RBI,RDB]`; implicit `LP` |
| x-ups-bi-ext | 00-h10004-s3 | `BI[NLF,RBI,RDE]` below the root extension |
| x-ups-br | 00-h10024-s0 | 0x0f value in a branch (key 0x0f01 too): `BR[RBR,RDB,RDB]`; implicit `BR` |
| x-ups-bv | 00-h10024-s0 | valueless branch at [0,15]: `BV[RBV,RDB,RDB]`; implicit `BR` |
| x-ups-lsa | 00-h10004-s3 | the empty key is the only key (root leaf): `LSa[NLF,SPB]` |
| x-ups-lsb | 00-h10024-s0 | leaf 0x0f01 below slot 15: `LSb[MVL,SPB,RDB,RDB]`; implicit `BR` |
| x-ups-lsc | 00-h10004-s3 | one key under nibble 0: `LSc[MVL,NLF,SPB,RDB]` |
| x-ups-lsc-wex | 00-h10004-s3 | single-leaf trie: `LSc[MVL,NLF,SPB,WEX]` |
| x-ups-esl0 | 00-h10024-s0 | extension [0,1,0] below slot 15: `ESl0[MVE,SPB,RDB,RDB]`; implicit `BR` |
| x-ups-esl1 | 00-h10024-s0 | extension [0] below slot 15: `ESl1[SPB,RDB,RDB]`; implicit `BR` |
| x-ups-esn0 | 00-h10024-s0 | accounts only (root ext [0,0,7,3,…]), 5 receipts: `ESn0[MVE,NLF,SPB,WEX]`; implicit `LP` |
| x-ups-esn1 | 00-h10024-s0 | accounts only, root ext [0,0]: `ESn1[NLF,SPB,WEX]`; implicit `LP` |
| x-ups-pt | 00-h10024-s0 | non-canonical empty-key extension above 0x0f: `LP[RLP,PT,RDB,RDB]` (both runs) |

Every repeat copies the chunk inner, so key, `from_shard` and root agree: public dup byte 1
(`Public.sourceDupByte`).  The replaced slot's old witness entry stays as the extra, unused entry
`RelD0` requires per duplicate (spec v0a §2.5).

Empty values: `applyNewChunk` reads the groups data of every shard listed in
`BufferedReceiptIndices` and ignores the value; it is the only D0 read whose value can be
present and empty (account / access-key values must decode, queue indices must be 16 bytes or
absent, the scheduler state must decode).  So the zero-length value records (val `vz` rows,
zero-length `VPRE` SHA jobs) come from the qv path; codec/acct/akey reads can never be empty in
an accepted witness.

Upsert notation: the scheduler's write of key `0x0f` (`traceUpsert`, `Render/Ups/TreeTrace.lean`;
the `ups` table) as `terminal[part kinds bottom-up]`, main run then implicit run (`npudr
v3native <case>`, field `us`).  Together with the public fixtures (`LP[RLP,…]`) sections (f)
cover all 11 terminal cases `UCase.all` and all 12 part kinds `UKind.all`.

Reachability in D0a (why some shapes need surgery, and what cannot occur):

* D0 writes only `0x0f` (`PTrie.upsert`) and the receivers' accounts (same-length in-place
  `PTrie.set`) (`spec/lean/v3/NearSpecV3/RuntimeD0.lean`, header "Writes"): **no deletions**,
  no account creation; the ups table sees only the `0x0f` upsert.
* Each implicit transition's pre-state is the previous post-state, where `0x0f` is present
  (`PTrie.find_upsert_self`), so implicit runs end in `LP` or `BR` only.
* LP/BR **with a value-length change** is unreachable in D0a: Canon0f
  (`ChunkValidationV0a.canon0f`) makes every read `0x0f` value exactly the layout's n² links,
  and the new state has n² links too (single epoch), so |old| = |new| = 37 + 24n².
* `LSa` needs a leaf whose full key is a proper byte-prefix of `0x0f`, i.e. the empty key at
  the root: the trie holds only the empty key.  `BR`, `BV`, `LSb`, `ESl0`, `ESl1` need keys
  with byte prefix `0x0f` longer than one byte (no nearcore `TrieKey` has one); `PT` needs a
  non-canonical empty-key extension.  RelD0a does not restrict the state's key set or node
  canonicality (only the nodes on read paths are decoded, by hash), so these are accepted
  witnesses the prover must handle; `ESn*`/`LSc` need states without other nibble-0 columns.
* **Insert into an empty trie** (pre-state root `0^32`): `PTrie.upsert (.hash _) = none`
  (`spec/lean/NearSpec/TrieUpsert.lean`), and Lean `checkD0` rejects such a witness earlier
  (`invalid: MissingTrieValue (BufferedReceiptIndices)`: the zero root is an unrevealed
  `.hash`), so it is not in RelD0.  The Python reference (and nearcore, whose empty trie root is
  `Hash::default()`) accepts it: `gen_extra_d0a.py --base …/00-h10004-s3 --state keep:` is a
  Lean/Python disagreement, recorded in `docs/logs/v3-prover-cover-2026-10.md`, not a fixture
  (a spec decision).

ChaCha word counts: A8 allows at most one request per `(slot, to_shard)`, so a run has at most
n·(#new slots) ≤ n² requests; each shuffle of a bucket of k draws ≥ k−1 words.  The base
fixtures have n ≤ 5 and at most one implicit block (≤ 2 scheduler runs), so ~600 words is the
most they reach (x-bw-n5: 597); W0 = 770,000 is far out of reach of small fixtures (its AIR
side, the rng table's counter, is covered by the sampler/negative tests).  The boundary
fixtures sit on ChaCha20 block boundaries (16, 64, 65 words).

`mutants/` (all rejected: `expected_rel_d0a = false`, `mutation = w.dup_noextra`): a dup case
without the extra unused entries (`invalid: source_receipt_proofs contains extra proofs`).

An *inconsistent* repeat (public dup byte 2) cannot come from any claim: the key is the chunk
hash, which commits to the from-shard and the root, so `prepD0` lists are consistent by
construction.  The dup-byte-2 negative is therefore a prepared-statement mutation (see
`run-v2.d/extra.sh`).

## Checks

`run-v2.d/extra.sh` (run by default by `run-v2.sh`, or `./run-v2-section.sh extra`; needs the
zk-formal exe `nearspec-v3-check-d0a` built from the current tree): acceptance (Lean + Python +
D0a difftest), public tape / `Prep.encode` / Hint / `d0-prep` / `v3prepare` against
`np-lean-prep-v3`, the tape's `[dup, rep]` source bytes against an independent recomputation,
node/val/head real-witness entries (`v3check`, val/head Rust == Lean render), SHA job families
and bins against `np-lean-shabins-v3` (+ `v3check` of sha_t/sha_r), srcp/acct (`v3check`, Rust ==
Lean render), bus 14 (B_SRC) balance of the srcp table against the public tape (`npudr v3bus`),
and the negatives (dup byte 2 from a from-shard or root change, cleared `rep` bit: bus 14
unbalanced).  2026-10-13: 292 PASS, 0 FAIL, ~2 min.

Lane v3-prover-cover (sections e, f), 2026-10-13: `npudr v3prove --check-only` 22/22 (25 tables, 51
buses); sections extra / trie / a7 / schedqv / collect / rcptfam on the 22 new cases: 931 PASS
(Rust == Lean for every native object, entry list and render); one real proof of x-bw-implicit
(`PROVE_V3=1`), see `docs/logs/v3-prover-cover-2026-10.md`.

Limits: the receipt SHA family (incl. the gated `RC` jobs) is still Lean-supplied
(`sha_receipt.json`; no real-witness rcpt dumper yet, lane `v3-prover-rcptfam`), so the Rust RC
gating on duplicates is compared only through the bins built from it; the Lean node render is
skipped (slow; `EXTRA_NODE_MAX`), node is `v3check`ed.
