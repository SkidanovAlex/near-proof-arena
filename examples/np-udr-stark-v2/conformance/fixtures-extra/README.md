# Extra D0a fixtures (repeated source keys, empty values)

Accepted D0a statements (claim + witness) that exercise prover paths the 64 public D0a fixtures
(`oracle/fixtures/v3/public-d0a/d0`) never reach: those never repeat a source key and never read
an empty value.  Lane `v3-prover-fixtures`, 2026-10-13.

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

Every repeat copies the chunk inner, so key, `from_shard` and root agree: public dup byte 1
(`Public.sourceDupByte`).  The replaced slot's old witness entry stays as the extra, unused entry
`RelD0` requires per duplicate (spec v0a §2.5).

Empty values: `applyNewChunk` reads the groups data of every shard listed in
`BufferedReceiptIndices` and ignores the value; it is the only D0 read whose value can be
present and empty (account / access-key values must decode, queue indices must be 16 bytes or
absent, the scheduler state must decode).  So the zero-length value records (val `vz` rows,
zero-length `VPRE` SHA jobs) come from the qv path; codec/acct/akey reads can never be empty in
an accepted witness.

`mutants/` (all rejected: `expected_rel_d0a = false`, `mutation = w.dup_noextra`): a dup case
without the extra unused entries (`invalid: source_receipt_proofs contains extra proofs`).

An *inconsistent* repeat (public dup byte 2) cannot come from any claim: the key is the chunk
hash, which commits to the from-shard and the root, so `prepD0` lists are consistent by
construction.  The dup-byte-2 negative is therefore a prepared-statement mutation (see
`run-v2.d/extra.sh`).

## Checks

`run-v2.d/extra.sh` (run by default by `run-v2.sh`, or `./run-v2-section.sh extra`).
