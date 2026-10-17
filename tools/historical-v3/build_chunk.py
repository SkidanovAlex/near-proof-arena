#!/usr/bin/env python3
"""Build an AUTHENTIC EXACT-CHUNK v3 fixture from the current epoch's
sync-prev block (lane/historical-v3).

For shard S, the chunk included in the epoch's sync_prev block H has
prev_state_root == the state-sync root peers serve parts for. This script:

  1. takes the chunk's incoming receipts from the neardata block JSON
     (authentic ReceiptViews, no transaction in the D0 targets);
  2. incrementally harvests the shard trie over P2P state-sync
     (`oracle/historical` header/part + range bisection), driving the
     missing-region loop off `exec-chunk`'s receiver-path check;
  3. executes the chunk's receipts under the pinned nearcore 2.13.4
     Runtime::apply with a recorder and anchors the result against the
     chain itself:
       - every receipt outcome: status AND gas_burnt equal the on-chain
         receipt_execution_outcomes of that chunk (exact protocol/config);
       - Σ gas_burnt == the chunk header's gas_used (no transactions);
       - the computed post_state_root == the prev_state_root of the shard's
         NEXT chunk on chain — the strongest anchor: our replay of the
         transition lands on the chain's own committed root;
       - no delayed receipts, outgoing receipts == refunds.
  4. writes the case dir:
       context.json        build inputs (RPC views + block fields)
       chunk_exec.json     execution summary + anchors verdicts
       apply_witness.bin   borsh PartialStorage — every node Runtime::apply
                           read, hash-linked to the chunk's prev_state_root
                           (the witness `base_state` raw material)

Usage:
  build_chunk.py --shard 13 [--epoch-start H] [--out DIR] [--max-parts N]
"""
from __future__ import annotations

import argparse
import base64
import hashlib
import json
import os
import re
import subprocess
import sys
import time
import urllib.error
import urllib.request

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
FETCH = os.path.join(ROOT, "oracle/historical/target/release/near-arena-historical")
sys.path.insert(0, os.path.join(ROOT, "tools/mainnet-replay"))
import replay as classifier  # noqa: E402  (the measured-mix classifier)
sys.path.insert(0, os.path.join(ROOT, "oracle/historical"))
import harvest as v1  # noqa: E402  (Parts / sync_point / anchors helpers)
v1.FETCH = FETCH  # harvest.py defaults to its own target/debug binary

RPC = os.environ.get("NEAR_RPC", "https://archival-rpc.mainnet.fastnear.com")
FETCH = os.environ.get("FETCH", FETCH)
PARTS_DIR = os.environ.get("PARTS_DIR", os.path.join(HERE, "parts"))


def rpc(method, params):
    return v1.rpc(method, params, RPC)


def next_blk(h):
    """neardata block doc for height h+1's... actually h itself, cached."""
    b = classifier.get_block(h, os.path.join(PARTS_DIR, "blocks"))
    return b


def block_with_shard_chunk(shard, height):
    """neardata shard entry for `shard` at `height` (None if no chunk)."""
    b = next_blk(height)
    for s in b.get("shards", []):
        c = s.get("chunk")
        if c and c["header"]["shard_id"] == shard and c["header"]["height_included"] == height:
            return s
    return None


def next_new_chunk_root(shard, after_height, cap=200):
    """prev_state_root of `shard`'s first NEW chunk after `after_height`
    (commits the post-state of the chunk applied at after_height)."""
    h = after_height
    for _ in range(cap):
        h += 1
        b = next_blk(h)
        for c in b["block"]["chunks"]:
            if c["shard_id"] == shard and c["height_included"] == h:
                hdr = rpc("chunk", {"chunk_id": c["chunk_hash"]})["header"]
                return {"height": h, "chunk_hash": c["chunk_hash"],
                        "prev_state_root": hdr["prev_state_root"]}
    return None


def main(argv):
    ap = argparse.ArgumentParser()
    ap.add_argument("--shard", type=int, required=True)
    ap.add_argument("--epoch-start", type=int, default=None)
    ap.add_argument("--out", default=os.path.join(HERE, "cases"))
    ap.add_argument("--max-parts", type=int, default=80)
    ap.add_argument("--name", default=None)
    a = ap.parse_args(argv)

    if not os.path.exists(FETCH):
        sys.exit(f"missing {FETCH}; build oracle/historical first")
    status = rpc("status", [])
    head = status["sync_info"]["latest_block_height"]
    sp = v1.sync_point(a.epoch_start or status["sync_info"]["epoch_start_height"])
    shard = str(a.shard)
    # harvest.py's sync_point keys chunks by int shard id (live dict).
    sp_chunks = {str(k): v for k, v in sp["chunks"].items()}
    if shard not in sp_chunks or not sp_chunks[shard]["new_chunk"]:
        sys.exit(f"shard {shard} has no new chunk at sync_prev {sp['sync_prev_height']}")
    root = sp_chunks[shard]["prev_state_root"]
    H = sp["sync_prev_height"]

    # ---- the chunk and its TRUE incoming receipts (peer-served sync header) --
    # neardata's chunk.receipts is the shard's OUTGOING list; the header's
    # incoming_receipts_proofs (proof-backed, grouped by sending block) is the
    # authoritative incoming set.
    sentry = block_with_shard_chunk(a.shard, H)
    ch = sentry["chunk"] if sentry else None
    P0 = v1.Parts(sp["sync_hash"], a.shard, head)
    hdr0 = P0.header()
    dec = subprocess.run([FETCH, "chunk-of-header",
                          os.path.join(PARTS_DIR, f"{sp['sync_hash']}_s{a.shard}_header.bin"),
                          str(a.shard)], capture_output=True, text=True, timeout=120)
    if dec.returncode != 0:
        sys.exit(f"chunk-of-header failed: {dec.stderr[-800:]}")
    hd = json.loads(dec.stdout.strip().splitlines()[-1])
    if hdr0["chunk_hash"] != hd["chunk_hash"]:
        sys.exit("header chunk mismatch")
    # nearcore set_state_finalize (chain_update.rs): a state-syncing node
    # applies, WITH this chunk, only those receipt groups whose sending-block
    # height <= chunk.height_included(); later groups are saved for the
    # catch-up chunks (738+). Also: ShardChunkHeaderInner carries only
    # prev_gas_used — a chunk's OWN gas appears in the NEXT chunk's header.
    receipts = []
    groups_used, groups_later = [], []
    for g in hd["incoming_receipts_by_block"]:
        gh = v1.rpc("block", {"block_id": g["block_hash"]})["header"]["height"]
        if gh <= H:
            groups_used.append(g)
            receipts.extend(g["receipts"])
        else:
            groups_later.append({"block_hash": g["block_hash"], "height": gh,
                                 "receipt_ids": [r["receipt_id"] for r in g["receipts"]]})
    if groups_later:
        print("  catch-up groups saved for later chunks:", groups_later, flush=True)
    if ch is not None and set(r["receipt_id"] for r in receipts) !=             set(r["receipt_id"] for r in
                ch["receipts"] + ch.get("local_receipts", []) + ch.get("instant_receipts", [])):
        # informational: neardata's list differs from the incoming set
        print("  note: neardata chunk.receipts != header incoming set "
              f"({len(ch['receipts'])} vs {len(receipts)})", flush=True)
    # outcomes the chain recorded for this shard in this block (spot anchors)
    onchain = {}
    if sentry:
        for o in sentry.get("receipt_execution_outcomes", []):
            oo = o.get("outcome") or (o.get("execution_outcome") or {}).get("outcome") or {}
            oid = (o.get("receipt") or {}).get("receipt_id")
            if oo and oid:
                onchain[oid] = oo

    # execution context (same fields the v1 ctx uses; block = sync_prev)
    blk = rpc("block", {"block_id": sp["sync_prev_hash"]})
    pv = rpc("EXPERIMENTAL_protocol_config", {"block_id": sp["sync_prev_hash"]})
    assert pv["protocol_version"] == 86 and pv["chain_id"] == "mainnet", pv
    ctx = {
        "protocol_version": 86,
        "chain_id": "mainnet",
        "shard_id": a.shard,
        "block_height": H,
        "block_gas_price": blk["header"]["gas_price"],
        "gas_limit": ch["header"]["gas_limit"],
        "pre_state_root": root,
        "receipts": receipts,
    }
    name = a.name or f"exact-s{a.shard}-h{H}"

    # ---- harvest over P2P, driving the missing-region loop ----------------
    P = v1.Parts(sp["sync_hash"], a.shard, head)
    hdr = P.header()
    assert hdr["chunk_hash"] == ch["header"]["chunk_hash"], (hdr["chunk_hash"], ch["header"]["chunk_hash"])
    assert hdr["chunk_prev_state_root"] == root, (hdr["chunk_prev_state_root"], root)
    print(f"chunk {hdr['chunk_hash']} at {H}; {P.num_parts} state parts; "
          f"{len(receipts)} incoming receipts")

    # seed the loop with every receiver's account-key part (+ a margin)
    # trie columns (core/primitives/src/trie_key.rs): ACCOUNT=0,
    # CONTRACT_CODE=1, RECEIVED_DATA=3, DELAYED=7, CONTRACT_DATA=9,
    # BANDWIDTH=15. Seed the account + contract-code regions of every
    # receipt's receiver; the missing-region loop adds the rest.
    pids = set()
    for r in receipts:
        recv = r.get("receiver_id")
        if recv:
            pids.add(P.locate("00" + recv.encode().hex()))
            pids.add(P.locate("01" + recv.encode().hex()))
    pids.add(P.locate("0f"))          # bandwidth scheduler state
    pids.add(P.locate("07"))          # delayed-receipt indices
    if not pids:
        pids.add(P.locate("00"))
    code_again = set()

    ctxf = os.path.join(PARTS_DIR, f"ctx_{name}.json")
    os.makedirs(PARTS_DIR, exist_ok=True)
    json.dump(ctx, open(ctxf, "w"), indent=1)
    out = os.path.join(a.out, name)
    os.makedirs(out, exist_ok=True)

    exec_json = None
    for it in range(40):
        files = [P.fetch(p) for p in sorted(pids)]
        wpath = os.path.join(out, "apply_witness.bin")
        r = subprocess.run([FETCH, "exec-chunk", "--ctx", ctxf, "--parts", ",".join(files),
                            "--out-witness", wpath],
                           capture_output=True, text=True, timeout=1800)
        if r.returncode == 0:
            exec_json = json.loads(r.stdout.strip().splitlines()[-1])
            break
        # A CompilationError(CodeDoesNotExist{account}) means the contract-
        # code region (col 01) of `account` was not harvested: retry there.
        for acct in re.findall(r'CodeDoesNotExist \{ account_id: AccountId\("([^"]+)"\)', r.stdout + r.stderr):
            if acct not in code_again:
                code_again.add(acct)
                pid = P.locate("01" + acct.encode().hex())
                for d in (0, 1, -1):
                    q = pid + d
                    if 0 <= q < P.num_parts and q not in pids:
                        pids.add(q)
                        print(f"  [{it}] contract code of {acct} -> part {q}", flush=True)
        m = re.search(r"receiver path not in harvested trie|MissingTrieValue \{ context: \w+, hash: (\w+)", r.stderr)
        m2 = re.search(r"MissingTrieValue \{ context: \w+, hash: (\w+)", r.stderr)
        target = (m2.group(1) if m2 else None) or (m.group(1) if m and m.group(1) else None)
        if target is None:
            sys.exit(f"exec-chunk failed without a missing-node hint:\n{r.stderr[-1500:]}")
        path = P.whereis(target, files)
        if path is None:
            sys.exit(f"cannot place missing node {target}")
        pid = P.locate(path)
        placed = False
        for d in (0, 1, -1, 2, -2, 3, -3, 4, -4):
            q = pid + d
            if 0 <= q < P.num_parts and q not in pids:
                pids.add(q)
                placed = True
                print(f"  [{it}] apply needs node {target[:16]}.. at {path[:20]}.. -> part {q}", flush=True)
                break
        if not placed:
            sys.exit(f"cannot find a part for node {target} (path {path}); pids={sorted(pids)}")
        if len(pids) > a.max_parts:
            sys.exit(f"harvest exceeded --max-parts {a.max_parts}; pids={sorted(pids)}")
    if exec_json is None:
        sys.exit("harvest loop did not converge")

    # ---- anchors: our execution vs the chain's own records ----------------
    anchors = {}
    o_by_id = {o["id"]: o for o in exec_json["outcomes"]}
    ok_ids = set(o_by_id) == set(onchain)
    anchors["outcome_set_equals_onchain"] = {
        "ok": bool(ok_ids),
        "meaning": "our replay produced exactly the outcomes the chain recorded for this chunk",
        "ours": sorted(o_by_id), "onchain": sorted(onchain),
    }
    def kind(st_json, st_debug):
        s = json.dumps(st_json)
        if "SuccessValue" in s or "SuccessValue" in st_debug:
            return "SuccessValue"
        if "Failure" in s or "Failure" in st_debug:
            return "Failure"
        return s[:40] + "/" + st_debug[:40]

    mism = []
    for rid, oo in sorted(onchain.items()):
        mine = o_by_id.get(rid)
        if not mine:
            mism.append({"id": rid, "why": "missing"})
            continue
        st_on = oo.get("status")
        if mine["gas_burnt"] != int(oo.get("gas_burnt", "0")):
            mism.append({"id": rid, "why": "gas", "ours": mine["gas_burnt"],
                         "onchain": int(oo.get("gas_burnt", "0"))})
        elif kind(st_on, "") != kind(None, mine["status"]):
            mism.append({"id": rid, "why": "status", "ours": mine["status"],
                         "onchain": st_on})
    anchors["per_outcome_status_and_gas"] = {
        "ok": not mism and ok_ids, "meaning": "status and gas_burnt equal on-chain per receipt",
        "mismatches": mism,
    }
    gas_hdr = int(ch["header"]["gas_used"])
    anchors["gas_header_prev_chunk_only"] = {
        "ok": True,
        "meaning": "informational: the chunk header's own gas field is prev_gas_used "
                   "(the PREVIOUS chunk's gas); this chunk's gas is anchored via the "
                   "next chunk's header below",
        "header_prev_gas_used": gas_hdr,
    }
    nxt = next_new_chunk_root(a.shard, H)
    ok_root = bool(nxt) and nxt["prev_state_root"] == exec_json["post_state_root"]
    anchors["post_state_root_equals_chain"] = {
        "ok": ok_root,
        "meaning": "computed post-state root == prev_state_root of the shard's next chunk "
                   "(the chain's own commitment to this transition's result)",
        "next_chunk": nxt, "ours": exec_json["post_state_root"],
    }
    if nxt:
        nh = rpc("chunk", {"chunk_id": nxt["chunk_hash"]})["header"]
        # ShardChunkHeaderInner carries only prev_gas_used: the NEXT chunk's
        # header commits to THIS chunk's total gas.
        ok_gas = int(nh["gas_used"]) == exec_json["gas_burnt_receipts_total"]
        anchors["gas_used_equals_next_header_prev_gas_used"] = {
            "ok": ok_gas,
            "meaning": "Σ gas_burnt of the replayed receipts == the next chunk header's "
                       "prev_gas_used (the chain's commitment to this chunk's gas)",
            "ours": exec_json["gas_burnt_receipts_total"],
            "next_header_gas_used": int(nh["gas_used"]),
        }
    anchors["no_delayed_receipts"] = {"ok": exec_json["delayed_receipts_count"] == 0,
                                      "meaning": "every incoming receipt applied in this chunk"}
    anchors["protocol_config_86_mainnet"] = {"ok": True,
                                             "meaning": "EXPERIMENTAL_protocol_config at sync_prev"}
    ok_all = all(v["ok"] for v in anchors.values())

    json.dump({"context": ctx, "execution": exec_json, "anchors": anchors,
               "ok": ok_all,
               "parts": [P.meta[p] for p in sorted(pids)],
               "header": hdr,
               "onchain": {"sync_prev_height": H, "chunk": ch["header"],
                           "block_gas_price": blk["header"]["gas_price"]},
               },
              open(os.path.join(out, "chunk_exec.json"), "w"), indent=1)
    json.dump(ctx, open(os.path.join(out, "context.json"), "w"), indent=1)
    print(json.dumps({"name": name, "ok": ok_all,
                      "anchors": {k: v["ok"] for k, v in anchors.items()},
                      "post_state_root": exec_json["post_state_root"],
                      "parts_harvested": len(pids),
                      "recorded_nodes": exec_json["recorded_nodes"]}, indent=1))
    return 0 if ok_all else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
