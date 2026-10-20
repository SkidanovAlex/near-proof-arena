#!/usr/bin/env python3
"""Measured workload-class mix and G_alpha rows from NEAR mainnet chunks.

HANDOVER §8 ("Mainnet replay: real class weights and a measured G_alpha"),
STATUS-V3-D3 §4 ("Measured mainnet class weights ... to replace the ASSUMED
ones"; "G_alpha is a checkpoint value ... re-fix it ... from the measured
rows").

This is a *measurement*, not an execution replay: classifying a chunk into
the workload classes of `near-chunk-v3` needs only observables that public
chain data carries. No trie node, witness or challenge artifact is touched,
and no signed draft is regenerated (CONTRACTS §11: measured weights "come as
a versioned successor with MEASURED").

Data source: `https://mainnet.neardata.xyz/v0/block/H` (public, no
credentials; one JSON document per block with every shard's chunk, receipts,
transactions, receipt execution outcomes and state changes). Requests are
throttled with back-off on HTTP 429; `state.json` makes runs resumable; each
block is cached on disk.

Per chunk the classifier reads explicit, decidable observables (each recorded
in `samples.jsonl`; the report states which predicate used which field):

  transactions           chunk.transactions
  tx succeeded           receipt_execution_outcomes with tx_hash; status
  applied receipts       chunk receipts / local_receipts / instant_receipts
  cross-shard receipt    receipt listed for the chunk (local_receipts are
                         same-shard)
  receipt action kinds   receipt.receipt.Action.actions[].<kind>
  callbacks/yields       ActionReceipt.output_data_receivers nonempty, or
                         is_promise_yield, or a Data receipt (promise results,
                         yield resumes)
  validator updates      chunk.header.validator_proposals nonempty
  epoch boundary         block.header.epoch_id differs from the previous
                         sampled block's (only exact at window starts every
                         epoch; boundaries inside the window are detected by
                         consecutive blocks)
  delayed/buffered       chunk.header.congestion_info.delayed_receipts_gas /
                         buffered_receipts_gas > 0 (nonempty queue analogue)
  implicit creation      state_changes account_update on an implicit-format
                         account id (64 hex chars)
  function-call gas      Σ of the WHOLE metadata.gas_profile of each
                         FunctionCall-receipt outcome ("profile": the VM
                         burnt gas = wasm_gas + actions + ext, the quantity
                         oracle/v3-d3/src/d3.rs sums into
                         `fc_gas_burnt_for_function_call`), else that
                         outcome's gas_burnt ("outcome": includes wiring
                         gas, an overestimate). This is the chunk gas axis
                         of `near-chunk-v3` (the d3-maxgas predicate, G_alpha).

Reporting (two honest views, because the class predicates overlap across
tiers by design — D0 ⊂ D1 ⊂ D2 ⊂ D3a — while weights must partition):

  predicate frequencies  each class's predicate measured independently over
                         all chunks (with Wilson 95% intervals); overlapping
                         by construction.
  weights_ppm            a partition for a successor's sampling weights,
                         precedence lowest tier first (the ladder's order):
                         d0-* (no transactions, transfer-only traffic) >
                         d1-* (transactions, transfer-only receipts) >
                         d2-* (non-WASM actions/queues/epoch) >
                         d3-* (function-call gas / callbacks / deploys),
                         with class_of's inner precedence (maxgas >
                         callbacks > calls > nonwasm; epoch > queues >
                         actions; receipts > transfers > mixed; missing).
                         Receipts-only chunks without transactions are
                         assigned to d0-transfers; the same real chunks also
                         satisfy the d1-receipts predicate, whose standalone
                         frequency is in the predicate view.

Outputs (docs/e2e-results/mainnet-replay-2026-10/):
  samples.jsonl   one record per classified chunk (auditable)
  weights.json    counts, both views, Wilson intervals, renormalized ppm
  gas.json        per-chunk function-call gas percentiles vs G_alpha

Usage:
  replay.py sample [--from-height H] --blocks N [--out DIR]
  replay.py report [--out DIR]
"""
from __future__ import annotations

import argparse
import base64
import json
import math
import os
import sys
import time
import urllib.error
import urllib.request

BLOCK_URL = "https://mainnet.neardata.xyz/v0/block/{}"
RPC_STATUS_URL = "https://rpc.mainnet.fastnear.com"
# G_alpha = 2^22 * 822,756 (NearSpecV3.D3.gAlpha; the e.g_alpha restriction).
G_ALPHA = 2**22 * 822756
MIN_REQUEST_INTERVAL = 0.30  # politeness: >= 0.25 s, docs/HISTORICAL_REPLAY.md §1
CLASSES = [
    "d0-quiet", "d0-transfers", "d0-missing",
    "d1-transfers", "d1-mixed", "d1-receipts",
    "d2-actions", "d2-queues", "d2-epoch",
    "d3-calls", "d3-callbacks", "d3-nonwasm", "d3-maxgas",
]


def fetch(url: str, tries: int = 8) -> bytes:
    delay = MIN_REQUEST_INTERVAL
    last: Exception | None = None
    for i in range(tries):
        try:
            req = urllib.request.Request(url, headers={"User-Agent": "near-proof-arena-replay/1"})
            with urllib.request.urlopen(req, timeout=60) as r:
                return r.read()
        except urllib.error.HTTPError as e:
            if e.code == 404:
                raise
            last = e
        except (urllib.error.URLError, TimeoutError) as e:
            last = e
        if i + 1 < tries:
            time.sleep(delay)
            delay = min(delay * 2, 30.0)
    raise RuntimeError(f"unreachable: {url}: {last}")


def get_block(height: int, cache_dir: str) -> dict | None:
    """Fetch (and cache) one block document; None past the chain tip (404)."""
    os.makedirs(cache_dir, exist_ok=True)
    path = os.path.join(cache_dir, f"{height}.json")
    if os.path.exists(path) and os.path.getsize(path) > 0:
        with open(path) as f:
            try:
                return json.load(f)
            except json.JSONDecodeError:
                os.unlink(path)
    try:
        raw = fetch(BLOCK_URL.format(height))
    except urllib.error.HTTPError as e:
        if e.code == 404:
            return None
        raise
    tmp = path + ".tmp"
    with open(tmp, "wb") as f:
        f.write(raw)
    os.replace(tmp, path)
    time.sleep(MIN_REQUEST_INTERVAL)
    if raw.strip() in (b"null", b""):
        # neardata answers 200 with a JSON `null` for heights it does not
        # have (observed on mainnet): a gap, not the chain tip. Cached, so a
        # resume does not refetch it.
        return None
    return json.loads(raw)


def fetch_tip() -> int:
    body = json.dumps({"jsonrpc": "2.0", "id": "x", "method": "status", "params": []}).encode()
    req = urllib.request.Request(RPC_STATUS_URL, data=body,
                                 headers={"Content-Type": "application/json"})
    with urllib.request.urlopen(req, timeout=30) as r:
        st = json.load(r)
    return st["result"]["sync_info"]["latest_block_height"]


# ---- per-chunk feature extraction ------------------------------------------

def receipt_action_kinds(receipt: dict) -> list[str]:
    """Effective action kinds: a Delegate action is unwrapped to the signed
    inner action (Delegate(Transfer) executes as a Transfer,
    Delegate(FunctionCall) executes WASM like any FunctionCall; the wrapper
    only changes signature checking)."""
    rr = receipt.get("receipt", {})
    a = rr.get("Action")
    if not a:
        return []
    kinds = []
    for x in a.get("actions", []):
        if not (isinstance(x, dict) and x):
            continue
        k = next(iter(x.keys()))
        inner = (x.get("Delegate") or {}).get("delegate_action", {}).get("actions", [])
        if isinstance(inner, list) and inner:
            for y in inner:
                if isinstance(y, dict) and y:
                    kinds.append(next(iter(y.keys())))
        else:
            kinds.append(k)
    return kinds


def is_callbackish(receipt: dict) -> bool:
    """promise_then registrations / promise_and joins / yields / resumes."""
    rr = receipt.get("receipt", {})
    if "Data" in rr:
        return True  # data receipts carry promise results / yield resumes
    a = rr.get("Action")
    if not a:
        return False
    return bool(a.get("is_promise_yield")) or bool(a.get("output_data_receivers"))


def status_ok(status) -> bool:
    if isinstance(status, dict):
        return "SuccessValue" in status or "SuccessReceiptId" in status
    return status in ("SuccessValue", "SuccessReceiptId")


def is_implicit_account(acc: str) -> bool:
    return len(acc) == 64 and all(c in "0123456789abcdefABCDEF" for c in acc)


def chunk_features(shard: dict, epoch_changed: bool, shard_missed_prev: bool,
                   implicit_created: bool) -> dict:
    ch = shard["chunk"]
    hdr = ch["header"]
    conges = hdr.get("congestion_info") or {}
    receipts = list(ch.get("receipts") or [])
    local = list(ch.get("local_receipts") or [])
    instant = list(ch.get("instant_receipts") or [])
    applied = receipts + local + instant

    tx_results: list[str] = []
    fc_gas = 0
    fc_gas_source = "none"
    n_fc_outcomes = 0
    for o in shard.get("receipt_execution_outcomes") or []:
        oo = o.get("outcome") or (o.get("execution_outcome") or {}).get("outcome") or {}
        if not oo:
            continue
        if o.get("tx_hash") is not None:
            tx_results.append("ok" if status_ok(oo.get("status")) else "fail")
        rec = o.get("receipt") or {}
        if "FunctionCall" not in receipt_action_kinds(rec):
            continue
        n_fc_outcomes += 1
        prof = (oo.get("metadata") or {}).get("gas_profile")
        if prof:
            fc_gas += sum(int(e.get("gas_used", "0")) for e in prof)
            fc_gas_source = "profile"
        else:
            fc_gas += int(oo.get("gas_burnt", "0"))
            if fc_gas_source != "profile":
                fc_gas_source = "outcome"

    kinds = [k for r in applied for k in receipt_action_kinds(r)]
    return {
        "shard_id": hdr["shard_id"],
        "height": hdr["height_included"],
        "n_transactions": len(ch.get("transactions") or []),
        "tx_results": tx_results,
        "n_receipts": len(applied),
        "n_cross_receipts": len(receipts),
        "receipt_action_kinds": sorted(set(kinds)),
        "n_receipt_action_kinds": len(kinds),
        "n_callbacks": sum(1 for r in applied if is_callbackish(r)),
        "validator_proposals": len(hdr.get("validator_proposals") or []),
        "epoch_changed_in_window": epoch_changed,
        "delayed_gas": int(conges.get("delayed_receipts_gas", "0") or 0),
        "buffered_gas": int(conges.get("buffered_receipts_gas", "0") or 0),
        "fc_gas": fc_gas,
        "fc_gas_source": fc_gas_source,
        "shard_missed_prev_block": shard_missed_prev,
        "implicit_created": implicit_created,
        "n_function_call_outcomes": n_fc_outcomes,
    }


# ---- classification ----------------------------------------------------------

def predicates(f: dict) -> dict[str, bool]:
    """Every class's predicate, measured independently (overlapping)."""
    txs = f["n_transactions"] > 0
    tr_ok = f["tx_results"] and all(x == "ok" for x in f["tx_results"])
    tr_any_fail = any(x == "fail" for x in f["tx_results"])
    kinds = f["receipt_action_kinds"]
    transfer_only = set(kinds) <= {"Transfer"}
    delayed = f["delayed_gas"] > 0 or f["buffered_gas"] > 0
    epochish = f["epoch_changed_in_window"] or f["validator_proposals"] > 0
    wasm = "FunctionCall" in kinds or f["n_function_call_outcomes"] > 0
    deploys = "DeployContract" in kinds
    traffic = txs or f["n_receipts"] > 0
    quiet_ish = not txs and not delayed and not epochish and not wasm and not deploys
    implicit = f["shard_missed_prev_block"] or f["implicit_created"]
    return {
        # d0-*: no transactions, transfer-only receipts (or nothing), quiet.
        "d0-quiet": not txs and f["n_receipts"] == 0 and quiet_ish,
        "d0-transfers": not txs and transfer_only and f["n_cross_receipts"] > 0
                        and not delayed and not epochish and not wasm and not deploys,
        "d0-missing": not txs and implicit and transfer_only
                      and not wasm and not deploys,
        # d1-*: transactions, transfer-only receipt traffic.
        "d1-transfers": txs and transfer_only and tr_ok and not wasm and not delayed
                        and not epochish and not deploys,
        "d1-mixed": txs and transfer_only and tr_any_fail and not wasm and not delayed
                    and not epochish and not deploys,
        "d1-receipts": not txs and transfer_only and f["n_cross_receipts"] > 0
                       and not delayed and not epochish and not wasm and not deploys,
        # d2-*: no WASM executed; non-Transfer action kinds (incl. deploys),
        # queue or epoch features.
        "d2-actions": not wasm and not delayed and not epochish and traffic
                      and not set(kinds) <= {"Transfer"},
        "d2-queues": not wasm and delayed,
        "d2-epoch": not wasm and epochish,
        # d3-*: WASM executed (or the d3-nonwasm contract-state remainder).
        "d3-calls": wasm and f["fc_gas"] * 2 < G_ALPHA and f["n_callbacks"] == 0,
        "d3-callbacks": wasm and f["n_callbacks"] > 0 and f["fc_gas"] * 2 < G_ALPHA,
        "d3-nonwasm": not wasm and deploys,
        "d3-maxgas": f["fc_gas"] * 2 >= G_ALPHA,
    }


def classify(f: dict) -> str:
    """One class per chunk: the partition view (see module docstring).

    Lowest tier first (the ladder's order), then class_of's inner precedence;
    receipts-only chunks land in d0-transfers (they also satisfy the
    d1-receipts predicate, measured separately in `predicates`)."""
    p = predicates(f)
    if p["d3-maxgas"]:
        return "d3-maxgas"
    if p["d3-callbacks"]:
        return "d3-callbacks"
    if p["d3-calls"]:
        return "d3-calls"
    if p["d2-epoch"]:
        return "d2-epoch"
    if p["d2-queues"]:
        return "d2-queues"
    if p["d2-actions"]:
        return "d2-actions"
    if p["d3-nonwasm"]:
        return "d3-nonwasm"
    if f["n_transactions"] > 0:
        return "d1-transfers" if p["d1-transfers"] else "d1-mixed"
    if f["shard_missed_prev_block"] or f["implicit_created"]:
        return "d0-missing"
    if p["d1-receipts"]:
        return "d0-transfers"
    return "d0-quiet"


# ---- crawling ----------------------------------------------------------------

def shard_entry_id(s: dict) -> int:
    """A shard entry's id; `chunk` is null when the shard had no chunk
    included in that block (the observable behind the `d0-missing`
    implicit-transition analogue)."""
    c = s.get("chunk")
    return s["shard_id"] if c is None else c["header"]["shard_id"]


def shard_ids_of(block: dict) -> list[int]:
    return [shard_entry_id(s) for s in block.get("shards", [])]


def implicit_creations(block: dict) -> dict[int, bool]:
    out: dict[int, bool] = {}
    for s in block.get("shards", []):
        sid = shard_entry_id(s)
        created = False
        for sc in s.get("state_changes") or []:
            if sc.get("type") != "account_update":
                continue
            acc = (sc.get("change") or {}).get("account_id", "")
            if is_implicit_account(acc):
                created = True
                break
        out[sid] = created
    return out


def load_state(path: str, from_height: int | None) -> dict:
    if os.path.exists(path):
        with open(path) as f:
            return json.load(f)
    return {"next_height": from_height, "epoch_id": None, "prev_included": {}}


def sample(args) -> int:
    out_dir = args.out
    os.makedirs(out_dir, exist_ok=True)
    cache = os.path.join(out_dir, "blocks")
    state_path = os.path.join(out_dir, "state.json")
    samples_path = os.path.join(out_dir, "samples.jsonl")
    state = load_state(state_path, args.from_height)
    resume = os.path.exists(state_path)
    if state["next_height"] is None:
        state["next_height"] = fetch_tip() - 5  # a few blocks behind the tip
    start = state["next_height"]
    end = start + args.blocks
    # Prev-block chunk presence for the `d0-missing` analogue: unknown for the
    # first block of a window (assume every shard included; recorded as such).
    prev_included: dict[int, bool] = {int(k): v for k, v in (state["prev_included"] or {}).items()}
    epoch_prev = state["epoch_id"]

    out = open(samples_path, "a" if resume else "w")
    n_done = 0
    try:
        gaps = 0
        for h in range(start, end):
            block = get_block(h, cache)
            if block is None:
                # Past the tip (404) or a gap in the feed (200 + `null`):
                # either way no chunk data at this height. A tip 404 stops
                # the crawl; a gap advances and marks every known shard as
                # having had no chunk in this block.
                if fetch_tip() - h <= 2:
                    print(f"caught up with the tip at height {h}")
                    break
                gaps += 1
                if gaps > 50:
                    print("too many feed gaps; stopping early", flush=True)
                    break
                for sid in list(prev_included):
                    prev_included[sid] = False
                state["next_height"] = h + 1
                n_done += 1
                continue
            epoch = base64.b64decode(block["block"]["header"]["epoch_id"]).hex()
            entries = block.get("shards", [])
            included = {shard_entry_id(s) for s in entries if s.get("chunk")}
            impl = implicit_creations(block)
            epoch_changed = epoch_prev is not None and epoch != epoch_prev
            for s in entries:
                sid = shard_entry_id(s)
                if s.get("chunk") is None:
                    # No chunk included this block: record the miss, no sample.
                    prev_included[sid] = False
                    continue
                f = chunk_features(
                    s,
                    epoch_changed=epoch_changed,
                    shard_missed_prev=(sid in prev_included) and not prev_included[sid],
                    implicit_created=impl.get(sid, False),
                )
                f["class"] = classify(f)
                out.write(json.dumps(f, separators=(",", ":")) + "\n")
            for sid in included:
                prev_included[sid] = True
            for sid in list(prev_included):
                if sid not in included:
                    prev_included[sid] = False
            epoch_prev = epoch
            state["next_height"] = h + 1
            n_done += 1
            if n_done % 25 == 0:
                state["epoch_id"] = epoch_prev
                state["prev_included"] = {str(k): v for k, v in prev_included.items()}
                with open(state_path, "w") as sf:
                    json.dump(state, sf)
                out.flush()
                print(f"... height {h} ({n_done}/{args.blocks} blocks)", flush=True)
    finally:
        state["epoch_id"] = epoch_prev
        state["prev_included"] = {str(k): v for k, v in prev_included.items()}
        with open(state_path, "w") as sf:
            json.dump(state, sf)
        out.close()
    print(f"sampled heights [{start}, {state['next_height'] - 1}]; next resume point "
          f"{state['next_height']}")
    return 0


# ---- reporting ---------------------------------------------------------------

def wilson(k: int, n: int, z: float = 1.959963984540054) -> tuple[float, float]:
    if n == 0:
        return (0.0, 0.0)
    p = k / n
    d = 1 + z * z / n
    c = (p + z * z / (2 * n)) / d
    h = z * math.sqrt(p * (1 - p) / n + z * z / (4 * n * n)) / d
    return (max(0.0, c - h), min(1.0, c + h))


def renormalize_ppm(weights: dict[str, int]) -> dict[str, int] | None:
    total = sum(weights.values())
    if total == 0:
        return None
    out = {k: w * 1_000_000 // total for k, w in weights.items()}
    # Remainder distribution identical to arena-types::renormalize_ppm:
    # largest remainder first, ties by position (dict order here).
    order = sorted(weights, key=lambda k: (-(weights[k] * 1_000_000 % total),
                                           list(weights).index(k)))
    short = 1_000_000 - sum(out.values())
    for k in order[:short]:
        out[k] += 1
    return out


def percentile(sorted_rows: list[int], p: float) -> int | None:
    if not sorted_rows:
        return None
    i = min(len(sorted_rows) - 1, max(0, round(p * (len(sorted_rows) - 1))))
    return sorted_rows[i]


def report(args) -> int:
    out_dir = args.out
    rows = [json.loads(l) for l in open(os.path.join(out_dir, "samples.jsonl")) if l.strip()]
    heights = sorted({r["height"] for r in rows})
    n_chunks = len(rows)
    if n_chunks == 0:
        print("no samples; run `sample` first", file=sys.stderr)
        return 1

    # Partition view (one class per chunk; the sampling-weight analogue).
    counts = {c: 0 for c in CLASSES}
    for r in rows:
        counts[r["class"]] += 1
    weights = renormalize_ppm(counts)
    cis = {c: wilson(counts[c], n_chunks) for c in CLASSES}

    # Predicate view (overlapping frequencies).
    pred_counts = {c: 0 for c in CLASSES}
    for r in rows:
        pr = predicates(r)
        for c in CLASSES:
            if pr[c]:
                pred_counts[c] += 1
    pred_cis = {c: wilson(pred_counts[c], n_chunks) for c in CLASSES}

    gas_rows = sorted(r["fc_gas"] for r in rows)
    fc_rows = [r for r in rows if r["fc_gas"] > 0]
    fc_sorted = sorted(r["fc_gas"] for r in fc_rows)
    gas_report = {
        "definition": "Per chunk: Σ of the whole metadata.gas_profile of each "
                      "FunctionCall-receipt outcome ('profile'; the VM burnt gas "
                      "wasm_gas + actions + ext — the quantity "
                      "oracle/v3-d3/src/d3.rs sums into "
                      "fc_gas_burnt_for_function_call), else that outcome's "
                      "gas_burnt ('outcome'; includes wiring gas, an overestimate).",
        "gas_source_chunks": {
            "profile": sum(1 for r in rows if r["fc_gas_source"] == "profile"),
            "outcome": sum(1 for r in rows if r["fc_gas_source"] == "outcome"),
            "none": sum(1 for r in rows if r["fc_gas_source"] == "none"),
        },
        "chunks": n_chunks,
        "g_alpha": G_ALPHA,
        "percentiles_all_chunks": {f"p{int(p * 100)}": percentile(gas_rows, p)
                                   for p in (0.5, 0.9, 0.99, 0.999)},
        "max_all_chunks": gas_rows[-1] if gas_rows else None,
        "percentiles_chunks_with_function_calls": {
            f"p{int(p * 100)}": percentile(fc_sorted, p) for p in (0.5, 0.9, 0.99, 0.999)},
        "max_chunks_with_function_calls": fc_sorted[-1] if fc_sorted else None,
        "share_at_or_above_half_g_alpha_ppm": (
            round(1_000_000 * sum(1 for g in gas_rows if g * 2 >= G_ALPHA) / n_chunks)),
        "window_heights": [heights[0], heights[-1]],
        "note": "Rows feed the operator's G_alpha checkpoint decision "
                "(STATUS-V3-D3 §4); re-fixing the value is a user decision.",
    }

    weights_report = {
        "schema": "near-arena-class-weights-measured-v1",
        "challenge": "near-chunk-v3",
        "status": "MEASURED (research artifact; no signed draft is changed; a successor "
                  "challenge adopts weights per CONTRACTS §11)",
        "window": {"heights": [heights[0], heights[-1]], "blocks": len(heights),
                   "chunks": n_chunks},
        "predicate_note": "Explicit mainnet observables per chunk; documented analogues of "
                          "oracle/v3-d1/src/arena.rs class_of (tools/mainnet-replay/replay.py). "
                          "`counts`/`weights_ppm` partition chunks (lowest tier first; "
                          "receipts-only chunks without transactions are d0-transfers, and the "
                          "same chunks also satisfy d1-receipts); `predicate_frequencies` "
                          "measures every class's predicate independently with overlaps.",
        "counts": counts,
        "weights_ppm": weights,
        "wilson95_partition": {c: [round(lo, 6), round(hi, 6)] for c, (lo, hi) in cis.items()},
        "predicate_frequencies": pred_counts,
        "predicate_wilson95": {c: [round(lo, 6), round(hi, 6)]
                               for c, (lo, hi) in pred_cis.items()},
    }
    with open(os.path.join(out_dir, "weights.json"), "w") as f:
        json.dump(weights_report, f, indent=1)
    with open(os.path.join(out_dir, "gas.json"), "w") as f:
        json.dump(gas_report, f, indent=1)
    print(json.dumps({"counts": counts, "weights_ppm": weights}, indent=1))
    print(json.dumps(gas_report["percentiles_all_chunks"], indent=1))
    print(json.dumps(gas_report["percentiles_chunks_with_function_calls"], indent=1))
    return 0


def main(argv: list[str]) -> int:
    p = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    sub = p.add_subparsers(dest="cmd", required=True)
    s = sub.add_parser("sample", help="crawl a window of blocks and classify chunks")
    s.add_argument("--from-height", type=int, default=None, dest="from_height",
                   help="first height (default: 5 blocks behind the current tip)")
    s.add_argument("--blocks", type=int, default=400)
    s.add_argument("--out", default="docs/e2e-results/mainnet-replay-2026-10")
    s.set_defaults(fn=sample)
    r = sub.add_parser("report", help="aggregate samples into weights.json + gas.json")
    r.add_argument("--out", default="docs/e2e-results/mainnet-replay-2026-10")
    r.set_defaults(fn=report)
    args = p.parse_args(argv)
    return args.fn(args)


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
