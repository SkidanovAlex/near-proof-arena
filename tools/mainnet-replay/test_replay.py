#!/usr/bin/env python3
"""Self-checks for tools/mainnet-replay/replay.py: predicate/classification
behaviour on synthetic chunk feature records (no network).

    python3 tools/mainnet-replay/test_replay.py
"""
from __future__ import annotations

import base64
import json
import os
import sys
import tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import replay  # noqa: E402


def feats(**kw) -> dict:
    base = {
        "shard_id": 0, "height": 1, "n_transactions": 0, "tx_results": [],
        "n_receipts": 0, "n_cross_receipts": 0, "receipt_action_kinds": [],
        "n_receipt_action_kinds": 0, "n_callbacks": 0,
        "validator_proposals": 0, "epoch_changed_in_window": False,
        "delayed_gas": 0, "buffered_gas": 0, "fc_gas": 0,
        "fc_gas_source": "none", "shard_missed_prev_block": False,
        "implicit_created": False, "n_function_call_outcomes": 0,
    }
    base.update(kw)
    return base


def expect(class_, f) -> None:
    got = replay.classify(f)
    assert got == class_, f"{f} -> {got}, want {class_}"


def main() -> int:
    g_half = replay.G_ALPHA // 2
    # D0 family
    expect("d0-quiet", feats())
    expect("d0-transfers", feats(n_receipts=2, n_cross_receipts=2,
                                 receipt_action_kinds=["Transfer"]))
    expect("d0-missing", feats(shard_missed_prev_block=True))
    expect("d0-missing", feats(implicit_created=True))
    # D1: transactions, transfer-only receipts
    expect("d1-transfers", feats(n_transactions=1, tx_results=["ok"],
                                 receipt_action_kinds=["Transfer"], n_receipts=1,
                                 n_cross_receipts=1))
    expect("d1-mixed", feats(n_transactions=2, tx_results=["ok", "fail"]))
    # receipts-only chunks satisfy BOTH d0-transfers and d1-receipts; the
    # partition puts them in d0-transfers, the predicate view keeps both.
    r = feats(n_receipts=1, n_cross_receipts=1, receipt_action_kinds=["Transfer"])
    expect("d0-transfers", r)
    p = replay.predicates(r)
    assert p["d0-transfers"] and p["d1-receipts"]
    # D2
    # D2 — deploy chunks satisfy BOTH d2-actions and d3-nonwasm predicates
    # (overlap by design); the partition puts them in d2-actions (lowest tier).
    r = feats(n_receipts=1, receipt_action_kinds=["DeployContract"])
    expect("d2-actions", r)
    p = replay.predicates(r)
    assert p["d2-actions"] and p["d3-nonwasm"]
    expect("d2-actions", feats(n_receipts=1, receipt_action_kinds=["Stake"]))
    expect("d2-queues", feats(delayed_gas=1))
    expect("d2-epoch", feats(validator_proposals=3))
    # D3: wasm executed via an unwrapped Delegate(FunctionCall)
    expect("d3-calls", feats(n_receipts=1, receipt_action_kinds=["FunctionCall"],
                             n_function_call_outcomes=1, fc_gas=1_000_000_000))
    expect("d3-calls", feats(n_receipts=1, receipt_action_kinds=["Delegate"],
                             n_function_call_outcomes=1,
                             fc_gas=replay.G_ALPHA // 2 - 1))
    expect("d3-callbacks", feats(n_receipts=1, receipt_action_kinds=["FunctionCall"],
                                 n_function_call_outcomes=1, n_callbacks=1,
                                 fc_gas=1_000_000_000))
    expect("d3-maxgas", feats(n_receipts=1, receipt_action_kinds=["FunctionCall"],
                              n_function_call_outcomes=1, fc_gas=g_half))
    expect("d3-maxgas", feats(fc_gas=replay.G_ALPHA))
    # a FunctionCall receipt listed for the chunk counts as WASM traffic even
    # without a recorded outcome (postponed/deferred execution is rare and
    # the receipt kind alone is the honest observable here)
    expect("d3-calls", feats(n_receipts=1, receipt_action_kinds=["FunctionCall"]))
    # precedence: maxgas beats callbacks beats calls; epoch beats queues
    expect("d3-maxgas", feats(n_receipts=1, receipt_action_kinds=["FunctionCall"],
                              n_function_call_outcomes=1, n_callbacks=2,
                              fc_gas=g_half, validator_proposals=1))
    # weights: renormalization is exact and matches arena-types' rule
    w = replay.renormalize_ppm({"a": 1, "b": 1, "c": 1})
    assert w == {"a": 333_334, "b": 333_333, "c": 333_333}  # ties by position
    w = replay.renormalize_ppm({"a": 999_999})
    assert w == {"a": 1_000_000}
    # wilson: k=0 -> zero-width at 0; k=n -> zero-width at 1
    assert replay.wilson(0, 10) == (0.0, 0.0) or replay.wilson(0, 10)[0] == 0.0
    lo, hi = replay.wilson(5, 10)
    assert lo < 0.5 < hi and 0 <= lo and hi <= 1
    # percentile picks within the sorted row set
    assert replay.percentile([1, 2, 3, 4], 0.5) in (2, 3)
    assert replay.percentile([], 0.5) is None

    # end-to-end on a synthetic neardata-style block (shapes from mainnet):
    # shard with a null chunk (missing), a FunctionCall receipt executed via a
    # Delegate wrapper, tx outcome statuses.
    blk = {
        "block": {"header": {"height": 7,
                             "epoch_id": base64.b64encode(b"e1").decode()}},
        "shards": [
            {"chunk": None, "shard_id": 4,
             "receipt_execution_outcomes": [], "state_changes": []},
            {"chunk": {
                "header": {"shard_id": 5, "height_included": 7,
                           "validator_proposals": [],
                           "congestion_info": {"delayed_receipts_gas": "0",
                                               "buffered_receipts_gas": "0"}},
                "transactions": [],
                "receipts": [{"receipt": {"Action": {
                    "actions": [{"Delegate": {"delegate_action": {"actions": [
                        {"FunctionCall": {"method_name": "m"}}]}}}],
                    "output_data_receivers": [{"data_id": "d1"}],
                    "is_promise_yield": False}}}],
                "local_receipts": [], "instant_receipts": []},
             "receipt_execution_outcomes": [
                 {"tx_hash": None,
                  "receipt": {"receipt": {"Action": {"actions": [
                      {"Delegate": {"delegate_action": {"actions": [
                          {"FunctionCall": {}}]}}}]}}},
                  "outcome": {"status": {"SuccessValue": ""},
                              "gas_burnt": 5_000_000_000_000,
                              "metadata": {"gas_profile": [
                                  {"cost_category": "WASM_HOST_COST",
                                   "gas_used": "1200000000000"},
                                  {"cost_category": "ACTION_COST",
                                   "gas_used": "100000000000"}]}}},
             ],
             "state_changes": []},
        ],
    }
    with tempfile.TemporaryDirectory() as d:
        cache = os.path.join(d, "blocks")
        os.makedirs(cache)
        with open(os.path.join(cache, "7.json"), "w") as fh:
            json.dump(blk, fh)
        state = os.path.join(d, "state.json")
        with open(state, "w") as fh:
            json.dump({"next_height": 7, "epoch_id": None, "prev_included": {}}, fh)
        samples = os.path.join(d, "samples.jsonl")

        class A:  # minimal argv namespace
            from_height = 7
            blocks = 1
            out = d
        replay.sample(A)
        rows = [json.loads(l) for l in open(samples)]
        assert len(rows) == 1, rows
        f = rows[0]
        assert f["shard_id"] == 5
        assert f["fc_gas_source"] == "profile"
        assert f["fc_gas"] == 1_300_000_000_000  # whole profile summed
        assert f["n_callbacks"] == 1  # output_data_receivers nonempty
        assert f["class"] == "d3-callbacks", f["class"]
    print("test_replay: all checks passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
