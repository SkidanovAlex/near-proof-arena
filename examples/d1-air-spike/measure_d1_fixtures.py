#!/usr/bin/env python3
"""D1-AIR design spike: per-fixture workload measurements for the D1 cost model
(docs/zk-formal/V3-D1-DESIGN.md §5).

For every case directory it runs the independent Python D1 checker
(oracle/tools/spec_check_v3_d1.py, unmodified) with its tries replaced by the recording
trie of the D0a checker (spec_check_v3_d0a.RecTrie: records every key read), and reports

* transactions, signature checks (non-duplicate, non-expired), candidates (transactions that
  reach the signer-account read, step 5), successes, local receipts, new transactions,
  incoming receipts;
* the unfolded pre-trie bytes of the main transition (A7's pre term, `unfold_pre`) along all
  keys read, and along the keys read minus the transaction keys (account + access key of each
  candidate signer): the difference is the transactions' marginal A7 cost.

Usage: measure_d1_fixtures.py CASE_DIR... > out.jsonl   (prints a summary to stderr)
"""
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
TOOLS = os.path.join(HERE, "..", "..", "oracle", "tools")
sys.path.insert(0, TOOLS)

import spec_check_v3_d0a as d0a  # noqa: E402  (installs RecTrie into spec_check_v3)
import spec_check_v3_d1 as d1  # noqa: E402
from v3lib.prim import nibbles  # noqa: E402

d1.PartialTrie = d0a.RecTrie  # the D1 checker imported the name directly

COL_ACCOUNT = d1.COL_ACCOUNT
COL_ACCESS_KEY = d1.COL_ACCESS_KEY


_W = []
_orig_decode = d1.decode_state_witness_d1


def _rec_decode(b):
    w = _orig_decode(b)
    _W.append(w)
    return w


d1.decode_state_witness_d1 = _rec_decode


def tx_keys(txs):
    """The keys step 5/6 reads for each transaction (signer account, access key)."""
    keys = set()
    for t in txs:
        keys.add(bytes([COL_ACCOUNT]) + t.signer)
        keys.add(bytes([COL_ACCESS_KEY]) + t.signer + bytes([COL_ACCESS_KEY]) + bytes([0]) + t.pk)
    return keys


def measure(case):
    meta = json.load(open(os.path.join(case, "meta.json")))
    d0a._TRIES.clear()
    _W.clear()
    verdict, reason = d1.check_case(case)
    res = meta.get("tx_results", [])
    out = dict(case=os.path.basename(case.rstrip("/")), verdict=verdict,
               txs=len(res),
               sig_checks=sum(1 for r in res if r not in ("Expired", "skipped_duplicate")),
               candidates=sum(1 for r in res if r not in
                              ("Expired", "skipped_duplicate", "InvalidSignature", "CostOverflow")),
               successes=sum(1 for r in res if r.startswith("success")),
               local=sum(1 for r in res if r == "success_local"),
               new_txs=len(meta.get("new_tx_labels", [])),
               receipts=meta["features"]["n_receipts"],
               witness_bytes=meta["features"]["witness_bytes"])
    if verdict != "accept" or not d0a._TRIES or not _W:
        return out
    main = d0a._TRIES[0]
    all_keys = set(main.keys)
    txk = tx_keys(_W[0]["txs"]) & all_keys
    rest = all_keys - txk
    pre_all = d0a.unfold_pre(main.pre_store, main.pre_root, [nibbles(k) for k in all_keys])
    pre_rest = d0a.unfold_pre(main.pre_store, main.pre_root, [nibbles(k) for k in rest])
    out.update(keys_read=len(all_keys), tx_keys_read=len(txk),
               unfold_pre_all=pre_all, unfold_pre_without_tx_keys=pre_rest,
               unfold_pre_tx_marginal=pre_all - pre_rest,
               base_state_bytes=sum(len(v) for v in main.pre_store.values()))
    return out


def main():
    rows = []
    for c in sys.argv[1:]:
        r = measure(c)
        rows.append(r)
        print(json.dumps(r))
    acc = [r for r in rows if r["verdict"] == "accept"]
    def mx(k, rs=acc):
        v = [r.get(k, 0) for r in rs]
        return (max(v) if v else 0, sum(v))
    print("cases %d accepted %d" % (len(rows), len(acc)), file=sys.stderr)
    for k in ("txs", "sig_checks", "candidates", "successes", "local", "new_txs", "receipts",
              "witness_bytes", "keys_read", "tx_keys_read", "unfold_pre_all",
              "unfold_pre_without_tx_keys", "unfold_pre_tx_marginal", "base_state_bytes"):
        m, s = mx(k)
        print("  %-28s max %9d  sum %10d" % (k, m, s), file=sys.stderr)


if __name__ == "__main__":
    main()
