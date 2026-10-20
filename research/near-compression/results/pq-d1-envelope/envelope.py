#!/usr/bin/env python3
"""Per-table PQ-envelope check of the classical NEAR AIRs (nearAirV3 / nearAirV3D1).

Input: the Lean exports (`np-lean-export-v3` / `np-lean-export-v3d1`, format np-air-v2).
Output: envelope CSV + a text summary.  Usage:
  envelope.py <air.json> <variant> <out.csv>
Every number is computed from the JSON (the Lean AIR value), nothing is hand-entered except
the table names (positional, from NearAirDefs / NearAirD1Defs).
"""
import json, sys, math, collections

P = 15 * 2**27 + 1
NAMES_D0A = ["sha0", "sha1", "nodeA7", "head", "valA7", "walk", "uniq", "upsA7", "chacha", "rng",
             "shuf", "codec", "scandist", "proc", "mem", "cmp", "rcptQ", "acct", "akey", "bnd",
             "srcpDD", "sizeA7", "qv", "mrk", "sort"]
FAMILY = {"sha0": "sha256", "sha1": "sha256", "nodeA7": "trie", "head": "trie", "valA7": "trie",
          "walk": "trie", "uniq": "trie", "upsA7": "trie", "sizeA7": "trie", "mrk": "receipts/merkle",
          "sort": "receipts/merkle", "chacha": "scheduler", "rng": "scheduler", "shuf": "scheduler",
          "codec": "scheduler", "scandist": "scheduler", "proc": "scheduler", "mem": "scheduler",
          "cmp": "scheduler", "rcptQ": "receipts", "rcptD1": "receipts", "acct": "accounts",
          "akey": "accounts", "bnd": "receipts", "srcpDD": "receipts", "qv": "queue",
          "tx": "d1-tx", "akm": "d1-tx", "kib": "d1-relay", "kibD1": "d1-relay", "plf": "d1-relay",
          "rid": "d1-relay", "nodeD1": "trie", "uniqD1": "trie", "walkU": "trie(unread)",
          "nmem": "trie(unread)", "uval": "trie(unread)", "mrkD1": "receipts/merkle"}


def names_for(variant, n):
    names = list(NAMES_D0A)
    if variant == "d0a":
        return names
    names[16] = "rcptD1"
    names[23] = "mrkD1"
    if variant == "d1":
        return names + ["tx", "akm", "kib", "plf", "rid"]
    if variant == "d1a7b":
        names[2] = "nodeD1"
        names[6] = "uniqD1"
        return names + ["tx", "akm", "kibD1", "plf", "rid", "walkU", "nmem", "uval"]
    raise SystemExit("variant")


def deg(e):
    t = e[0]
    if t in ("c", "p"):
        return 0
    if t in ("v", "first", "last", "trans"):
        return 1
    if t == "+":
        return max(deg(e[1]), deg(e[2]))
    if t == "*":
        return deg(e[1]) + deg(e[2])
    if t == "-":
        return deg(e[1])
    raise ValueError(t)


def walk(e, f):
    f(e)
    if e[0] in ("+", "*"):
        walk(e[1], f); walk(e[2], f)
    elif e[0] == "-":
        walk(e[1], f)


def cse(exprs, memo):
    """Unique nodes of the DAG (the SWIRL keygen builds a CSE'd DAG; NV evaluates it node by node)."""
    def key(e):
        t = e[0]
        if t in ("c", "p"):
            k = (t, e[1])
        elif t == "v":
            k = (t, e[1], e[2])
        elif t in ("first", "last", "trans"):
            k = (t,)
        elif t == "-":
            k = (t, key(e[1]))
        else:
            k = (t, key(e[1]), key(e[2]))
        memo.add(k)
        return k
    for e in exprs:
        key(e)
    return memo


def main():
    path, variant, out = sys.argv[1:4]
    A = json.load(open(path))
    T = A["tables"]
    names = names_for(variant, len(T))
    assert len(names) == len(T), (len(names), len(T))
    rows = []
    bus_load = collections.defaultdict(int)      # (bus, send) -> sum over rows of max multiplicity, at maxLog
    bus_bits = collections.defaultdict(int)
    for idx, t in enumerate(T):
        nm = names[idx]
        cons = t["constraints"]
        inters = t["interactions"]
        w, ml = t["width"], t["maxLog"]
        cdeg = max([deg(c) for c in cons] + [0])
        next_cols, pubs, sels = set(), set(), set()
        def visit(e):
            if e[0] == "v" and e[2] == 1:
                next_cols.add(e[1])
            if e[0] == "p":
                pubs.add(e[1])
            if e[0] in ("first", "last", "trans"):
                sels.add(e[0])
        allx = list(cons)
        for i in inters:
            allx += i["mult"] + i["msg"]
        for e in allx:
            walk(e, visit)
        nbits = [len(i["mult"]) for i in inters]
        msgw = [len(i["msg"]) for i in inters]
        # LogUp: count = sum 2^k b_k; fraction numerator degree = max bit degree; denominator = max msg degree
        cnt_deg = max([max([deg(b) for b in i["mult"]] + [0]) for i in inters] + [0])
        msg_deg = max([max([deg(m) for m in i["msg"]] + [0]) for i in inters] + [0])
        nbitcons = sum(nbits)  # booleanity constraints the export appended
        dag = len(cse(allx, set()))
        buses = sorted({i["bus"] for i in inters})
        for i in inters:
            k = len(i["mult"])
            bus_load[(i["bus"], i["send"])] += (2 ** ml) * (2 ** k - 1)
            bus_bits[(i["bus"], i["send"])] = max(bus_bits[(i["bus"], i["send"])], k)
        rows.append(dict(
            idx=idx, table=nm, family=FAMILY.get(nm, "?"), width=w, maxLog=ml,
            constraints=len(cons), user_constraints=len(cons) - nbitcons, max_deg=cdeg,
            interactions=len(inters), sends=sum(1 for i in inters if i["send"]),
            max_msg=max(msgw + [0]), max_mult_bits=max(nbits + [0]), multibit_inters=sum(1 for k in nbits if k >= 2),
            count_deg=cnt_deg, msg_deg=msg_deg, next_cols=len(next_cols),
            opened_masked=w + len(next_cols), opened_full=2 * w if next_cols else w,
            pub_reads=len(pubs), selectors="|".join(sorted(sels)), dag_nodes=dag,
            fractions_at_max=(2 ** ml) * len(inters), cells_at_max=(2 ** ml) * w,
            buses=" ".join(map(str, buses))))
    # envelope verdict per table
    for r in rows:
        v = []
        if r["max_deg"] > 8: v.append("deg>8")
        if r["constraints"] > 2 ** 14: v.append("constraints>2^14")
        if r["opened_masked"] > 1024: v.append("opened>1024")
        if r["max_msg"] + 1 > 16: v.append("msg+bus>16")
        if r["maxLog"] > 24: v.append("height>2^24")
        r["envelope"] = "fits" if not v else ";".join(v)
    keys = list(rows[0].keys())
    with open(out, "w") as f:
        f.write(",".join(keys) + "\n")
        for r in rows:
            f.write(",".join(str(r[k]) for k in keys) + "\n")
    # summary
    tot_frac = sum(r["fractions_at_max"] for r in rows)
    tot_open = sum(r["opened_masked"] for r in rows)
    print(f"variant {variant}: {len(T)} tables, numBuses {A['numBuses']}, numPub {A['numPub']}, maxPub {A.get('maxPub')}, pubSegs {len(A.get('pubSegs', []))}")
    print(f"  max degree {max(r['max_deg'] for r in rows)}, max constraints/table {max(r['constraints'] for r in rows)}, "
          f"total constraints {sum(r['constraints'] for r in rows)}")
    print(f"  max interactions/row {max(r['interactions'] for r in rows)}, max msg {max(r['max_msg'] for r in rows)}, max mult bits {max(r['max_mult_bits'] for r in rows)}")
    print(f"  total opened cols (masked next) {tot_open}, unmasked {sum(r['opened_full'] for r in rows)}; total width {sum(r['width'] for r in rows)}")
    print(f"  fractions at maxLog heights: 2^{math.log2(tot_frac):.2f}; cells at maxLog 2^{math.log2(sum(r['cells_at_max'] for r in rows)):.2f}")
    print(f"  DAG nodes (sum over tables, CSE per table): {sum(r['dag_nodes'] for r in rows)}")
    print(f"  tables over envelope: {[ (r['table'], r['envelope']) for r in rows if r['envelope']!='fits']}")
    # bus loads vs p (exact-multiset recovery from mod-p LogUp)
    over = []
    for (b, s), L in sorted(bus_load.items()):
        if L >= P:
            over.append((b, "send" if s else "recv", bus_bits[(b, s)], round(math.log2(L), 2)))
    print(f"  bus sides with worst-case load >= p at maxLog heights (bus, side, max bits, log2 load): {len(over)} of {len(bus_load)}")
    for o in over:
        print("   ", o)
    segs = A.get("pubSegs", [])
    print(f"  public segments: {[(s['bus'], 'send' if s['send'] else 'recv', s['width']) for s in segs]}")
    json.dump({"bus_load_log2": {f"{b}{'s' if s else 'r'}": round(math.log2(L), 2) for (b, s), L in bus_load.items()},
               "over_p": over}, open(out.replace(".csv", "-buses.json"), "w"), indent=1)


main()
