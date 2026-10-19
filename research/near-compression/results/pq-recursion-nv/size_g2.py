# G2 (program binding by a cached program commitment, "B1") final-size model [MODEL].
# Builds on pq-nv-preprocessed/prep_model.py (B1 costs: one more round-0 tree per child of an NV
# proof, round 0 on Johnson for multi-commit children, app table removed) and adds this lane's
# Merkle cut: the level's node-job start rides on SibWS4, 4 program rows per Merkle level (was 5).
# FINAL keeps one commitment and picks its own shape (it binds its child by BIND; V_d pins it).
# Usage: NV_MCA=O2 python3 size_g2.py
import math, os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'pq-nv-preprocessed'))
import prep_model as pm  # noqa: E402
e = pm.e
pm.MODE['b1'] = True
e.P_FIXED -= e.APP_ROWS; e.APP_ROWS = 0          # app table and APPB role removed


def search(tag):
    res = []
    for b in (6, 7):
        for k in (3, 4):
            for k1 in (1, 2):
                for lf in range(1, 12):
                    ns = 18                         # penultimate log_h >= 20, b + log_h <= 27
                    if (ns + 2 - k1 - lf) % k or ns + 2 + b > e.MAX_DOM:
                        continue
                    c, pb, q = e.fixed_point(236, 236, 42, b, ns, k1=k1, k=k, lf=lf)
                    res.append((pb, c, (b, ns, k, k1, lf), q))
    res.sort(key=lambda r: r[0]['total'])
    print(f"== {tag}")
    for pb, c, sh, q in res[:3]:
        print(f"  final {pb['total']:,} B (whir {pb['whir']:,} gkr {pb['gkr']:,} L={pb['L']} certified={pb['certified']}, "
              f"final shape {pb['shape']} q={pb['q']}) | pen {sh} q={q} | prog {c['prog']:,} NvAir {c['nv_rows']:,} "
              f"({100 * (1 - c['nv_rows'] / 2 ** 18):+.1f}% to 2^18) SHA {c['sha_rows']:,}", flush=True)


search("B1, app table removed, Merkle 5 rows/level (prep lane figure)")
e.PER_LEVEL = 4
pm.tree_rows = lambda depth, k1, w: 1 + (1 << k1) * -(-w // 2) + 4 * depth + 2 + 4
search("B1, app table removed, Merkle 4 rows/level (SibWS4 starts the node job)")
# app-binding role removed from NvAir (measured nv_degrees: w 77 -> 76, 51 -> 48 interactions,
# 37 -> 36 rotated columns, degree 9)
e.NV_COLS, e.NV_IPR = 76, 48
e.COLS, e.ROT = e.COLS - 1, e.ROT - 1
search("+ app-binding role removed (NvAir 76 cols, 48 interactions/row)")
