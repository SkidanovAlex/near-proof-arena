"""pq-nv-preprocessed: cost of extra (preprocessed / cached) child commitments in NV  [MODEL].

Per-commitment NV cost (measured on the program generator, results/pq-nv-preprocessed/DESIGN.md §4):
  per round-0 query and extra tree: 1 leaf job + 2^k1 * ceil(w/2) Horn2 + 5 rows per Merkle level
  + 2 Dig + 4 (root check) rows; SHA: one node compression per level + the leaf job's blocks.
  fixed: constant commit (<= 2 ce + 3 rows), 3 rows per opened column, stacking terms.
  (The query index bits, the fold and the final check are shared by every tree.)

Scenarios:
  A   only base / L1 children carry preprocessed tables: the NV fixed point and FINAL are unchanged;
      the extra rows land in L1 (verifying the base), computed here for the pinned base shapes.
  B1  program binding by commitment (recursion-lane G2 proposal): every NV-family proof carries a second
      commitment with its 4 program columns; the parent opens it (one more round-0 tree), the app table goes,
      and the inner proofs' round 0 runs on Johnson (O-2 multi-commitment rule); FINAL keeps one commitment.

Usage: python3 prep_model.py            (needs ../pq-recursion-nv/extrapolate_nv2.py)
"""
import math
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'pq-recursion-nv'))
import extrapolate_nv2 as e  # noqa: E402

# adopted program-cut state (size_cut3.py milestones; = the recursion lane's backed figures)
e.PER_LEVEL = 5; e.QR_BASE -= 26; e.FOLD_ROW = 5; e.FINAL_EQ = 22
e.final_per_q = lambda lf: e.FINAL_EQ + e.FINAL_OTHER + (1 << lf) + 2; e.LEAF_FELTS_PER_ROW = 2
e.Q0_BASE -= 44; e.QR_BASE -= 44
e.P_FIXED -= 6764

PEN = (7, 18, 4, 2, 6)   # adopted penultimate (b, n_stack, k, k1, lf)


def tree_rows(depth, k1, w):
    """Program rows per round-0 query for one extra tree (coset-leaf lever: one leaf job)."""
    return 1 + (1 << k1) * -(-w // 2) + 5 * depth + 2 + 4


def tree_comps(depth, k1, w):
    blk = -(-((1 << k1) * w * 4 + 33 + 8 + 17) // 128)
    return depth + blk


FIXED_PER_COMMIT = 60 + 3 * 4 + 40   # const / loaded commit, 4 opened columns, stacking terms

_orig_nv_circuit = e.nv_circuit
_orig_schedule = e.schedule
MODE = {'b1': False}


def nv_circuit(rounds_q, depth0, depthr, child_W, lf=3, k1=1):
    c = _orig_nv_circuit(rounds_q, depth0, depthr, child_W, lf, k1)
    if not MODE['b1']:
        return c
    q0 = rounds_q[0]
    extra = q0 * tree_rows(depth0, k1, 1) + FIXED_PER_COMMIT
    comps = q0 * tree_comps(depth0, k1, 1)
    prog = c['prog'] + extra
    prog += prog % 2
    nv_rows = c['nv_rows'] + (prog - c['prog']) * 3 // 2 + 8 * comps
    sha_rows = c['sha_rows'] + e.SHA_ROWS * comps
    c.update(prog=prog, prog_log=math.ceil(math.log2(prog + 2)), comps=c['comps'] + comps, nv_rows=nv_rows,
             sha_rows=sha_rows,
             cells=nv_rows * e.NV_COLS + sha_rows * e.SHA_COLS + e.TAB_ROWS * e.TAB_COLS + 65536 * 5,
             inter=e.p2(nv_rows) * e.NV_IPR + e.p2(sha_rows) * e.SHA_IPR + e.TAB_ROWS * 2 + 65536)
    return c


def schedule(cells, b, k1, k, log_h, lf, target):
    q, d = _orig_schedule(cells, b, k1, k, log_h, lf, target)
    if MODE['b1']:
        # O-2 multi-commitment rule: the child's round 0 runs on the Johnson fallback
        P = e.ext.P(target=target, m=3, extra=e.L15, shrink=0)
        qj = e.with_regime('m64', lambda: e.ext.layer(cells, e.COLS, b, k1, k, log_h, lf, P))['q']
        q = [max(q[0], qj[0])] + list(q[1:])
    return q, d


e.nv_circuit = nv_circuit
e.schedule = schedule


def show(tag):
    b, ns, k, k1, lf = PEN
    c, pb, q = e.fixed_point(236, 236, 42, b, ns, k1=k1, k=k, lf=lf)
    print(f"{tag:46s} final {pb['total']:,} B (whir {pb['whir']:,} gkr {pb['gkr']:,} L={pb['L']}) | pen q={q} | "
          f"prog {c['prog']:,} NvAir {c['nv_rows']:,} (2^{math.log2(c['nv_rows']):.3f}, {100 * (1 - c['nv_rows'] / 2 ** 18):+.1f}% headroom to 2^18) "
          f"SHA {c['sha_rows']:,} | final shape {pb['shape']} q={pb['q']}", flush=True)
    return c, pb


def final_at(c, shape, target=236, digest=42):
    """Final proof bytes when FINAL runs at a fixed (penultimate) shape (recursion lane @717eb518e:
    FINAL = the uniform program under the final domain; (b, log_h, k1, k, lf))."""
    b, log_h, k1, k, lf = shape
    P = e.ext.P(target=target, m=3, extra=e.L15, shrink=0, digest=digest)
    reg = e.regime_for((b, log_h, k1, k, lf))
    r = e.with_regime(reg, lambda: e.ext.layer(c['cells'], e.COLS, b, k1, k, log_h, lf, dict(P, colb=0)))
    w = r['bytes'] - (3112 + 8456 + 1840 + 861)
    g, L = e.gkr(c['inter'])
    n = math.ceil(math.log2(max(c['nv_rows'], c['sha_rows']))) - e.L_SKIP
    certified = (b, log_h, k1, k, lf) in e.CERT_SHAPES
    reserve = e.o2_reserve(len(r['q'])) if certified and reg == 'O2' else 0
    return round(w + g + e.relations(n) + e.stacking(log_h - e.L_SKIP, r['width']) + 73 + reserve), L, r['q']


def show_fixed_final(tag, pen=PEN):
    b, ns, k, k1, lf = pen
    c, pb, q = e.fixed_point(236, 236, 42, b, ns, k1=k1, k=k, lf=lf)
    tot, L, fq = final_at(c, (b, ns + 2, k1, k, lf))
    print(f"{tag:46s} FINAL at the penultimate shape {pen}: {tot:,} B (L={L}, final q={fq}) | NvAir {c['nv_rows']:,}", flush=True)


def l1_cost():
    """Scenario A: extra rows / compressions in L1 per extra commitment of the base."""
    print("\nScenario A (only the base carries preprocessed tables): L1 cost per extra base commitment")
    # pinned base (DESIGN-BASE §3): l_skip 2, n_stack 22, k1 = 1, x15 domain (+4 Merkle levels)
    for name, b, q0, l1_prog, l1_comps in [("pinned b=1, m=16", 1, 536, 623_802, 22_751 + 1_600),
                                           ("alternative b=2, m=8", 2, 268, 400_280, 14_421 + 1_600)]:
        depth = 2 + 22 + b - 1 + 4
        for w in (1, 8):
            r, cp = q0 * tree_rows(depth, 1, w) + FIXED_PER_COMMIT, q0 * tree_comps(depth, 1, w)
            print(f"  base {name:22s} depth {depth}, stacked width {w}: +{r:,} program rows "
                  f"({100 * r / l1_prog:.1f}% of L1's {l1_prog:,}), +{cp:,} compressions "
                  f"(+{100 * cp / l1_comps:.0f}%); NvAir +{r * 3 // 2 + 8 * cp:,} rows, SHA +{e.SHA_ROWS * cp:,} rows")
    # break-even against public-value code records (toy measurement: 84-106 NV rows per record)
    for name, b, q0 in [("b=1", 1, 536), ("b=2", 2, 268)]:
        depth = 2 + 22 + b - 1 + 4
        r = q0 * tree_rows(depth, 1, 1) + FIXED_PER_COMMIT
        print(f"  break-even vs public code records at 95 rows/record ({name}): {r // 95:,} records")


if __name__ == '__main__':
    print("pq-nv-preprocessed cost model [MODEL; extrapolate_nv2 + size_cut3 milestones]")
    MODE['b1'] = False
    c0, p0 = show("baseline (1 commitment, toy app table)")
    MODE['b1'] = True
    c1, p1 = show("B1: program commitment, app table kept")
    saved = (e.P_FIXED, e.APP_ROWS)
    e.P_FIXED -= e.APP_ROWS
    e.APP_ROWS = 0
    c2, p2 = show("B1: program commitment, app table removed")
    e.P_FIXED, e.APP_ROWS = saved
    MODE['b1'] = False
    for rows in (400_000, 624_000):
        e.P_FIXED += rows - e.APP_ROWS
        e.APP_ROWS = rows
        show(f"app-table binding, real L1 ({rows:,} rows)")
        e.P_FIXED, e.APP_ROWS = saved
    # FINAL at the fixed point (recursion lane @717eb518e): FINAL = the uniform program, penultimate shape
    print()
    for pen in (PEN, (7, 18, 4, 1, 7)):
        globals()['PEN'] = pen
        MODE['b1'] = False
        show_fixed_final("baseline, FINAL at the fixed point", pen)
        MODE['b1'] = True
        e.P_FIXED -= e.APP_ROWS; e.APP_ROWS = 0
        show_fixed_final("B1 (app table removed), FINAL at the fixed point", pen)
        e.P_FIXED, e.APP_ROWS = saved
        MODE['b1'] = False
    globals()['PEN'] = (7, 18, 4, 2, 6)
    l1_cost()
