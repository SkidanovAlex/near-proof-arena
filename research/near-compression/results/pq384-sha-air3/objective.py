"""SHA AIR v4 byte / latency objective.  MODEL (lane/pq-sha384-air3).

Turns a SHA-512 compression AIR shape into (final-layer proof bytes, prover latency):

  shape = one or more AIRs, each with
      rows   rows per compression (committed, tight heights)
      cols   main columns
      rot    columns read at the next row (opened twice)
      ipr    interactions per row
      deg    max constraint degree
      nodes  zerocheck DAG nodes (symbolic constraint DAG, keygen)
  plus the fixed tables it needs (rows, cols, rot, interactions per row).

Bytes: extrapolate_nv2.py (results/pq-recursion-nv, measured laws, model within 0.5 % of the
268-bit real-settings chain) with its SHA terms replaced by the shape:
  * cells   = NvAir rows * 74 + sum_airs comps * rows * cols + tables;
  * COLS    = 74 + sum cols + table cols + byte table 5, ROT likewise (relations 48 B each);
  * D       = max(NvAir degree 8, sha degrees) (round polynomials 48 (D+1) per round);
  * L       = GKR over power-of-two heights of every AIR (interactions = p2(height) * ipr);
  * n       = log2(tallest trace) - l_skip.
Regimes: NV_MCA = m3 | m64 | O2, and O2 + the program cut (-28 %), as in size_cut_mca.py.

Latency: prover-latency/latency_model.py (lane/pq-prover-latency) with its SHA AIR entry replaced:
zerocheck work per AIR = (deg + 1) * p2(height) / 4 * nodes * 0.42 Ext12-mul equivalents, LogUp-GKR
40 muls per fraction; reported as the post-execution tail of design G (adversarial, N = 32,
z_inner = z_base = 24, mid / optimistic GPU), the configuration of LATENCY.md's SHA lever.

Usage:  python3 objective.py [m3|m64|O2|O2cut|all] [design ...]
"""
import functools
import math
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
NV = os.path.join(HERE, '..', 'pq-recursion-nv')
sys.path.insert(0, NV)
sys.path.insert(0, os.path.join(HERE, '..', '..', 'prover-latency'))

NV_COLS, NV_ROT, NV_DEG, NV_NODES = 74, 36, 8, 3637
BYTE_COLS, BYTE_ROT = 5, 2

# ---------------------------------------------------------------- shapes
# v2.1 (measured, keygen of the NV crate copy: 171 cols, 144 next-row, degree 21, 12,718 nodes)
V21 = dict(airs=[dict(name='Sha512Air', rows=43, cols=171, rot=144, ipr=14, deg=21, nodes=12718)],
           tables=[dict(name='TableAir', rows=64, cols=13, rot=11, ipr=2, deg=3, nodes=600)])
DESIGNS = {'v2.1': V21}


def load(mca):
    os.environ['NV_MCA'] = mca
    for m in ('extrapolate_nv2', 'ext', 'latency_model'):
        sys.modules.pop(m, None)
    import extrapolate_nv2 as X
    import ext
    ext.bits = functools.lru_cache(maxsize=None)(X.bits_mca)  # O2 is slow uncached
    return X


def p2(x):
    return 1 << math.ceil(math.log2(max(1, x)))


def apply(X, d):
    """Point extrapolate_nv2's SHA terms at design d."""
    airs, tabs = d['airs'], d['tables']
    X.COLS = NV_COLS + sum(a['cols'] for a in airs + tabs) + BYTE_COLS
    X.ROT = NV_ROT + sum(a['rot'] for a in airs + tabs) + BYTE_ROT
    X.D = max([NV_DEG] + [a['deg'] for a in airs + tabs])
    X.AIRS = 2 + len(airs) + len(tabs)
    X.SHA_ROWS = airs[0]['rows']
    X.SHA_IPR = airs[0]['ipr']
    orig = X._orig_nv_circuit if hasattr(X, '_orig_nv_circuit') else X.nv_circuit
    X._orig_nv_circuit = orig

    def nv_circuit(*a, **kw):
        c = orig(*a, **kw)
        comps, nvr = c['comps'], c['nv_rows']
        heights = [comps * s['rows'] for s in airs]
        cells = nvr * NV_COLS + sum(h * s['cols'] for h, s in zip(heights, airs)) \
            + sum(t['rows'] * t['cols'] for t in tabs) + 65536 * BYTE_COLS
        inter = p2(nvr) * X.NV_IPR + sum(p2(h) * s['ipr'] for h, s in zip(heights, airs)) \
            + sum(t['rows'] * t['ipr'] for t in tabs) + 65536
        return dict(c, sha_rows=max(heights), cells=cells, inter=inter, heights=heights)
    X.nv_circuit = nv_circuit
    return X


def best(X):
    out = None
    for b in (3, 4, 5, 6):
        for ns in (17, 18, 19):
            c, pb, q = X.fixed_point(236, 236, 42, b, ns)
            if out is None or pb['total'] < out[1]['total']:
                out = (c, pb)
    return out


def final_bytes(d, regime):
    X = apply(load('O2' if regime == 'O2cut' else regime), d)
    if regime == 'O2cut':
        X.P_FIXED = int(X.P_FIXED * .72)
        X.Q0_COST, X.QR_COST, X.FINAL_PER_Q = int(451 * .72), int(530 * .72), int(110 * .72)
    c, pb = best(X)
    return dict(total=pb['total'], c=c, pb=pb)


def latency(d):
    """Post-execution tail (s) of design G, adversarial, N = 32, z_inner = z_base = 24: (mid, optimistic)."""
    X = apply(load('m3'), d)
    import latency_model as LM
    LM.X = X
    airs = d['airs']

    def zc(nv_rows, sha_rows, case='mid', bottom_up=False):
        comps = sha_rows / airs[0]['rows']
        a = LM.AIRS['nv']
        hn = p2(nv_rows)
        z = (a['deg'] + 1) * hn / 4 * a['nodes'] * LM.NODE_MUL_EQ
        gk = hn * a['ipr'] + 65536
        for s in airs:
            hs = p2(comps * s['rows'])
            z += (s['deg'] + 1) * hs / 4 * s['nodes'] * LM.NODE_MUL_EQ
            gk += hs * s['ipr']
        base = z + gk * LM.GKR_MUL_PER_FRACTION
        return base if bottom_up else base * LM.ZC_OVERHEAD[LM.LMH[case]]
    LM.zc_ext12_muls = zc

    def node_circuit(cells):
        r = int(cells / (73 + 171))          # the latency lane's L1 split, in v2.1 rows
        comps = r / 43
        hs = [int(comps * s['rows']) for s in airs]
        cl = r * 73 + sum(h * s['cols'] for h, s in zip(hs, airs))
        return dict(cells=cl, nv_rows=r, sha_rows=int(comps * airs[0]['rows']),
                    inter=r * 55 + sum(h * s['ipr'] for h, s in zip(hs, airs)))
    LM.node_circuit = node_circuit
    a = LM.chain('adversarial', 32, 'mid', z_inner=24, z_base=24)
    h = LM.chain('adversarial', 32, 'high', z_inner=24, z_base=24)
    fin = a['layers'][-1][3]
    return dict(tail_mid=LM.tail_s(a), tail_opt=LM.tail_s(h), final_zc_mid=fin['zc'], final_total_mid=fin['total'])


def per_comp(d):
    a = d['airs']
    return dict(cells=sum(s['rows'] * s['cols'] for s in a), cols=sum(s['cols'] for s in a),
                rot=sum(s['rot'] for s in a), deg=max(s['deg'] for s in a),
                ipr=sum(s['ipr'] for s in a), nodes=sum(s['nodes'] for s in a),
                zc=sum((s['deg'] + 1) * s['rows'] * s['nodes'] for s in a))


def report(names, regimes):
    for n in names:
        d = DESIGNS[n]
        pc = per_comp(d)
        line = (f"{n:28s} cells/comp {pc['cells']:6,} cols {pc['cols']:4} rot {pc['rot']:4} deg {pc['deg']:2} "
                f"ipr {pc['ipr']:3} nodes {pc['nodes']:6,} (d+1)*rows*nodes {pc['zc']:.3e}")
        for r in regimes:
            fb = final_bytes(d, r)
            line += f" | {r} {fb['total']:,} (L={fb['pb']['L']})"
        lt = latency(d)
        line += f" | tail {lt['tail_mid']:.2f} s (opt {lt['tail_opt']:.2f}), final ZC {lt['final_zc_mid']:.2f} s"
        print(line, flush=True)


if __name__ == '__main__':
    reg = sys.argv[1] if len(sys.argv) > 1 else 'm3'
    regimes = ['m3', 'm64', 'O2', 'O2cut'] if reg == 'all' else [reg]
    names = sys.argv[2:] or list(DESIGNS)
    report(names, regimes)
