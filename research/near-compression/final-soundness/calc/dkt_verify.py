#!/usr/bin/env python3
"""Independent re-derivation of the DKT26 Thm 5.12 (O-1) numbers used by bound_mca.py.

Written from the paper text (DKT26 eqs. (65)-(68)) and the Lean definition `johnsonE0`
(ArkLib quangvdao@a5aa2677, HiddenDerivative/Parameters/Johnson/FiniteBounds.lean), without
importing bound.py / bound_mca.py.  All roundings are decided in exact integer/rational
arithmetic (no floating point before the final log2).

For each WHIR round of the three bound.py shapes and each fold code C^(i,s), s = 0..k_i:
  A      = ceil((1 + 1/128) sqrt(k/n) n)                (backend ListDecoding m = 64)
  A_s    = ceil(A n_s / n)                              (same agreement fraction)
  eta    = A_s/n_s - sqrt(D/n_s),  D = k_s - 1
  m      = max(ceil(sqrt(D/n)/(2 eta)), 3),  t = m + 1/2
  B_jet  = ceil(t / sqrt(D/n)) - 1,  B_Z = ceil(t^2 n / (3 D)) - 1
  E      = (2 B_jet - 1) B_Z + (n-D)/(A-D) (B_Z + B_jet + 4 D B_jet B_Z) + (n-D-1) B_jet
           (= Lean johnsonE0 n D A eta, the bound in johnson_lineMCA_probability)
  list   = min(B_jet, floor(n(A-D)/(A^2 - nD)))  (eq. (67); Lean proves only the pairwise part)
Prints per round: bits/query = -log2(A/n), q = ceil(236/bits), max_s log2(E/q_F), list.
Usage: python3 -I dkt_verify.py [--json]
"""
import json
import math
import sys
from fractions import Fraction as Fr
from math import isqrt

P = 15 * 2**27 + 1
QF = P**12
LOGQ = math.log2(P) * 12
QBITS = 236
C_ODD = 15
SHAPES = {   # bound.py SHAPES (log_h, b, k1, k, lf); n = 15 * 2^(log_h+b) kept in every round
    'final': (19, 8, 1, 3, 9),
    'inner NV': (19, 6, 1, 4, 6),
    'base stress': (21, 6, 1, 4, 8),
}


def rounds(log_h, b, k1, k, lf):
    nr = 1 + -(-(log_h - k1 - lf) // k)
    n = C_ODD * 2 ** (log_h + b)
    out, mv = [], log_h
    for i in range(nr):
        ki = k1 if i == 0 else k
        out.append((n, 2 ** mv, ki))
        mv -= ki
    return out


def ceil_fr(x):
    return -((-x.numerator) // x.denominator)


def log2_fr(x):
    return math.log2(x.numerator) - math.log2(x.denominator)


def johnson_agreement(n, k, M=64):
    # smallest A with A >= (1+1/(2M)) sqrt(k n)  <=>  (2M A)^2 >= (2M+1)^2 k n
    c = (2 * M + 1) ** 2 * k * n
    A = isqrt(c) // (2 * M)
    while (2 * M * A) ** 2 < c:
        A += 1
    while A > 0 and (2 * M * (A - 1)) ** 2 >= c:
        A -= 1
    return A


def smallest(pred, lo=1):
    hi = lo
    while not pred(hi):
        hi *= 2
    while lo < hi:
        mid = (lo + hi) // 2
        if pred(mid):
            hi = mid
        else:
            lo = mid + 1
    return lo


def thm512(n, k, A):
    D = k - 1
    assert 1 <= D <= n - 2, (n, k)
    assert A * A > n * D, 'eta0 > 0 fails'          # sqrt(D/n) < A/n
    assert A <= n
    rm = Fr(D, n)                                     # rho_minus = x^2
    a = Fr(A, n)
    # m0 = ceil(x/(2(a-x))): smallest c with x(1+2c) <= 2ca  <=>  rm (1+2c)^2 <= 4 c^2 a^2
    m0 = smallest(lambda c: rm * (1 + 2 * c) ** 2 <= 4 * c * c * a * a)
    m = max(m0, 3)
    t = Fr(2 * m + 1, 2)
    # B_jet = ceil(t/x) - 1: smallest c with c^2 rm >= t^2
    Bj = smallest(lambda c: c * c * rm >= t * t) - 1
    Bz = ceil_fr(t * t / (3 * rm)) - 1
    theta = Fr(n - D, A - D)
    E = (2 * Bj - 1) * Bz + theta * (Bz + Bj + 4 * D * Bj * Bz) + (n - D - 1) * Bj
    closed = Fr(8) * n * t ** 3 / (3 * rm)
    assert E < closed, 'eq. (68) closed form violated'
    pair = (n * (A - D)) // (A * A - n * D)
    return dict(n=n, k=k, A=A, D=D, m=m, t=t, Bj=Bj, Bz=Bz, E=E, list=min(Bj, pair),
                list_pair=pair, logEq=log2_fr(E) - LOGQ)


def layer(shape, M=64):
    res = []
    for (n, kdim, ki) in rounds(*shape):
        A = johnson_agreement(n, kdim, M)
        bits = -log2_fr(Fr(A, n))
        q = math.ceil(QBITS / bits)
        codes = []
        for s in range(ki + 1):
            ns, ks = n >> s, kdim >> s
            As = ceil_fr(Fr(A * ns, n))
            codes.append(thm512(ns, ks, As))
        res.append(dict(n=n, k=kdim, ki=ki, A=A, bits=bits, q=q, qbits=q * bits,
                        fold_max=max(c['logEq'] for c in codes),
                        list=max(c['list'] for c in codes),
                        list_from=('B_jet' if all(c['list'] == c['Bj'] for c in codes) else 'mixed/pairwise'),
                        m=codes[0]['m'], codes=codes))
    return res


O2_PLANS = {   # MCA-UPGRADE.md section 2 / dkt_certs.json _plans: A = ceil(ratio sqrt((k-1)/n) n)
    'final': ['0.835', '0.818', '0.879', '0.768'],
    'inner NV': ['0.817', '0.809', '0.895', '0.768'],
}
W_BATCH = {'final': 141, 'inner NV': 141, 'base stress': 601}


def first_order_agreement(n, k, ratio):
    r = Fr(ratio)
    c = r * r * (k - 1) * n                      # smallest A with A^2 >= r^2 (k-1) n
    A = isqrt(c.numerator // c.denominator)
    while Fr(A * A) < c:
        A += 1
    while A > 0 and Fr((A - 1) ** 2) >= c:
        A -= 1
    return A


def o2(certs):
    """Per-round O-2 numbers from the certified (n, k, A) table; every code each round needs must
    have a certificate (these are exactly the ones kernel-checked in lean/DKTCerts.lean)."""
    res = {}
    for name, ratios in O2_PLANS.items():
        rows = []
        for (n, kdim, ki), ratio in zip(rounds(*SHAPES[name]), ratios):
            A = first_order_agreement(n, kdim, ratio)
            bits = -log2_fr(Fr(A, n))
            q = math.ceil(QBITS / bits)
            es, ls, missing = [], [], []
            for s in range(ki + 1):
                ns, ks = n >> s, kdim >> s
                As = ceil_fr(Fr(A * ns, n))
                c = certs.get(f'{ns},{ks},{As},1')
                if c is None:
                    missing.append((ns, ks, As))
                    continue
                es.append(log2_fr(Fr(c['E'])) - LOGQ)
                ls.append(math.log2(Fr(c['list'])))
            rows.append(dict(n=n, k=kdim, A=A, ratio=float(Fr(A, n)) / math.sqrt((kdim - 1) / n),
                             bits=bits, q=q, qbits=q * bits, fold=max(es) if es else None,
                             list=max(ls) if ls else None, missing=missing))
        n0, k0 = rounds(*SHAPES[name])[0][:2]
        cb = certs.get(f'{n0},{k0},{rows[0]["A"]},{W_BATCH[name] - 1}')
        res[name] = dict(rows=rows, batch=(log2_fr(Fr(cb['E'])) - LOGQ) if cb else None)
    return res


def main():
    out = {}
    for name, sh in SHAPES.items():
        L = layer(sh)
        out[name] = L
        print(f'== {name}: queries {[r["q"] for r in L]} (sum {sum(r["q"] for r in L)})')
        for i, r in enumerate(L):
            print(f'  r{i}: n={r["n"]} k=2^{int(math.log2(r["k"]))} A={r["A"]} bits/query={r["bits"]:.4f} '
                  f'q={r["q"]} ({r["qbits"]:.2f} bits) m_DKT={r["m"]} list<=2^{math.log2(r["list"]):.2f} '
                  f'[{r["list_from"]}] max_s E/q=2^{r["fold_max"]:.2f}')
            for c in r['codes']:
                print(f'      C(n={c["n"]},k={c["k"]}) A={c["A"]} m={c["m"]} Bjet={c["Bj"]} Bz={c["Bz"]} '
                      f'pairwise={c["list_pair"]} log2E={log2_fr(c["E"]):.4f} E/q=2^{c["logEq"]:.3f}')
    certs = json.load(open(__file__.rsplit('/', 1)[0] + '/dkt_certs.json'))
    for name, r in o2(certs).items():
        print(f'== O-2 {name}: queries {[x["q"] for x in r["rows"]]} (sum {sum(x["q"] for x in r["rows"])}); '
              f'mu-batching curve E/q = 2^{r["batch"]:.2f}')
        for i, x in enumerate(r['rows']):
            print(f'  r{i}: A={x["A"]} a/sqrt(rho-)={x["ratio"]:.4f} bits/query={x["bits"]:.4f} q={x["q"]} '
                  f'({x["qbits"]:.2f} bits) max_s E/q=2^{x["fold"]:.2f} list<=2^{x["list"]:.2f} '
                  f'missing={x["missing"]}')
    if '--json' in sys.argv:
        print(json.dumps({k: [dict(q=r['q'], bits=r['bits'], fold=r['fold_max'], list=r['list'])
                              for r in v] for k, v in out.items()}, indent=1))


if __name__ == '__main__':
    main()
