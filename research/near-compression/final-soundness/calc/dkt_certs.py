#!/usr/bin/env python3
"""Produce / re-check the DKT26 first-order certificates used by bound_mca.py (O-2).

Runs the authors' exact-arithmetic certificate engine (scripts/tune_first_order_mca.py of
github.com/quangvdao/rs-beyond-johnson, pinned at commit 60b7257, MIT/Apache-2.0) on every
Reed-Solomon code that a planned WHIR round analyses: the round's code and the fold sub-round
codes C^(i,s) (conservatively of length n/2^(s-1), as in bound.py), at the round's agreement
fraction a = A/n.  For each code it searches supports (m, B_d, B_jet) of the
derivative-weighted family (DKT26 eq. (60)), keeps the first one (smallest m) whose line
exceptional count E and list bound L satisfy E/|F| <= 2^-275 and L <= 2^44, and stores the
exact rationals in dkt_certs.json with the selected transfer theorem and characteristic guard.
The application checkers of the paper select the 'tight-2D-minus-3-v3' Taylor model; so do we.

Usage:  python3 -I dkt_certs.py /path/to/rs-beyond-johnson [--check]
  --check   re-evaluate every stored certificate (no search) and compare.
The JSON is committed; bound_mca.py reads it and needs no third-party code.
"""
import json
import math
import os
import sys
import time
from decimal import Decimal
from fractions import Fraction as F
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import bound_mca as BM  # noqa: E402

OUT = os.path.join(HERE, 'dkt_certs.json')
E_MAX = BM.LOG_F - 275          # log2 of the largest admissible exceptional count
L_MAX = 44.0
DKT_COMMIT = '60b7257'

# Per-round plans.  ('F', ratio) = first order at A = ceil(ratio * sqrt((k-1)/n) * n);
# ('J', M) = Johnson radius with backend ListDecoding(M) (DKT26 Thm 5.12, no certificate needed).
# Ratios are the largest that reach the next-lower query count (MCA-UPGRADE.md section 3).
PLANS = {
    'final': dict(batching='tensor', plan=[('F', 0.835), ('F', 0.818), ('F', 0.880), ('F', 0.768)]),
    'inner NV': dict(batching='tensor', plan=[('F', 0.817), ('F', 0.811), ('F', 0.895), ('F', 0.768)]),
}
FALLBACK = {  # used when a stretch ratio cannot be certified
    'final': [None, None, None, ('J', 64)],
    'inner NV': [None, None, None, ('J', 64)],
}


def codes_for(shape, plan):
    out = []
    for r, (reg, par) in zip(BM.rounds_of(shape), plan):
        if reg != 'F':
            continue
        A = BM.agreement('F', r['n'], r['kdim'], ratio=par)
        a = Decimal(A) / r['n']
        for sub in range(1, r['k'] + 1):
            n_s, k_s = r['n'] // 2 ** (sub - 1), r['kdim'] // 2 ** (sub - 1)
            out.append((n_s, k_s, BM.dceil(a * n_s)))
    return out


T = None


def _init(path):
    global T
    sys.path.insert(0, os.path.join(path, 'scripts'))
    import tune_first_order_mca as mod
    T = mod


def evaluate(n, k, A, m, M, mu, ell=1):
    c = T.certificate(n, k, A, m, M, mu, True, ell=ell, method='best',
                      taylor_degree_model=T.TIGHT_TAYLOR_DEGREE_MODEL)
    if c is None:
        return None
    return dict(E=c['exact_exceptional_bound'], list=c['exact_list_bound'], m=m, B_d=M, B_jet=mu,
                H=c['height'], transfer=c['selected_transfer_method'], transfer_theorem=c['selected_transfer_theorem'],
                list_method=c['selected_list_method'], list_theorem=c['selected_list_theorem'],
                char_gt=c['characteristic_strictly_greater_than'], ell=ell)


def search(args):
    n, k, A, ell = args
    t0 = time.time()
    rho, a = k / n, A / n
    best = None
    for m in list(range(4, 33, 2)) + [40, 48, 64, 80, 96, 128, 160, 192, 256]:
        mu0 = m * a / rho
        for M in sorted(set([max(1, round(m * f)) for f in (0.25, 0.5, 0.75, 1.0, 1.25, 1.5, 2.0)])):
            for f in (0.55, 0.65, 0.75, 0.85, 0.95, 1.05):
                mu = max(M, int(mu0 * f))
                N, r = T.support_counts(n, k, A, m, M, mu, True)
                if N <= n * r:
                    continue
                c = evaluate(n, k, A, m, M, mu, ell)
                if c is None:
                    continue
                e, lst = math.log2(F(c['E'])), math.log2(F(c['list']))
                if e <= E_MAX and lst <= L_MAX and (best is None or (e + 2 * lst) < best[0]):
                    best = (e + 2 * lst, c)
        if best is not None:
            break
    res = None if best is None else best[1]
    return (n, k, A, ell), res, time.time() - t0


def main():
    if len(sys.argv) < 2:
        sys.exit(__doc__)
    path = sys.argv[1]
    if len(sys.argv) > 2 and sys.argv[2] == '--check':
        _init(path)
        data = json.load(open(OUT))
        bad = 0
        for key, c in data.items():
            if key.startswith('_'):
                continue
            n, k, A, ell = map(int, key.split(','))
            d = evaluate(n, k, A, c['m'], c['B_d'], c['B_jet'], ell)
            ok = d is not None and d['E'] == c['E'] and d['list'] == c['list']
            bad += not ok
            print(f"{key}: {'ok' if ok else 'MISMATCH'}  E/|F| = 2^{math.log2(F(c['E'])) - BM.LOG_F:.2f}  list 2^{math.log2(F(c['list'])):.2f}")
        sys.exit(1 if bad else 0)
    shapes = {'final': BM.SHAPES['final (layer d)'], 'inner NV': BM.SHAPES['inner NV (layers 1..d-1)']}
    data = json.load(open(OUT)) if os.path.exists(OUT) else {}
    jobs = []
    for nm, pl in PLANS.items():
        for c in codes_for(shapes[nm], pl['plan']):
            key = f'{c[0]},{c[1]},{c[2]},1'
            if key not in data:
                jobs.append(c + (1,))
    jobs = sorted(set(jobs))
    print(f'{len(jobs)} codes to certify', flush=True)
    with Pool(int(os.environ.get('JOBS', '8')), initializer=_init, initargs=(path,)) as pool:
        for key, res, dt in pool.imap_unordered(search, jobs):
            ks = ','.join(map(str, key))
            if res is None:
                print(f'{ks}: no certificate within the search box [{dt:.0f}s]', flush=True)
                continue
            data[ks] = res
            print(f"{ks}: m={res['m']} B_d={res['B_d']} B_jet={res['B_jet']} E/|F|=2^{math.log2(F(res['E'])) - BM.LOG_F:.2f} "
                  f"list=2^{math.log2(F(res['list'])):.2f} [{dt:.0f}s]", flush=True)
            json.dump(data, open(OUT, 'w'), indent=1, sort_keys=True)
    # final plans: replace uncertified rounds by the fallback
    plans = {}
    for nm, pl in PLANS.items():
        plan = []
        for i, step in enumerate(pl['plan']):
            sub = codes_for(dict(shapes[nm]), [p if j == i else ('J', 64) for j, p in enumerate(pl['plan'])])
            ok = all(f'{c[0]},{c[1]},{c[2]},1' in data for c in sub)
            plan.append(list(step) if ok else list(FALLBACK[nm][i] or ('J', 64)))
        plans[nm] = dict(batching=pl['batching'], plan=plan)
    data['_plans'] = plans
    data['_meta'] = dict(engine=f'rs-beyond-johnson@{DKT_COMMIT} scripts/tune_first_order_mca.py',
                         taylor_model='tight-2D-minus-3-v3', support='derivative-weighted',
                         E_max_log2_over_F=-275, list_max_log2=L_MAX)
    json.dump(data, open(OUT, 'w'), indent=1, sort_keys=True)
    print(json.dumps(plans))


if __name__ == '__main__':
    main()
