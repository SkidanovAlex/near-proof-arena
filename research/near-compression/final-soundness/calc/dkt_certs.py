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
  --check [file]  re-evaluate every stored certificate (no search) and compare; also checks
            E/|F| <= 2^-275, list <= 2^44 and char p > char_gt.  file defaults to dkt_certs.json.
  --table [prio]  O-2 table mode: certify the exact thresholds of AgreementTable::canonical for
            the real shapes (prio 0: final, bound.py final, inner NV, base; 1: + b = 2 chain),
            output dkt_certs_o2.json.
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
GRID_MARGIN = 0.05
J_CURVES = set()


def a1(r):
    """DKT26 eq. (31): first-order agreement threshold."""
    rc = 11 - 3 * math.sqrt(13)
    if r < rc:
        s, lo, hi = math.sqrt(r / 2), 0.0, 1.0
        for _ in range(200):
            mid = (lo + hi) / 2
            lo, hi = (mid, hi) if mid * mid * (mid + 3) < s else (lo, mid)
        return s * (1 + lo)
    return (3 * r + 2 * math.sqrt(r * (5 - r) * (2 - r))) / (8 - r)

# Per-round plans.  ('F', ratio) = first order at A = ceil(ratio * sqrt((k-1)/n) * n);
# ('J', M) = Johnson radius with backend ListDecoding(M) (DKT26 Thm 5.12, no certificate needed).
# Ratios are the largest that reach the next-lower query count (MCA-UPGRADE.md section 3).
# inner r2 at 0.750 (q = 30) was tried: no certificate within the search box for its two
# largest codes, so 0.895 (q = 31) is used.
PLANS = {
    'final': dict(batching='first-curve', plan=[('F', 0.835), ('F', 0.818), ('F', 0.879), ('F', 0.768)]),
    'inner NV': dict(batching='first-curve', plan=[('F', 0.817), ('F', 0.809), ('F', 0.895), ('F', 0.768)]),
}
FALLBACK = {  # used when a stretch ratio cannot be certified
    'final': [None, None, None, ('J', 64)],
    'inner NV': [None, None, ('F', 0.895), ('J', 64)],
}


def codes_for(shape, plan):
    out = []
    for r, (reg, par) in zip(BM.rounds_of(shape), plan):
        if reg != 'F':
            continue
        A = BM.agreement('F', r['n'], r['kdim'], ratio=par)
        a = F(A, r['n'])                       # exact, as bound_mca.layer
        for sub in range(1, r['k'] + 2):      # C^(i,0..k_i): lists for all, MCA for the fold codes
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



# ----------------------------------------------------------------------------------------
# O-2 table mode (--table): certify exactly the agreement thresholds that the recursion lane's
# backend binds into the vk (stark-backend-unified.patch AgreementTable::canonical, lane
# pq-recursion-sha384 @ cf2262a24), for the real shapes of dkt_cert_check.py, round codes and
# fold sub-codes s = 0..k_i (n >> s, k >> s, ceil(A / 2^s)).  Output: dkt_certs_o2.json.
# ----------------------------------------------------------------------------------------
OUT_O2 = os.path.join(HERE, 'dkt_certs_o2.json')
O2_MARGIN_MILLI, O2_M = 50, 64
O2_SHAPES = {   # name: (log_h, b, k1, k, lf, priority)   -- dkt_cert_check.py SH, same names
    'final (extrapolation optimum) b7 h20 k1=1 k4 lf7': (20, 7, 1, 4, 7, 0),
    'final (bound.py) b8 h19 k1=1 k3 lf9': (19, 8, 1, 3, 9, 0),
    'inner NV b6 h19 k1=1 k4 lf6': (19, 6, 1, 4, 6, 0),
    'base app stress b6 h21 k1=1 k4 lf8': (21, 6, 1, 4, 8, 0),
    'measured chain inner b2 h20 k1=1 k4 lf3': (20, 2, 1, 4, 3, 1),
    'measured chain final b2 h21 k1=1 k3 lf8': (21, 2, 1, 3, 8, 1),
}


def o2_agree(n, k, margin_milli=O2_MARGIN_MILLI, m=O2_M):
    """AgreementTable::canonical, operation for operation in IEEE f64 (Python float == Rust f64;
    sqrt, +, *, / correctly rounded; dkt_a1 is the same bisection).  Returns the integer A."""
    cap = 1.0 + 1.0 / (2.0 * max(m, 1))
    rho = k / n
    ratio = min(a1(rho) / math.sqrt(rho) + margin_milli / 1000.0, cap)
    return math.ceil(ratio * math.sqrt((k - 1) / n) * n)


def o2_rounds(log_h, b, k1, k, lf):
    nr = 1 + math.ceil((log_h - k1 - lf) / k)
    ks = [k1] + [k] * (nr - 1)
    n, mv, out = C_ODD_O2 * 2 ** (log_h + b), log_h, []
    for i, ki in enumerate(ks):
        kd = 2 ** mv
        A = o2_agree(n, kd)
        subs = [(n >> s, kd >> s, -(-A // 2 ** s)) for s in range(ki + 1)]   # ceil(A/n * n_s), exact
        out.append(dict(i=i, k=ki, n=n, kdim=kd, A=A, subs=subs))
        mv -= ki
    return out


C_ODD_O2 = 15
O2_CURVE_ELLS = (52, 140, 600)    # W - 1 for W = 53 (NV final b7 h20), 141 (bound.py NV), 601 (base app)


def table_main(path, only_prio):
    data = json.load(open(OUT_O2)) if os.path.exists(OUT_O2) else {}
    certs = {k: v for k, v in data.items() if not k.startswith('_')}
    failed = data.get('_no_certificate', {})
    jobs = []
    for nm, (lh, b, k1, k, lf, pr) in O2_SHAPES.items():
        if pr > only_prio:
            continue
        for r in o2_rounds(lh, b, k1, k, lf):
            for c in r['subs']:
                key = f'{c[0]},{c[1]},{c[2]},1'
                if key not in certs and key not in failed:
                    jobs.append(c + (1,))
        # 'first-curve' mu batching (bound_mca.py): powers curve of degree W-1 on the round-0 code
        c0 = o2_rounds(lh, b, k1, k, lf)[0]['subs'][0]
        for ell in O2_CURVE_ELLS:
            if f'{c0[0]},{c0[1]},{c0[2]},{ell}' not in certs:
                jobs.append(c0 + (ell,))
    jobs = sorted(set(jobs), key=lambda j: j[1])        # small k first
    # reuse supports already found for the same (n, k, A) in dkt_certs.json (plans or grid):
    # re-evaluated here, so the stored record is complete and freshly checked
    old = json.load(open(OUT)) if os.path.exists(OUT) else {}
    prev = {k: v for k, v in old.items() if not k.startswith('_')}
    prev.update(old.get('_grid', {}).get('certs', {}))
    seeded = [j for j in jobs if prev.get(','.join(map(str, j)))]
    if seeded:
        _init(path)
        for j in seeded:
            p = prev[','.join(map(str, j))]
            c = evaluate(*j[:3], p['m'], p['B_d'], p['B_jet'], j[3])
            if c and math.log2(F(c['E'])) <= E_MAX and math.log2(F(c['list'])) <= L_MAX:
                certs[','.join(map(str, j))] = c
                jobs.remove(j)
        print(f'{len(seeded)} supports reused from {os.path.basename(OUT)}', flush=True)
    print(f'{len(jobs)} codes to certify', flush=True)

    def save():
        out = dict(certs)
        out['_no_certificate'] = failed
        out['_meta'] = dict(engine=f'rs-beyond-johnson@{DKT_COMMIT} scripts/tune_first_order_mca.py',
                            taylor_model='tight-2D-minus-3-v3', support='derivative-weighted',
                            E_max_log2_over_F=-275, list_max_log2=L_MAX,
                            rule='A = ceil(min(a1(rho)/sqrt(rho) + margin_milli/1000, 1 + 1/(2m)) * sqrt((k-1)/n) * n) '
                                 'in IEEE f64 (AgreementTable::canonical, lane/pq-recursion-sha384 @ cf2262a24); '
                                 'fold sub-code s: (n >> s, k >> s, ceil(A / 2^s))',
                            margin_milli=O2_MARGIN_MILLI, m=O2_M)
        out['_shapes'] = {nm: [dict(round=r['i'], k_i=r['k'], n=r['n'], kdim=r['kdim'], A=r['A'],
                                    covered=all(f'{c[0]},{c[1]},{c[2]},1' in certs for c in r['subs']),
                                    **({'first_curve_ells': [e for e in O2_CURVE_ELLS
                                        if f"{r['subs'][0][0]},{r['subs'][0][1]},{r['subs'][0][2]},{e}" in certs]} if r['i'] == 0 else {}))
                               for r in o2_rounds(*v[:5])] for nm, v in O2_SHAPES.items()}
        json.dump(out, open(OUT_O2, 'w'), indent=1, sort_keys=True)

    with Pool(int(os.environ.get('JOBS', '8')), initializer=_init, initargs=(path,)) as pool:
        for key, res, dt in pool.imap_unordered(search, jobs):
            ks = ','.join(map(str, key))
            if res is None:
                failed[ks] = 'no certificate within the search box'
                print(f'{ks}: no certificate within the search box [{dt:.0f}s]', flush=True)
            else:
                certs[ks] = res
                print(f"{ks}: m={res['m']} B_d={res['B_d']} B_jet={res['B_jet']} E/|F|=2^{math.log2(F(res['E'])) - BM.LOG_F:.2f} "
                      f"list=2^{math.log2(F(res['list'])):.2f} [{dt:.0f}s]", flush=True)
            save()
    save()


def main():
    if len(sys.argv) < 2:
        sys.exit(__doc__)
    path = sys.argv[1]
    if len(sys.argv) > 2 and sys.argv[2] == '--table':
        table_main(path, int(sys.argv[3]) if len(sys.argv) > 3 else 0)
        return
    if len(sys.argv) > 2 and sys.argv[2] == '--grid':
        # size-model rule: a(rho) = (a1(rho)/sqrt(rho) + GRID_MARGIN) sqrt((k-1)/n), checked at n = 15*2^27
        # (the largest final-layer domain the models allow) for k = 2^j, and at the two first fold codes.
        data = json.load(open(OUT))
        jobs = []
        for j in range(8, 25):
            n, k = 15 * 2 ** 27, 2 ** j
            ratio = a1(k / n) / math.sqrt(k / n) + GRID_MARGIN
            A = BM.dceil(Decimal(ratio) * (Decimal(k - 1) / n).sqrt() * n)
            for s in range(3):
                # exact ceil(A / 2^s).  (The stored grid was made with dceil(Decimal(A) / n * n_s), which
                # rounds A/n up in the last digit and gives A + 1 at s = 0 for some k; superseded by
                # --table / dkt_certs_o2.json.)
                jobs.append((n >> s, k >> s, -(-A // 2 ** s), 1))
        grid = {}
        with Pool(int(os.environ.get('JOBS', '8')), initializer=_init, initargs=(path,)) as pool:
            for key, res, dt in pool.imap_unordered(search, jobs):
                ks = ','.join(map(str, key))
                grid[ks] = None if res is None else dict(E=res['E'], list=res['list'], m=res['m'], B_d=res['B_d'], B_jet=res['B_jet'])
                print(ks, 'FAIL' if res is None else f"E/|F|=2^{math.log2(F(res['E'])) - BM.LOG_F:.2f} list=2^{math.log2(F(res['list'])):.2f}", f'[{dt:.0f}s]', flush=True)
        data['_grid'] = dict(margin=GRID_MARGIN, n=15 * 2 ** 27, certs=grid)
        json.dump(data, open(OUT, 'w'), indent=1, sort_keys=True)
        return
    if len(sys.argv) > 2 and sys.argv[2] == '--check':
        _init(path)
        data = json.load(open(sys.argv[3] if len(sys.argv) > 3 else OUT))
        bad = 0
        for key, c in data.items():
            if key.startswith('_'):
                continue
            n, k, A, ell = map(int, key.split(','))
            d = evaluate(n, k, A, c['m'], c['B_d'], c['B_jet'], ell)
            ok = (d is not None and d['E'] == c['E'] and d['list'] == c['list'] and int(c['char_gt']) < BM.P
                  and math.log2(F(c['E'])) <= E_MAX and math.log2(F(c['list'])) <= L_MAX)
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
        if pl['batching'] == 'first-curve' and pl['plan'][0][0] == 'F':   # mu batching: powers, degree W-1
            c0 = codes_for(shapes[nm], pl['plan'][:1])[0]
            if f"{c0[0]},{c0[1]},{c0[2]},{shapes[nm]['W'] - 1}" not in data:
                jobs.append(c0 + (shapes[nm]['W'] - 1,))
    # O-1 alone: mu batching (powers, degree W-1) at the Johnson agreement of ListDecoding(64), via the
    # first-order curve theorem (DKT26 Lemma 5.9 / Cor 7.3; any a > a1 is allowed).
    for sh in (BM.SHAPES['final (layer d)'], BM.SHAPES['inner NV (layers 1..d-1)'], BM.SHAPES['base app (layer 0, stress)']):
        r0 = BM.rounds_of(sh)[0]
        cj = (r0['n'], r0['kdim'], BM.agreement('J', r0['n'], r0['kdim'], M=64), sh['W'] - 1)
        J_CURVES.add(','.join(map(str, cj)))
        if ','.join(map(str, cj)) not in data:
            jobs.append(cj)
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
    need = set()
    for nm, pl in plans.items():
        for c in codes_for(shapes[nm], [tuple(x) for x in pl['plan']]):
            need.add(f'{c[0]},{c[1]},{c[2]},1')
        if pl['batching'] == 'first-curve' and pl['plan'][0][0] == 'F':
            c0 = codes_for(shapes[nm], [tuple(pl['plan'][0])])[0]
            need.add(f"{c0[0]},{c0[1]},{c0[2]},{shapes[nm]['W'] - 1}")
    data = {k: v for k, v in data.items() if k in need or k in J_CURVES or k == '_grid'}     # drop certificates no plan uses
    data['_plans'] = plans
    data['_meta'] = dict(engine=f'rs-beyond-johnson@{DKT_COMMIT} scripts/tune_first_order_mca.py',
                         taylor_model='tight-2D-minus-3-v3', support='derivative-weighted',
                         E_max_log2_over_F=-275, list_max_log2=L_MAX)
    json.dump(data, open(OUT, 'w'), indent=1, sort_keys=True)
    print(json.dumps(plans))


if __name__ == '__main__':
    main()
