#!/usr/bin/env python3
"""Upgraded per-round WHIR bound for the PQ SWIRL stack (lane/pq-mca-upgrade).

Same protocol, moves and QROM accounting as bound.py (PROOF.md sections 3-7). What changes is
the proximity/MCA input of PROOF.md section 4, i.e. the agreement a_i = 1 - delta_i at which
every WHIR round is analysed, and the list / MCA / batching constants that come with it.

Regimes (one per WHIR round; MCA-UPGRADE.md section 2 has the theorem statements):

  bcgm   today's bound.  a = (1+1/2m) sqrt(rho), m = 3.  Fold and mu-batching MCA from
         BCGM ePrint 2025/2051 Def 9.1 / Thm 9.2 (CCC 2026).  List m/rho.
  J      O-1, Johnson radius.  a = sqrt(rho)(1+1/2M) for a large backend ListDecoding(M).
         Line MCA, every characteristic, any evaluation set: DKT26 Thm 5.12 (Lean:
         johnson_lineMCA_probability).  Multi-variable fold: DKT26 Cor 7.7/7.8 (Lean:
         fullSetLevelWitness_interleaved_of_exactAgreement, tensorFoldBad_card_le) -- one
         line count per fold sub-round, width independent.  List: Thm 5.12 eq (67).
         mu-batching of the W stacked columns (powers, degree W-1) -- three options:
            'bchks46' BCHKS25 Thm 4.6 (powers MCA up to Johnson; proof sketched),
            'tensor'  backend change: batch with eq-weights of h = ceil(log2 W) challenges,
                      DKT26 Cor 7.8 (Lean) -> h * E_line / |F|,
            'affine'  backend change: W-1 independent challenges, BCGM Lemma 7.1 /
                      DKT26 Cor 7.2 -> E_line / (|F|-1).
  F      O-2, first-order beyond Johnson.  a = A/n below sqrt(rho).  DKT26 Thm 5.8 /
         Prop 5.10 / Lemma 5.9 / Lemma 5.11 with an explicit finite certificate
         (m, B_d, B_jet) per code, produced and checked with the authors' exact-arithmetic
         engine (github.com/quangvdao/rs-beyond-johnson @ 60b7257) by dkt_certs.py; the
         resulting integers are stored in dkt_certs.json and read here.  Needs
         char p > max(k-1, B_d): p = 2^30.9 > 2^21 >= k for every code here.

Query counts use the backend's logic with alpha_i := a_i:
      q_i = ceil((security_bits - query_pow_bits) / -log2(a_i)) = ceil(236 / -log2 a_i).
OOD samples per round u_i >= 1 are raised only if the list makes l^2/2 (2^m_i/|F|)^u exceed
the budget (each extra sample: one Ext12 answer, 48 B).

Usage: python3 -I bound_mca.py   (stdlib only; prints the tables; writes nothing)
"""
import json
import math
import os
import sys
from decimal import Decimal, getcontext, ROUND_CEILING
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import bound as B  # noqa: E402  (same directory; shares constants and the QROM theorem)

getcontext().prec = 80
LOG2 = math.log2
LOG_F, Z, TARGET, C_ODD = B.LOG_F, B.Z, B.TARGET, B.C_ODD
QBITS = TARGET - Z                    # 236 query bits per round
BUDGET = -270.0                       # every non-query move must stay below this (query moves sit at ~-268)
P = B.P
CERTS = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'dkt_certs.json')


def lg(x):
    return LOG2(x) if x > 0 else -math.inf


def dceil(x):
    return int(x.to_integral_value(rounding=ROUND_CEILING))


# ----------------------------------------------------------------------------------------
# BCGM (today) -- identical to bound.py
# ----------------------------------------------------------------------------------------
def bcgm_err(d, n, k, m=3):
    rho = k / n
    return B.log_mca(d, LOG2(n), LOG2(rho), m)


# ----------------------------------------------------------------------------------------
# DKT26 Thm 5.12 (ordinary / Johnson line MCA, every characteristic, any evaluation set)
# ----------------------------------------------------------------------------------------
def psi(D, Bj):
    """Lemma 5.3 challenge-degree coefficient of the joint image bound."""
    return 1 + (2 * D - 1) * (2 * Bj - 1) + 2 * max(0, Bj - 2 * D - 1)


def dkt_johnson(n, k, A):
    """Theorem 5.12 at (n, D = k-1, A): returns (log2 E, list bound, m_DKT).

    E is the larger of the two printed forms of E_ord^(1) (Lemma 5.3 with L = D+1, and the
    Thm 5.8 display (2b-1)h + lam (h + b + 4Dbh) + (n-D-1)b), so either reading is covered.
    """
    D = k - 1
    assert 1 <= D <= n - 2
    x = (Decimal(D) / Decimal(n)).sqrt()
    eta0 = Decimal(A) / Decimal(n) - x
    assert eta0 > 0, 'agreement must exceed the finite Johnson radius sqrt((k-1)/n)'
    m = max(dceil(x / (2 * eta0)), 3)
    t = Decimal(m) + Decimal('0.5')
    Bj = dceil(t / x) - 1
    H = dceil(t * t / (3 * x * x)) - 1
    lam = Fraction(n - D, A - D)
    e1 = (2 * Bj - 1) * H + lam * (Bj + H * psi(D, Bj)) + (n - D - 1) * Bj
    e2 = (2 * Bj - 1) * H + lam * (H + Bj + 4 * D * Bj * H) + (n - D - 1) * Bj
    E = max(e1, e2)
    pair = Fraction(n * (A - D), A * A - n * D) if A * A > n * D else math.inf
    lst = min(Bj, math.floor(pair))
    return LOG2(E), lst, m


def bchks46(M, n, k, A):
    """BCHKS25 Thm 4.6 (list correlated agreement for the powers generator of degree M, up to
    Johnson), with the paper's convention deg <= kk, rho = kk/n, gamma = 1 - A/n and the
    stated (conservative) m = max(ceil(sqrt(rho)/(1-sqrt(rho)-gamma)), 3).  Returns log2 |E|."""
    kk = k - 1
    rho = Decimal(kk) / Decimal(n)
    sr = rho.sqrt()
    gamma = 1 - Decimal(A) / Decimal(n)
    eta = 1 - sr - gamma
    assert eta > 0
    m = max(dceil(sr / eta), 3)
    t = Decimal(m) + Decimal('0.5')
    a = (2 * t ** 5 + 3 * t * gamma * rho) / (3 * rho * sr) * n + t / sr
    return LOG2(float(M * a))


# ----------------------------------------------------------------------------------------
# DKT26 first-order certificates (O-2), produced by dkt_certs.py
# ----------------------------------------------------------------------------------------
_certs = None


def first_order(n, k, A, ell=1):
    global _certs
    if _certs is None:
        _certs = json.load(open(CERTS)) if os.path.exists(CERTS) else {}
    c = _certs.get(f'{n},{k},{A},{ell}')
    if c is None:
        return None
    return LOG2(Fraction(c['E'])), Fraction(c['list'])


# ----------------------------------------------------------------------------------------
# WHIR schedule with a per-round agreement rule (config.rs:405-478 structure)
# ----------------------------------------------------------------------------------------
def rounds_of(s):
    log_h, b, k1, k, lf = s['log_h'], s['b'], s['k1'], s['k'], s['lf']
    n_rounds = 1 + math.ceil((log_h - k1 - lf) / k)
    ks = [k1 if i == 0 else k for i in range(n_rounds)]
    n = C_ODD * 2 ** (log_h + b)               # keep-domain: |L_i| constant
    out, mv = [], log_h
    for i, ki in enumerate(ks):
        out.append(dict(i=i, k=ki, n=n, kdim=2 ** mv, mvars=mv))
        mv -= ki
    return out


def agreement(regime, n, kdim, M=None, ratio=None):
    """Integer agreement threshold A for code (n, kdim)."""
    if regime == 'bcgm':
        return math.ceil(Decimal(7) / 6 * (Decimal(kdim) / n).sqrt() * n)
    if regime == 'J':
        return dceil((1 + Decimal(1) / (2 * M)) * (Decimal(kdim) / n).sqrt() * n)
    if regime == 'F':
        return dceil(Decimal(ratio) * (Decimal(kdim - 1) / n).sqrt() * n)
    raise ValueError(regime)


def code_terms(regime, n, kdim, a_frac, ell=1):
    """(log2 line-MCA error, list bound) for code (n, kdim) at agreement fraction a_frac."""
    A = dceil(Decimal(a_frac) * n)
    if regime == 'bcgm':
        return bcgm_err(1, n, kdim), 3 * n / kdim
    if regime == 'J':
        e, lst, _ = dkt_johnson(n, kdim, A)
        return e - LOG_F, lst
    if regime == 'F':
        r = first_order(n, kdim, A, ell)
        if r is None:
            return None
        return r[0] - LOG_F, r[1]
    raise ValueError(regime)


def layer(s, plan, batching='bchks46', verbose=False):
    """plan: list of (regime, param) per WHIR round.  Returns dict with schedule and moves."""
    rds = rounds_of(s)
    assert len(plan) == len(rds), (len(plan), len(rds))
    for r, (reg, par) in zip(rds, plan):
        if reg == 'bcgm':
            A = agreement('bcgm', r['n'], r['kdim'])
        elif reg == 'J':
            A = agreement('J', r['n'], r['kdim'], M=par)
        else:
            A = agreement('F', r['n'], r['kdim'], ratio=par)
        r.update(reg=reg, par=par, A=A, a=Decimal(A) / r['n'], log_a=LOG2(A / r['n']))
        r['q'] = math.ceil(QBITS / -r['log_a'])
        # codes C^(i,s) = RS[L_i^(2^s), m_i - s], s = 0..k_i (Pus26 Thm 5.3 needs lists for all of
        # them and MCA for s >= 1).  The fold move s is charged the MCA of C^(i,s-1) (length
        # n/2^(s-1), conservative as in bound.py) and, for safety, the max over all codes.
        terms = []
        for sub in range(1, r['k'] + 2):
            n_s, k_s = r['n'] // 2 ** (sub - 1), r['kdim'] // 2 ** (sub - 1)
            t = code_terms(reg, n_s, k_s, r['a'])
            if t is None:
                raise SystemExit(f'missing first-order certificate for n={n_s} k={k_s} a={float(r["a"]):.6g}: run dkt_certs.py')
            terms.append(t)
        r['fold_err'] = [max(t[0] for t in terms)] * r['k']
        r['list'] = max(float(t[1]) for t in terms)
        r['log_list'] = LOG2(r['list'])
    # OOD samples
    for j, r in enumerate(rds):
        u = 1
        if j > 0:
            while 2 * r['log_list'] - 1 + u * (r['mvars'] - LOG_F) > BUDGET:
                u += 1
        r['u'] = u
    mv = []

    def add(name, e):
        mv.append((name, e))

    r0 = rds[0]
    lst0 = r0['log_list'] * s.get('commits', 1)
    N, ml = s['log_int'], s['msg_len']
    add('logup alpha,beta (L3.1)', lst0 + B.lsum(lg(ml) + 2 * N - 1, 1 + N) - LOG_F)
    add('gkr sumcheck round + xi coordinate (L3.2, L3.3)', lst0 + lg(3 + 2 ** B.L_SKIP) - LOG_F)
    add('constraint batching lambda (L3.4)', lst0 + lg(s['n_constraints'] - 1) - LOG_F)
    add('claim batching mu (L3.4)', lst0 + lg(3 * s['airs'] - 1) - LOG_F)
    d = s['degree']
    add('zerocheck univariate round r_0 (L3.5)', lst0 + lg((d + 1) * (2 ** B.L_SKIP - 1)) - LOG_F)
    add('stacking lambda (L3.7)', lst0 + lg(2 * s['cols'] - 1) - LOG_F)
    W = s['W']
    # mu batching at round 0's agreement
    if r0['reg'] == 'bcgm':
        eb = bcgm_err(W - 1, r0['n'], r0['kdim'])
        bname = 'BCGM Thm 9.2 d=W-1'
    elif batching == 'bchks46':
        eb = bchks46(W - 1, r0['n'], r0['kdim'], r0['A']) - LOG_F
        bname = 'BCHKS25 Thm 4.6 powers'
    elif batching == 'tensor':
        eb = lg(math.ceil(LOG2(W))) + r0['fold_err'][0]
        bname = 'tensor batching, DKT26 Cor 7.8'
    elif batching == 'affine':
        eb = r0['fold_err'][0] + 1e-9
        bname = 'affine batching, BCGM L7.1 / DKT26 Cor 7.2'
    elif batching == 'first-curve':
        t = code_terms('F', r0['n'], r0['kdim'], r0['a'], ell=W - 1)
        if t is None:
            raise SystemExit('missing first-order powers certificate: run dkt_certs.py')
        eb = t[0]
        bname = 'DKT26 first-order curve, ell=W-1'
    else:
        raise ValueError(batching)
    add(f'whir mu batching ({bname}) (L4.2)', B.lsum(eb, r0['log_list'] + lg(W - 1) - LOG_F))
    for j, r in enumerate(rds):
        last = j == len(rds) - 1
        for sub in range(1, r['k'] + 1):
            add(f'whir fold r{j}.{sub} (L4.3)', B.lsum(r['fold_err'][sub - 1], r['log_list'] + lg(3) - LOG_F))
        if not last:
            nx = rds[j + 1]
            add(f'whir OOD r{j + 1} x{nx["u"]} (L4.4)', 2 * nx['log_list'] - 1 + nx['u'] * (nx['mvars'] - LOG_F))
        add(f'whir query r{j} incl. grinding z={Z} (L4.5, L5.1)', -Z + r['q'] * r['log_a'])
        if last:
            add(f'whir final gamma r{j} (L4.6)', lg(r['q'] + 1) - LOG_F)
        else:
            add(f'whir gamma r{j} (L4.6)', rds[j + 1]['log_list'] + lg(r['q'] + rds[j + 1]['u']) - LOG_F)
    worst_nq = max((e, nm) for nm, e in mv if 'query' not in nm)
    worst = max((e, nm) for nm, e in mv)
    return dict(rounds=rds, moves=mv, worst=worst, worst_nonquery=worst_nq,
                q=[r['q'] for r in rds], u=[r['u'] for r in rds])


SHAPES = B.SHAPES


def show(name, s, plan, batching, label):
    res = layer(s, plan, batching)
    print(f"-- {name} [{label}]  queries {res['q']}  (sum {sum(res['q'])})  OOD {res['u']}")
    for r in res['rounds']:
        extra = f"m_DKT={dkt_johnson(r['n'], r['kdim'], r['A'])[2]}" if r['reg'] == 'J' else ''
        print(f"   r{r['i']}: {r['reg']:4} rho=2^{LOG2(r['kdim'] / r['n']):.2f} a/sqrt(rho)={float(r['a']) / math.sqrt(r['kdim'] / r['n']):.5f} "
              f"bits/query={-r['log_a']:.3f} q={r['q']} -> {-r['q'] * r['log_a']:.2f}+{Z}; list<=2^{r['log_list']:.2f}; "
              f"fold MCA max 2^{max(r['fold_err']):.2f} {extra}")
    print(f"   worst non-query move: 2^{res['worst_nonquery'][0]:.2f}  [{res['worst_nonquery'][1]}]")
    print(f"   worst move:           2^{res['worst'][0]:.2f}  [{res['worst'][1]}]")
    return res


def main():
    print(f"|F| = 2^{LOG_F:.2f}; per-round target {TARGET} = {QBITS} query bits + z = {Z}; non-query budget 2^{BUDGET}\n")
    final, inner, base = (SHAPES[k] for k in ('final (layer d)', 'inner NV (layers 1..d-1)', 'base app (layer 0, stress)'))
    out = {}
    for M in (64, 1024):
        print(f"==== O-1: Johnson radius, backend ListDecoding(m = {M}) ====")
        for nm, s in (('final', final), ('inner NV', inner), ('base stress', base)):
            plan = [('J', M)] * len(rounds_of(s))
            for bt in ('bchks46', 'tensor'):
                out[(nm, 'J', M, bt)] = show(nm, s, plan, bt, f'J m={M}, batching {bt}')
        print()
    print("==== today: BCGM m = 3 ====")
    for nm, s in (('final', final), ('inner NV', inner), ('base stress', base)):
        out[(nm, 'bcgm')] = show(nm, s, [('bcgm', 3)] * len(rounds_of(s)), 'bchks46', 'BCGM m=3')
    if os.path.exists(CERTS):
        cert = json.load(open(CERTS))
        plans = cert.get('_plans', {})
        print("\n==== O-2: first-order certificates (dkt_certs.json) ====")
        for nm, s in (('final', final), ('inner NV', inner)):
            if nm in plans:
                pl = [tuple(x) for x in plans[nm]['plan']]
                out[(nm, 'F')] = show(nm, s, pl, plans[nm].get('batching', 'tensor'), 'O-1+O-2 per-round best')
    # QROM totals (Theorem 6.1/7.4 of PROOF.md, unchanged)
    print("\n==== end-to-end (PROOF.md Thm 6.4 / 7.4, unchanged accounting) ====")
    for key in sorted(out, key=str):
        eps = out[key]['worst'][0]
        tot = B.fs_bound_k0(eps, B.T_LOG)
        print(f"   {str(key):45} eps_rbr = 2^{eps:.2f}  total 2^{tot:.2f}  (7-layer union 2^{tot + LOG2(7):.2f})")
    return out


if __name__ == '__main__':
    main()
