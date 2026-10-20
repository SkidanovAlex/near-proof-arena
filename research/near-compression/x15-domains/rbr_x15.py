"""Per-round (round-by-round) WHIR soundness errors on 15*2^N evaluation domains.

Recomputes every error term of WHIR Theorem 5.2 (ePrint 2024/1586) at the
shapes the L4-C model picks (models-C/ext.py) with the x15 domain lever, using

  * MCA error: Bordage-Chiesa-Guan-Manzur, ePrint 2025/2051, Def. 9.1 / Thm 9.2
        eps = (m+1/2)^7 / (3 rho^{3/2}) * d * n^2 / |F|      (d = generator degree)
    (for comparison only: BCHKS25 = ECCC TR25-169 Thm 1.5, a/|F| with
        a = (2(m+1/2)^5 + 3(m+1/2) gamma rho)/(3 rho^{3/2}) * n + (m+1/2)/sqrt(rho),
     which is what the pinned stark-backend calculator uses (CA, + Haboeck MCA));
  * Johnson list size l = 1/(2 eta sqrt(rho)) = m/rho at eta = sqrt(rho)/(2m)
    (WHIR Thm 4.3), radius delta = 1 - (1+1/(2m)) sqrt(rho)  (= BCGM's gamma bound);
  * eps_fold = 3 l/|F| + eps_MCA(d=1);  eps_out = 2^{m_i} l^2 /(2|F|);
    eps_shift = (1-delta)^t + l (t+1)/|F|;  eps_fin = (1-delta)^t;
    mu batching (W stacked columns, powers generator) = eps_MCA(d = W-1).

n = 15 * 2^(log_h + b - i) in round i (shrink = 1), or 15 * 2^(log_h + b) for
all rounds with non-shrinking domains (E5).  |F| = p^12, log2 = 370.88
(NOT 372 = 12*31, which the L4-C note used).

Output: worst term per source, in log2, per scenario.  Model numbers only;
the theorems' applicability to 15*2^N domains is argued in SOUNDNESS.md.
"""
import math
import sys

P = 15 * 2**27 + 1
LOG_F = 12 * math.log2(P)
L15 = math.log2(15)


def lg_add(*xs):
    m = max(xs)
    return m + math.log2(sum(2 ** (x - m) for x in xs))


def mca_bcgm(log_n, log_rho, d, m):
    return (7 * math.log2(m + 0.5) - math.log2(3) - 1.5 * log_rho
            + math.log2(d) + 2 * log_n - LOG_F)


def ca_bchks(log_n, log_rho, m):
    rho = 2 ** log_rho
    gamma = 1 - math.sqrt(rho) * (1 + 1 / (2 * m))
    a = ((2 * (m + .5) ** 5 + 3 * (m + .5) * gamma * rho) / (3 * rho ** 1.5) * 2 ** log_n
         + (m + .5) / math.sqrt(rho))
    return math.log2(a) - LOG_F


def per_query_bits(log_rho, m):
    return -math.log2((1 + 1 / (2 * m)) * 2 ** (log_rho / 2))


def rounds(shape, ex, shrink):
    """yield (i, log_n_i, log_deg_i, k_i) for WHIR rounds of the model shape."""
    b, k1, k, log_h, lf = shape['b'], shape['k1'], shape['k'], shape['log_h'], shape['lf']
    out = [(0, log_h + b + ex, log_h, k1)]
    deg, i = log_h - k1, 1
    while deg > lf:
        out.append((i, log_h + b + ex - shrink * i, deg, k))
        deg -= k
        i += 1
    return out, deg


def analyse(shape, W, m, target, z, ex=L15, shrink=1, mca='bcgm'):
    rs, _ = rounds(shape, ex, shrink)
    worst = {}

    def put(key, val):
        worst[key] = max(worst.get(key, -1e9), val)
    log_l = lambda log_rho: math.log2(m) - log_rho          # Johnson list size m/rho
    qs = []
    n0, d0 = rs[0][1], rs[0][2]
    rho0 = d0 - n0
    put('mu (d=W-1)', mca_bcgm(n0, rho0, W - 1, m) if mca == 'bcgm'
        else ca_bchks(n0, rho0, m) + math.log2(W - 1))
    for idx, (i, log_n, deg, ki) in enumerate(rs):
        log_rho = deg - log_n
        ll = log_l(log_rho)
        for s in range(1, ki + 1):
            e = (mca_bcgm(log_n - s, log_rho, 1, m) if mca == 'bcgm'
                 else ca_bchks(log_n - s, log_rho, m))
            put('fold (MCA + sumcheck)', lg_add(e, math.log2(3) + ll - LOG_F))
            put('  of which MCA', e)
        t = math.ceil(target / per_query_bits(log_rho, m))
        qs.append(t)
        q_err = -t * per_query_bits(log_rho, m) - z
        if idx + 1 < len(rs):
            _, n_next, deg_next, _ = rs[idx + 1]
            ll_next = log_l(deg_next - n_next)
            put('out (OOD)', deg_next + 2 * ll_next - 1 - LOG_F)
            put('shift (queries + gamma)', lg_add(q_err, ll_next + math.log2(t + 1) - LOG_F))
        else:
            put('fin (queries)', q_err)
    return worst, qs, rs


SCEN = {
    # Shapes printed by the models-C fixed point at c_sha = 19,448 (measured L3 SHA AIR),
    # 460 columns (scratch: shapes.py; same base() as models-C/run.py).  W = stacked width.
    # name: (shape, W, query target, grinding z, shrink)
    'T x15 final':            (dict(b=7, k1=1, k=4, log_h=20, lf=7), 151, 268, 0, 1),
    'T x15 penultimate':      (dict(b=9, k1=1, k=3, log_h=18, lf=11), 601, 268, 0, 1),
    'L x15 final':            (dict(b=7, k1=1, k=4, log_h=20, lf=7), 133, 226, 32, 1),
    'L x15 penultimate':      (dict(b=9, k1=1, k=3, log_h=18, lf=11), 529, 236, 32, 1),
    'T COMBO+E5 final':       (dict(b=7, k1=1, k=4, log_h=20, lf=7), 96, 268, 0, 0),
    'T COMBO+E5 penultimate': (dict(b=8, k1=1, k=5, log_h=19, lf=8), 191, 268, 0, 0),
    'L COMBO+E5 final':       (dict(b=7, k1=1, k=4, log_h=20, lf=7), 86, 226, 32, 0),
    'L COMBO+E5 penultimate': (dict(b=9, k1=1, k=4, log_h=18, lf=9), 342, 236, 32, 0),
    'stress: h+b=27, b=8':    (dict(b=8, k1=1, k=4, log_h=19, lf=7), 111, 268, 0, 1),
}


def main():
    print(f"log2|Ext12| = {LOG_F:.2f}")
    for mca in ('bcgm', 'bchks'):
        print(f"\n=== MCA bound: {'BCGM ePrint 2025/2051 Thm 9.2 (contract)' if mca == 'bcgm' else 'BCHKS25 Thm 1.5 (backend calculator; comparison)'} ===")
        for name, (shape, W, target, z, shrink) in SCEN.items():
            for m in (3, 8):
                for ex, tag in ((L15, 'x15'), (0.0, 'x1 ')):
                    if tag == 'x1 ' and 'stress' not in name:
                        continue
                    worst, qs, rs = analyse(shape, W, m, target, z, ex, shrink, mca)
                    n0 = rs[0][1]
                    line = ' '.join(f"{k.strip()}={v:7.1f}" for k, v in worst.items())
                    print(f"{name:42} {tag} m={m} n0=2^{n0:.2f} rho0=2^{shape['log_h']-n0:.2f} q={qs}\n    {line}")
                    worst_nonquery = max(v for k, v in worst.items() if 'queries' not in k)
                    print(f"    worst non-query term 2^{worst_nonquery:.1f}: margin to 2^-268 = {-268 - worst_nonquery:+.1f} bits, to 2^-258 = {-258 - worst_nonquery:+.1f}")


if __name__ == '__main__':
    main()
