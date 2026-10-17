#!/usr/bin/env python3
"""Numerics for HROB.md: block-robust rbr of WHIR-Y and the resulting digest width.

Stdlib only.  Reuses Theorem 4's chain bound from wb_bound.py (bound(..., hat=...)),
with the robust errors eps_rob(m) proven in HROB.md (Theorem R) instead of Lemma 5:

  query move on oracle j (q_j queries, radius delta_j, B_j blocks):
      eps_q(m) = Lfac_j(m) * N_j(m) * (1-delta_j)^q_j         N_j(m) = sum_{i<=m} C(B_j, i)
      Lfac_j(m) = 1 for m = 0, for variant U, and for the final query move;
                  Johnson list size l_{j+1}(delta_{j+1} + m/B_{j+1}) otherwise (variant L).
      (min with Lemma 5 of ANALYSIS.md at alpha = 1 - delta_j, which is also valid.)
  fold / batching move on oracle j at level m:
      err*_MCA(delta_j + m/B_j) + l * d / |F|   (BCGM Thm 9.2, minimal multiplicity M' <= MMAX)
  OOD / combination moves: l^2 2^{m_j} / |F|, l (t+1) / |F|  (negligible, included).

Radius choice (Theorem R, conditions (F) and, for variant U, (O)):
      delta_j = J_M(rho_j) - K/B_j                 (variant L; J_M = 1 - (1 + 1/2M) sqrt(rho))
      delta_j = min(J_M - K/B_j, 1 - sqrt(rho) - 2K/B_j - margin)   (variant U)
and q_j = ceil(target / -log2(1 - delta_j)) + extra.

Bytes: q_j * leaf_j  +  D * (narrow multiproof siblings, levels >= c_j)
                     + 48 * (wide siblings, levels 1..c_j-1)           (cap_cost.sib)
Baseline: today's shape at D = 42 B, delta_j = J_M, no blocks.

Usage: python3 hrob.py            # tables (writes hrob_table.txt via shell redirect)
"""
import math, sys
import wb_bound
from wb_bound import lcomb, lsum, ladd, NEG
from cap_cost import sib

LOGF = 12 * math.log2(2013265921)      # |Ext12 over BabyBear| = p^12, log2 = 370.88
MMAX = 64

# final 12k shape (levers_model, m = 8): oracle j = f_0..f_3
SHAPE = dict(
    name="final 12k today (b=8,k1=1,k=3,h=19, M=8, 268 bits)",
    logrho=[8, 8, 10, 12],          # log2 inverse rate of oracle j
    logn=[27, 26, 25, 24],          # log2 |L_j|
    depth=[26, 23, 22, 21],         # Merkle depth = log2(#leaves), leaf = fold coset
    leaf=[1760, 384, 384, 384],     # opened bytes per query (220 cols x 2 rows x 4 B; 8 x Ext12)
    bdeg=[219, 1, 1, 1],            # max generator degree at the oracle's first random combination
    M=8, target=268, z=0,
)


def J(logrho, M):
    return 1 - (1 + 1 / (2 * M)) * 2 ** (-logrho / 2)


def johnson_list(logrho, r):
    """log2 of the Johnson list size 1/(2 eps sqrt rho) at radius r = 1 - sqrt(rho) - eps."""
    s = 2 ** (-logrho / 2)
    eps = 1 - s - r
    if eps <= 0:
        return math.inf
    return max(0.0, -math.log2(2 * eps * s))


def mca_err(logrho, logn, r, d):
    """log2 BCGM Thm 9.2 error at radius r, minimal multiplicity M' in [3, MMAX]; inf if none."""
    s = 2 ** (-logrho / 2)
    for Mp in range(3, MMAX + 1):
        if r <= 1 - (1 + 1 / (2 * Mp)) * s:
            return (7 * math.log2(Mp + 0.5) - math.log2(3) + 1.5 * logrho
                    + math.log2(max(d, 1)) + 2 * logn - LOGF)
    return math.inf


def radii(sh, cs, K, variant):
    out = []
    for j, c in enumerate(cs):
        B = 2 ** c
        eta = K / B
        d = J(sh["logrho"][j], sh["M"]) - eta
        if variant == "U":
            s = 2 ** (-sh["logrho"][j] / 2)
            d = min(d, 1 - s - 2 * eta - s / 64)
        out.append(d)
    return out


def eps_rob(sh, cs, K, deltas, qs, variant, top):
    """log2 eps_rob(m), m = 0..top: max over moves of the Theorem R bounds."""
    nor = len(cs)
    res = []
    for m in range(top + 1):
        worst = NEG
        for j in range(nor):
            B = 2 ** cs[j]
            # query move on oracle j
            lN = lsum(lcomb(B, i) for i in range(m + 1))
            base = qs[j] * math.log2(1 - deltas[j])
            if m == 0 or variant == "U" or j == nor - 1:
                lf = 0.0
            else:
                Bn = 2 ** cs[j + 1]
                lf = johnson_list(sh["logrho"][j + 1], deltas[j + 1] + m / Bn)
            e = lf + lN + base
            # Lemma 5 alternative (alpha = 1 - delta_j)
            wb_bound.SHIFT = False
            e5 = wb_bound.eps_query(qs[j], -math.log2(1 - deltas[j]), B, m) if m <= B else 0.0
            worst = max(worst, min(e, e5))
            # fold / batching moves on oracle j (radius shifted by m/B_j)
            r = deltas[j] + m / B
            fe = mca_err(sh["logrho"][j], sh["logn"][j], r, sh["bdeg"][j])
            ll = johnson_list(sh["logrho"][j], r)
            fe = ladd(fe, ll + math.log2(3) - LOGF) if fe != math.inf else math.inf
            # OOD / combination (list at r, or at r + K/B for variant U)
            rr = r + (K / B if variant == "U" else 0.0)
            lo = johnson_list(sh["logrho"][j], rr)
            ood = 2 * lo + sh["logn"][j] - LOGF if lo != math.inf else math.inf
            comb = lo + math.log2(qs[j] + 1) - LOGF if lo != math.inf else math.inf
            worst = max(worst, fe, ood, comb)
        res.append(min(worst, 0.0))
    return res


def bytes_of(sh, qs, cs, D):
    tot = 0.0
    for j, q in enumerate(qs):
        c = cs[j]
        narrow = sum(sib(l, q) for l in range(max(c, 1), sh["depth"][j] + 1))
        wide = sum(sib(l, q) for l in range(1, c))
        tot += q * sh["leaf"][j] + D * narrow + 48 * wide
    return tot


def nmin_for(sh, cs, K, variant, extra):
    deltas = radii(sh, cs, K, variant)
    if min(deltas) <= 0:
        return None
    qs = [math.ceil((sh["target"] - sh["z"]) / -math.log2(1 - d)) + extra for d in deltas]
    hat_raw = eps_rob(sh, cs, K, deltas, qs, variant, K + 1)
    if any(x == math.inf for x in hat_raw[:K + 1]):
        return None
    hat, cur = [], NEG
    for e in hat_raw:
        cur = max(cur, e); hat.append(cur)
    for n in range(190, 340):
        P = wb_bound.bound(n, None, None, K, z=sh["z"], hat=hat)
        if P <= -128:
            return n, qs, deltas, hat
    return None


def baseline(sh, D=42):
    qs = [math.ceil((sh["target"] - sh["z"]) / -math.log2(1 - J(r, sh["M"]))) for r in sh["logrho"]]
    return qs, bytes_of(sh, qs, [0] * len(qs), D)


def search(sh, variant, cs_list, Ks=range(0, 21), extras=(0, 1, 2, 3, 4, 6, 8)):
    qb, b0 = baseline(sh)
    best = None
    rows = []
    for cs in cs_list:
        rbest = None
        for K in Ks:
            for ex in extras:
                r = nmin_for(sh, cs, K, variant, ex)
                if r is None:
                    continue
                n, qs, deltas, hat = r
                D = math.ceil(n / 8)
                by = bytes_of(sh, qs, cs, D)
                cand = (b0 - by, K, ex, n, D, qs)
                if rbest is None or cand[0] > rbest[0]:
                    rbest = cand
        rows.append((cs, rbest))
        if rbest and (best is None or rbest[0] > best[1][0]):
            best = (cs, rbest)
    return qb, b0, rows, best


if __name__ == "__main__":
    shapes = [SHAPE,
              dict(SHAPE, name="final 12k levers (236 + z=32, M=8)", target=268, z=32),
              dict(SHAPE, name="final 12k, contract M=3 (268 bits)", M=3)]
    for sh in shapes:
        qb, b0 = baseline(sh)
        print(f"== {sh['name']}\n   baseline 42 B: q={qb}  WHIR opening bytes={b0:,.0f}")
        uniform = [[c] * 4 for c in range(6, 17)]
        mixed = [[a, a, b, b] for a in range(8, 15) for b in range(a, 18)]
        for variant in ("L", "U"):
            _, _, rows, best = search(sh, variant, uniform + mixed)
            for cs, rb in rows[:len(uniform)]:
                if rb:
                    sv, K, ex, n, D, qs = rb
                    print(f"   [{variant}] c={cs}  K*={K:2d} extra={ex}  n_min={n} D={D} B  q={qs}  net saving={sv/1000:6.1f} KB")
                else:
                    print(f"   [{variant}] c={cs}  infeasible")
            cs, (sv, K, ex, n, D, qs) = best
            print(f"   [{variant}] BEST c={cs}  K*={K} extra={ex}  n_min={n} D={D} B  q={qs}  net saving={sv/1000:.1f} KB")
        sys.stdout.flush()
