#!/usr/bin/env python3
"""Numerics for research/near-compression/weak-binding/ANALYSIS.md (stdlib only).

Evaluates the bound of Theorem 2 (graded-potential QROM bound for BCS with
capped, position-indexed Merkle trees) and finds the minimal Merkle digest
width n.  All quantities are carried as log2 values.

  P <= ( sum_{chains 0=i0<...<im=K+1} C(t,m) prod_k G(i_k - i_{k-1}) + sqrt(ell/2^n) )^2

  G(1) = max( sqrt(10 t/2^n),  Gfs(1) )
  G(2) = max( 3 t/2^n,         Gfs(2) )
  G(d) = Gfs(d)                for d >= 3
  Gfs(d) = sqrt(10 (2^-z * epshat(K+1-d) + 2t/2^384))

epshat(m) = max_{m'<=m} eps_rob(m');  eps_rob(m) = max over rounds of the
block-robust query error of Lemma 3, plus eps_other (non-query verifier moves,
hypothesis H-rob).

Usage:  python3 wb_bound.py          # n_min table, writes wb_bound.json
        python3 wb_bound.py eps      # log2 eps_q(m) per shape and cap size
"""
import json, math, sys

NEG = float("-inf")

def ladd(a, b):
    if a == NEG: return b
    if b == NEG: return a
    if a < b: a, b = b, a
    return a + math.log2(1.0 + 2.0 ** (b - a))

def lsum(xs):
    s = NEG
    for x in xs: s = ladd(s, x)
    return s

def lcomb(N, k):
    """log2 binomial(N, k), N int, small k."""
    if k < 0 or k > N: return NEG
    return sum(math.log2(N - i) - math.log2(i + 1) for i in range(k))

SHIFT = False   # set by --shift: H-rob variant with agreement density alpha + m/B (Section 6.3)

def eps_query(q, bbits, B, m):
    """Lemma 3 (log2): Pr[some <= m blocks cover all queries outside A], dens(A) <= 2^-bbits.
    With SHIFT, dens(A) <= 2^-bbits + m/B (radius shift from robust folding, Section 6.3)."""
    la = -bbits
    if SHIFT and m > 0:
        la = math.log2(min(1.0, 2.0 ** la + m / B))
    l1a = math.log2(1.0 - 2.0 ** la)
    if m == 0:
        return q * la
    lcb = lcomb(B, m) if m <= B else NEG
    terms = []
    for k in range(q + 1):
        cover = min(k * l1a, lcb + k * math.log2(m / B))
        terms.append(lcomb(q, k) + (q - k) * la + cover)
    return min(lsum(terms), 0.0)

def epshat_table(rounds, B, top, eps_other):
    raw = [min(ladd(max(eps_query(q, b, B, m) for (q, b) in rounds), eps_other), 0.0)
           for m in range(top + 1)]
    hat, cur = [], NEG
    for e in raw:
        cur = max(cur, e); hat.append(cur)
    return hat

def bound(n, rounds, B, K, z=0, t_log=64, ell_log=17, eps_other=-300.0, hat=None):
    top = K + 1
    if hat is None:
        hat = epshat_table(rounds, B, top, eps_other)
    lt = t_log
    t_int = 2 ** t_log
    G = {}
    for d in range(1, top + 1):
        g = 0.5 * (math.log2(10) + ladd(-z + hat[top - d], 1 + lt - 384))
        if d == 1:
            g = max(g, 0.5 * (math.log2(10) + lt - n))
        elif d == 2:
            g = max(g, math.log2(3) + lt - n)
        G[d] = g
    W = [[NEG] * (top + 1) for _ in range(top + 1)]
    W[0][0] = 0.0
    for m in range(1, top + 1):
        for j in range(1, top + 1):
            W[m][j] = lsum(W[m - 1][i] + G[j - i] for i in range(j) if W[m - 1][i] != NEG)
    amp = lsum(lcomb(t_int, m) + W[m][top] for m in range(1, top + 1))
    amp = ladd(amp, 0.5 * (ell_log - n))
    return 2 * amp

def best(n, rounds, B, z=0, Kmax=40, **kw):
    hat = epshat_table(rounds, B, Kmax + 1, kw.get("eps_other", -300.0))
    res = []
    for K in range(0, Kmax + 1):
        res.append((bound(n, rounds, B, K, z=z, hat=hat[:K + 2], **kw), K))
    return min(res)

def nmin(rounds, B, z=0, target=-128.0, lo=190, hi=340, **kw):
    for n in range(lo, hi + 1):
        P, K = best(n, rounds, B, z=z, **kw)
        if P <= target:
            return n, K, P
    return None

def R(qs, target):
    return [(q, target / q) for q in qs]

SHAPES = {
    "generic 4x40 (268 b/round)": (R([40] * 4, 268), 0),
    "generic 4x50 (268 b/round)": (R([50] * 4, 268), 0),
    "generic 4x60 (268 b/round)": (R([60] * 4, 268), 0),
    "final 12k today 69/69/55/46 (268)": (R([69, 69, 55, 46], 268), 0),
    "final 12k levers 61/61/49/41 (236+z32)": (R([61, 61, 49, 41], 236), 32),
}

if __name__ == "__main__":
    if "--shift" in sys.argv:
        SHIFT = True
        sys.argv.remove("--shift")
    caps = (64, 256, 1024, 4096, 16384)
    if len(sys.argv) > 1 and sys.argv[1] == "eps":
        for name, (rounds, z) in SHAPES.items():
            q, b = rounds[-1]
            for B in caps:
                row = [eps_query(q, b, B, m) for m in range(0, 7)]
                cost = [round(row[m] - row[0], 1) for m in range(7)]
                print(f"{name:40s} q={q} B={B:5d} log2 eps_q(m) m=0..6: {[round(x,1) for x in row]}  loss vs m=0: {cost}")
        sys.exit()
    out = {}
    for name, (rounds, z) in SHAPES.items():
        for B in caps:
            n, K, P = nmin(rounds, B, z=z)
            print(f"{name:40s} B={B:5d}  n_min={n} ({math.ceil(n/8)} B)  K*={K}  log2P={P:.2f}", flush=True)
            out[f"{name}|B={B}"] = {"n_min": n, "bytes": math.ceil(n / 8), "K": K, "log2P": round(P, 2)}
        for n in range(290, 345):
            P = bound(n, rounds, 64, 0, z=z)
            if P <= -128:
                print(f"{name:40s} zero tolerance K=0: n_min={n} ({math.ceil(n/8)} B) log2P={P:.2f}")
                out[f"{name}|K=0"] = {"n_min": n, "bytes": math.ceil(n / 8), "log2P": round(P, 2)}
                break
    with open(__file__.replace(".py", "_shift.json" if SHIFT else ".json"), "w") as f:
        json.dump(out, f, indent=1)
