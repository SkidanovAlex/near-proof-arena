"""Stronger lower bound: mixed subtree attacks (beta fraction of level-l subtrees fully agreeing,
gamma-fraction of leaves inside the others), any query distribution with m distinct leaves in u
level-l subtrees (equal groups optimal for the defender by convexity)."""
import math, sys
sys.path.insert(0, str(__import__('pathlib').Path(__file__).resolve().parents[2]/'native'))
sys.path.insert(0, str(__import__('pathlib').Path(__file__).resolve().parent))
import final_layer_model as F, levers_model as L
from lb import log2C

def log2sum(xs):
    mx = max(xs)
    if mx == -math.inf: return mx
    return mx + math.log2(sum(2**(x-mx) for x in xs))

def miss_log2(n, s, u, g, alpha, B):
    """log2 Pr[all queries agree] for attack with B full subtrees out of n (subtree size s leaves)."""
    gamma = (alpha*n - B)/(n - B) if n > B else 0.0
    if gamma <= 0: inner = -math.inf
    else:
        G = math.floor(gamma*s)
        inner = log2C(G, g) - log2C(s, g) if G >= g else -math.inf
    terms = []
    denom = log2C(n, B)
    for j in range(0, min(u, B)+1):
        t = log2C(u, j) + log2C(n-u, B-j) - denom
        if t == -math.inf: continue
        terms.append(t if u-j == 0 else (t + (u-j)*inner if inner > -math.inf else -math.inf))
    return log2sum(terms) if terms else -math.inf

def Bgrid(n, alpha):
    Amax = math.floor(alpha*n)
    if Amax <= 60: return list(range(0, Amax+1))
    return sorted(set([0,1,2,3] + [round(Amax*x/60) for x in range(61)]))

def u_min(level, depth, m, alpha, target):
    n, s = 2**level, 2**(depth-level)
    if n >= m*64:
        return m    # fine levels: groups are singletons w.h.p. for any sound D (u must be ~m)
    grid = Bgrid(n, alpha)
    lo = 1
    for u in range(max(1, math.ceil(m/s)), min(n, m)+1):
        g = math.ceil(m/u)
        worst = max(miss_log2(n, s, u, g, alpha, B) for B in grid)
        if worst <= -target:
            return u
    return min(n, m)

def lb(q, depth, bits, target=268, leafbytes=384, digest=48):
    alpha = 2.0**-bits
    best = None
    for m in range(q, q+1):   # m=q distinct leaves (more leaves only add value bytes)
        tot = 2 - m + sum(u_min(l, depth, m, alpha, target) for l in range(1, depth))
        best = tot
    return best

if __name__ == '__main__':
    for label, b, k1, k, log_h, log_final, m in [('c12k today(m8)', 8,1,3,19,9,8), ('child gas-failure5', 7,3,3,17,2,3)]:
        r = L.layer(1<<20, 300, 268, m, 48, b, k1, k, log_h, log_final)
        rates=[b]; rate=b+k1-1
        for i in range(1,len(r['q'])): rates.append(rate); rate+=k-1
        depths=[log_h+b-k1]+[log_h+b-i-k for i in range(1,len(r['q']))]
        tu=tl=0
        print(label)
        for q,d,rt in zip(r['q'],depths,rates):
            bq=L.bits(rt,m); u=F.multiproof_digests(q,d); l2=lb(q,d,bq)
            tu+=u; tl+=l2
            print(f"  q={q} d={d} bits={bq:.2f} uniform={u:.1f} LB_mixed={l2:.1f} gap={u-l2:.1f} ({(u-l2)/u*100:.1f}%)")
        print(f"  TOTAL uniform={tu:.0f} LB_mixed={tl:.0f} gap={tu-tl:.0f} digests = {48*(tu-tl):.0f} B")
