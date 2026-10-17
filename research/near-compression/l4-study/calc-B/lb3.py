"""Lower bound v3: two-class subtree attacks at each level l: B 'heavy' subtrees with internal
agreement a_h, the rest a_l, mean alpha.  Defender: any distribution with m=q distinct leaves in u
level-l subtrees (equal groups).  Report min u per level s.t. every attack has miss <= 2^-target."""
import math, sys
sys.path.insert(0, str(__import__('pathlib').Path(__file__).resolve().parents[2]/'native'))
sys.path.insert(0, str(__import__('pathlib').Path(__file__).resolve().parent))
import final_layer_model as F, levers_model as L
from lb import log2C
from lb2 import log2sum

def inner(a, s, g):
    G = math.floor(a*s + 1e-9)
    return log2C(G, g) - log2C(s, g) if G >= g else -math.inf

def miss(n, s, u, g, alpha, B, ah):
    al = (alpha*n - B*ah)/(n-B) if n > B else 0.0
    if al < -1e-12: return -math.inf
    ih, il = inner(ah, s, g), inner(max(al,0), s, g)
    terms, den = [], log2C(n, B)
    for j in range(0, min(u, B)+1):
        t = log2C(u, j) + log2C(n-u, B-j) - den
        if t == -math.inf: continue
        x = t
        if j: x = x + j*ih if ih > -math.inf else -math.inf
        if u-j: x = x + (u-j)*il if il > -math.inf else -math.inf
        terms.append(x)
    return log2sum(terms) if terms else -math.inf

def u_min(level, depth, m, alpha, target):
    n, s = 2**level, 2**(depth-level)
    if n >= m*m*16:
        return m
    Bs = sorted(set([1,2,3,4,6,8,12,16,24,32,48,64,96,128,192,256,384,512,768,1024,2048,4096] ))
    Bs = [B for B in Bs if B < n]
    for u in range(max(1, math.ceil(m/s)), min(n, m)+1):
        g = math.ceil(m/u)
        worst = miss(n, s, u, g, alpha, 0, 0.0)
        for B in Bs:
            amin = alpha*n/B  # all agreement in heavy subtrees if <=1
            for ah in [min(1.0, alpha*n/B*f) for f in (1.0,)] + [alpha*(1+x) for x in (0.5,1,2,4,8,16,32)] + [1.0]:
                if ah > 1 or B*ah > alpha*n + 1e-9: continue
                worst = max(worst, miss(n, s, u, g, alpha, B, ah))
            if worst > -target: break
        if worst <= -target:
            return u
    return min(n, m)

def lb(q, depth, bits, target=268):
    a = 2.0**-bits
    return 2 - q + sum(u_min(l, depth, q, a, target) for l in range(1, depth))

if __name__ == '__main__':
    for label, b, k1, k, log_h, log_final, m in [('c12k today(m8)', 8,1,3,19,9,8), ('c24k today(m8)', 6,1,3,21,8,8), ('child gas-failure5', 7,3,3,17,2,3)]:
        r = L.layer(1<<20, 300, 268, m, 48, b, k1, k, log_h, log_final)
        rates=[b]; rate=b+k1-1
        for i in range(1,len(r['q'])): rates.append(rate); rate+=k-1
        depths=[log_h+b-k1]+[log_h+b-i-k for i in range(1,len(r['q']))]
        tu=tl=0
        print(label)
        for q,d,rt in zip(r['q'],depths,rates):
            bq=L.bits(rt,m); u=F.multiproof_digests(q,d); l3=lb(q,d,bq)
            tu+=u; tl+=l3
            print(f"  q={q} d={d} bits={bq:.2f} uniform={u:.1f} LB={l3:.1f} gap={u-l3:.1f} ({(u-l3)/u*100:.1f}%)")
        print(f"  TOTAL uniform={tu:.0f} LB={tl:.0f} gap={tu-tl:.0f} digests = {48*(tu-tl):.0f} B")
