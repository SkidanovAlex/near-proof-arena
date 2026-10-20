"""Lower bound on expected Merkle multiproof digests for ANY query distribution over a
fixed public leaf layout, against the subtree-aligned agreement attack; vs uniform queries."""
import math, sys
sys.path.insert(0, str(__import__('pathlib').Path(__file__).resolve().parents[2]/'native'))
import final_layer_model as F
from math import lgamma, log

def log2C(n, k):
    if k < 0 or k > n: return -math.inf
    return (lgamma(n+1)-lgamma(k+1)-lgamma(n-k+1))/log(2)

def u_needed(level, alpha, target_log2):
    """min distinct level-l subtrees u such that C(A,u)/C(n,u) <= 2^target (A=floor(alpha*n))."""
    n = 2**level
    A = math.floor(alpha*n)
    if A < 1:
        return 1   # attack not realisable at this granularity; only trivially >=1
    for u in range(1, n+1):
        if u > A or log2C(A,u)-log2C(n,u) <= target_log2:
            return u
    return n

def lb_digests(q, depth, bits_per_query, target=268, slack=8):
    alpha = 2.0**-bits_per_query
    best = 0
    for s in range(1, slack+1):
        tot = 2
        for l in range(1, depth):
            tot += (1-2.0**-s)*u_needed(l, alpha, -target+s)
        ud = q  # distinct leaves (<= q); also needed >= u_needed(depth)
        best = max(best, tot - ud)
    return best

def uniform(q, depth):
    return F.multiproof_digests(q, depth)

if __name__ == '__main__':
    import levers_model as L
    # final-layer shape at c_sha=12k, today_m8: b=8,k1=1,k=3,log_h=19 q=[69,69,55,46]
    for label, b, k1, k, log_h, log_final, m, target in [
        ('c12k today(m8)', 8,1,3,19,9,8,268), ('c24k today(m8)', 6,1,3,21,8,8,268),
        ('child gas-failure5', 7,3,3,17,2,3,268)]:
        r = L.layer(1<<20, 300, target, m, 48, b, k1, k, log_h, log_final)
        rates=[b]; rate=b+k1-1
        for i in range(1,len(r['q'])): rates.append(rate); rate+=k-1
        depths=[log_h+b-k1]+[log_h+b-i-k for i in range(1,len(r['q']))]
        tu=tl=tn=0
        print(label)
        for q,d,rt in zip(r['q'],depths,rates):
            bq=L.bits(rt,m)
            u=uniform(q,d); lb=lb_digests(q,d,bq,target)
            naive=q*d; nl = q*(d-math.log2(q))
            tu+=u; tl+=lb; tn+=naive
            print(f"  q={q:3d} depth={d:2d} bits/q={bq:5.2f}  naive q*d={naive:5d}  uniform-multiproof={u:7.1f}  q*log2(N/q)={nl:7.1f}  LB(any distribution)={lb:7.1f}  gap={u-lb:6.1f} ({(u-lb)/u*100:4.1f}%)")
        print(f"  TOTAL naive={tn} uniform={tu:.0f} LB={tl:.0f} gap={tu-tl:.0f} digests = {48*(tu-tl):.0f} B")
