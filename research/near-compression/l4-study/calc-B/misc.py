import math, random, sys
sys.path.insert(0, str(__import__('pathlib').Path(__file__).resolve().parents[2]/'native'))
import final_layer_model as F, levers_model as L
rounds = [(69,26,3.91),(69,23,3.91),(55,22,4.91),(46,21,5.91)]   # c12k today(m8) final layer
def touched(n, q): return n*(1-(1-1/n)**q)
print("== tree cap (on top of optimal multiproof), digests per round ==")
for q,d,_ in rounds:
    mp = F.multiproof_digests(q,d)
    best = (0, 0)
    for c in range(0, 12):
        sib_top = sum(2*touched(2**(l-1),q) - touched(2**l,q) for l in range(1,c+1))
        delta = (2**c - 1) - sib_top     # extra cap digests (minus the root) minus siblings no longer needed
        if delta < best[1]: best = (c, delta)
    print(f"  q={q} d={d} multiproof={mp:.1f} best cap level={best[0]} change={best[1]:+.2f} digests")
print("== arity (multiproof digests, same leaf count 2^d) ==")
for q,d,_ in rounds:
    row=[]
    for a in (2,4,8,16):
        h = d/math.log2(a)
        if abs(h-round(h))>1e-9: row.append(f"a={a}: n/a"); continue
        h=int(round(h)); tot=0
        for l in range(1,h+1):
            tot += a*touched(a**(l-1),q) - touched(a**l,q)
        row.append(f"a={a}: {tot:.0f}")
    print(f"  q={q} d={d}  " + "  ".join(row))
print("== hypothetical: all rounds in ONE tree (not realisable: commit order) ==")
tot_sep = sum(F.multiproof_digests(q,d) for q,d,_ in rounds)
# one tree of 4 * 2^26 leaves; queries confined to their sub-tree => saving is only the top 2 levels
print(f"  separate={tot_sep:.0f}; merged saving <= ~{len(rounds)*1} digests (the roots), i.e. <= {len(rounds)*48} B")
print("== grinding for small multiproof (conditional query distribution) ==")
random.seed(1)
def mp_size(pos, d):
    s = set(pos); tot = 0
    for l in range(d, 0, -1):
        par = {}
        for x in s: par.setdefault(x>>1, []).append(x)
        tot += sum(1 for v in par.values() if len(v)==1)
        s = set(par)
    return tot
for q,d,bits in rounds[:1]+rounds[3:]:
    N = 1<<d
    xs = sorted(mp_size([random.randrange(N) for _ in range(q)], d) for _ in range(20000))
    mean = sum(xs)/len(xs); sd = (sum((x-mean)**2 for x in xs)/len(xs))**.5
    print(f"  q={q} d={d}: mean={mean:.1f} (model {F.multiproof_digests(q,d):.1f}) sd={sd:.2f}")
    marg = F.multiproof_digests(q+1,d)-F.multiproof_digests(q,d) + 8   # +1 query: path digests + 8 Ext12 leaf values (=8 digest-equivalents)
    for z in (1,2,4,8):
        thr = xs[int(len(xs)*2**-z)]
        saving = mean - sum(x for x in xs if x<=thr)/max(1,sum(1 for x in xs if x<=thr))
        cost = math.ceil(z/bits)*marg
        print(f"    z={z}: conditional mean saves {saving:5.1f} digests; extra queries {math.ceil(z/bits)} cost {cost:5.1f} -> net {cost-saving:+.1f}")
