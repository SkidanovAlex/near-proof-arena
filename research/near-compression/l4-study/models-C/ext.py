"""Extended lever model (scratch). Reproduces levers_model at default params."""
import math, functools
import levers_model as L

DEF = dict(extra=0.0, cell=4, shrink=1, colb=96, ext=48, maxdom=27, leaf='tree', dedup='none',
           digest=48, target=268, m=3, pack=1.0)

def bits(rate, m):
    return rate/2 - math.log2(1 + 1/(2*m))

@functools.lru_cache(maxsize=None)
def mp_digests(q, nleaves):
    """expected sibling digests (optimal multiproof) for q uniform queries into nleaves leaves (any N)."""
    D = math.ceil(math.log2(nleaves) - 1e-9)
    tot = 0.0
    def touched(l):  # level l from root (0 = root)
        n = math.ceil(nleaves / 2**(D-l))
        return n * (1 - (1 - 1/n)**q)
    for l in range(1, D+1):
        tot += 2*touched(l-1) - touched(l)
    return tot

@functools.lru_cache(maxsize=None)
def mp_internal(q, nleaves):
    """expected distinct internal nodes hashed when verifying q paths with dedup."""
    D = math.ceil(math.log2(nleaves) - 1e-9)
    tot = 0.0
    for l in range(0, D):
        n = math.ceil(nleaves / 2**(D-l))
        tot += n * (1 - (1 - 1/n)**q)
    return tot

def layer(cells, cols, b, k1, k, log_h, log_final, P):
    width = max(1, -(-cells // (1 << log_h)))
    s, ex = P['shrink'], P['extra']
    rounds = []
    rate = b + ex
    rounds.append(dict(q=math.ceil(P['target']/bits(rate, P['m'])), kk=k1,
                       leaves=2**(log_h + b + ex - k1)))
    vars_left, rate, i = log_h - k1, b + ex + k1 - s, 1
    while vars_left > log_final:
        rounds.append(dict(q=math.ceil(P['target']/bits(rate, P['m'])), kk=k,
                           leaves=2**(log_h + b + ex - s*i - k)))
        vars_left -= k; rate += k - s; i += 1
    for r in rounds:
        r['leaves'] = round(r['leaves'])
    dig = P['digest']
    auth = dig * round(sum(mp_digests(r['q'], r['leaves']) for r in rounds))
    initial = rounds[0]['q'] * (1 << k1) * width * P['cell'] * P['pack']
    codeword = sum(r['q'] for r in rounds[1:]) * (1 << k) * P['ext'] * P['pack']
    n = len(rounds)
    small = 2*(k1 + k*(n-1))*P['ext'] + (n-1)*2*dig + (1 << max(log_final, 0))*P['ext'] + 132
    relations = cols*P['colb'] + 3112
    total = auth + initial + codeword + small + relations + 8456 + 1840 + 861
    return dict(bytes=round(total), auth=auth, initial=round(initial), codeword=round(codeword),
                final_poly=(1 << log_final)*P['ext'], relations=relations, rounds=rounds,
                q=[r['q'] for r in rounds], b=b, k1=k1, k=k, log_h=log_h, log_final=log_final, width=width)

def best(cells, cols, P, kmax=5):
    out = None
    for b in range(2, 16):
        for log_h in range(8, int(P['maxdom'] - b) + 1):
            if cells / (1 << log_h) > 1 << 14: continue
            for k in range(1, kmax+1):
                for k1 in range(1, 6):
                    for lf in range(0, min(log_h - k1, 14) + 1):
                        if (log_h - k1 - lf) % k: continue
                        r = layer(cells, cols, b, k1, k, log_h, lf, P)
                        if out is None or r['bytes'] < out['bytes']: out = r
    return out

def sha_blocks(cells, b, k1, k, log_h, lf, P):
    r = layer(cells, 300, b, k1, k, log_h, lf, P)
    leaf = lambda nb: -(-(nb + 58) // 128)
    total = 733
    for i, rd in enumerate(r['rounds']):
        kk = rd['kk']; q = rd['q']
        row = r['width'] * 4 if i == 0 else 48
        if P['leaf'] == 'tree':
            leafc = (1 << kk) * leaf(row) + (1 << kk) - 1
        else:
            leafc = leaf((1 << kk) * row)
        depth = math.ceil(math.log2(rd['leaves']) - 1e-9)
        if P['dedup'] == 'multiproof':
            nodes = mp_internal(q, rd['leaves'])
            total += q * leafc + nodes
        else:
            total += q * (leafc + depth)
    total += -(-((1 << lf) * 48) // 128)
    return round(total), sum(r['q'])

def cheapest(cells, P, c_sha):
    out = None
    for b in range(2, 16):
        for log_h in range(8, int(P['maxdom'] - b) + 1):
            if cells / (1 << log_h) > 1 << 14: continue
            for k in range(1, 6):
                for k1 in range(1, 6):
                    for lf in range(0, min(log_h - k1, 14) + 1):
                        if (log_h - k1 - lf) % k: continue
                        blocks, q = sha_blocks(cells, b, k1, k, log_h, lf, P)
                        r = layer(cells, 300, b, k1, k, log_h, lf, P)
                        extra = r['q'][-1] * (1 << lf) * 40
                        cost = blocks * c_sha + extra
                        if out is None or cost < out[3]:
                            out = (blocks, q, dict(b=b, k1=k1, k=k, log_h=log_h, lf=lf, extra=extra), cost)
    return out[:3]

def fixed_point(c_sha, Ppen, Pfin, cols=300, c_query=2000, c_fixed=1 << 20, cell_scale=1.0):
    cells = 1 << 24
    for _ in range(20):
        blocks, q, shape = cheapest(cells, Ppen, c_sha)
        new = int((blocks * c_sha + q * c_query + c_fixed + shape['extra']) * cell_scale)
        if abs(new - cells) < cells // 1000:
            cells = new; break
        cells = new
    return cells, blocks, shape, best(cells, cols, Pfin)

def P(**kw):
    d = dict(DEF); d.update(kw); return d
