import math, sys
sys.path.insert(0, str(__import__('pathlib').Path(__file__).resolve().parents[2]/'native'))
import levers_model as L
ARITY_PATH_FACTOR = 1.0
orig_layer = L.layer
def sha_blocks(cells, target, m, b, k1, k, log_h, log_final):
    r = orig_layer(cells, 300, target, m, 48, b, k1, k, log_h, log_final)
    leaf = lambda nbytes: -(-(nbytes + 58) // 128)
    total = 733
    for i, q in enumerate(r['q']):
        kk = k1 if i == 0 else k
        row = r['width'] * L.BASE if i == 0 else L.EXT
        depth = log_h + b - kk - (i if i else 0)
        total += q * ((1 << kk) * leaf(row) + (1 << kk) - 1 + math.ceil(depth*ARITY_PATH_FACTOR))
    total += -(-((1 << log_final) * L.EXT) // 128)
    return total, sum(r['q'])
L.sha_blocks = sha_blocks
import json
rows=[]
for c in (12000, 24000, 32000):
    for pen_arity in (1.0, 0.5):
        ARITY_PATH_FACTOR = pen_arity
        for (pen_t, fin_t, m, lab) in ((268,268,8,'today(m8)'), (236,226,8,'levers z=32')):
            line=[]
            cells=None
            for dig in (48, 42, 36, 32, 28, 26):
                cells_, blocks, shape, f = L.fixed_point(c, 2000, 1<<20, pen_t, fin_t, m, dig)
                line.append((dig, f['bytes'], f['auth']))
                cells=cells_
            print(f"c_sha={c:>5} pen 4-ary={'yes' if pen_arity<1 else 'no '} {lab:12} cells=2^{math.log2(cells):.2f} " + "  ".join(f"{d}B:{b:,}" for d,b,a in line))
            rows.append(dict(c=c, pen4=pen_arity<1, lab=lab, cells=cells, line=line))
json.dump(rows, open(str(__import__('pathlib').Path(__file__).resolve().parent/'digest.json'),'w'))
