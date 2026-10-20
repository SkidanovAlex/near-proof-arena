"""Hash-only floor of the recursive final layer under each admissible lever.

Extends final_layer_model.py (calibrated against the measured child) with:
  * grinding z bits per query phase.  Under the U-6 bounded-query contract the
    adversary must hit a marked set of density 2^-z * eps with t quantum
    queries, success O(t^2 2^-z eps), so z bits of proof-of-work lower the
    per-round query target by z (honest cost 2^z SHA-384 per round);
  * the per-round target itself (258 if the CMS19 constant is pinned near 1,
    268 today);
  * list multiplicity m (agreement (1+1/2m) sqrt(rho); MCA proven for m >= 3,
    CCC 2026 Thm 5, error grows as m^7);
  * truncated Merkle digests (binding needs ~t^3/2^n, so n >= 336 keeps 2^-144);
  * a separate first-round folding factor k1 (WHIR allows per-round folding;
    the pinned backend does not);
  * the final circuit's cell count.
Design model only: no lever here is adopted, implemented or certified.
"""
import itertools
import math
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import final_layer_model as base   # noqa: E402

EXT, BASE, MAX_LOG_DOMAIN = base.EXT, base.BASE, base.MAX_LOG_DOMAIN


def bits(log_inv_rate, m):
    return -math.log2(math.sqrt(2.0 ** -log_inv_rate) * (1 + 1 / (2 * m)))


def layer(cells, cols, target, m, digest, b, k1, k, log_h, log_final):
    width = max(1, -(-cells // (1 << log_h)))
    rounds = []
    q = math.ceil(target / bits(b, m))
    rounds.append(dict(q=q, depth=log_h + b - k1))
    vars_left, rate, i = log_h - k1, b + k1 - 1, 1
    while vars_left > log_final:
        q = math.ceil(target / bits(rate, m))
        rounds.append(dict(q=q, depth=log_h + b - i - k))
        vars_left -= k
        rate += k - 1
        i += 1
    auth = digest * round(sum(base.multiproof_digests(r['q'], r['depth']) for r in rounds))
    initial = rounds[0]['q'] * (1 << k1) * width * BASE
    codeword = sum(r['q'] for r in rounds[1:]) * (1 << k) * EXT
    n = len(rounds)
    small = 2 * (k1 + k * (n - 1)) * EXT + (n - 1) * 2 * digest + (1 << max(log_final, 0)) * EXT + 132
    relations = 2 * cols * EXT + 3112
    total = auth + initial + codeword + small + relations + 8456 + 1840 + 861
    return dict(bytes=total, auth=auth, initial=initial, codeword=codeword,
                final_poly=(1 << max(log_final, 0)) * EXT, relations=relations,
                q=[r['q'] for r in rounds], b=b, k1=k1, k=k, log_h=log_h, log_final=log_final, width=width)


def best(cells, cols, target, m, digest, allow_k1):
    out = None
    for b in range(2, 14):
        for log_h in range(8, MAX_LOG_DOMAIN - b + 1):
            if cells / (1 << log_h) > 1 << 14:
                continue
            for k in range(1, 6):
                for k1 in (range(1, 6) if allow_k1 else [k]):
                    for log_final in range(0, min(log_h - k1, 14) + 1):
                        if (log_h - k1 - log_final) % k:
                            continue
                        r = layer(cells, cols, target, m, digest, b, k1, k, log_h, log_final)
                        if out is None or r['bytes'] < out['bytes']:
                            out = r
    return out


SCENARIOS = [
    # name, target bits, m, digest bytes, per-round k1
    ('today (268, m=3, 48 B)', 268, 3, 48, False),
    ('+ k1 free', 268, 3, 48, True),
    ('+ m=8', 268, 8, 48, True),
    ('+ constant pinned (258)', 258, 8, 48, True),
    ('+ grinding z=24 (234)', 234, 8, 48, True),
    ('+ grinding z=32 (226)', 226, 8, 48, True),
    ('+ 42 B digests (z=32)', 226, 8, 42, True),
]


def main():
    base.calibrate()
    # The general layer() must reproduce the calibrated child too.
    child = layer(1 << 17, 295, 268, 3, 48, 7, 3, 3, 17, 2)
    assert child['q'] == [82, 63, 51, 43, 37] and child['initial'] == 2624 and child['codeword'] == 74496
    print(f"{'scenario':28} " + ' '.join(f'{f"cells 2^{c}":>12}' for c in (22, 24, 26, 27, 28)))
    rows = {}
    for name, target, m, digest, k1 in SCENARIOS:
        line = []
        for c in (22, 24, 26, 27, 28):
            r = best(1 << c, 300, target, m, digest, k1)
            rows[(name, c)] = r
            line.append(f"{r['bytes']:>12,}")
        print(f'{name:28} ' + ' '.join(line))
    print()
    for c in (24, 27):
        r = rows[(SCENARIOS[-1][0], c)]
        print(f'best all-levers @2^{c}:', {k: v for k, v in r.items()})


if __name__ == '__main__':
    main()


def sha_blocks(cells, target, m, b, k1, k, log_h, log_final):
    """In-circuit SHA-384 compressions to verify a layer of this shape (driver-calibrated)."""
    r = layer(cells, 300, target, m, 48, b, k1, k, log_h, log_final)
    leaf = lambda nbytes: -(-(nbytes + 58) // 128)
    total = 733
    for i, q in enumerate(r['q']):
        kk = k1 if i == 0 else k
        row = r['width'] * BASE if i == 0 else EXT
        depth = log_h + b - kk - (i if i else 0)
        total += q * ((1 << kk) * leaf(row) + (1 << kk) - 1 + depth)
    # The final polynomial is absorbed into the transcript and evaluated at every last-round query.
    total += -(-((1 << log_final) * EXT) // 128)
    return total, sum(r['q'])


FINAL_EVAL_CELLS = 40   # committed cells per Ext12 multiply-add in the verifier circuit (estimate)


def final_eval_cells(cells, target, m, b, k1, k, log_h, log_final):
    r = layer(cells, 300, target, m, 48, b, k1, k, log_h, log_final)
    return r['q'][-1] * (1 << log_final) * FINAL_EVAL_CELLS


def cheapest(cells, target, m):
    out = None
    for b in range(2, 14):
        for log_h in range(8, MAX_LOG_DOMAIN - b + 1):
            if cells / (1 << log_h) > 1 << 14:
                continue
            for k in range(1, 6):
                for k1 in range(1, 6):
                    for log_final in range(0, min(log_h - k1, 14) + 1):
                        if (log_h - k1 - log_final) % k:
                            continue
                        blocks, q = sha_blocks(cells, target, m, b, k1, k, log_h, log_final)
                        extra = final_eval_cells(cells, target, m, b, k1, k, log_h, log_final)
                        cost = blocks * C_SHA_HINT + extra
                        if out is None or cost < out[3]:
                            out = (blocks, q, dict(b=b, k1=k1, k=k, log_h=log_h, log_final=log_final, final_eval_cells=extra), cost)
    return out[:3]


C_SHA_HINT = 12000


def fixed_point(c_sha, c_query, c_fixed, pen_target, fin_target, m, digest):
    cells = 1 << 24
    for _ in range(20):
        global C_SHA_HINT
        C_SHA_HINT = c_sha
        blocks, q, shape = cheapest(cells, pen_target, m)
        new = blocks * c_sha + q * c_query + c_fixed + shape['final_eval_cells']
        if abs(new - cells) < cells // 1000:
            cells = new
            break
        cells = new
    return cells, blocks, shape, best(cells, 300, fin_target, m, digest, True)


def fixed_point_table():
    print(f"{'c_sha':>6} {'pen target':>10} {'fin target/digest':>18} {'pen SHA':>8} {'cells':>8} {'final bytes':>12}")
    for c_sha in (1000, 1500, 2500, 4000, 8000):
        for pen_t, fin_t, dig in ((268, 268, 48), (236, 258, 48), (236, 226, 42)):
            cells, blocks, shape, fin = fixed_point(c_sha, 2000, 1 << 20, pen_t, fin_t, 8, dig)
            print(f"{c_sha:>6} {pen_t:>10} {f'{fin_t}/{dig}B':>18} {blocks:>8} {'2^%.2f' % math.log2(cells):>8} {fin['bytes']:>12,}")
