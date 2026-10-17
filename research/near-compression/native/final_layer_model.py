"""Wire-size model of a recursive final layer on the SHA-384/Ext12 SWIRL stack.

A design model, not a measurement and not a security certificate. It answers:
given the in-circuit cost of verifying a child proof, which final-layer shapes
can fit under 300,000 bytes with the backend's own query schedule
(WhirConfig::new, 268 query bits, no grinding)?

Calibration (asserted below): the model reproduces the measured gas-failure5
child exactly -- query schedule, Merkle digest count, opened values, WHIR bytes
and verifier SHA-384 call counts.  Everything about the *parent* circuit
(cells per SHA-384 compression, columns, arithmetic cells) is an explicit
input, to be replaced by measurements once a parent AIR exists.
"""
import argparse
import json
import math

DIGEST = 48          # SHA-384
EXT = 48             # Ext12 element, 12 x 4 bytes
BASE = 4
TARGET_BITS = 268
MAX_LOG_DOMAIN = 27  # BabyBear two-adicity; driver asserts l_skip+n_stack+b <= 27
L_SKIP = 2


def per_query_bits(regime, log_inv_rate, m=3):
    rho = 2.0 ** -log_inv_rate
    agree = (1 + rho) / 2 if regime == 'unique' else math.sqrt(rho) * (1 + 1 / (2 * m))
    return -math.log2(agree)


def schedule(b, k, log_h, regime, log_final=None):
    """Mirror WhirConfig::new: rounds, queries, Merkle depths."""
    if log_final is None:
        log_final = log_h % k
    rounds = -(-(log_h - log_final) // k)
    out, rate = [], b
    for i in range(rounds):
        q = math.ceil(TARGET_BITS / per_query_bits(regime, rate))
        depth = log_h + b - i - k          # domain halves per round; leaves group 2^k points
        out.append(dict(queries=q, depth=depth))
        rate += k - 1
    return out, log_h - rounds * k


def multiproof_digests(q, depth):
    """Expected sibling digests of an optimal multiproof for q uniform leaf queries."""
    touched = lambda lvl: (1 << lvl) * (1 - (1 - 2.0 ** -lvl) ** q)   # distinct nodes at level lvl
    return sum(2 * touched(l - 1) - touched(l) for l in range(1, depth + 1))


def whir_bytes(b, k, log_h, width, regime, dedup=0.0, log_final=None):
    sched, log_final = schedule(b, k, log_h, regime, log_final)
    if dedup == 'multiproof':
        digests = round(sum(multiproof_digests(r['queries'], r['depth']) for r in sched))
        dedup = 0.0
    else:
        digests = sum(r['queries'] * r['depth'] for r in sched)
    initial = sched[0]['queries'] * (1 << k) * width * BASE
    codeword = sum(r['queries'] for r in sched[1:]) * (1 << k) * EXT
    n = len(sched)
    small = 2 * k * n * EXT + (n - 1) * 2 * DIGEST + (1 << log_final) * EXT + 132
    return dict(schedule=sched, digests=digests, auth=round(digests * DIGEST * (1 - dedup)),
                initial=initial, codeword=codeword, small=small,
                total=round(digests * DIGEST * (1 - dedup)) + initial + codeword + small)


def verifier_sha_blocks(b, k, log_h, width, regime):
    """SHA-384 compressions in one verify, as counted by the instrumented driver."""
    sched, _ = schedule(b, k, log_h, regime)
    leaf_in = lambda nbytes: -(-(nbytes + 17 + 41) // 128)   # framing + length padding
    total = 0
    for i, r in enumerate(sched):
        row = width * BASE if i == 0 else EXT
        total += r['queries'] * ((1 << k) * leaf_in(row) + (1 << k) - 1 + r['depth'])
    return total + 733                                          # transcript (measured)


def proof_bytes(b, k, log_h, width, cols, regime, dedup=0.0, log_final=None):
    w = whir_bytes(b, k, log_h, width, regime, dedup, log_final)
    relations = 2 * cols * EXT + 3112                           # calibrated constant
    gkr, stacking, other = 8456, 1840, 861
    return w, w['total'] + relations + gkr + stacking + other


def calibrate():
    w, total = proof_bytes(7, 3, L_SKIP + 15, 1, 295, 'list')
    assert [r['queries'] for r in w['schedule']] == [82, 63, 51, 43, 37]
    assert w['digests'] == 5354 and w['initial'] == 2624 and w['codeword'] == 74496
    assert w['digests'] * DIGEST == 256992
    assert abs(w['total'] - 336260) <= 16, w['total']
    assert abs(total - 378849) <= 16, total
    # leaf 2208 + node 7286 + transcript 733 = 10227 measured compression blocks
    assert verifier_sha_blocks(7, 3, L_SKIP + 15, 1, 'list') == 10227
    mp = whir_bytes(7, 3, L_SKIP + 15, 1, 'list', 'multiproof')['digests']
    assert mp <= 4017, mp      # measured unique digests (dictionary) bound the multiproof above


def best_final(cells, cols, regime, dedup):
    """Smallest final proof over (b, k, n_stack) for a circuit of `cells` cells."""
    best = None
    for b in range(1, 12):
        for k in range(1, 6):
            for log_h in range(10, MAX_LOG_DOMAIN - b + 1):
                width = max(1, -(-cells // (1 << log_h)))
                if width > 1 << 16:
                    continue
                for log_final in range(log_h % k, min(log_h, 15), k):
                  w, total = proof_bytes(b, k, log_h, width, cols, regime, dedup, log_final)
                  cand = (total, dict(b=b, k=k, log_h=log_h, width=width, bytes=total, log_final=log_final,
                                    queries=[r['queries'] for r in w['schedule']],
                                    whir=w['total'], initial=w['initial'], auth=w['auth']))
                  if best is None or cand[0] < best[0]:
                      best = cand
    return best[1]


def cheapest_child(cells, regime):
    """Penultimate-layer shape minimising the final layer's SHA-384 work."""
    best = None
    for b in range(1, 12):
        for k in range(1, 6):
            for log_h in range(10, MAX_LOG_DOMAIN - b + 1):
                width = max(1, -(-cells // (1 << log_h)))
                blocks = verifier_sha_blocks(b, k, log_h, width, regime)
                if best is None or blocks < best[0]:
                    best = (blocks, dict(b=b, k=k, log_h=log_h, width=width, sha_blocks=blocks))
    return best[1]


def fixed_point(c_sha, c_query, cols, regime, dedup, c_fixed=1 << 22, iters=30):
    """Each layer verifies the previous one; iterate until the cell count settles."""
    cells = 1 << 24
    for _ in range(iters):
        child = cheapest_child(cells, regime)
        q = sum(r['queries'] for r in schedule(child['b'], child['k'], child['log_h'], regime)[0])
        new = child['sha_blocks'] * c_sha + q * c_query + c_fixed
        if new == cells:
            break
        cells = new
    return cells, child, best_final(cells, cols, regime, dedup)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--out')
    args = ap.parse_args()
    calibrate()
    rows = []
    for regime in ('list', 'unique'):
        for c_sha in (8_000, 12_000, 20_000, 30_000):
            for cols in (300, 600, 1500):
                for dedup in (0.0, 'multiproof'):
                    cells, child, final = fixed_point(c_sha, 20_000, cols, regime, dedup)
                    rows.append(dict(regime=regime, c_sha=c_sha, cols=cols, dedup=dedup,
                                     cells_log2=round(math.log2(cells), 2), child=child, final=final))
    for r in rows:
        f = r['final']
        print(f"{r['regime']:6} c_sha={r['c_sha']:>6} cols={r['cols']:>5} dedup={str(r['dedup']):>10} "
              f"cells=2^{r['cells_log2']:<5} child_sha={r['child']['sha_blocks']:>6} "
              f"final={f['bytes']:>8} (b={f['b']} k={f['k']} h=2^{f['log_h']} fin=2^{f['log_final']} W={f['width']} "
              f"q={f['queries']} init={f['initial']} auth={f['auth']})")
    if args.out:
        with open(args.out, 'w') as fh:
            json.dump(dict(status='DESIGN_MODEL_ONLY', calibrated_against='gas-failure5 child',
                           target_bits=TARGET_BITS, rows=rows), fh, indent=1)


if __name__ == '__main__':
    main()
