"""Independent Ext4 interpolation checks with heterogeneous shared-column packing."""
import json
import random
from pathlib import Path
import pq384_terminal_gkr as g
from swirl_weighted_stack_ext import kernels, power, P


def total(xs):
    out = g.ZERO
    for x in xs:
        out = g.add(out, x)
    return out


def dense_weights(log, point):
    # Explicit Lagrange products, independent of the kernel recurrence.
    domain = [pow(31, ((P - 1) // (1 << log)) * i, P) for i in range(1 << log)]
    uni = []
    for j, z in enumerate(domain):
        numerator, denominator = g.ONE, 1
        for k, y in enumerate(domain):
            if k != j:
                numerator = g.mul(numerator, g.sub(point[0], g.base(y)))
                denominator = denominator * (z - y) % P
        uni.append(g.mul(numerator, g.base(pow(denominator, -1, P))))
    result = []
    for bits in range(1 << (len(point) - 1)):
        factor = g.ONE
        for j, x in enumerate(point[1:]):
            factor = g.mul(factor, x if (bits >> j) & 1 else g.sub(g.ONE, x))
        result.extend(g.mul(factor, x) for x in uni)
    return result


def main():
    rng = random.Random(20261018)
    rand = lambda: tuple(rng.randrange(P) for _ in range(4))
    checks = wrong_rotation = short = 0
    for lskip in (1, 2, 3):
        stack_log = lskip + 2
        for trial in range(4):
            r = [rand() for _ in range(3)]
            u = [rand() for _ in range(3)]
            # Three different heights in ONE destination column; remaining rows zero.
            placements = [(lskip + 1, 0), (lskip, 1 << (lskip + 1)),
                          (max(0, lskip - 1), 3 << lskip)]
            stacked = [g.ZERO] * (1 << stack_log)
            combined = [g.ZERO] * len(stacked)
            direct = wrong = terminal = g.ZERO
            for height, start in placements:
                column = [rand() for _ in range(1 << height)]
                a, b = rand(), rand()
                stride = 1 << max(lskip - height, 0)
                for j, x in enumerate(column):
                    stacked[start + j * stride] = x
                point = [power(r[0], stride)] + r[1:1 + max(height - lskip, 0)]
                weights = dense_weights(min(lskip, height), point)
                direct = g.add(direct, total(g.mul(w, g.add(g.mul(a, x), g.mul(b, column[(j+1)%len(column)])))
                                             for j, (w, x) in enumerate(zip(weights, column))))
                wrong = g.add(wrong, total(g.mul(w, g.add(g.mul(a, x), g.mul(b, column[(j-1)%len(column)])))
                                           for j, (w, x) in enumerate(zip(weights, column))))
                for row in range(len(stacked)):
                    on_domain = [g.base(pow(31, ((P-1)//(1<<lskip))*(row%(1<<lskip)), P))]
                    on_domain += [g.base((row >> j) & 1) for j in range(lskip, stack_log)]
                    ka, kb = kernels(lskip, stack_log, height, start, r, on_domain)
                    combined[row] = g.add(combined[row], g.add(g.mul(a, ka), g.mul(b, kb)))
                ka, kb = kernels(lskip, stack_log, height, start, r, u)
                terminal = g.add(terminal, g.add(g.mul(a, ka), g.mul(b, kb)))
                short += height < lskip
            assert total(g.mul(x, y) for x, y in zip(stacked, combined)) == direct
            assert total(g.mul(x, y) for x, y in zip(combined, dense_weights(lskip, u))) == terminal
            checks += 2
            wrong_rotation += wrong != direct
    assert wrong_rotation == 12 and short == 12
    result = dict(status='EXT4_MIXED_PACKING_DENSE_PARITY', identity_checks=checks,
                  shared_column_fixtures=12, short_sources=short, wrong_rotation_distinguished=wrong_rotation,
                  scope='Independent small-domain algebra checks, not a sumcheck or PCS proof.')
    out = Path(__file__).resolve().parents[2] / 'results/swirl-security-review/native-stack-layout/ext4-checks.json'
    out.write_text(json.dumps(result, indent=2) + '\n')
    print(result)


if __name__ == '__main__':
    main()
