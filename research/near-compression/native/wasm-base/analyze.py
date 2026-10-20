#!/usr/bin/env python3
"""Cost per op from the prove logs (TABLE/STEPS/PROOF/TIME lines), in the units of
docs/zk-formal/V3-PERF-DESIGN.md §2.1 and tools/perf-design/model.py (`row_cost`, ML backend):

  committed cells per row  = m (main base cells; SWIRL commits no aux and no quotient)
  work cell-eq per row     = m + f · F_GKR / C + 6 X / C       (ML / SWIRL-like backend)
  X = 4.5 E^2, F_GKR = 42 E + 28 X, C = 306 (1+B)/3 + (4B/128)·1.05·2750 + 6 B E + 2·0.7·(6E+10), B = 2

f = LogUp fractions per row = number of interactions of the table (every interaction of every row
is a GKR leaf, including padding rows).  Per-op figures are *marginal*: the difference between two
program lengths divided by the step difference (fixed tables RANGE16/BYTE and the boundary cancel).
Usage: analyze.py <log_short> <log_long> [more logs ...]"""
import re, sys


def model(E, B=2):
    X = 4.5 * E * E
    C = 306 * (1 + B) / 3 + (4 * B / 128) * 1.05 * 2750 + 6 * B * E + 2 * 0.7 * (6 * E + 10)
    return X, C, (42 * E + 28 * X) / C, 6 * X / C


def parse(path):
    tabs, d = {}, {}
    for ln in open(path):
        m = re.match(r"TABLE (\S+)\s+width\s+(\d+) rows\s+(\d+) height\s+(\d+) cells\s+(\d+) constraints\s+(\d+) interactions\s+(\d+) degree (\d+)", ln)
        if m:
            n, w, rows, h, cells, ncon, ni, deg = m.groups()
            tabs[n] = dict(w=int(w), rows=int(rows), h=int(h), ni=int(ni), deg=int(deg))
        m = re.match(r"STEPS (\d+)", ln)
        if m:
            d['steps'] = int(m.group(1))
        m = re.match(r"PROOF total=(\d+)", ln)
        if m:
            d['proof'] = int(m.group(1))
        m = re.match(r"TIME .*prove ([\d.]+)s verify ([\d.]+)s", ln)
        if m:
            d['prove'], d['verify'] = float(m.group(1)), float(m.group(2))
    d['tabs'] = tabs
    return d


def totals(d, active=False):
    cells = frac = rows = 0
    for n, t in d['tabs'].items():
        r = t['rows'] if active else t['h']
        cells += r * t['w']
        frac += r * t['ni']
        rows += r
    return cells, frac, rows


def main():
    logs = [parse(p) for p in sys.argv[1:]]
    for E in (10, 12):
        X, C, fg, zc = model(E)
        print(f"E={E}: ops/cell C={C:.1f}, cell-eq per GKR fraction={fg:.2f}, per row zerocheck={zc:.2f}")
    print()
    for p, d in zip(sys.argv[1:], logs):
        c, f, r = totals(d)
        print(f"{p}: steps {d['steps']} committed cells {c} fractions {f} rows {r} proof {d.get('proof')} B "
              f"prove {d.get('prove')} s verify {d.get('verify')} s")
    a, b = logs[0], logs[-1]
    ds = b['steps'] - a['steps']
    print(f"\nmarginal per op between {a['steps']} and {b['steps']} steps (padded heights):")
    for active in (False, True):
        ca, fa, ra = totals(a, active)
        cb, fb, rb = totals(b, active)
        dc, df, dr = (cb - ca) / ds, (fb - fa) / ds, (rb - ra) / ds
        tag = "active rows only" if active else "padded (power-of-two) heights"
        print(f"  [{tag}] committed cells/op {dc:.1f}  fractions/op {df:.1f}  rows/op {dr:.2f}")
        for E in (10, 12):
            X, C, fg, zc = model(E)
            print(f"      E={E}: work cell-eq/op = {dc:.1f} + {df:.1f}·{fg:.2f} + {dr:.2f}·{zc:.2f} = {dc + df * fg + dr * zc:.0f}")
    print("\nper-table (long run): name width interactions degree rows/op")
    for n, t in b['tabs'].items():
        print(f"  {n:<9} {t['w']:>3} {t['ni']:>3} {t['deg']} {t['rows'] / b['steps']:.3f}")
    # per-op cost of each chip when an adversary runs only that op (1 row per op)
    _, C12, fg12, zc12 = model(12)
    _, C10, fg10, zc10 = model(10)
    print("\nadversarial single-op chains (1 chip row per op; RANGE16/BYTE amortised):")
    print("  chip      m   f  deg | committed | SWIRL/ML E=12 | ML E=10 | univariate U-logUp E=10 (est.)")
    for n, t in b['tabs'].items():
        if n in ("BOUNDARY", "RANGE16", "BYTE"):
            continue
        m, f, deg = t['w'], t['ni'], t['deg']
        ml12 = m + f * fg12 + zc12
        ml10 = m + f * fg10 + zc10
        dq = max(deg - 1, 1)
        ucells = m + 10 * ((f + 1) // 2 + 1) + 10 * dq
        uwork = ucells + f * 4410 / C10
        print(f"  {n:<8} {m:>3} {f:>3} {deg:>3} | {m:>9} | {ml12:>13.0f} | {ml10:>7.0f} | cells {ucells}, work {uwork:.0f}")


if __name__ == '__main__':
    main()
