"""Streamed x15 LDE + Merkle commit: memory bound and a throughput extrapolation.

Shapes: models-C fixed point at c_sha = 19,448 (see rbr_x15.py), the layer whose
prover commits on 15 * 2^(h+b) = 15 * 2^27 points per column.

Measured constants (this host, 8 threads on CPUs 8-15/24-31, shared with
other jobs; results/commit-*.txt): coset radix-2 RS encoding 4.6-7.3 ns per
(point, column) at coset size 2^18-2^20; SHA-384 Merkle (leaf + tree) 3.2-4.6
ns per (point, column) at W = 64.  Extrapolated linearly in points, with the
NTT's log factor scaled 27/20.  Everything below is MODELLED, not measured, at
these shapes.
"""
import math

GiB = 2 ** 30
SHAPES = {
    # name: (W stacked columns, h = log2 trace height per column, b = log2 blowup (2-adic), k1)
    'T x15 final (b7,h20,W151)': (151, 20, 7, 1),
    'L x15 final (b7,h20,W133)': (133, 20, 7, 1),
    'T COMBO+E5 final (W96)': (96, 20, 7, 1),
    'C-invention COMBO+E5 (b8,h19,W111)': (111, 19, 8, 1),
}
RS_NS = (4.6, 7.3)
MERKLE_NS = (3.2, 4.6)


def main():
    for name, (W, h, b, k1) in SHAPES.items():
        L = h + b                      # 2-adic part of the domain per coset
        pts = 15 * 2 ** L              # domain points per column
        elems = W * pts
        print(f"\n{name}: domain 15*2^{L} = 2^{math.log2(pts):.2f}, LDE cells {elems:.3e} = 2^{math.log2(elems):.2f}"
              f" -> {elems * 4 / 1e12:.2f} TB if materialised (4 B cells)")
        coeff = W * 2 ** h * 4
        print(f"  resident coefficients W*2^h*4B = {coeff / GiB:.2f} GiB")
        for s in (0, 3, 7):
            chunk = W * 2 ** (L - s) * 4
            print(f"  chunk = one radix-2 sub-coset zeta^a*omega^t*H_(2^{L - s}) (s={s}, {15 * 2 ** s} chunks):"
                  f" {chunk / GiB:7.2f} GiB per chunk")
        leaves = 15 * 2 ** (L - k1)
        print(f"  leaf digests 15*2^{L - k1} x 48 B = {leaves * 48 / GiB:.1f} GiB; full tree ~{2 * leaves * 48 / GiB:.1f} GiB;"
              f" cap at 2^20-point chunks: {15 * 2 ** (L - 20) * 48 / 2**10:.1f} KiB + recompute <= q0 chunks")
        r1 = 15 * 2 ** (L - 1) * 48
        print(f"  round-1 Ext12 codeword 15*2^{L - 1} x 48 B = {r1 / GiB:.1f} GiB (streamable the same way)")
        lo = elems * (RS_NS[0] * L / 20 + MERKLE_NS[0]) * 1e-9
        hi = elems * (RS_NS[1] * L / 20 + MERKLE_NS[1]) * 1e-9
        print(f"  CPU extrapolation (8 threads, measured constants): {lo / 60:.0f}-{hi / 60:.0f} min;"
              f" ideal linear scaling to 192 cores: {lo / 24 / 60:.1f}-{hi / 24 / 60:.1f} min")
        q0 = 52
        direct = q0 * 2 ** k1 * W * 2 ** h
        print(f"  opened rows without the LDE: direct evaluation of q0*2^k1 = {q0 * 2 ** k1} points x W columns"
              f" = {direct:.2e} mult-adds (seconds on CPU)")


if __name__ == '__main__':
    main()
