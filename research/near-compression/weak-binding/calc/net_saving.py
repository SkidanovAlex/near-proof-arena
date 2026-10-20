#!/usr/bin/env python3
"""Net final-layer saving vs 42-B digests: (42 - D) * 3 KB minus the wide-top cost of
making blocks = level-c subtrees (cap_cost.py), summed over the WHIR trees of the shape."""
import math, sys
import wb_bound
from wb_bound import SHAPES, nmin
wb_bound.SHIFT = "--shift" in sys.argv
from cap_cost import extra
KB_PER_BYTE = 3.0
for name in ("final 12k today 69/69/55/46 (268)", "final 12k levers 61/61/49/41 (236+z32)", "generic 4x50 (268 b/round)"):
    rounds, z = SHAPES[name]
    print(name)
    for c in range(6, 15):
        n, K, P = nmin(rounds, 2 ** c, z=z)
        D = math.ceil(n / 8)
        top = sum(min(extra(q, c, D)) for (q, _) in rounds) / 1000
        print(f"  c={c:2d} B={2**c:6d} n_min={n} D={D} B  K*={K:2d}  gross={(42-D)*KB_PER_BYTE:5.1f} KB  "
              f"block-structure cost={top:4.1f} KB  net={(42-D)*KB_PER_BYTE-top:5.1f} KB", flush=True)
