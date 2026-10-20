#!/usr/bin/env python3
"""Extra proof bytes per Merkle tree for making blocks = level-c subtrees (Section 5.3).

Variant 'cap'  : send all 2^c narrow block roots; saves the multiproof siblings at levels 1..c.
Variant 'wide' : levels < c use 48-B (untruncated SHA-384) digests; multiproof siblings at
                 levels 1..c-1 cost 48 B instead of D bytes.
Expected multiproof siblings at level l for q uniform queries: 2*u_{l-1} - u_l,
u_l = 2^l (1 - (1 - 2^-l)^q)  (with replacement; d large).
"""
import sys
def u(l, q): return (2 ** l) * (1 - (1 - 2.0 ** -l) ** q)
def sib(l, q): return 2 * u(l - 1, q) - u(l, q)
def extra(q, c, D, wide=48):
    s_le_c = sum(sib(l, q) for l in range(1, c + 1))
    s_lt_c = sum(sib(l, q) for l in range(1, c))
    cap = (2 ** c) * D - s_le_c * D
    wd = s_lt_c * (wide - D)
    return cap, wd
if __name__ == "__main__":
    D = int(sys.argv[1]) if len(sys.argv) > 1 else 28
    for q in (41, 46, 50, 55, 60, 69):
        row = []
        for c in range(5, 15):
            cap, wd = extra(q, c, D)
            row.append(f"c={c}:{min(cap, wd)/1000:.1f}{'C' if cap <= wd else 'W'}")
        print(f"q={q} D={D}B  extra KB/tree (C=cap, W=wide top):", " ".join(row))
