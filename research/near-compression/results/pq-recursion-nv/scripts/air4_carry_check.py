#!/usr/bin/env python3
"""Independent interval check of the SHA AIR v4 residual equations (FAITHFUL.md §V).

Written from air.rs (lane/pq-sha384-air3 @ 34a427692), not from carry_bounds_v4.py.
Each check is E_i = R_i - S_i with every cell replaced by the integer value of its sender
expression.  Ranges: word / sign-form limb [0, 2^w - 1]; sum of two limbs [0, 2(2^w - 1)];
Y = Sigma0 + Maj - d in [-(2^w - 1), 2(2^w - 1)]; carries [0, 7] (A: stored with offset 4).
Asserts max |E_i| < p / 2 so that E_i = 0 mod p implies E_i = 0 over Z.
"""
P = 2**31 - 2**27 + 1
W = [21, 21, 22]
def L(w): return (0, 2**w - 1)          # one canonical limb
def L2(w): return (0, 2 * (2**w - 1))   # sum of two canonical limbs
def Y(w): return (-(2**w - 1), 2 * (2**w - 1))
C = (0, 7)
def add(*xs): return (sum(x[0] for x in xs), sum(x[1] for x in xs))
def neg(x): return (-x[1], -x[0])
def scale(k, x): return (k * x[0], k * x[1]) if k >= 0 else (k * x[1], k * x[0])
def lhs(i, out, off):  # out_i + 2^w (c_i - off) - (c_{i-1} - off)
    t = add(out, scale(2**W[i], add(C, (-off, -off))))
    if i > 0:
        t = add(t, neg(add(C, (-off, -off))))
    return t
def red(i, s):  # s_i - 2^w c_i + c_{i-1}
    t = add(s, neg(scale(2**W[i], C)))
    if i > 0:
        t = add(t, C)
    return t
worst = 0
rows = []
for i, w in enumerate(W):
    eqs = {
        "A out (R3): lhs(n0,c,4) - Y - e": add(lhs(i, L(w), 4), neg(Y(w)), neg(L(w))),
        "A in  (R3): lhs(n1,c,4) - M_in + d_in - e": add(lhs(i, L(w), 4), neg(L2(w)), L(w), neg(L(w))),
        "E out (R4): lhs(n0,c,0) - (h+K) - L_out - (d+W)": add(lhs(i, L(w), 0), neg(L2(w)), neg(L2(w)), neg(L2(w))),
        "E in  (R5): lhs(n1,c,0) - (h+K) - L_in - (W+d)": add(lhs(i, L(w), 0), neg(L2(w)), neg(L2(w)), neg(L2(w))),
        "W     (R6): lhs(n,c,0) - s1 - V - W7": add(lhs(i, L(w), 0), neg(L(w)), neg(L2(w)), neg(L(w))),
        "FF    (R7): reduce(H + final, c) - O": add(red(i, L2(w)), neg(L(w))),
    }
    for k, (lo, hi) in eqs.items():
        m = max(-lo, hi) / P
        worst = max(worst, m)
        rows.append((k, i, lo, hi, m))
for k, i, lo, hi, m in rows:
    print(f"{k:50s} limb {i}  [{lo:>12,}, {hi:>12,}]  max|E|/p = {m:.4f}")
print(f"worst max|E|/p = {worst:.4f}")
assert worst < 0.5
print("OK: every residual field equation is an integer equation")
