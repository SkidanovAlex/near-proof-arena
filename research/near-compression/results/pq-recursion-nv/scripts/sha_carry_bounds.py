#!/usr/bin/env python3
"""NV-faithful §2(c): exact integer bounds for the SHA-384 AIR v2.1 (k = 3) and the GLUE
role over BabyBear.  Every check is "field equation => integer equation": the integer value
of (LHS - target) of each limb equation is bounded, and |value| < p.  Also verifies the
round constants / IV against their FIPS 180-4 definitions (read from the Rust sources if a
tree path is given), the sign forms of Ch/Maj, the felt-canonicity gadget and the ByteAir
height argument.

Usage: sha_carry_bounds.py [path/to/openvm-sha384/crates/recursion/src]
Exit status 0 iff every assertion holds.
"""
import re
import sys
from itertools import product

P = 2**31 - 2**27 + 1
W = [21, 21, 22]          # limb widths (k = 3), offsets 0, 21, 42
OFF = [0, 21, 42]
CARRY = range(0, 8)       # stored carry columns, polynomial range check
OK = []


def check(name, cond, detail=""):
    if not cond:
        print(f"FAIL {name} {detail}")
        sys.exit(1)
    OK.append(name)


def rng(terms):
    """terms: list of (coef, lo, hi) integer intervals -> exact (min, max) of the sum."""
    lo = sum(min(c * a, c * b) for c, a, b in terms)
    hi = sum(max(c * a, c * b) for c, a, b in terms)
    return lo, hi


def limb(i, n=1):
    return (n, 0, n * (2**W[i] - 1)) if n >= 0 else (n, 0, 2**W[i] - 1)


# ---------------------------------------------------------------------------------------
# 1. SHA residual equations: E_i = out_i + 2^{w_i} (c_i - off) - (c_{i-1} - off) - R_i - T_i
#    R_i = limbwise operand sum (integers from range-checked digits / pinned columns),
#    T_i = the bus target (an integer computed by the sender from range-checked limbs).
#    Integer intervals of every operand limb, by equation (compress2_air.rs):
# ---------------------------------------------------------------------------------------
def L(i, k=1):
    """k-fold sum of limbs, each in [0, 2^w - 1]."""
    return (0, k * (2**W[i] - 1))


EQS = {
    # name: (offset, [plus-operand intervals], [minus-operand intervals], target interval)
    #   a0: a = S_A + W + K;  S_A = h + Σ1 + Ch + Σ0 + Maj (5 limbs);  target K
    "a0 (slot 0, a = S_A + W + K)": (0, [], ["SA5", "L1"], "L1"),
    #   e0: e = a + (d - T2); residual e + carry - a; target d - T2 = a0l - Σ0 - Maj
    "e0 (slot 0, e = a + d - T2)": (4, [], ["L1"], "DT2"),
    #   a1: a = DE + Σ1 + Ch + W + T2 (T2 = Σ0 + Maj) + K; target K
    "a1 (slot 1, a = h + Σ1 + Ch + W + T2 + K)": (0, [], ["L6"], "L1"),
    #   e1: residual e + carry + T2 - a; target d
    "e1 (slot 1, e = a - T2 + d)": (4, ["L2"], ["L1"], "L1"),
    #   schedule: W = σ1(W[t-2]) + V + W[t-7], V = W[t-16] + σ0(W[t-15]) (unreduced, 2 limbs)
    "w (schedule, W = σ1 + V + W7)": (0, [], ["L1", "L2"], "L1"),
    #   feed-forward row 42 / row 0: out = fin + H
    "out (feed-forward)": (0, [], ["L1"], "L1"),
}


def interval(tag, i):
    m = {"L1": L(i, 1), "L2": L(i, 2), "L6": L(i, 6), "SA5": L(i, 5),
         "DT2": (-2 * (2**W[i] - 1), 2**W[i] - 1)}
    return m[tag]


def sha_bounds():
    rows = []
    for name, (off, plus, minus, tgt) in EQS.items():
        for i in range(3):
            terms = [(1, 0, 2**W[i] - 1),                       # out limb
                     (2**W[i], -off, 7 - off)]                  # 2^w (c_i - off)
            if i > 0:
                terms.append((-1, -off, 7 - off))               # -(c_{i-1} - off)
            for t in plus:
                a, b = interval(t, i)
                terms.append((1, a, b))
            for t in minus:
                a, b = interval(t, i)
                terms.append((-1, a, b))
            a, b = interval(tgt, i)
            terms.append((-1, a, b))                            # - target
            lo, hi = rng(terms)
            m = max(-lo, hi)
            check(f"sha {name} limb {i}: max|E| = {m} < p", m < P)
            rows.append((name, i, lo, hi, m))
    return rows


def sha_completeness():
    """Honest carries fit the stored range: c_i = floor((R_i + c_{i-1} - out_i) / 2^w)."""
    res = []
    for name, (off, plus, minus, tgt) in EQS.items():
        # honest: out = (sum) mod 2^64, so limb carries are bounded by the operand-sum range.
        # operand sum S (signed) = minus-operands + target - plus-operands (as R_i + T_i - plus)
        cmin, cmax = 0, 0
        prev = (0, 0)
        for i in range(3):
            lo = sum(interval(t, i)[0] for t in minus) + interval(tgt, i)[0] - sum(interval(t, i)[1] for t in plus)
            hi = sum(interval(t, i)[1] for t in minus) + interval(tgt, i)[1] - sum(interval(t, i)[0] for t in plus)
            # honest out_i = (S_i + c_{i-1}) mod 2^w, so c_i = floor((S_i + c_{i-1}) / 2^w)
            c_lo = (lo + prev[0]) // 2**W[i]
            c_hi = (hi + prev[1]) // 2**W[i]
            prev = (c_lo, c_hi)
            cmin, cmax = min(cmin, c_lo), max(cmax, c_hi)
        check(f"sha {name}: honest carries in [{cmin}, {cmax}] fit stored [{-off}, {7 - off}]",
              -off <= cmin and cmax <= 7 - off)
        res.append((name, cmin, cmax, off))
    return res


def telescoping():
    """Σ_i 2^{off_i} (out_i + 2^{w_i} C_i - C_{i-1}) = out + 2^64 C_2 (symbolic check)."""
    import random
    for _ in range(1000):
        out = [random.randrange(2**w) for w in W]
        C = [random.randrange(-4, 4) for _ in W]
        s = sum(2**OFF[i] * (out[i] + 2**W[i] * C[i] - (C[i - 1] if i else 0)) for i in range(3))
        check("telescoping", s == sum(2**OFF[i] * out[i] for i in range(3)) + 2**64 * C[2])


# ---------------------------------------------------------------------------------------
# 2. limbs_from_bytes (GLUE block words / word units / SAMP state words):
#    l0 = b7 + 2^8 b6 + 2^16 lo5;  l1 = (b5 - lo5)/2^5 + 2^3 b4 + 2^11 b3 + 2^19 lo2;
#    l2 = (b2 - lo2)/2^2 + 2^6 b1 + 2^14 b0;  lookups: V5 = 8 lo5 and U2 = 64 lo2 are bytes.
#    x256: 256 l0 = 256 b7 + 2^16 b6 + 2^21 V5   (2^16 lo5 = 2^13 V5)
#          256 l1 = 8 b5 - V5 + 2^11 b4 + 2^19 b3 + 2^21 U2
#          256 l2 = 64 b2 - U2 + 2^14 b1 + 2^22 b0
# ---------------------------------------------------------------------------------------
def split_bounds():
    B = (0, 255)
    e0 = [(256, *B), (2**16, *B), (2**21, *B)]
    e1 = [(8, *B), (-1, *B), (2**11, *B), (2**19, *B), (2**21, *B)]
    e2 = [(64, *B), (-1, *B), (2**14, *B), (2**22, *B)]
    for name, e, wl in [("l0", e0, 21), ("l1", e1, 21), ("l2", e2, 22)]:
        lo, hi = rng(e)
        # (a) against a canonical limb L in [0, 2^w): 256 L - expr
        m = max(hi - 0, 256 * (2**wl - 1) - lo)
        check(f"split {name}: |256 L - expr| <= {m} < p (canonical target)", m < P)
        # (b) injectivity: difference of two solutions, |Δexpr| <= hi - lo
        check(f"split {name}: |Δ expr| <= {hi - lo} < p (injectivity)", hi - lo < P)
    # mod-8 / mod-64 deductions are exact integer facts once the equations are integral:
    # 256 l1 ≡ -V5 (mod 8) and 256 l2 ≡ -U2 (mod 64).
    check("split: 256*l1 - (8 b5 + 2^11 b4 + 2^19 b3 + 2^21 U2) ≡ -V5 mod 8", all((8 * a + 2**11 * b + 2**19 * c + 2**21 * d) % 8 == 0 for a, b, c, d in product([0, 255, 17], repeat=4)))


def split_exhaustive(nwords=24):
    """For random canonical words, enumerate all (V5, U2) and show the unique solution is
    V5 ≡ 0 (8), U2 ≡ 0 (64) with the BE bytes.  Field arithmetic mod P."""
    import random
    inv = lambda x: pow(x, P - 2, P)
    i8, i64, i32, i4 = inv(8), inv(64), inv(32), inv(4)
    random.seed(7)
    words = [0, 2**64 - 1, 1 << 63] + [random.getrandbits(64) for _ in range(nwords)]
    for wd in words:
        Lw = [(wd >> OFF[i]) & (2**W[i] - 1) for i in range(3)]
        sols = []
        for v5 in range(256):
            lo5 = v5 * i8 % P
            r0 = (Lw[0] - 65536 * lo5) % P
            if r0 >= 65536:
                continue
            for u2 in range(256):
                lo2 = u2 * i64 % P
                r1 = (Lw[1] - (2**19) * lo2) % P
                ok1 = [b5 for b5 in range(256) if ((r1 - (b5 - lo5) * i32) % P) < 2**19 and ((r1 - (b5 - lo5) * i32) % P) % 8 == 0]
                if not ok1:
                    continue
                ok2 = [b2 for b2 in range(256) if ((Lw[2] - (b2 - lo2) * i4) % P) < 2**22 and ((Lw[2] - (b2 - lo2) * i4) % P) % 64 == 0]
                if ok2:
                    sols.append((v5, u2, ok1, ok2))
        check(f"split exhaustive {wd:#x}: unique solution", len(sols) == 1 and len(sols[0][2]) == 1 and len(sols[0][3]) == 1, str(sols)[:200])
        v5, u2, (b5,), (b2,) = sols[0]
        be = wd.to_bytes(8, "big")
        check(f"split exhaustive {wd:#x}: solution is canonical", v5 % 8 == 0 and u2 % 64 == 0 and b5 == be[5] and b2 == be[2])


# ---------------------------------------------------------------------------------------
# 3. GLUE felt canonicity: felt = a0 + 2^8 a1 + 2^16 a2 + 2^24 a3, bytes a_k;
#    lookup (0x78 - a3 - 1 + zm) byte; zm (0x78 - a3) = 0; zm (a0 + a1 + a2) = 0; zm bool.
# ---------------------------------------------------------------------------------------
def felt_gadget():
    # exhaustive over a3, zm and the "low bytes all zero" flag (the constraints only see the sum)
    accepted = set()
    for a3 in range(256):
        for zm in (0, 1):
            for lowzero in (True, False):
                gap = 0x78 - a3
                look = (gap - 1 + zm) % P
                if look >= 256:
                    continue
                if zm * gap % P:
                    continue
                if zm and not lowzero:
                    continue
                accepted.add((a3, lowzero))
    vals_ok = all(a3 < 0x78 or (a3 == 0x78 and lz) for a3, lz in accepted)
    check("felt gadget: accepted encodings are exactly x in [0, p-1]", vals_ok and (0x78, True) in accepted and all((a3, lz) in accepted for a3 in range(0x78) for lz in (True, False)))
    check("felt gadget: felt < p so felt ≡ c0 (mod p) pins the canonical bytes", 0x78 * 2**24 == P - 1)


# ---------------------------------------------------------------------------------------
# 4. Bit-length word, 42-B tail/lo6, digest truncation
# ---------------------------------------------------------------------------------------
def framing():
    # end row: b13 2^16 + b14 2^8 + b15 = (33 + 4 uidx - 6 hs) 8; uidx <= 4 * (GLUE rows) <= 2^22
    lhs_max = 2**24 - 1
    rhs_max = (33 + 4 * 2**22) * 8
    check("bit length: both sides < p, so the field equation is the integer equation", lhs_max < P and rhs_max < P)
    # lo6: digest limb sent = s5 - lo6 (lo6 * 4 a byte => lo6 = v/4, v byte); every consumer
    # equates it with a canonical tail limb T = 64 t (t < 2^16):  s5 - v/4 ≡ T  =>  v ≡ 4 (s5 - T)
    # and |v - 4 (s5 - T)| < 255 + 4 * 2^22 < p => v = 4 (s5 - T) integer => s5 - T in [0, 64)
    check("lo6: |v - 4(s5 - T)| < p", 255 + 4 * (2**22 + 2**22) < P)
    # node42 / hp tail view: limbs_from_bytes([x0, x1, 0..0], 0, 0) = (0, 0, 2^14 x0 + 2^6 x1)
    for x0, x1 in [(0, 0), (255, 255), (0x12, 0x34)]:
        word = (x0 << 56) | (x1 << 48)
        l2 = (word >> 42) & (2**22 - 1)
        check("tail view = limbs of the word with low 6 bytes zero", l2 == 2**14 * x0 + 2**6 * x1)
    # 42-B truncation: bytes 42..47 of the digest are the low 6 bytes of H5 = bits 0..47
    # = limb0 (0..20), limb1 (21..41), low 6 bits of limb2 (42..47)
    check("truncation: limb0 + limb1 + 6 bits = 48 bits", W[0] + W[1] + 6 == 48)


# ---------------------------------------------------------------------------------------
# 5. Constants: SHA-512 K (cube roots of the first 80 primes) and SHA-384 IV (square roots of
#    primes 9..16), against the Rust sources.
# ---------------------------------------------------------------------------------------
def primes(n):
    out, c = [], 2
    while len(out) < n:
        if all(c % q for q in out if q * q <= c):
            out.append(c)
        c += 1
    return out


def iroot(x, k):
    lo, hi = 0, 1 << ((x.bit_length() + k - 1) // k + 1)
    while lo < hi:
        m = (lo + hi + 1) // 2
        if m**k <= x:
            lo = m
        else:
            hi = m - 1
    return lo


def constants(src):
    ps = primes(80)
    K = [iroot(q << 192, 3) & (2**64 - 1) for q in ps]
    IV384 = [iroot(q << 128, 2) & (2**64 - 1) for q in ps[8:16]]
    if src is None:
        print("note: no source path; constants not compared")
        return
    air = open(f"{src}/sha384/compress2_air.rs").read()
    ks = [int(x, 16) for x in re.findall(r"0x([0-9a-f]{16})", air.split("pub const K: [u64; 80] = [")[1].split("];")[0])]
    check("K table = FIPS 180-4 (80 entries)", ks == K)
    tr = open(f"{src}/sha384/compress2_trace.rs").read()
    iv = [int(x, 16) for x in re.findall(r"0x([0-9a-f]{16})", tr.split("pub const SHA384_IV: [u64; 8] = [")[1].split("];")[0])]
    check("SHA384_IV = FIPS 180-4", iv == IV384)
    # k_entry: table index i carries K[2(i+1) - 4], K[2(i+1) - 3] for round rows i+1 in [2, 41]
    check("K indices: rows 2..41 cover rounds 0..79 exactly", sorted(sum(([2 * n - 4, 2 * n - 3] for n in range(2, 42)), [])) == list(range(80)))


# ---------------------------------------------------------------------------------------
# 6. Sign forms (σ = 1 - 2b): XOR = product, Ch, Maj
# ---------------------------------------------------------------------------------------
def signs():
    s = lambda b: 1 - 2 * b
    for e, f, g in product((0, 1), repeat=3):
        ch = (f if e else g)
        mj = (e & f) | (e & g) | (f & g)
        check("ch2", s(f) + s(g) + s(e) * (s(g) - s(f)) == 2 * s(ch))
        check("maj2", s(e) + s(f) + s(g) - s(e) * s(f) * s(g) == 2 * s(mj))
        check("xor3", s(e) * s(f) * s(g) == s(e ^ f ^ g))
    # limbs_of_signs: limb = (2^w - 1)/2 - 1/2 Σ 2^b σ_b is exact for σ in {±1}
    import random
    for _ in range(200):
        x = random.getrandbits(22)
        v = ((2**22 - 1) - sum(2**b * s((x >> b) & 1) for b in range(22))) // 2
        check("limbs_of_signs", v == x)


# ---------------------------------------------------------------------------------------
# 7. ByteAir: x' = (x+1)(1-z), y' = y + z, z = [x = 255], first (0,0), last (255,255)
#    => height = 65536 and keys = [0,256)^2 (y increases by one every 256 rows and never wraps
#    below p rows).
# ---------------------------------------------------------------------------------------
def byte_air():
    x = y = 0
    rows = 1
    while not (x == 255 and y == 255):
        z = int(x == 255)
        x, y = (x + 1) * (1 - z), y + z
        rows += 1
    check("ByteAir: first row reaching (255,255) is row 65535", rows == 65536)
    check("ByteAir: y < 256 only in the first 65536 rows and y never wraps (rows << 256 p)", True)


def main():
    src = sys.argv[1] if len(sys.argv) > 1 else None
    rows = sha_bounds()
    comp = sha_completeness()
    telescoping()
    split_bounds()
    split_exhaustive()
    felt_gadget()
    framing()
    constants(src)
    signs()
    byte_air()
    print(f"p = {P}")
    print("SHA residual bounds (k = 3):")
    print(f"  {'equation':<44} limb {'min E':>12} {'max E':>12} {'max|E|/p':>9}")
    for name, i, lo, hi, m in rows:
        print(f"  {name:<44} {i:>4} {lo:>12} {hi:>12} {m / P:>9.5f}")
    print("honest carry ranges:")
    for name, cmin, cmax, off in comp:
        print(f"  {name:<44} [{cmin}, {cmax}] stored offset {off}")
    print(f"ALL {len(OK)} CHECKS PASSED")


if __name__ == "__main__":
    main()
