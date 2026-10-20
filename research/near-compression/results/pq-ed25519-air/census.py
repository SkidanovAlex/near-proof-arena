#!/usr/bin/env python3
"""Operation census for NearSpecV3.Ed25519 (spec/lean/v3/NearSpecV3/Ed25519.lean).

This is an executable transcription of that Lean module, preserving its exact
recursion structure:

  * `F.powAux 256 b e` runs 256 levels; every level does one squaring `mul r r`,
    and every level whose bit of `e` is 1 does one extra `mul (mul r r) b`.
  * `smulAux 256 n P` runs 256 levels; every level does one `Point.add Q Q`
    (doubling) and, if the bit of `n` is 1, one extra `Point.add Q2 P`.
  * `Point.add` performs 11 `F.mul` and 8 `F.add`/`F.sub` (counted below from
    the source expression, not assumed).

It counts every field operation the Lean code executes.  The arithmetic is Nat
arithmetic reduced mod p, exactly as in Lean, so the same file doubles as a
faithfulness check: run over oracle/fixtures/v3/ed25519/*.jsonl it must
reproduce every `verify` verdict (using hashlib only for SHA-512, which is not
part of the field-op census).

Nothing here is a proof; it is an instrumented transcription.
"""
import json
import sys
from collections import Counter
from pathlib import Path

P = 2**255 - 19
L = 2**252 + 27742317777372353535851937790883648493
D = 37095705934669439343138083508754565189542113879843219016388785533085940283555
SQRTM1 = 19681161376707505956807079304988542015446066515923890162744021073123829784752

C = Counter()


def mul(a, b):
    C["F.mul"] += 1
    return (a * b) % P


def fadd(a, b):
    C["F.add"] += 1
    return (a + b) % P


def fsub(a, b):
    C["F.sub"] += 1
    return (a + (P - b % P)) % P


def fneg(a):
    C["F.neg"] += 1
    return (P - a % P) % P


def pow_(b, e):
    """F.powAux 256 b e."""
    C["powAux.call"] += 1
    C["powAux.level"] += 256
    r = 1
    # powAux is MSB-first: level f+1 recurses into (e/2) and doubles on the way out.
    for i in range(255, -1, -1):
        r2 = mul(r, r)
        if (e >> i) & 1:
            r = mul(r2, b)
        else:
            r = r2
    return r


def inv(a):
    C["F.inv"] += 1
    return pow_(a, P - 2)


def isNeg(a):
    return a % P % 2 == 1


def abs_(a):
    return fneg(a) if isNeg(a) else a % P


def sqrtRatio(u, v):
    """F.sqrtRatio: returns (ok, root)."""
    C["sqrtRatio.call"] += 1
    v3 = mul(mul(v, v), v)
    v7 = mul(mul(v3, v3), v)
    r = mul(mul(u, v3), pow_(mul(u, v7), (P - 5) // 8))
    check = mul(v, mul(r, r))
    if check == u % P:
        return True, abs_(r)
    elif check == fneg(u):
        C["sqrtRatio.sqrtM1_branch"] += 1
        return True, abs_(mul(r, SQRTM1))
    else:
        return False, None


def point_zero():
    return (0, 1, 1, 0)


def point_ofAffine(x, y):
    return (x % P, y % P, 1, mul(x, y))


def point_add(Pa, Qa):
    C["Point.add"] += 1
    PX, PY, PZ, PT = Pa
    QX, QY, QZ, QT = Qa
    # a := F.mul (F.sub P.Y P.X) (F.sub Q.Y Q.X)          -> 1 mul, 2 sub
    a = mul(fsub(PY, PX), fsub(QY, QX))
    # b := F.mul (F.add P.Y P.X) (F.add Q.Y Q.X)          -> 1 mul, 2 add
    b = mul(fadd(PY, PX), fadd(QY, QX))
    # c := F.mul (F.mul P.T (F.mul 2 d)) Q.T              -> 3 mul
    c = mul(mul(PT, mul(2, D)), QT)
    # dd := F.mul (F.mul P.Z 2) Q.Z                       -> 2 mul
    dd = mul(mul(PZ, 2), QZ)
    e = fsub(b, a)
    f = fsub(dd, c)
    g = fadd(dd, c)
    h = fadd(b, a)
    # <F.mul e f, F.mul g h, F.mul f g, F.mul e h>         -> 4 mul
    return (mul(e, f), mul(g, h), mul(f, g), mul(e, h))


def point_neg(Pa):
    X, Y, Z, T = Pa
    return (fneg(X), Y, Z, fneg(T))


def smul(n, Pt):
    """smulAux 256 n P (LSB-first execution order, same operation multiset)."""
    C["smul.call"] += 1
    C["smul.level"] += 256
    Q = point_zero()
    # smulAux is MSB-first: level f+1 recurses into (n/2) and doubles on the way out.
    for i in range(255, -1, -1):
        Q2 = point_add(Q, Q)
        if (n >> i) & 1:
            Q = point_add(Q2, Pt)
        else:
            Q = Q2
    return Q


def affine(Pt):
    X, Y, Z, T = Pt
    zi = inv(Z)
    return (mul(X, zi), mul(Y, zi))


def leN(n, k):
    return [(n >> (8 * i)) & 0xFF for i in range(k)]


def encode(Pt):
    x, y = affine(Pt)
    return leN((y + 2**255 * (x % 2)) % 2**256, 32)


def leToNat(bs):
    n = 0
    for i, b in enumerate(bs):
        n += b << (8 * i)
    return n


B_X = 15112221349535400772501151409588531511454012693041857206046113283949847762202
B_Y = 46316835694926478169428394003475163141307993866256225615783033603165251855960
B = point_ofAffine(B_X, B_Y)


def decode(bs):
    C["decode.call"] += 1
    n = leToNat(bs)
    y = n % 2**255 % P
    sign = n // 2**255 % 2
    yy = mul(y, y)                      # 1
    u = fsub(yy, 1)                     # sub
    v = fadd(mul(D, yy), 1)             # 1 mul, add
    ok, x0 = sqrtRatio(u, v)
    if not ok:
        return None
    x = fneg(x0) if sign == 1 else x0
    return (x, y, 1, mul(x, y))         # 1 mul


def sha512(data):
    import hashlib
    return hashlib.sha512(bytes(data)).digest()


def verify_raw(pk, sig, msg):
    """Returns (verdict, sha512_input_length). Counters accumulate in C."""
    if len(pk) != 32 or len(sig) != 64:
        return False, 0
    A = decode(pk)
    if A is None:
        return False, 0
    Rb = sig[:32]
    s = leToNat(sig[32:])
    if L <= s:
        return False, 0
    h = sha512(list(Rb) + list(pk) + list(msg))
    C["sha512.call"] += 1
    C["sha512.input_bytes"] += len(Rb) + len(pk) + len(msg)
    k = leToNat(list(h)) % L
    Rprime = encode(point_add(smul(s, B), smul(k, point_neg(A))))
    return Rprime == list(Rb), len(Rb) + len(pk) + len(msg)


def sha512_blocks(nbytes):
    return (nbytes + 1 + 16 + 127) // 128


def popcount(x):
    return bin(x).count("1")


def max_popcount_below(n):
    if n <= 0:
        return 0
    best = 0
    for b in range(n.bit_length() - 1, -1, -1):
        if (n >> b) & 1:
            # take prefix equal, this bit 0, all lower bits 1
            cand = bin(n >> (b + 1)).count("1") + (b)
            best = max(best, cand)
            # and the branch bit 1, remaining lower must be < rest
    # the "all lower 1 with borrow" trick above gives the maximum
    return best


def closed_form(ps, pk, sqrtM1=False, sign=True, abs_neg=True):
    """Census as a function of popcount(s), popcount(k) and the two branch flags.

    Derived term by term from the source expressions:
      Point.add   = 2 + 3 + 2 + 4 = 11 mul, 2+2+1+1+1+1 = 8 add/sub
      sqrtRatio   = v3 2, v7 2, [mul(u,v7) 1, pow 507, mul(u,v3) 1, outer 1],
                    check 2, (+1 mul if the sqrtM1 branch is taken)
      decode      = yy 1, d*yy 1, sqrtRatio, x*y 1;  sub 1, add 1, neg(u) 1
      encode      = pow(Z,p-2) 509, X*zi 1, Y*zi 1;  point_neg(A) 2 neg
    """
    point_adds = 512 + ps + pk + 1          # 2*256 doublings + set bits + final add
    pa_muls = 11 * point_adds
    pa_adds = 8 * point_adds
    sqrt_muls = 2 + 2 + 1 + 507 + 1 + 1 + 2 + (1 if sqrtM1 else 0)
    decode_muls = 1 + 1 + sqrt_muls + 1
    encode_muls = 509 + 1 + 1
    return {
        "F.mul": pa_muls + decode_muls + encode_muls,
        "F.add/F.sub": pa_adds + 2,
        # point_neg(A) 2, sqrtRatio's neg(u) (only when the first branch fails),
        # abs_ in sqrtRatio (only if the raw root is odd), decode sign flip (0/1)
        "F.neg": 2 + (1 if sqrtM1 or True else 0) + (1 if abs_neg else 0) + (1 if sign else 0),
        "Point.add": point_adds,
        "Point.doubling": 512,
        "F.inv (pow p-2)": 1,
        "F.pow (p-5)/8": 1,
        "sqrtRatio.call": 1,
        "sqrtM1_branch": 1 if sqrtM1 else 0,
    }


if __name__ == "__main__":
    import hashlib
    # sanity: pow multiplier counts
    C.clear(); pow_(2, P - 2)
    print("pow(p-2):", dict(C))
    C.clear(); pow_(2, (P - 5) // 8)
    print("pow((p-5)/8):", dict(C))

    print("max popcount(s) for s<L:", max_popcount_below(L))
    print("L bitlen:", L.bit_length())

    fx = Path("oracle/fixtures/v3/ed25519")
    files = sorted(fx.glob("*.jsonl"))
    total = 0
    bad = 0
    stats = []
    for f in files:
        if f.name == "sha512.jsonl":
            continue
        for line in f.read_text().splitlines():
            if not line.strip():
                continue
            j = json.loads(line)
            pk = list(bytes.fromhex(j["pk"]))
            sig = list(bytes.fromhex(j["sig"]))
            msg = list(bytes.fromhex(j["msg"]))
            C.clear()
            got, hlen = verify_raw(pk, sig, msg)
            total += 1
            want = j.get("verify")
            if want is not None and bool(want) != got:
                bad += 1
                print("MISMATCH", f.name, j.get("id"), "want", want, "got", got)
            if got:
                s = leToNat(sig[32:])
                k = leToNat(list(sha512(bytes(pk).join([bytes(sig[:32]), bytes(msg)]))) ) % L
                stats.append((popcount(s), popcount(k), hlen, dict(C)))
    print(f"fixtures: {total} checked, {bad} mismatches")
    if stats:
        import statistics
        ps = [x[0] for x in stats]
        pk_ = [x[1] for x in stats]
        hl = [x[2] for x in stats]
        print(f"accepting fixtures: {len(stats)}")
        print(f"popcount(s): min {min(ps)} avg {statistics.mean(ps):.1f} max {max(ps)}")
        print(f"popcount(k): min {min(pk_)} avg {statistics.mean(pk_):.1f} max {max(pk_)}")
        print(f"sha512 input bytes: min {min(hl)} max {max(hl)}")
        muls = [x[3]["F.mul"] for x in stats]
        adds = [x[3]["F.add"] + x[3]["F.sub"] for x in stats]
        pa = [x[3]["Point.add"] for x in stats]
        print(f"executed F.mul: min {min(muls)} avg {statistics.mean(muls):.1f} max {max(muls)}")
        print(f"executed add/sub: min {min(adds)} avg {statistics.mean(adds):.1f} max {max(adds)}")
        print(f"executed Point.add: min {min(pa)} avg {statistics.mean(pa):.1f} max {max(pa)}")
        # compare executed vs closed form for one sample
        ps0, pk0, hl0, c0 = stats[0]
        cf = closed_form(ps0, pk0)
        print("sample closed form:", cf)
        print("sample executed     :", {k: v for k, v in c0.items()
              if k in ("F.mul", "F.add", "F.sub", "Point.add")})
