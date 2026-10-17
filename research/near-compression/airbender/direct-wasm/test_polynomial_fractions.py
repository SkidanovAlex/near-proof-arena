"""Formal fractions, independent normalization, and specialization-domain negatives."""
import json
import random
from test_bezout_smoothness import divide, egcd, sub
from test_bivariate_multiplicity import add, mul, trim


def make(n, d):
    n, d = trim(n), trim(d)
    assert d, 'formally zero denominator'
    return n, d


def equiv(a, b, p): return trim(mul(a[0], b[1], p)) == trim(mul(b[0], a[1], p))
def plus(a, b, p): return make(add(mul(a[0], b[1], p), mul(b[0], a[1], p), p), mul(a[1], b[1], p))
def times(a, b, p): return make(mul(a[0], b[0], p), mul(a[1], b[1], p))
def negative(a, p): return make(sub([], a[0], p), a[1])
def inverse(a): return make(a[1], a[0]) if a[0] else make([], [1])


def canonical(a, p):
    g, _, _ = egcd(*a, p)
    n, nr = divide(a[0], g, p)
    d, dr = divide(a[1], g, p)
    assert not nr and not dr
    scale = pow(d[-1], -1, p)
    return tuple(c*scale % p for c in n), tuple(c*scale % p for c in d)


def main():
    rng = random.Random(7103)
    cases = safe_specializations = zero_numerators = 0
    for p in (2, 3, 5, 17):
        def poly(nonzero=False):
            a = [rng.randrange(p) for _ in range(rng.randrange(1, 7))]
            if nonzero and not any(a): a[0] = 1
            return a+[0]*rng.randrange(3)
        def evalp(cs, x): return sum(c*pow(x, i, p) for i, c in enumerate(cs)) % p
        for _ in range(150):
            a, b = make(poly(), poly(True)), make(poly(), poly(True))
            s, t = poly(True), poly(True)
            aa = make(mul(a[0], s, p), mul(a[1], s, p))
            aaa = make(mul(aa[0], t, p), mul(aa[1], t, p))
            bb = make(mul(b[0], t, p), mul(b[1], t, p))
            assert equiv(a, aa, p) and equiv(aa, a, p)
            assert equiv(aa, aaa, p) and equiv(a, aaa, p)
            assert canonical(a, p) == canonical(aa, p) == canonical(aaa, p)
            assert equiv(a, b, p) == (canonical(a, p) == canonical(b, p))
            assert equiv(plus(a, b, p), plus(aa, bb, p), p)
            assert equiv(times(a, b, p), times(aa, bb, p), p)
            assert equiv(negative(a, p), negative(aa, p), p)
            assert equiv(inverse(a), inverse(aa), p)
            if a[0]: assert equiv(times(a, inverse(a), p), make([1], [1]), p)
            else:
                assert inverse(a) == make([], [1])
                zero_numerators += 1
            for x in range(p):
                d, dd = evalp(a[1], x), evalp(aa[1], x)
                if d and dd:
                    assert evalp(a[0], x)*pow(d, -1, p) % p == evalp(aa[0], x)*pow(dd, -1, p) % p
                    safe_specializations += 1
            cases += 1
        # Nonzero formal denominator vanishing at every base-field point.
        all_roots = [0]* (p+1)
        all_roots[1], all_roots[p] = p-1, 1
        a = make([1], all_roots)
        assert all(evalp(a[1], x) == 0 for x in range(p))
        assert equiv(times(a, inverse(a), p), make([1], [1]), p)
        # Z/Z equals one as a rational function but this representative has a pole at zero.
        cancelled = make([0, 1], [0, 1])
        assert equiv(cancelled, make([1], [1]), p)
        assert evalp(cancelled[1], 0) == 0
    try: make([1], [0, 0])
    except AssertionError: pass
    else: raise AssertionError('zero denominator accepted')
    print(json.dumps(dict(fraction_cases=cases, safe_specializations=safe_specializations,
        zero_numerators=zero_numerators, everywhere_vanishing_formal_denominators=4,
        cancelled_pole_examples=4, zero_denominator_rejections=1,
        scope='Formal polynomial fraction quotient, arithmetic and inverse. Full rational-function Field instance and specialization transport remain open.'), indent=2))


if __name__ == '__main__': main()
