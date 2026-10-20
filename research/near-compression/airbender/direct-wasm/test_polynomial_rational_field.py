"""Rational-field laws, characteristic, and indeterminate regressions."""
import json
import random
from test_polynomial_fractions import make, equiv, plus, times, negative, inverse, canonical


def main():
    rng = random.Random(44071)
    field_cases = characteristic_checks = variable_checks = 0
    for p in (2, 3, 5, 17):
        zero, one, z = make([], [1]), make([1], [1]), make([0, 1], [1])
        def scalar(c): return make([c % p], [1])
        def random_fraction():
            n = [rng.randrange(p) for _ in range(rng.randrange(5))]
            d = [rng.randrange(p) for _ in range(rng.randrange(1, 5))]
            if not any(d): d[0] = 1
            return make(n, d)
        for n in range(-2*p, 2*p+1):
            assert equiv(scalar(n), zero, p) == (n % p == 0)
            assert equiv(scalar(-n), negative(scalar(n), p), p)
            assert equiv(scalar(n+1), plus(scalar(n), one, p), p)
            characteristic_checks += 1
        for _ in range(100):
            a, b, c = random_fraction(), random_fraction(), random_fraction()
            equalities = [
                (plus(a, zero, p), a),
                (plus(a, b, p), plus(b, a, p)),
                (plus(plus(a, b, p), c, p), plus(a, plus(b, c, p), p)),
                (times(times(a, b, p), c, p), times(a, times(b, c, p), p)),
                (times(a, one, p), a),
                (times(a, b, p), times(b, a, p)),
                (times(a, zero, p), zero),
                (times(a, plus(b, c, p), p), plus(times(a, b, p), times(a, c, p), p)),
                (plus(a, negative(a, p), p), zero),
                (inverse(inverse(a)), a),
            ]
            if a[0]: equalities.append((times(a, inverse(a), p), one))
            else: equalities.append((inverse(a), zero))
            for left, right in equalities:
                assert equiv(left, right, p)
                assert canonical(left, p) == canonical(right, p)
            poly = [rng.randrange(p) for _ in range(rng.randrange(10))]+[0, 0]
            value = zero
            for coefficient in reversed(poly):
                value = plus(scalar(coefficient), times(z, value, p), p)
            assert equiv(value, make(poly, [1]), p)
            assert equiv(value, zero, p) == (not any(poly))
            variable_checks += 1
            field_cases += 1
        poly = [0]*(p+1)
        poly[1], poly[p] = p-1, 1
        assert all(sum(c*pow(x, i, p) for i, c in enumerate(poly)) % p == 0 for x in range(p))
        assert not equiv(make(poly, [1]), zero, p)
    print(json.dumps(dict(field_law_cases=field_cases, characteristic_checks=characteristic_checks,
        indeterminate_evaluation_checks=variable_checks, finite_function_collapse_negatives=4,
        scope='Complete Lean rational-function Field and characteristic, injective coefficient map, transcendental indeterminate. Safe specialization and full MCA/protocol soundness remain open.'), indent=2))


if __name__ == '__main__': main()
