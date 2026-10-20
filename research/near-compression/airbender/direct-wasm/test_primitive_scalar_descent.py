"""Constructed finite Bezout units and rational factorization descent."""
import json
import random
from test_bivariate_multiplicity import add, mul, trim
from test_bezout_smoothness import divide, egcd
from test_polynomial_fractions import make, times, plus, inverse, canonical, equiv
from test_polynomial_content_normalization import content
from test_primitive_polynomial_product import product, primitive
from test_rational_factor_clearing import clearing


def unit_combination(rows, prime):
    g, weights = [], []
    for row in rows:
        g, a, b = egcd(g, row, prime)
        weights = [mul(a, w, prime) for w in weights]+[b]
    return g, weights


def normalize(coefficients, prime):
    den, rows = clearing(coefficients, prime)
    g = content(rows, prime)
    assert g
    rows = [divide(row, g, prime)[0] for row in rows]
    assert content(rows, prime) == [1]
    scalar = make(g, den)
    for c, row in zip(coefficients, rows):
        assert equiv(c, times(scalar, make(row, [1]), prime), prime)
    return scalar, rows


def rational_product(a, b, prime):
    out = [make([], [1]) for _ in range(len(a)+len(b)-1)]
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i+j] = plus(out[i+j], times(x, y, prime), prime)
    return out


def main():
    rng = random.Random(4651)
    units = scalar_checks = rejected = factorizations = coefficients = 0
    for prime in (2, 3, 5, 17):
        def nonzero_poly():
            return [rng.randrange(prime) for _ in range(rng.randrange(3))]+[rng.randrange(1, prime)]
        def family():
            rows = [nonzero_poly() if rng.randrange(3) else [] for _ in range(rng.randrange(1, 4))]
            if not any(rows): rows[0] = [1]
            return primitive(rows, prime)+[[], [0, 0]]
        for _ in range(100):
            rows = family()
            g, weights = unit_combination(rows, prime)
            assert g == [1]
            total = []
            for w, row in zip(weights, rows): total = add(total, mul(w, row, prime), prime)
            assert trim(total) == [1]
            units += 1
            for _ in range(8):
                r = make(nonzero_poly() if rng.randrange(4) else [], nonzero_poly())
                scaled = [canonical(times(r, make(row, [1]), prime), prime) for row in rows]
                all_polynomial = all(len(d) == 1 for _, d in scaled)
                assert all_polynomial == (len(canonical(r, prime)[1]) == 1)
                if all_polynomial:
                    descended = []
                    for w, (num, den) in zip(weights, scaled):
                        descended = add(descended, mul(w, [v*pow(den[0], -1, prime)%prime for v in num], prime), prime)
                    assert equiv(r, make(descended, [1]), prime)
                else: rejected += 1
                scalar_checks += 1
        for _ in range(40):
            left, right = family()[:-2], family()[:-2]
            c = nonzero_poly()
            r = make(nonzero_poly(), nonzero_poly())
            s = times(make(c, [1]), inverse(r), prime)
            p = [times(r, make(row, [1]), prime) for row in left]
            q = [times(s, make(row, [1]), prime) for row in right]
            # Redundant denominator factors stress exact descent, not pointwise values.
            for cs in (p, q):
                for i, (num, den) in enumerate(cs):
                    inflation = nonzero_poly()
                    cs[i] = make(mul(num, inflation, prime), mul(den, inflation, prime))
            source = [mul(c, row, prime) for row in product(left, right, prime)]
            pq = rational_product(p, q, prime)
            assert all(equiv(x, make(y, [1]), prime) for x, y in zip(pq, source))
            a, normalized_left = normalize(p, prime)
            b, normalized_right = normalize(q, prime)
            scalar = times(a, b, prime)
            num, den = canonical(scalar, prime)
            assert len(den) == 1
            descended_scalar = [x*pow(den[0], -1, prime)%prime for x in num]
            complement = [mul(descended_scalar, row, prime) for row in normalized_right]
            descended_product = product(normalized_left, complement, prime)
            assert list(map(trim, source)) == list(map(trim, descended_product))
            coefficients += len(source)
            factorizations += 1
        # Without primitive coefficients, 1/Z sends all rows into polynomials.
        rows = [[0, 1], [0, 1, 1]]
        r = make([1], [0, 1])
        assert len(canonical(r, prime)[1]) > 1
        assert all(len(canonical(times(r, make(row, [1]), prime), prime)[1]) == 1 for row in rows)
        # The empty/all-zero family satisfies integrality vacuously, but is not primitive.
        assert content([[], [0, 0]], prime) == []
    print(json.dumps(dict(constructed_unit_combinations=units,
        scalar_integrality_checks=scalar_checks, nonpolynomial_scalar_rejections=rejected,
        rational_factorizations_descended=factorizations, reconstructed_source_coefficients=coefficients,
        nonprimitive_counterexamples=4, zero_family_counterexamples=4,
        scope='Constructed unit span, rational scalar descent, primitive rational representations and polynomial factorization descent. Source-parameter-degree inheritance and full MCA/PQ128 remain open.'), indent=2))


if __name__ == '__main__':
    main()
