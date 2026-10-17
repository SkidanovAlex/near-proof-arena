"""Finite coefficient content, primitive normalization and reconstruction."""
import json
import random
from test_bezout_smoothness import divide, egcd
from test_bivariate_multiplicity import mul, trim
from test_independent_constraint_mixing import evaluate
from test_rational_factor_clearing import clearing
from test_polynomial_fractions import make


def content(rows, prime):
    result = []
    for row in rows: result = egcd(result, row, prime)[0]
    return result


def main():
    rng = random.Random(4640)
    families = reconstructions = greatest_checks = primitive_checks = roots = 0
    for prime in (2, 3, 5, 17):
        for _ in range(100):
            factor = [rng.randrange(prime) for _ in range(rng.randrange(5))]+[1]
            rows = [[rng.randrange(prime) for _ in range(rng.randrange(6))] for _ in range(rng.randrange(1, 7))]
            if not any(any(row) for row in rows): rows[0] = [1]
            rows = [mul(row, factor, prime)+[0]*rng.randrange(3) for row in rows]+[[], [0, 0]]
            g = content(rows, prime)
            assert g
            normalized = []
            for row in rows:
                q, remainder = divide(row, g, prime)
                assert not remainder and trim(mul(q, g, prime)) == trim(row)
                normalized.append(q)
                reconstructions += 1
            assert content(normalized, prime) == [1]
            assert len(rows) == len(normalized)
            for _ in range(20):
                d = [rng.randrange(prime) for _ in range(rng.randrange(5))]+[1]
                divides_all = all(not divide(row, d, prime)[1] for row in rows)
                assert divides_all == (not divide(g, d, prime)[1])
                greatest_checks += 1
                if all(not divide(row, d, prime)[1] for row in normalized):
                    assert len(trim(d)) == 1
                    primitive_checks += 1
            for z in range(prime):
                scale = evaluate(g, z, prime)
                if not scale: continue
                original = [evaluate(row, z, prime) for row in rows]
                primitive = [evaluate(row, z, prime) for row in normalized]
                for a in range(prime):
                    assert evaluate(original, a, prime) == scale*evaluate(primitive, a, prime) % prime
                    roots += 1
            families += 1
        # Arbitrary clearing content is removed from the fixed irreducible Y^2-Z.
        for exponent in (1, 2, 5, 9):
            den = [0]*exponent+[1]
            source = [[0, prime-1], [], [1]]
            _, rows = clearing([make(mul(row, den, prime), den) for row in source], prime)
            g = content(rows, prime)
            assert g == [0]*(3*exponent)+[1]
            normalized = [divide(row, g, prime)[0] for row in rows]
            assert normalized == source
    print(json.dumps(dict(nonzero_coefficient_families=families, exact_row_reconstructions=reconstructions,
        universal_common_divisor_checks=greatest_checks, primitive_divisor_checks=primitive_checks,
        safe_scaled_evaluation_checks=roots, redundant_denominator_content_removed=16,
        scope='Constructed common content, exact primitive normalization and irreducibility preservation. Gauss descent and original-source parameter-degree bounds remain open.'), indent=2))


if __name__ == '__main__':
    main()
