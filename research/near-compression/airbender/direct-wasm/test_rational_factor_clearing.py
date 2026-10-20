"""Exact common denominator clearing, scalar invariants and content blowup."""
import json
import random
from test_bivariate_multiplicity import add, mul, trim
from test_polynomial_fractions import make, times, equiv
from test_independent_constraint_mixing import evaluate
from test_polynomial_bezout_existence import irreducible


def clearing(coefficients, prime):
    if not coefficients: return [1], []
    (num, den), rest = coefficients[0], coefficients[1:]
    tail_den, tail_rows = clearing(rest, prime)
    return mul(den, tail_den, prime), [mul(num, tail_den, prime)]+[mul(den, row, prime) for row in tail_rows]


def main():
    rng = random.Random(4632)
    families = coefficients = evaluations = scalar_irreducibles = 0
    for prime in (2, 3, 5, 17):
        for _ in range(100):
            cs = []
            for _ in range(rng.randrange(7)):
                num = [rng.randrange(prime) for _ in range(rng.randrange(4))]+[0]
                den = [rng.randrange(prime) for _ in range(rng.randrange(3))]+[rng.randrange(1, prime), 0]
                cs.append(make(num, den))
            denominator, rows = clearing(cs, prime)
            assert trim(denominator) and len(rows) == len(cs)
            for r, row in zip(cs, rows):
                assert equiv(times(make(denominator, [1]), r, prime), make(row, [1]), prime)
                coefficients += 1
            # Algebraic-variable support and degree are unchanged, even with padding.
            assert [bool(r[0]) for r in cs] == [bool(trim(row)) for row in rows]
            for z in range(prime):
                scale = evaluate(denominator, z, prime)
                if not scale: continue
                original = [evaluate(num, z, prime)*pow(evaluate(den, z, prime), -1, prime) % prime for num, den in cs]
                cleared = [evaluate(row, z, prime) for row in rows]
                for a in range(prime):
                    assert evaluate(cleared, a, prime) == scale*evaluate(original, a, prime) % prime
                    assert (evaluate(cleared, a, prime) == 0) == (evaluate(original, a, prime) == 0)
                    evaluations += 1
            families += 1
        for a in range(prime):
            for b in range(prime):
                poly = [a, b, 1]
                if irreducible(poly, prime):
                    for c in range(1, prime):
                        assert irreducible([c*v % prime for v in poly], prime)
                        scalar_irreducibles += 1
        # Redundant denominators generate arbitrary content even for fixed Y^2-Z.
        for exponent in (1, 2, 5):
            den = [0]*exponent+[1]
            source = [[0, prime-1], [], [1]]
            presentations = [make(mul(row, den, prime), den) for row in source]
            common, rows = clearing(presentations, prime)
            assert len(common)-1 == 3*exponent
            assert max(len(trim(row))-1 for row in rows) == 3*exponent+1
            assert all(evaluate(row, 0, prime) == 0 for row in rows)
            assert evaluate(source[-1], 0, prime) == 1
    print(json.dumps(dict(rational_polynomial_families=families, exact_cleared_coefficients=coefficients,
        safe_root_and_evaluation_comparisons=evaluations, nonzero_scalar_irreducibility_checks=scalar_irreducibles,
        unbounded_content_examples=12,
        scope='Explicit nonzero common denominator clearing preserves generic degree, roots and irreducibility. Primitive normalization and source-controlled parameter-degree bounds remain open.'), indent=2))


if __name__ == '__main__':
    main()
