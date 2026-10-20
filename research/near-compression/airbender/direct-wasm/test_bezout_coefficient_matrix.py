"""Explicit Bezout orientation checked against Euclid, convolution, and elimination."""
import json
import random
from test_bezout_smoothness import divide, egcd
from test_bivariate_multiplicity import add, mul, trim
from test_determinant_row_replacement import solve_transpose
from test_polynomial_determinant_degree import numeric_det


def coeff(poly, i):
    return poly[i] if 0 <= i < len(poly) else 0


def entry(p, q, m, n, i, j):
    if j < n:
        return coeff(p, i-j) if j <= i else 0
    return coeff(q, i-(j-n)) if j < m+n and j-n <= i else 0


def main():
    rng = random.Random(4548)
    systems = actions = inverses = cramer = empty = constants = loose = 0
    for prime in (2, 3, 5, 17):
        accepted = 0
        while accepted < 80:
            # m is a degree bound, not necessarily the exact degree of p.
            m, n = rng.randrange(4), rng.randrange(4)
            actual = rng.randrange(m+1)
            p = [rng.randrange(prime) for _ in range(actual)]+[rng.randrange(1, prime)]
            q = [rng.randrange(prime) for _ in range(n)]+[rng.randrange(1, prime)]
            g, a, b = egcd(p, q, prime)
            if g != [1]:
                continue
            p += [0]*rng.randrange(4)
            q += [0]*rng.randrange(4)
            size = m+n
            matrix = [[entry(p, q, m, n, i, j) for i in range(size)] for j in range(size)]
            determinant = numeric_det(matrix, prime)
            assert determinant != 0
            for target in [[rng.randrange(prime) for _ in range(size)]] + [[0]*r+[1] for r in range(size)]:
                quotient, u = divide(mul(a, target, prime), q, prime)
                v = trim(add(mul(b, target, prime), mul(quotient, p, prime), prime))
                assert len(u) <= n and len(v) <= m
                # Padding must not affect the finite coefficient map.
                u += [0]*3
                v += [0]*2
                weights = [coeff(u, j) for j in range(n)]+[coeff(v, j) for j in range(m)]
                product = add(mul(u, p, prime), mul(v, q, prime), prime)
                for i in range(size+5):
                    result = sum(weights[j]*entry(p, q, m, n, i, j) for j in range(size)) % prime
                    assert result == coeff(product, i) == coeff(target, i)
                    actions += 1
                assert weights == solve_transpose(matrix, [coeff(target, i) for i in range(size)], prime)
                for r in range(size):
                    changed = [row[:] for row in matrix]
                    changed[r] = [coeff(target, i) for i in range(size)]
                    assert weights[r] == numeric_det(changed, prime)*pow(determinant, -1, prime) % prime
                    cramer += 1
            inverses += size
            empty += size == 0
            constants += n == 0 or m == 0
            loose += actual < m
            systems += 1
            accepted += 1
    # A shared factor invalidates the determinant nonzero claim.
    for prime in (2, 3, 5, 17):
        p = q = [1, 1]
        matrix = [[entry(p, q, 1, 1, i, j) for i in range(2)] for j in range(2)]
        assert numeric_det(matrix, prime) == 0
    assert empty and constants and loose
    print(json.dumps(dict(coprime_systems=systems, coefficient_actions=actions,
        monomial_targets=inverses, cramer_entries=cramer, empty_matrices=empty,
        constant_cases=constants, loose_p_degree_bounds=loose, noncoprime_negatives=4,
        scope='Explicit bounded Bezout matrix action, row inverse, nonzero determinant and Cramer coefficients. Source-degree rational denominator composition and protocol soundness remain open.'), indent=2))


if __name__ == '__main__':
    main()
