"""Dense trivariate source specialization and local lifting from actual entries."""
import json
import random
from test_independent_constraint_mixing import evaluate
from test_bivariate_multiplicity import compose
from test_hensel_bounded_reconstruction import lift
from test_hensel_coefficient_step import order
from test_polynomial_determinant_degree import determinant


def main():
    rng = random.Random(4571)
    families = coefficients = lifts = singular = empty_rows = 0
    for prime in (2, 3, 5, 17):
        for _ in range(50):
            d = rng.randrange(1, min(prime, 4))
            z0 = rng.randrange(prime)
            # Initial polynomial Y^d-(Z-z0), irreducible over F_p(Z).
            initial = [[z0, prime-1]]+[[] for _ in range(d-1)]+[[1]]
            dense = [[v]+[[rng.randrange(prime) for _ in range(rng.randrange(4))]
                           for _ in range(rng.randrange(1, 4))] for v in initial]
            dense += [[] for _ in range(rng.randrange(3))]
            empty_rows += sum(not row for row in dense)
            source = [row[0] if row else [] for row in dense]
            deriv = [[(i+1)*c % prime for c in source[i+1]] for i in range(d)]
            size, n = 2*d-1, d-1
            matrix = []
            for j in range(size):
                src, shift = (source, j) if j < n else (deriv, j-n)
                matrix.append([src[i-shift] if 0 <= i-shift < len(src) else [] for i in range(size)])
            den = determinant(matrix, prime)
            assert den and len(den) <= size+1
            bad = 0
            for z in range(prime):
                rows = [[evaluate(v, z, prime) for v in row] for row in dense]
                q = [evaluate(v, z, prime) for v in source]
                for i in range(len(dense)+4):
                    numeric = rows[i][0] if i < len(rows) and rows[i] else 0
                    assert numeric == (q[i] if i < len(q) else 0)
                    coefficients += 1
                qprime = [i*q[i] % prime for i in range(1, len(q))]
                has_singular = False
                for a in range(prime):
                    if evaluate(q, a, prime):
                        continue
                    if not evaluate(qprime, a, prime):
                        has_singular = True
                        assert evaluate(den, z, prime) == 0
                        continue
                    if not evaluate(den, z, prime):
                        continue
                    for precision in (1, 3, 5):
                        f = lift(rows, a, precision, prime)
                        assert (f[0] if f else 0) == a and len(f) <= precision+1
                        assert order(compose(rows, f, prime), precision+1)
                        lifts += 1
                bad += has_singular
            assert bad <= size
            singular += bad
            families += 1
    assert empty_rows and lifts and singular
    print(json.dumps(dict(dense_source_families=families, source_coefficient_checks=coefficients,
        finite_hensel_lifts=lifts, singular_specialization_points=singular,
        empty_source_rows=empty_rows,
        scope='Explicit source specialization and dense trivariate lifting with irreducible initial polynomial. General initial-factor selection, useful-branch coverage and protocol soundness remain open.'), indent=2))


if __name__ == '__main__':
    main()
