"""Shared-denominator specialization, singular-point bound and finite Hensel lift."""
import json
import random
from test_bivariate_multiplicity import add, mul, trim, compose
from test_hensel_bounded_reconstruction import lift
from test_hensel_coefficient_step import order
from test_independent_constraint_mixing import evaluate
from test_polynomial_determinant_degree import determinant
from test_bezout_smoothness import egcd


def main():
    rng = random.Random(4564)
    families = identities = smooth = exceptions = lifts = singular_points = 0
    for prime in (2, 3, 5, 17):
        for _ in range(60):
            d = rng.randrange(1, min(prime, 4))
            z0 = rng.randrange(prime)
            cs = [rng.randrange(1, prime)]+[rng.randrange(prime) for _ in range(d-1)]
            ps = [[-z0*c % prime, c] for c in cs]+[[1]]
            qs = [[(i+1)*v % prime for v in ps[i+1]] for i in range(d)]
            n, size = d-1, 2*d-1
            def entry(j, i):
                src, shift = (ps, j) if j < n else (qs, j-n)
                return src[i-shift] if 0 <= i-shift < len(src) else []
            matrix = [[entry(j, i) for i in range(size)] for j in range(size)]
            den = determinant(matrix, prime)
            assert den and len(den) <= size+1
            nums = []
            for r in range(size):
                changed = [row[:] for row in matrix]
                changed[r] = [[1]]+[[] for _ in range(size-1)]
                num = determinant(changed, prime)
                assert len(num) <= size+1
                nums.append(num)
            for i in range(size+3):
                actual = []
                for j in range(size):
                    actual = add(actual, mul(nums[j], entry(j, i), prime), prime)
                assert trim(actual) == (den if i == 0 else [])
                identities += 1
            bad = singular = 0
            for z in range(prime):
                p = [evaluate(v, z, prime) for v in ps]
                q = [evaluate(v, z, prime) for v in qs]
                value = evaluate(den, z, prime)
                has_singular = any(evaluate(p, a, prime) == 0 and evaluate(q, a, prime) == 0 for a in range(prime))
                singular += has_singular
                if has_singular:
                    assert not value
                if not value:
                    bad += 1
                    continue
                weights = [evaluate(v, z, prime)*pow(value, -1, prime) % prime for v in nums]
                assert trim(add(mul(weights[:n], p, prime), mul(weights[n:], q, prime), prime)) == [1]
                assert egcd(p, q, prime)[0] == [1]
                for a in range(prime):
                    if evaluate(p, a, prime) == 0:
                        assert evaluate(q, a, prime) != 0
                        smooth += 1
                        # Preserve the initial Y polynomial while adding arbitrary X terms.
                        rows = [[c]+[rng.randrange(prime) for _ in range(3)] for c in p]
                        for precision in (1, 2, 4):
                            f = lift(rows, a, precision, prime)
                            assert (f[0] if f else 0) == a
                            assert len(f) <= precision+1
                            assert order(compose(rows, f, prime), precision+1)
                            lifts += 1
            assert singular <= bad <= size
            singular_points += singular
            exceptions += bad
            families += 1
    # Irreducible Y^p-Z is inseparable: the degree<char premise is essential.
    for prime in (2, 3, 5, 17):
        derivative = [i*(1 if i == prime else 0) % prime for i in range(1, prime+1)]
        assert not any(derivative)
    print(json.dumps(dict(eisenstein_families=families, exact_certificate_coefficients=identities,
        safe_smooth_roots=smooth, denominator_exception_points=exceptions,
        singular_specialization_points=singular_points, finite_hensel_lifts=lifts,
        characteristic_degree_counterexamples=4,
        scope='Shared denominator protects certificate specialization and finite Hensel lifting; singular points obey the source-degree bound. Useful-branch extraction and protocol/QROM composition remain open.'), indent=2))


if __name__ == '__main__':
    main()
