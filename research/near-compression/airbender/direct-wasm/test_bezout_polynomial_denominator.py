"""Check a single source-degree denominator and exact polynomial certificates."""
import json
import random
from test_bivariate_multiplicity import add, mul, trim
from test_independent_constraint_mixing import evaluate
from test_polynomial_determinant_degree import determinant, numeric_det, permutation_det
from test_determinant_row_replacement import solve_transpose


def main():
    rng = random.Random(4553)
    cases = identities = safe = roots = singular = empty = 0
    for prime in (2, 3, 5, 17):
        for _ in range(90):
            m, n, D = rng.randrange(4), rng.randrange(3), rng.randrange(4)
            ps = [[rng.randrange(prime) for _ in range(D+1)]+[0] for _ in range(m+1)]
            qs = [[rng.randrange(prime) for _ in range(D+1)]+[0] for _ in range(n+1)]
            size = m+n
            def entry(j, i):
                src, offset = (ps, j) if j < n else (qs, j-n)
                return src[i-offset] if 0 <= i-offset < len(src) else []
            matrix = [[entry(j, i) for i in range(size)] for j in range(size)]
            den = determinant(matrix, prime)
            assert den == permutation_det(matrix, prime)
            assert len(den) <= size*D+1
            if not den:
                singular += 1
                continue
            empty += size == 0
            # Polynomial target entries exercise the numerator bound too.
            target = [[rng.randrange(prime) for _ in range(D+1)] for _ in range(size)]
            nums = []
            for r in range(size):
                changed = [row[:] for row in matrix]
                changed[r] = target
                numerator = determinant(changed, prime)
                assert len(numerator) <= size*D+1
                nums.append(numerator)
            # Exact coefficient identity over F_p[Z], not just sampled values.
            for i in range(size+3):
                actual = []
                for j in range(size):
                    actual = add(actual, mul(nums[j], entry(j, i), prime), prime)
                expected = mul(den, target[i], prime) if i < size else []
                assert trim(actual) == trim(expected)
                identities += 1
            bad = 0
            for z in range(prime):
                scalar = [[evaluate(v, z, prime) for v in row] for row in matrix]
                d = evaluate(den, z, prime)
                assert numeric_det(scalar, prime) == d
                if not d:
                    bad += 1
                    continue
                actual = [evaluate(v, z, prime)*pow(d, -1, prime) % prime for v in nums]
                expected = solve_transpose(scalar, [evaluate(v, z, prime) for v in target], prime)
                assert actual == expected
                safe += 1
            assert bad <= size*D
            roots += bad
            cases += 1
    # A nonzero formal denominator may vanish at every base-field point.
    # This validates why the bound cannot assert a safe point unconditionally.
    for prime in (2, 3, 5, 17):
        den = [0, prime-1]+[0]*(prime-2)+[1]
        assert any(den) and all(evaluate(den, z, prime) == 0 for z in range(prime))
    print(json.dumps(dict(nonzero_polynomial_systems=cases, exact_coefficient_identities=identities,
        safe_specializations=safe, exceptional_points=roots, singular_systems=singular,
        empty_systems=empty, nowhere_safe_formal_denominators=4,
        scope='Source-degree common denominator, polynomial Cramer identity, and specialization root bound. Full useful-branch and protocol/QROM soundness remain open.'), indent=2))


if __name__ == '__main__':
    main()
