"""Source-degree collision guard, specialization, and selected-source lifting."""
import json
import random
from test_bivariate_multiplicity import add, mul, trim, compose
from test_independent_constraint_mixing import evaluate
from test_polynomial_determinant_degree import determinant
from test_hensel_bounded_reconstruction import lift
from test_hensel_coefficient_step import order


def matrix(ps, qs, m, n):
    result = []
    for j in range(m+n):
        src, shift = (ps, j) if j < n else (qs, j-n)
        result.append([src[i-shift] if 0 <= i-shift < len(src) else [] for i in range(m+n)])
    return result


def main():
    rng = random.Random(4582)
    cases = identities = collisions = safe_roots = lifts = constants = rejected = 0
    for prime in (2, 3, 5, 17):
        for _ in range(65):
            m = rng.randrange(1, min(4, prime))
            n = rng.randrange(3)
            z0 = rng.randrange(prime)
            # Selected irreducible initial factor Y^m-(Z-z0).
            ps = [[z0, prime-1]]+[[] for _ in range(m-1)]+[[1]]
            qs = [[rng.randrange(prime), rng.randrange(prime)] for _ in range(n)]+[[1]]
            M = matrix(ps, qs, m, n)
            den = determinant(M, prime)
            if not den:
                rejected += 1
                continue
            assert len(den) <= m+n+1
            nums = []
            for r in range(m+n):
                changed = [row[:] for row in M]
                changed[r] = [[1]]+[[] for _ in range(m+n-1)]
                nums.append(determinant(changed, prime))
            for i in range(m+n):
                actual = []
                for j in range(m+n):
                    actual = add(actual, mul(nums[j], M[j][i], prime), prime)
                assert trim(actual) == (den if i == 0 else [])
                identities += 1
            derivative = [[(i+1)*v % prime for v in ps[i+1]] for i in range(m)]
            dden = determinant(matrix(ps, derivative, m, m-1), prime)
            assert dden
            bad = 0
            for z in range(prime):
                h, g = [evaluate(v, z, prime) for v in ps], [evaluate(v, z, prime) for v in qs]
                d = evaluate(den, z, prime)
                common = any(evaluate(h, a, prime) == 0 and evaluate(g, a, prime) == 0 for a in range(prime))
                bad += common
                if common:
                    assert not d
                if not d:
                    continue
                weights = [evaluate(v, z, prime)*pow(d, -1, prime) % prime for v in nums]
                assert trim(add(mul(weights[:n], h, prime), mul(weights[n:], g, prime), prime)) == [1]
                for a in range(prime):
                    if evaluate(h, a, prime):
                        continue
                    assert evaluate(g, a, prime)
                    safe_roots += 1
                    if not evaluate(dden, z, prime):
                        continue
                    product = mul(h, g, prime)
                    rows = [[c, rng.randrange(prime), rng.randrange(prime)] for c in product]+[[]]
                    for precision in (1, 3):
                        f = lift(rows, a, precision, prime)
                        assert (f[0] if f else 0) == a and len(f) <= precision+1
                        assert order(compose(rows, f, prime), precision+1)
                        lifts += 1
            assert bad <= m+n
            collisions += bad
            constants += n == 0
            cases += 1
    # Formal distinctness does not prevent a collision after specialization.
    for prime in (2, 3, 5, 17):
        ps, qs = [[0, prime-1], [1]], [[], [1]]
        den = determinant(matrix(ps, qs, 1, 1), prime)
        assert den and evaluate(den, 0, prime) == 0
    assert collisions and constants and lifts
    print(json.dumps(dict(coprime_parameter_pairs=cases, exact_certificate_coefficients=identities,
        collision_parameter_points=collisions, protected_selected_roots=safe_roots,
        guarded_full_source_lifts=lifts, constant_complements=constants,
        rejected_zero_determinants=rejected, distinct_factor_collision_examples=4,
        scope='Shared source-degree collision guard and combined derivative/collision protected lifting. General factor selection, certificate extraction, useful-branch coverage and protocol soundness remain open.'), indent=2))


if __name__ == '__main__':
    main()
