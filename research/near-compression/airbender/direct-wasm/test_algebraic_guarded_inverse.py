"""Derivative inverse representatives, quotient reduction and safe root values."""
import json
import random
from test_bivariate_multiplicity import add, mul, trim
from test_bezout_smoothness import egcd
from test_independent_constraint_mixing import evaluate
from test_polynomial_determinant_degree import determinant
from test_factor_collision_guard import matrix


def main():
    rng = random.Random(4610)
    systems = quotient_inverses = root_inverses = excluded = 0
    for prime in (2, 3, 5, 17):
        for _ in range(60):
            d = rng.randrange(1, min(4, prime))
            z0 = rng.randrange(prime)
            cs = [rng.randrange(1, prime)]+[rng.randrange(prime) for _ in range(d-1)]
            h = [[-z0*c % prime, c] for c in cs]+[[1]]
            dh = [[(i+1)*v % prime for v in h[i+1]] for i in range(d)]
            M = matrix(h, dh, d, d-1)
            den = determinant(M, prime)
            assert den
            nums = []
            for r in range(2*d-1):
                changed = [row[:] for row in M]
                changed[r] = [[1]]+[[] for _ in range(2*d-2)]
                nums.append(determinant(changed, prime))
            B = nums[d-1:]
            # Reduction of B_numerator*h' modulo the monic h over F_p[Z].
            product = [[] for _ in range(len(B)+len(dh)-1)]
            for i, x in enumerate(B):
                for j, y in enumerate(dh): product[i+j] = add(product[i+j], mul(x, y, prime), prime)
            while product and not trim(product[-1]): product.pop()
            while len(product) > d:
                k, c = len(product)-len(h), product[-1]
                for j, hj in enumerate(h):
                    product[k+j] = trim(add(product[k+j], [-v % prime for v in mul(c, hj, prime)], prime))
                while product and not trim(product[-1]): product.pop()
            assert product == [den]
            quotient_inverses += 1
            for z in range(prime):
                dz = evaluate(den, z, prime)
                if not dz:
                    excluded += 1
                    continue
                hs, ds = [evaluate(c, z, prime) for c in h], [evaluate(c, z, prime) for c in dh]
                gcd, _, independent = egcd(hs, ds, prime)
                assert gcd == [1]
                Bs = [evaluate(c, z, prime)*pow(dz, -1, prime) % prime for c in B]
                for a in range(prime):
                    if evaluate(hs, a, prime): continue
                    slope = evaluate(ds, a, prime)
                    assert slope
                    inverse = evaluate(Bs, a, prime)
                    assert inverse == pow(slope, -1, prime) == evaluate(independent, a, prime)
                    root_inverses += 1
            systems += 1
    assert systems and root_inverses and excluded
    print(json.dumps(dict(irreducible_parameter_systems=systems,
        polynomial_quotient_inverse_checks=quotient_inverses,
        guarded_root_inverse_values=root_inverses, excluded_denominator_points=excluded,
        scope='Actual quotient derivative inverse represented by a safe certificate multiplier; numeric values agree with independent Euclid. Full extension Hensel specialization and MCA remain open.'), indent=2))


if __name__ == '__main__':
    main()
