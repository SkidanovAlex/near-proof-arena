"""Specialize rational Bezout certificates and lift the resulting smooth roots."""
import json
import random
from test_polynomial_fractions import make, equiv, plus, times
from test_bivariate_multiplicity import mul, compose, trim
from test_bezout_smoothness import sub
from test_independent_constraint_mixing import evaluate
from test_hensel_bounded_reconstruction import lift
from test_hensel_coefficient_step import order


def main():
    rng = random.Random(59031)
    fixtures = coefficient_identities = safe_evaluations = smooth_roots = lifts = poles = singular_roots = 0
    witnesses = []
    for p in (3, 5, 17):
        zero, one = make([], [1]), make([1], [1])
        def polyprod(a, b):
            out = [zero for _ in range(len(a)+len(b)-1)]
            for i, x in enumerate(a):
                for j, y in enumerate(b): out[i+j] = plus(out[i+j], times(x, y, p), p)
            return out
        def scalar(a, z):
            d = evaluate(a[1], z, p)
            assert d
            return evaluate(a[0], z, p)*pow(d, -1, p) % p
        for _ in range(80):
            b = [rng.randrange(p) for _ in range(rng.randrange(1, 4))]
            c = [rng.randrange(p) for _ in range(rng.randrange(1, 4))]
            disc = trim(sub(mul(b, b, p), [4*x % p for x in c], p))
            if not disc: continue
            # Q=Y^2+b(Z)Y+c(Z). -4Q+(2Y+b)Q'=b^2-4c.
            Q = [make(c, [1]), make(b, [1]), one]
            derivative = [make(b, [1]), make([2], [1])]
            A, B = [make([-4 % p], disc)], [make(b, disc), make([2], disc)]
            aq, bq = polyprod(A, Q), polyprod(B, derivative)
            for i in range(3):
                assert equiv(plus(aq[i], bq[i], p), one if i == 0 else zero, p)
                coefficient_identities += 1
            excluded = 0
            for z in range(p):
                bz, cz, dz = evaluate(b, z, p), evaluate(c, z, p), evaluate(disc, z, p)
                if not dz:
                    excluded += 1
                    for a in range(p):
                        if (a*a+bz*a+cz) % p == 0:
                            assert (2*a+bz) % p == 0
                            singular_roots += 1
                    continue
                qs = [scalar(v, z) for v in Q]
                As, Bs = [scalar(v, z) for v in A], [scalar(v, z) for v in B]
                for a in range(p):
                    qval = evaluate(qs, a, p)
                    derivative_value = (2*a+bz) % p
                    assert (As[0]*qval+evaluate(Bs, a, p)*derivative_value) % p == 1
                    safe_evaluations += 1
                    if qval: continue
                    assert derivative_value
                    smooth_roots += 1
                    rows = [[cz, -1 % p], [bz], [1]]
                    for n in (1, 2, 4):
                        f = lift(rows, a, n, p)
                        assert f[0] == a and len(f) <= n+1 and order(compose(rows, f, p), n+1)
                        lifts += 1
                    if len(witnesses) < 4:
                        witnesses.append(dict(prime=p, b=b, c=c, discriminant=disc, z=z, root=a))
            assert excluded <= len(disc)-1
            poles += excluded
            fixtures += 1
    assert singular_roots > 0 and smooth_roots > 0
    print(json.dumps(dict(quadratic_certificate_fixtures=fixtures,
        formal_coefficient_identities=coefficient_identities, safe_certificate_evaluations=safe_evaluations,
        specialized_smooth_roots=smooth_roots, finite_hensel_lifts=lifts,
        excluded_discriminant_points=poles, singular_roots_only_at_excluded_points=singular_roots,
        witnesses=witnesses,
        scope='Specialized rational Bezout certificates imply smooth roots and finite Hensel lifts. Generic coefficient-denominator budgets, branch specialization and full MCA remain open.'), indent=2))


if __name__ == '__main__': main()
