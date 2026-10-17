"""Selected-factor smoothness, collision negatives, and actual-source lifts."""
import json
import random
from test_bivariate_multiplicity import mul, compose
from test_independent_constraint_mixing import evaluate
from test_hensel_bounded_reconstruction import lift
from test_hensel_coefficient_step import order
from test_bezout_smoothness import egcd


def derivative(p, prime):
    return [i*p[i] % prime for i in range(1, len(p))]


def main():
    rng = random.Random(4576)
    rules = criteria = collisions = repeated = lifts = certificates = 0
    for prime in (2, 3, 5, 17):
        for _ in range(100):
            h = [rng.randrange(prime) for _ in range(rng.randrange(1, 9))]
            g = [rng.randrange(prime) for _ in range(rng.randrange(1, 7))]
            p = mul(h, g, prime)
            dh, dg, dp = derivative(h, prime), derivative(g, prime), derivative(p, prime)
            gcd, A, B = egcd(h, g, prime)
            for a in range(prime):
                hv, gv = evaluate(h, a, prime), evaluate(g, a, prime)
                hd, gd, pd = evaluate(dh, a, prime), evaluate(dg, a, prime), evaluate(dp, a, prime)
                assert pd == (hd*gv+hv*gd) % prime
                rules += 1
                if hv:
                    continue
                assert bool(pd) == (bool(hd) and bool(gv))
                criteria += 1
                collisions += gv == 0
                assert evaluate(derivative(mul(h, mul(h, g, prime), prime), prime), a, prime) == 0
                repeated += 1
                if gcd == [1]:
                    assert (evaluate(A, a, prime)*hv+evaluate(B, a, prime)*gv) % prime == 1
                    assert gv
                    certificates += 1
                if not hd or not gv:
                    continue
                # Full source has initial h*g; add arbitrary higher X terms.
                rows = [[c, rng.randrange(prime), rng.randrange(prime)] for c in p]+[[], [0]]
                for n in (1, 2, 4):
                    f = lift(rows, a, n, prime)
                    assert (f[0] if f else 0) == a and len(f) <= n+1
                    assert order(compose(rows, f, prime), n+1)
                    lifts += 1
        # Explicit collision of individually smooth factors is singular.
        h = [0, 1]
        assert evaluate(derivative(h, prime), 0, prime) == 1
        assert evaluate(derivative(mul(h, h, prime), prime), 0, prime) == 0
    assert collisions and lifts and certificates
    print(json.dumps(dict(derivative_product_evaluations=rules, selected_root_criteria=criteria,
        colliding_roots=collisions, repeated_factor_singular_roots=repeated,
        unit_certificate_noncollisions=certificates, actual_source_hensel_lifts=lifts,
        scope='Selected-factor root smoothness and lifting with explicit noncollision. Parameter-degree collision guards and useful-branch coverage remain open.'), indent=2))


if __name__ == '__main__':
    main()
