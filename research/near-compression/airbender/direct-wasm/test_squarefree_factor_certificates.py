"""Formal derivative product rule and certificates inherited by selected factors."""
import json
import random
from test_bivariate_multiplicity import add, mul, trim
from test_bezout_smoothness import egcd
from test_independent_constraint_mixing import evaluate


def derivative(p, prime):
    return trim([i*p[i] % prime for i in range(1, len(p))])


def main():
    rng = random.Random(4587)
    products = certificates = root_conditions = rejected = 0
    for prime in (2, 3, 5, 17):
        for _ in range(180):
            h = [rng.randrange(prime) for _ in range(rng.randrange(1, 8))]+[1]
            g = [rng.randrange(prime) for _ in range(rng.randrange(7))]+[1]
            p = mul(h, g, prime)
            dh, dg, dp = derivative(h, prime), derivative(g, prime), derivative(p, prime)
            assert dp == trim(add(mul(dh, g, prime), mul(h, dg, prime), prime))
            products += 1
            gcd, S, T = egcd(p, dp, prime)
            if gcd != [1]:
                rejected += 1
                continue
            U = add(mul(S, g, prime), mul(T, dg, prime), prime)
            V = mul(T, dh, prime)
            W = mul(T, g, prime)
            assert trim(add(mul(U, h, prime), mul(V, g, prime), prime)) == [1]
            assert trim(add(mul(U, h, prime), mul(W, dh, prime), prime)) == [1]
            # Padding changes representation but not either identity.
            assert trim(add(mul(U+[0, 0], h+[0], prime), mul(V+[0], g+[0, 0], prime), prime)) == [1]
            for a in range(prime):
                if not evaluate(h, a, prime):
                    assert evaluate(dh, a, prime) and evaluate(g, a, prime)
                    root_conditions += 1
            certificates += 1
        # A repeated nonconstant factor prevents a source derivative unit certificate.
        h = [1, 1]
        p = mul(h, h, prime)
        assert egcd(p, derivative(p, prime), prime)[0] != [1]
        # Base-field evaluation alone cannot justify formal polynomial equality.
        vanishing = [0, prime-1]+[0]*(prime-2)+[1]
        assert trim(vanishing) and all(evaluate(vanishing, a, prime) == 0 for a in range(prime))
    assert certificates and rejected and root_conditions
    print(json.dumps(dict(formal_derivative_product_identities=products,
        constructed_factor_certificate_pairs=certificates, protected_selected_roots=root_conditions,
        rejected_nonsquarefree_products=rejected, repeated_factor_negatives=4,
        finite_field_evaluation_counterexamples=4,
        scope='Explicit factor/complement and selected-factor derivative certificates from a source derivative unit certificate; collision-count composition. General source separability and factor selection remain open.'), indent=2))


if __name__ == '__main__':
    main()
